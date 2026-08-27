//! BLAKE2s over sixteen inputs at once, in SME2 streaming mode.
//!
//! A streaming vector is 512 bits, so one register holds one state word across
//! sixteen lanes, and `xar` fuses each xor with its rotation. The catch is that
//! the SME block is shared by a whole core cluster and one thread saturates it,
//! so this is faster per thread and slower per machine: [`enabled`] hands it to
//! the few workers that can reach a block of their own and leaves everyone else
//! on NEON.
//!
//! Two hazards come with the mode. A signal delivered inside the kernel runs
//! its handler with `PSTATE.SM` still set, where Advanced SIMD is illegal, so a
//! handler using vector code takes `SIGILL`; nothing in this workspace installs
//! one. And bare `smstart` enables ZA without committing a pending lazy save,
//! which is safe only because nothing else here uses ZA, so `TPIDR2_EL0` is
//! always zero.

use std::sync::OnceLock;

use super::{BLOCK_LEN, IV, OUT_LEN, PARAM_IV, arm::Neon, hash_many_with};

std::arch::global_asm!(include_str!("blake2s_sme2.s"), options(raw));

unsafe extern "C" {
    /// Returns the streaming vector length in 32-bit lanes; anything but 16
    /// means it wrote nothing.
    fn blake2s_hash16_sme2(
        inputs: *const *const u8,
        state: *const u32,
        t_offset: u64,
        len: u64,
        out: *mut u8,
        iv: *const u32,
    ) -> u64;
}

/// Inputs per call: the 32-bit lanes of one streaming vector.
pub(super) const LANES: usize = 16;

/// Read an integer `sysctl`, `None` if it does not exist.
fn sysctl(name: &core::ffi::CStr) -> Option<i32> {
    let mut value: i32 = 0;
    let mut len = core::mem::size_of::<i32>();
    // SAFETY: a read-only sysctl with a correctly sized destination and a null
    // new-value pointer.
    let rc = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            (&raw mut value).cast(),
            &raw mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    (rc == 0).then_some(value)
}

/// Whether this machine has the kernel's vector length and agrees with the
/// scalar backend on one block.
fn probe() -> bool {
    if sysctl(c"hw.optional.arm.FEAT_SME2") != Some(1) {
        return false;
    }
    // Sixteen different blocks, so a lane that reads the wrong input fails here
    // rather than in a proof.
    let blocks: [[u8; BLOCK_LEN]; LANES] = std::array::from_fn(|l| std::array::from_fn(|i| (l * 61 + i * 7) as u8));
    let inputs: [*const u8; LANES] = std::array::from_fn(|l| blocks[l].as_ptr());
    let mut out = [0u8; LANES * OUT_LEN];
    // SAFETY: sixteen pointers to a whole readable block, and room for sixteen
    // digests.
    let lanes = unsafe {
        blake2s_hash16_sme2(
            inputs.as_ptr(),
            PARAM_IV.as_ptr(),
            0,
            BLOCK_LEN as u64,
            out.as_mut_ptr(),
            IV.as_ptr(),
        )
    };
    lanes == LANES as u64 && (0..LANES).all(|l| out[l * OUT_LEN..(l + 1) * OUT_LEN] == super::hash(&blocks[l])[..])
}

/// How many workers take the streaming path, at most one per cluster.
///
/// A second thread on a cluster splits one block rather than finding another,
/// so past three this only takes cores away from NEON. `LEANVM_SME_WORKERS`
/// overrides it, `0` disabling the backend.
fn streaming_workers() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| {
        std::env::var("LEANVM_SME_WORKERS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(SLOTS)
            .min(SLOTS)
    })
}

/// One streaming slot per SME block: two performance clusters and the
/// efficiency one.
const SLOTS: usize = 3;

/// Whether the calling worker should take the streaming path.
///
/// Worker 0 is the dispatcher and worker 1 the first performance worker, which
/// the scheduler does place on different performance clusters; worker `perf` is
/// the first efficiency one, which reaches the third block. The
/// [`parallel::in_task`] guard is what makes slot 0 safe: every thread outside
/// the pool reads as worker 0 too, and without it one of those could split the
/// dispatcher's block, which is the single thing this list exists to prevent. A
/// bad landing costs little anyway, since guided self-scheduling leaves a
/// worker that shares a block claiming fewer chunks.
pub(super) fn enabled() -> bool {
    // Before `available`, which probes by running the kernel: on a host that
    // claims the feature but faults on `SMSTART`, setting the count to zero has
    // to be enough to stay away from it.
    let slots = [0, 1, parallel::topology().perf];
    let slots = &slots[..streaming_workers()];
    // A sequential pool dispatches nothing, so nothing is ever in a task, and
    // with one thread there is no block to contend for either.
    let in_pool_work = parallel::in_task() || parallel::num_threads() <= 1;
    in_pool_work && slots.contains(&parallel::worker_id()) && available()
}

/// Whether this host runs the kernel at all, probed once.
pub(super) fn available() -> bool {
    static AVAILABLE: OnceLock<bool> = OnceLock::new();
    *AVAILABLE.get_or_init(probe)
}

/// [`super::hash_many_dyn_from_state`] on the streaming backend.
///
/// # Safety
/// `data` must hold `n * len` bytes for `n = out.len() / OUT_LEN`, and `len`
/// must be a nonzero multiple of [`BLOCK_LEN`].
pub(super) unsafe fn hash_many(data: &[u8], len: usize, state: &[u32; 8], t_offset: u64, out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    if n < LANES {
        // Under one vector there is nothing for the wide lanes to carry, and
        // NEON does not pay to enter streaming mode.
        // SAFETY: the caller's sizes, unchanged.
        unsafe { hash_many_with::<Neon>(data, len, state, t_offset, out) };
        return;
    }
    let mut inputs = [std::ptr::null::<u8>(); LANES];
    for g in 0..n / LANES {
        let base = g * LANES;
        for (l, slot) in inputs.iter_mut().enumerate() {
            *slot = data[(base + l) * len..].as_ptr();
        }
        // SAFETY: every pointer has `len` readable bytes, and the sixteen
        // digests at `base` are inside `out`.
        unsafe {
            blake2s_hash16_sme2(
                inputs.as_ptr(),
                state.as_ptr(),
                t_offset,
                len as u64,
                out.as_mut_ptr().add(base * OUT_LEN),
                IV.as_ptr(),
            );
        }
    }
    // The remainder rides a padded group rather than a NEON call. Leaving
    // streaming mode to finish a handful of inputs costs several times what
    // the spare lanes do, those being free: the kernel drives sixteen either
    // way. Repeating the last input fills them.
    let done = n - n % LANES;
    if done < n {
        for (l, slot) in inputs.iter_mut().enumerate() {
            *slot = data[(done + l).min(n - 1) * len..].as_ptr();
        }
        let mut padded = [0u8; LANES * OUT_LEN];
        // SAFETY: every pointer is one of this batch's own inputs, so each has
        // `len` readable bytes, and `padded` holds all sixteen digests.
        unsafe {
            blake2s_hash16_sme2(
                inputs.as_ptr(),
                state.as_ptr(),
                t_offset,
                len as u64,
                padded.as_mut_ptr(),
                IV.as_ptr(),
            );
        }
        out[done * OUT_LEN..].copy_from_slice(&padded[..(n - done) * OUT_LEN]);
    }
}
