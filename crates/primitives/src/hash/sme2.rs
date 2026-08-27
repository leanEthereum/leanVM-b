//! BLAKE2s over sixteen inputs at once, in SME2 streaming mode.
//!
//! A streaming vector is 512 bits, so one register holds one state word across
//! sixteen lanes, and `xar` fuses each xor with its rotation. The catch is that
//! the SME block is shared by a whole core cluster and one thread saturates it,
//! so this is faster per thread and slower per machine: [`enabled`] hands it to
//! the few workers that can reach a block of their own and leaves everyone else
//! on NEON.

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
    let block = [0u8; BLOCK_LEN];
    let inputs = [block.as_ptr(); LANES];
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
    lanes == LANES as u64 && out.chunks_exact(OUT_LEN).all(|d| d == super::hash(&block))
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
/// Workers 0 and 1 are dispatcher and first performance worker, which the
/// scheduler tends to place on different performance clusters, and worker
/// `perf` is the first efficiency one, which reaches the third block. A bad
/// landing costs little: guided self-scheduling leaves a streaming worker that
/// shares a block claiming fewer chunks.
pub(super) fn enabled() -> bool {
    if !available() {
        return false;
    }
    let slots = [0, 1, parallel::topology().perf];
    slots[..streaming_workers()].contains(&parallel::worker_id())
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
    // Fewer than sixteen inputs left, and a batch under sixteen never entered
    // the loop at all: NEON finishes those, being the faster of the two below
    // one full vector.
    let done = n - n % LANES;
    if done < n {
        // SAFETY: `n - done` inputs of `len` bytes remain, with as many digests.
        unsafe {
            hash_many_with::<Neon>(&data[done * len..], len, state, t_offset, &mut out[done * OUT_LEN..]);
        }
    }
}
