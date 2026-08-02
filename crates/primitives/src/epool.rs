//! Efficiency-core helper pool: barrier-free extra throughput for the
//! prover's embarrassingly parallel phases.
//!
//! The prover sizes rayon's global pool to the performance-core count and
//! pins its workers to `QOS_CLASS_USER_INTERACTIVE`, which keeps them off the
//! efficiency cores (see `lean_vm::init_prover_pool`). On an Apple Silicon
//! host that leaves the E-cores completely idle for the whole proof.
//!
//! Widening the main pool to include them is a known regression, not a win:
//! kernels that partition into one equal band per worker gate their barrier
//! on the slowest core, so a band landing on an E-core stalls every P-core at
//! the join. This module takes the opposite shape:
//!
//! - the main pool is untouched — same width, same QoS, same kernels;
//! - a separate lazily-built pool of `hw.perflevel1.logicalcpu` threads runs
//!   at `QOS_CLASS_UTILITY`, which the scheduler places on E-cores while the
//!   higher-QoS main workers own the P-cores;
//! - work is handed to it through [`run_hetero_chunks`], a shared **atomic
//!   chunk queue** drained by both pools. Because chunks are claimed one at a
//!   time rather than partitioned up front, a slow E-core simply claims fewer
//!   of them, and at the join it owns at most one outstanding chunk.
//!
//! Output is identical by construction: chunk `i` covers a fixed range and is
//! processed by the same function regardless of which pool claims it.
//!
//! On non-macOS or non-Apple-Silicon hosts, and whenever detection fails, the
//! helper pool is absent and the queue is drained by the main pool alone.
//! With a deliberately single-threaded main pool (`RAYON_NUM_THREADS=1`) the
//! queue runs inline on the calling thread and spawns nothing.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use rayon::prelude::*;

/// Logical efficiency-core count on Apple Silicon macOS, else 0.
///
/// Queries `hw.perflevel1.logicalcpu` through the `sysctlbyname` *syscall*,
/// never a spawned `sysctl` process. Apple Silicon has no SMT, so logical ==
/// physical. Any error (missing key, denied, non-positive) degrades to 0,
/// i.e. "no helper pool", never to a failure.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn ecore_count() -> usize {
    unsafe extern "C" {
        fn sysctlbyname(
            name: *const core::ffi::c_char,
            oldp: *mut core::ffi::c_void,
            oldlenp: *mut usize,
            newp: *mut core::ffi::c_void,
            newlen: usize,
        ) -> core::ffi::c_int;
    }
    let mut n: i32 = 0;
    let mut len = core::mem::size_of::<i32>();
    // SAFETY: a read-only sysctl by name; `n`/`len` are correctly sized and
    // the new-value pointer is null, so nothing is written to the kernel.
    let rc = unsafe {
        sysctlbyname(
            c"hw.perflevel1.logicalcpu".as_ptr(),
            (&raw mut n).cast(),
            &raw mut len,
            core::ptr::null_mut(),
            0,
        )
    };
    if rc == 0 && len == core::mem::size_of::<i32>() && n > 0 {
        n as usize
    } else {
        0
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
fn ecore_count() -> usize {
    0
}

/// Tag the current thread `QOS_CLASS_UTILITY` (Darwin value `0x11`). Utility
/// work is scheduled onto efficiency cores while the main pool's
/// `USER_INTERACTIVE` workers occupy the performance cores. Best-effort: QoS
/// is a scheduling hint, and a failure must not affect correctness.
#[cfg(target_os = "macos")]
fn set_utility_qos() {
    const QOS_CLASS_UTILITY: u32 = 0x11;
    unsafe extern "C" {
        fn pthread_set_qos_class_self_np(qos_class: u32, relative_priority: i32) -> i32;
    }
    // SAFETY: a libSystem call that only adjusts this thread's scheduling class.
    unsafe {
        let _ = pthread_set_qos_class_self_np(QOS_CLASS_UTILITY, 0);
    }
}

#[cfg(not(target_os = "macos"))]
fn set_utility_qos() {}

fn build_epool() -> Option<rayon::ThreadPool> {
    let n = ecore_count();
    if n == 0 {
        return None;
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .thread_name(|i| format!("ecore-{i}"))
        .start_handler(|_| set_utility_qos())
        .build()
        .ok()
}

/// The lazily-built efficiency-core helper pool, or `None` off-target.
pub fn epool() -> Option<&'static rayon::ThreadPool> {
    static POOL: OnceLock<Option<rayon::ThreadPool>> = OnceLock::new();
    POOL.get_or_init(build_epool).as_ref()
}

/// Don't engage the helper pool below this many chunks: tiny jobs drain
/// faster than the cross-pool kickoff amortizes.
const EPOOL_MIN_CHUNKS: usize = 16;

/// Process chunks `0..n_chunks` exactly once each, in parallel, drawing from
/// a shared atomic queue drained by the main rayon pool plus (when present,
/// and when the job is large enough) the efficiency-core helper pool.
///
/// `f(i)` must be safe to run concurrently for distinct `i` and must not
/// depend on which thread or pool runs it. Chunk-claim order is
/// nondeterministic; callers get deterministic *output* by making `f(i)`
/// write only to chunk `i`'s disjoint range.
pub fn run_hetero_chunks<F>(n_chunks: usize, f: F)
where
    F: Fn(usize) + Sync,
{
    run_chunks_with_helper(n_chunks, &f, epool());
}

/// [`run_hetero_chunks`] with an explicit helper pool, so tests can exercise
/// the two-pool queue on hosts without efficiency cores.
pub fn run_chunks_with_helper<F>(n_chunks: usize, f: &F, helper: Option<&rayon::ThreadPool>)
where
    F: Fn(usize) + Sync,
{
    if n_chunks == 0 {
        return;
    }
    let main_threads = rayon::current_num_threads();
    if main_threads <= 1 {
        // A deliberately single-threaded pool stays truly single-threaded:
        // run inline, spawn nothing.
        for i in 0..n_chunks {
            f(i);
        }
        return;
    }
    let next = AtomicUsize::new(0);
    let worker = || {
        loop {
            let i = next.fetch_add(1, Ordering::Relaxed);
            if i >= n_chunks {
                break;
            }
            f(i);
        }
    };
    // Main-pool side: one queue-draining task per worker. `with_max_len(1)`
    // splits down to single indices so every main worker can pick one up;
    // under nesting fewer run, which the queue tolerates by construction.
    let drain_main = || {
        (0..main_threads)
            .into_par_iter()
            .with_max_len(1)
            .for_each(|_| worker());
    };
    match helper.filter(|_| n_chunks >= EPOOL_MIN_CHUNKS) {
        Some(ep) => std::thread::scope(|s| {
            // The scoped thread parks inside `broadcast` while the E-workers
            // drain; it costs no main-pool worker. The scope join bounds the
            // tail wait at one chunk on one efficiency core.
            s.spawn(|| ep.broadcast(|_| worker()));
            drain_main();
        }),
        None => drain_main(),
    }
}

/// A `*mut T` that can cross into the chunk closures. The queue hands each
/// chunk index to exactly one worker, so the disjointness that makes the
/// pointer sound is the caller's chunk-ownership contract, restated at each
/// `unsafe` use site.
#[derive(Clone, Copy)]
pub struct SyncPtr<T>(pub *mut T);

// SAFETY: `SyncPtr` grants no access on its own; every dereference is inside
// an `unsafe` block whose comment establishes that the range being touched is
// owned by exactly one chunk.
unsafe impl<T> Send for SyncPtr<T> {}
unsafe impl<T> Sync for SyncPtr<T> {}

impl<T> SyncPtr<T> {
    #[inline]
    pub fn ptr(self) -> *mut T {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicU32;

    /// Every chunk runs exactly once, whichever pool claims it.
    #[test]
    fn helper_queue_runs_each_chunk_exactly_once() {
        let helper = rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap();
        for n in [0usize, 1, 15, 16, 257] {
            let counts: Vec<AtomicU32> = (0..n).map(|_| AtomicU32::new(0)).collect();
            run_chunks_with_helper(
                n,
                &|i| {
                    counts[i].fetch_add(1, Ordering::Relaxed);
                },
                Some(&helper),
            );
            for (i, c) in counts.iter().enumerate() {
                assert_eq!(c.load(Ordering::Relaxed), 1, "chunk {i} of {n}");
            }
        }
    }

    /// Below the engagement threshold the helper is skipped, but every chunk
    /// still runs.
    #[test]
    fn small_jobs_skip_helper_but_complete() {
        let n = EPOOL_MIN_CHUNKS - 1;
        let counts: Vec<AtomicU32> = (0..n).map(|_| AtomicU32::new(0)).collect();
        run_hetero_chunks(n, |i| {
            counts[i].fetch_add(1, Ordering::Relaxed);
        });
        assert!(counts.iter().all(|c| c.load(Ordering::Relaxed) == 1));
    }
}
