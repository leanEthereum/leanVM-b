//! Shared primitives: the GF(2^128)/GF(2^8) field kernels, bit transposes,
//! multilinear helpers, the scratch buffer pool, and small integer utilities.

pub mod bits;
pub mod field;
pub mod multilinear;
pub mod scratch;

pub use field::{F128, F256Unreduced, G, g_pow, g_powers, mul_by_x, x_pow};

/// `log2` of a power of two (panics otherwise).
pub fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))` for `n ≥ 1`.
pub fn log2_ceil_usize(n: usize) -> usize {
    assert!(n >= 1);
    usize::BITS as usize - (n - 1).leading_zeros() as usize
}

/// Allocate a `Vec<T>` of length `n` whose contents are NOT zero-initialized.
/// Caller MUST write every slot before reading it.
///
/// Used to skip the eager zero-init of large ping-pong buffers in hot prover
/// paths (Ligerito codeword + Merkle tree, zerocheck Round-2 fold, NTT
/// scratch, lincheck packing). At m=29 the
/// zero-fill of a fresh 128 MB `vec![T::default(); n]` runs sequentially on
/// the main thread (~22 ms), which caps the parallel speedup of those phases.
///
/// `T: Copy` ensures `T` has no Drop impl, so the leaked uninitialized
/// elements are a no-op on drop.
///
/// # Safety contract
///
/// Reading uninitialized memory is UB per Rust's memory model regardless of
/// whether all bit patterns are valid for `T`. Caller must ensure every slot
/// is written before any read.
// `uninit_vec` flags exactly this pattern; here it is the deliberate purpose of
// the function (the safety contract above is what makes it sound).
#[allow(clippy::uninit_vec)]
pub fn alloc_uninit_vec<T: Copy>(n: usize) -> Vec<T> {
    let mut v: Vec<T> = Vec::with_capacity(n);
    // SAFETY:
    // - capacity == n was just allocated, so set_len(n) is in bounds.
    // - T: Copy implies !Drop, so leaking uninit elements is a no-op.
    // - Caller upholds write-before-read.
    unsafe {
        v.set_len(n);
    }
    v
}

/// Cached [`perf_core_count`]. The uncached version may spawn `sysctl`; this
/// memoizes it so hot paths can cheaply ask "is the current rayon pool the
/// homogeneous P-core pool?" (i.e. `current_num_threads() <= this`).
#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))] // caller is aarch64-only
pub fn perf_core_count_cached() -> usize {
    use std::sync::OnceLock;
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(perf_core_count)
}

/// Best-effort count of performance cores. On macOS, queries
/// `hw.perflevel0.physicalcpu` (= P-core count on Apple silicon, =
/// physical CPU count on Intel). Elsewhere, falls back to
/// `std::thread::available_parallelism()`.
fn perf_core_count() -> usize {
    #[cfg(target_os = "macos")]
    {
        if let Ok(out) = std::process::Command::new("sysctl")
            .args(["-n", "hw.perflevel0.physicalcpu"])
            .output()
            && let Ok(s) = std::str::from_utf8(&out.stdout)
            && let Ok(n) = s.trim().parse::<usize>()
            && n > 0
        {
            return n;
        }
    }
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}