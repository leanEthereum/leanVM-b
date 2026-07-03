//! GF(2^128) in GHASH form — re-exported from the flock (`flare`) crate.
//!
//! The Ligerito PCS (`crate::pcs`) is flock's, so the whole stack shares one
//! field type. We add only the small monomial-basis helpers the VM needs
//! (domain separators / opcodes as `x^k`, the g-power index encoding).

use rayon::prelude::*;

pub use flare::field::{F128, F256Unreduced, mul_by_x};

/// `[g^0, g^1, …, g^{n-1}]` (the index column over a range), built in parallel:
/// each chunk seeds with one `g`-power (`x_pow`, `O(log)`) and fills by
/// `mul_by_x` (`g = x`, a shift + conditional XOR), so the otherwise-serial
/// prefix-product chain is broken across cores. Below one chunk it is a plain
/// serial fill. Used for the address/pc lookup tables (`cpu`, `leaf`).
pub fn g_powers(n: usize) -> Vec<F128> {
    const CHUNK: usize = 1 << 12;
    let mut v = vec![F128::ZERO; n];
    v.par_chunks_mut(CHUNK).enumerate().for_each(|(ci, chunk)| {
        let mut acc = x_pow(ci * CHUNK);
        for slot in chunk.iter_mut() {
            *slot = acc;
            acc = mul_by_x(acc);
        }
    });
    v
}

/// `x^k` in the GHASH monomial basis — used for domain separators and opcodes
/// (§8: `x, x^2, x^3, …`) and the `g`-power index encoding (§1).
///
/// Square-and-multiply: `O(log k)` field multiplications. (A naïve `k`×
/// `mul_by_x` is `O(k)`, which turns the per-row `g^index` fills and the
/// address-table build into `O(n²)` over a trace of `n` rows.)
pub fn x_pow(k: usize) -> F128 {
    let mut result = F128::ONE;
    let mut base = F128::generator(); // x = g
    let mut e = k;
    while e > 0 {
        if e & 1 == 1 {
            result *= base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

/// The fixed generator `g = x` (the GHASH variable). A logical index `i` is
/// carried as `g^i`; incrementing it is `mul_by_x` (multiply by `g`), the free
/// virtual operation of the design. `x` is primitive: its multiplicative order
/// is exactly `2^128 − 1` (checked via `x^{(2^128−1)/p} ≠ 1` for every prime
/// `p | 2^128 − 1`), which exceeds every index used (memory size `2^h`,
/// program length, access counts). For `k < 128`, `g^k` is the monomial `x^k`
/// (bit `k`), which the XMSS encoding check relies on (the
/// `encoding_check_telescopes` test in `xmss/`).
pub const G: F128 = F128::generator();

/// `g^i`, the `g`-power encoding of index `i` (§1). Equal to `x_pow(i)` since
/// `g = x`.
#[inline]
pub fn g_pow(i: usize) -> F128 {
    x_pow(i)
}

/// Multilinear extension of the index column `[g^0, g^1, …, g^{2^n−1}]` over the
/// `n`-variable cube (cell `i` at the cube point of its binary digits):
/// `∏_{k=0}^{n−1} (1 + ζ_k·(1 + g^{2^k}))`, evaluated in `O(n)` (§5.3).
pub fn index_mle(zeta: &[F128]) -> F128 {
    let mut acc = F128::ONE;
    let mut g2k = G; // g^{2^0} = g
    for &z in zeta {
        acc *= F128::ONE + z * (F128::ONE + g2k);
        g2k = g2k * g2k; // g^{2^{k+1}}
    }
    acc
}
