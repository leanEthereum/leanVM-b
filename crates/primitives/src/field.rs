// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary field arithmetic.
//!
//! - [`F8`]   — GF(2^8) with AES polynomial x^8 + x^4 + x^3 + x + 1
//! - [`F128`] — GF(2^128) in GHASH form, polynomial x^128 + x^7 + x^2 + x + 1
//! - [`F256Unreduced`] — 256-bit unreduced GHASH products, for deferred reduction

pub mod gf2_128;
pub mod gf2_8;
pub mod phi8;

pub use gf2_8::F8;
pub use gf2_128::{F128, F256Unreduced, mul_by_x};
pub use phi8::{PHI_8_TABLE, phi8};

// ---------------------------------------------------------------------------
// leanVM g-power helpers: domain separators / opcodes as x^k, and the g-power
// index encoding.
// ---------------------------------------------------------------------------

use rayon::prelude::*;

/// `[g^0, g^1, …, g^{n-1}]`, built in parallel: each chunk seeds with one g-power
/// (`x_pow`, `O(log)`) and fills by `mul_by_x`, breaking the serial prefix chain
/// across cores.
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

/// `x^k` in the GHASH monomial basis by square-and-multiply (`O(log k)`). Used for
/// domain separators, opcodes, and the g-power index encoding.
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

/// The fixed generator `g = x`, of multiplicative order `2^128 − 1` (`x` is
/// primitive) — larger than every index used. For `k < 128`, `g^k` is the monomial
/// `x^k` (bit `k`), which the XMSS encoding check relies on.
pub const G: F128 = F128::generator();

/// `g^i`, the g-power encoding of index `i` (§1).
#[inline]
pub fn g_pow(i: usize) -> F128 {
    x_pow(i)
}

/// MLE of the index column `[g^0, …, g^{2^n−1}]` over the `n`-variable cube:
/// `∏_k (1 + ζ_k·(1 + g^{2^k}))`, evaluated in `O(n)` (§5.3).
pub fn index_mle(zeta: &[F128]) -> F128 {
    let mut acc = F128::ONE;
    let mut g2k = G; // g^{2^0} = g
    for &z in zeta {
        acc *= F128::ONE + z * (F128::ONE + g2k);
        g2k = g2k * g2k;
    }
    acc
}
