// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! `K = F64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and
//! `E = F128T = K[y]/(y^2 + x*y + 1)`. Addresses, pc/fp, counters, and physical
//! committed columns are K-valued. A machine word is `c0 + c1*y ∈ E` with
//! `c0,c1 ∈ K`; challenges, sumcheck/GKR values, and transcript scalars are
//! E-valued.
//!
//! - [`F64`]   — GF(2^64), polynomial x^64 + x^4 + x^3 + x + 1
//! - [`F128T`] — GF(2^128) as `K[y]/(y^2 + x*y + 1)`
//! - [`F128TUnreduced`] / [`F128TBaseUnreduced`] — its deferred-reduction accumulators
//! - [`F8`]    — GF(2^8) with AES polynomial x^8 + x^4 + x^3 + x + 1
//! - [`F192`]  — `K[y]/(y^3 + y + 1)`
//! - [`F192Unreduced`] — its deferred-reduction accumulator

pub mod gf2_64;
pub mod gf2_64x3;
pub mod gf2_8;
pub mod phi8_tower;
pub mod tower_f128;
pub mod tower_f128_artin;
pub mod vpclmul;

pub use gf2_64::F64;
pub use gf2_64x3::{F192, F192Unreduced};
pub use gf2_8::F8;
pub use phi8_tower::{PHI_8_TABLE, phi8};
pub use tower_f128::{F128T, F128TBaseUnreduced, F128TUnreduced};
pub use tower_f128_artin::{F128TArtin, F128TArtinBaseUnreduced, F128TArtinUnreduced};

// ---------------------------------------------------------------------------
// leanVM g-power helpers: domain separators / opcodes as x^k, and the g-power
// index encoding (§1, §8).
// ---------------------------------------------------------------------------

use rayon::prelude::*;

/// Multiply by `x = g` in `K`, where `x^64 = x^4 + x^3 + x + 1` and
/// `0x1B = x^4 + x^3 + x + 1`.
/// `const` so table constants (`g^k` separators, opcodes) evaluate at compile time.
#[inline]
pub const fn mul_by_g(a: F64) -> F64 {
    let carry = a.0 >> 63;
    F64((a.0 << 1) ^ (0x1B * carry))
}

/// Multiply an `E`-element by the base generator `g = x ∈ K`: lane-wise
/// [`mul_by_g`] on both `K`-coefficients (`(c0 + c1·y)·g = c0·g + (c1·g)·y`) —
/// two shift+folds, no PMULL.
#[inline]
pub const fn mul_by_g_e(a: F128T) -> F128T {
    F128T {
        c0: mul_by_g(F64(a.c0)).0,
        c1: mul_by_g(F64(a.c1)).0,
    }
}

/// `[g^0, g^1, …, g^{n-1}]`, built in parallel: each chunk seeds with one g-power
/// (`x_pow`, `O(log)`) and fills by `mul_by_g`, breaking the serial prefix chain
/// across cores.
pub fn g_powers(n: usize) -> Vec<F64> {
    const CHUNK: usize = 1 << 12;
    let mut v = vec![F64::ZERO; n];
    v.par_chunks_mut(CHUNK).enumerate().for_each(|(ci, chunk)| {
        let mut acc = x_pow(ci * CHUNK);
        for slot in chunk.iter_mut() {
            *slot = acc;
            acc = mul_by_g(acc);
        }
    });
    v
}

/// `x^k` in the monomial basis of `K` by square-and-multiply (`O(log k)`). Used
/// for domain separators, opcodes, and the g-power index encoding.
pub fn x_pow(k: usize) -> F64 {
    let mut result = F64::ONE;
    let mut base = G; // x = g
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

/// The fixed generator `g = x ∈ K`, with `ord(g) = 2^64 - 1` (pinned by a
/// field test), larger than every index any admissible
/// instance uses (the verifier's instance caps, §cpu). For `k < 64`, `g^k` is
/// the monomial `x^k` (bit `k`), which the XMSS encoding check relies on.
pub const G: F64 = F64::G;

/// `g^i`, the g-power encoding of index `i` (§1).
#[inline]
pub fn g_pow(i: usize) -> F64 {
    x_pow(i)
}

/// MLE of the index column `[g^0, …, g^{2^n−1}]` over the `n`-variable cube,
/// evaluated at an `E`-point: `∏_k (1 + ζ_k·(1 + g^{2^k}))` in `O(n)` (§5.3).
/// The `g^{2^k}` factors are `K`-constants, so each term is one mixed product.
pub fn index_mle(zeta: &[F128T]) -> F128T {
    let mut acc = F128T::ONE;
    let mut g2k = G; // g^{2^0} = g
    for &z in zeta {
        acc *= F128T::ONE + z.mul_base(F64::ONE + g2k);
        g2k = g2k * g2k;
    }
    acc
}
