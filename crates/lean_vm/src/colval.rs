//! One column value, `K` while a table is unfolded and `E` once it is not.
//!
//! A table's columns are `K`-valued (`F64`, §def:column). The table sumcheck folds
//! them against an `E` challenge in the round the table joins (§sec:air), so from the
//! next round on they are `E`-valued. Both phases evaluate the SAME identities,
//! so each identity is written once against this trait and instantiated twice.
//! There is no second copy to drift, which matters: the verifier evaluates the
//! same identity as the prover, and a divergence would be a soundness bug rather
//! than a wrong number.
//!
//! What the `K` instance buys, per operation:
//!
//! | operation                     | `K`                     | `E`                  |
//! |-------------------------------|-------------------------|----------------------|
//! | column times column           | 1 PMULL                 | 6 PMULL + reduce     |
//! | column times `η`-power or coeff | 3 PMULL (`mul_base`)  | 6 PMULL + reduce     |
//! | `c0 + c1·y + c2·y²`           | free (it IS the triple) | 2 mul-by-`y` + adds  |
//! | a dense form over `n` columns | `n` mixed, one reduce   | `n` full, one reduce |

use primitives::field::{F64, F192, F192BaseUnreduced, F192Unreduced, mul_by_g, mul_by_g_e};
use std::ops::{Add, Mul};

/// A value a constraint reads out of a column.
pub trait ColVal: Copy + Send + Sync + Add<Output = Self> + Mul<Output = Self> {
    const ZERO: Self;
    const ONE: Self;

    /// The third interpolation node of a sumcheck round, `lo + g·(lo + hi)`, in the
    /// column's own field: no lift, so a `K` round pays a `mul_by_g` and an add.
    fn at_g(lo: Self, hi: Self) -> Self;

    /// Times a `K` constant: a `g`-power, an opcode tag.
    fn mul_k(self, k: F64) -> Self;

    /// Times an `E` value: an `η`-power, a bus coefficient, a machine word.
    fn mul_e(self, e: F192) -> F192;

    /// Lift into `E`.
    fn to_e(self) -> F192;

    /// A 192-bit machine word from its three `K`-lanes, `c0 + c1·y + c2·y²`.
    fn word(c0: Self, c1: Self, c2: Self) -> F192;

    /// `constant + Σ coeffs[i]·vals[i]`, accumulated unreduced and reduced once.
    fn dot(coeffs: &[F192], vals: &[Self], constant: F192) -> F192;
}

impl ColVal for F64 {
    const ZERO: Self = F64::ZERO;
    const ONE: Self = F64::ONE;

    #[inline(always)]
    fn at_g(lo: Self, hi: Self) -> Self {
        lo + mul_by_g(lo + hi)
    }

    #[inline(always)]
    fn mul_k(self, k: F64) -> Self {
        self * k
    }

    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        e.mul_base(self)
    }

    #[inline(always)]
    fn to_e(self) -> F192 {
        F192::from(self)
    }

    #[inline(always)]
    fn word(c0: Self, c1: Self, c2: Self) -> F192 {
        F192::new(c0.0, c1.0, c2.0)
    }

    #[inline(always)]
    fn dot(coeffs: &[F192], vals: &[Self], constant: F192) -> F192 {
        let acc = coeffs
            .iter()
            .zip(vals)
            .fold(F192BaseUnreduced::ZERO, |acc, (&w, &v)| acc ^ w.mul_base_unreduced(v));
        constant + acc.reduce()
    }
}

impl ColVal for F192 {
    const ZERO: Self = F192::ZERO;
    const ONE: Self = F192::ONE;

    #[inline(always)]
    fn at_g(lo: Self, hi: Self) -> Self {
        lo + mul_by_g_e(lo + hi)
    }

    #[inline(always)]
    fn mul_k(self, k: F64) -> Self {
        self.mul_base(k)
    }

    #[inline(always)]
    fn mul_e(self, e: F192) -> F192 {
        self * e
    }

    #[inline(always)]
    fn to_e(self) -> F192 {
        self
    }

    #[inline(always)]
    fn word(c0: Self, c1: Self, c2: Self) -> F192 {
        c0 + F192::Y * (c1 + F192::Y * c2)
    }

    #[inline(always)]
    fn dot(coeffs: &[F192], vals: &[Self], constant: F192) -> F192 {
        let acc = coeffs
            .iter()
            .zip(vals)
            .fold(F192Unreduced::ZERO, |acc, (&w, &v)| acc ^ w.mul_unreduced(v));
        constant + acc.reduce()
    }
}
