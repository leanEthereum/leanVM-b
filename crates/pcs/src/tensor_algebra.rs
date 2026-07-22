// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Adapted from [`super::tensor_algebra`] (itself a port of binius64's
// `crates/math/src/tensor_algebra.rs`) for the 64-bit transition:
// K = F_{2^64} packing, E = GF(2^192) tower opening field.

//! Tensor-algebra helpers for the rectangular (f = 64, e = 192) ring switch.
//!
//! Two pieces live here:
//!
//! 1. **The rectangular transpose** [`transpose_s_hat`]: an element of
//!    `K (x)_F2 E` is a 64x192 F_2 matrix. The prover's message `s_hat_v` is
//!    its row view: 64 E-elements, `s_hat_v[i]` = the MLE of the i-th
//!    bit-slice of the witness at the suffix point. The transpose re-packs
//!    the columns: 192 K-elements `s_hat_u`, where
//!    ```text
//!        bit i of s_hat_u[w]  ==  bit w of s_hat_v[i]
//!    ```
//!    `s_hat_u[w]` is `t_w` in the ring-switching-generalized note: the
//!    packed-polynomial claim attached to the w-th E-basis coordinate,
//!    `t_w = sum_y A(y, w) * P_packed(y)` with `A(y, w)` = the w-th F_2
//!    coordinate of `eq(r_suffix, y)`.
//!
//! 2. **The square E-tensor algebra** [`TensorAlgebraE`] over
//!    `E (x)_F2 E`: the verifier's polylog `eval_rs_eq` accumulates
//!    `sum_y eq(query, y) (x) eq(r_suffix, y)`, which is E-valued on BOTH
//!    factors (the K packing never appears there because `rs_eq_ind` is
//!    E-valued). The F_2 coordinates of an E element are the bits of its
//!    `(c0, c1, c2)` representation.
//!
//! "Bit w" of an E element means: bit w of `c0` for `w < 64`, bit `w - 64`
//! of `c1` for `w < 128`, and bit `w - 128` of `c2` otherwise.

use core::ops::{Add, AddAssign};
use primitives::field::{F64, F192};

/// The degree of K = F_{2^64} over F_2 (the packing degree f).
pub const DEGREE: usize = 64;

/// The degree of E = GF(2^192) over F_2 (the opening degree e).
pub const DEGREE_E: usize = 192;

/// Bit w of an E element in the tower basis (w in 0..192).
#[inline(always)]
fn ext_bit(e: F192, w: usize) -> u64 {
    if w < 64 {
        (e.c0 >> w) & 1
    } else if w < 128 {
        (e.c1 >> (w - 64)) & 1
    } else {
        (e.c2 >> (w - 128)) & 1
    }
}

/// Rectangular tensor-algebra transpose: `s_hat_v` (64 E-elements, the row
/// view of a `K (x)_F2 E` element) to `s_hat_u` (192 K-elements, the column
/// view).
///
/// ```text
///     bit i of s_hat_u[w]  ==  bit w of s_hat_v[i],   i in 0..64, w in 0..192
/// ```
///
/// `s_hat_u[w] = t_w` in the ring-switching-generalized note. Mirror of
/// the legacy tensor-algebra transpose, generalized to the 64x192 shape.
/// Naive O(64 * 192) bit-scan; the input is a fixed 1.5 KiB, so this is never
/// on a hot path.
pub fn transpose_s_hat(s_hat_v: &[F192]) -> Vec<F64> {
    assert_eq!(
        s_hat_v.len(),
        DEGREE,
        "transpose_s_hat: s_hat_v must have one entry per packing bit (64)"
    );
    let mut s_hat_u = vec![F64::ZERO; DEGREE_E];
    for (i, elem) in s_hat_v.iter().enumerate() {
        // Deposit bit w of elem into bit i of s_hat_u[w]; scan set bits only.
        let mut c0 = elem.c0;
        while c0 != 0 {
            let w = c0.trailing_zeros() as usize;
            s_hat_u[w].0 |= 1u64 << i;
            c0 &= c0 - 1;
        }
        let mut c1 = elem.c1;
        while c1 != 0 {
            let w = c1.trailing_zeros() as usize;
            s_hat_u[64 | w].0 |= 1u64 << i;
            c1 &= c1 - 1;
        }
        let mut c2 = elem.c2;
        while c2 != 0 {
            let w = c2.trailing_zeros() as usize;
            s_hat_u[128 | w].0 |= 1u64 << i;
            c2 &= c2 - 1;
        }
    }
    s_hat_u
}

/// An element of `E (x)_F2 E` (E = the tower GF(2^192)), stored as 192
/// `F192` elements: `elems[i]` is the second-factor component attached to
/// the i-th F_2-basis element of the first factor, i.e.
/// `bit_j(elems[i])` = the coefficient of `b_i (x) b_j`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TensorAlgebraE {
    /// Length-192 vector; see the struct docs for the indexing convention.
    pub elems: Vec<F192>,
}

impl TensorAlgebraE {
    /// All-zero element.
    pub fn zero() -> Self {
        Self {
            elems: vec![F192::ZERO; DEGREE_E],
        }
    }

    /// Multiplicative identity: `1 (x) 1`.
    pub fn one() -> Self {
        let mut elems = vec![F192::ZERO; DEGREE_E];
        elems[0] = F192::ONE;
        Self { elems }
    }

    /// Embed `x` into the vertical subring: returns `1 (x) x`.
    pub fn from_vertical(x: F192) -> Self {
        let mut elems = vec![F192::ZERO; DEGREE_E];
        elems[0] = x;
        Self { elems }
    }

    /// Multiply by an element of the vertical subring (`1 (x) scalar`): each
    /// `elems[i]` is scaled by `scalar` in E.
    pub fn scale_vertical(mut self, scalar: F192) -> Self {
        for e in self.elems.iter_mut() {
            *e *= scalar;
        }
        self
    }

    /// Multiply by an element of the horizontal subring (`scalar (x) 1`).
    /// Implemented as `transpose . scale_vertical . transpose`.
    pub fn scale_horizontal(self, scalar: F192) -> Self {
        self.transpose().scale_vertical(scalar).transpose()
    }

    /// Transpose: swap the two tensor factors. Concretely, after transpose,
    /// `bit_j(elems'[i]) = bit_i(elems[j])` for all `i, j in [0, 192)`.
    pub fn transpose(mut self) -> Self {
        square_transpose_ext(&mut self.elems);
        self
    }

    /// Fold to a single E element: transpose, then scale row `w` by
    /// `coeffs[w]` and sum.
    ///
    /// Computes `sum_w coeffs[w] * transpose(self).elems[w]`. With `self =
    /// sum_y eq(query, y) (x) eq(z, y)` and `coeffs = eq(r'')` this is the
    /// MLE of `rs_eq_ind` at `query` (see `ring_switch::eval_rs_eq`).
    pub fn fold_vertical(self, coeffs: &[F192]) -> F192 {
        assert_eq!(coeffs.len(), DEGREE_E, "fold_vertical: coeffs.len() must be 192");
        let transposed = self.transpose();
        let mut acc = F192::ZERO;
        for (e, c) in transposed.elems.iter().zip(coeffs.iter()) {
            acc += *e * *c;
        }
        acc
    }
}

impl Add<&TensorAlgebraE> for TensorAlgebraE {
    type Output = TensorAlgebraE;
    fn add(mut self, rhs: &TensorAlgebraE) -> TensorAlgebraE {
        self += rhs;
        self
    }
}

impl AddAssign<&TensorAlgebraE> for TensorAlgebraE {
    fn add_assign(&mut self, rhs: &TensorAlgebraE) {
        for (a, b) in self.elems.iter_mut().zip(rhs.elems.iter()) {
            *a = *a + *b;
        }
    }
}

/// In-place 192x192 F_2 matrix transpose of the F192 coefficient table.
///
/// On input: `elems[i]` viewed as a 192-bit row; bit `j` (tower basis) is the
/// F_2 coefficient at position `(i, j)`. On output: bit `j` of `elems[i]`
/// becomes the old bit `i` of `elems[j]`. Mirror of
/// `tensor_algebra::square_transpose`, extended to `(c0, c1, c2)`.
fn square_transpose_ext(elems: &mut [F192]) {
    assert_eq!(elems.len(), DEGREE_E, "square_transpose_ext: input must be length 192");

    let mut out = [F192::ZERO; DEGREE_E];
    for (j, o) in out.iter_mut().enumerate() {
        let mut c0: u64 = 0;
        let mut c1: u64 = 0;
        let mut c2: u64 = 0;
        for i in 0..64 {
            c0 |= ext_bit(elems[i], j) << i;
        }
        for i in 64..128 {
            c1 |= ext_bit(elems[i], j) << (i - 64);
        }
        for i in 128..192 {
            c2 |= ext_bit(elems[i], j) << (i - 128);
        }
        *o = F192::new(c0, c1, c2);
    }
    elems.copy_from_slice(&out);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_ext(s: &mut u64) -> F192 {
        F192::new(splitmix64(s), splitmix64(s), splitmix64(s))
    }

    #[test]
    fn rect_transpose_bit_relation() {
        let mut s = 1u64;
        let s_hat_v: Vec<F192> = (0..DEGREE).map(|_| rand_ext(&mut s)).collect();
        let s_hat_u = transpose_s_hat(&s_hat_v);
        assert_eq!(s_hat_u.len(), DEGREE_E);
        for i in 0..DEGREE {
            for w in 0..DEGREE_E {
                assert_eq!(
                    (s_hat_u[w].0 >> i) & 1,
                    ext_bit(s_hat_v[i], w),
                    "bit ({i}, {w}) not transposed"
                );
            }
        }
    }

    #[test]
    fn square_transpose_is_involution() {
        let mut s = 2u64;
        let orig: Vec<F192> = (0..DEGREE_E).map(|_| rand_ext(&mut s)).collect();
        let t = TensorAlgebraE { elems: orig.clone() };
        let tt = t.clone().transpose();
        // Bit relation on a spot-check diagonal band plus full involution.
        for i in 0..DEGREE_E {
            for w in [0usize, 1, 63, 64, 65, 127] {
                assert_eq!(ext_bit(tt.elems[i], w), ext_bit(orig[w], i));
            }
        }
        assert_eq!(tt.transpose().elems, orig, "transpose twice must be id");
    }

    /// `fold_vertical(from_vertical(x), coeffs)` is exactly the F_2-linear
    /// map Phi sending the w-th E-basis bit to coeffs[w], applied to x. This
    /// is the map the ring switch uses to define `rs_eq_ind`.
    #[test]
    fn fold_vertical_is_phi() {
        let mut s = 3u64;
        let coeffs: Vec<F192> = (0..DEGREE_E).map(|_| rand_ext(&mut s)).collect();
        let x = rand_ext(&mut s);
        let folded = TensorAlgebraE::from_vertical(x).fold_vertical(&coeffs);
        let mut expected = F192::ZERO;
        for (w, &c) in coeffs.iter().enumerate() {
            if ext_bit(x, w) == 1 {
                expected += c;
            }
        }
        assert_eq!(folded, expected);
    }

    /// `scale_horizontal(1 (x) 1, s) == s (x) 1 == transpose(1 (x) s)`.
    #[test]
    fn scale_horizontal_semantics() {
        let mut s = 4u64;
        let x = rand_ext(&mut s);
        let lhs = TensorAlgebraE::one().scale_horizontal(x);
        let rhs = TensorAlgebraE::from_vertical(x).transpose();
        assert_eq!(lhs, rhs);
    }
}
