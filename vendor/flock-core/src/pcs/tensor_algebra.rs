// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from binius64's `crates/math/src/tensor_algebra.rs`
// (https://github.com/binius-zk/binius64), specialized to `F = F_2`,
// `FE = F_{2^128}`.

//! Tensor algebra over `F_{2^128} ⊗_{F_2} F_{2^128}`.
//!
//! An element is a length-128 vector of `F128` (the "vertical-subring" elements
//! in DP24 nomenclature). Conceptually it's a 128×128 F_2 matrix, where row `i`
//! is `elems[i]` viewed via its bit-decomposition in the GHASH polynomial
//! basis (`bit_j(elems[i])` = coefficient of `γ^i ⊗ γ^j` in the tensor algebra).
//!
//! Used by the verifier's polylog `eval_rs_eq` (DP24 §1.3, Figure 3).

use crate::field::F128;
use core::ops::{Add, AddAssign};

/// The degree of `F_{2^128}` over `F_2`.
pub const DEGREE: usize = 128;

/// An element of `F_{2^128} ⊗_{F_2} F_{2^128}`, stored as 128 `F128` elements
/// (the vertical-subring decomposition).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TensorAlgebra {
    /// Length-128 vector. `elems[i]` is the coefficient of `γ^i` in the
    /// vertical basis decomposition.
    pub elems: Vec<F128>,
}

impl TensorAlgebra {
    /// All-zero element.
    pub fn zero() -> Self {
        Self {
            elems: vec![F128::ZERO; DEGREE],
        }
    }

    /// Multiplicative identity: `1 ⊗ 1`.
    pub fn one() -> Self {
        let mut elems = vec![F128::ZERO; DEGREE];
        elems[0] = F128::ONE;
        Self { elems }
    }

    /// Embed `x ∈ F_{2^128}` into the vertical subring: returns `1 ⊗ x`.
    pub fn from_vertical(x: F128) -> Self {
        let mut elems = vec![F128::ZERO; DEGREE];
        elems[0] = x;
        Self { elems }
    }

    /// Multiply by an element of the vertical subring: each `elems[i]` is
    /// scaled by `scalar` in `F_{2^128}`.
    pub fn scale_vertical(mut self, scalar: F128) -> Self {
        for e in self.elems.iter_mut() {
            *e *= scalar;
        }
        self
    }

    /// Multiply by an element of the horizontal subring. Implemented as
    /// `transpose ∘ scale_vertical ∘ transpose`.
    pub fn scale_horizontal(self, scalar: F128) -> Self {
        self.transpose().scale_vertical(scalar).transpose()
    }

    /// Transpose the tensor algebra element: swap vertical and horizontal
    /// subring roles. Concretely, after transpose, `bit_j(elems'[i]) =
    /// bit_i(elems[j])` for all `i, j ∈ [0, 128)`.
    pub fn transpose(mut self) -> Self {
        square_transpose(&mut self.elems);
        self
    }

    /// Fold the tensor algebra element to a single `F128` by scaling rows with
    /// `coeffs` (length 128) and summing.
    ///
    /// Computes `Σ_i coeffs[i] · transpose(self).elems[i]`.
    pub fn fold_vertical(self, coeffs: &[F128]) -> F128 {
        assert_eq!(
            coeffs.len(),
            DEGREE,
            "fold_vertical: coeffs.len() must be 128"
        );
        let transposed = self.transpose();
        let mut acc = F128::ZERO;
        for (e, c) in transposed.elems.iter().zip(coeffs.iter()) {
            acc += *e * *c;
        }
        acc
    }
}

impl Add<&TensorAlgebra> for TensorAlgebra {
    type Output = TensorAlgebra;
    fn add(mut self, rhs: &TensorAlgebra) -> TensorAlgebra {
        self += rhs;
        self
    }
}

impl AddAssign<&TensorAlgebra> for TensorAlgebra {
    fn add_assign(&mut self, rhs: &TensorAlgebra) {
        for (a, b) in self.elems.iter_mut().zip(rhs.elems.iter()) {
            *a = *a + *b;
        }
    }
}

/// In-place 128×128 F_2 matrix transpose of the F128 coefficient table.
///
/// On input: `elems[i]` viewed as a 128-bit row; bit `j` is the F_2 coefficient
/// at position `(i, j)`.
/// On output: bit `j` of `elems[i]` becomes the old bit `i` of `elems[j]`.
///
/// V1 implementation: naive O(D²) bit-scan. Each of 128² output bits is read
/// from exactly one input bit.
fn square_transpose(elems: &mut [F128]) {
    assert_eq!(
        elems.len(),
        DEGREE,
        "square_transpose: input must be length 128"
    );

    let mut out = [F128::ZERO; DEGREE];
    for j in 0..DEGREE {
        let src_bit = |k: usize| -> u64 {
            if j < 64 {
                (elems[k].lo >> j) & 1
            } else {
                (elems[k].hi >> (j - 64)) & 1
            }
        };
        let mut lo: u64 = 0;
        let mut hi: u64 = 0;
        for i in 0..64 {
            lo |= src_bit(i) << i;
        }
        for i in 64..128 {
            hi |= src_bit(i) << (i - 64);
        }
        out[j] = F128 { lo, hi };
    }
    elems.copy_from_slice(&out);
}
