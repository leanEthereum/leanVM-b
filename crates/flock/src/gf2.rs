//! The two things a circuit walk needs, independent of which circuit it is.
//!
//! A circuit's matrices are never built. Instead it is described twice, and
//! both descriptions are `O(circuit)`: forwards, threading wire values against
//! column weights to give every row its `(A₀ w, B₀ w)` pair, and backwards, the
//! reverse-mode transpose of that walk, giving the column marginal
//! `(A₀ + α B₀)ᵀ u`. [`RowValues`] is what the forward walk fills and
//! [`MatrixSide`] is what tells the backward walk which operand of each row it
//! is following.
//!
//! The pair is cross-checked by the protocol itself: lincheck's terminal
//! identity is exactly the assertion that the backward walk's marginal,
//! contracted against the column weights, equals the forward walk's bilinear
//! form. `sha3`'s `marginal_walk_transposes_the_forward_walk` asserts it
//! directly as well.
//!
//! The gadgets themselves live with the circuit, in [`crate::hash`]: Keccak's
//! word is a 64-bit lane rather than a 32-bit one, and its only nonlinear
//! gadget is `chi`'s AND, so there is nothing here to share.

use primitives::field::F192;

/// The matrix-vector products `(A_0 w, B_0 w)`. Rows with no wire keep their zeros.
pub(crate) struct RowValues {
    pub(crate) a: Vec<F192>,
    pub(crate) b: Vec<F192>,
    wc: F192,
}

impl RowValues {
    pub(crate) fn new(k: usize, wc: F192) -> Self {
        Self {
            a: vec![F192::ZERO; k],
            b: vec![F192::ZERO; k],
            wc,
        }
    }

    /// A product row: both operands are wires.
    #[inline]
    pub(crate) fn product(&mut self, k: usize, a: F192, b: F192) {
        self.a[k] = a;
        self.b[k] = b;
    }

    /// A row whose B side is the lone constant wire: a free input, or a lin-id
    /// pin materializing an affine word into its own slots.
    #[inline]
    pub(crate) fn bconst(&mut self, k: usize, a: F192) {
        self.a[k] = a;
        self.b[k] = self.wc;
    }
}

/// Which matrix operand the backward walk follows in each R1CS row. One walk
/// per side, so a row contributes its weight to exactly one of them.
#[derive(Clone, Copy)]
pub(crate) enum MatrixSide {
    A,
    B,
}

impl MatrixSide {
    #[inline]
    pub(crate) fn split(self, value: F192) -> (F192, F192) {
        match self {
            Self::A => (value, F192::ZERO),
            Self::B => (F192::ZERO, value),
        }
    }
}
