// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system for hash circuits over GF(2), reduced
//! to evaluation claims on the committed packed witness.
//!
//! Protocol flow (all challenges from the shared [`fiat_shamir`] transcript):
//!   1. The caller commits the packed Boolean witness `q_flock` (inside the VM's
//!      one stacked [`pcs`] commitment).
//!   2. [`zerocheck`] reduces `a·b ⊕ c = 0` over the cube to evaluation claims
//!      on `(â, b̂, ĉ)`.
//!   3. [`lincheck`] reduces those to the `2^k_skip` bit-slice values of `z` at
//!      one point, against the per-block matrices.
//!   4. The PCS binds that family of slices ([`sha2::SliceClaim`]) to the
//!      commitment.
//!
//! [`sha2`] is the one circuit: the SHA-256 compression as a per-block R1CS,
//! plus its witness generation and the leanVM-facing reduction entry points
//! (`Sha2Setup::{prove_reduction, verify_reduction, …}`). Steps 2 to 4 above
//! are circuit-agnostic: they take the block shape as plain numbers and reach
//! the matrices only through [`lincheck::LincheckCircuit`], whose one live impl
//! walks the circuit rather than reading any matrix.
//!
//! SHA-256's XORs, rotations and shifts are free over GF(2), so its only
//! nonlinear constraints are the bitwise ANDs of `Ch` and `Maj` and the product
//! bits of the modular ADDs. The private `gf2` module owns that part: the wire
//! word, the AND gadget and the two adders, forwards and transposed, kept
//! separate because the fused three-operand adder's bit boundaries are the
//! subtlest thing here.

mod gf2;
pub mod lincheck;
/// The circuit driven through the whole reduction. A `src` module rather than
/// its own test binary so it shares the process, and its guest compilation,
/// with the unit tests.
#[cfg(test)]
mod reduction_tests;
pub mod sha2;
pub mod verifier;
mod witness;
pub mod zerocheck;
