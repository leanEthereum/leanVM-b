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
//!   4. The PCS binds that family of slices ([`hash::SliceClaim`]) to the
//!      commitment.
//!
//! [`hash`] is the one circuit: one Keccak sponge step,
//! `permute(prev ^ (msg || 0...0))`, as a per-block R1CS, plus its witness
//! generation and the leanVM-facing reduction entry points
//! (`Sha3Setup::{prove_reduction, verify_reduction, …}`). Steps 2 to 4 above
//! are circuit-agnostic: they take the block shape as plain numbers and reach
//! the matrices only through [`lincheck::LincheckCircuit`], whose one live impl
//! walks the circuit rather than reading any matrix.
//!
//! Keccak's theta, rho, pi and iota are all free over GF(2), and so is the
//! absorb, so the only nonlinear constraints are chi's ANDs, one per bit of the
//! state per round. The private `gf2` module owns the two things a walk needs
//! whichever circuit it is; the gadgets themselves are small enough to live
//! with the circuit.

mod gf2;
pub mod lincheck;
/// The circuit driven through the whole reduction. A `src` module rather than
/// its own test binary so it shares the process with the unit tests.
#[cfg(test)]
mod reduction_tests;
pub mod hash;
pub mod verifier;
mod witness;
pub mod zerocheck;
