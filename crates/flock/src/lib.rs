// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system for hash circuits over GF(2), reduced
//! to evaluation claims on the committed packed witness.
//!
//! Protocol flow (all challenges from the shared [`fiat_shamir`] transcript):
//!   1. The caller commits the packed Boolean witness `q_flock` (inside the VM's
//!      one stacked [`pcs`] commitment).
//!   2. [`zerocheck`] reduces `a·b ⊕ c = 0` over the cube to evaluation claims
//!      on `(â, b̂, ĉ)`.
//!   3. [`lincheck`] reduces those to a single claim `ẑ(ρ') = v` against the
//!      per-block matrices.
//!   4. The PCS discharges the resulting [`proof::ZClaim`]s.
//!
//! [`blake2s`] is the one circuit: the BLAKE2s compression encoded as a
//! per-block R1CS (`build_block_r1cs`), plus its witness generation and the
//! leanVM-facing reduction entry points
//! (`Blake2sSetup::{prove_reduction, verify_reduction, …}`). Steps 2 to 4 above
//! are circuit-agnostic: they read a [`r1cs::BlockR1cs`] and its packed
//! witness.
//!
//! BLAKE2s is a 32-bit ARX round whose XORs and rotations are free over GF(2),
//! so its only nonlinear constraints are the product bits of the modular ADDs.
//! The private `gf2` module owns that part: the symbolic affine word and the two
//! adder gadgets, kept separate because the fused three-operand adder's bit
//! boundaries are the subtlest thing here and deserve their own tests.

pub mod blake2s;
mod gf2;
pub mod lincheck;
pub mod proof;
pub mod r1cs;
pub mod verifier;
mod witness;
pub mod zerocheck;
