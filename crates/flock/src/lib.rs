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
//! Steps 2 to 4 are circuit-agnostic: they read a [`r1cs::BlockR1cs`] and its
//! packed witness. Two circuits supply those:
//!
//! - [`blake3`], the one leanVM proves: the BLAKE3 compression as a per-block
//!   R1CS (`build_block_r1cs`), plus its witness generation and the
//!   leanVM-facing reduction entry points
//!   (`Blake3Setup::{prove_reduction, verify_reduction, …}`).
//! - [`blake2s`], the ten-round sibling, at the same `k_log = 14`. It shares
//!   the reduction and is proven through it by `tests/blake2s_reduction.rs`,
//!   but has no leanVM embedding: nothing outside flock consumes it yet.
//!
//! Both encode the same primitive, a 32-bit ARX round whose only nonlinear
//! constraints are the ADD product bits, so the symbolic-word representation
//! and the adder gadgets live once in the private `gf2` module and each circuit only supplies
//! its schedule, layout and finalization.

pub mod blake2s;
pub mod blake3;
mod blake3_witness;
mod gf2;
pub mod lincheck;
pub mod proof;
pub mod r1cs;
pub mod verifier;
pub mod zerocheck;
