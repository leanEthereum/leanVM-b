// Credit: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system for hash circuits over GF(2), reduced
//! to evaluation claims on the committed packed witness.
//!
//! Protocol flow (all challenges from the shared [`fiat_shamir`] transcript):
//!   1. The caller commits the packed Boolean witness `q_pkd` (inside the VM's
//!      one stacked [`pcs`] commitment).
//!   2. [`zerocheck`] reduces `a·b ⊕ c = 0` over the cube to evaluation claims
//!      on `(â, b̂, ĉ)`.
//!   3. [`lincheck`] reduces those to a single claim `ẑ(ρ') = v` against the
//!      per-block matrices.
//!   4. The PCS discharges the resulting [`proof::ZClaim`]s.
//!
//! [`blake3`] is the one circuit: the BLAKE3 compression encoded as a
//! per-block R1CS (`build_block_r1cs`), with the pinned root-block
//! configuration baked into constant rows, plus its witness generation
//! ([`blake3_witness`]) and the leanVM-facing reduction entry points
//! (`Blake3Setup::{prove_reduction, verify_reduction, …}`).

pub mod blake3;
pub mod blake3_witness;
pub mod lincheck;
pub mod proof;
pub mod r1cs;
pub mod verifier;
pub mod zerocheck;
