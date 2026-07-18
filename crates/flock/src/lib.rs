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
//! [`sha256`] is the circuit used by leanVM: one fixed-IV SHA-256 compression
//! encoded as a per-block R1CS, with witness generation and the leanVM-facing
//! reduction entry points.

pub mod binary_witness;
pub mod lincheck;
pub mod proof;
pub mod r1cs;
pub mod sha256;
pub mod verifier;
pub mod zerocheck;

#[cfg(test)]
pub(crate) mod test_rng;
