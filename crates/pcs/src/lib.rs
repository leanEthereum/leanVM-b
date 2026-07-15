// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Tower-field polynomial commitment infrastructure.
//!
//! Boolean witnesses are packed into `K = GF(2^64)` and Ligerito opens them
//! over its quadratic extension `E = GF(2^128)`.

pub mod ligerito;
pub mod ligerito_k;
pub mod merkle;
pub mod ntt;
pub mod pack_k;
pub mod ring_switch_k;
pub mod stack_open_k;
pub mod tensor_algebra_k;

#[cfg(test)]
pub(crate) mod test_rng;

pub use pack_k::{LOG_PACKING_K as LOG_PACKING, PaddingSpec, pack_witness_k as pack_witness};

/// Transcript aliases used by Flock's reduction-only tests.
pub type Proof = fiat_shamir::transcript::Proof<ligerito_k::LigeritoProofK>;
pub type ProverState = fiat_shamir::transcript::ProverState<ligerito_k::LigeritoProofK>;
pub type VerifierState<'a> = fiat_shamir::transcript::VerifierState<'a, ligerito_k::LigeritoProofK>;
