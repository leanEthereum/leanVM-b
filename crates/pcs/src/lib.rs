// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Tower-field polynomial commitment infrastructure.
//!
//! Boolean witnesses are packed into `K = GF(2^64)` and Ligerito opens them
//! over its cubic extension `E = GF(2^192)`.

mod ligerito_config;
pub mod ligerito;
pub mod merkle;
pub mod ntt;
pub mod pack;
pub mod ring_switch;
pub mod stack_open;
pub mod tensor_algebra;

#[cfg(test)]
pub(crate) mod test_rng;

pub use pack::{LOG_PACKING, PaddingSpec, pack_witness};

/// Transcript aliases used by Flock's reduction-only tests.
pub type Proof = fiat_shamir::transcript::Proof<ligerito::LigeritoProof>;
pub type ProverState = fiat_shamir::transcript::ProverState<ligerito::LigeritoProof>;
pub type VerifierState<'a> = fiat_shamir::transcript::VerifierState<'a, ligerito::LigeritoProof>;
