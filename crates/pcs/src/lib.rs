// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Tower-field polynomial commitment infrastructure.
//!
//! Boolean witnesses are packed into `K = GF(2^64)` and Ligerito opens them
//! over its cubic extension `E = GF(2^192)`.

pub mod ligerito;
pub mod ligerito_config;
mod ligerito_induce;
mod ligerito_ntt_ext;
pub mod merkle;
pub mod ntt;
pub mod pack;
pub mod ring_switch;
pub mod stack_open;
pub(crate) mod tensor_algebra;

pub use pack::{LOG_PACKING, PaddingSpec, pack_witness};

/// Transcript state aliases used by Flock's reduction-only tests.
pub type ProverState = fiat_shamir::transcript::ProverState<ligerito::LigeritoProof>;
pub type VerifierState<'a> = fiat_shamir::transcript::VerifierState<'a, ligerito::LigeritoProof>;
