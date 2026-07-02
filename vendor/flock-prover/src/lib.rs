//! `flock-prover` (vendored, BLAKE3 subset): the R1CS prover orchestration plus
//! the BLAKE3 per-block R1CS encoder, trimmed from flock's `flock-prover` crate
//! to only what leanVM-b's BLAKE3 instruction needs.
//!
//! Vendored — like `flock-core`/`flare` — so leanVM-b does not depend on the
//! external `../binary-fields/flock` tree. It builds against the SAME vendored
//! `flock-core` (path `../flock-core`) that leanVM-b imports as `flare`, so the
//! `F128` packed witness this prover produces is the same field type as the rest
//! of the committed columns (the whole point of the integration).
//!
//! Dropped vs. upstream: the keccak / keccak3 / sha2 encoders, the hash-chain
//! and Merkle-path statement builders (`chain`, `merkle_path`, `chain_common`,
//! `proof_io`), and the `flock_chain` binary. Only single-block BLAKE3
//! compression proving (`r1cs_hashes::blake3`) and the generic R1CS prover
//! (`prover`) are kept.

pub use flock_core::*;

pub mod prover;
pub mod r1cs_hashes;
