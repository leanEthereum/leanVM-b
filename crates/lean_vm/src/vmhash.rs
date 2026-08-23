//! VM-provable hashing.
//!
//! The VM instruction absorbs one 136-byte rate block into a running
//! `Keccak-f[1600]` state, so a guest can drive the sponge for any input length.
//! What every call site here actually needs is the 64-byte case, which is a
//! single absorb into the zero state and so exactly SHA3-256 of those 64 bytes.
//! Longer messages take the chain of those ([`primitives::hash::hash_md`]),
//! which is what the guest can reproduce a group at a time.

/// SHA3-256 of exactly 64 bytes (two 256-bit halves laid out little-endian),
/// which is the Fiat-Shamir chain step and the PCS Merkle parent. Lives in
/// [`fiat_shamir`] (the shared [`fiat_shamir::FiatShamirState`] state is built
/// on it).
pub use fiat_shamir::compress;
