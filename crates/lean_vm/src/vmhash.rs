//! VM-provable `sha2_eth` hashing.
//!
//! The VM instruction exposes one SHA-256 compression with a memory-supplied
//! chaining value and nothing else: `sha2_eth` carries the message length in
//! its FIRST block, so a block needs no byte counter and no finalization flag.
//! A guest therefore implements a hash of any length as the plain chain
//! `C(iv_for_len(n), m_1), C(·, m_2), …`, with the starting value a
//! compile-time constant and a zero-padded partial final block.

/// `sha2_eth` of exactly 64 bytes (two 256-bit halves laid out little-endian),
/// which is the `Sha2` opcode's default chaining value and also the PCS Merkle
/// parent. Lives in [`fiat_shamir`] (the shared
/// [`fiat_shamir::FiatShamirState`] state is built on it).
pub use fiat_shamir::compress;
