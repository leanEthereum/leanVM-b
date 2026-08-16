//! VM-provable standard SHA-256 hashing.
//!
//! The VM instruction exposes one SHA-256 compression with a memory-supplied
//! chaining value and bytecode-supplied byte counter and finalization flags. A
//! guest can therefore implement the standard sequential compression chain for
//! any input length, including a zero-padded partial final block.

/// Standard SHA-256 of exactly 64 bytes (two 256-bit halves laid out
/// little-endian, the `Sha2` opcode's default metadata), which is also the
/// PCS Merkle parent. Lives in [`fiat_shamir::sponge`] (the shared Fiat-Shamir
/// sponge is built on it).
pub use fiat_shamir::sponge::compress;
