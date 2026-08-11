//! VM-provable standard BLAKE2s hashing.
//!
//! The VM instruction exposes one BLAKE2s compression with a memory-supplied
//! chaining value and bytecode-supplied counter, block length, and flags. A
//! guest can therefore replay the standard chunk/tree mode instead of using a
//! custom Merkle--Damgard construction.

/// Standard BLAKE2s of exactly 64 bytes (two 256-bit halves laid out
/// little-endian, the `Blake2s` opcode's default metadata), which is also the
/// PCS Merkle parent. Lives in [`fiat_shamir::sponge`] (the shared Fiat-Shamir
/// sponge is built on it).
pub use fiat_shamir::sponge::compress;
