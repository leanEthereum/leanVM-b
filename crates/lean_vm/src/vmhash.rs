//! VM-provable standard BLAKE2s hashing.
//!
//! The VM instruction exposes one BLAKE2s compression whose chaining value, byte
//! counter and finalization flags are all memory-supplied. A guest can therefore
//! implement the standard sequential compression chain for any input length,
//! including a zero-padded partial final block, and the length need not be known
//! when the program is compiled.

/// Standard BLAKE2s of exactly 64 bytes (two 256-bit halves laid out
/// little-endian, the `Blake2s` opcode's default metadata), which is also the
/// PCS Merkle parent. Lives in [`fiat_shamir`] (the shared
/// [`fiat_shamir::FiatShamirState`] state is built on it).
pub use fiat_shamir::compress;
