//! VM-provable standard BLAKE3 hashing helpers.
//!
//! The VM instruction exposes one BLAKE3 compression with a memory-supplied
//! chaining value and bytecode-supplied counter, block length, and flags. A
//! guest can therefore replay the standard chunk/tree mode instead of using a
//! custom Merkle--Damgard construction.

use primitives::field::F64;

/// The historical one-block helper: standard BLAKE3 of exactly 64 bytes (two
/// 256-bit halves laid out little-endian — the `Blake3` opcode's default
/// metadata). This remains useful for Merkle parent nodes and existing callers.
/// Lives in [`fiat_shamir::sponge`] (the shared Fiat–Shamir sponge is built on it).
pub use fiat_shamir::sponge::compress;

/// Standard BLAKE3 of the little-endian byte encoding of a K-word slice,
/// returned as four field words. A guest replays it with the `blake3` opcode's
/// chunk-chaining metadata: one compression per 64-byte block, CHUNK_START on
/// the first, CHUNK_END | ROOT on the last (zero-padded partial tail).
pub fn hash_slice(data: &[F64]) -> [F64; 4] {
    let mut hasher = blake3::Hasher::new();
    for word in data {
        hasher.update(&word.0.to_le_bytes());
    }
    let digest = hasher.finalize();
    let w = |o: usize| u64::from_le_bytes(digest.as_bytes()[o..o + 8].try_into().unwrap());
    [F64(w(0)), F64(w(8)), F64(w(16)), F64(w(24))]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(k: u64) -> F64 {
        F64(k.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x51)
    }

    /// `hash_slice` is exactly standard BLAKE3 of the words' little-endian
    /// bytes, and the PCS Merkle leaf hash (`::pcs::merkle::hash_leaf`) equals
    /// it on the same field words — the invariant that lets a recursive
    /// verifier reuse ONE routine for the transcript/leaf hashing and the PCS
    /// tree. Covers empty, single-word, odd, multi-block, and multi-chunk
    /// slices.
    #[test]
    fn hash_slice_is_standard_blake3() {
        for n in [0usize, 1, 2, 3, 5, 8, 64, 65] {
            let words: Vec<F64> = (0..n).map(|i| e(i as u64 + 1)).collect();
            let bytes: Vec<u8> = words.iter().flat_map(|w| w.0.to_le_bytes()).collect();
            let got = hash_slice(&words);
            let expected = blake3::hash(&bytes);
            let mut got_bytes = [0u8; 32];
            for (k, w) in got.iter().enumerate() {
                got_bytes[8 * k..8 * k + 8].copy_from_slice(&w.0.to_le_bytes());
            }
            assert_eq!(got_bytes, *expected.as_bytes(), "n={n}");
            assert_eq!(::pcs::merkle::hash_leaf(&bytes), *expected.as_bytes(), "n={n}");
        }
    }

    /// Standard BLAKE3 binds the length, so a slice and the same slice with an
    /// extra trailing zero word hash differently — no padding ambiguity.
    #[test]
    fn hash_slice_binds_length() {
        assert_ne!(hash_slice(&[e(7)]), hash_slice(&[e(7), F64::ZERO]));
        let four: Vec<F64> = (1..=4).map(e).collect();
        let mut padded = four.clone();
        padded.extend([F64::ZERO; 4]);
        assert_ne!(hash_slice(&four), hash_slice(&padded));
    }
}
