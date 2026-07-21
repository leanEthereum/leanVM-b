//! VM-provable standard BLAKE3 hashing helpers.
//!
//! The VM instruction exposes one BLAKE3 compression with a memory-supplied
//! chaining value and bytecode-supplied counter, block length, and flags. A
//! guest can therefore replay the standard chunk/tree mode instead of using a
//! custom Merkle--Damgard construction.

use primitives::field::F128;

/// The historical one-block helper: standard BLAKE3 of exactly 64 bytes.
/// This remains useful for Merkle parent nodes and existing callers.
pub use fiat_shamir::sponge::compress;

/// Standard BLAKE3 of the little-endian byte encoding of a field-element slice.
pub fn hash_slice(data: &[F128]) -> [F128; 2] {
    let mut hasher = blake3::Hasher::new();
    for word in data {
        hasher.update(&word.to_le_bytes());
    }
    let digest = hasher.finalize();
    [
        F128::from_le_bytes(digest.as_bytes()[..16].try_into().unwrap()),
        F128::from_le_bytes(digest.as_bytes()[16..].try_into().unwrap()),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(k: u64) -> F128 {
        F128::new(k, k.wrapping_mul(0x9e37_79b9) ^ 0x51)
    }

    #[test]
    fn hash_slice_is_standard_blake3() {
        for n in [0usize, 1, 2, 3, 64, 65] {
            let words: Vec<F128> = (0..n).map(|i| e(i as u64 + 1)).collect();
            let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
            let got = hash_slice(&words);
            let expected = blake3::hash(&bytes);
            assert_eq!(got[0].to_le_bytes(), expected.as_bytes()[..16]);
            assert_eq!(got[1].to_le_bytes(), expected.as_bytes()[16..]);
            assert_eq!(::pcs::merkle::hash_leaf(&bytes), *expected.as_bytes());
        }
    }
}
