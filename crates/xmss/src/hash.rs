//! The XMSS hash layer: [`tweak_hash`] is standard BLAKE2s of the exact byte
//! string `tweak | pp | payload`, for chain steps, Merkle nodes, WOTS public
//! keys, and message encodings alike.
//!
//! The 16-byte tweak makes every call site a distinct hash function
//! (multi-target separation, as in leanVM) and the public parameter separates
//! users. Standard BLAKE2s binds the exact payload length.
//!
//! Compression counts per call: chain step 1, Merkle node 1, message encoding
//! 2, WOTS public key 11. A full XMSS verification is a constant 144
//! compressions: 2 (encoding) + 99 (chains, fixed by the target sum) + 11
//! (tips) + 32 (Merkle path).

use crate::*;

// Tweak types (tweak byte 0), so distinct kinds of hashes cannot alias.
pub const TWEAK_TYPE_CHAIN: u8 = 0;
pub const TWEAK_TYPE_WOTS_PK: u8 = 1;
pub const TWEAK_TYPE_MERKLE: u8 = 2;
pub const TWEAK_TYPE_ENCODING: u8 = 3;

pub const TWEAK_LEN: usize = 16;
pub type Tweak = [u8; TWEAK_LEN];

/// A full 32-byte BLAKE2s chaining value/output.
pub const STATE_LEN: usize = 32;

/// `[tweak_type (1) | sub_position (4) | index (4) | zeros (7)]`, little-endian.
/// `index` is the epoch (chain / wots_pk / encoding) or the Merkle node index;
/// `sub_position` is the chain position or the Merkle level.
pub fn make_tweak(tweak_type: u8, sub_position: u32, index: u32) -> Tweak {
    let mut tweak = [0u8; TWEAK_LEN];
    tweak[0] = tweak_type;
    tweak[1..5].copy_from_slice(&sub_position.to_le_bytes());
    tweak[5..9].copy_from_slice(&index.to_le_bytes());
    tweak
}

/// Standard BLAKE2s of the exact-length `tweak | pp | payload` byte string. One
/// compression for chain steps (48 bytes total) and Merkle nodes (64 bytes
/// total), more for the multi-block WOTS public-key and encoding inputs.
pub fn tweak_hash(pp: &PublicParam, tweak_type: u8, sub_position: u32, index: u32, payload: &[u8]) -> Digest {
    let mut hasher = primitives::blake2s::Hasher::new();
    hasher.update(&make_tweak(tweak_type, sub_position, index));
    hasher.update(pp);
    hasher.update(payload);
    hasher.finalize()[..DIGEST_LEN].try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tweak_separates_everything() {
        let pp = [7u8; PUBLIC_PARAM_LEN];
        let x = [1u8; DIGEST_LEN];
        let base = tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &x);
        // Different type, position, index, or pp: different hash.
        assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_MERKLE, 3, 5, &x));
        assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 4, 5, &x));
        assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 6, &x));
        assert_ne!(base, tweak_hash(&[8u8; 16], TWEAK_TYPE_CHAIN, 3, 5, &x));
        // Standard BLAKE2s binds the exact payload length.
        let mut extended = [0u8; STATE_LEN];
        extended[..DIGEST_LEN].copy_from_slice(&x);
        assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &extended));
    }

    #[test]
    fn multi_block_hash_is_standard_blake2s() {
        let pp = [9u8; PUBLIC_PARAM_LEN];
        let data = [5u8; 2 * STATE_LEN];
        let mut input = Vec::new();
        input.extend_from_slice(&make_tweak(TWEAK_TYPE_WOTS_PK, 0, 42));
        input.extend_from_slice(&pp);
        input.extend_from_slice(&data);
        let expected = primitives::blake2s::hash(&input);
        assert_eq!(
            tweak_hash(&pp, TWEAK_TYPE_WOTS_PK, 0, 42, &data),
            expected[..DIGEST_LEN]
        );
    }
}
