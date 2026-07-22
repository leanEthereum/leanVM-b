//! The XMSS hash layer, built from keyed BLAKE3:
//!
//! - [`tweak_hash`]: keyed BLAKE3 of `payload` under `pp | tweak`, used for chain steps
//!   and Merkle nodes;
//! - [`tweak_hash_many`]: the same exact-length keyed construction for the WOTS
//!   public-key and message-encoding inputs, which span multiple compression
//!   blocks.
//!
//! The 16-byte tweak makes every call site a distinct hash function
//! (multi-target separation, as in leanVM) and the public parameter separates
//! users. Keyed BLAKE3 binds the exact payload length.
//!
//! Compression counts per call: chain step 1, quaternary Merkle node 1, message
//! encoding 1, WOTS public key 11. A full XMSS verification is a constant 128
//! compressions: 1 (encoding) + 100 (chains, fixed by the target sum) + 11
//! (tips) + 16 (Merkle path).

use crate::*;

// Tweak types (tweak byte 0), so distinct kinds of hashes cannot alias.
pub const TWEAK_TYPE_CHAIN: u8 = 0;
pub const TWEAK_TYPE_WOTS_PK: u8 = 1;
pub const TWEAK_TYPE_MERKLE: u8 = 2;
pub const TWEAK_TYPE_ENCODING: u8 = 3;

pub const TWEAK_LEN: usize = 16;
pub type Tweak = [u8; TWEAK_LEN];

/// A full 32-byte BLAKE3 chaining value/output.
pub const STATE_LEN: usize = 32;
pub type State = [u8; STATE_LEN];

/// `[tweak_type (1) | sub_position (4) | index (4) | zeros (7)]`, little-endian.
/// `index` is the slot (chain / wots_pk / encoding) or the Merkle node index;
/// `sub_position` is the chain position or the Merkle level.
pub fn make_tweak(tweak_type: u8, sub_position: u32, index: u32) -> Tweak {
    let mut tweak = [0u8; TWEAK_LEN];
    tweak[0] = tweak_type;
    tweak[1..5].copy_from_slice(&sub_position.to_le_bytes());
    tweak[5..9].copy_from_slice(&index.to_le_bytes());
    tweak
}

fn hash_key(pp: &PublicParam, tweak_type: u8, sub_position: u32, index: u32) -> [u8; 32] {
    let mut key = [0u8; 32];
    key[..PUBLIC_PARAM_LEN].copy_from_slice(pp);
    key[PUBLIC_PARAM_LEN..].copy_from_slice(&make_tweak(tweak_type, sub_position, index));
    key
}

/// Keyed BLAKE3 of `payload` under the key `pp | tweak`.
pub fn tweak_hash(
    pp: &PublicParam,
    tweak_type: u8,
    sub_position: u32,
    index: u32,
    payload: &[u8],
) -> Digest {
    blake3::keyed_hash(&hash_key(pp, tweak_type, sub_position, index), payload).as_bytes()
        [..DIGEST_LEN]
        .try_into()
        .unwrap()
}

/// Keyed BLAKE3 of the exact-length `data` byte string under `pp | tweak`.
pub fn tweak_hash_many(
    pp: &PublicParam,
    tweak_type: u8,
    sub_position: u32,
    index: u32,
    data: &[u8],
) -> Digest {
    tweak_hash(pp, tweak_type, sub_position, index, data)
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
        // Keyed BLAKE3 binds the exact payload length.
        let mut extended = [0u8; STATE_LEN];
        extended[..DIGEST_LEN].copy_from_slice(&x);
        assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &extended));
    }

    #[test]
    fn multi_block_hash_is_standard_keyed_blake3() {
        let pp = [9u8; PUBLIC_PARAM_LEN];
        let data = [5u8; 2 * STATE_LEN];
        let expected = blake3::keyed_hash(&hash_key(&pp, TWEAK_TYPE_WOTS_PK, 0, 42), &data);
        assert_eq!(
            tweak_hash_many(&pp, TWEAK_TYPE_WOTS_PK, 0, 42, &data),
            expected.as_bytes()[..DIGEST_LEN]
        );
    }
}
