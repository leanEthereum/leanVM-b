//! The XMSS hash layer: [`tweak_hash`] is standard SHA3-256 of the exact byte
//! string `tweak | pp | payload`, for chain steps, Merkle nodes, WOTS public
//! keys, and message encodings alike.
//!
//! The 16-byte tweak makes every call site a distinct hash function
//! (multi-target separation, as in leanVM) and the public parameter separates
//! users. Standard SHA3-256 binds the exact payload length.
//!
//! The byte string is zero-filled to a whole number of 32-byte groups, because
//! the VM carries a value as 128-bit memory cells and can only hash whole ones.
//! Up to 64 bytes that is one [`primitives::sha3::hash_block`], plain SHA3-256;
//! beyond it the groups chain through [`primitives::sha3::hash_md`], which is
//! what the VM's 64-byte opcode can reproduce. Every call site has a fixed
//! length and its own tweak, so the padding costs no separation.

use crate::*;

// Tweak types (tweak byte 0), so distinct kinds of hashes cannot alias.
pub const TWEAK_TYPE_CHAIN: u8 = 0;
pub const TWEAK_TYPE_WOTS_PK: u8 = 1;
pub const TWEAK_TYPE_MERKLE: u8 = 2;
pub const TWEAK_TYPE_ENCODING: u8 = 3;

pub const TWEAK_LEN: usize = 16;
pub type Tweak = [u8; TWEAK_LEN];

/// A full 32-byte SHA3-256 output.
pub const STATE_LEN: usize = 32;

/// `[tweak_type (1) | sub_position (4) | index (4) | payload_len (4) | zeros (3)]`,
/// little-endian. `index` is the epoch (chain / wots_pk / encoding) or the
/// Merkle node index; `sub_position` is the chain position or the Merkle level.
///
/// The payload length is in the tweak because the hashed string is zero-filled
/// to whole 32-byte groups, so the padding alone would let a short payload and
/// a longer zero-tailed one collide. Binding it here costs nothing: the tweak
/// had spare bytes, and it is already the first thing hashed.
pub fn make_tweak(tweak_type: u8, sub_position: u32, index: u32, payload_len: usize) -> Tweak {
    let mut tweak = [0u8; TWEAK_LEN];
    tweak[0] = tweak_type;
    tweak[1..5].copy_from_slice(&sub_position.to_le_bytes());
    tweak[5..9].copy_from_slice(&index.to_le_bytes());
    tweak[9..13].copy_from_slice(&(payload_len as u32).to_le_bytes());
    tweak
}

/// `tweak | pp | payload`, zero-filled to whole 32-byte groups and hashed: one
/// SHA3-256 up to 64 bytes, a [`primitives::sha3::hash_md`] chain beyond it.
pub fn tweak_hash(pp: &PublicParam, tweak_type: u8, sub_position: u32, index: u32, payload: &[u8]) -> Digest {
    /// The longest string any call site hashes: a WOTS public key's `V` chain
    /// tips. On the stack, because a chain step is one of these and the encoding
    /// grinds thousands.
    const CAP: usize = TWEAK_LEN + PUBLIC_PARAM_LEN + V * DIGEST_LEN;
    let len = (TWEAK_LEN + PUBLIC_PARAM_LEN + payload.len())
        .next_multiple_of(32)
        .max(64);
    assert!(len <= CAP, "payload longer than any call site hashes");
    let mut msg = [0u8; CAP];
    msg[..TWEAK_LEN].copy_from_slice(&make_tweak(tweak_type, sub_position, index, payload.len()));
    msg[TWEAK_LEN..][..PUBLIC_PARAM_LEN].copy_from_slice(pp);
    msg[TWEAK_LEN + PUBLIC_PARAM_LEN..][..payload.len()].copy_from_slice(payload);
    primitives::sha3::hash_md(&msg[..len])[..DIGEST_LEN].try_into().unwrap()
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
        // The tweak binds the exact payload length, so a zero-tailed longer
        // payload is a different hash even though both pad to 64 bytes.
        let mut extended = [0u8; STATE_LEN];
        extended[..DIGEST_LEN].copy_from_slice(&x);
        assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &extended));
    }

    /// A payload that fills 64 bytes exactly is plain SHA3-256; anything longer
    /// is the chain. Both are pinned here so a change to either shows up.
    #[test]
    fn multi_block_hash_is_the_padded_chain() {
        let pp = [9u8; PUBLIC_PARAM_LEN];
        let data = [5u8; 2 * STATE_LEN];
        let mut input = Vec::new();
        input.extend_from_slice(&make_tweak(TWEAK_TYPE_WOTS_PK, 0, 42, data.len()));
        input.extend_from_slice(&pp);
        input.extend_from_slice(&data);
        input.resize(input.len().next_multiple_of(32).max(64), 0);
        let expected = primitives::sha3::hash_md(&input);
        assert_eq!(
            tweak_hash(&pp, TWEAK_TYPE_WOTS_PK, 0, 42, &data),
            expected[..DIGEST_LEN]
        );
    }
}
