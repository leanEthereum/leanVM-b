//! The hash layer: plain BLAKE3 for the single-block hashes, and a
//! Merkle-Damgard mode for the multi-block ones.
//!
//! - [`tweak_hash`]: `blake3(tweak | pp | payload)` truncated to a 16-byte
//!   [`Digest`]. Used for chain steps (48-byte input) and Merkle nodes (64
//!   bytes).
//! - [`md_tweak_hash`]: Merkle-Damgard over [`compress`]
//!   (`H: {0,1}^512 -> {0,1}^256`, BLAKE3 of exactly 64 bytes, the VM blake3
//!   opcode shape). The 32-byte state starts at `IV = tweak | pp` and absorbs
//!   32-byte blocks; the final state is truncated to a digest. Used for the
//!   WOTS public-key hash (42 tips = 672 bytes = 21 blocks) and the message
//!   encoding (msg block + zero-padded randomness block). The chaining state
//!   is the FULL 32-byte output (truncating mid-chain would admit 2^64
//!   internal collisions).
//!
//! The 16-byte tweak makes every call site a distinct hash function
//! (multi-target separation, as in leanVM) and the public parameter separates
//! users. Input lengths are fixed per tweak type, and BLAKE3 itself binds the
//! input length, so no length field is needed.
//!
//! Compression counts per call: chain step 1, Merkle node 1, message encoding
//! 2, WOTS public key 21. A full XMSS verification is a constant 155
//! compressions: 2 (encoding) + 100 (chains, fixed by the target sum) + 21
//! (tips) + 32 (Merkle path).

use crate::*;

// Tweak types (tweak byte 0), so distinct kinds of hashes cannot alias.
pub const TWEAK_TYPE_CHAIN: u8 = 0;
pub const TWEAK_TYPE_WOTS_PK: u8 = 1;
pub const TWEAK_TYPE_MERKLE: u8 = 2;
pub const TWEAK_TYPE_ENCODING: u8 = 3;

pub const TWEAK_LEN: usize = 16;
pub type Tweak = [u8; TWEAK_LEN];

/// The Merkle-Damgard chaining state / block: a full 32-byte BLAKE3 output.
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

/// Plain BLAKE3, truncated: `blake3(tweak | pp | payload)[..16]`. The hash for
/// the single-block inputs: chain steps and Merkle nodes.
pub fn tweak_hash(
    pp: &PublicParam,
    tweak_type: u8,
    sub_position: u32,
    index: u32,
    payload: &[u8],
) -> Digest {
    let mut h = blake3::Hasher::new();
    h.update(&make_tweak(tweak_type, sub_position, index));
    h.update(pp);
    h.update(payload);
    h.finalize().as_bytes()[..DIGEST_LEN].try_into().unwrap()
}

/// The MD primitive: `H: {0,1}^512 -> {0,1}^256`, BLAKE3 of 64 bytes (one
/// internal compression; the VM blake3 opcode shape).
#[inline]
pub fn compress(state: &State, block: &State) -> State {
    let mut input = [0u8; 2 * STATE_LEN];
    input[..STATE_LEN].copy_from_slice(state);
    input[STATE_LEN..].copy_from_slice(block);
    *blake3::hash(&input).as_bytes()
}

/// Merkle-Damgard over 32-byte blocks: `state <- compress(state, block)`,
/// starting from `iv`. `data` must be a multiple of 32 bytes.
pub fn md_hash(iv: State, data: &[u8]) -> State {
    assert!(data.len().is_multiple_of(STATE_LEN));
    data.chunks_exact(STATE_LEN)
        .fold(iv, |state, chunk| compress(&state, chunk.try_into().unwrap()))
}

/// The Merkle-Damgard tweakable hash, for the multi-block inputs (the WOTS
/// public-key hash and the message encoding): `IV = tweak | pp`, absorb
/// `data`, truncate the final state to a digest. Costs `data.len() / 32`
/// compressions.
pub fn md_tweak_hash(
    pp: &PublicParam,
    tweak_type: u8,
    sub_position: u32,
    index: u32,
    data: &[u8],
) -> Digest {
    let mut iv = [0u8; STATE_LEN];
    iv[..TWEAK_LEN].copy_from_slice(&make_tweak(tweak_type, sub_position, index));
    iv[TWEAK_LEN..].copy_from_slice(pp);
    md_hash(iv, data)[..DIGEST_LEN].try_into().unwrap()
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
        // BLAKE3 binds the payload length: zero-extension changes the hash.
        let mut extended = [0u8; STATE_LEN];
        extended[..DIGEST_LEN].copy_from_slice(&x);
        assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &extended));
    }

    #[test]
    fn md_matches_manual_chaining() {
        let pp = [9u8; PUBLIC_PARAM_LEN];
        let data = [5u8; 2 * STATE_LEN];
        let mut iv = [0u8; STATE_LEN];
        iv[..TWEAK_LEN].copy_from_slice(&make_tweak(TWEAK_TYPE_WOTS_PK, 0, 42));
        iv[TWEAK_LEN..].copy_from_slice(&pp);
        let expected = compress(
            &compress(&iv, data[..STATE_LEN].try_into().unwrap()),
            data[STATE_LEN..].try_into().unwrap(),
        );
        assert_eq!(
            md_tweak_hash(&pp, TWEAK_TYPE_WOTS_PK, 0, 42, &data),
            expected[..DIGEST_LEN]
        );
    }
}
