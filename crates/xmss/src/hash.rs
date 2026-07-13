//! The hash layer, built entirely from one primitive — [`compress`]
//! (`H: {0,1}^512 -> {0,1}^256`, BLAKE3 of exactly 64 bytes, the VM blake3
//! opcode shape):
//!
//! - [`tweak_hash`]: one compression, `H(tweak | pp, payload | 0-pad)`. Used
//!   for chain steps (16-byte payload, zero-padded) and Merkle nodes (32
//!   bytes exactly).
//! - [`md_tweak_hash`]: Merkle-Damgard over [`compress`], with the absorbed
//!   size in the IV *in the exponent* of the VM's field generator:
//!   `IV = g^{num_bytes} (8B, GF(2^64)) | 0^24`, where `num_bytes` counts
//!   everything absorbed. The first block is `tweak | pp`, then the payload's
//!   32-byte blocks; the final state is truncated to a digest. Used for the
//!   WOTS public-key hash (42 tips = 22 blocks) and the message encoding
//!   (tweak/pp + msg + zero-padded randomness = 3 blocks). The chaining state
//!   is the FULL 32-byte output (truncating mid-chain would admit 2^64
//!   internal collisions). The exponent form makes the size element free for
//!   the VM, whose loop counters ARE g-powers.
//!
//! The 16-byte tweak makes every call site a distinct hash function
//! (multi-target separation, as in leanVM) and the public parameter separates
//! users. Payload lengths are FIXED per tweak type — the single-block hash
//! zero-pads, so unlike raw BLAKE3 it does not bind the payload length
//! itself; the multi-block hash binds its total length through the IV.
//!
//! Compression counts per call: chain step 1, Merkle node 1, message encoding
//! 3, WOTS public key 22. A full XMSS verification is a constant 157
//! compressions: 3 (encoding) + 100 (chains, fixed by the target sum) + 22
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

/// Single-block tweakable hash: one compression `H(tweak | pp, payload |
/// 0-pad)` — the state operand carries the tweak and public parameter, the
/// block the payload, zero-padded to 32 bytes (the payload length is fixed
/// per tweak type). The hash for chain steps (16-byte payload) and Merkle
/// nodes (32 bytes).
pub fn tweak_hash(
    pp: &PublicParam,
    tweak_type: u8,
    sub_position: u32,
    index: u32,
    payload: &[u8],
) -> Digest {
    assert!(payload.len() <= STATE_LEN, "single-block payload exceeds 32 bytes");
    let mut state = [0u8; STATE_LEN];
    state[..TWEAK_LEN].copy_from_slice(&make_tweak(tweak_type, sub_position, index));
    state[TWEAK_LEN..].copy_from_slice(pp);
    let mut block = [0u8; STATE_LEN];
    block[..payload.len()].copy_from_slice(payload);
    compress(&state, &block)[..DIGEST_LEN].try_into().unwrap()
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
/// public-key hash and the message encoding): `IV = g^{num_bytes} | 0^24`
/// with the total absorbed size in the exponent of the VM's field generator
/// (GF(2^64), [`gf64::g_pow_bytes`]); the first block is `tweak | pp`,
/// then `data`. Truncates the final state to a digest. Costs
/// `1 + data.len() / 32` compressions.
pub fn md_tweak_hash(
    pp: &PublicParam,
    tweak_type: u8,
    sub_position: u32,
    index: u32,
    data: &[u8],
) -> Digest {
    let num_bytes = STATE_LEN + data.len();
    let mut iv = [0u8; STATE_LEN];
    iv[..8].copy_from_slice(&crate::gf64::g_pow_bytes(num_bytes));
    let mut first = [0u8; STATE_LEN];
    first[..TWEAK_LEN].copy_from_slice(&make_tweak(tweak_type, sub_position, index));
    first[TWEAK_LEN..].copy_from_slice(pp);
    let state = compress(&iv, &first);
    md_hash(state, data)[..DIGEST_LEN].try_into().unwrap()
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
        // NOTE: the single-block hash zero-pads its payload, so it does NOT
        // bind the payload length — lengths are fixed per tweak type instead.
        let mut extended = [0u8; STATE_LEN];
        extended[..DIGEST_LEN].copy_from_slice(&x);
        assert_eq!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &extended));
    }

    #[test]
    fn md_matches_manual_chaining() {
        let pp = [9u8; PUBLIC_PARAM_LEN];
        let data = [5u8; 2 * STATE_LEN];
        // IV = g^{num_bytes} | 0^24, num_bytes = tweak/pp block + data.
        let mut iv = [0u8; STATE_LEN];
        iv[..8].copy_from_slice(&crate::gf64::g_pow_bytes(STATE_LEN + data.len()));
        let mut first = [0u8; STATE_LEN];
        first[..TWEAK_LEN].copy_from_slice(&make_tweak(TWEAK_TYPE_WOTS_PK, 0, 42));
        first[TWEAK_LEN..].copy_from_slice(&pp);
        let expected = compress(
            &compress(&compress(&iv, &first), data[..STATE_LEN].try_into().unwrap()),
            data[STATE_LEN..].try_into().unwrap(),
        );
        assert_eq!(
            md_tweak_hash(&pp, TWEAK_TYPE_WOTS_PK, 0, 42, &data),
            expected[..DIGEST_LEN]
        );
    }
}
