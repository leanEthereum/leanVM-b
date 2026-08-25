//! The tweakable hash `Th(P, tw, M) = Truncate_n(SHA3-256(tw | P | M))`, and the
//! 16-byte tweak that names one hash call in the whole structure.
//!
//! The byte string is zero-filled to whole 32-byte groups, because the VM
//! carries a value as 128-bit memory cells and can only hash whole ones. Up to
//! 64 bytes that is one `primitives::hash::hash_block`, plain SHA3-256; beyond
//! it the groups chain through `primitives::hash::hash_md`, which is what the
//! VM's 64-byte opcode can reproduce. The tweak's last two bytes carry the
//! payload length, set by the hash rather than by its caller: without it the
//! zero-fill would let a short payload and a longer zero-tailed one collide.
//!
//! Permutations per call, the input including the 32 bytes of tweak and public
//! parameter: 1 for a chain step, a Merkle node, a derived secret and an
//! encoding, 2 for the message digest, 7 for the few-time roots, and 21 for a
//! one-time leaf. A verification is 564 of them.

use crate::*;

pub const TWEAK_LEN: usize = 16;
pub type Tweak = [u8; TWEAK_LEN];

// Tweak types, the tweak's first byte, so no two kinds of call can alias.
pub const TWEAK_PRF: u8 = 0;
pub const TWEAK_CHAIN: u8 = 1;
pub const TWEAK_LEAF: u8 = 2;
pub const TWEAK_NODE: u8 = 3;
pub const TWEAK_ENC: u8 = 4;
pub const TWEAK_FTS_PRF: u8 = 5;
pub const TWEAK_FTS_LEAF: u8 = 6;
pub const TWEAK_FTS_NODE: u8 = 7;
pub const TWEAK_FTS_ROOTS: u8 = 8;
pub const TWEAK_MSG: u8 = 9;

/// `enc(t, lay, tau, p, j)`: fourteen bytes of little-endian fields, then two
/// that [`th`] fills with the payload length. `lay` is a layer of the hypertree
/// or a tree of a few-time forest, and is byte wide.
pub fn tweak(t: u8, lay: usize, tau: u32, p: u32, j: u32) -> Tweak {
    debug_assert!(lay < 256);
    let mut tw = [0u8; TWEAK_LEN];
    tw[0] = t;
    tw[1] = lay as u8;
    tw[2..6].copy_from_slice(&tau.to_le_bytes());
    tw[6..10].copy_from_slice(&p.to_le_bytes());
    tw[10..14].copy_from_slice(&j.to_le_bytes());
    tw
}

/// The longest string any call site hashes: a one-time key's `V` chain tips. On
/// the stack, because a chain step is one of these and the encoding grinds
/// thousands of them.
const CAP: usize = TWEAK_LEN + PUBLIC_PARAM_LEN + V * N;

/// `Th` over a byte payload: an encoding input or a derived secret.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    debug_assert!(TWEAK_LEN + PUBLIC_PARAM_LEN + payload.len() <= CAP);
    let mut msg = [0u8; CAP];
    let len = TWEAK_LEN + PUBLIC_PARAM_LEN + payload.len();
    msg[..TWEAK_LEN].copy_from_slice(&tweak_with_payload_len(tw, payload.len()));
    msg[TWEAK_LEN..][..PUBLIC_PARAM_LEN].copy_from_slice(pp);
    msg[TWEAK_LEN + PUBLIC_PARAM_LEN..][..payload.len()].copy_from_slice(payload);
    primitives::hash::hash_md(&msg[..len])[..N].try_into().unwrap()
}

/// The tweak as hashed: its last two bytes are the payload's length, which the
/// hash sets rather than the caller, so no call site can forget it.
pub fn tweak_with_payload_len(tw: &Tweak, payload_len: usize) -> Tweak {
    let mut out = *tw;
    out[14..].copy_from_slice(
        &u16::try_from(payload_len)
            .expect("a payload is under 64 KiB")
            .to_le_bytes(),
    );
    out
}

/// `Th` over a concatenation of digests: a Merkle node, a one-time leaf, or the
/// few-time roots.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    let payload_len = values.len() * N;
    debug_assert!(TWEAK_LEN + PUBLIC_PARAM_LEN + payload_len <= CAP);
    let mut msg = [0u8; CAP];
    msg[..TWEAK_LEN].copy_from_slice(&tweak_with_payload_len(tw, payload_len));
    msg[TWEAK_LEN..][..PUBLIC_PARAM_LEN].copy_from_slice(pp);
    for (slot, value) in msg[TWEAK_LEN + PUBLIC_PARAM_LEN..]
        .as_chunks_mut::<N>()
        .0
        .iter_mut()
        .zip(values)
    {
        *slot = *value;
    }
    primitives::hash::hash_md(&msg[..TWEAK_LEN + PUBLIC_PARAM_LEN + payload_len])[..N]
        .try_into()
        .unwrap()
}
