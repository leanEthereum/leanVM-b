//! The tweakable hash `Th(P, tw, M) = Truncate_n(BLAKE2s(tw | P | M))`, and the
//! 16-byte tweak that names one hash call in the whole structure.
//!
//! Compressions per call, the input including the 32 bytes of tweak and public
//! parameter: 1 for a chain step, a Merkle node, a derived secret and an
//! encoding, 2 for the message digest, 4 for the few-time roots, and 11 for a
//! one-time leaf.

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

/// `enc(t, lay, tau, p, j)`: fourteen bytes of little-endian fields and two of
/// padding. `lay` is a layer of the hypertree or a tree of a few-time forest,
/// and is byte wide.
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

/// `Th` over a byte payload: an encoding input or a derived secret.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    let mut hasher = primitives::hash::Hasher::new();
    hasher.update(tw).update(pp).update(payload);
    hasher.finalize()[..N].try_into().unwrap()
}

/// `Th` over a concatenation of digests: a Merkle node, a one-time leaf, or the
/// few-time roots.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    let mut hasher = primitives::hash::Hasher::new();
    hasher.update(tw).update(pp);
    for value in values {
        hasher.update(value);
    }
    hasher.finalize()[..N].try_into().unwrap()
}
