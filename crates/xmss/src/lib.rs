//! XMSS over BLAKE3 (inspired by leanVM's `xmss` crate, byte-oriented).
//!
//! The single-block hashes (chain steps, Merkle nodes) are plain BLAKE3 of
//! `tweak | pp | payload`, truncated to n = 128 bits ([`tweak_hash`]). The
//! multi-block inputs (the WOTS public key, the message encoding) are hashed
//! with a Merkle-Damgard mode over 64-byte BLAKE3 compressions
//! ([`md_tweak_hash`]); see [`hash`] for the constructions and per-call
//! compression counts.

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

pub mod gf64;
mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod xmss;
pub use xmss::*;

/// n = 128 bits.
pub const DIGEST_LEN: usize = 16;
pub type Digest = [u8; DIGEST_LEN];
pub type PublicParam = [u8; PUBLIC_PARAM_LEN];
pub type Randomness = [u8; RANDOMNESS_LEN];
/// The message to sign (a 256-bit message hash).
pub type Message = [u8; MESSAGE_LEN];

// WOTS
pub const V: usize = 42; // number of hash chains
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W; // 8
/// Chain hashes the VERIFIER walks, summed over all chains: `sum(chain_length -
/// 1 - e_i)`. Constant because the encoding sum is fixed to [`TARGET_SUM`].
pub const NUM_CHAIN_HASHES: usize = 100;
/// A WOTS encoding `(e_0, .., e_{v-1})` is valid iff every `e_i < CHAIN_LENGTH`,
/// `sum(e_i) = TARGET_SUM`, and the 2 leftover digest bits are zero (see
/// [`wots_encode`]). The signer grinds the randomness until the encoding is
/// valid (no checksum chains). 194 sits above the mean (147) so verification
/// walks fewer chain steps; grinding is ~2^14 encode attempts (~2^12 for the
/// sum, 2^2 for the zero bits).
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES; // 194
pub const RANDOMNESS_LEN: usize = 24;
pub const MESSAGE_LEN: usize = 32;
pub const PUBLIC_PARAM_LEN: usize = 16;

// XMSS
/// Merkle tree height: a key is valid for up to `2^32` slots.
pub const LOG_LIFETIME: usize = 32;

/// Serialized sizes (exact under bincode: fixed arrays, no length prefixes).
pub const WOTS_SIG_SIZE: usize = RANDOMNESS_LEN + V * DIGEST_LEN; // 696
pub const XMSS_SIG_SIZE: usize = WOTS_SIG_SIZE + LOG_LIFETIME * DIGEST_LEN; // 1208
pub const PUB_KEY_FLAT_SIZE: usize = DIGEST_LEN + PUBLIC_PARAM_LEN; // 32

// The encoding uses v*w = 126 of the digest's 128 bits, 21 digits per 64-bit
// word (the VM's word width); the leftover top bit of each word is ground to
// zero, so each digest word decomposes exactly into its 21 chunks.
const _: () = assert!(V * W + 2 == DIGEST_LEN * 8);
const _: () = assert!((V / 2) * W + 1 == 64);

/// Serde for `[T; N]` with N > 32 (serde only derives arrays up to 32):
/// serialized as a fixed-length tuple, exactly like the native array impls.
pub mod array_serialization {
    use serde::de::{Error, SeqAccess, Visitor};
    use serde::ser::SerializeTuple;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::marker::PhantomData;

    pub fn serialize<S: Serializer, T: Serialize, const N: usize>(
        data: &[T; N],
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        let mut tup = ser.serialize_tuple(N)?;
        for elem in data {
            tup.serialize_element(elem)?;
        }
        tup.end()
    }

    struct ArrayVisitor<T, const N: usize>(PhantomData<T>);

    impl<'de, T: Deserialize<'de> + Copy + Default, const N: usize> Visitor<'de> for ArrayVisitor<T, N> {
        type Value = [T; N];

        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "an array of length {N}")
        }

        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<[T; N], A::Error> {
            let mut out = [T::default(); N];
            for (i, slot) in out.iter_mut().enumerate() {
                *slot = seq.next_element()?.ok_or_else(|| Error::invalid_length(i, &self))?;
            }
            Ok(out)
        }
    }

    pub fn deserialize<'de, D, T, const N: usize>(de: D) -> Result<[T; N], D::Error>
    where
        D: Deserializer<'de>,
        T: Deserialize<'de> + Copy + Default,
    {
        de.deserialize_tuple(N, ArrayVisitor::<T, N>(PhantomData))
    }
}
