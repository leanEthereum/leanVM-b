//! WOTS (Winternitz one-time signature) with target-sum encoding.

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

#[derive(Debug)]
pub struct WotsSecretKey {
    pub pre_images: [Digest; V],
    public_key: WotsPublicKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; V]);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct WotsSignature {
    #[serde(with = "crate::array_serialization")]
    pub chain_tips: [Digest; V],
    pub randomness: Randomness,
}

impl WotsSecretKey {
    pub fn new(pre_images: [Digest; V], public_param: &PublicParam, slot: u32) -> Self {
        Self {
            pre_images,
            public_key: WotsPublicKey(std::array::from_fn(|i| {
                iterate_hash(&pre_images[i], CHAIN_LENGTH - 1, public_param, slot, i, 0)
            })),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign_with_randomness(
        &self,
        message: &Message,
        slot: u32,
        public_param: &PublicParam,
        randomness: Randomness,
    ) -> Option<WotsSignature> {
        let encoding = wots_encode(message, slot, public_param, &randomness)?;
        Some(WotsSignature {
            chain_tips: std::array::from_fn(|i| {
                iterate_hash(&self.pre_images[i], encoding[i] as usize, public_param, slot, i, 0)
            }),
            randomness,
        })
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message: &Message,
        slot: u32,
        public_param: &PublicParam,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode(message, slot, public_param, &self.randomness)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                public_param,
                slot,
                i,
                encoding[i] as usize,
            )
        })))
    }
}

impl WotsPublicKey {
    /// The Merkle leaf: standard BLAKE3 over the tweak, public parameter, and
    /// 42 concatenated chain tips (704 bytes, 11 compressions in one chunk).
    pub fn hash(&self, public_param: &PublicParam, slot: u32) -> Digest {
        let mut data = [0u8; V * DIGEST_LEN];
        for (chunk, tip) in data.chunks_exact_mut(DIGEST_LEN).zip(&self.0) {
            chunk.copy_from_slice(tip);
        }
        tweak_hash_many(public_param, TWEAK_TYPE_WOTS_PK, 0, slot, &data)
    }
}

/// One chain step (1 compression). The position `chain_index * CHAIN_LENGTH +
/// step` identifies the edge from chain value `step` to `step + 1`.
pub fn chain_step(public_param: &PublicParam, slot: u32, chain_index: usize, step: usize, x: &Digest) -> Digest {
    let position = (chain_index * CHAIN_LENGTH + step) as u32;
    tweak_hash(public_param, TWEAK_TYPE_CHAIN, position, slot, x)
}

/// Walk chain `chain_index` for `n` steps starting at chain value `start_step`.
pub fn iterate_hash(
    a: &Digest,
    n: usize,
    public_param: &PublicParam,
    slot: u32,
    chain_index: usize,
    start_step: usize,
) -> Digest {
    (0..n).fold(*a, |acc, j| {
        chain_step(public_param, slot, chain_index, start_step + j, &acc)
    })
}

pub fn find_randomness_for_wots_encoding(
    message: &Message,
    slot: u32,
    public_param: &PublicParam,
    rng: &mut impl CryptoRng,
) -> (Randomness, [u8; V], usize) {
    let mut num_iters = 0;
    loop {
        num_iters += 1;
        let randomness: Randomness = rng.random();
        if let Some(encoding) = wots_encode(message, slot, public_param, &randomness) {
            return (randomness, encoding, num_iters);
        }
    }
}

/// The target-sum encoding. `D = MD(msg | randomness | zeros)` under the
/// encoding tweak, truncated to 16 bytes: 2 standard BLAKE3 compressions over
/// the 96-byte exact input. `D`'s two
/// little-endian 64-bit words each hold 21 chunks of 3 bits (the VM's word
/// width budgets the monomial encoding at 64 bits per word: `g^k = x^k` only
/// for `k < 64`): digit `i < 21` sits at bits `3i` of word 0, digit `i >= 21`
/// at bits `3(i-21)` of word 1. The encoding is valid iff the leftover top
/// bit of EACH word (bits 63 and 127) is zero AND the chunks sum to
/// [`TARGET_SUM`]. Grinding the top bits to zero makes each digest word
/// exactly `sum(e_i * 2^{3i})` of its 21 digits, so both words decompose into
/// the chunks with no slack term — in-circuit this is checked over GF(2^64)
/// per word by accumulating the dispatched digit literals against `8^i`
/// monomial weights (see `tests/xmss_aggregate.py`).
pub fn wots_encode(
    message: &Message,
    slot: u32,
    public_param: &PublicParam,
    randomness: &Randomness,
) -> Option<[u8; V]> {
    let mut data = [0u8; 2 * STATE_LEN];
    data[..MESSAGE_LEN].copy_from_slice(message);
    data[MESSAGE_LEN..][..RANDOMNESS_LEN].copy_from_slice(randomness);
    let digest = tweak_hash_many(public_param, TWEAK_TYPE_ENCODING, 0, slot, &data);

    if digest[7] >> 7 != 0 || digest[DIGEST_LEN - 1] >> 7 != 0 {
        return None; // the leftover top bit of each 64-bit word must be zero
    }
    let bit = |j: usize| (digest[j / 8] >> (j % 8)) & 1;
    let pos = |i: usize| if i < V / 2 { W * i } else { 64 + W * (i - V / 2) };
    let mut encoding = [0u8; V];
    for (i, e) in encoding.iter_mut().enumerate() {
        *e = (0..W).fold(0, |acc, k| acc | (bit(pos(i) + k) << k));
    }
    (encoding.iter().map(|&x| x as usize).sum::<usize>() == TARGET_SUM).then_some(encoding)
}
