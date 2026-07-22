//! XMSS: a 4-ary Merkle tree of `2^LOG_LIFETIME` WOTS public-key hashes.
//!
//! Mirrors leanVM's memory-optimized secret key: for a range of R = slot_end -
//! slot_start + 1 slots, storage is O(sqrt(R) + LOG_LIFETIME) instead of O(R).
//! The key stores the top tree (in-range band plus a thin spine) and one cached
//! bottom subtree, cut at `split_level = ceil(log2(R)) / 2`. Out-of-range nodes
//! are deterministic `gen_random_node` fillers.

use std::sync::Mutex;

use rand::CryptoRng;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey {
    pub(crate) slot_start: u32, // inclusive
    pub(crate) slot_end: u32,   // inclusive
    pub(crate) public_param: PublicParam,
    pub(crate) seed: [u8; 32],
    pub(crate) split_level: usize, // bottom-subtree height (2^split_level leaves each)
    // top[l - split_level] = level-l nodes for indices [slot_start >> l, slot_end >> l]
    pub(crate) top: Vec<Vec<Digest>>,
    pub(crate) cache: Mutex<Option<BottomSubtree>>,
}

/// Bottom subtree covering the last-signed slot; its leaf range is derived from
/// `subtree_index`.
#[derive(Debug)]
pub(crate) struct BottomSubtree {
    subtree_index: u64, // = slot >> split_level
    layers: Vec<Vec<Digest>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    /// Three siblings per quaternary level, ordered by child position with the
    /// current node omitted, level-major from leaf to root.
    #[serde(with = "array_serialization")]
    pub merkle_proof: [Digest; MERKLE_PROOF_LEN],
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
    pub public_param: PublicParam,
}

impl XmssPublicKey {
    pub fn flatten(&self) -> [u8; PUB_KEY_FLAT_SIZE] {
        let mut out = [0u8; PUB_KEY_FLAT_SIZE];
        out[..DIGEST_LEN].copy_from_slice(&self.merkle_root);
        out[DIGEST_LEN..].copy_from_slice(&self.public_param);
        out
    }
}

// Prover-side PRF domains (secret derivation and filler nodes; never on the
// verification path, so not restricted to the 64-to-32 primitive).
const PRF_DOMAINSEP_WOTS_SECRET_KEY: u32 = 1000;
const PRF_DOMAINSEP_PUBLIC_PARAM: u32 = 1001;
const PRF_DOMAINSEP_RANDOM_NODE: u32 = 1002;

fn prf(seed: &[u8; 32], domain: u32, a: u64, b: u64) -> Digest {
    let mut msg = [0u8; 20];
    msg[..4].copy_from_slice(&domain.to_le_bytes());
    msg[4..12].copy_from_slice(&a.to_le_bytes());
    msg[12..20].copy_from_slice(&b.to_le_bytes());
    blake3::keyed_hash(seed, &msg).as_bytes()[..DIGEST_LEN].try_into().unwrap()
}

fn gen_wots_secret_key(seed: &[u8; 32], slot: u32, public_param: &PublicParam) -> WotsSecretKey {
    let pre_images =
        std::array::from_fn(|i| prf(seed, PRF_DOMAINSEP_WOTS_SECRET_KEY, slot as u64, i as u64));
    WotsSecretKey::new(pre_images, public_param, slot)
}

fn gen_public_param(seed: &[u8; 32]) -> PublicParam {
    prf(seed, PRF_DOMAINSEP_PUBLIC_PARAM, 0, 0)
}

/// Deterministic pseudo-random digest for an out-of-range tree node.
fn gen_random_node(seed: &[u8; 32], level: usize, index: u64) -> Digest {
    prf(seed, PRF_DOMAINSEP_RANDOM_NODE, level as u64, index)
}

/// Quaternary Merkle parent at `level` (one compression: four 16-byte children
/// fill the 64-byte keyed-BLAKE3 message block).
pub fn merkle_node(
    public_param: &PublicParam,
    level: usize,
    index: u64,
    children: &[Digest; MERKLE_ARITY],
) -> Digest {
    let mut data = [0u8; MERKLE_ARITY * DIGEST_LEN];
    for (dst, child) in data.chunks_exact_mut(DIGEST_LEN).zip(children) {
        dst.copy_from_slice(child);
    }
    tweak_hash(public_param, TWEAK_TYPE_MERKLE, level as u32, index as u32, &data)
}

fn log4_ceil(n: u64) -> usize {
    (n.next_power_of_two().trailing_zeros() as usize).div_ceil(2)
}

/// Level-0 layer: WOTS public-key hashes for the in-range leaves `[lo, hi]`.
fn leaf_layer(seed: &[u8; 32], public_param: &PublicParam, lo: u64, hi: u64) -> Vec<Digest> {
    (lo..=hi)
        .into_par_iter()
        .map(|slot| {
            gen_wots_secret_key(seed, slot as u32, public_param)
                .public_key()
                .hash(public_param, slot as u32)
        })
        .collect()
}

/// Build levels `(from_level+1)..=to_level` onto `layers`; out-of-range
/// children use `gen_random_node`.
fn build_up(
    seed: &[u8; 32],
    public_param: &PublicParam,
    layers: &mut Vec<Vec<Digest>>,
    lo: u64,
    hi: u64,
    from_level: usize,
    to_level: usize,
) {
    for level in (from_level + 1)..=to_level {
        let (base, top) = (lo >> (2 * level), hi >> (2 * level));
        let (prev_base, prev_top) = (lo >> (2 * (level - 1)), hi >> (2 * (level - 1)));
        let prev = layers.last().unwrap();
        let nodes: Vec<Digest> = (base..=top)
            .into_par_iter()
            .map(|i| {
                let child = |idx: u64| {
                    if idx >= prev_base && idx <= prev_top {
                        prev[(idx - prev_base) as usize]
                    } else {
                        gen_random_node(seed, level - 1, idx)
                    }
                };
                let children = std::array::from_fn(|j| child(MERKLE_ARITY as u64 * i + j as u64));
                merkle_node(public_param, level, i, &children)
            })
            .collect();
        layers.push(nodes);
    }
}

/// In-range leaf bounds of the bottom subtree with the given index.
fn subtree_bounds(slot_start: u64, slot_end: u64, split_level: usize, subtree_index: u64) -> (u64, u64) {
    (
        slot_start.max(subtree_index << (2 * split_level)),
        slot_end.min(((subtree_index + 1) << (2 * split_level)) - 1),
    )
}

/// Build Merkle layers `0..=to_level` for the in-range leaves `[lo, hi]`.
fn build_subtree_layers(
    seed: &[u8; 32],
    public_param: &PublicParam,
    lo: u64,
    hi: u64,
    to_level: usize,
) -> Vec<Vec<Digest>> {
    let mut layers = vec![leaf_layer(seed, public_param, lo, hi)];
    build_up(seed, public_param, &mut layers, lo, hi, 0, to_level);
    layers
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssKeyGenError {
    InvalidRange,
}

pub fn xmss_key_gen(
    seed: [u8; 32],
    slot_start: u32,
    slot_end: u32,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if slot_start > slot_end {
        return Err(XmssKeyGenError::InvalidRange);
    }
    let public_param = gen_public_param(&seed);
    let (lo, hi) = (slot_start as u64, slot_end as u64);

    // ~sqrt(R) leaves per bottom subtree, measured in quaternary levels.
    let split_level = log4_ceil(hi - lo + 1).div_ceil(2);

    // Roots of each bottom subtree, built one at a time so peak memory stays O(sqrt(R)).
    let first_subtree = lo >> (2 * split_level);
    let last_subtree = hi >> (2 * split_level);
    let root_layer: Vec<Digest> = (first_subtree..=last_subtree)
        .into_par_iter()
        .map(|s| {
            let (in_lo, in_hi) = subtree_bounds(lo, hi, split_level, s);
            build_subtree_layers(&seed, &public_param, in_lo, in_hi, split_level)[split_level][0]
        })
        .collect();

    // Top part: quaternary levels split_level..=MERKLE_HEIGHT.
    let mut top = vec![root_layer];
    build_up(&seed, &public_param, &mut top, lo, hi, split_level, MERKLE_HEIGHT);

    let pub_key = XmssPublicKey {
        merkle_root: top.last().unwrap()[0],
        public_param,
    };
    let secret_key = XmssSecretKey {
        slot_start,
        slot_end,
        public_param,
        seed,
        split_level,
        top,
        cache: Mutex::new(None),
    };
    Ok((secret_key, pub_key))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssSignatureError {
    SlotOutOfRange,
    InvalidRandomness,
}

/// WARNING: XMSS is a stateful signature scheme, never sign twice with the same
/// `slot`. (Even signing the same message twice at the same slot is insecure,
/// because the signature randomness is drawn fresh.)
pub fn xmss_sign(
    rng: &mut impl CryptoRng,
    secret_key: &XmssSecretKey,
    message: &Message,
    slot: u32,
) -> Result<XmssSignature, XmssSignatureError> {
    if slot < secret_key.slot_start || slot > secret_key.slot_end {
        return Err(XmssSignatureError::SlotOutOfRange);
    }
    let (randomness, ..) =
        find_randomness_for_wots_encoding(message, slot, &secret_key.public_param, rng);
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, slot, &secret_key.public_param);
    let wots_signature = wots_secret_key
        .sign_with_randomness(message, slot, &secret_key.public_param, randomness)
        .ok_or(XmssSignatureError::InvalidRandomness)?;

    // Cache the bottom subtree covering `slot` (reused across its
    // 4^split_level slots), then read the authentication path.
    let subtree_index = (slot as u64) >> (2 * secret_key.split_level);
    let mut cache = secret_key.cache.lock().unwrap();
    if cache.as_ref().is_none_or(|s| s.subtree_index != subtree_index) {
        *cache = Some(secret_key.build_bottom_subtree(subtree_index));
    }
    let sub = cache.as_ref().unwrap();
    let merkle_proof = std::array::from_fn(|proof_index| {
        let level = proof_index / MERKLE_SIBLINGS;
        let sibling_ordinal = proof_index % MERKLE_SIBLINGS;
        let node_index = (slot as u64) >> (2 * level);
        let child_position = (node_index % MERKLE_ARITY as u64) as usize;
        let sibling_position = if sibling_ordinal < child_position {
            sibling_ordinal
        } else {
            sibling_ordinal + 1
        };
        let sibling_index = node_index - child_position as u64 + sibling_position as u64;
        secret_key.merkle_node_at(level, sibling_index, sub)
    });
    drop(cache);
    Ok(XmssSignature {
        wots_signature,
        merkle_proof,
    })
}

impl XmssSecretKey {
    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            merkle_root: self.top.last().unwrap()[0],
            public_param: self.public_param,
        }
    }

    /// (Re)build the bottom subtree with the given index.
    fn build_bottom_subtree(&self, subtree_index: u64) -> BottomSubtree {
        let (lo, hi) = subtree_bounds(
            self.slot_start as u64,
            self.slot_end as u64,
            self.split_level,
            subtree_index,
        );
        let layers = build_subtree_layers(&self.seed, &self.public_param, lo, hi, self.split_level);
        BottomSubtree { subtree_index, layers }
    }

    /// Authentication-path node at `level`: from the top part, the cached
    /// subtree, or `gen_random_node`.
    fn merkle_node_at(&self, level: usize, node_index: u64, sub: &BottomSubtree) -> Digest {
        let (lo, hi, level_base, layers) = if level >= self.split_level {
            (self.slot_start as u64, self.slot_end as u64, self.split_level, &self.top)
        } else {
            let (lo, hi) = subtree_bounds(
                self.slot_start as u64,
                self.slot_end as u64,
                self.split_level,
                sub.subtree_index,
            );
            (lo, hi, 0, &sub.layers)
        };
        let base = lo >> (2 * level);
        if node_index >= base && node_index <= (hi >> (2 * level)) {
            layers[level - level_base][(node_index - base) as usize]
        } else {
            gen_random_node(&self.seed, level, node_index)
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssVerifyError {
    InvalidWots,
    InvalidMerklePath,
}

pub fn xmss_verify(
    pub_key: &XmssPublicKey,
    message: &Message,
    signature: &XmssSignature,
    slot: u32,
) -> Result<(), XmssVerifyError> {
    let wots_public_key = signature
        .wots_signature
        .recover_public_key(message, slot, &pub_key.public_param)
        .ok_or(XmssVerifyError::InvalidWots)?;
    let mut current = wots_public_key.hash(&pub_key.public_param, slot);
    for level in 0..MERKLE_HEIGHT {
        let child_position = ((slot as u64 >> (2 * level)) & 3) as usize;
        let mut siblings = signature.merkle_proof
            [level * MERKLE_SIBLINGS..(level + 1) * MERKLE_SIBLINGS]
            .iter();
        let children = std::array::from_fn(|position| {
            if position == child_position {
                current
            } else {
                *siblings.next().unwrap()
            }
        });
        let parent_index = (slot as u64) >> (2 * (level + 1));
        current = merkle_node(&pub_key.public_param, level + 1, parent_index, &children);
    }
    if current == pub_key.merkle_root {
        Ok(())
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
