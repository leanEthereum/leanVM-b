//! XMSS: a Merkle tree of `2^LOG_LIFETIME` WOTS public-key hashes.
//!
//! Mirrors leanVM's memory-optimized secret key: for a range of R = epoch_end -
//! epoch_start + 1 epochs, storage is O(sqrt(R) + LOG_LIFETIME) instead of O(R).
//! The key stores the top tree (in-range band plus a thin spine) and one cached
//! bottom subtree, cut at `split_level = ceil(log2(R)) / 2`. Out-of-range nodes
//! are deterministic `gen_random_node` fillers.

use std::sync::Mutex;

use rand::CryptoRng;
use serde::{Deserialize, Serialize};

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey {
    pub(crate) epoch_start: u32, // inclusive
    pub(crate) epoch_end: u32,   // inclusive
    pub(crate) public_param: PublicParam,
    pub(crate) seed: [u8; 32],
    pub(crate) split_level: usize, // bottom-subtree height (2^split_level leaves each)
    // top[l - split_level] = level-l nodes for indices [epoch_start >> l, epoch_end >> l]
    pub(crate) top: Vec<Vec<Digest>>,
    pub(crate) cache: Mutex<Option<BottomSubtree>>,
}

/// Bottom subtree covering the last-signed epoch; its leaf range is derived from
/// `subtree_index`.
#[derive(Debug)]
pub(crate) struct BottomSubtree {
    subtree_index: u64, // = epoch >> split_level
    layers: Vec<Vec<Digest>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub merkle_proof: [Digest; LOG_LIFETIME],
}

/// Ordered lexicographically on `flatten()`, which is what an aggregate's signer
/// set is sorted and deduplicated by.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    primitives::blake2s::keyed_hash(seed, &msg)[..DIGEST_LEN]
        .try_into()
        .unwrap()
}

fn gen_wots_secret_key(seed: &[u8; 32], epoch: u32) -> WotsSecretKey {
    let pre_images = std::array::from_fn(|i| prf(seed, PRF_DOMAINSEP_WOTS_SECRET_KEY, epoch as u64, i as u64));
    WotsSecretKey::new(pre_images)
}

fn gen_public_param(seed: &[u8; 32]) -> PublicParam {
    prf(seed, PRF_DOMAINSEP_PUBLIC_PARAM, 0, 0)
}

/// Deterministic pseudo-random digest for an out-of-range tree node.
fn gen_random_node(seed: &[u8; 32], level: usize, index: u64) -> Digest {
    prf(seed, PRF_DOMAINSEP_RANDOM_NODE, level as u64, index)
}

/// Merkle parent at `level` (1 compression: both children fill one block).
fn merkle_node(public_param: &PublicParam, level: usize, index: u64, left: &Digest, right: &Digest) -> Digest {
    let mut data = [0u8; 2 * DIGEST_LEN];
    data[..DIGEST_LEN].copy_from_slice(left);
    data[DIGEST_LEN..].copy_from_slice(right);
    tweak_hash(public_param, TWEAK_TYPE_MERKLE, level as u32, index as u32, &data)
}

fn log2_ceil(n: u64) -> usize {
    n.next_power_of_two().trailing_zeros() as usize
}

/// Level-0 layer: WOTS public-key hashes for the in-range leaves `[lo, hi]`.
///
/// Sequential: this runs once per bottom subtree, and the subtrees are what
/// [`xmss_key_gen`] fans out over.
fn leaf_layer(seed: &[u8; 32], public_param: &PublicParam, lo: u64, hi: u64) -> Vec<Digest> {
    (lo..=hi)
        .map(|epoch| {
            gen_wots_secret_key(seed, epoch as u32)
                .public_key(public_param, epoch as u32)
                .hash(public_param, epoch as u32)
        })
        .collect()
}

/// Build levels `(from_level+1)..=to_level` onto `layers`; out-of-range children
/// use `gen_random_node`.
///
/// Sequential: each level depends on the one below it, and every level here is at
/// most `O(sqrt(R))` wide, whether it is a bottom subtree's levels or the top part
/// built from the subtree roots.
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
        let (base, top) = (lo >> level, hi >> level);
        let (prev_base, prev_top) = (lo >> (level - 1), hi >> (level - 1));
        let prev = layers.last().unwrap();
        let nodes: Vec<Digest> = (base..=top)
            .map(|i| {
                let child = |idx: u64| {
                    if idx >= prev_base && idx <= prev_top {
                        prev[(idx - prev_base) as usize]
                    } else {
                        gen_random_node(seed, level - 1, idx)
                    }
                };
                merkle_node(public_param, level, i, &child(2 * i), &child(2 * i + 1))
            })
            .collect();
        layers.push(nodes);
    }
}

/// In-range leaf bounds of the bottom subtree with the given index.
fn subtree_bounds(epoch_start: u64, epoch_end: u64, split_level: usize, subtree_index: u64) -> (u64, u64) {
    (
        epoch_start.max(subtree_index << split_level),
        epoch_end.min(((subtree_index + 1) << split_level) - 1),
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
    epoch_start: u32,
    epoch_end: u32,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if epoch_start > epoch_end {
        return Err(XmssKeyGenError::InvalidRange);
    }
    let public_param = gen_public_param(&seed);
    let (lo, hi) = (epoch_start as u64, epoch_end as u64);

    // ~sqrt(R) leaves per bottom subtree; always <= LOG_LIFETIME/2.
    let split_level = log2_ceil(hi - lo + 1).div_ceil(2);

    // The bottom subtrees are the only fan-out in key generation: `O(sqrt(R))` of
    // them, each independent, each holding only its own `O(sqrt(R))` layers, so
    // peak memory stays `O(sqrt(R))` and one flat dispatch covers the whole tree.
    // Everything below this is sequential by construction.
    let first_subtree = lo >> split_level;
    let last_subtree = hi >> split_level;
    let root_layer: Vec<Digest> = parallel::map_collect((last_subtree - first_subtree + 1) as usize, |i| {
        let subtree = first_subtree + i as u64;
        let (in_lo, in_hi) = subtree_bounds(lo, hi, split_level, subtree);
        build_subtree_layers(&seed, &public_param, in_lo, in_hi, split_level)[split_level][0]
    });

    // Top part: levels split_level..=LOG_LIFETIME.
    let mut top = vec![root_layer];
    build_up(&seed, &public_param, &mut top, lo, hi, split_level, LOG_LIFETIME);

    let pub_key = XmssPublicKey {
        merkle_root: top.last().unwrap()[0],
        public_param,
    };
    let secret_key = XmssSecretKey {
        epoch_start,
        epoch_end,
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
    EpochOutOfRange,
}

/// WARNING: XMSS is a stateful signature scheme, never sign twice with the same
/// `epoch`. (Even signing the same message twice at the same epoch is insecure,
/// because the signature randomness is drawn fresh.)
pub fn xmss_sign(
    rng: &mut impl CryptoRng,
    secret_key: &XmssSecretKey,
    message: &Message,
    epoch: u32,
) -> Result<XmssSignature, XmssSignatureError> {
    if epoch < secret_key.epoch_start || epoch > secret_key.epoch_end {
        return Err(XmssSignatureError::EpochOutOfRange);
    }
    let (randomness, encoding, _) = find_randomness_for_wots_encoding(message, epoch, &secret_key.public_param, rng);
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, epoch);
    let wots_signature = wots_secret_key.sign(&encoding, randomness, epoch, &secret_key.public_param);

    // Cache the bottom subtree covering `epoch` (reused across its 2^split_level
    // epochs), then read the authentication path.
    let subtree_index = (epoch as u64) >> secret_key.split_level;
    let mut cache = secret_key.cache.lock().unwrap();
    if cache.as_ref().is_none_or(|s| s.subtree_index != subtree_index) {
        *cache = Some(secret_key.build_bottom_subtree(subtree_index));
    }
    let sub = cache.as_ref().unwrap();
    let merkle_proof = std::array::from_fn(|level| {
        let neighbour_index = ((epoch as u64) >> level) ^ 1;
        secret_key.merkle_sibling(level, neighbour_index, sub)
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
            self.epoch_start as u64,
            self.epoch_end as u64,
            self.split_level,
            subtree_index,
        );
        let layers = build_subtree_layers(&self.seed, &self.public_param, lo, hi, self.split_level);
        BottomSubtree { subtree_index, layers }
    }

    /// Authentication-path sibling at `level`: from the top part, the cached
    /// subtree, or `gen_random_node`.
    fn merkle_sibling(&self, level: usize, neighbour_index: u64, sub: &BottomSubtree) -> Digest {
        let (lo, hi, level_base, layers) = if level >= self.split_level {
            (
                self.epoch_start as u64,
                self.epoch_end as u64,
                self.split_level,
                &self.top,
            )
        } else {
            let (lo, hi) = subtree_bounds(
                self.epoch_start as u64,
                self.epoch_end as u64,
                self.split_level,
                sub.subtree_index,
            );
            (lo, hi, 0, &sub.layers)
        };
        let base = lo >> level;
        if neighbour_index >= base && neighbour_index <= (hi >> level) {
            layers[level - level_base][(neighbour_index - base) as usize]
        } else {
            gen_random_node(&self.seed, level, neighbour_index)
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
    epoch: u32,
) -> Result<(), XmssVerifyError> {
    let wots_public_key = signature
        .wots_signature
        .recover_public_key(message, epoch, &pub_key.public_param)
        .ok_or(XmssVerifyError::InvalidWots)?;
    let mut current = wots_public_key.hash(&pub_key.public_param, epoch);
    for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
        let is_left = ((epoch as u64 >> level) & 1) == 0;
        let parent_index = (epoch as u64) >> (level + 1);
        let (left, right) = if is_left {
            (current, *neighbour)
        } else {
            (*neighbour, current)
        };
        current = merkle_node(&pub_key.public_param, level + 1, parent_index, &left, &right);
    }
    if current == pub_key.merkle_root {
        Ok(())
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
