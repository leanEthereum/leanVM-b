// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with SHA-256, ARM crypto-extension accelerated.
//!
//! Layout for `num_leaves = 2^k` leaves:
//!   tree[0..num_leaves]                              = leaf hashes (level k)
//!   tree[num_leaves..3·num_leaves/2]                 = level k−1
//!   ...
//!   tree[2·num_leaves − 2..2·num_leaves − 1]         = root (level 0)
//!
//! Total nodes: `2·num_leaves − 1`. The flat layout keeps the tree contiguous
//! in memory for cheap Merkle-path extraction later.
//!
//! Hash uses the [`sha2`] crate. On aarch64 with the `sha2` target feature
//! (set implicitly by `target-cpu=native` on M-series), the crate uses
//! `sha256h`/`sha256h2`/`sha256su0`/`sha256su1` ARM crypto extension
//! instructions; this is detected at runtime by [`cpufeatures`].
//!
//! No domain separation between leaf and internal hashes — this is a
//! micro-benchmark module, not production code. A production PCS commit
//! should prepend `0x00`/`0x01` (or equivalent) to distinguish the two
//! pre-images and avoid second-preimage attacks via interpretation collision.

use rayon::prelude::*;
use sha2::{Digest, Sha256};

pub type Hash = [u8; 32];

/// 4-way interleaved SHA-256 using ARM crypto-extension intrinsics.
///
/// The M-series SHA unit is pipelined: a single dependent compress
/// chain runs at ~21 ns/compress, while interleaved independent
/// streams sustain ~16 ns/compress on real (distinct) data — a ~1.35×
/// throughput win, measured on M4 Max at m=30. The `sha2` crate hashes
/// one stream at a time, so bulk Merkle hashing (independent leaves /
/// independent nodes within a level) leaves that on the table.
///
/// Digests are byte-identical to `Sha256::digest`.
#[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
mod sha256x4 {
    use super::Hash;
    use core::arch::aarch64::*;

    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    const IV_ABCD: [u32; 4] = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a];
    const IV_EFGH: [u32; 4] = [0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];

    /// One interleaved compression round over 4 independent states.
    /// `blocks[i]` must be ≥ 64 bytes; only the first 64 are consumed.
    #[inline(always)]
    unsafe fn compress4(
        abcd: &mut [uint32x4_t; 4],
        efgh: &mut [uint32x4_t; 4],
        blocks: [*const u8; 4],
    ) {
        unsafe {
            let mut msg0 = [vdupq_n_u32(0); 4];
            let mut msg1 = [vdupq_n_u32(0); 4];
            let mut msg2 = [vdupq_n_u32(0); 4];
            let mut msg3 = [vdupq_n_u32(0); 4];
            for i in 0..4 {
                // SHA-256 message words are big-endian.
                msg0[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(blocks[i])));
                msg1[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(blocks[i].add(16))));
                msg2[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(blocks[i].add(32))));
                msg3[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(blocks[i].add(48))));
            }
            let abcd_save = *abcd;
            let efgh_save = *efgh;

            macro_rules! rounds4 {
                ($msg:expr, $ki:expr) => {{
                    let kv = vld1q_u32(K.as_ptr().add($ki));
                    for i in 0..4 {
                        let wk = vaddq_u32($msg[i], kv);
                        let t = abcd[i];
                        abcd[i] = vsha256hq_u32(abcd[i], efgh[i], wk);
                        efgh[i] = vsha256h2q_u32(efgh[i], t, wk);
                    }
                }};
            }
            macro_rules! sched {
                ($m0:expr, $m1:expr, $m2:expr, $m3:expr) => {
                    for i in 0..4 {
                        $m0[i] = vsha256su1q_u32(vsha256su0q_u32($m0[i], $m1[i]), $m2[i], $m3[i]);
                    }
                };
            }

            rounds4!(msg0, 0);
            rounds4!(msg1, 4);
            rounds4!(msg2, 8);
            rounds4!(msg3, 12);
            for r in 1..4 {
                sched!(msg0, msg1, msg2, msg3);
                sched!(msg1, msg2, msg3, msg0);
                sched!(msg2, msg3, msg0, msg1);
                sched!(msg3, msg0, msg1, msg2);
                rounds4!(msg0, 16 * r);
                rounds4!(msg1, 16 * r + 4);
                rounds4!(msg2, 16 * r + 8);
                rounds4!(msg3, 16 * r + 12);
            }
            for i in 0..4 {
                abcd[i] = vaddq_u32(abcd[i], abcd_save[i]);
                efgh[i] = vaddq_u32(efgh[i], efgh_save[i]);
            }
        }
    }

    /// Hash 4 equal-length inputs, producing 4 standard SHA-256 digests.
    #[inline]
    pub fn hash4_equal_len(inputs: [&[u8]; 4], out: &mut [Hash]) {
        let len = inputs[0].len();
        debug_assert!(inputs.iter().all(|x| x.len() == len));
        debug_assert!(out.len() >= 4);

        unsafe {
            let mut abcd = [vld1q_u32(IV_ABCD.as_ptr()); 4];
            let mut efgh = [vld1q_u32(IV_EFGH.as_ptr()); 4];

            // Full 64-byte blocks.
            let n_full = len / 64;
            for blk in 0..n_full {
                compress4(
                    &mut abcd,
                    &mut efgh,
                    [
                        inputs[0].as_ptr().add(blk * 64),
                        inputs[1].as_ptr().add(blk * 64),
                        inputs[2].as_ptr().add(blk * 64),
                        inputs[3].as_ptr().add(blk * 64),
                    ],
                );
            }

            // Tail: remaining bytes + 0x80 + zero pad + 64-bit BE bit length.
            // One extra block when rem ≤ 55, two when 56 ≤ rem ≤ 63.
            let rem = len % 64;
            let bit_len = (len as u64) * 8;
            let n_tail = if rem < 56 { 1 } else { 2 };
            let mut tails = [[0u8; 128]; 4];
            for i in 0..4 {
                tails[i][..rem].copy_from_slice(&inputs[i][len - rem..]);
                tails[i][rem] = 0x80;
                tails[i][n_tail * 64 - 8..n_tail * 64].copy_from_slice(&bit_len.to_be_bytes());
            }
            for blk in 0..n_tail {
                compress4(
                    &mut abcd,
                    &mut efgh,
                    [
                        tails[0].as_ptr().add(blk * 64),
                        tails[1].as_ptr().add(blk * 64),
                        tails[2].as_ptr().add(blk * 64),
                        tails[3].as_ptr().add(blk * 64),
                    ],
                );
            }

            // Digest = big-endian a..h.
            for i in 0..4 {
                let be_lo = vrev32q_u8(vreinterpretq_u8_u32(abcd[i]));
                let be_hi = vrev32q_u8(vreinterpretq_u8_u32(efgh[i]));
                vst1q_u8(out[i].as_mut_ptr(), be_lo);
                vst1q_u8(out[i].as_mut_ptr().add(16), be_hi);
            }
        }
    }
}

/// Global SHA-256 call/compression counters, enabled with
/// `--features hash-count` (e.g. by `benches/verifier_hash_count.rs`).
/// Relaxed atomics — exact totals, no ordering guarantees across threads.
#[cfg(feature = "hash-count")]
pub mod hash_count {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

    pub static LEAF_CALLS: AtomicU64 = AtomicU64::new(0);
    pub static LEAF_COMPRESSIONS: AtomicU64 = AtomicU64::new(0);
    pub static PAIR_CALLS: AtomicU64 = AtomicU64::new(0);

    /// SHA-256 compression count for a one-shot hash of `len` bytes:
    /// ceil((len + 9) / 64) — payload + 0x80 pad + 8-byte length.
    #[inline]
    pub fn sha256_blocks(len: usize) -> u64 {
        ((len + 9).div_ceil(64)) as u64
    }

    pub fn reset() {
        LEAF_CALLS.store(0, Relaxed);
        LEAF_COMPRESSIONS.store(0, Relaxed);
        PAIR_CALLS.store(0, Relaxed);
    }

    /// (leaf_calls, leaf_compressions, pair_calls). Each pair hash is
    /// 2 compressions (64 B payload + padding block).
    pub fn snapshot() -> (u64, u64, u64) {
        (
            LEAF_CALLS.load(Relaxed),
            LEAF_COMPRESSIONS.load(Relaxed),
            PAIR_CALLS.load(Relaxed),
        )
    }
}

/// Hash one leaf of arbitrary byte length.
#[inline]
pub fn hash_leaf(data: &[u8]) -> Hash {
    #[cfg(feature = "hash-count")]
    {
        use std::sync::atomic::Ordering::Relaxed;
        hash_count::LEAF_CALLS.fetch_add(1, Relaxed);
        hash_count::LEAF_COMPRESSIONS.fetch_add(hash_count::sha256_blocks(data.len()), Relaxed);
    }
    Sha256::digest(data).into()
}

/// Hash a pair of children into a parent node (64 B → 32 B).
#[inline]
pub fn hash_pair(left: &Hash, right: &Hash) -> Hash {
    #[cfg(feature = "hash-count")]
    hash_count::PAIR_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut h = Sha256::new();
    h.update(left);
    h.update(right);
    h.finalize().into()
}

/// Compute the Merkle root of `data` split into `num_leaves` equal-sized leaves.
///
/// Multi-threaded via rayon. `num_leaves` must be a power of two and divide
/// `data.len()`. Returns the 32-byte root. The intermediate tree is allocated
/// and dropped; if you need it for path opening, use [`merkle_tree`] instead.
pub fn merkle_root(data: &[u8], num_leaves: usize) -> Hash {
    let tree = merkle_tree(data, num_leaves);
    tree[tree.len() - 1]
}

/// Compute the full Merkle tree (flat layout, see module docs) for `data`
/// split into `num_leaves` equal-sized leaves.
pub fn merkle_tree(data: &[u8], num_leaves: usize) -> Vec<Hash> {
    assert!(
        num_leaves.is_power_of_two() && num_leaves > 0,
        "num_leaves must be power of 2"
    );
    assert_eq!(
        data.len() % num_leaves,
        0,
        "data length must be a multiple of num_leaves"
    );

    let leaf_size = data.len() / num_leaves;
    let total_nodes = 2 * num_leaves - 1;
    // Uninit alloc — every node is written exactly once before being read:
    // leaves at step 1, then each internal level reads the level below (which
    // was just written) and writes itself.
    let mut tree: Vec<Hash> = crate::alloc_uninit_vec(total_nodes);

    // 1. Leaves — fully parallel; 4-way interleaved SHA where available.
    #[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
    {
        tree[..num_leaves]
            .par_chunks_mut(4)
            .zip(data.par_chunks(4 * leaf_size))
            .for_each(|(outs, leaves)| {
                if outs.len() == 4 {
                    #[cfg(feature = "hash-count")]
                    {
                        use std::sync::atomic::Ordering::Relaxed;
                        hash_count::LEAF_CALLS.fetch_add(4, Relaxed);
                        hash_count::LEAF_COMPRESSIONS
                            .fetch_add(4 * hash_count::sha256_blocks(leaf_size), Relaxed);
                    }
                    sha256x4::hash4_equal_len(
                        [
                            &leaves[..leaf_size],
                            &leaves[leaf_size..2 * leaf_size],
                            &leaves[2 * leaf_size..3 * leaf_size],
                            &leaves[3 * leaf_size..],
                        ],
                        outs,
                    );
                } else {
                    for (out, leaf) in outs.iter_mut().zip(leaves.chunks(leaf_size)) {
                        *out = hash_leaf(leaf);
                    }
                }
            });
    }
    #[cfg(not(all(target_arch = "aarch64", target_feature = "sha2")))]
    {
        tree[..num_leaves]
            .par_iter_mut()
            .zip(data.par_chunks(leaf_size))
            .for_each(|(out, leaf)| *out = hash_leaf(leaf));
    }

    // 2. Internal levels — parallel within a level, sequential across levels.
    let mut read_start = 0usize;
    let mut read_len = num_leaves;
    while read_len > 1 {
        let next_len = read_len >> 1;
        // Split the buffer at the end of the current level so we get two
        // non-overlapping mutable slices: `read` (input) and `write` (output).
        let (read, rest) = tree[read_start..].split_at_mut(read_len);
        let write = &mut rest[..next_len];

        // 4 parents at a time = 8 contiguous children = 256 contiguous bytes;
        // each parent hashes its 64-byte child pair, interleaved 4-way.
        #[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
        {
            let read_bytes: &[u8] =
                unsafe { core::slice::from_raw_parts(read.as_ptr() as *const u8, read.len() * 32) };
            let hash_quad = |outs: &mut [Hash], children: &[u8]| {
                if outs.len() == 4 {
                    #[cfg(feature = "hash-count")]
                    hash_count::PAIR_CALLS.fetch_add(4, std::sync::atomic::Ordering::Relaxed);
                    sha256x4::hash4_equal_len(
                        [
                            &children[..64],
                            &children[64..128],
                            &children[128..192],
                            &children[192..256],
                        ],
                        outs,
                    );
                } else {
                    for (i, out) in outs.iter_mut().enumerate() {
                        let l: &Hash = children[i * 64..i * 64 + 32].try_into().unwrap();
                        let r: &Hash = children[i * 64 + 32..i * 64 + 64].try_into().unwrap();
                        *out = hash_pair(l, r);
                    }
                }
            };
            // Small upper levels can't fill the cores (≤ SERIAL_LEVEL_NODES / 4
            // SHA-x4 tasks), so a rayon dispatch per level costs more than the
            // hashing itself (~3× at the top of a 2^18 tree). Hash them serially
            // — still 4-way SIMD — and only fan out the wide lower levels.
            const SERIAL_LEVEL_NODES: usize = 1024;
            if write.len() <= SERIAL_LEVEL_NODES {
                for (outs, children) in write.chunks_mut(4).zip(read_bytes.chunks(256)) {
                    hash_quad(outs, children);
                }
            } else {
                write
                    .par_chunks_mut(4)
                    .zip(read_bytes.par_chunks(256))
                    .for_each(|(outs, children)| hash_quad(outs, children));
            }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "sha2")))]
        {
            write
                .par_iter_mut()
                .enumerate()
                .for_each(|(i, out)| *out = hash_pair(&read[2 * i], &read[2 * i + 1]));
        }

        read_start += read_len;
        read_len = next_len;
    }

    tree
}

/// Sequential (single-threaded) version of [`merkle_tree`]. Used for
/// benchmark comparison and as the test oracle.
pub fn merkle_tree_sequential(data: &[u8], num_leaves: usize) -> Vec<Hash> {
    assert!(num_leaves.is_power_of_two() && num_leaves > 0);
    assert_eq!(data.len() % num_leaves, 0);

    let leaf_size = data.len() / num_leaves;
    let total_nodes = 2 * num_leaves - 1;
    let mut tree: Vec<Hash> = crate::alloc_uninit_vec(total_nodes);

    for (i, leaf) in data.chunks(leaf_size).enumerate() {
        tree[i] = hash_leaf(leaf);
    }
    let mut read_start = 0usize;
    let mut read_len = num_leaves;
    while read_len > 1 {
        let next_len = read_len >> 1;
        for i in 0..next_len {
            let left = tree[read_start + 2 * i];
            let right = tree[read_start + 2 * i + 1];
            tree[read_start + read_len + i] = hash_pair(&left, &right);
        }
        read_start += read_len;
        read_len = next_len;
    }
    tree
}

// ---------------------------------------------------------------------------
// Merkle path opening and verification.
// ---------------------------------------------------------------------------

/// Build an opening proof for leaf `index`: the sibling hashes from the leaf
/// level up to (but not including) the root.
///
/// `tree` must be the flat tree produced by [`merkle_tree`] or
/// [`merkle_tree_sequential`] for `num_leaves` leaves. The returned vector has
/// length `log2(num_leaves)`.
///
/// Verify with [`verify_merkle_proof`].
pub fn merkle_proof(tree: &[Hash], num_leaves: usize, index: usize) -> Vec<Hash> {
    assert!(num_leaves.is_power_of_two() && num_leaves > 0);
    assert!(index < num_leaves);
    assert_eq!(tree.len(), 2 * num_leaves - 1);

    let log_n = num_leaves.trailing_zeros() as usize;
    let mut proof = Vec::with_capacity(log_n);

    let mut level_start = 0usize;
    let mut level_len = num_leaves;
    let mut idx = index;
    while level_len > 1 {
        let sibling_idx = idx ^ 1;
        proof.push(tree[level_start + sibling_idx]);
        level_start += level_len;
        level_len >>= 1;
        idx >>= 1;
    }
    proof
}

/// Verify a Merkle opening: recomputes the root from `leaf_hash`, the path,
/// and the leaf index. Returns true iff the recomputed root matches `root`.
pub fn verify_merkle_proof(root: &Hash, leaf_hash: &Hash, index: usize, proof: &[Hash]) -> bool {
    let mut acc = *leaf_hash;
    let mut idx = index;
    for sibling in proof {
        // If idx is even, our node is the LEFT child; sibling is on the RIGHT.
        let (left, right) = if idx & 1 == 0 {
            (acc, *sibling)
        } else {
            (*sibling, acc)
        };
        acc = hash_pair(&left, &right);
        idx >>= 1;
    }
    &acc == root
}

// ---------------------------------------------------------------------------
// Multi-proof (Octopus / batched opening): one shared proof for multiple leaf
// positions, deduplicating siblings that lie on multiple paths.
// ---------------------------------------------------------------------------

/// Build a Merkle multi-proof for `positions`. Returns the sibling hashes
/// needed to verify ALL positions against the root, in the canonical
/// bottom-up sorted-by-position traversal order.
///
/// `positions` need not be sorted or unique; the function sorts + dedupes
/// internally. For `q` queries in a tree of depth `d`, the output is at
/// most `q · d` hashes (matching `q` independent paths) and typically much
/// smaller (siblings shared across multiple paths are emitted once).
///
/// Verify with [`verify_merkle_multi_proof`].
pub fn merkle_multi_proof(tree: &[Hash], num_leaves: usize, positions: &[usize]) -> Vec<Hash> {
    assert!(num_leaves.is_power_of_two() && num_leaves > 0);
    assert_eq!(tree.len(), 2 * num_leaves - 1);

    if positions.is_empty() || num_leaves == 1 {
        return Vec::new();
    }

    let mut active: Vec<usize> = positions.to_vec();
    active.sort_unstable();
    active.dedup();
    debug_assert!(active.iter().all(|&p| p < num_leaves));

    let mut proof = Vec::new();
    let mut level_start = 0usize;
    let mut level_len = num_leaves;

    while level_len > 1 {
        let mut next = Vec::with_capacity(active.len());
        let mut i = 0;
        while i < active.len() {
            let p = active[i];
            let sib_active = i + 1 < active.len() && active[i + 1] == (p ^ 1);
            if sib_active {
                // Both children active — no sibling hash needed; both fold into
                // the same parent.
                i += 2;
            } else {
                // Sibling not in active set; emit it.
                proof.push(tree[level_start + (p ^ 1)]);
                i += 1;
            }
            next.push(p >> 1);
        }
        // `next` is sorted-unique by construction: the input was sorted-unique;
        // consecutive sibling pairs (handled above) collapse to one; otherwise
        // p >> 1 preserves strict ordering.
        active = next;
        level_start += level_len;
        level_len >>= 1;
    }

    proof
}

/// Verify a Merkle multi-proof produced by [`merkle_multi_proof`].
///
/// `sorted_unique_positions` and `leaf_hashes` must be aligned and sorted:
/// `leaf_hashes[i]` is the hash of the leaf at `sorted_unique_positions[i]`,
/// and the position list is strictly ascending. Returns true iff the
/// reconstructed root equals `root` and the proof is consumed exactly.
pub fn verify_merkle_multi_proof(
    root: &Hash,
    num_leaves: usize,
    sorted_unique_positions: &[usize],
    leaf_hashes: &[Hash],
    proof: &[Hash],
) -> bool {
    if !num_leaves.is_power_of_two() || num_leaves == 0 {
        return false;
    }
    if sorted_unique_positions.len() != leaf_hashes.len() {
        return false;
    }
    if sorted_unique_positions.is_empty() {
        // Vacuous; nothing to verify. Treat as "ok" iff the proof is empty.
        return proof.is_empty();
    }
    // Verify the position list is sorted strictly ascending + in range.
    for (i, &p) in sorted_unique_positions.iter().enumerate() {
        if p >= num_leaves {
            return false;
        }
        if i > 0 && sorted_unique_positions[i - 1] >= p {
            return false;
        }
    }
    // Edge case: 1-leaf tree, no proof needed.
    if num_leaves == 1 {
        return proof.is_empty() && leaf_hashes[0] == *root;
    }

    let mut active: Vec<(usize, Hash)> = sorted_unique_positions
        .iter()
        .copied()
        .zip(leaf_hashes.iter().copied())
        .collect();
    let mut proof_iter = proof.iter().copied();
    let mut level_len = num_leaves;

    while level_len > 1 {
        let mut next = Vec::with_capacity(active.len());
        let mut i = 0;
        while i < active.len() {
            let (p, h) = active[i];
            let sib_active = i + 1 < active.len() && active[i + 1].0 == (p ^ 1);
            let (left, right) = if sib_active {
                let (_, h_sib) = active[i + 1];
                // Sorted strictly ascending → active[i+1].0 = p + 1 (= p ^ 1
                // since p is even when p ^ 1 = p + 1). So p is LEFT child.
                debug_assert_eq!(p & 1, 0);
                i += 2;
                (h, h_sib)
            } else {
                let sib = match proof_iter.next() {
                    Some(s) => s,
                    None => return false,
                };
                i += 1;
                if p & 1 == 0 { (h, sib) } else { (sib, h) }
            };
            next.push((p >> 1, hash_pair(&left, &right)));
        }
        active = next;
        level_len >>= 1;
    }

    // After the loop, `active` has exactly one element (the root). Reject
    // any leftover proof bytes.
    if proof_iter.next().is_some() {
        return false;
    }
    active.len() == 1 && active[0].1 == *root
}
