// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with BLAKE3.
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
//! Hashing is **VM-native** — built only from the fixed 64→32 BLAKE3 compression
//! `f(a,b) = BLAKE3(a‖b)` that leanVM-b's `Blake3` opcode computes (see
//! [`compress`]), so every node hash a verifier recomputes can be replayed by a
//! program running on the VM (the prerequisite for recursion). An internal node
//! ([`hash_pair`]) is one compression. A leaf ([`hash_leaf`]) is a **Merkle–
//! Damgård chain with the byte length in the IV** — one compression per 32-byte
//! block — NOT a one-shot `blake3::hash` (whose multi-block chunk tree, flags,
//! and counter the opcode cannot express). Bulk hashing (independent leaves,
//! independent nodes within a level) is parallelised across nodes with rayon.
//!
//! No domain separation between leaf and internal hashes — but the length-in-IV
//! leaf construction differs structurally from a pair compression, so a leaf and
//! an internal node do not share a pre-image shape. A production PCS may still
//! prefer explicit `0x00`/`0x01` tags.

use crate::field::F128;
use rayon::prelude::*;

pub type Hash = [u8; 32];

/// Global BLAKE3 call/compression counters, enabled with
/// `--features hash-count` (e.g. by `benches/verifier_hash_count.rs`).
/// Relaxed atomics — exact totals, no ordering guarantees across threads.
#[cfg(feature = "hash-count")]
pub mod hash_count {
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

    pub static LEAF_CALLS: AtomicU64 = AtomicU64::new(0);
    pub static LEAF_COMPRESSIONS: AtomicU64 = AtomicU64::new(0);
    pub static PAIR_CALLS: AtomicU64 = AtomicU64::new(0);

    /// BLAKE3 compression count for a one-shot hash of `len` bytes: one
    /// compression per 64-byte block (ceil(len / 64), min 1 — no length pad).
    #[inline]
    pub fn blake3_blocks(len: usize) -> u64 {
        (len.div_ceil(64)).max(1) as u64
    }

    pub fn reset() {
        LEAF_CALLS.store(0, Relaxed);
        LEAF_COMPRESSIONS.store(0, Relaxed);
        PAIR_CALLS.store(0, Relaxed);
    }

    /// (leaf_calls, leaf_compressions, pair_calls). Each pair hash is one
    /// compression (64 B, no length padding block).
    pub fn snapshot() -> (u64, u64, u64) {
        (
            LEAF_CALLS.load(Relaxed),
            LEAF_COMPRESSIONS.load(Relaxed),
            PAIR_CALLS.load(Relaxed),
        )
    }
}

/// The VM's 64→32 BLAKE3 compression `f(a, b) = BLAKE3(a‖b)` on two 32-byte
/// halves — exactly leanVM-b's `Blake3` opcode / `vmhash::compress`. THE
/// primitive; [`hash_pair`] and the [`hash_leaf`] MD chain are both just this.
#[inline]
fn compress(a: &[u8; 32], b: &[u8; 32]) -> Hash {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(a);
    buf[32..].copy_from_slice(b);
    *blake3::hash(&buf).as_bytes()
}

/// `g^k`, the field generator to the `k`-th power by square-and-multiply — the
/// length marker for the leaf IV. Mirrors leanVM-b's `vmhash`/XMSS convention so
/// [`hash_leaf`] equals `vmhash::hash_slice` on the same field words.
fn g_pow(k: usize) -> F128 {
    let mut result = F128::ONE;
    let mut base = F128::generator();
    let mut e = k;
    while e > 0 {
        if e & 1 == 1 {
            result = result * base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

/// IV `(g^{num_bytes}, 0)` serialized to 32 bytes.
#[inline]
fn leaf_iv(num_bytes: usize) -> Hash {
    let iv0 = g_pow(num_bytes);
    let mut cv = [0u8; 32];
    cv[..8].copy_from_slice(&iv0.lo.to_le_bytes());
    cv[8..16].copy_from_slice(&iv0.hi.to_le_bytes());
    cv
}

/// The Merkle–Damgård state after `IV(num_bytes)` absorbs `z` all-zero 32-byte
/// blocks — the reusable "trailing zeros" prefix of the RTL leaf hash. Memoized
/// because `z` is constant across all leaves of a tree (the MSB-lane zero lanes),
/// so the whole zero suffix costs a handful of compressions ONCE per tree instead
/// of `z` per leaf.
fn zero_suffix_state(num_bytes: usize, z: usize) -> Hash {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};
    static CACHE: OnceLock<Mutex<HashMap<(usize, usize), Hash>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(&h) = cache.lock().unwrap().get(&(num_bytes, z)) {
        return h;
    }
    let mut cv = leaf_iv(num_bytes);
    for _ in 0..z {
        cv = compress(&cv, &[0u8; 32]);
    }
    cache.lock().unwrap().insert((num_bytes, z), cv);
    cv
}

/// Hash one leaf with the VM-native Merkle–Damgård slice hash, **right-to-left**:
/// IV `(g^{num_bytes}, 0)`, then one [`compress`] per 32-byte block from the LAST
/// block to the first. Hashing RTL puts trailing all-zero blocks (the MSB-lane
/// zero lanes, `ligero_commit`) at the chain's *prefix*, whose state depends only
/// on `(length, #zero-blocks)` — precomputed once per tree and reused, so those
/// compressions are skipped entirely (forward hashing can't: trailing zeros there
/// hang off the varying real-data state). The length in the IV binds the leaf
/// size. Prover (tree build) and verifier (opening re-hash) both call this, so
/// they stay consistent. Costs `⌈len/32⌉ − #trailing-zero-blocks` compressions.
#[inline]
pub fn hash_leaf(data: &[u8]) -> Hash {
    let num_blocks = data.len().div_ceil(32).max(1);
    // Count trailing all-zero 32-byte blocks.
    let mut z = 0;
    while z < num_blocks {
        let end = data.len().saturating_sub(z * 32);
        let start = end.saturating_sub(32);
        if data[start..end].iter().any(|&b| b != 0) {
            break;
        }
        z += 1;
    }
    #[cfg(feature = "hash-count")]
    {
        use std::sync::atomic::Ordering::Relaxed;
        hash_count::LEAF_CALLS.fetch_add(1, Relaxed);
        hash_count::LEAF_COMPRESSIONS.fetch_add((num_blocks - z) as u64, Relaxed);
    }
    let mut cv = zero_suffix_state(data.len(), z);
    for bi in (0..num_blocks - z).rev() {
        let start = bi * 32;
        let end = (start + 32).min(data.len());
        let mut b = [0u8; 32];
        b[..end - start].copy_from_slice(&data[start..end]);
        cv = compress(&cv, &b);
    }
    cv
}

/// Hash a pair of children into a parent node (64 B → 32 B): one [`compress`],
/// which is already exactly the VM opcode.
#[inline]
pub fn hash_pair(left: &Hash, right: &Hash) -> Hash {
    #[cfg(feature = "hash-count")]
    hash_count::PAIR_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    compress(left, right)
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

// The VM `compress` = `blake3::hash(64B)` is a ROOT single-block chunk. blake3's
// SIMD `hash_many` reproduces it exactly when the last block carries the ROOT
// flag (verified in tests), so many independent leaf compressions batch 4–16×.
const B3_IV: [u32; 8] = [
    0x6a09_e667, 0xbb67_ae85, 0x3c6e_f372, 0xa54f_f53a, 0x510e_527f, 0x9b05_688c, 0x1f83_d9ab, 0x5be0_cd19,
];
const B3_CHUNK_START: u8 = 1;
const B3_CHUNK_END: u8 = 2;
const B3_ROOT: u8 = 8;

/// Hash all `out.len()` equal-size leaves with the VM-native MD slice hash, but
/// SIMD-batch each MD step's `compress` across leaves via blake3's `hash_many`.
/// Byte-identical to calling [`hash_leaf`] per leaf: the same **right-to-left**
/// chain with the shared trailing-zero prefix skipped (MSB-lane zero lanes). Per
/// group it skips `z` = the MINIMUM trailing-zero blocks across the group's leaves
/// (every leaf has ≥ z, so the shared `zero_suffix_state` is a common prefix; a
/// leaf with extra zeros hashes them explicitly — same result). Removes the
/// per-call `blake3::hash` overhead, the lack of cross-leaf SIMD, AND the zero
/// lanes.
fn hash_leaves_batched(data: &[u8], leaf_size: usize, out: &mut [Hash]) {
    use rayon::prelude::*;
    // Leaves per SIMD group: enough to fill the batch + amortize, small enough to
    // stay cache-resident (n·(32 cv + 64 block + 32 out) bytes).
    const GROUP: usize = 4096;
    let n_blocks = leaf_size.div_ceil(32).max(1);

    out.par_chunks_mut(GROUP).enumerate().for_each(|(gi, out_group)| {
        let plat = blake3::platform::Platform::detect();
        let n = out_group.len();
        let base = gi * GROUP * leaf_size;
        // z = min trailing all-zero 32-byte blocks across the group (uniform for
        // MSB-lane's structural zero lanes; 0 for zero-free levels).
        let mut z = n_blocks;
        for i in 0..n {
            let leaf_end = base + (i + 1) * leaf_size;
            let mut zi = 0;
            while zi < n_blocks {
                let end = leaf_end - zi * 32;
                let start = end.saturating_sub(32);
                if data[start..end].iter().any(|&b| b != 0) {
                    break;
                }
                zi += 1;
            }
            z = z.min(zi);
            if z == 0 {
                break;
            }
        }
        let start_cv = zero_suffix_state(leaf_size, z);
        let mut cvs: Vec<[u8; 32]> = vec![start_cv; n];
        let mut blocks: Vec<[u8; 64]> = vec![[0u8; 64]; n];
        let mut hm_out = vec![0u8; n * 32];
        // Absorb the real blocks last-to-first (RTL); the trailing z zero blocks
        // are already folded into `start_cv`.
        for j in (0..n_blocks - z).rev() {
            for (i, blk) in blocks.iter_mut().enumerate() {
                blk[..32].copy_from_slice(&cvs[i]);
                let off = base + i * leaf_size + j * 32;
                let end = (off + 32).min(base + (i + 1) * leaf_size);
                let len = end - off;
                blk[32..32 + len].copy_from_slice(&data[off..end]);
                blk[32 + len..].fill(0); // zero-pad an odd tail (matches hash_leaf)
            }
            let refs: Vec<&[u8; 64]> = blocks.iter().collect();
            plat.hash_many::<64>(
                &refs,
                &B3_IV,
                0,
                blake3::IncrementCounter::No,
                0,
                B3_CHUNK_START,
                B3_CHUNK_END | B3_ROOT,
                &mut hm_out,
            );
            for (i, cv) in cvs.iter_mut().enumerate() {
                cv.copy_from_slice(&hm_out[i * 32..i * 32 + 32]);
            }
        }
        for (o, cv) in out_group.iter_mut().zip(cvs.iter()) {
            *o = *cv;
        }
    });
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

    // 1. Leaves — the VM-native MD slice hash (one `compress` per 32-byte block),
    // but the per-step compressions are SIMD-batched ACROSS leaves via blake3's
    // `hash_many` (byte-identical to per-leaf `hash_leaf`, so recursion
    // reproducibility is preserved) — recovering the one-shot-`blake3::hash` speed
    // the VM-native chain otherwise loses to per-call overhead + no SIMD.
    hash_leaves_batched(data, leaf_size, &mut tree[..num_leaves]);

    // 2. Internal levels — parallel within a level, sequential across levels.
    // Small upper levels can't fill the cores, so a rayon dispatch per level
    // costs more than the hashing itself; hash those serially and only fan out
    // the wide lower levels.
    const SERIAL_LEVEL_NODES: usize = 1024;
    let mut read_start = 0usize;
    let mut read_len = num_leaves;
    while read_len > 1 {
        let next_len = read_len >> 1;
        // Split the buffer at the end of the current level so we get two
        // non-overlapping mutable slices: `read` (input) and `write` (output).
        let (read, rest) = tree[read_start..].split_at_mut(read_len);
        let write = &mut rest[..next_len];

        if write.len() <= SERIAL_LEVEL_NODES {
            for (i, out) in write.iter_mut().enumerate() {
                *out = hash_pair(&read[2 * i], &read[2 * i + 1]);
            }
        } else {
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

/// Reconstruct the full per-query Merkle paths from a *pruned* (octopus) proof —
/// the inverse of [`merkle_multi_proof`]. Given the ORIGINAL `queries` (unsorted,
/// possibly duplicate), the distinct leaves' hashes (`leaf_hashes`, aligned with
/// the sorted-unique query set), and the pruned `sibling_hashes`, it rebuilds for
/// each query its full `log2(num_leaves)`-sibling path — the *expanded* form the
/// recursion-friendly [`verify_merkle_proof`] consumes. Returns the paths
/// concatenated flat (one `height`-long path per query, in query order), or `None`
/// on any inconsistency (wrong sibling count, unresolvable node). It authenticates
/// nothing itself; the caller verifies each restored path against the root.
pub fn restore_multi_proof(
    num_leaves: usize,
    queries: &[usize],
    leaf_hashes: &[Hash],
    sibling_hashes: &[Hash],
) -> Option<Vec<Hash>> {
    if !num_leaves.is_power_of_two() || num_leaves == 0 {
        return None;
    }
    let height = num_leaves.trailing_zeros() as usize;
    let mut sorted: Vec<usize> = queries.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    if sorted.len() != leaf_hashes.len() || sorted.last().is_some_and(|&p| p >= num_leaves) {
        return None;
    }
    // Rebuild every tree node on the query paths bottom-up, pulling a pruned
    // sibling only where that sibling is not itself a queried subtree (which we
    // just computed). `known[lvl]` records the nodes present at each level.
    let mut supplied = sibling_hashes.iter();
    let mut known: Vec<Vec<(usize, Hash)>> = Vec::with_capacity(height);
    let mut nodes: Vec<(usize, Hash)> = sorted.iter().copied().zip(leaf_hashes.iter().copied()).collect();
    for _ in 0..height {
        let mut level = Vec::with_capacity(2 * nodes.len());
        let mut parents = Vec::with_capacity(nodes.len());
        let mut i = 0;
        while i < nodes.len() {
            let idx = nodes[i].0;
            let paired = idx & 1 == 0 && nodes.get(i + 1).is_some_and(|&(j, _)| j == (idx | 1));
            let (left, right) = if paired {
                (nodes[i].1, nodes[i + 1].1)
            } else if idx & 1 == 0 {
                (nodes[i].1, *supplied.next()?)
            } else {
                (*supplied.next()?, nodes[i].1)
            };
            parents.push((idx >> 1, hash_pair(&left, &right)));
            level.push((idx & !1, left));
            level.push((idx | 1, right));
            i += if paired { 2 } else { 1 };
        }
        known.push(level);
        nodes = parents;
    }
    if supplied.next().is_some() {
        return None; // extra siblings ⇒ malformed proof
    }
    // Read each distinct leaf's full sibling path out of the reconstructed levels.
    let per_distinct: Vec<Vec<Hash>> = sorted
        .iter()
        .map(|&leaf| {
            (0..height)
                .map(|lvl| {
                    let sib = (leaf >> lvl) ^ 1;
                    let level = &known[lvl];
                    level.binary_search_by_key(&sib, |&(j, _)| j).ok().map(|pos| level[pos].1)
                })
                .collect::<Option<Vec<_>>>()
        })
        .collect::<Option<Vec<_>>>()?;
    // Fan back out to the original (unsorted, possibly duplicate) query order.
    let mut out = Vec::with_capacity(queries.len() * height);
    for &q in queries {
        let slot = sorted.binary_search(&q).ok()?;
        out.extend_from_slice(&per_distinct[slot]);
    }
    Some(out)
}

#[cfg(test)]
mod prune_tests {
    use super::*;

    /// `merkle_multi_proof` (prune) then `restore_multi_proof` (expand) reproduces
    /// each query's full path, and every restored path authenticates to the root —
    /// including unsorted, duplicate queries. Extra siblings are rejected.
    #[test]
    fn prune_restore_roundtrip() {
        let num_leaves = 8usize;
        let leaf_size = 4usize;
        let height = 3usize;
        let data: Vec<u8> = (0..(num_leaves * leaf_size) as u8).collect();
        let tree = merkle_tree(&data, num_leaves);
        let root = tree[tree.len() - 1];

        let queries = [5usize, 1, 5, 3, 1]; // unsorted, with duplicates
        let mut sorted = queries.to_vec();
        sorted.sort_unstable();
        sorted.dedup(); // [1, 3, 5]
        let leaf_hashes: Vec<Hash> = sorted.iter().map(|&q| hash_leaf(&data[q * leaf_size..(q + 1) * leaf_size])).collect();

        let pruned = merkle_multi_proof(&tree, num_leaves, &sorted);
        let flat = restore_multi_proof(num_leaves, &queries, &leaf_hashes, &pruned).expect("restore");
        assert_eq!(flat.len(), queries.len() * height);
        for (i, &q) in queries.iter().enumerate() {
            let leaf = hash_leaf(&data[q * leaf_size..(q + 1) * leaf_size]);
            let path = &flat[i * height..(i + 1) * height];
            assert!(verify_merkle_proof(&root, &leaf, q, path), "restored path for query {q} (pos {i}) must verify");
        }

        // An extra (unconsumed) sibling is a malformed proof.
        let mut extra = pruned.clone();
        extra.push([0u8; 32]);
        assert!(restore_multi_proof(num_leaves, &queries, &leaf_hashes, &extra).is_none());
    }

    /// The zero-suffix skip in `hash_leaf` must equal a naive right-to-left MD
    /// over the full leaf (with the trailing zeros hashed explicitly) — i.e. the
    /// precompute is a faithful shortcut, for any number of trailing zero blocks.
    #[test]
    fn hash_leaf_zero_skip_matches_full_rtl() {
        let full_rtl = |data: &[u8]| -> Hash {
            let nb = data.len().div_ceil(32).max(1);
            let mut cv = leaf_iv(data.len());
            for bi in (0..nb).rev() {
                let start = bi * 32;
                let end = (start + 32).min(data.len());
                let mut b = [0u8; 32];
                b[..end - start].copy_from_slice(&data[start..end]);
                cv = compress(&cv, &b);
            }
            cv
        };
        for zero_blocks in 0..6usize {
            let mut data = vec![0u8; 8 * 32];
            // fill the leading blocks with non-zero data, leave `zero_blocks` trailing zero
            for (i, b) in data.iter_mut().enumerate().take((8 - zero_blocks) * 32) {
                *b = (i as u8) | 1;
            }
            assert_eq!(hash_leaf(&data), full_rtl(&data), "zero_blocks={zero_blocks}");
        }
    }
}

#[cfg(test)]
mod vmhash_batch_tests {
    use super::*;

    /// blake3's SIMD `hash_many` with the ROOT flag must reproduce
    /// `blake3::hash(64B)` (the VM `compress`) exactly — the invariant the batched
    /// leaf hasher relies on.
    #[test]
    fn hash_many_root_matches_hash() {
        let plat = blake3::platform::Platform::detect();
        let mut b0 = [0u8; 64];
        for (i, x) in b0.iter_mut().enumerate() {
            *x = (i as u8).wrapping_mul(7).wrapping_add(1);
        }
        let mut b1 = [0u8; 64];
        for (i, x) in b1.iter_mut().enumerate() {
            *x = (i as u8).wrapping_mul(13).wrapping_add(3);
        }
        let inputs: [&[u8; 64]; 2] = [&b0, &b1];
        let mut out = [0u8; 64];
        plat.hash_many::<64>(&inputs, &B3_IV, 0, blake3::IncrementCounter::No, 0, B3_CHUNK_START, B3_CHUNK_END | B3_ROOT, &mut out);
        assert_eq!(&out[..32], blake3::hash(&b0).as_bytes());
        assert_eq!(&out[32..], blake3::hash(&b1).as_bytes());
    }

    /// The SIMD-batched `merkle_tree` must be byte-identical to the per-leaf
    /// `merkle_tree_sequential` (which uses `hash_leaf`) — same root, same nodes —
    /// across leaf sizes incl. an odd (non-32-multiple) leaf and group boundaries.
    #[test]
    fn batched_matches_sequential() {
        for (num_leaves, leaf_size) in [(8usize, 32usize), (16, 1024), (2, 48), (8192, 16), (1, 32)] {
            let data: Vec<u8> = (0..num_leaves * leaf_size).map(|i| (i.wrapping_mul(131) ^ 0x5a) as u8).collect();
            assert_eq!(
                merkle_tree(&data, num_leaves),
                merkle_tree_sequential(&data, num_leaves),
                "num_leaves={num_leaves} leaf_size={leaf_size}"
            );
        }
    }
}
