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
//! Hashing uses standard BLAKE3. The VM instruction exposes the chaining value,
//! counter, block length, and flags needed to replay both leaf chunk processing
//! and parent nodes in-circuit.

use primitives::field::F128;
use rayon::prelude::*;

pub type Hash = [u8; 32];

/// Encode a Merkle hash as the two little-endian field words used by transcripts.
#[inline]
pub fn hash_to_scalars(hash: &Hash) -> [F128; 2] {
    [
        F128::from_le_bytes(hash[..16].try_into().unwrap()),
        F128::from_le_bytes(hash[16..].try_into().unwrap()),
    ]
}

/// Decode the two field words used by transcripts back into a Merkle hash.
#[inline]
pub fn scalars_to_hash(scalars: &[F128]) -> Hash {
    assert_eq!(scalars.len(), 2, "a Merkle hash is exactly two field words");
    let mut hash = [0u8; 32];
    hash[..16].copy_from_slice(&scalars[0].to_le_bytes());
    hash[16..].copy_from_slice(&scalars[1].to_le_bytes());
    hash
}

/// The VM's 64→32 BLAKE3 compression `f(a, b) = BLAKE3(a‖b)` on two 32-byte
/// halves — exactly leanVM-b's `Blake3` opcode / `vmhash::compress`. THE
/// primitive used by internal Merkle nodes.
#[inline]
fn compress(a: &[u8; 32], b: &[u8; 32]) -> Hash {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(a);
    buf[32..].copy_from_slice(b);
    *blake3::hash(&buf).as_bytes()
}

/// Hash one leaf with standard BLAKE3.
#[inline]
pub fn hash_leaf(data: &[u8]) -> Hash {
    *blake3::hash(data).as_bytes()
}

/// Hash a pair of children into a parent node (64 B → 32 B): one [`compress`],
/// which is already exactly the VM opcode.
#[inline]
pub fn hash_pair(left: &Hash, right: &Hash) -> Hash {
    compress(left, right)
}

/// Hash equal-size leaves in parallel with standard BLAKE3.
fn hash_leaves_batched(data: &[u8], leaf_size: usize, out: &mut [Hash]) {
    out.par_iter_mut().enumerate().for_each(|(i, slot)| {
        let start = i * leaf_size;
        *slot = hash_leaf(&data[start..start + leaf_size]);
    });
}

/// Compute the full Merkle tree (flat layout, see module docs) for `data`
/// split into `num_leaves` equal-sized leaves.
#[tracing::instrument(
    name = "Hashing",
    skip_all,
    fields(
        num_leaves = num_leaves,
        leaf_size = data.len().checked_div(num_leaves).unwrap_or(0)
    )
)]
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
    let mut tree: Vec<Hash> = primitives::alloc_uninit_vec(total_nodes);

    // 1. Leaves — independent standard BLAKE3 hashes.
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

// ---------------------------------------------------------------------------
// Merkle path opening and verification.
// ---------------------------------------------------------------------------

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
/// Verify by expanding with [`restore_multi_proof`] and checking each restored
/// path via [`verify_merkle_proof`].
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
}

#[cfg(test)]
mod vmhash_batch_tests {
    use super::*;

    /// Sequential (per-leaf `hash_leaf`) reference for the parallel
    /// [`merkle_tree`].
    fn merkle_tree_sequential(data: &[u8], num_leaves: usize) -> Vec<Hash> {
    assert!(num_leaves.is_power_of_two() && num_leaves > 0);
    assert_eq!(data.len() % num_leaves, 0);

    let leaf_size = data.len() / num_leaves;
    let total_nodes = 2 * num_leaves - 1;
    let mut tree: Vec<Hash> = primitives::alloc_uninit_vec(total_nodes);

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

    /// The parallel `merkle_tree` must be byte-identical to the per-leaf
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
