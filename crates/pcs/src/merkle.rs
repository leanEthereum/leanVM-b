// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with BLAKE2s, SIMD-batching independent hashes across
//! leaves and internal levels through the lane-transposed multi-input hasher in
//! [`primitives::blake2s`].
//!
//! The committer's half. What a proof actually carries (the digest encoding,
//! the leaf/node hashes, one phase's pruned octopus) lives in
//! [`fiat_shamir::merkle`], beside the transcript that transports it; this
//! module only builds the tree those phases are cut from.
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
//! Hashing is standard BLAKE2s-256. Independent hashes of equal-length inputs
//! step their block counters in lockstep, so the batched hasher is
//! byte-identical to an independent [`hash_leaf`] per input; the leaf-size
//! dispatch below exists only to make the length a compile-time constant.
//! Leaves of other sizes use the scalar path. Internal 64-byte child pairs,
//! which are one compression each, always take the batched path.

pub use fiat_shamir::merkle::{Hash, hash_leaf, hash_pair};
use parallel::SendPtr;
use primitives::field::F64;
use primitives::pretty_integer;
use zk_alloc::ArenaVec;

/// Hashes per pool task: enough to amortize the widest SIMD batch while
/// keeping input references and output rows cache-resident.
const HASH_GROUP: usize = 1024;

/// Batch independent BLAKE2s hashes of contiguous `N`-byte inputs into
/// uninitialized output slots.
fn hash_many_uninit<const N: usize>(data: &[u8], out: &mut [std::mem::MaybeUninit<Hash>]) {
    const {
        assert!(N > 0 && N.is_multiple_of(64));
    }
    debug_assert_eq!(data.len(), out.len() * N);
    // Hash is [u8; 32] with no padding; expose the contiguous output storage
    // the batched hasher writes 32 bytes per input into.
    let out_bytes = unsafe { core::slice::from_raw_parts_mut(out.as_mut_ptr().cast::<u8>(), out.len() * 32) };
    primitives::blake2s::hash_many::<N>(data, out_bytes);
}

/// Dispatch one pool task per `HASH_GROUP`-sized output group, handing each
/// `f` the group's start index and its own output window.
fn for_each_hash_group(
    out: &mut [std::mem::MaybeUninit<Hash>],
    f: impl Fn(usize, &mut [std::mem::MaybeUninit<Hash>]) + Sync,
) {
    let n_groups = out.len().div_ceil(HASH_GROUP);
    let out_base = SendPtr(out.as_mut_ptr());
    let out_len = out.len();
    parallel::for_each(n_groups, |g| {
        let lo = g * HASH_GROUP;
        let len = HASH_GROUP.min(out_len - lo);
        // SAFETY: the queue hands each `g` to exactly one worker, and group `g`
        // writes only `out[lo .. lo+len]`, so the mutable ranges are pairwise
        // disjoint and in bounds.
        f(lo, unsafe { out_base.slice(lo, len) });
    });
}

fn hash_leaves_batched_uninit(data: &[u8], leaf_size: usize, out: &mut [std::mem::MaybeUninit<Hash>]) {
    fn batched<const N: usize>(data: &[u8], out: &mut [std::mem::MaybeUninit<Hash>]) {
        // Leaf hashing is the purest embarrassingly parallel phase here:
        // fixed-size independent groups, no cross-group dependency, one join
        // at the end. The pool's efficiency-core workers pull from the same claim
        // counter as the performance ones, so this is also where the otherwise
        // idle E-cores get spent (see the `parallel` crate).
        for_each_hash_group(out, |lo, outputs| {
            let len = outputs.len();
            hash_many_uninit::<N>(&data[lo * N..(lo + len) * N], outputs);
        });
    }
    match leaf_size {
        64 => batched::<64>(data, out),
        128 => batched::<128>(data, out),
        256 => batched::<256>(data, out),
        512 => batched::<512>(data, out),
        // The WHIR recursion levels commit F192 rows, so their leaves are
        // `num_interleaved * 24` bytes, a multiple of 64 but not a power of
        // two, which used to miss every batched arm and fall through to the
        // one-leaf-at-a-time path with no cross-leaf SIMD at all.
        192 => batched::<192>(data, out),
        384 => batched::<384>(data, out),
        768 => batched::<768>(data, out),
        1024 => batched::<1024>(data, out),
        _ => parallel::for_each_mut(out, |i, slot| {
            slot.write(hash_leaf(&data[i * leaf_size..(i + 1) * leaf_size]));
        }),
    }
}

fn hash_pairs_level_uninit(read: &[Hash], write: &mut [std::mem::MaybeUninit<Hash>]) {
    debug_assert_eq!(read.len(), 2 * write.len());
    let read_bytes = unsafe { core::slice::from_raw_parts(read.as_ptr().cast::<u8>(), read.len() * 32) };
    for_each_hash_group(write, |lo, outputs| {
        let len = outputs.len();
        hash_many_uninit::<64>(&read_bytes[lo * 64..(lo + len) * 64], outputs);
    });
}

/// Compute the full Merkle tree (flat layout, see module docs) for `data`
/// split into `num_leaves` equal-sized leaves.
#[tracing::instrument(
    name = "Hashing",
    skip_all,
    fields(
        num_leaves = %pretty_integer(num_leaves),
        leaf_size = %pretty_integer(data.len().checked_div(num_leaves).unwrap_or(0))
    )
)]
pub fn merkle_tree(data: &[u8], num_leaves: usize) -> ArenaVec<Hash> {
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
    let mut tree = zk_alloc::alloc_uninit(total_nodes);

    // 1. Leaves: independent standard BLAKE2s hashes.
    hash_leaves_batched_uninit(data, leaf_size, &mut tree[..num_leaves]);

    // 2. Internal levels: parallel within a level, sequential across levels.
    internal_levels_uninit(&mut tree, num_leaves);

    // SAFETY: leaves and each successive internal level initialize the full tree.
    unsafe { zk_alloc::assume_init(tree) }
}

/// Merkle tree over an interleaved matrix of `row_words`-wide rows, hashing each
/// row zero-extended to `leaf_words`.
///
/// A padding-free L0 commitment interleaves only the lanes that carry data, while
/// the leaf image stays the full `leaf_words` the verifier expects: the lanes past
/// `row_words` are the stacked witness's zero padding, whose codeword is zero.
/// Staging a tile of leaves supplies those zeros without materialising them in the
/// codeword, so the hashed image is exactly the one a `leaf_words`-wide codeword
/// would have produced.
#[tracing::instrument(
    name = "Hashing",
    skip_all,
    fields(num_leaves = %pretty_integer(num_leaves), leaf_size = %pretty_integer(leaf_words * 8))
)]
pub fn merkle_tree_padded_rows(data: &[F64], num_leaves: usize, row_words: usize, leaf_words: usize) -> ArenaVec<Hash> {
    assert!(
        num_leaves.is_power_of_two() && num_leaves > 0,
        "num_leaves must be power of 2"
    );
    assert_eq!(
        data.len(),
        row_words * num_leaves,
        "data is num_leaves rows of row_words"
    );
    assert!(
        0 < row_words && row_words <= leaf_words && leaf_words <= STAGE_TILE_WORDS,
        "leaf holds the committed lanes, zero-padded, and fits the staging tile"
    );
    if row_words == leaf_words {
        // Nothing to pad, so nothing to stage: hash the rows where they lie. The
        // staging path costs a copy of the whole codeword and shrinks the hasher's
        // batch from `HASH_GROUP` leaves to what the tile holds, and a full-width
        // commitment would pay both for no zeros at all.
        // SAFETY: F64 is repr(transparent) over u64, so on this (LE) target the
        // slice is the little-endian word image the leaves are hashed from, exactly
        // what `fiat_shamir::merkle::hash_row` serializes.
        let bytes = unsafe { core::slice::from_raw_parts(data.as_ptr().cast::<u8>(), std::mem::size_of_val(data)) };
        return merkle_tree(bytes, num_leaves);
    }
    let total_nodes = 2 * num_leaves - 1;
    let mut tree = zk_alloc::alloc_uninit(total_nodes);
    hash_leaves_padded_rows_uninit(data, row_words, leaf_words, &mut tree[..num_leaves]);
    internal_levels_uninit(&mut tree, num_leaves);
    // SAFETY: leaves and each successive internal level initialize the full tree.
    unsafe { zk_alloc::assume_init(tree) }
}

/// Staging tile, in words: 16 KiB, so the transposed leaves stay L1-resident and
/// the tile lives on the task's stack. Also bounds the leaf width, so an L0 leaf
/// (`2^INITIAL_FOLDING_FACTOR` words) has to fit.
const STAGE_TILE_WORDS: usize = 2048;
const _: () = assert!((1usize << crate::whir_config::INITIAL_FOLDING_FACTOR) <= STAGE_TILE_WORDS);

fn hash_leaves_padded_rows_uninit(
    data: &[F64],
    row_words: usize,
    leaf_words: usize,
    out: &mut [std::mem::MaybeUninit<Hash>],
) {
    let per_tile = STAGE_TILE_WORDS / leaf_words;
    for_each_hash_group(out, |lo, outputs| {
        // Zeroed once per task: the lanes past `row_words` are the witness's zero
        // padding, so the tile's tail columns are never written again.
        let mut tile = [F64::ZERO; STAGE_TILE_WORDS];
        for (t, chunk) in outputs.chunks_mut(per_tile).enumerate() {
            let base = lo + t * per_tile;
            let len = chunk.len();
            for (i, leaf) in tile.chunks_mut(leaf_words).take(len).enumerate() {
                leaf[..row_words].copy_from_slice(&data[(base + i) * row_words..][..row_words]);
            }
            // SAFETY: F64 is repr(transparent) over u64, so the tile's prefix is the
            // little-endian byte image of `len` leaves of `leaf_words` words, which
            // on this (LE) target is what `fiat_shamir::merkle::hash_row`
            // serializes. Exactly `len * leaf_words` initialized elements are cast.
            let bytes = unsafe { core::slice::from_raw_parts(tile.as_ptr().cast::<u8>(), len * leaf_words * 8) };
            // Hash inline: this already runs inside a pool task, so
            // `hash_leaves_batched_uninit` would dispatch a nested one.
            if (leaf_words * 8).is_multiple_of(64) {
                // SAFETY: Hash is [u8; 32] with no padding, so the output slots are
                // `len * 32` contiguous writable bytes.
                let out_bytes = unsafe { core::slice::from_raw_parts_mut(chunk.as_mut_ptr().cast::<u8>(), len * 32) };
                primitives::blake2s::hash_many_dyn(bytes, leaf_words * 8, out_bytes);
            } else {
                for (i, slot) in chunk.iter_mut().enumerate() {
                    slot.write(hash_leaf(&bytes[i * leaf_words * 8..(i + 1) * leaf_words * 8]));
                }
            }
        }
    });
}

fn internal_levels_uninit(tree: &mut [std::mem::MaybeUninit<Hash>], num_leaves: usize) {
    let mut read_start = 0usize;
    let mut read_len = num_leaves;
    while read_len > 1 {
        let next_len = read_len >> 1;
        let read = unsafe { std::slice::from_raw_parts(tree.as_ptr().add(read_start).cast::<Hash>(), read_len) };
        let write_start = read_start + read_len;
        hash_pairs_level_uninit(read, &mut tree[write_start..write_start + next_len]);

        read_start += read_len;
        read_len = next_len;
    }
}

#[cfg(test)]
mod leaf_hash_and_tree_tests {
    use super::*;

    /// Every batched arm of the dispatcher must agree with the scalar
    /// [`hash_leaf`], including leaf counts that are not a multiple of the
    /// batch width.
    #[test]
    fn leaf_dispatch_matches_scalar_hash() {
        for leaf in [64usize, 128, 192, 256, 384, 512, 768, 1024] {
            let n_leaves = 37usize;
            let data: Vec<u8> = (0..n_leaves * leaf).map(|i| (i * 17 + 3) as u8).collect();
            let mut out: Vec<std::mem::MaybeUninit<Hash>> =
                (0..n_leaves).map(|_| std::mem::MaybeUninit::uninit()).collect();
            hash_leaves_batched_uninit(&data, leaf, &mut out);
            for i in 0..n_leaves {
                // SAFETY: the dispatcher initializes every slot.
                let got = unsafe { out[i].assume_init() };
                assert_eq!(
                    got,
                    hash_leaf(&data[i * leaf..(i + 1) * leaf]),
                    "leaf {i} at leaf_size={leaf}"
                );
            }
        }
    }

    /// Sequential (per-leaf `hash_leaf`) reference for the parallel
    /// [`merkle_tree`].
    fn merkle_tree_sequential(data: &[u8], num_leaves: usize) -> Vec<Hash> {
        assert!(num_leaves.is_power_of_two() && num_leaves > 0);
        assert_eq!(data.len() % num_leaves, 0);

        let leaf_size = data.len() / num_leaves;
        let total_nodes = 2 * num_leaves - 1;
        let mut tree = Vec::with_capacity(total_nodes);

        for (i, leaf) in data.chunks(leaf_size).enumerate() {
            debug_assert_eq!(tree.len(), i);
            tree.push(hash_leaf(leaf));
        }
        let mut read_start = 0usize;
        let mut read_len = num_leaves;
        while read_len > 1 {
            let next_len = read_len >> 1;
            for i in 0..next_len {
                let left = tree[read_start + 2 * i];
                let right = tree[read_start + 2 * i + 1];
                tree.push(hash_pair(&left, &right));
            }
            read_start += read_len;
            read_len = next_len;
        }
        tree
    }

    /// The parallel `merkle_tree` must be byte-identical to the per-leaf
    /// `merkle_tree_sequential` (which uses `hash_leaf`): same root, same nodes,
    /// across leaf sizes incl. an odd (non-32-multiple) leaf and group boundaries.
    #[test]
    fn batched_matches_sequential() {
        for (num_leaves, leaf_size) in [
            (64usize, 64usize),
            (64, 128),
            (64, 256),
            (4096, 512),
            (64, 1024),
            (8, 32),
            (2, 48),
            (8192, 16),
            (1, 32),
        ] {
            let data: Vec<u8> = (0..num_leaves * leaf_size)
                .map(|i| (i.wrapping_mul(131) ^ 0x5a) as u8)
                .collect();
            assert_eq!(
                &merkle_tree(&data, num_leaves)[..],
                &merkle_tree_sequential(&data, num_leaves)[..],
                "num_leaves={num_leaves} leaf_size={leaf_size}"
            );
        }
    }

    /// The zero-extending tree must equal the tree of the full-width matrix it
    /// stands for. Sizes cross the staging tile and the hash-group boundary, and
    /// include row widths that are not powers of two and not multiples of the tile.
    #[test]
    fn padded_rows_tree_matches_full_width() {
        for (num_leaves, row_words, leaf_words) in [
            (8usize, 64usize, 64usize),
            (2048, 37, 64),
            (64, 1, 64),
            (1024, 8, 8),
            (32, 5, 8),
            // 40-byte leaves: not whole blocks, so the leaf hashing takes the
            // scalar arm rather than the batched one.
            (16, 3, 5),
        ] {
            let data: Vec<F64> = (0..row_words * num_leaves)
                .map(|i| F64(i.wrapping_mul(0x9E37_79B9_7F4A_7C15) as u64 | 1))
                .collect();
            let mut padded = vec![F64::ZERO; num_leaves * leaf_words];
            for pos in 0..num_leaves {
                padded[pos * leaf_words..pos * leaf_words + row_words]
                    .copy_from_slice(&data[pos * row_words..(pos + 1) * row_words]);
            }
            // SAFETY: F64 is repr(transparent) over u64; on this LE target the slice
            // is the little-endian word image the leaves are hashed from.
            let bytes = unsafe { core::slice::from_raw_parts(padded.as_ptr().cast::<u8>(), padded.len() * 8) };
            assert_eq!(
                &merkle_tree_padded_rows(&data, num_leaves, row_words, leaf_words)[..],
                &merkle_tree(bytes, num_leaves)[..],
                "num_leaves={num_leaves} row_words={row_words} leaf_words={leaf_words}"
            );
        }
    }
}
