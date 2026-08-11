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

    // SAFETY: leaves and each successive internal level initialize the full tree.
    unsafe { zk_alloc::assume_init(tree) }
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
}
