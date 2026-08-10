// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary Merkle tree with BLAKE3, SIMD-batching independent hashes across
//! leaves and internal levels through BLAKE3's multi-input backend.
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
//! Hashing uses standard BLAKE3. The VM instruction exposes the chaining value,
//! counter, block length, and flags needed to replay both leaf chunk processing
//! and parent nodes in-circuit. Whole-block leaves of 64 through 1024 bytes are
//! one BLAKE3 chunk, so batching them with `hash_many` is byte-identical to an
//! independent `blake3::hash` per leaf. Other sizes use the ordinary one-shot
//! API. Internal 64-byte child pairs always take the batched path.

#[cfg(target_arch = "aarch64")]
mod blake3_neon8;

pub use fiat_shamir::merkle::{Hash, hash_leaf, hash_pair};
use parallel::SendPtr;
use primitives::pretty_integer;
use zk_alloc::ArenaVec;

// Standard unkeyed BLAKE3 IV and single-chunk root flags, used to drive the
// crate's multi-input SIMD backend directly.
const B3_IV: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];
const B3_CHUNK_START: u8 = 1;
const B3_CHUNK_END: u8 = 2;
const B3_ROOT: u8 = 8;

/// Hashes per pool task: enough to amortize the widest SIMD batch while
/// keeping input references and output rows cache-resident.
const HASH_GROUP: usize = 1024;

/// SIMD-batch independent standard BLAKE3 hashes of contiguous `N`-byte
/// inputs. A whole-block input no longer than 1024 bytes is exactly one chunk;
/// counter zero, CHUNK_START on its first block, and CHUNK_END|ROOT on its last
/// reproduce `blake3::hash` byte-for-byte.
fn hash_many_oneshot_uninit<const N: usize>(
    platform: blake3::platform::Platform,
    data: &[u8],
    out: &mut [std::mem::MaybeUninit<Hash>],
) {
    const {
        assert!(N > 0 && N.is_multiple_of(64) && N <= 1024);
    }
    debug_assert_eq!(data.len(), out.len() * N);
    let inputs: Vec<&[u8; N]> = data.chunks_exact(N).map(|input| input.try_into().unwrap()).collect();
    // Hash is [u8; 32] with no padding; expose the contiguous output storage
    // expected by hash_many, which writes exactly 32 bytes per input.
    let out_bytes = unsafe { core::slice::from_raw_parts_mut(out.as_mut_ptr().cast::<u8>(), out.len() * 32) };
    platform.hash_many::<N>(
        &inputs,
        &B3_IV,
        0,
        blake3::IncrementCounter::No,
        0,
        B3_CHUNK_START,
        B3_CHUNK_END | B3_ROOT,
        out_bytes,
    );
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

fn hash_leaves_batched_uninit(
    platform: blake3::platform::Platform,
    data: &[u8],
    leaf_size: usize,
    out: &mut [std::mem::MaybeUninit<Hash>],
) {
    fn batched<const N: usize>(
        platform: blake3::platform::Platform,
        data: &[u8],
        out: &mut [std::mem::MaybeUninit<Hash>],
    ) {
        // Leaf hashing is the purest embarrassingly parallel phase here:
        // fixed-size independent groups, no cross-group dependency, one join
        // at the end. The pool's efficiency-core workers pull from the same claim
        // counter as the performance ones, so this is also where the otherwise
        // idle E-cores get spent (see the `parallel` crate).
        for_each_hash_group(out, |lo, outputs| {
            let len = outputs.len();
            let inputs = &data[lo * N..(lo + len) * N];
            // Eight-wide NEON for the complete groups; upstream `hash_many`
            // for whatever remains (a chunk's leaf count need not be a
            // multiple of 8).
            #[cfg(target_arch = "aarch64")]
            {
                let done = blake3_neon8::hash_complete_groups::<N>(inputs, outputs);
                if done < len {
                    hash_many_oneshot_uninit::<N>(platform, &inputs[done * N..], &mut outputs[done..]);
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            hash_many_oneshot_uninit::<N>(platform, inputs, outputs);
        });
    }
    match leaf_size {
        64 => batched::<64>(platform, data, out),
        128 => batched::<128>(platform, data, out),
        256 => batched::<256>(platform, data, out),
        512 => batched::<512>(platform, data, out),
        // The WHIR recursion levels commit F192 rows, so their leaves are
        // `num_interleaved * 24` bytes, a multiple of 64 but not a power of
        // two, which used to miss every batched arm and fall through to the
        // one-leaf-at-a-time path with no cross-leaf SIMD at all.
        192 => batched::<192>(platform, data, out),
        384 => batched::<384>(platform, data, out),
        768 => batched::<768>(platform, data, out),
        1024 => batched::<1024>(platform, data, out),
        _ => parallel::for_each_mut(out, |i, slot| {
            slot.write(hash_leaf(&data[i * leaf_size..(i + 1) * leaf_size]));
        }),
    }
}

fn hash_pairs_level_uninit(
    platform: blake3::platform::Platform,
    read: &[Hash],
    write: &mut [std::mem::MaybeUninit<Hash>],
) {
    debug_assert_eq!(read.len(), 2 * write.len());
    let read_bytes = unsafe { core::slice::from_raw_parts(read.as_ptr().cast::<u8>(), read.len() * 32) };
    for_each_hash_group(write, |lo, outputs| {
        let len = outputs.len();
        hash_many_oneshot_uninit::<64>(platform, &read_bytes[lo * 64..(lo + len) * 64], outputs);
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
    let platform = blake3::platform::Platform::detect();

    // 1. Leaves: independent standard BLAKE3 hashes.
    hash_leaves_batched_uninit(platform, data, leaf_size, &mut tree[..num_leaves]);

    // 2. Internal levels: parallel within a level, sequential across levels.
    let mut read_start = 0usize;
    let mut read_len = num_leaves;
    while read_len > 1 {
        let next_len = read_len >> 1;
        let read = unsafe { std::slice::from_raw_parts(tree.as_ptr().add(read_start).cast::<Hash>(), read_len) };
        let write_start = read_start + read_len;
        hash_pairs_level_uninit(platform, read, &mut tree[write_start..write_start + next_len]);

        read_start += read_len;
        read_len = next_len;
    }

    // SAFETY: leaves and each successive internal level initialize the full tree.
    unsafe { zk_alloc::assume_init(tree) }
}

#[cfg(test)]
mod leaf_hash_and_tree_tests {
    use super::*;

    /// The eight-wide NEON leaf kernel must reproduce `blake3::hash` for every
    /// leaf, at every leaf size the dispatch uses, including batches that are
    /// not a multiple of eight.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn neon8_leaves_match_standard_blake3() {
        fn check<const N: usize>() {
            for n_leaves in [1usize, 7, 8, 9, 16, 37, 64] {
                let data: Vec<u8> = (0..n_leaves * N).map(|i| (i * 31 + 7) as u8).collect();
                let mut out: Vec<std::mem::MaybeUninit<Hash>> =
                    (0..n_leaves).map(|_| std::mem::MaybeUninit::uninit()).collect();
                let done = super::blake3_neon8::hash_complete_groups::<N>(&data, &mut out);
                assert_eq!(done, n_leaves / 8 * 8);
                for i in 0..done {
                    // SAFETY: the kernel initialized the first `done` slots.
                    let got = unsafe { out[i].assume_init() };
                    assert_eq!(
                        got,
                        *blake3::hash(&data[i * N..(i + 1) * N]).as_bytes(),
                        "leaf {i} of {n_leaves} at N={N}"
                    );
                }
            }
        }
        check::<64>();
        check::<128>();
        check::<256>();
        check::<192>();
        check::<384>();
        check::<512>();
        check::<768>();
        check::<1024>();
    }

    /// End-to-end through the dispatcher at the L0 leaf size this branch
    /// actually commits with (64 lanes x 8-byte F64 = 512 bytes).
    #[test]
    fn leaf_dispatch_matches_standard_blake3() {
        for leaf in [64usize, 128, 192, 256, 384, 512, 768, 1024] {
            let n_leaves = 37usize;
            let data: Vec<u8> = (0..n_leaves * leaf).map(|i| (i * 17 + 3) as u8).collect();
            let mut out: Vec<std::mem::MaybeUninit<Hash>> =
                (0..n_leaves).map(|_| std::mem::MaybeUninit::uninit()).collect();
            hash_leaves_batched_uninit(blake3::platform::Platform::detect(), &data, leaf, &mut out);
            for i in 0..n_leaves {
                // SAFETY: the dispatcher initializes every slot.
                let got = unsafe { out[i].assume_init() };
                assert_eq!(
                    got,
                    *blake3::hash(&data[i * leaf..(i + 1) * leaf]).as_bytes(),
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
