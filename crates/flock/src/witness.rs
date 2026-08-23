// CREDIT: https://github.com/succinctlabs/flock (flock-prover), MIT OR Apache-2.0.
//! Bit-packing and R1CS-row helpers for the monolithic hash R1CS modules
//! (only `sha3` in this vendored subset).

use primitives::bits::transpose_8_u64s_to_64_bytes;
use zk_alloc::ArenaVec;

/// OR the low 32 bits of `val` into `buf` starting at bit-offset `bit_off`.
/// Handles u64 straddling when `bit_off % 64 > 32`.
#[inline(always)]
/// of the `u64` words on a little-endian target.
pub(crate) fn packed_bytes(words: &[u64]) -> &[u8] {
    const _: () = assert!(
        cfg!(target_endian = "little"),
        "packed witness bytes assume little-endian"
    );
    // SAFETY: `u64` has no padding or invalid bit patterns, and `u8`'s
    // alignment divides `u64`'s, so the words are a valid `8 · len` byte slice.
    unsafe { core::slice::from_raw_parts(words.as_ptr().cast::<u8>(), words.len() * 8) }
}

// ---------------------------------------------------------------------------
// Generic witness packing driver.
// ---------------------------------------------------------------------------

/// Drive the parallel chunked witness build for `n_blocks` instances padded
/// to `2^n_blocks_log` slots. Returns `(z, a, b, z_lincheck)`: the three
/// bit-packed `u64` tables (`K / 64` words per instance) and the lincheck
/// byte stripe.
///
/// `per_block(initial, z_u64, a_u64, b_u64)` populates one block's worth of
/// `(z, a, b)` data: 3 zero-initialized `u64`-buffers of length `K / 64`.
/// `K` is derived from `k_log`. `initial_states.len()` may be less than
/// `2^n_blocks_log`.
///
/// `padding` controls what fills the trailing `2^n_blocks_log −
/// initial_states.len()` slots:
/// - `None`: leave them all-zero (trivial constraint satisfaction).
/// - `Some(p)`: build a real block from `p` in every padding slot. Encoders
///   that pin a constant wire need this so the constant column is all-ones
///   across *every* batched instance (see `lincheck's `LincheckCircuit::const_pin_col``).
pub(crate) fn drive_witness_packed_and_lincheck<S: Sync, F>(
    initial_states: &[S],
    padding: Option<&S>,
    n_blocks_log: usize,
    k_log: usize,
    per_block: F,
) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>)
where
    F: Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
{
    let k = 1usize << k_log;
    let u64_per_block = k / 64;
    let n_total = 1usize << n_blocks_log;
    let n_blocks = initial_states.len();
    assert!(
        n_blocks <= n_total,
        "{n_blocks} blocks > 2^{n_blocks_log} = {n_total} slots"
    );
    assert!(
        n_total >= 8 && n_total.is_multiple_of(8),
        "lincheck stripe layout requires n_total ≥ 8 and divisible by 8"
    );

    let total_words = n_total * u64_per_block;
    // Zero inside the parallel loop because the builders OR bits into each group.
    // SAFETY (x3): the parallel loop below writes every element of z/a/b before
    // any is read: each group memsets its own slice, then ORs bits into it.
    let mut z = unsafe { ArenaVec::<u64>::uninitialized(total_words) };
    let mut a = unsafe { ArenaVec::<u64>::uninitialized(total_words) };
    let mut b = unsafe { ArenaVec::<u64>::uninitialized(total_words) };
    // SAFETY: group `g` writes chunk `g` of the stripe table in full, since the
    // transpose stores all 64 bytes of each of the `u64_per_block` destination
    // windows and `u64_per_block * 64 == k == stripe.len()`. The chunk counts
    // match, so every chunk is claimed by exactly one group.
    let mut z_lincheck = unsafe { ArenaVec::<u8>::uninitialized((n_total / 8) * k) };

    // Four output tables at two widths, indexed by the same group: `z`/`a`/`b`
    // take eight blocks' packed words, `z_lincheck` takes one byte stripe.
    let z_chunks = parallel::Chunks::new(&mut z, 8 * u64_per_block);
    let a_chunks = parallel::Chunks::new(&mut a, 8 * u64_per_block);
    let b_chunks = parallel::Chunks::new(&mut b, 8 * u64_per_block);
    let stripe_chunks = parallel::Chunks::new(&mut z_lincheck, k);
    debug_assert_eq!(z_chunks.count(), stripe_chunks.count());
    parallel::for_each(z_chunks.count(), |g| {
        // SAFETY: each group `g` takes chunk `g` of each table exactly once, and
        // all four tables stay borrowed for the whole dispatch.
        let (z_grp, a_grp, b_grp, stripe) =
            unsafe { (z_chunks.get(g), a_chunks.get(g), b_chunks.get(g), stripe_chunks.get(g)) };
        z_grp.fill(0);
        a_grp.fill(0);
        b_grp.fill(0);
        for k_in in 0..8 {
            let global_idx = 8 * g + k_in;
            let init: &S = if global_idx < n_blocks {
                &initial_states[global_idx]
            } else if let Some(p) = padding {
                // Fill the padding slot with a real block so its constant
                // wire is set (see `padding` docs above).
                p
            } else {
                // No padding block, leave this slot zero.
                continue;
            };
            let range = k_in * u64_per_block..(k_in + 1) * u64_per_block;
            let z_u64 = &mut z_grp[range.clone()];
            let a_u64 = &mut a_grp[range.clone()];
            let b_u64 = &mut b_grp[range];
            per_block(init, z_u64, a_u64, b_u64);
        }

        // Bit-transpose 8 z chunks into the lincheck stripe.
        for i in 0..u64_per_block {
            let lanes: [u64; 8] = [
                z_grp[i],
                z_grp[u64_per_block + i],
                z_grp[2 * u64_per_block + i],
                z_grp[3 * u64_per_block + i],
                z_grp[4 * u64_per_block + i],
                z_grp[5 * u64_per_block + i],
                z_grp[6 * u64_per_block + i],
                z_grp[7 * u64_per_block + i],
            ];
            transpose_8_u64s_to_64_bytes(&lanes, &mut stripe[i * 64..i * 64 + 64]);
        }
    });

    (z, a, b, z_lincheck)
}
