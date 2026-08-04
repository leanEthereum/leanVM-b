//! Additive NTT over GF(2^64) using the LCH novel polynomial basis: the
//! encoding layer of the 64-bit transition (commitments over K = F_{2^64}).
//!
//! The transform uses the same subspace-polynomial construction,
//! neighbors-last layer ordering, and SoA interleaved layout as the
//! extension-field transform. Its inner butterflies use architecture-specific
//! SIMD kernels where available; large transforms are memory-bandwidth bound.

use primitives::field::F64;

/// Normalized subspace-polynomial evaluation table (see the extension-field twin).
fn generate_evals_from_subspace(basis: &[F64]) -> Vec<Vec<F64>> {
    let l = basis.len();
    let mut evals: Vec<Vec<F64>> = Vec::with_capacity(l);
    evals.push(basis.to_vec());
    for i in 1..l {
        let mut row = Vec::with_capacity(l - i);
        for k in 1..evals[i - 1].len() {
            let val = evals[i - 1][k] * (evals[i - 1][k] + evals[i - 1][0]);
            row.push(val);
        }
        evals.push(row);
    }
    for row in evals.iter_mut() {
        let inv = row[0].inv();
        for v in row.iter_mut() {
            *v *= inv;
        }
    }
    evals
}

/// `Σ_j bit_j(idx) · basis[j]`.
#[inline]
fn span_get(basis: &[F64], idx: usize) -> F64 {
    let mut acc = F64::ZERO;
    for (j, &b) in basis.iter().enumerate() {
        if (idx >> j) & 1 == 1 {
            acc += b;
        }
    }
    acc
}

/// Additive NTT over F_{2^64} with the standard polynomial-basis subspace
/// `{1, x, x², …}`: the F_2-subspace is `{0, 1, …, 2^ℓ−1}` under the natural
/// integer encoding, exactly as in the extension-field version (whose domain already
/// lived inside this very subfield).
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    evals: Vec<Vec<F64>>,
}

impl AdditiveNttF64 {
    fn new(basis: &[F64]) -> Self {
        Self {
            evals: generate_evals_from_subspace(basis),
        }
    }

    /// Standard NTT with basis `{1, x, …, x^(dim-1)}`. Requires `dim ≤ 63` so
    /// the evaluation domain (and the twiddles) stay inside F_{2^64} without
    /// wrap; far beyond any codeword size in use.
    pub fn standard(dim: usize) -> Self {
        assert!(dim <= 63, "standard NTT requires dim ≤ 63");
        let basis: Vec<F64> = (0..dim).map(|i| F64(1u64 << i)).collect();
        Self::new(&basis)
    }

    pub fn log_domain_size(&self) -> usize {
        self.evals.len()
    }

    /// Twiddle at `(layer, block)`; see the extension-field twin for the convention.
    pub fn twiddle(&self, layer: usize, block: usize) -> F64 {
        let v = &self.evals[self.log_domain_size() - layer - 1];
        span_get(&v[1..], block)
    }

    /// Forward additive NTT in place (scalar; used directly for tests and as
    /// the small-input path).
    pub fn forward_transform_scalar(&self, data: &mut [F64]) {
        let log_d = log2_pow2(data.len());
        assert!(log_d <= self.log_domain_size());
        for layer in 0..log_d {
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half) {
                    let idx1 = idx0 | block_size_half;
                    let v = data[idx1];
                    let new_u = data[idx0] + v * twiddle;
                    data[idx0] = new_u;
                    data[idx1] = v + new_u;
                }
            }
        }
    }

    /// Interleaved (SoA) forward NTT of `num_ntts` independent lanes sharing
    /// the twiddle structure (`data[pos * num_ntts + lane]`, so one Merkle leaf
    /// is one position, a contiguous slice of `num_ntts` F_{2^64} elements),
    /// starting at `start_layer`: the RS-encoding caller replicates the message
    /// into all `2^rate` sub-blocks, which IS the exact post-layer-`rate` state,
    /// and skips those layers here.
    pub fn forward_transform_interleaved_from_layer(&self, data: &mut [F64], num_ntts: usize, start_layer: usize) {
        self.forward_transform_interleaved_parallel_from_layer(data, num_ntts, start_layer);
    }

    /// Scalar reference for the interleaved forward NTT (test oracle).
    pub fn forward_transform_interleaved_scalar_from_layer(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start_layer: usize,
    ) {
        let n_total = data.len();
        let log_d = log2_pow2(n_total / num_ntts);

        for layer in start_layer..log_d {
            let num_blocks = 1usize << layer;
            let block_size = 1usize << (log_d - layer);
            let block_size_half = block_size >> 1;
            let block_elems = block_size * num_ntts;
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block * block_elems;
                for row in 0..block_size_half {
                    let off_top = block_start + row * num_ntts;
                    let off_bot = off_top + block_size_half * num_ntts;
                    for lane in 0..num_ntts {
                        let v = data[off_bot + lane];
                        let new_u = data[off_top + lane] + v * twiddle;
                        data[off_top + lane] = new_u;
                        data[off_bot + lane] = v + new_u;
                    }
                }
            }
        }
    }

    /// Parallel interleaved forward NTT, cache-blocked like the extension-field twin:
    /// top layers sweep the full buffer (fused two-layer passes, row-parallel),
    /// deep layers run as cache-resident sub-NTTs in parallel. Constants are
    /// re-derived for 8-byte elements.
    pub fn forward_transform_interleaved_parallel_from_layer(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start_layer: usize,
    ) {
        assert!(num_ntts.is_power_of_two() && num_ntts > 0);
        let n_total = data.len();
        assert_eq!(n_total % num_ntts, 0);
        let log_d = log2_pow2(n_total / num_ntts);
        assert!(log_d <= self.log_domain_size());
        assert!(start_layer <= log_d);

        // Target sub-group ≈ 2 MB; each position is num_ntts × 8 bytes.
        const TARGET_SUBGROUP_LOG_BYTES: usize = 21;
        let log_bytes_per_position = 3 + log2_pow2(num_ntts);
        let target_log_positions = TARGET_SUBGROUP_LOG_BYTES.saturating_sub(log_bytes_per_position);
        let cache_n_top = log_d.saturating_sub(target_log_positions);

        const PARALLEL_FLOOR_LOG_D: usize = 12;
        const MIN_SUB_LOG: usize = 8;
        let n_top = if log_d >= PARALLEL_FLOOR_LOG_D {
            let want_subs_log = log2_pow2(parallel::num_threads().next_power_of_two());
            let max_n_top = log_d.saturating_sub(MIN_SUB_LOG);
            cache_n_top.max(want_subs_log.min(max_n_top))
        } else {
            cache_n_top
        };
        if n_top == 0 || log_d < 8 {
            self.forward_transform_interleaved_scalar_from_layer(data, num_ntts, start_layer);
            return;
        }

        // Top layers: full-buffer sweeps, fusing two layers where possible.
        let mut layer = start_layer.min(n_top);
        while layer < n_top {
            let num_blocks = 1usize << layer;
            let block_size = 1usize << (log_d - layer);
            let block_elems = block_size * num_ntts;

            if layer + 2 < n_top && block_size >= 8 {
                // Fuse three layers: one pass over the block instead of
                // three. At the top layers a pass is a DRAM round-trip of the
                // whole codeword, so the pass count sets the cost.
                let eighth = block_size >> 3;
                for block in 0..num_blocks {
                    let mut t = [F64::ZERO; 7];
                    t[0] = self.twiddle(layer, block);
                    for s in 0..2 {
                        t[1 + s] = self.twiddle(layer + 1, 2 * block + s);
                    }
                    for s in 0..4 {
                        t[3 + s] = self.twiddle(layer + 2, 4 * block + s);
                    }
                    let start = block * block_elems;
                    butterfly_interleaved_fused_3layer_par_rows(
                        &mut data[start..start + block_elems],
                        &t,
                        eighth,
                        num_ntts,
                    );
                }
                layer += 3;
            } else if layer + 1 < n_top && block_size >= 4 {
                let quarter = block_size >> 2;
                for block in 0..num_blocks {
                    let t_outer = self.twiddle(layer, block);
                    let t_inner_a = self.twiddle(layer + 1, 2 * block);
                    let t_inner_b = self.twiddle(layer + 1, 2 * block + 1);
                    let start = block * block_elems;
                    butterfly_interleaved_fused_2layer_par_rows(
                        &mut data[start..start + block_elems],
                        t_outer,
                        t_inner_a,
                        t_inner_b,
                        quarter,
                        num_ntts,
                    );
                }
                layer += 2;
            } else {
                let block_size_half = block_size >> 1;
                for block in 0..num_blocks {
                    let t = self.twiddle(layer, block);
                    let start = block * block_elems;
                    butterfly_interleaved_block_par_rows(
                        &mut data[start..start + block_elems],
                        t,
                        block_size_half,
                        num_ntts,
                    );
                }
                layer += 1;
            }
        }

        // Deep layers: parallel cache-resident sub-NTTs.
        let sub_size_positions = 1usize << (log_d - n_top);
        let sub_elems = sub_size_positions * num_ntts;
        parallel::chunks_mut(data, sub_elems, |sub_idx, sub_data| {
            for layer in n_top.max(start_layer)..log_d {
                let layer_in_sub = layer - n_top;
                let num_blocks_in_sub = 1usize << layer_in_sub;
                let block_size = 1usize << (log_d - layer);
                let block_size_half = block_size >> 1;
                let block_elems = block_size * num_ntts;
                for block_in_sub in 0..num_blocks_in_sub {
                    let global_block = sub_idx * num_blocks_in_sub + block_in_sub;
                    let twiddle = self.twiddle(layer, global_block);
                    let block_start = block_in_sub * block_elems;
                    let block = &mut sub_data[block_start..block_start + block_elems];
                    butterfly_interleaved_block(block, twiddle, block_size_half, num_ntts);
                }
            }
        });
    }

    /// Inverse additive NTT in place (scalar). Exact inverse of the forward
    /// transform; used by tests.
    #[cfg(test)]
    pub fn inverse_transform(&self, data: &mut [F64]) {
        let log_d = log2_pow2(data.len());
        assert!(log_d <= self.log_domain_size());
        for layer in (0..log_d).rev() {
            let num_blocks = 1usize << layer;
            let block_size_half = 1usize << (log_d - layer - 1);
            for block in 0..num_blocks {
                let twiddle = self.twiddle(layer, block);
                let block_start = block << (log_d - layer);
                for idx0 in block_start..(block_start + block_size_half) {
                    let idx1 = idx0 | block_size_half;
                    let u = data[idx0];
                    let new_v = data[idx1] + u;
                    data[idx1] = new_v;
                    data[idx0] = u + new_v * twiddle;
                }
            }
        }
    }
}

fn butterfly_interleaved_block_par_rows(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    const PARALLEL_ROW_THRESHOLD: usize = 1024;
    if block_size_half < PARALLEL_ROW_THRESHOLD {
        butterfly_interleaved_block(block, twiddle, block_size_half, num_ntts);
        return;
    }
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    let bot_base = parallel::SendPtr(bot.as_mut_ptr());
    parallel::chunks_mut(top, num_ntts, |r, top_row| {
        // SAFETY: distinct `r` take disjoint `num_ntts`-windows of `bot`, the
        // same windows `chunks_mut` just proved disjoint in `top`; the two halves
        // are themselves disjoint by `split_at_mut`.
        let bot_row = unsafe { bot_base.slice(r * num_ntts, top_row.len()) };
        butterfly_lanes(top_row, bot_row, twiddle);
    });
}

/// Run `do_one` over every row group of a fused multi-layer block: `block` is
/// `N * stride_rows * num_ntts` elements, and group `r` owns the `N` windows
/// `block[i * stride + r * num_ntts .. + num_ntts]` for `i` in `0..N`.
/// Distinct `r` give disjoint windows within each slab, and the slabs are
/// disjoint by construction, so the groups are pairwise disjoint, which is what
/// makes one pointer plus an index sound where `N` nested `split_at_mut`s would
/// be needed to say the same thing.
fn fused_rows<const N: usize>(
    block: &mut [F64],
    stride_rows: usize,
    num_ntts: usize,
    do_one: impl Fn(&mut [&mut [F64]; N]) + Sync,
) {
    const PARALLEL_ROW_THRESHOLD: usize = 512;
    let stride = stride_rows * num_ntts;
    debug_assert_eq!(block.len(), N * stride);

    let base = parallel::SendPtr(block.as_mut_ptr());
    let group = |r: usize| {
        let off = r * num_ntts;
        // SAFETY: see the disjointness argument above; `off + num_ntts <= stride`
        // because `r < stride_rows`.
        let mut rows: [&mut [F64]; N] = std::array::from_fn(|i| unsafe { base.slice(i * stride + off, num_ntts) });
        do_one(&mut rows);
    };

    if stride_rows < PARALLEL_ROW_THRESHOLD {
        for r in 0..stride_rows {
            group(r);
        }
    } else {
        parallel::for_each(stride_rows, group);
    }
}

/// Fused three-layer (radix-8) butterfly over one layer-L block: applies
/// layers L, L+1 and L+2 in a single pass over the block's rows, instead of
/// the three full-buffer sweeps they would otherwise cost.
///
/// The eight participating rows stay L1-resident across all twelve
/// butterflies, exactly as the four rows do in the fused-2 kernel; each
/// butterfly is the same lane kernel, already 8-wide on NEON and AVX-512.
///
/// `block` is `8 * eighth * num_ntts` elements. For each `r ∈ 0..eighth` the
/// rows `r + i·eighth` for `i ∈ 0..8` participate. Layer L pairs them at
/// distance `4·eighth`, layer L+1 at `2·eighth`, layer L+2 at `eighth`.
/// `t` holds the seven twiddles breadth-first: `t[0]` is layer L, `t[1..3]`
/// layer L+1 (one per half), `t[3..7]` layer L+2 (one per quarter).
fn butterfly_interleaved_fused_3layer_par_rows(block: &mut [F64], t: &[F64; 7], eighth: usize, num_ntts: usize) {
    fused_rows::<8>(block, eighth, num_ntts, |rows| {
        let [r0, r1, r2, r3, r4, r5, r6, r7] = rows;
        // Layer L, distance 4·eighth.
        butterfly_lanes(r0, r4, t[0]);
        butterfly_lanes(r1, r5, t[0]);
        butterfly_lanes(r2, r6, t[0]);
        butterfly_lanes(r3, r7, t[0]);
        // Layer L+1, distance 2·eighth: t[1] on the new top half, t[2] on the
        // new bottom half.
        butterfly_lanes(r0, r2, t[1]);
        butterfly_lanes(r1, r3, t[1]);
        butterfly_lanes(r4, r6, t[2]);
        butterfly_lanes(r5, r7, t[2]);
        // Layer L+2, distance eighth: one twiddle per quarter.
        butterfly_lanes(r0, r1, t[3]);
        butterfly_lanes(r2, r3, t[4]);
        butterfly_lanes(r4, r5, t[5]);
        butterfly_lanes(r6, r7, t[6]);
    });
}

/// Fused 2-layer butterfly, row-parallel; see the extension-field twin for the shape.
fn butterfly_interleaved_fused_2layer_par_rows(
    block: &mut [F64],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
    quarter: usize,
    num_ntts: usize,
) {
    fused_rows::<4>(block, quarter, num_ntts, |rows| {
        let [row_a, row_b, row_c, row_d] = rows;
        // Layer L butterflies (a,c) and (b,d), then layer L+1 (a,b) and
        // (c,d); each stage runs the NEON lane-pair kernel over the rows.
        butterfly_lanes(row_a, row_c, t_outer);
        butterfly_lanes(row_b, row_d, t_outer);
        butterfly_lanes(row_a, row_b, t_inner_a);
        butterfly_lanes(row_c, row_d, t_inner_b);
    });
}

#[inline]
fn butterfly_interleaved_block(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// Butterfly all `num_ntts` lanes of one (top row, bottom row) pair with a
/// shared twiddle: new_u = u + v*t; new_v = v + new_u.
///
/// On NEON this processes eight lanes per iteration. Four independent pair
/// reductions stay in the vector register file, exposing their PMULL chains
/// in parallel and amortizing the loop branch and constant setup. The pair
/// kernel handles a short even tail, and the scalar path handles an odd tail.
#[inline]
fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let vectors = top.len() / 8;
        // SAFETY: the target features are enabled at compile time and each
        // iteration reads and writes exactly eight elements from both rows.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_avx512(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
        }
        for lane in 8 * vectors..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v * twiddle;
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        let vectors = top.len() / 8;
        // SAFETY: aes target feature is enabled at compile time; the kernel
        // reads/writes exactly lanes [8i, 8i+8) of each row.
        unsafe {
            for i in 0..vectors {
                butterfly_lanes_neon_8(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
            let mut lane = 8 * vectors;
            while lane + 2 <= top.len() {
                butterfly_lane_pair_neon(top.as_mut_ptr().add(lane), bot.as_mut_ptr().add(lane), twiddle.0);
                lane += 2;
            }
        }
        if top.len() % 2 == 1 {
            let last = top.len() - 1;
            let v = bot[last];
            let new_u = top[last] + v * twiddle;
            top[last] = new_u;
            bot[last] = v + new_u;
        }
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")
    )))]
    {
        for lane in 0..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v * twiddle;
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
}

/// Eight F64 butterflies as four independent NEON lane-pair reductions.
/// Loading all four bottom vectors before reducing them gives the out-of-order
/// core four independent PMULL chains to schedule, while one call amortizes
/// loop control and the duplicated twiddle/reduction constants over 8 lanes.
///
/// # Safety
/// Requires the `aes` target feature; `top`/`bot` must each point at eight
/// readable+writable F64 values.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lanes_neon_8(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::reduce_pair_pmull4;

    // SAFETY: caller guarantees the two eight-element regions; F64 is
    // repr(transparent) over u64 and this function carries the aes feature.
    unsafe {
        let v0 = vld1q_u64(bot.cast());
        let v1 = vld1q_u64(bot.cast::<u64>().add(2));
        let v2 = vld1q_u64(bot.cast::<u64>().add(4));
        let v3 = vld1q_u64(bot.cast::<u64>().add(6));
        let tw = vdupq_n_u64(twiddle);

        let p00: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v0), twiddle));
        let p01: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v0),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p10: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v1), twiddle));
        let p11: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v1),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p20: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v2), twiddle));
        let p21: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v2),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let p30: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v3), twiddle));
        let p31: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v3),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));

        let prod0 = reduce_pair_pmull4(p00, p01);
        let prod1 = reduce_pair_pmull4(p10, p11);
        let prod2 = reduce_pair_pmull4(p20, p21);
        let prod3 = reduce_pair_pmull4(p30, p31);

        let u0 = vld1q_u64(top.cast());
        let u1 = vld1q_u64(top.cast::<u64>().add(2));
        let u2 = vld1q_u64(top.cast::<u64>().add(4));
        let u3 = vld1q_u64(top.cast::<u64>().add(6));
        let new_u0 = veorq_u64(u0, prod0);
        let new_u1 = veorq_u64(u1, prod1);
        let new_u2 = veorq_u64(u2, prod2);
        let new_u3 = veorq_u64(u3, prod3);
        let new_v0 = veorq_u64(v0, new_u0);
        let new_v1 = veorq_u64(v1, new_u1);
        let new_v2 = veorq_u64(v2, new_u2);
        let new_v3 = veorq_u64(v3, new_u3);

        vst1q_u64(top.cast(), new_u0);
        vst1q_u64(top.cast::<u64>().add(2), new_u1);
        vst1q_u64(top.cast::<u64>().add(4), new_u2);
        vst1q_u64(top.cast::<u64>().add(6), new_u3);
        vst1q_u64(bot.cast(), new_v0);
        vst1q_u64(bot.cast::<u64>().add(2), new_v1);
        vst1q_u64(bot.cast::<u64>().add(4), new_v2);
        vst1q_u64(bot.cast::<u64>().add(6), new_v3);
    }
}

/// Eight F64 butterflies using the four independent 128-bit lanes of
/// VPCLMULQDQ. Even and odd u64 lanes are multiplied separately, reduced in
/// parallel, then packed back into their original order.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX-512F; `top` and `bot` must each address eight
/// readable and writable F64 values.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2")]
unsafe fn butterfly_lanes_avx512(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn reduce(p: __m512i, r: __m512i) -> __m512i {
        let t = _mm512_clmulepi64_epi128::<0x01>(p, r);
        let u = _mm512_clmulepi64_epi128::<0x01>(t, r);
        _mm512_xor_si512(_mm512_xor_si512(p, t), u)
    }

    // SAFETY: the caller supplies valid eight-element rows and the function's
    // target features cover every intrinsic below.
    unsafe {
        let u = _mm512_loadu_si512(top.cast());
        let v = _mm512_loadu_si512(bot.cast());
        let tw = _mm512_set1_epi64(twiddle as i64);
        let r = _mm512_set1_epi64(0x1b);

        let even = reduce(_mm512_clmulepi64_epi128::<0x00>(v, tw), r);
        let odd = reduce(_mm512_clmulepi64_epi128::<0x11>(v, tw), r);
        let odd = _mm512_shuffle_epi32::<0x4e>(odd);
        let product = _mm512_mask_blend_epi64(0xaa, even, odd);

        let new_u = _mm512_xor_si512(u, product);
        let new_v = _mm512_xor_si512(v, new_u);
        _mm512_storeu_si512(top.cast(), new_u);
        _mm512_storeu_si512(bot.cast(), new_v);
    }
}

/// Two F64 butterflies with a shared twiddle, NEON-resident end to end.
/// The two products issue as PMULL/PMULL2 on the loaded row (no lane
/// extraction) and reduce through the all-PMULL lane-pair fold
/// ([`primitives::field::gf2_64::aarch64::reduce_pair_pmull4`]), replacing the
/// old 10-op shift-XOR fold chain.
///
/// # Safety
/// Requires the `aes` target feature; `top`/`bot` must each point at two
/// readable+writable F64 values.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lane_pair_neon(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::reduce_pair_pmull4;
    // SAFETY: caller guarantees the pointees; F64 is repr(transparent) u64.
    unsafe {
        let u = vld1q_u64(top as *const u64);
        let v = vld1q_u64(bot as *const u64);
        // Products v_lane * twiddle: PMULL on the low lanes, PMULL2 on the
        // highs (the dup is loop-invariant and hoisted after inlining).
        let tw = vdupq_n_u64(twiddle);
        let p0: uint64x2_t = core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v), twiddle));
        let p1: uint64x2_t = core::mem::transmute(vmull_high_p64(
            core::mem::transmute::<uint64x2_t, poly64x2_t>(v),
            core::mem::transmute::<uint64x2_t, poly64x2_t>(tw),
        ));
        let prod = reduce_pair_pmull4(p0, p1);
        let new_u = veorq_u64(u, prod);
        let new_v = veorq_u64(v, new_u);
        vst1q_u64(top as *mut u64, new_u);
        vst1q_u64(bot as *mut u64, new_v);
    }
}

#[inline]
fn log2_pow2(n: usize) -> usize {
    assert!(n.is_power_of_two() && n > 0, "length must be a positive power of 2");
    n.trailing_zeros() as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    /// Check forward∘inverse = id and scalar == interleaved == parallel, plus
    /// linearity.
    #[test]
    fn inverse_roundtrip_and_variants_agree() {
        let ntt = AdditiveNttF64::standard(12);
        let mut rng = Rng::new(1);
        for log_d in [1usize, 3, 6, 10] {
            let n = 1usize << log_d;
            let orig: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();

            let mut a = orig.clone();
            ntt.forward_transform_scalar(&mut a);
            let mut b = orig.clone();
            ntt.forward_transform_interleaved_scalar_from_layer(&mut b, 1, 0);
            assert_eq!(a, b, "interleaved(1 lane) == scalar at log_d={log_d}");
            let mut c = orig.clone();
            ntt.forward_transform_interleaved_parallel_from_layer(&mut c, 1, 0);
            assert_eq!(a, c, "parallel == scalar at log_d={log_d}");

            ntt.inverse_transform(&mut a);
            assert_eq!(a, orig, "inverse roundtrip at log_d={log_d}");
        }
    }

    /// The parallel interleaved path must match the scalar reference at sizes
    /// that actually reach the fused multi-layer passes.
    ///
    /// `interleaved_lanes_are_independent_ntts` runs at `log_d = 7`, below the
    /// driver's `log_d < 8` bail-out, so it only ever exercises the scalar
    /// path. These shapes give `n_top >= 3`, which is what selects the
    /// radix-8 fused pass, and cover a non-zero `start_layer` because the
    /// commit path enters at `log_inv_rate`.
    #[test]
    fn interleaved_parallel_matches_scalar_at_fused_sizes() {
        let mut rng = Rng::new(0xC0FFEE);
        for log_d in [12usize, 14] {
            for lanes in [8usize, 64] {
                for start_layer in [0usize, 1] {
                    let ntt = AdditiveNttF64::standard(log_d);
                    let n = (1usize << log_d) * lanes;
                    let original: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();

                    let mut want = original.clone();
                    ntt.forward_transform_interleaved_scalar_from_layer(&mut want, lanes, start_layer);
                    let mut got = original.clone();
                    ntt.forward_transform_interleaved_from_layer(&mut got, lanes, start_layer);

                    assert_eq!(
                        got, want,
                        "parallel != scalar at log_d={log_d}, lanes={lanes}, start_layer={start_layer}"
                    );
                }
            }
        }
    }

    #[test]
    fn interleaved_lanes_are_independent_ntts() {
        let ntt = AdditiveNttF64::standard(10);
        let mut rng = Rng::new(2);
        let log_d = 7;
        let n = 1usize << log_d;
        for lanes in [1usize, 2, 4, 8, 64] {
            // SoA buffer + per-lane copies.
            let mut soa = vec![F64::ZERO; n * lanes];
            let mut per_lane: Vec<Vec<F64>> = vec![vec![F64::ZERO; n]; lanes];
            for pos in 0..n {
                for lane in 0..lanes {
                    let v = F64(rng.next_u64());
                    soa[pos * lanes + lane] = v;
                    per_lane[lane][pos] = v;
                }
            }
            ntt.forward_transform_interleaved_from_layer(&mut soa, lanes, 0);
            for (lane, lane_data) in per_lane.iter_mut().enumerate() {
                ntt.forward_transform_scalar(lane_data);
                for pos in 0..n {
                    assert_eq!(soa[pos * lanes + lane], lane_data[pos]);
                }
            }
        }
    }

    #[test]
    fn linearity() {
        let ntt = AdditiveNttF64::standard(8);
        let mut rng = Rng::new(3);
        let n = 256;
        let a: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();
        let b: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();
        let sum: Vec<F64> = a.iter().zip(&b).map(|(x, y)| *x + *y).collect();
        let mut ta = a.clone();
        let mut tb = b.clone();
        let mut tsum = sum.clone();
        ntt.forward_transform_scalar(&mut ta);
        ntt.forward_transform_scalar(&mut tb);
        ntt.forward_transform_scalar(&mut tsum);
        for i in 0..n {
            assert_eq!(tsum[i], ta[i] + tb[i]);
        }
    }
}
