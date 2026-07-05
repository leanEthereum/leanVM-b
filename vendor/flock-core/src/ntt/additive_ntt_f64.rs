//! Additive NTT over GF(2^64) using the LCH novel polynomial basis: the
//! encoding layer of the 64-bit transition (commitments over K = F_{2^64}).
//!
//! Structure and conventions mirror [`super::additive_ntt_f128`] exactly (see
//! its module docs for the subspace-polynomial construction, the
//! neighbors-last layer ordering, and the SoA interleaved layout). The inner
//! butterfly loops route through a NEON lane-pair kernel (two 1-PMULL
//! products per iteration with a vectorized 0x1B fold, no GPR round-trips);
//! at large sizes the transform is memory-bandwidth bound either way, like
//! its F128 twin.

use crate::field::F64;

/// Normalized subspace-polynomial evaluation table (see the F128 twin).
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
/// integer encoding, exactly as in the F128 version (whose domain already
/// lived inside this very subfield).
#[derive(Clone, Debug)]
pub struct AdditiveNttF64 {
    evals: Vec<Vec<F64>>,
}

impl AdditiveNttF64 {
    pub fn new(basis: &[F64]) -> Self {
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

    /// Twiddle at `(layer, block)`; see the F128 twin for the convention.
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

    /// Forward NTT in place, dispatching to the parallel path for large
    /// inputs (single-lane case of the interleaved transform).
    pub fn forward_transform(&self, data: &mut [F64]) {
        self.forward_transform_interleaved_from_layer(data, 1, 0);
    }

    /// Interleaved (SoA) forward NTT: `num_ntts` independent lanes sharing
    /// the twiddle structure; `data[pos * num_ntts + lane]`. Same layout
    /// contract as the F128 twin (one Merkle leaf = one position = a
    /// contiguous slice of `num_ntts` F_{2^64} elements).
    pub fn forward_transform_interleaved(&self, data: &mut [F64], num_ntts: usize) {
        self.forward_transform_interleaved_from_layer(data, num_ntts, 0);
    }

    /// Interleaved forward NTT starting at `start_layer` (the RS-encoding
    /// caller replicates the message into all `2^rate` sub-blocks, which IS
    /// the exact post-layer-`rate` state, and skips those layers here).
    pub fn forward_transform_interleaved_from_layer(
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

    /// Parallel interleaved forward NTT, cache-blocked like the F128 twin:
    /// top layers sweep the full buffer (fused two-layer passes, row-parallel),
    /// deep layers run as cache-resident sub-NTTs in parallel. Constants are
    /// re-derived for 8-byte elements.
    pub fn forward_transform_interleaved_parallel_from_layer(
        &self,
        data: &mut [F64],
        num_ntts: usize,
        start_layer: usize,
    ) {
        use rayon::prelude::*;
        let n_total = data.len();
        let log_d = log2_pow2(n_total / num_ntts);

        // Target sub-group ≈ 2 MB; each position is num_ntts × 8 bytes.
        const TARGET_SUBGROUP_LOG_BYTES: usize = 21;
        let log_bytes_per_position = 3 + log2_pow2(num_ntts);
        let target_log_positions = TARGET_SUBGROUP_LOG_BYTES.saturating_sub(log_bytes_per_position);
        let cache_n_top = log_d.saturating_sub(target_log_positions);

        const PARALLEL_FLOOR_LOG_D: usize = 12;
        const MIN_SUB_LOG: usize = 8;
        let n_top = if log_d >= PARALLEL_FLOOR_LOG_D {
            let want_subs_log = log2_pow2(rayon::current_num_threads().next_power_of_two());
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

            if layer + 1 < n_top && block_size >= 4 {
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
        data.par_chunks_mut(sub_elems)
            .enumerate()
            .for_each(|(sub_idx, sub_data)| {
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

fn butterfly_interleaved_block_par_rows(
    block: &mut [F64],
    twiddle: F64,
    block_size_half: usize,
    num_ntts: usize,
) {
    use rayon::prelude::*;
    const PARALLEL_ROW_THRESHOLD: usize = 1024;
    if block_size_half < PARALLEL_ROW_THRESHOLD {
        butterfly_interleaved_block(block, twiddle, block_size_half, num_ntts);
        return;
    }
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    top.par_chunks_mut(num_ntts)
        .zip(bot.par_chunks_mut(num_ntts))
        .for_each(|(top_row, bot_row)| {
            butterfly_lanes(top_row, bot_row, twiddle);
        });
}

/// Fused 2-layer butterfly, row-parallel; see the F128 twin for the shape.
fn butterfly_interleaved_fused_2layer_par_rows(
    block: &mut [F64],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
    quarter: usize,
    num_ntts: usize,
) {
    use rayon::prelude::*;
    const PARALLEL_ROW_THRESHOLD: usize = 512;
    let stride = quarter * num_ntts;
    debug_assert_eq!(block.len(), 4 * stride);

    let do_one =
        |row_a: &mut [F64], row_b: &mut [F64], row_c: &mut [F64], row_d: &mut [F64]| {
            // Layer L butterflies (a,c) and (b,d), then layer L+1 (a,b) and
            // (c,d); each stage runs the NEON lane-pair kernel over the rows.
            butterfly_lanes(row_a, row_c, t_outer);
            butterfly_lanes(row_b, row_d, t_outer);
            butterfly_lanes(row_a, row_b, t_inner_a);
            butterfly_lanes(row_c, row_d, t_inner_b);
        };

    let (top_half, bot_half) = block.split_at_mut(2 * stride);
    let (q1, q2) = top_half.split_at_mut(stride);
    let (q3, q4) = bot_half.split_at_mut(stride);

    if quarter < PARALLEL_ROW_THRESHOLD {
        for r in 0..quarter {
            let off = r * num_ntts;
            let (q1r, _) = q1[off..].split_at_mut(num_ntts);
            let (q2r, _) = q2[off..].split_at_mut(num_ntts);
            let (q3r, _) = q3[off..].split_at_mut(num_ntts);
            let (q4r, _) = q4[off..].split_at_mut(num_ntts);
            do_one(q1r, q2r, q3r, q4r);
        }
    } else {
        q1.par_chunks_mut(num_ntts)
            .zip(q2.par_chunks_mut(num_ntts))
            .zip(q3.par_chunks_mut(num_ntts))
            .zip(q4.par_chunks_mut(num_ntts))
            .for_each(|(((row_a, row_b), row_c), row_d)| {
                do_one(row_a, row_b, row_c, row_d);
            });
    }
}

#[inline]
fn butterfly_interleaved_block(
    block: &mut [F64],
    twiddle: F64,
    block_size_half: usize,
    num_ntts: usize,
) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_lanes(
            &mut top[off..off + num_ntts],
            &mut bot[off..off + num_ntts],
            twiddle,
        );
    }
}


/// Butterfly all `num_ntts` lanes of one (top row, bottom row) pair with a
/// shared twiddle: new_u = u + v*t; new_v = v + new_u.
///
/// On NEON this processes two lanes per iteration entirely inside the vector
/// register file (2 PMULL for the products, one vectorized 0x1B fold for the
/// pair, no GPR round-trips), which is what makes the F64 NTT beat the F128
/// one on equal bytes; the scalar path is the portable fallback and the odd
/// tail.
#[inline]
fn butterfly_lanes(top: &mut [F64], bot: &mut [F64], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        let pairs = top.len() / 2;
        // SAFETY: aes target feature is enabled at compile time; the kernel
        // reads/writes exactly lanes [2i, 2i+1] of each row.
        unsafe {
            for i in 0..pairs {
                butterfly_lane_pair_neon(
                    top.as_mut_ptr().add(2 * i),
                    bot.as_mut_ptr().add(2 * i),
                    twiddle.0,
                );
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
    #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
    {
        for lane in 0..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v * twiddle;
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
}

/// Two F64 butterflies with a shared twiddle, NEON-resident end to end.
///
/// # Safety
/// Requires the `aes` target feature; `top`/`bot` must each point at two
/// readable+writable F64 values.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn butterfly_lane_pair_neon(top: *mut F64, bot: *mut F64, twiddle: u64) {
    use core::arch::aarch64::*;
    // SAFETY: caller guarantees the pointees; F64 is repr(transparent) u64.
    unsafe {
        let u = vld1q_u64(top as *const u64);
        let v = vld1q_u64(bot as *const u64);
        // Products v_lane * twiddle (2 PMULL), then repack (lo0,lo1)/(hi0,hi1).
        let p0: uint64x2_t =
            core::mem::transmute(vmull_p64(vgetq_lane_u64::<0>(v), twiddle));
        let p1: uint64x2_t =
            core::mem::transmute(vmull_p64(vgetq_lane_u64::<1>(v), twiddle));
        let lo = vtrn1q_u64(p0, p1);
        let hi = vtrn2q_u64(p0, p1);
        // Fold both highs by 0x1B: x^64 = x^4 + x^3 + x + 1.
        let f = veorq_u64(
            veorq_u64(hi, vshlq_n_u64::<1>(hi)),
            veorq_u64(vshlq_n_u64::<3>(hi), vshlq_n_u64::<4>(hi)),
        );
        let ov = veorq_u64(
            veorq_u64(vshrq_n_u64::<63>(hi), vshrq_n_u64::<61>(hi)),
            vshrq_n_u64::<60>(hi),
        );
        let f2 = veorq_u64(
            veorq_u64(ov, vshlq_n_u64::<1>(ov)),
            veorq_u64(vshlq_n_u64::<3>(ov), vshlq_n_u64::<4>(ov)),
        );
        let prod = veorq_u64(veorq_u64(lo, f), f2);
        let new_u = veorq_u64(u, prod);
        let new_v = veorq_u64(v, new_u);
        vst1q_u64(top as *mut u64, new_u);
        vst1q_u64(bot as *mut u64, new_v);
    }
}

#[inline]
fn log2_pow2(n: usize) -> usize {
    assert!(
        n.is_power_of_two() && n > 0,
        "length must be a positive power of 2"
    );
    n.trailing_zeros() as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// The NTT of the coefficient vector of the constant-1 polynomial in the
    /// novel basis must be all-ones (Ŵ_0 normalization); more usefully, the
    /// forward transform must equal naive per-point evaluation of the novel
    /// basis expansion. We check forward∘inverse = id and scalar==interleaved
    /// ==parallel instead, plus linearity.
    #[test]
    fn inverse_roundtrip_and_variants_agree() {
        let ntt = AdditiveNttF64::standard(12);
        let mut s = 1u64;
        for log_d in [1usize, 3, 6, 10] {
            let n = 1usize << log_d;
            let orig: Vec<F64> = (0..n).map(|_| F64(splitmix64(&mut s))).collect();

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

    #[test]
    fn interleaved_lanes_are_independent_ntts() {
        let ntt = AdditiveNttF64::standard(10);
        let mut s = 2u64;
        let log_d = 7;
        let n = 1usize << log_d;
        let lanes = 4usize;
        // SoA buffer + per-lane copies.
        let mut soa = vec![F64::ZERO; n * lanes];
        let mut per_lane: Vec<Vec<F64>> = vec![vec![F64::ZERO; n]; lanes];
        for pos in 0..n {
            for lane in 0..lanes {
                let v = F64(splitmix64(&mut s));
                soa[pos * lanes + lane] = v;
                per_lane[lane][pos] = v;
            }
        }
        ntt.forward_transform_interleaved(&mut soa, lanes);
        for (lane, lane_data) in per_lane.iter_mut().enumerate() {
            ntt.forward_transform_scalar(lane_data);
            for pos in 0..n {
                assert_eq!(soa[pos * lanes + lane], lane_data[pos]);
            }
        }
    }

    #[test]
    fn linearity() {
        let ntt = AdditiveNttF64::standard(8);
        let mut s = 3u64;
        let n = 256;
        let a: Vec<F64> = (0..n).map(|_| F64(splitmix64(&mut s))).collect();
        let b: Vec<F64> = (0..n).map(|_| F64(splitmix64(&mut s))).collect();
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
