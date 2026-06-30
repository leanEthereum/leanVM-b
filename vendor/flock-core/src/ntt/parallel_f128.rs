// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Parallel additive NTT over F_{2^128} (GHASH form).
//!
//! Mirrors [`super::parallel_f32`] / [`super::parallel_f64`]: position-major
//! SoA layout, SIMD across NTT instances via [`ghash_mul_vec2_neon`], shared
//! twiddle table for all parallel NTTs. SIMD width is 2 (one F128 pair per
//! `ghash_mul_vec2_neon`), so `num_ntts` must be a multiple of 2.

use crate::field::F128;

#[inline]
fn next_s(s: F128, s_at_root: F128) -> F128 {
    s * s + s_at_root * s
}

pub fn compute_twiddles(k: usize, beta: F128) -> Vec<F128> {
    if k == 0 {
        return Vec::new();
    }
    let n = 1usize << k;
    let mut twiddles = vec![F128::ZERO; n - 1];

    let mut len = 1usize << (k - 1);
    let mut layer: Vec<F128> = (0..len)
        .map(|i| beta + F128::new((2 * i) as u64, 0))
        .collect();
    let mut s_at_root = F128::ONE;

    let mut write_at = len;
    for i in 0..len {
        twiddles[write_at - 1 + i] = layer[i];
    }

    for _ in 1..k {
        write_at >>= 1;
        let next_s_root = next_s(layer[1] + layer[0], s_at_root);
        let new_len = write_at;
        for i in 0..new_len {
            layer[i] = next_s(layer[2 * i], s_at_root);
        }
        len = new_len;
        s_at_root = next_s_root;

        let s_inv = s_at_root.inv();
        for j in 0..len {
            twiddles[write_at - 1 + j] = s_inv * layer[j];
        }
    }

    twiddles
}

#[inline]
#[allow(dead_code)] // active in tests and non-aarch64 builds
fn butterfly_scalar(data: &mut [F128], lambda: F128, num_ntts: usize) {
    let rows = data.len() / num_ntts;
    let half = rows >> 1;
    let half_offset = half * num_ntts;
    let (top, bot) = data.split_at_mut(half_offset);
    for row in 0..half {
        let off = row * num_ntts;
        for lane in 0..num_ntts {
            let w = bot[off + lane];
            top[off + lane] += lambda * w;
            bot[off + lane] = w + top[off + lane];
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
fn butterfly_row_pair_neon(top_row: &mut [F128], bot_row: &mut [F128], lambda: F128) {
    use crate::field::gf2_128::aarch64::ghash_mul_vec2_neon;

    debug_assert_eq!(top_row.len(), bot_row.len());
    let num_ntts = top_row.len();
    // SAFETY: aes/neon are statically enabled at compile time.
    unsafe {
        let mut lane = 0usize;
        while lane < num_ntts {
            let t0 = top_row[lane];
            let t1 = top_row[lane + 1];
            let b0 = bot_row[lane];
            let b1 = bot_row[lane + 1];

            let prod = ghash_mul_vec2_neon([lambda, lambda], [b0, b1]);

            let new_t0 = F128 {
                lo: t0.lo ^ prod[0].lo,
                hi: t0.hi ^ prod[0].hi,
            };
            let new_t1 = F128 {
                lo: t1.lo ^ prod[1].lo,
                hi: t1.hi ^ prod[1].hi,
            };
            let new_b0 = F128 {
                lo: b0.lo ^ new_t0.lo,
                hi: b0.hi ^ new_t0.hi,
            };
            let new_b1 = F128 {
                lo: b1.lo ^ new_t1.lo,
                hi: b1.hi ^ new_t1.hi,
            };

            top_row[lane] = new_t0;
            top_row[lane + 1] = new_t1;
            bot_row[lane] = new_b0;
            bot_row[lane + 1] = new_b1;

            lane += 2;
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline]
fn butterfly_neon(data: &mut [F128], lambda: F128, num_ntts: usize) {
    let rows = data.len() / num_ntts;
    let half = rows >> 1;
    let half_offset = half * num_ntts;
    let (top, bot) = data.split_at_mut(half_offset);
    for row in 0..half {
        let off = row * num_ntts;
        let top_row = &mut top[off..off + num_ntts];
        let bot_row = &mut bot[off..off + num_ntts];
        butterfly_row_pair_neon(top_row, bot_row, lambda);
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn butterfly_par(data: &mut [F128], lambda: F128, num_ntts: usize) {
    use rayon::prelude::*;
    let half_offset = ((data.len() / num_ntts) >> 1) * num_ntts;
    let (top, bot) = data.split_at_mut(half_offset);
    top.par_chunks_mut(num_ntts)
        .zip(bot.par_chunks_mut(num_ntts))
        .for_each(|(t, b)| butterfly_row_pair_neon(t, b, lambda));
}

#[inline]
fn butterfly(data: &mut [F128], lambda: F128, num_ntts: usize) {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        butterfly_neon(data, lambda, num_ntts);
    }
    #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
    {
        butterfly_scalar(data, lambda, num_ntts);
    }
}

fn fft_rec(data: &mut [F128], tw: &[F128], idx: usize, num_ntts: usize) {
    let rows = data.len() / num_ntts;
    if rows == 1 {
        return;
    }
    butterfly(data, tw[idx - 1], num_ntts);
    let half_size = (rows >> 1) * num_ntts;
    let (lo, hi) = data.split_at_mut(half_size);
    fft_rec(lo, tw, 2 * idx, num_ntts);
    fft_rec(hi, tw, 2 * idx + 1, num_ntts);
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
const PARALLEL_ROW_THRESHOLD: usize = 1024;

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn fft_rec_par(data: &mut [F128], tw: &[F128], idx: usize, num_ntts: usize) {
    let rows = data.len() / num_ntts;
    if rows == 1 {
        return;
    }
    let lambda = tw[idx - 1];
    if rows >= PARALLEL_ROW_THRESHOLD {
        butterfly_par(data, lambda, num_ntts);
        let half_size = (rows >> 1) * num_ntts;
        let (lo, hi) = data.split_at_mut(half_size);
        rayon::join(
            || fft_rec_par(lo, tw, 2 * idx, num_ntts),
            || fft_rec_par(hi, tw, 2 * idx + 1, num_ntts),
        );
    } else {
        butterfly(data, lambda, num_ntts);
        let half_size = (rows >> 1) * num_ntts;
        let (lo, hi) = data.split_at_mut(half_size);
        fft_rec_par(lo, tw, 2 * idx, num_ntts);
        fft_rec_par(hi, tw, 2 * idx + 1, num_ntts);
    }
}

#[derive(Clone, Debug)]
pub struct ParallelNttF128 {
    k: usize,
    num_ntts: usize,
    twiddles: Vec<F128>,
}

impl ParallelNttF128 {
    pub fn new(k: usize, beta: F128, num_ntts: usize) -> Self {
        assert!(
            num_ntts.is_multiple_of(2) && num_ntts > 0,
            "num_ntts must be a positive multiple of 2 for SIMD lanes",
        );
        assert!(k <= 128, "F_{{2^128}} supports at most k = 128");
        Self {
            k,
            num_ntts,
            twiddles: compute_twiddles(k, beta),
        }
    }

    pub fn k(&self) -> usize {
        self.k
    }
    pub fn num_ntts(&self) -> usize {
        self.num_ntts
    }
    pub fn domain_size(&self) -> usize {
        1usize << self.k
    }
    pub fn twiddles(&self) -> &[F128] {
        &self.twiddles
    }

    pub fn forward(&self, data: &mut [F128]) {
        assert_eq!(
            data.len(),
            self.domain_size() * self.num_ntts,
            "data length must be 2^k × num_ntts",
        );
        if self.k == 0 {
            return;
        }
        fft_rec(data, &self.twiddles, 1, self.num_ntts);
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    pub fn forward_parallel(&self, data: &mut [F128]) {
        assert_eq!(
            data.len(),
            self.domain_size() * self.num_ntts,
            "data length must be 2^k × num_ntts",
        );
        if self.k == 0 {
            return;
        }
        fft_rec_par(data, &self.twiddles, 1, self.num_ntts);
    }
}
