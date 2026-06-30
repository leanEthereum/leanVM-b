// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Additive NTT over GF(2^8) (Lin–Chung–Han basis).
//!
//! Evaluation domain `W = β + span{1, 2, …, 2^{k-1}}` (additive coset of an
//! F_2 subspace of F_{2^8}). Maximum useful `k` is 7 (|W| = 128); going to k=8
//! exhausts all 256 elements of F_{2^8}.
//!
//! Scalar/portable implementation — correctness first. NEON "triple" variants
//! that batch a/b/c with shared twiddles can be added later if the round-1 URM
//! hot path needs them.

use crate::field::F8;

pub mod additive_ntt_f128;
pub mod inv_table;
pub mod inv_table_deg4;
pub mod parallel_f128;
pub use additive_ntt_f128::AdditiveNttF128;
pub use inv_table::InvNttTableByteSingleGf8;
pub use inv_table_deg4::InvNttTableSToV8Gf8;
pub use parallel_f128::ParallelNttF128;

/// Twiddle recurrence used to build the next subspace layer's evaluation points:
/// `next_s(s, root) = s² + root · s = s · (s + root)`.
#[inline]
fn next_s(s: F8, s_at_root: F8) -> F8 {
    s * s + s_at_root * s
}

/// Build the size-(2^k − 1) twiddle table for the additive NTT.
///
/// Layout: level-L twiddles live at offset (2^L − 1).
/// Level 0 has 2^{k-1} twiddles, level 1 has 2^{k-2}, …, level k−1 has 1.
pub fn compute_twiddles(k: usize, beta: F8) -> Vec<F8> {
    if k == 0 {
        return Vec::new();
    }
    let n = 1usize << k;
    let mut twiddles = vec![F8::ZERO; n - 1];

    // Layer 0: 2^{k-1} points beta + {0, 2, 4, ..., 2(len-1)}.
    let mut len = 1usize << (k - 1);
    let mut layer: Vec<F8> = (0..len).map(|i| beta + F8((2 * i) as u8)).collect();
    let mut s_at_root = F8::ONE;

    // Write layer 0 directly (s_at_root = 1 ⇒ no scaling needed).
    let mut write_at = len;
    for i in 0..len {
        twiddles[write_at - 1 + i] = layer[i];
    }

    // Subsequent layers: halve the size, advance the recurrence, scale by s⁻¹.
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
fn fft_butterfly(v: &mut [F8], lambda: F8) {
    let n = v.len();
    let half = n >> 1;
    for i in 0..half {
        let w = v[half + i];
        v[i] += lambda * w;
        v[half + i] = w + v[i];
    }
}

fn fft_rec(v: &mut [F8], tw: &[F8], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    fft_butterfly(v, tw[idx - 1]);
    let half = n >> 1;
    let (lo, hi) = v.split_at_mut(half);
    fft_rec(lo, tw, 2 * idx);
    fft_rec(hi, tw, 2 * idx + 1);
}

#[inline]
fn ifft_butterfly(v: &mut [F8], lambda: F8) {
    let n = v.len();
    let half = n >> 1;
    for i in 0..half {
        v[half + i] += v[i];
        v[i] += lambda * v[half + i];
    }
}

fn ifft_rec(v: &mut [F8], tw: &[F8], idx: usize) {
    let n = v.len();
    if n == 1 {
        return;
    }
    let half = n >> 1;
    let (lo, hi) = v.split_at_mut(half);
    ifft_rec(lo, tw, 2 * idx);
    ifft_rec(hi, tw, 2 * idx + 1);
    ifft_butterfly(v, tw[idx - 1]);
}

/// Additive NTT over GF(2^8) with domain of size 2^k.
///
/// Internal LCH basis: the forward transform maps coefficients in the
/// Lin–Chung–Han basis to evaluations at the 2^k points of the domain.
/// `inverse` is the exact reverse.
#[derive(Clone, Debug)]
pub struct AdditiveNttGf8 {
    k: usize,
    twiddles: Vec<F8>,
}

impl AdditiveNttGf8 {
    /// Build an NTT for a 2^k-point domain with offset β.
    pub fn new(k: usize, beta: F8) -> Self {
        Self {
            k,
            twiddles: compute_twiddles(k, beta),
        }
    }

    pub fn k(&self) -> usize {
        self.k
    }
    pub fn domain_size(&self) -> usize {
        1usize << self.k
    }
    pub fn twiddles(&self) -> &[F8] {
        &self.twiddles
    }

    pub fn forward(&self, v: &mut [F8]) {
        assert_eq!(
            v.len(),
            self.domain_size(),
            "forward: input length must be 2^k"
        );
        if v.len() <= 1 {
            return;
        }
        fft_rec(v, &self.twiddles, 1);
    }

    pub fn inverse(&self, v: &mut [F8]) {
        assert_eq!(
            v.len(),
            self.domain_size(),
            "inverse: input length must be 2^k"
        );
        if v.len() <= 1 {
            return;
        }
        ifft_rec(v, &self.twiddles, 1);
    }
}