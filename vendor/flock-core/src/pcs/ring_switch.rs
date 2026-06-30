// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The verifier's polylog `eval_rs_eq` helper is ported from binius64's
// `crates/verifier/src/ring_switch.rs`
// (https://github.com/binius-zk/binius64). The rest of this module (the
// prover-side reduction adapted for the φ_8 LCH basis) is original to Flock.

//! Ring-switching reduction (DP24-style, adapted for the φ_8 LCH basis).
//!
//! Converts the zerocheck's claim `ẑ_skip(z_skip, x_outer) = v` into a BaseFold
//! sumcheck claim over the packed multilinear `f_packed` with a transparent
//! multilinear `rs_eq_ind`.
//!
//! ## Non-novelty basis: only affects the claim-check step
//!
//! Binius's DP24 ring-switching uses tensor-product (`eq_ind`) weights for the
//! verifier's claim check. That requires the prefix's LCH-Lagrange to factor
//! as `eq(x_skip, i_skip)`, which holds only for the *novelty basis* of the
//! subspace.
//!
//! Our zerocheck uses the φ_8 image of {1,2,4,…,32} as the 6-dim LCH basis.
//! That basis is **not** a novelty basis (verified at k=2: the ratio of
//! Lagrange values doesn't satisfy the tensor identity), so the 64 weights
//! `ν_φ8(i_skip)(z_skip)` are not tensor-factorizable.
//!
//! Resolution: replace the verifier's claim check with **direct** Lagrange
//! weights (computed via [`lagrange_weights_naive`]); every other component of
//! the reduction (`s_hat_v`, `s_hat_u`, BaseFold target `T`, `rs_eq_ind`) is
//! independent of the prefix and stays identical to Binius.
//!
//! ## Prover vs. verifier paths for `rs_eq_ind`
//!
//! - **Prover side** (used by [`prove`], [`prove_batched`]): materializes
//!   `rs_eq_ind` densely (or sparsely) via [`fold_b128_elems`] / [`RsEqInd`].
//!   The dense vector becomes the BaseFold target witness, so the prover does
//!   need the full `2^(m-7)` entries.
//! - **Verifier side** (used by [`verify_succinct`] + [`eval_rs_eq`]): never
//!   materializes `rs_eq_ind`. Instead, evaluates `MLE(rs_eq_ind)(c)` at the
//!   BaseFold final challenge point in `O((m-7) · 128²)` field ops via the
//!   DP24 tensor-algebra iterative algorithm ([DP24] §1.3, Figure 3). This is
//!   polylog in the witness size.
//!
//! [DP24]: <https://eprint.iacr.org/2024/504>
//!
//! ## Layout (for m-bit witness, F_{2^128} packing with LOG_PACKING = 7)
//!
//! Zerocheck output: `(z_skip ∈ F, x_outer ∈ F^{m−6})` with claim `v`.
//!
//! After translation:
//! - **prefix bits 0..6**: weighted by `ν_φ8(·)(z_skip)` (the 64 Lagrange weights).
//! - **prefix bit 6**: weighted by `eq(x_outer[0], ·)`.
//! - **suffix coords**: `x_outer[1..]`, length `m − 7`.
//!
//! The packed witness has `2^(m−7)` F_{2^128} elements indexed by the suffix.
//! `s_hat_v` has 128 entries indexed by the 7-bit prefix.

use crate::bits::transpose_8x8_bits;
use crate::challenger::Challenger;
use crate::field::F128;
use crate::zerocheck::PaddingSpec;
use crate::zerocheck::multilinear::lagrange_weights_naive;
use crate::zerocheck::univariate_skip::build_eq;
use serde::{Deserialize, Serialize};

use super::pack::LOG_PACKING;

/// Per-block padding descriptor in F_{2^128} units. Computed once from a bit-
/// level [`PaddingSpec`] and reused across the fold kernels: any chunk whose
/// index modulo `chunks_per_block` is ≥ `useful_chunks_per_block` is fully
/// inside the zero-padded suffix of every block and can be skipped.
#[derive(Clone, Copy, Debug)]
struct ChunkPadding {
    /// `chunks_per_block - 1` for fast `idx % chunks_per_block` via AND;
    /// `usize::MAX` (= "no skip") when there is only one block (e.g. dense
    /// paddings).
    chunk_in_block_mask: usize,
    /// Index of the first fully-padding chunk within each block.
    useful_chunks_per_block: usize,
}

impl ChunkPadding {
    /// Build the per-chunk skip table for a given F128-chunk width
    /// (e.g. `chunk_width = 8` for the 8-wide MFR path). Returns a "no skip"
    /// descriptor if either (a) the spec covers the entire packed witness as
    /// one block, or (b) every chunk in a block is at least partially useful.
    fn new(padding: &PaddingSpec, chunk_width: usize) -> Self {
        // Block size in F128 elements = 2^(k_log - LOG_PACKING).
        if padding.k_log <= LOG_PACKING {
            // Block smaller than one F128 — no per-block structure to exploit.
            return Self::no_skip();
        }
        let block_size_f128 = 1usize << (padding.k_log - LOG_PACKING);
        if block_size_f128 < chunk_width {
            return Self::no_skip();
        }
        let chunks_per_block = block_size_f128 / chunk_width;
        let useful_f128 = padding.useful_bits_per_block.div_ceil(1 << LOG_PACKING);
        let useful_chunks_per_block = useful_f128.div_ceil(chunk_width).min(chunks_per_block);
        if useful_chunks_per_block == chunks_per_block {
            return Self::no_skip();
        }
        debug_assert!(chunks_per_block.is_power_of_two());
        Self {
            chunk_in_block_mask: chunks_per_block - 1,
            useful_chunks_per_block,
        }
    }

    fn no_skip() -> Self {
        Self {
            chunk_in_block_mask: usize::MAX,
            useful_chunks_per_block: usize::MAX,
        }
    }

    /// True iff the chunk at this global index is fully inside padding.
    #[inline(always)]
    fn skip(&self, chunk_idx: usize) -> bool {
        (chunk_idx & self.chunk_in_block_mask) >= self.useful_chunks_per_block
    }
}

/// Build the 128-entry weights vector for the verifier's ring-switching claim
/// check, given the zerocheck's `z_skip` (univariate-skip coord, absorbs 6
/// boolean coords via the φ_8 basis) and `x_outer_0` (the 7th prefix bit, a
/// fresh F_{2^128} multilinear coord).
///
/// ```text
/// weights[i] = ν_φ8(i & 63)(z_skip) · eq(x_outer_0, (i >> 6) & 1)
///            for i ∈ {0..128}
/// ```
///
/// `i & 63` selects the low 6 bits (LCH dimensions); `(i >> 6) & 1` is the 7th
/// bit (a standard multilinear coord).
pub fn build_claim_weights(z_skip: F128, x_outer_0: F128) -> Vec<F128> {
    const K_SKIP: usize = 6;
    let lambda = lagrange_weights_naive(K_SKIP, z_skip); // length 64
    debug_assert_eq!(lambda.len(), 1 << K_SKIP);

    let eq_lo = F128::ONE + x_outer_0; // eq(x_outer_0, 0)
    let eq_hi = x_outer_0; // eq(x_outer_0, 1)

    let n = 1 << LOG_PACKING; // 128
    let mut weights = Vec::with_capacity(n);
    // Layout: i ∈ {0..64} → bit-6 = 0 branch (eq_lo); i ∈ {64..128} → bit-6 = 1.
    for i in 0..n {
        let i_lo = i & 63;
        let bit_6 = (i >> 6) & 1;
        let eq_b6 = if bit_6 == 1 { eq_hi } else { eq_lo };
        weights.push(lambda[i_lo] * eq_b6);
    }
    weights
}

/// Batched version of [`fold_1b_rows_naive`]: compute `s_hat_v_k` for each
/// `suffix_tensors[k]` in a single bit-scan over `packed_witness`. Halves the
/// amortized bit-scanning cost vs calling `fold_1b_rows_naive` per suffix.
///
/// All suffix tensors must have the same length as `packed_witness`.
pub fn fold_1b_rows_multi(packed_witness: &[F128], suffix_tensors: &[&[F128]]) -> Vec<Vec<F128>> {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_multi_padded(packed_witness, suffix_tensors, &PaddingSpec::dense(m))
}

/// Padding-aware variant of [`fold_1b_rows_multi`]. Routes the k=2 MFR fast
/// paths through their `_padded` kernels; the scalar bit-scan fallback (k ≠ 2
/// or non-divisible len) is untouched — those `m` are tiny anyway.
pub fn fold_1b_rows_multi_padded(
    packed_witness: &[F128],
    suffix_tensors: &[&[F128]],
    padding: &PaddingSpec,
) -> Vec<Vec<F128>> {
    use rayon::prelude::*;
    let k = suffix_tensors.len();
    let n = 1 << LOG_PACKING;
    assert!(
        suffix_tensors
            .iter()
            .all(|t| t.len() == packed_witness.len())
    );

    let zero_acc = || vec![vec![F128::ZERO; n]; k];

    // The k=2 case (one pair of outers) is the hot path used by `open_batch`
    // for zerocheck + lincheck claims. Method-of-four-Russians fold (ported
    // from Binius): process several elements at a time with subset-sum table
    // lookups per output bit, eliminating the scalar bit-scan's data-dependent
    // control flow. The 16-wide variant groups 16 elements (four 4-element
    // tables, 16-bit masks) so each acc entry is touched once per 16 elements,
    // halving acc RMW traffic (the fold is LSU-bound) for ~1.25× over 8-wide.
    // We run two *independent* 1-way 16-wide folds rather than one fused 2-way
    // fold: the fused kernel's two accumulators + eight tables cause register
    // pressure that eats most of the 16-wide win, and the shared bit-transpose
    // it would save is nearly free. Falls back to the fused 8-wide → 4-wide →
    // scalar as divisibility drops (only at toy m).
    if k == 2 {
        if packed_witness.len().is_multiple_of(16) {
            let a0 =
                fold_1b_rows_1way_mfr_16wide_padded(packed_witness, suffix_tensors[0], padding);
            let a1 =
                fold_1b_rows_1way_mfr_16wide_padded(packed_witness, suffix_tensors[1], padding);
            return vec![a0, a1];
        }
        if packed_witness.len().is_multiple_of(8) {
            let (a0, a1) = fold_1b_rows_2way_mfr_8wide_padded(
                packed_witness,
                suffix_tensors[0],
                suffix_tensors[1],
                padding,
            );
            return vec![a0, a1];
        }
        if packed_witness.len().is_multiple_of(4) {
            let (a0, a1) = fold_1b_rows_2way_mfr_padded(
                packed_witness,
                suffix_tensors[0],
                suffix_tensors[1],
                padding,
            );
            return vec![a0, a1];
        }
    }

    packed_witness
        .par_iter()
        .enumerate()
        .fold(zero_acc, |mut acc, (i_rest, elem)| {
            // Single bit-scan, write into all k accumulators.
            let mut lo = elem.lo;
            while lo != 0 {
                let r = lo.trailing_zeros() as usize;
                for (j, t) in suffix_tensors.iter().enumerate() {
                    acc[j][r] += t[i_rest];
                }
                lo &= lo - 1;
            }
            let mut hi = elem.hi;
            while hi != 0 {
                let r = hi.trailing_zeros() as usize;
                for (j, t) in suffix_tensors.iter().enumerate() {
                    acc[j][64 | r] += t[i_rest];
                }
                hi &= hi - 1;
            }
            acc
        })
        .reduce(zero_acc, |mut a, b| {
            for (av, bv) in a.iter_mut().zip(b.iter()) {
                for (avi, bvi) in av.iter_mut().zip(bv.iter()) {
                    *avi += *bvi;
                }
            }
            a
        })
}

/// Parallel `build_eq` for ring-switching's suffix tensors. Same output as
/// [`crate::zerocheck::univariate_skip::build_eq`] (byte-identical), but
/// parallelizes the inner doubling loop across rayon threads.
///
/// Each level `i` doubles a table of size `2^i` → `2^(i+1)`: for each
/// `x ∈ 0..2^i`, write `t[x | (1<<i)] = t[x] * r_i` and
/// `t[x] = t[x] * (1-r_i)`. The iterations within one level are
/// independent and trivially parallelize. Earlier levels are tiny so
/// rayon's per-task overhead dominates; we keep them sequential and only
/// switch to parallel above a threshold.
fn build_eq_parallel(r: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    let n = r.len();
    // Uninit alloc — at iter `i`, the loop reads from t[..2^i] (always written
    // by an earlier iter or the t[0] = ONE seed) and writes to t[2^i..2^(i+1)]
    // (purely written, never read first). So every slot is written before any
    // read; uninit is safe.
    let mut t = crate::alloc_uninit_f128_vec(1usize << n);
    t[0] = F128::ONE;
    // Threshold below which rayon dispatch overhead beats the parallel work.
    const PAR_THRESHOLD: usize = 1 << 12;
    for i in 0..n {
        let r_i = r[i];
        let one_minus_r = F128::ONE + r_i;
        let half = 1usize << i;
        let (lo, hi_rest) = t.split_at_mut(half);
        let hi = &mut hi_rest[..half];
        if half < PAR_THRESHOLD {
            for (lo_x, hi_x) in lo.iter_mut().zip(hi.iter_mut()) {
                let old = *lo_x;
                *hi_x = old * r_i;
                *lo_x = old * one_minus_r;
            }
        } else {
            lo.par_iter_mut()
                .zip(hi.par_iter_mut())
                .for_each(|(lo_x, hi_x)| {
                    let old = *lo_x;
                    *hi_x = old * r_i;
                    *lo_x = old * one_minus_r;
                });
        }
    }
    t
}

/// Tensor-factored `build_eq`: split the point `r` (length `n`) into a low
/// part `r[..n_lo]` and a high part `r[n_lo..]`, returning the two smaller
/// eq-tables `(eq_lo, eq_hi)` of lengths `2^n_lo` and `2^(n - n_lo)`.
///
/// The full tensor factors **exactly** (GF(2^128) is a field — multiply is
/// associative and has no rounding):
///
/// ```text
/// build_eq_parallel(r)[i] == eq_lo[i & (2^n_lo - 1)] * eq_hi[i >> n_lo]
/// ```
///
/// because round `j` of `build_eq` splits on bit `j` of the index and bit `j`
/// selects `r[j]`. So the low `n_lo` index bits depend only on `r[..n_lo]` and
/// the high bits only on `r[n_lo..]`.
///
/// Materializing the two factors costs `2^n_lo + 2^(n - n_lo)` entries instead
/// of `2^n`. Consumers either reconstruct each full entry on demand as one GF
/// multiply ([`fold_b128_elems_split`]) or never form it at all when the
/// consumer is linear in the tensor ([`fold_1b_rows_split`]).
pub fn build_eq_split(r: &[F128], n_lo: usize) -> (Vec<F128>, Vec<F128>) {
    assert!(n_lo <= r.len());
    let eq_lo = build_eq_parallel(&r[..n_lo]);
    let eq_hi = build_eq_parallel(&r[n_lo..]);
    (eq_lo, eq_hi)
}

/// Pick the low-split width `n_lo` for a suffix tensor of length `2^n`.
/// Balanced near `n/2` so both factors are ~`2^(n/2)` (L1/L2-resident), and
/// clamped to `[4, n]` so the low block `2^n_lo` is a whole number of 16-wide
/// MFR chunks (`n_lo ≥ 4` ⇒ block ≥ 16). The high part drives block-level
/// parallelism (`2^(n - n_lo)` blocks). Only meaningful for `n ≥ 4` (the
/// split path requires `len` divisible by 16).
pub fn split_n_lo(n: usize) -> usize {
    (n / 2).clamp(4, n)
}

/// Build the 16-entry subset-sum lookup table over 4 F128 elements.
///
/// `sums[mask]` = `Σ_{k=0..4 : bit_k(mask) = 1} elems[k]` for `mask ∈ 0..16`.
/// Cost: 15 F128 additions (8 + 4 + 2 + 1) via the standard doubling pattern.
#[inline(always)]
fn subset_sums_4(elems: [F128; 4]) -> [F128; 16] {
    let mut sums = [F128::ZERO; 16];
    // After processing elem[i], sums[0..2^(i+1)] are populated with the
    // subset sums over elems[0..=i].
    for (i, &e) in elems.iter().enumerate() {
        let span_log = i + 1;
        let half = 1 << i;
        // sums[half..2*half] = sums[0..half] + e
        for k in 0..half {
            sums[half + k] = sums[k] + e;
        }
        let _ = span_log;
    }
    sums
}

/// Like `fold_1b_rows_multi` for `k=2`, but using the **method-of-four-Russians**
/// algorithm ported from Binius. Processes the packed witness in groups of 4
/// elements; per group, builds two 16-entry subset-sum lookup tables (one
/// per claim) and then for each output bit position `r ∈ 0..128` does **one
/// table lookup + one RMW** into the accumulator, regardless of bit density.
///
/// This replaces the scalar bit-scan, which is data-dependent (per set bit:
/// `trailing_zeros + RMW + branch`) with a constant-cost-per-`r` inner loop.
/// At ~50% set-bit density, this is ~2× fewer RMWs per element (128 per
/// group of 4 elements = 32 per element, vs ~64 set bits × 1 RMW per element
/// in the scalar path), and the OoO engine can pipeline the constant-cost
/// loop more aggressively than the bit-scan.
pub fn fold_1b_rows_2way_mfr(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
) -> (Vec<F128>, Vec<F128>) {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_2way_mfr_padded(packed_witness, t0, t1, &PaddingSpec::dense(m))
}

/// Padding-aware variant of [`fold_1b_rows_2way_mfr`]. Skips chunks of 4
/// F128s that fall entirely in the zero padding of every block.
pub fn fold_1b_rows_2way_mfr_padded(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING; // 128
    assert_eq!(t0.len(), packed_witness.len());
    assert_eq!(t1.len(), packed_witness.len());
    assert!(
        packed_witness.len().is_multiple_of(4),
        "fold_1b_rows_2way_mfr requires len divisible by 4 (got {})",
        packed_witness.len()
    );
    let skip = ChunkPadding::new(padding, 4);

    let pair = packed_witness
        .par_chunks(4)
        .zip(t0.par_chunks(4))
        .zip(t1.par_chunks(4))
        .enumerate()
        .fold(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (chunk_idx, ((m_chunk, t0_chunk), t1_chunk))| {
                if skip.skip(chunk_idx) {
                    return (a0, a1);
                }
                let v0: [F128; 4] = [t0_chunk[0], t0_chunk[1], t0_chunk[2], t0_chunk[3]];
                let v1: [F128; 4] = [t1_chunk[0], t1_chunk[1], t1_chunk[2], t1_chunk[3]];

                // Build the two 16-entry subset-sum lookup tables.
                let lookup0 = subset_sums_4(v0);
                let lookup1 = subset_sums_4(v1);

                // Cache all 16 bytes of each m element for fast indexed access.
                let m_bytes: [[u8; 16]; 4] = [
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[0].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[0].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[1].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[1].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[2].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[2].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[3].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[3].hi.to_le_bytes());
                        b
                    },
                ];

                // For each byte position (16 total = bits [r_byte*8, r_byte*8+8)):
                //   - Gather the same byte from each of the 4 m elements.
                //   - Pack into a u64 with the 4 bytes occupying byte slots 0..4
                //     (slots 4..8 are zero).
                //   - Apply 8×8 bit transpose. After transpose, byte p of the
                //     u64 has its low-bit positions filled with
                //     (bit-p of m[0]'s r_byte, bit-p of m[1]'s, bit-p of m[2]'s,
                //      bit-p of m[3]'s) — that's exactly the 4-bit mask for
                //     output position r = r_byte*8 + p.
                //   - Look up the mask in the subset-sum tables and XOR into
                //     a0[r], a1[r].
                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24);
                    let transposed = transpose_8x8_bits(combined);
                    let tb = transposed.to_le_bytes();
                    let base = r_byte * 8;
                    // 8 unrolled lookups + RMWs. Each transposed byte's low
                    // 4 bits hold the mask; high 4 bits are always zero (the
                    // upper 4 byte-slots of `combined` were zero).
                    a0[base] += lookup0[(tb[0] & 0x0F) as usize];
                    a1[base] += lookup1[(tb[0] & 0x0F) as usize];
                    a0[base + 1] += lookup0[(tb[1] & 0x0F) as usize];
                    a1[base + 1] += lookup1[(tb[1] & 0x0F) as usize];
                    a0[base + 2] += lookup0[(tb[2] & 0x0F) as usize];
                    a1[base + 2] += lookup1[(tb[2] & 0x0F) as usize];
                    a0[base + 3] += lookup0[(tb[3] & 0x0F) as usize];
                    a1[base + 3] += lookup1[(tb[3] & 0x0F) as usize];
                    a0[base + 4] += lookup0[(tb[4] & 0x0F) as usize];
                    a1[base + 4] += lookup1[(tb[4] & 0x0F) as usize];
                    a0[base + 5] += lookup0[(tb[5] & 0x0F) as usize];
                    a1[base + 5] += lookup1[(tb[5] & 0x0F) as usize];
                    a0[base + 6] += lookup0[(tb[6] & 0x0F) as usize];
                    a1[base + 6] += lookup1[(tb[6] & 0x0F) as usize];
                    a0[base + 7] += lookup0[(tb[7] & 0x0F) as usize];
                    a1[base + 7] += lookup1[(tb[7] & 0x0F) as usize];
                }

                (a0, a1)
            },
        )
        .reduce(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (b0, b1)| {
                for r in 0..n {
                    a0[r] += b0[r];
                    a1[r] += b1[r];
                }
                (a0, a1)
            },
        );

    (pair.0, pair.1)
}

/// **Experimental** 8-wide / two-k=4-table version of [`fold_1b_rows_2way_mfr`].
/// Packs 8 witness elements per transpose group (the 4-wide version wastes the
/// upper 4 transpose rows). The single transpose is shared across both claims;
/// each claim uses two small 16-entry tables (low nibble = elems 0-3, high =
/// elems 4-7) XORed in-register before one acc RMW. Net vs the current 2-way:
/// transposes halved, acc-RMWs halved per claim, same small tables.
pub fn fold_1b_rows_2way_mfr_8wide(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
) -> (Vec<F128>, Vec<F128>) {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_2way_mfr_8wide_padded(packed_witness, t0, t1, &PaddingSpec::dense(m))
}

/// Padding-aware variant of [`fold_1b_rows_2way_mfr_8wide`]. Skips chunks of
/// 8 F128s that fall entirely in the zero padding of every block — those
/// chunks contribute nothing (witness bytes = 0 → subset-sum mask = 0 →
/// `lookup[0] = 0`).
pub fn fold_1b_rows_2way_mfr_8wide_padded(
    packed_witness: &[F128],
    t0: &[F128],
    t1: &[F128],
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING;
    assert_eq!(t0.len(), packed_witness.len());
    assert_eq!(t1.len(), packed_witness.len());
    assert!(packed_witness.len().is_multiple_of(8));
    let skip = ChunkPadding::new(padding, 8);

    packed_witness
        .par_chunks(8)
        .zip(t0.par_chunks(8))
        .zip(t1.par_chunks(8))
        .enumerate()
        .fold(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (chunk_idx, ((m_chunk, t0_chunk), t1_chunk))| {
                if skip.skip(chunk_idx) {
                    return (a0, a1);
                }
                let t0_lo = subset_sums_4([t0_chunk[0], t0_chunk[1], t0_chunk[2], t0_chunk[3]]);
                let t0_hi = subset_sums_4([t0_chunk[4], t0_chunk[5], t0_chunk[6], t0_chunk[7]]);
                let t1_lo = subset_sums_4([t1_chunk[0], t1_chunk[1], t1_chunk[2], t1_chunk[3]]);
                let t1_hi = subset_sums_4([t1_chunk[4], t1_chunk[5], t1_chunk[6], t1_chunk[7]]);

                let mut m_bytes = [[0u8; 16]; 8];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let tb = transpose_8x8_bits(combined).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let mask = tb[p];
                        let lo = (mask & 0x0F) as usize;
                        let hi = (mask >> 4) as usize;
                        a0[base + p] += t0_lo[lo] + t0_hi[hi];
                        a1[base + p] += t1_lo[lo] + t1_hi[hi];
                    }
                }
                (a0, a1)
            },
        )
        .reduce(
            || (vec![F128::ZERO; n], vec![F128::ZERO; n]),
            |(mut a0, mut a1), (b0, b1)| {
                for r in 0..n {
                    a0[r] += b0[r];
                    a1[r] += b1[r];
                }
                (a0, a1)
            },
        )
}

/// Single-tensor (k=1) version of the method-of-four-Russians fold, mirroring
/// [`fold_1b_rows_2way_mfr`]. Same algorithm but maintains one subset-sum
/// table and one accumulator. Used by [`fold_1b_rows_naive`] for inputs
/// divisible by 4 (the standard case at any reasonable `m`).
pub fn fold_1b_rows_1way_mfr(packed_witness: &[F128], t: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING; // 128
    assert_eq!(t.len(), packed_witness.len());
    assert!(
        packed_witness.len().is_multiple_of(4),
        "fold_1b_rows_1way_mfr requires len divisible by 4 (got {})",
        packed_witness.len()
    );

    packed_witness
        .par_chunks(4)
        .zip(t.par_chunks(4))
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (m_chunk, t_chunk)| {
                let v: [F128; 4] = [t_chunk[0], t_chunk[1], t_chunk[2], t_chunk[3]];
                let lookup = subset_sums_4(v);

                let m_bytes: [[u8; 16]; 4] = [
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[0].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[0].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[1].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[1].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[2].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[2].hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m_chunk[3].lo.to_le_bytes());
                        b[8..].copy_from_slice(&m_chunk[3].hi.to_le_bytes());
                        b
                    },
                ];

                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24);
                    let transposed = transpose_8x8_bits(combined);
                    let tb = transposed.to_le_bytes();
                    let base = r_byte * 8;
                    acc[base] += lookup[(tb[0] & 0x0F) as usize];
                    acc[base + 1] += lookup[(tb[1] & 0x0F) as usize];
                    acc[base + 2] += lookup[(tb[2] & 0x0F) as usize];
                    acc[base + 3] += lookup[(tb[3] & 0x0F) as usize];
                    acc[base + 4] += lookup[(tb[4] & 0x0F) as usize];
                    acc[base + 5] += lookup[(tb[5] & 0x0F) as usize];
                    acc[base + 6] += lookup[(tb[6] & 0x0F) as usize];
                    acc[base + 7] += lookup[(tb[7] & 0x0F) as usize];
                }

                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n],
            |mut a, b| {
                for r in 0..n {
                    a[r] += b[r];
                }
                a
            },
        )
}

/// **Experimental** 8-wide / two-k=4-table variant. Packs 8 elements per
/// transpose (vs the 4-wide version's wasted upper rows), but keeps two small
/// 16-entry tables (low nibble = elems 0-3, high nibble = elems 4-7). The two
/// lookups are XORed in-register before a single `acc` RMW — so vs the current
/// kernel this halves the transpose count AND halves the acc-RMW count, while
/// keeping the well-reused small tables.
pub fn fold_1b_rows_1way_mfr_8wide_k4(packed_witness: &[F128], t: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING;
    assert_eq!(t.len(), packed_witness.len());
    assert!(packed_witness.len().is_multiple_of(8));

    packed_witness
        .par_chunks(8)
        .zip(t.par_chunks(8))
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (m_chunk, t_chunk)| {
                let lo_tbl = subset_sums_4([t_chunk[0], t_chunk[1], t_chunk[2], t_chunk[3]]);
                let hi_tbl = subset_sums_4([t_chunk[4], t_chunk[5], t_chunk[6], t_chunk[7]]);

                let mut m_bytes = [[0u8; 16]; 8];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let tb = transpose_8x8_bits(combined).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let mask = tb[p];
                        acc[base + p] +=
                            lo_tbl[(mask & 0x0F) as usize] + hi_tbl[(mask >> 4) as usize];
                    }
                }
                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n],
            |mut a, b| {
                for r in 0..n {
                    a[r] += b[r];
                }
                a
            },
        )
}

/// Single-tensor 16-wide method-of-four-Russians fold. Processes 16 witness
/// elements per group (four 4-element subset-sum tables, 16-bit per-position
/// masks) so each length-128 accumulator entry is touched once per 16 elements
/// instead of once per 8, halving acc load+store traffic. Gathers (32·N), eor3
/// count, and table-build adds match the 8-wide kernel; the only delta is fewer
/// acc RMWs. Measured ~1.25× over the 8-wide kernel (the fold is LSU-bound).
///
/// `open_batch`'s k=2 path runs this **twice** (once per suffix tensor) rather
/// than one fused 2-way fold: keeping a single length-128 accumulator + four
/// tables in flight avoids the register pressure of the 2-way's two
/// accumulators + eight tables, which ate most of the 16-wide win there. The
/// shared bit-transpose recomputed per call is nearly free (the fold is not
/// memory-bandwidth bound).
pub fn fold_1b_rows_1way_mfr_16wide_padded(
    packed_witness: &[F128],
    t: &[F128],
    padding: &PaddingSpec,
) -> Vec<F128> {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING;
    assert_eq!(t.len(), packed_witness.len());
    assert!(packed_witness.len().is_multiple_of(16));
    let skip = ChunkPadding::new(padding, 16);

    packed_witness
        .par_chunks(16)
        .zip(t.par_chunks(16))
        .enumerate()
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (chunk_idx, (m_chunk, t_chunk))| {
                if skip.skip(chunk_idx) {
                    return acc;
                }
                let tbl0 = subset_sums_4([t_chunk[0], t_chunk[1], t_chunk[2], t_chunk[3]]);
                let tbl1 = subset_sums_4([t_chunk[4], t_chunk[5], t_chunk[6], t_chunk[7]]);
                let tbl2 = subset_sums_4([t_chunk[8], t_chunk[9], t_chunk[10], t_chunk[11]]);
                let tbl3 = subset_sums_4([t_chunk[12], t_chunk[13], t_chunk[14], t_chunk[15]]);

                let mut m_bytes = [[0u8; 16]; 16];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let lo8: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let hi8: u64 = (m_bytes[8][r_byte] as u64)
                        | ((m_bytes[9][r_byte] as u64) << 8)
                        | ((m_bytes[10][r_byte] as u64) << 16)
                        | ((m_bytes[11][r_byte] as u64) << 24)
                        | ((m_bytes[12][r_byte] as u64) << 32)
                        | ((m_bytes[13][r_byte] as u64) << 40)
                        | ((m_bytes[14][r_byte] as u64) << 48)
                        | ((m_bytes[15][r_byte] as u64) << 56);
                    let tlo = transpose_8x8_bits(lo8).to_le_bytes();
                    let thi = transpose_8x8_bits(hi8).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let m_lo = tlo[p];
                        let m_hi = thi[p];
                        acc[base + p] += tbl0[(m_lo & 0x0F) as usize]
                            + tbl1[(m_lo >> 4) as usize]
                            + tbl2[(m_hi & 0x0F) as usize]
                            + tbl3[(m_hi >> 4) as usize];
                    }
                }
                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n],
            |mut a, b| {
                for r in 0..n {
                    a[r] += b[r];
                }
                a
            },
        )
}

/// Dense (no-skip) wrapper over [`fold_1b_rows_1way_mfr_16wide_padded`]. Used by
/// [`fold_1b_rows_naive`] for inputs divisible by 16.
pub fn fold_1b_rows_1way_mfr_16wide_k4(packed_witness: &[F128], t: &[F128]) -> Vec<F128> {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    fold_1b_rows_1way_mfr_16wide_padded(packed_witness, t, &PaddingSpec::dense(m))
}

/// Tensor-split sibling of [`fold_1b_rows_1way_mfr_16wide_padded`]. Instead of
/// streaming a fully-materialized length-`2^n` suffix tensor `t`, it takes the
/// two factors `(eq_lo, eq_hi)` from [`build_eq_split`] and reassociates the
/// fold as inner-then-outer:
///
/// ```text
/// s_hat_v[r] = Σ_i bit_r(W[i]) · t[i]
///            = Σ_{i_hi} eq_hi[i_hi] · ( Σ_{i_lo} bit_r(W[i_hi·B + i_lo]) · eq_lo[i_lo] )
/// ```
///
/// with `B = eq_lo.len()` (a multiple of 16) and `i = i_hi·B + i_lo`. The inner
/// sum is the same 16-wide method-of-four-Russians fold over one length-`B`
/// block against `eq_lo`; the outer step scales that length-128 block result by
/// `eq_hi[i_hi]` and XORs it into the global accumulator.
///
/// Result is **byte-identical** to
/// `fold_1b_rows_1way_mfr_16wide_padded(W, build_eq_parallel(r), padding)`:
/// GF(2^128) add is XOR (associative/commutative) and multiply is exact and
/// distributes, so the reassociation reproduces the same multiset of XOR terms.
/// Two wins over the materialized kernel:
///   1. The four MFR subset-sum tables per 16-element chunk are built from
///      `eq_lo` and are **identical for every block**, so they are precomputed
///      once and reused across all `2^(n - n_lo)` blocks (no per-chunk table
///      rebuilds).
///   2. The `2^n`-entry tensor is never streamed from RAM — only `eq_lo`
///      (+ its tables) and `eq_hi` are read, and they stay cache-resident.
///      Since the fold is LSU-bound, dropping that traffic is the main win.
pub fn fold_1b_rows_split(
    packed_witness: &[F128],
    eq_lo: &[F128],
    eq_hi: &[F128],
    padding: &PaddingSpec,
) -> Vec<F128> {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING; // 128
    let b = eq_lo.len();
    assert!(
        b.is_multiple_of(16),
        "fold_1b_rows_split: eq_lo block size must be a multiple of 16 (got {b})"
    );
    assert_eq!(packed_witness.len(), b * eq_hi.len());
    let chunks_per_block = b / 16;
    let skip = ChunkPadding::new(padding, 16);

    // Precompute the eq_lo subset-sum tables once and reuse for every block.
    // `tables[c]` holds the four 16-entry tables for local chunk `c`'s 16 eq_lo
    // values — exactly what the materialized kernel rebuilds per chunk.
    let tables: Vec<[[F128; 16]; 4]> = (0..chunks_per_block)
        .map(|c| {
            let o = c * 16;
            [
                subset_sums_4([eq_lo[o], eq_lo[o + 1], eq_lo[o + 2], eq_lo[o + 3]]),
                subset_sums_4([eq_lo[o + 4], eq_lo[o + 5], eq_lo[o + 6], eq_lo[o + 7]]),
                subset_sums_4([eq_lo[o + 8], eq_lo[o + 9], eq_lo[o + 10], eq_lo[o + 11]]),
                subset_sums_4([eq_lo[o + 12], eq_lo[o + 13], eq_lo[o + 14], eq_lo[o + 15]]),
            ]
        })
        .collect();

    packed_witness
        .par_chunks(b)
        .enumerate()
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, (i_hi, w_block)| {
                let mut inner = [F128::ZERO; 128];
                let base_chunk = i_hi * chunks_per_block;
                for c in 0..chunks_per_block {
                    // Same per-chunk skip predicate as the materialized kernel,
                    // evaluated at the identical global chunk index — so the two
                    // touch the exact same set of chunks.
                    if skip.skip(base_chunk + c) {
                        continue;
                    }
                    let m_chunk = &w_block[c * 16..c * 16 + 16];
                    let [tbl0, tbl1, tbl2, tbl3] = &tables[c];

                    let mut m_bytes = [[0u8; 16]; 16];
                    for (e, slot) in m_bytes.iter_mut().enumerate() {
                        slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                        slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                    }

                    for r_byte in 0..16 {
                        let lo8: u64 = (m_bytes[0][r_byte] as u64)
                            | ((m_bytes[1][r_byte] as u64) << 8)
                            | ((m_bytes[2][r_byte] as u64) << 16)
                            | ((m_bytes[3][r_byte] as u64) << 24)
                            | ((m_bytes[4][r_byte] as u64) << 32)
                            | ((m_bytes[5][r_byte] as u64) << 40)
                            | ((m_bytes[6][r_byte] as u64) << 48)
                            | ((m_bytes[7][r_byte] as u64) << 56);
                        let hi8: u64 = (m_bytes[8][r_byte] as u64)
                            | ((m_bytes[9][r_byte] as u64) << 8)
                            | ((m_bytes[10][r_byte] as u64) << 16)
                            | ((m_bytes[11][r_byte] as u64) << 24)
                            | ((m_bytes[12][r_byte] as u64) << 32)
                            | ((m_bytes[13][r_byte] as u64) << 40)
                            | ((m_bytes[14][r_byte] as u64) << 48)
                            | ((m_bytes[15][r_byte] as u64) << 56);
                        let tlo = transpose_8x8_bits(lo8).to_le_bytes();
                        let thi = transpose_8x8_bits(hi8).to_le_bytes();
                        let base = r_byte * 8;
                        for p in 0..8 {
                            let m_lo = tlo[p];
                            let m_hi = thi[p];
                            inner[base + p] += tbl0[(m_lo & 0x0F) as usize]
                                + tbl1[(m_lo >> 4) as usize]
                                + tbl2[(m_hi & 0x0F) as usize]
                                + tbl3[(m_hi >> 4) as usize];
                        }
                    }
                }
                // Outer: scale this block's length-128 partial by eq_hi[i_hi].
                // `e · (Σ eq_lo·bit) = Σ (e·eq_lo)·bit` distributes exactly, so
                // each term equals the materialized `t[i] = eq_lo·eq_hi` term.
                let e = eq_hi[i_hi];
                for r in 0..n {
                    acc[r] += e * inner[r];
                }
                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n],
            |mut a, b| {
                for r in 0..n {
                    a[r] += b[r];
                }
                a
            },
        )
}

/// Two-claim variant of [`fold_1b_rows_split`] with stack-allocated per-claim
/// inner accumulators. The common batched case (exactly 2 dense claims, e.g.
/// `[ab, c]` or `[ab, c]` alongside a sparse chain claim) hits this fast path.
///
/// Cross-claim sharing per chunk:
///   * one streaming read of the 16 packed_witness entries
///   * one bit transpose ([`transpose_8x8_bits`])
///   * per-claim subset-sum table lookups + per-claim inner accumulator update
///
/// Per-claim outputs are **byte-identical** to calling [`fold_1b_rows_split`]
/// twice — same chunk-skip predicate, same XOR multiset.
pub fn fold_1b_rows_split_2way(
    packed_witness: &[F128],
    eq_lo_0: &[F128],
    eq_hi_0: &[F128],
    eq_lo_1: &[F128],
    eq_hi_1: &[F128],
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING; // 128
    let b = eq_lo_0.len();
    assert_eq!(eq_lo_1.len(), b);
    let n_hi = eq_hi_0.len();
    assert_eq!(eq_hi_1.len(), n_hi);
    assert!(
        b.is_multiple_of(16),
        "fold_1b_rows_split_2way: eq_lo block size must be a multiple of 16 (got {b})"
    );
    assert_eq!(packed_witness.len(), b * n_hi);
    let chunks_per_block = b / 16;
    let skip = ChunkPadding::new(padding, 16);

    // Precompute both claims' subset-sum tables once.
    let tables_0: Vec<[[F128; 16]; 4]> = (0..chunks_per_block)
        .map(|c| {
            let o = c * 16;
            [
                subset_sums_4([eq_lo_0[o], eq_lo_0[o + 1], eq_lo_0[o + 2], eq_lo_0[o + 3]]),
                subset_sums_4([
                    eq_lo_0[o + 4],
                    eq_lo_0[o + 5],
                    eq_lo_0[o + 6],
                    eq_lo_0[o + 7],
                ]),
                subset_sums_4([
                    eq_lo_0[o + 8],
                    eq_lo_0[o + 9],
                    eq_lo_0[o + 10],
                    eq_lo_0[o + 11],
                ]),
                subset_sums_4([
                    eq_lo_0[o + 12],
                    eq_lo_0[o + 13],
                    eq_lo_0[o + 14],
                    eq_lo_0[o + 15],
                ]),
            ]
        })
        .collect();
    let tables_1: Vec<[[F128; 16]; 4]> = (0..chunks_per_block)
        .map(|c| {
            let o = c * 16;
            [
                subset_sums_4([eq_lo_1[o], eq_lo_1[o + 1], eq_lo_1[o + 2], eq_lo_1[o + 3]]),
                subset_sums_4([
                    eq_lo_1[o + 4],
                    eq_lo_1[o + 5],
                    eq_lo_1[o + 6],
                    eq_lo_1[o + 7],
                ]),
                subset_sums_4([
                    eq_lo_1[o + 8],
                    eq_lo_1[o + 9],
                    eq_lo_1[o + 10],
                    eq_lo_1[o + 11],
                ]),
                subset_sums_4([
                    eq_lo_1[o + 12],
                    eq_lo_1[o + 13],
                    eq_lo_1[o + 14],
                    eq_lo_1[o + 15],
                ]),
            ]
        })
        .collect();

    let zero_acc = || (vec![F128::ZERO; n], vec![F128::ZERO; n]);

    packed_witness
        .par_chunks(b)
        .enumerate()
        .fold(zero_acc, |(mut acc0, mut acc1), (i_hi, w_block)| {
            // Two stack-allocated inner accumulators — identical layout to
            // the single-claim split path, just two of them.
            let mut inner0 = [F128::ZERO; 128];
            let mut inner1 = [F128::ZERO; 128];
            let base_chunk = i_hi * chunks_per_block;
            for c in 0..chunks_per_block {
                if skip.skip(base_chunk + c) {
                    continue;
                }
                let m_chunk = &w_block[c * 16..c * 16 + 16];
                let [t0a, t0b, t0c, t0d] = &tables_0[c];
                let [t1a, t1b, t1c, t1d] = &tables_1[c];

                let mut m_bytes = [[0u8; 16]; 16];
                for (e, slot) in m_bytes.iter_mut().enumerate() {
                    slot[..8].copy_from_slice(&m_chunk[e].lo.to_le_bytes());
                    slot[8..].copy_from_slice(&m_chunk[e].hi.to_le_bytes());
                }

                for r_byte in 0..16 {
                    let lo8: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24)
                        | ((m_bytes[4][r_byte] as u64) << 32)
                        | ((m_bytes[5][r_byte] as u64) << 40)
                        | ((m_bytes[6][r_byte] as u64) << 48)
                        | ((m_bytes[7][r_byte] as u64) << 56);
                    let hi8: u64 = (m_bytes[8][r_byte] as u64)
                        | ((m_bytes[9][r_byte] as u64) << 8)
                        | ((m_bytes[10][r_byte] as u64) << 16)
                        | ((m_bytes[11][r_byte] as u64) << 24)
                        | ((m_bytes[12][r_byte] as u64) << 32)
                        | ((m_bytes[13][r_byte] as u64) << 40)
                        | ((m_bytes[14][r_byte] as u64) << 48)
                        | ((m_bytes[15][r_byte] as u64) << 56);
                    let tlo = transpose_8x8_bits(lo8).to_le_bytes();
                    let thi = transpose_8x8_bits(hi8).to_le_bytes();
                    let base = r_byte * 8;
                    for p in 0..8 {
                        let m_lo = tlo[p];
                        let m_hi = thi[p];
                        let i_lo4 = (m_lo & 0x0F) as usize;
                        let i_hi4 = (m_lo >> 4) as usize;
                        let i_lo4h = (m_hi & 0x0F) as usize;
                        let i_hi4h = (m_hi >> 4) as usize;
                        inner0[base + p] += t0a[i_lo4] + t0b[i_hi4] + t0c[i_lo4h] + t0d[i_hi4h];
                        inner1[base + p] += t1a[i_lo4] + t1b[i_hi4] + t1c[i_lo4h] + t1d[i_hi4h];
                    }
                }
            }
            let e0 = eq_hi_0[i_hi];
            let e1 = eq_hi_1[i_hi];
            for r in 0..n {
                acc0[r] += e0 * inner0[r];
                acc1[r] += e1 * inner1[r];
            }
            (acc0, acc1)
        })
        .reduce(zero_acc, |(mut a0, mut a1), (b0, b1)| {
            for r in 0..n {
                a0[r] += b0[r];
                a1[r] += b1[r];
            }
            (a0, a1)
        })
}

/// AB-claim `s_hat_v` specialization that **skips `fold_1b_rows` entirely**
/// when the upstream layer has already produced
/// `z_vec[i_inner] = ẑ(i_inner, x_outer)` (length `2^k_log`) — the pre-sumcheck
/// partial fold lincheck builds via `partial_fold_packed_z`.
///
/// # Identity
///
/// For a PCS opening at point `(r_inner_skip, r_inner_rest, x_outer)` where
/// `x_outer` matches lincheck's, the AB-suffix tensor in `fold_1b_rows`
/// factors over the same axis decomposition that `z_vec` was built along:
///
/// ```text
/// s_hat_v[b] = Σ_{j ∈ {0,1}^(m−7)} eq(suffix, j) · bit_b(packed_witness[j])
///            = Σ_{k ∈ {0,1}^(k_log − LOG_PACKING)}
///                eq(r_inner_rest[1..], k) · z_vec[b + 2^LOG_PACKING · k]
/// ```
///
/// `r_inner_rest[0]` becomes ring-switch's `prefix0` (`x_outer_full[0]`);
/// `r_inner_rest[1..]` is the suffix's inner part. The witness's outer
/// coords were already folded into `z_vec` by the partial fold.
///
/// Output is **byte-identical** to
/// `fold_1b_rows(packed_witness, build_eq(suffix))` for the AB claim — same
/// algebraic identity, just reassociated to use the lincheck intermediate.
///
/// # Cost
///
/// `128 · 2^(k_log − LOG_PACKING)` F128 mul-adds + a tiny eq tensor build.
/// At keccak m=29, k_log=17: 128 · 1024 = 131k mul-adds — tens of µs MT, vs
/// the ~7 ms share that AB contributes to `fold_1b_rows_split_2way`.
///
/// # Panics
///
/// - if `z_vec.len() != 2^(LOG_PACKING + tail.len())`.
pub fn s_hat_v_from_z_vec(z_vec: &[F128], x_inner_rest_tail: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    let n_packed = 1usize << LOG_PACKING; // 128
    let n_tail = 1usize << x_inner_rest_tail.len();
    assert_eq!(
        z_vec.len(),
        n_packed * n_tail,
        "z_vec length {} mismatches 2^(LOG_PACKING + tail.len()) = {}",
        z_vec.len(),
        n_packed * n_tail,
    );

    if x_inner_rest_tail.is_empty() {
        // Degenerate case (k_log == LOG_PACKING): the LOG_PACKING boundary
        // ate the only inner-rest coord — z_vec IS the per-prefix-bit answer.
        return z_vec.to_vec();
    }

    let eq_tail = build_eq_parallel(x_inner_rest_tail);

    // Iterate over k outer (sequential per-thread → cache-friendly stride-1
    // reads of z_vec). Parallelize across k-ranges; each thread accumulates
    // a private length-128 buffer and the reduce step XORs them together.
    eq_tail
        .par_iter()
        .enumerate()
        .fold(
            || vec![F128::ZERO; n_packed],
            |mut acc, (k, &w)| {
                let block = &z_vec[k * n_packed..(k + 1) * n_packed];
                for b in 0..n_packed {
                    acc[b] += w * block[b];
                }
                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n_packed],
            |mut a, b| {
                for i in 0..n_packed {
                    a[i] += b[i];
                }
                a
            },
        )
}

/// Compute the slice-MLE vector `s_hat_v` (length 128) from a packed witness
/// and a tensor-expanded suffix point.
///
/// `packed_witness[i_rest] ∈ F_{2^128}` with `i_rest ∈ {0..2^L}` where
/// `L = log2(packed_witness.len())`. `suffix_tensor` is `eq_ind(suffix)` over a
/// suffix point of length `L`.
///
/// Output: `s_hat_v[i_skip] = Σ_{i_rest} (i_skip-th bit of packed_witness[i_rest]) · suffix_tensor[i_rest]`
/// for `i_skip ∈ {0..128}`. The bit-index uses the natural polynomial-basis
/// decomposition of F_{2^128} (i.e., bit-i of the u128 .lo:.hi).
///
/// O(2^L · 128) algorithm parallelized across packed-witness positions via
/// rayon: each thread folds a chunk into a per-thread length-128 partial
/// accumulator; the reduce step XORs partials elementwise into the final
/// output.
pub fn fold_1b_rows_naive(packed_witness: &[F128], suffix_tensor: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    let n = 1 << LOG_PACKING;

    // Method-of-four-Russians fast path (standard case at any reasonable m).
    // 16-wide groups 16 elements per transpose pair so each acc entry is
    // touched once per 16 elements (~1.25× over 8-wide); fall back to 8-wide,
    // then 4-wide, then scalar as divisibility drops.
    if packed_witness.len().is_multiple_of(16) {
        return fold_1b_rows_1way_mfr_16wide_k4(packed_witness, suffix_tensor);
    }
    if packed_witness.len().is_multiple_of(8) {
        return fold_1b_rows_1way_mfr_8wide_k4(packed_witness, suffix_tensor);
    }
    if packed_witness.len() >= 4 && packed_witness.len().is_multiple_of(4) {
        return fold_1b_rows_1way_mfr(packed_witness, suffix_tensor);
    }

    // Partition into chunks; each chunk computes its own partial.
    // Empty accumulator allocator returns Vec<F128>(n) for the fold's init.
    let zero_acc = || vec![F128::ZERO; n];

    

    packed_witness
        .par_iter()
        .zip(suffix_tensor.par_iter())
        .fold(zero_acc, |mut acc, (elem, &w)| {
            // Bit r ∈ 0..64: from elem.lo.
            let mut lo = elem.lo;
            while lo != 0 {
                let r = lo.trailing_zeros() as usize;
                acc[r] += w;
                lo &= lo - 1;
            }
            // Bit r ∈ 64..128: from elem.hi.
            let mut hi = elem.hi;
            while hi != 0 {
                let r = hi.trailing_zeros() as usize;
                acc[64 | r] += w;
                hi &= hi - 1;
            }
            acc
        })
        .reduce(zero_acc, |mut a, b| {
            for (av, bv) in a.iter_mut().zip(b.iter()) {
                *av += *bv;
            }
            a
        })
}

/// Compute the verifier's claim check: `Σ_i weights[i] · s_hat_v[i]`.
pub fn claim_check(weights: &[F128], s_hat_v: &[F128]) -> F128 {
    inner_product(weights, s_hat_v)
}

/// Standard inner product `Σ_i a[i] · b[i]` over F_{2^128}.
pub fn inner_product(a: &[F128], b: &[F128]) -> F128 {
    assert_eq!(a.len(), b.len());
    let mut acc = F128::ZERO;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc += x * y;
    }
    acc
}

/// **TensorAlgebra transpose** (a.k.a. "bit transpose" of `s_hat_v`).
///
/// View `s_hat_v` (length 128) as a 128×128 binary matrix with row `i_skip` =
/// the 128 polynomial-basis bits of `s_hat_v[i_skip]`. Output `s_hat_u`
/// (length 128) is the transposed matrix re-packed: row `b` of `s_hat_u` =
/// column `b` of the input. Equivalently:
/// ```text
///     bit i_skip of s_hat_u[b]  ==  bit b of s_hat_v[i_skip]
/// ```
///
/// Used in the DP24 ring-switching: after computing `s_hat_v` (slice MLEs at
/// the suffix point), `s_hat_u = transpose(s_hat_v)` is the data viewed with
/// the "vertical" and "horizontal" dimensions swapped. The BaseFold target is
/// `T = ⟨s_hat_u, eq_ind(r'')⟩`.
///
/// Naive O(128²) bit-extract implementation. NEON acceleration via bit
/// transpose intrinsics is future work.
pub fn tensor_algebra_transpose(s_hat_v: &[F128]) -> Vec<F128> {
    assert_eq!(s_hat_v.len(), 1 << LOG_PACKING);
    let mut s_hat_u = vec![F128::ZERO; 1 << LOG_PACKING];
    for i_skip in 0..128 {
        let elem = s_hat_v[i_skip];
        // Iterate over the 128 bits b of `elem`; deposit into s_hat_u[b]'s bit i_skip.
        for b in 0..64 {
            if (elem.lo >> b) & 1 == 1 {
                if i_skip < 64 {
                    s_hat_u[b].lo |= 1u64 << i_skip;
                } else {
                    s_hat_u[b].hi |= 1u64 << (i_skip - 64);
                }
            }
        }
        for b in 0..64 {
            if (elem.hi >> b) & 1 == 1 {
                if i_skip < 64 {
                    s_hat_u[64 | b].lo |= 1u64 << i_skip;
                } else {
                    s_hat_u[64 | b].hi |= 1u64 << (i_skip - 64);
                }
            }
        }
    }
    s_hat_u
}

/// Compute `rs_eq_ind` (the "ring-switching equality indicator"), a transparent
/// multilinear of length `2^L` over the suffix domain.
///
/// `rs_eq_ind[i_rest] = Σ_b (bit b of suffix_tensor[i_rest]) · eq_r_dprime[b]`
///
/// Each `suffix_tensor[i_rest] ∈ F_{2^128}` is treated as 128 F_2-bits in the
/// polynomial basis; the inner product with `eq_r_dprime` (length 128) produces
/// one F_{2^128} value per suffix position. This is the transparent multilinear
/// the BaseFold protocol runs its sumcheck against.
///
/// O(128 · 2^L) parallelized across positions via rayon. Output positions are
/// independent — direct `par_iter` + `collect`.
pub fn fold_b128_elems_naive(suffix_tensor: &[F128], eq_r_dprime: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    suffix_tensor
        .par_iter()
        .map(|&elem| {
            let mut acc = F128::ZERO;
            let mut lo = elem.lo;
            while lo != 0 {
                let b = lo.trailing_zeros() as usize;
                acc += eq_r_dprime[b];
                lo &= lo - 1;
            }
            let mut hi = elem.hi;
            while hi != 0 {
                let b = hi.trailing_zeros() as usize;
                acc += eq_r_dprime[64 | b];
                hi &= hi - 1;
            }
            acc
        })
        .collect()
}

/// Bit-table accelerated `fold_b128_elems`. Precomputes 16 lookup tables (one
/// per byte position), each with 256 entries: `T[byte_idx][value] = Σ eq_r_dprime[bit]`
/// over set bits in `value` (offset by `byte_idx * 8`). Per element: 16 table
/// lookups + 16 F128 XORs, no data-dependent bit-scan.
///
/// Tables: 16 × 256 × 16 B = 64 KB (fits in L1+L2). Target speedup ~3× vs the
/// `trailing_zeros` loop in `fold_b128_elems_naive`.
pub fn fold_b128_elems(suffix_tensor: &[F128], eq_r_dprime: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    const N_BYTES: usize = 16; // bytes per F128
    const TABLE_SIZE: usize = 256;

    // Build the 16 byte-tables. `tables[byte_idx * 256 + value]` = the F128
    // sum of `eq_r_dprime[byte_idx*8 + bit]` over set bits in `value`.
    let mut tables = vec![F128::ZERO; N_BYTES * TABLE_SIZE];
    for byte_idx in 0..N_BYTES {
        let bit_base = byte_idx * 8;
        for value in 0..TABLE_SIZE {
            let mut acc = F128::ZERO;
            for bit_in_byte in 0..8 {
                if (value >> bit_in_byte) & 1 == 1 {
                    acc += eq_r_dprime[bit_base + bit_in_byte];
                }
            }
            tables[byte_idx * TABLE_SIZE + value] = acc;
        }
    }

    suffix_tensor
        .par_iter()
        .map(|&elem| {
            let tables_ptr = tables.as_ptr();
            let lo_bytes = elem.lo.to_le_bytes();
            let hi_bytes = elem.hi.to_le_bytes();
            // Tree reduction (depth 4) — see fold_b128_elems_split for the
            // pattern. Raw pointer access avoids per-lookup bounds checks
            // (max index = 15 * 256 + 255 = 4095 = N_BYTES * TABLE_SIZE - 1,
            // in bounds).
            let (l0, l1, l2, l3, l4, l5, l6, l7, h0, h1, h2, h3, h4, h5, h6, h7) = unsafe {
                (
                    *tables_ptr.add(lo_bytes[0] as usize),
                    *tables_ptr.add(TABLE_SIZE + lo_bytes[1] as usize),
                    *tables_ptr.add(2 * TABLE_SIZE + lo_bytes[2] as usize),
                    *tables_ptr.add(3 * TABLE_SIZE + lo_bytes[3] as usize),
                    *tables_ptr.add(4 * TABLE_SIZE + lo_bytes[4] as usize),
                    *tables_ptr.add(5 * TABLE_SIZE + lo_bytes[5] as usize),
                    *tables_ptr.add(6 * TABLE_SIZE + lo_bytes[6] as usize),
                    *tables_ptr.add(7 * TABLE_SIZE + lo_bytes[7] as usize),
                    *tables_ptr.add(8 * TABLE_SIZE + hi_bytes[0] as usize),
                    *tables_ptr.add(9 * TABLE_SIZE + hi_bytes[1] as usize),
                    *tables_ptr.add(10 * TABLE_SIZE + hi_bytes[2] as usize),
                    *tables_ptr.add(11 * TABLE_SIZE + hi_bytes[3] as usize),
                    *tables_ptr.add(12 * TABLE_SIZE + hi_bytes[4] as usize),
                    *tables_ptr.add(13 * TABLE_SIZE + hi_bytes[5] as usize),
                    *tables_ptr.add(14 * TABLE_SIZE + hi_bytes[6] as usize),
                    *tables_ptr.add(15 * TABLE_SIZE + hi_bytes[7] as usize),
                )
            };
            let p0 = l0 + l1;
            let p1 = l2 + l3;
            let p2 = l4 + l5;
            let p3 = l6 + l7;
            let p4 = h0 + h1;
            let p5 = h2 + h3;
            let p6 = h4 + h5;
            let p7 = h6 + h7;
            let q0 = p0 + p1;
            let q1 = p2 + p3;
            let q2 = p4 + p5;
            let q3 = p6 + p7;
            let r0 = q0 + q1;
            let r1 = q2 + q3;
            r0 + r1
        })
        .collect()
}

/// Tensor-split sibling of [`fold_b128_elems`]. Takes the two factors
/// `(eq_lo, eq_hi)` from [`build_eq_split`] instead of the materialized
/// suffix tensor. Each full entry `elem = eq_lo[i_lo] * eq_hi[i_hi]` is
/// reconstructed on the fly (one GF multiply per output position) and fed to
/// the same 16-byte-table lookup — the bit-decomposition the table indexes
/// does **not** factor through the `eq_lo`/`eq_hi` split, so the product must
/// be formed first.
///
/// Output order matches the materialized tensor: `out[i_hi·B + i_lo]` with
/// `B = eq_lo.len()`, so it is **byte-identical** to
/// `fold_b128_elems(build_eq_parallel(r), eq_r_dprime)` (field multiply is
/// exact, so `eq_lo[i_lo] * eq_hi[i_hi]` has the same bits as the
/// materialized entry).
/// Number of bytes in an `F128` (= lookup tables for the fold).
const FOLD_N_BYTES: usize = 16;
/// Entries per byte-lookup table.
const FOLD_TABLE_SIZE: usize = 256;

/// Build the 16×256 byte-lookup table the fold indexes: `table[k·256 + v]` =
/// `Σ_{bit b set in v} eq_r_dprime[k·8 + b]`. For the ring-switch fold,
/// `eq_r_dprime` already has γ_k baked in, so the table carries γ too.
fn build_fold_byte_table(eq_r_dprime: &[F128]) -> Vec<F128> {
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    let mut tables = vec![F128::ZERO; FOLD_N_BYTES * FOLD_TABLE_SIZE];
    for byte_idx in 0..FOLD_N_BYTES {
        let bit_base = byte_idx * 8;
        for value in 0..FOLD_TABLE_SIZE {
            let mut acc = F128::ZERO;
            for bit_in_byte in 0..8 {
                if (value >> bit_in_byte) & 1 == 1 {
                    acc += eq_r_dprime[bit_base + bit_in_byte];
                }
            }
            tables[byte_idx * FOLD_TABLE_SIZE + value] = acc;
        }
    }
    tables
}

/// One folded output slot: `Σ_{k=0..16} tables[k·256 + byte_k(elem)]`, where
/// `byte_k` are the 16 little-endian bytes of `elem`. `tables` MUST be a
/// `build_fold_byte_table` output (length `16·256`). Tree-reduced (depth 4)
/// rather than a length-15 XOR chain so the adds pipeline.
#[inline(always)]
pub(crate) fn fold_one_slot(elem: F128, tables: &[F128]) -> F128 {
    debug_assert_eq!(tables.len(), FOLD_N_BYTES * FOLD_TABLE_SIZE);
    let lo_bytes = elem.lo.to_le_bytes();
    let hi_bytes = elem.hi.to_le_bytes();
    let tables_ptr = tables.as_ptr();
    // SAFETY: byte values are u8 (0..256); the max offset is
    // `15·256 + 255 = 4095 = 16·256 − 1`, in-bounds for the asserted length.
    let (l0, l1, l2, l3, l4, l5, l6, l7, h0, h1, h2, h3, h4, h5, h6, h7) = unsafe {
        (
            *tables_ptr.add(lo_bytes[0] as usize),
            *tables_ptr.add(FOLD_TABLE_SIZE + lo_bytes[1] as usize),
            *tables_ptr.add(2 * FOLD_TABLE_SIZE + lo_bytes[2] as usize),
            *tables_ptr.add(3 * FOLD_TABLE_SIZE + lo_bytes[3] as usize),
            *tables_ptr.add(4 * FOLD_TABLE_SIZE + lo_bytes[4] as usize),
            *tables_ptr.add(5 * FOLD_TABLE_SIZE + lo_bytes[5] as usize),
            *tables_ptr.add(6 * FOLD_TABLE_SIZE + lo_bytes[6] as usize),
            *tables_ptr.add(7 * FOLD_TABLE_SIZE + lo_bytes[7] as usize),
            *tables_ptr.add(8 * FOLD_TABLE_SIZE + hi_bytes[0] as usize),
            *tables_ptr.add(9 * FOLD_TABLE_SIZE + hi_bytes[1] as usize),
            *tables_ptr.add(10 * FOLD_TABLE_SIZE + hi_bytes[2] as usize),
            *tables_ptr.add(11 * FOLD_TABLE_SIZE + hi_bytes[3] as usize),
            *tables_ptr.add(12 * FOLD_TABLE_SIZE + hi_bytes[4] as usize),
            *tables_ptr.add(13 * FOLD_TABLE_SIZE + hi_bytes[5] as usize),
            *tables_ptr.add(14 * FOLD_TABLE_SIZE + hi_bytes[6] as usize),
            *tables_ptr.add(15 * FOLD_TABLE_SIZE + hi_bytes[7] as usize),
        )
    };
    // Level 1: 8 pair sums.
    let p0 = l0 + l1;
    let p1 = l2 + l3;
    let p2 = l4 + l5;
    let p3 = l6 + l7;
    let p4 = h0 + h1;
    let p5 = h2 + h3;
    let p6 = h4 + h5;
    let p7 = h6 + h7;
    // Level 2.
    let q0 = p0 + p1;
    let q1 = p2 + p3;
    let q2 = p4 + p5;
    let q3 = p6 + p7;
    // Level 3.
    let r0 = q0 + q1;
    let r1 = q2 + q3;
    // Level 4.
    r0 + r1
}

/// Per-output-index value of a [`RsEqInd::DeferredDense`] fold (the value the
/// materialized `fold_b128_elems_split` would store at position `j`):
/// `fold_one_slot(eq_lo[j & (B−1)] · eq_hi[j >> log2 B], table)`, `B = eq_lo.len()`.
#[inline(always)]
pub(crate) fn deferred_dense_value(
    eq_lo: &[F128],
    eq_hi: &[F128],
    table: &[F128],
    log_b: usize,
    j: usize,
) -> F128 {
    let mask = (1usize << log_b) - 1;
    fold_one_slot(eq_lo[j & mask] * eq_hi[j >> log_b], table)
}

pub fn fold_b128_elems_split(eq_lo: &[F128], eq_hi: &[F128], eq_r_dprime: &[F128]) -> Vec<F128> {
    let tables = build_fold_byte_table(eq_r_dprime);
    fold_b128_from_table(eq_lo, eq_hi, &tables)
}

/// Materialize a split-tensor fold from a prebuilt byte `tables`
/// (`build_fold_byte_table` output). Block-parallel over `eq_hi`: each rayon
/// task sweeps one `e_hi` over all of `eq_lo` (so `e_hi` is hoisted once per
/// block). Used to un-defer a [`RsEqInd::DeferredDense`] in the pcs combine's
/// general (mixed/sparse/packed-direct) fallback path.
pub(crate) fn fold_b128_from_table(eq_lo: &[F128], eq_hi: &[F128], tables: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;
    let b = eq_lo.len();
    // Each slot is written exactly once (`*slot = acc`) before any read.
    let mut out = crate::scratch::take_f128(b * eq_hi.len());
    out.par_chunks_mut(b)
        .zip(eq_hi.par_iter())
        .for_each(|(out_block, &e_hi)| {
            for (i_lo, slot) in out_block.iter_mut().enumerate() {
                *slot = fold_one_slot(eq_lo[i_lo] * e_hi, tables);
            }
        });
    out
}

// ---------------------------------------------------------------------------
// Sparse-tensor fast path.
//
// When the suffix `x_outer[1..]` has `k` coords exactly equal to `F128::ZERO`
// (as is the case for the hash-chain ẑ-opening, whose `x_inner_rest` is padded
// with trailing zeros), `build_eq` zeros out half the table per zero coord —
// so `1 − 2^{-k}` of the suffix tensor is zero and contributes nothing to
// `s_hat_v` (in `fold_1b_rows`) or `rs_eq_ind` (in `fold_b128_elems`). The
// sparse kernels touch only the `2^{-k}` support and produce byte-identical
// outputs to the dense kernels.
//
// Claims with fewer than `SPARSE_ZERO_THRESHOLD` zero coords stay on the dense
// (MFR / 8-wide) path; the crossover threshold of 3 is conservative — at 3
// zeros the support is 1/8 of the suffix length, plenty to amortize the
// sparse fold's per-entry overhead.
// ---------------------------------------------------------------------------

/// Minimum number of exactly-zero suffix coords for a claim to be routed
/// through the sparse kernels instead of the dense MFR fold.
const SPARSE_ZERO_THRESHOLD: usize = 3;

/// Sparse representation of `build_eq(coords)` when `coords` contains exact
/// `F128::ZERO` entries: stores values at the compact (live) tensor positions
/// and a `live_positions` table that maps compact bit `j` → original coord
/// position. Avoids materializing the scattered `(full_idx, val)` pairs —
/// consumers compute the scattered idx on-the-fly via [`Self::scatter_idx`]
/// (a bit-deposit / pdep operation) at the point of use.
#[derive(Clone, Debug)]
pub struct SparseEqTensor {
    /// `build_eq(live_coords)` — length `2^live_positions.len()`.
    pub live_tensor: Vec<F128>,
    /// Original-coord positions of each live coord, ascending. So compact bit
    /// `j` of an enumeration index maps to bit `live_positions[j]` of the full
    /// scattered index.
    pub live_positions: Vec<usize>,
}

impl SparseEqTensor {
    /// Compact-to-scattered index translation: deposit the live bits of `c`
    /// into the original-coord positions. Inline so consumers' hot loops fuse
    /// this with their own per-entry work.
    ///
    /// (Tried backing this with per-byte 256-entry LUTs to reduce the
    /// 19-iteration loop to 3 LUT reads + ORs at chain scale. Measured wash
    /// on the keccak chain m=30 bench — LLVM auto-pipelines the iterative
    /// bit-deposit so aggressively that the per-entry scatter is already at
    /// the noise floor.)
    #[inline(always)]
    pub fn scatter_idx(&self, c: usize) -> usize {
        let mut full = 0usize;
        for (j, &pos) in self.live_positions.iter().enumerate() {
            full |= ((c >> j) & 1) << pos;
        }
        full
    }

    /// Materialize the scattered `(idx, val)` pairs. Test-oracle / external
    /// consumers that genuinely need the materialized form should call this;
    /// the prover hot path leaves the entries deferred via `scatter_idx`.
    pub fn materialize(&self) -> Vec<(usize, F128)> {
        self.live_tensor
            .iter()
            .enumerate()
            .map(|(c, &v)| (self.scatter_idx(c), v))
            .collect()
    }

    /// Number of scattered entries.
    pub fn len(&self) -> usize {
        self.live_tensor.len()
    }

    pub fn is_empty(&self) -> bool {
        self.live_tensor.is_empty()
    }
}

/// Build the sparse `build_eq(coords)` representation, skipping the zero-coord
/// halvings. The output's `live_tensor` is the `build_eq` table over only the
/// nonzero coords (length `2^live_count`); the scattered (full) index for
/// compact entry `c` is reconstructed lazily via [`SparseEqTensor::scatter_idx`].
///
/// O(2^live_count) time and memory, vs the dense `build_eq`'s `O(2^coords.len())`.
pub fn build_eq_sparse(coords: &[F128]) -> SparseEqTensor {
    let live_positions: Vec<usize> = coords
        .iter()
        .enumerate()
        .filter_map(|(i, &c)| if c == F128::ZERO { None } else { Some(i) })
        .collect();
    let live_coords: Vec<F128> = live_positions.iter().map(|&i| coords[i]).collect();
    // Sequential build_eq. `build_eq_parallel` *does* save ~0.4 ms on the build
    // itself at 19 live coords, but the downstream `fold_1b_rows_sparse` /
    // `fold_b128_elems_sparse_pairs` then pay cross-core L2/L3 traffic to
    // consume a tensor that was distributed across worker caches — net wash to
    // slight loss at the ring_switch level. Keep the tensor cache-local here.
    let live_tensor = build_eq(&live_coords);
    SparseEqTensor {
        live_tensor,
        live_positions,
    }
}

/// Sparse counterpart of one column of [`fold_1b_rows_multi`]: scans only the
/// nonzero entries of the suffix tensor. Iterates compact (live-only) tensor
/// indices and computes the scattered `packed_witness` index inline via
/// [`SparseEqTensor::scatter_idx`] — avoids materializing the scattered
/// `(idx, val)` pairs upfront.
///
/// Produces the same 128-entry `s_hat_v` as
/// `fold_1b_rows_naive(packed_witness, build_eq(coords))`, since `build_eq`'s
/// zero-coord halvings would otherwise contribute zero to every accumulator.
pub fn fold_1b_rows_sparse(packed_witness: &[F128], eq: &SparseEqTensor) -> Vec<F128> {
    // Tried: MFR fast path via `fold_1b_rows_sparse_mfr_block4` for the chain's
    // block-of-4 / stride-128 support pattern. **Measured a regression on
    // blake3 m=29** (~2.5 ms slower at chain proof level) and roughly break-
    // even on keccak. The subset-sum + transpose overhead doesn't amortize
    // over only 4 entries per group when packed_witness reads are scattered
    // (stride 128 = 2 KB jumps defeat the prefetcher). Kept the MFR helper +
    // detector in this module — they may be useful for future protocols with
    // a larger block_size (≥ 16) — but the dispatch is reverted to scalar.
    fold_1b_rows_sparse_scalar(packed_witness, eq)
}

/// Scalar bit-scan fallback for `fold_1b_rows_sparse`. One bit-scan per support
/// entry — used when the support's index pattern isn't a uniform stride-block.
fn fold_1b_rows_sparse_scalar(packed_witness: &[F128], eq: &SparseEqTensor) -> Vec<F128> {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING;
    let zero_acc = || vec![F128::ZERO; n];

    eq.live_tensor
        .par_iter()
        .enumerate()
        .fold(zero_acc, |mut acc, (c, &val)| {
            // Scatter compact c → original index via the per-byte LUT (inlined).
            let idx = eq.scatter_idx(c);
            let elem = packed_witness[idx];
            let mut lo = elem.lo;
            while lo != 0 {
                let r = lo.trailing_zeros() as usize;
                acc[r] += val;
                lo &= lo - 1;
            }
            let mut hi = elem.hi;
            while hi != 0 {
                let r = hi.trailing_zeros() as usize;
                acc[64 | r] += val;
                hi &= hi - 1;
            }
            acc
        })
        .reduce(zero_acc, |mut a, b| {
            for r in 0..n {
                a[r] += b[r];
            }
            a
        })
}

/// Detect the regular block-of-N + stride pattern in a sparse support. Returns
/// `Some((block_size, stride))` if `support` has indices `g * stride + k` for
/// `g ∈ 0..num_groups, k ∈ 0..block_size` (ascending). Returns `None` otherwise
/// or when the support is too small to detect meaningfully.
///
/// For the hash-chain claim (zeros at suffix positions `region_log−k_skip+1`
/// through `k_log−k_skip−1`), the pattern is `block_size = 2^low_live_count`
/// (low live bits below the zero run) and `stride = 2^(zero_run_end+1)`.
///
/// Currently unused — see comment in [`fold_1b_rows_sparse`] for the MFR
/// regression rationale. Kept for future protocols with larger block sizes.
#[allow(dead_code)]
fn detect_block_stride(support: &[(usize, F128)]) -> Option<(usize, usize)> {
    if support.len() < 8 {
        return None;
    }
    // Block runs from index 0; count the contiguous prefix.
    if support[0].0 != 0 {
        return None;
    }
    let mut block_size = 1usize;
    while block_size < support.len() && support[block_size].0 == block_size {
        block_size += 1;
    }
    if block_size >= support.len() || !support.len().is_multiple_of(block_size) {
        return None;
    }
    let stride = support[block_size].0;
    if stride < block_size || !stride.is_power_of_two() {
        return None;
    }
    // Validate every group has the same shape.
    let num_groups = support.len() / block_size;
    for g in 0..num_groups {
        let base = g * stride;
        for k in 0..block_size {
            if support[g * block_size + k].0 != base + k {
                return None;
            }
        }
    }
    Some((block_size, stride))
}

/// MFR sparse fold for `block_size = 4` + arbitrary power-of-two stride.
/// Equivalent output to [`fold_1b_rows_sparse_scalar`] but uses the same
/// subset-sum / transpose machinery as [`fold_1b_rows_1way_mfr`], skipping the
/// zero entries between groups. Throughput per group is identical to the dense
/// 4-wide MFR kernel.
///
/// Currently unused — measured slower than scalar bit-scan for the chain
/// claim's 4-entries-per-group pattern (subset-sum table overhead doesn't
/// amortize over only 4 entries when packed_witness reads are scattered).
/// Kept for reference / future protocols with larger block sizes.
#[allow(dead_code)]
fn fold_1b_rows_sparse_mfr_block4(
    packed_witness: &[F128],
    support: &[(usize, F128)],
    stride: usize,
) -> Vec<F128> {
    use rayon::prelude::*;
    let n = 1 << LOG_PACKING;
    debug_assert!(support.len().is_multiple_of(4));
    let num_groups = support.len() / 4;

    (0..num_groups)
        .into_par_iter()
        .fold(
            || vec![F128::ZERO; n],
            |mut acc, g| {
                let base = g * stride;
                let m0 = packed_witness[base];
                let m1 = packed_witness[base + 1];
                let m2 = packed_witness[base + 2];
                let m3 = packed_witness[base + 3];
                let v: [F128; 4] = [
                    support[g * 4].1,
                    support[g * 4 + 1].1,
                    support[g * 4 + 2].1,
                    support[g * 4 + 3].1,
                ];
                let lookup = subset_sums_4(v);

                let m_bytes: [[u8; 16]; 4] = [
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m0.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m0.hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m1.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m1.hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m2.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m2.hi.to_le_bytes());
                        b
                    },
                    {
                        let mut b = [0u8; 16];
                        b[..8].copy_from_slice(&m3.lo.to_le_bytes());
                        b[8..].copy_from_slice(&m3.hi.to_le_bytes());
                        b
                    },
                ];

                for r_byte in 0..16 {
                    let combined: u64 = (m_bytes[0][r_byte] as u64)
                        | ((m_bytes[1][r_byte] as u64) << 8)
                        | ((m_bytes[2][r_byte] as u64) << 16)
                        | ((m_bytes[3][r_byte] as u64) << 24);
                    let transposed = transpose_8x8_bits(combined);
                    let tb = transposed.to_le_bytes();
                    let b = r_byte * 8;
                    acc[b] += lookup[(tb[0] & 0x0F) as usize];
                    acc[b + 1] += lookup[(tb[1] & 0x0F) as usize];
                    acc[b + 2] += lookup[(tb[2] & 0x0F) as usize];
                    acc[b + 3] += lookup[(tb[3] & 0x0F) as usize];
                    acc[b + 4] += lookup[(tb[4] & 0x0F) as usize];
                    acc[b + 5] += lookup[(tb[5] & 0x0F) as usize];
                    acc[b + 6] += lookup[(tb[6] & 0x0F) as usize];
                    acc[b + 7] += lookup[(tb[7] & 0x0F) as usize];
                }
                acc
            },
        )
        .reduce(
            || vec![F128::ZERO; n],
            |mut a, b| {
                for r in 0..n {
                    a[r] += b[r];
                }
                a
            },
        )
}

/// Sparse counterpart of [`fold_b128_elems`] returning **sparse pairs** instead
/// of a dense vector — skips the O(L) zero-init / scatter entirely. Each pair
/// `(idx, value)` has the same per-element bit-scan over `eq_r_dprime` as the
/// dense kernel computed at that index; positions absent from the output are
/// implicitly `F128::ZERO`. Consumers must handle the sparse representation
/// (see [`RsEqInd::Sparse`]).
///
/// Iterates compact tensor positions and scatters the index inline only at
/// emission — avoids materializing the scattered `(idx, val)` pairs upfront.
pub fn fold_b128_elems_sparse_pairs(
    eq: &SparseEqTensor,
    eq_r_dprime: &[F128],
) -> Vec<(usize, F128)> {
    use rayon::prelude::*;
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    eq.live_tensor
        .par_iter()
        .enumerate()
        .map(|(c, &tensor_val)| {
            let mut acc = F128::ZERO;
            let mut lo = tensor_val.lo;
            while lo != 0 {
                let b = lo.trailing_zeros() as usize;
                acc += eq_r_dprime[b];
                lo &= lo - 1;
            }
            let mut hi = tensor_val.hi;
            while hi != 0 {
                let b = hi.trailing_zeros() as usize;
                acc += eq_r_dprime[64 | b];
                hi &= hi - 1;
            }
            // Scatter compact c → original index via per-byte LUT (inlined).
            (eq.scatter_idx(c), acc)
        })
        .collect()
}

/// Dense-output sparse fold — kept for tests/oracles. Returns a length-`len`
/// `Vec<F128>` that is zero outside the support. Prefer
/// [`fold_b128_elems_sparse_pairs`] in the prover hot path.
pub fn fold_b128_elems_sparse(len: usize, eq: &SparseEqTensor, eq_r_dprime: &[F128]) -> Vec<F128> {
    let pairs = fold_b128_elems_sparse_pairs(eq, eq_r_dprime);
    let mut out = vec![F128::ZERO; len];
    for (idx, val) in pairs {
        out[idx] = val;
    }
    out
}

// ---------------------------------------------------------------------------
// Prover / verifier of the ring-switching reduction.
// ---------------------------------------------------------------------------

/// The prover message: the 128 slice-MLEs at the suffix point.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RingSwitchProof {
    pub s_hat_v: Vec<F128>,
}

/// What both prover and verifier compute as a result of the reduction:
/// the transparent multilinear and the BaseFold sumcheck target.
#[derive(Clone, Debug)]
pub struct RingSwitchOutput {
    pub rs_eq_ind: Vec<F128>,
    pub sumcheck_claim: F128,
}

/// Per-claim output of [`prove_batched`]. Mirrors [`RingSwitchOutput`] but lets
/// the prover skip the dense `2^(m-7)` `rs_eq_ind` allocation for claims whose
/// suffix tensor is sparse (e.g. the hash-chain claim). Verifier-side
/// (`ring_switch::verify` + `pcs::verify_opening_batch`) still consumes the
/// dense [`RingSwitchOutput`].
#[derive(Clone, Debug)]
pub struct RingSwitchBatchOutput {
    /// For dense claims this is `γ_k · B_k` — γ is baked into the byte
    /// table during the fold inside `prove_batched_padded_with_precomputed`,
    /// so pcs's combine just adds it without per-slot γ-mul. For sparse
    /// claims `γ_k · entries` are baked similarly.
    pub rs_eq_ind: RsEqInd,
    pub sumcheck_claim: F128,
}

/// Sparse-or-dense representation of `rs_eq_ind`. All variants here have γ_k
/// pre-multiplied in (see `RingSwitchBatchOutput`).
#[derive(Clone, Debug)]
pub enum RsEqInd {
    Dense(Vec<F128>),
    /// Deferred dense: the `γ_k·B_k` buffer is **not** materialized. Instead the
    /// fold ingredients (`build_eq_split` factors + the γ-baked byte table) are
    /// carried so pcs's combine can fold each slot on the fly and accumulate it
    /// straight into `b_combined` — avoiding a 2^(m-7) materialize + readback
    /// per claim. `value(j) = deferred_dense_value(eq_lo, eq_hi, table, log2(B), j)`,
    /// `B = eq_lo.len()`; byte-identical to `Dense(fold_b128_elems_split(..))`.
    DeferredDense {
        eq_lo: Vec<F128>,
        eq_hi: Vec<F128>,
        table: Vec<F128>,
    },
    Sparse {
        len: usize,
        entries: Vec<(usize, F128)>,
    },
}

impl RsEqInd {
    /// Logical length of the underlying vector.
    pub fn len(&self) -> usize {
        match self {
            Self::Dense(v) => v.len(),
            Self::DeferredDense { eq_lo, eq_hi, .. } => eq_lo.len() * eq_hi.len(),
            Self::Sparse { len, .. } => *len,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Accumulate `gamma * self[j]` into `out[j]` for all `j`. Sparse variants
    /// touch only their support; dense variants iterate `out` in lockstep.
    pub fn add_scaled_into(&self, gamma: F128, out: &mut [F128]) {
        debug_assert_eq!(out.len(), self.len());
        match self {
            Self::Dense(v) => {
                for (o, &x) in out.iter_mut().zip(v.iter()) {
                    *o += gamma * x;
                }
            }
            Self::DeferredDense {
                eq_lo,
                eq_hi,
                table,
            } => {
                let log_b = eq_lo.len().trailing_zeros() as usize;
                for (j, o) in out.iter_mut().enumerate() {
                    *o += gamma * deferred_dense_value(eq_lo, eq_hi, table, log_b, j);
                }
            }
            Self::Sparse { entries, .. } => {
                for &(idx, val) in entries {
                    out[idx] += gamma * val;
                }
            }
        }
    }

    /// Materialize the dense view. O(L) regardless of variant; use sparingly.
    pub fn to_dense(&self) -> Vec<F128> {
        match self {
            Self::Dense(v) => v.clone(),
            Self::DeferredDense {
                eq_lo,
                eq_hi,
                table,
            } => {
                let log_b = eq_lo.len().trailing_zeros() as usize;
                let l = eq_lo.len() * eq_hi.len();
                (0..l)
                    .map(|j| deferred_dense_value(eq_lo, eq_hi, table, log_b, j))
                    .collect()
            }
            Self::Sparse { len, entries } => {
                let mut out = vec![F128::ZERO; *len];
                for &(idx, val) in entries {
                    out[idx] = val;
                }
                out
            }
        }
    }

    /// Consume into a dense `Vec<F128>`. Returns the inner vector directly when
    /// already `Dense` (no copy).
    pub fn into_dense(self) -> Vec<F128> {
        match self {
            Self::Dense(v) => v,
            Self::DeferredDense { .. } => self.to_dense(),
            Self::Sparse { len, entries } => {
                let mut out = vec![F128::ZERO; len];
                for (idx, val) in entries {
                    out[idx] = val;
                }
                out
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    ClaimMismatch,
}

/// Prover side of the ring-switching reduction.
///
/// Inputs:
/// - `packed_witness` (length `2^L`, L = m − 7), the F_{2^128}-packed witness.
/// - `x_outer` (length m − 6), the multilinear coords from the zerocheck.
/// - `challenger` for sampling row-batching `r''`.
///
/// Output: the proof message `s_hat_v` (128 F_{2^128} values to send) plus the
/// BaseFold inputs `(rs_eq_ind, sumcheck_claim)`.
pub fn prove<Ch: Challenger>(
    packed_witness: &[F128],
    x_outer: &[F128],
    challenger: &mut Ch,
) -> (RingSwitchProof, RingSwitchOutput) {
    assert!(
        !x_outer.is_empty(),
        "x_outer must contain at least 1 coord (the 7th-bit factor)"
    );
    let l = packed_witness.len();
    assert_eq!(l, 1 << (x_outer.len() - 1).saturating_add(0)); // sanity (placeholder)
    // Actually: packed_witness.len() = 2^L where L = m - 7. And x_outer.len() = m - 6.
    // So packed_witness.len() = 2^(x_outer.len() - 1). Enforce that.
    assert_eq!(l, 1 << (x_outer.len() - 1));

    let trace = std::env::var("PCS_TRACE").is_ok();

    challenger.observe_label(b"flock-ring-switch-v0");

    // Suffix is x_outer[1..] (length m-7); first coord becomes the 7th-bit factor.
    let suffix = &x_outer[1..];
    let t = std::time::Instant::now();
    let suffix_tensor = build_eq_parallel(suffix);
    if trace {
        eprintln!(
            "    [rs::prove] build_eq(suffix L={}): {:6.2} ms",
            suffix.len(),
            t.elapsed().as_secs_f64() * 1e3
        );
    }
    debug_assert_eq!(suffix_tensor.len(), l);

    // Compute and send s_hat_v.
    let t = std::time::Instant::now();
    let s_hat_v = fold_1b_rows_naive(packed_witness, &suffix_tensor);
    if trace {
        eprintln!(
            "    [rs::prove] fold_1b_rows:          {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
    }
    challenger.observe_f128_slice(&s_hat_v);

    // Sample row-batching r''.
    let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
    let eq_r_dprime = build_eq(&r_dprime);

    // Compute BaseFold target: T = ⟨transpose(s_hat_v), eq(r'')⟩.
    let s_hat_u = tensor_algebra_transpose(&s_hat_v);
    let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

    // Compute transparent multilinear rs_eq_ind.
    let t = std::time::Instant::now();
    let rs_eq_ind = fold_b128_elems(&suffix_tensor, &eq_r_dprime);
    if trace {
        eprintln!(
            "    [rs::prove] fold_b128_elems:       {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    (
        RingSwitchProof { s_hat_v },
        RingSwitchOutput {
            rs_eq_ind,
            sumcheck_claim,
        },
    )
}

/// Batched prover: produce ring-switching proofs for `x_outers.len()` opening
/// points in one pass. Shares a single fused `fold_1b_rows` bit-scan over
/// `packed_witness`. Challenger interaction is byte-identical to calling
/// [`prove`] sequentially for each `x_outer`.
pub fn prove_batched<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    challenger: &mut Ch,
) -> (Vec<(RingSwitchProof, RingSwitchBatchOutput)>, Vec<F128>) {
    let m = LOG_PACKING + (packed_witness.len().trailing_zeros() as usize);
    prove_batched_padded(packed_witness, x_outers, &PaddingSpec::dense(m), challenger)
}

/// Padding-aware variant of [`prove_batched`]. Threads `padding` into
/// `fold_1b_rows_multi_padded` so dense suffix folds skip chunks that fall
/// entirely in the per-block zero padding.
///
/// Returns `(results, gammas_rs)` — γ_rs is sampled internally after all
/// claims are observed (Schwartz-Zippel-sound), and is **baked into each
/// `RingSwitchBatchOutput::rs_eq_ind`** so the pcs combine doesn't need a
/// per-slot γ-mul. The returned `gammas_rs` is for pcs to compute the
/// γ-weighted `target_combined` (Σ γ_rs[k] · sumcheck_claim_k).
pub fn prove_batched_padded<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> (Vec<(RingSwitchProof, RingSwitchBatchOutput)>, Vec<F128>) {
    prove_batched_padded_with_precomputed(packed_witness, x_outers, &[], padding, challenger)
}

/// Variant of [`prove_batched_padded`] that accepts an optional precomputed
/// `s_hat_v` per claim. When `precomputed_s_hat_v[i] = Some(v)` for claim `i`,
/// the prover skips that claim's `fold_1b_rows` work and uses `v` directly as
/// `s_hat_v` for the per-opening tail (sumcheck_claim, rs_eq_ind, transcript
/// observe). The eq tensor (`eq_lo`/`eq_hi` or sparse support) is still built
/// because `fold_b128_elems_split` needs it for `rs_eq_ind`.
///
/// Use case: AB-claim opening when lincheck's pre-sumcheck `z_vec` is
/// available — see [`s_hat_v_from_z_vec`] and `prover::open_claims`.
///
/// `precomputed_s_hat_v` must be `&[]` (no precomputes) or have length equal
/// to `x_outers.len()`. Each precomputed slice must be length `2^LOG_PACKING`.
///
/// Output is **byte-identical** to [`prove_batched_padded`] when the precomputed
/// `s_hat_v` is honest (matches what `fold_1b_rows` would produce). Transcript
/// observes the same bytes in the same order.
pub fn prove_batched_padded_with_precomputed<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> (Vec<(RingSwitchProof, RingSwitchBatchOutput)>, Vec<F128>) {
    assert!(!x_outers.is_empty());
    let trace = std::env::var("PCS_TRACE").is_ok();
    let n = x_outers.len();
    let l = packed_witness.len();
    for x in x_outers {
        assert!(!x.is_empty());
        assert_eq!(l, 1 << (x.len() - 1));
    }
    assert!(
        precomputed_s_hat_v.is_empty() || precomputed_s_hat_v.len() == n,
        "precomputed_s_hat_v: must be empty or length {n}, got {}",
        precomputed_s_hat_v.len(),
    );
    let n_packed = 1usize << LOG_PACKING;
    for p in precomputed_s_hat_v.iter().flatten() {
        assert_eq!(
            p.len(),
            n_packed,
            "precomputed_s_hat_v entry must have length 2^LOG_PACKING"
        );
    }

    // Per-orig-claim "precomputed?" predicate. Empty precomputed slice → all
    // claims need fold (matches the existing behavior bit-for-bit).
    let has_precomputed =
        |orig: usize| -> bool { precomputed_s_hat_v.get(orig).copied().flatten().is_some() };

    // 1. Classify each claim. Claims whose suffix `x_outer[1..]` has at least
    //    `SPARSE_ZERO_THRESHOLD` exactly-zero coords (e.g. the hash-chain
    //    ẑ-claim) skip the dense kernels entirely; the rest fuse through the
    //    existing MFR/8-wide multi-fold. Pulling sparse claims out also
    //    restores k==2 (the MFR fast-path threshold in `fold_1b_rows_multi`)
    //    when there are exactly two dense claims — the common case.
    #[derive(Clone, Copy)]
    enum Kind {
        Dense(usize),
        Sparse(usize),
    }
    let mut kinds: Vec<Kind> = Vec::with_capacity(n);
    let mut dense_suffixes: Vec<&[F128]> = Vec::new();
    let mut sparse_suffixes: Vec<&[F128]> = Vec::new();
    // Map dense/sparse claim index back to the original `x_outers` index — used
    // to look up precomputed slots without recomputing the classification.
    let mut dense_to_orig: Vec<usize> = Vec::new();
    let mut sparse_to_orig: Vec<usize> = Vec::new();
    for (orig, x) in x_outers.iter().enumerate() {
        let suffix = &x[1..];
        let n_zeros = suffix.iter().filter(|&&c| c == F128::ZERO).count();
        if n_zeros >= SPARSE_ZERO_THRESHOLD {
            kinds.push(Kind::Sparse(sparse_suffixes.len()));
            sparse_to_orig.push(orig);
            sparse_suffixes.push(suffix);
        } else {
            kinds.push(Kind::Dense(dense_suffixes.len()));
            dense_to_orig.push(orig);
            dense_suffixes.push(suffix);
        }
    }

    // 2. Build suffix representations. Dense claims use the tensor-split
    //    factorization (two ~2^(n/2) factors instead of the full 2^n tensor)
    //    whenever `len` is a whole number of 16-wide MFR chunks — i.e. all
    //    real workloads. The split keeps `build_eq` off the critical path and
    //    lets the fold skip streaming the multi-MB tensor (see
    //    `fold_1b_rows_split`). Tiny test sizes (len not divisible by 16) fall
    //    back to the materialized tensor + the legacy multi-fold.
    let use_split = l.is_multiple_of(16);
    let t = std::time::Instant::now();
    let dense_splits: Vec<(Vec<F128>, Vec<F128>)> = if use_split {
        dense_suffixes
            .iter()
            .map(|s| build_eq_split(s, split_n_lo(s.len())))
            .collect()
    } else {
        Vec::new()
    };
    let dense_tensors: Vec<Vec<F128>> = if use_split {
        Vec::new()
    } else {
        dense_suffixes
            .iter()
            .map(|s| build_eq_parallel(s))
            .collect()
    };
    let sparse_supports: Vec<SparseEqTensor> =
        sparse_suffixes.iter().map(|s| build_eq_sparse(s)).collect();
    if trace {
        eprintln!(
            "    [rs::prove_batched] build_eq dense×{} ({}) + sparse×{}: {:6.2} ms",
            dense_suffixes.len(),
            if use_split { "split" } else { "full" },
            sparse_supports.len(),
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    // 3. fold_1b_rows: split inner-then-outer fold per dense claim (or the
    //    legacy fused MFR multi-fold for tiny non-split sizes); per-claim
    //    sparse scan for the rest.
    //
    //    Precomputed claims skip fold_1b_rows entirely — their s_hat_v is
    //    supplied by the caller. dense_s_hat_v/sparse_s_hat_v are still
    //    indexed by classify-time index `d` / `s`; we splice precomputed
    //    values in at those slots and run the kernel only on the others.
    let dense_needs_fold: Vec<usize> = (0..dense_suffixes.len())
        .filter(|&d| !has_precomputed(dense_to_orig[d]))
        .collect();
    let sparse_needs_fold: Vec<usize> = (0..sparse_suffixes.len())
        .filter(|&s| !has_precomputed(sparse_to_orig[s]))
        .collect();
    let t = std::time::Instant::now();
    let mut dense_s_hat_v: Vec<Vec<F128>> = vec![Vec::new(); dense_suffixes.len()];
    let mut sparse_s_hat_v: Vec<Vec<F128>> = vec![Vec::new(); sparse_suffixes.len()];
    // Fill precomputed slots first.
    for d in 0..dense_suffixes.len() {
        if let Some(p) = precomputed_s_hat_v.get(dense_to_orig[d]).copied().flatten() {
            dense_s_hat_v[d] = p.to_vec();
        }
    }
    for s in 0..sparse_suffixes.len() {
        if let Some(p) = precomputed_s_hat_v
            .get(sparse_to_orig[s])
            .copied()
            .flatten()
        {
            sparse_s_hat_v[s] = p.to_vec();
        }
    }
    // Run the kernel only on claims that genuinely need fold_1b_rows.
    if use_split {
        match dense_needs_fold.len() {
            0 => {}
            2 => {
                // K=2 specialization with stack-allocated inner accumulators —
                // one packed_witness streaming pass, shared transposes.
                let d0 = dense_needs_fold[0];
                let d1 = dense_needs_fold[1];
                let (lo0, hi0) = (dense_splits[d0].0.as_slice(), dense_splits[d0].1.as_slice());
                let (lo1, hi1) = (dense_splits[d1].0.as_slice(), dense_splits[d1].1.as_slice());
                let (a, b) = fold_1b_rows_split_2way(packed_witness, lo0, hi0, lo1, hi1, padding);
                dense_s_hat_v[d0] = a;
                dense_s_hat_v[d1] = b;
            }
            _ => {
                for &d in &dense_needs_fold {
                    let (eq_lo, eq_hi) = (&dense_splits[d].0, &dense_splits[d].1);
                    dense_s_hat_v[d] = fold_1b_rows_split(packed_witness, eq_lo, eq_hi, padding);
                }
            }
        }
    } else if !dense_needs_fold.is_empty() {
        let dense_refs: Vec<&[F128]> = dense_needs_fold
            .iter()
            .map(|&d| dense_tensors[d].as_slice())
            .collect();
        let out = fold_1b_rows_multi_padded(packed_witness, &dense_refs, padding);
        for (i, &d) in dense_needs_fold.iter().enumerate() {
            dense_s_hat_v[d] = out[i].clone();
        }
    }
    for &s in &sparse_needs_fold {
        sparse_s_hat_v[s] = fold_1b_rows_sparse(packed_witness, &sparse_supports[s]);
    }
    if trace {
        eprintln!(
            "    [rs::prove_batched] fold_1b_rows dense(k={})+sparse(k={}): {:6.2} ms",
            dense_s_hat_v.len(),
            sparse_s_hat_v.len(),
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    // 4. Per-opening tail. Two phases:
    //    (a) Per claim: observe(label, s_hat_v), sample r''_i, compute
    //        sumcheck_claim. Stash factors needed for fold.
    //    (b) Sample γ_rs after all observations (Schwartz-Zippel-sound).
    //    (c) Per claim: bake γ_k into eq_r_dprime, fold. Output rs_eq_ind
    //        already has γ_k baked in — pcs combine just adds.
    let t = std::time::Instant::now();

    struct ClaimWork {
        s_hat_v: Vec<F128>,
        sumcheck_claim: F128,
        eq_r_dprime: Vec<F128>,
    }
    let mut work: Vec<ClaimWork> = Vec::with_capacity(n);
    for i in 0..n {
        challenger.observe_label(b"flock-ring-switch-v0");
        let s_hat_v: Vec<F128> = match kinds[i] {
            Kind::Dense(d) => dense_s_hat_v[d].clone(),
            Kind::Sparse(s) => sparse_s_hat_v[s].clone(),
        };
        challenger.observe_f128_slice(&s_hat_v);
        let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
        let eq_r_dprime = build_eq(&r_dprime);

        let s_hat_u = tensor_algebra_transpose(&s_hat_v);
        let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

        work.push(ClaimWork {
            s_hat_v,
            sumcheck_claim,
            eq_r_dprime,
        });
    }

    // γ_rs sampled after all RS observations — sound. Each γ_rs[k] is then
    // baked into eq_r_dprime[k] before building the Φ byte table, so the
    // fold output is γ_k · B_k directly. pcs combine just adds.
    let gammas_rs: Vec<F128> = (0..n).map(|_| challenger.sample_f128()).collect();

    let results: Vec<(RingSwitchProof, RingSwitchBatchOutput)> = work
        .into_iter()
        .zip(gammas_rs.iter())
        .enumerate()
        .map(|(i, (w, &g))| {
            let scaled_eq_r_dprime: Vec<F128> = w.eq_r_dprime.iter().map(|x| g * *x).collect();
            let rs_eq_ind = match kinds[i] {
                Kind::Dense(d) => {
                    if use_split {
                        // Defer the fold: carry the split factors + γ-baked byte
                        // table so pcs's combine folds each slot directly into
                        // `b_combined` (no 2^(m-7) materialize + readback). The
                        // table build is the only work done here (16·256 adds).
                        let (eq_lo, eq_hi) = &dense_splits[d];
                        RsEqInd::DeferredDense {
                            eq_lo: eq_lo.clone(),
                            eq_hi: eq_hi.clone(),
                            table: build_fold_byte_table(&scaled_eq_r_dprime),
                        }
                    } else {
                        RsEqInd::Dense(fold_b128_elems(&dense_tensors[d], &scaled_eq_r_dprime))
                    }
                }
                Kind::Sparse(s) => RsEqInd::Sparse {
                    len: l,
                    entries: fold_b128_elems_sparse_pairs(&sparse_supports[s], &scaled_eq_r_dprime),
                },
            };
            (
                RingSwitchProof { s_hat_v: w.s_hat_v },
                RingSwitchBatchOutput {
                    rs_eq_ind,
                    sumcheck_claim: w.sumcheck_claim,
                },
            )
        })
        .collect();

    if trace {
        eprintln!(
            "    [rs::prove_batched] per-opening tail ×{}: {:6.2} ms",
            n,
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    (results, gammas_rs)
}

/// Verifier side of the ring-switching reduction.
///
/// Inputs:
/// - `claim`: the zerocheck's claim value `ẑ_skip(z_skip, x_outer)`.
/// - `z_skip` ∈ F_{2^128}: the univariate-skip coord.
/// - `x_outer` (length m − 6): the multilinear coords.
/// - `proof`: the prover's `s_hat_v` message.
/// - `challenger` for sampling `r''` in lockstep with the prover.
///
/// Output: the matching BaseFold inputs `(rs_eq_ind, sumcheck_claim)`, or a
/// `ClaimMismatch` error if `weights · s_hat_v ≠ claim`.
pub fn verify<Ch: Challenger>(
    claim: F128,
    z_skip: F128,
    x_outer: &[F128],
    proof: &RingSwitchProof,
    challenger: &mut Ch,
) -> Result<RingSwitchOutput, VerifyError> {
    assert!(!x_outer.is_empty());
    let l = 1usize << (x_outer.len() - 1);
    assert_eq!(proof.s_hat_v.len(), 1 << LOG_PACKING);

    challenger.observe_label(b"flock-ring-switch-v0");

    // Verifier observes s_hat_v.
    challenger.observe_f128_slice(&proof.s_hat_v);

    // Check the claim against ν_φ8 ⊗ eq weights.
    let weights = build_claim_weights(z_skip, x_outer[0]);
    if claim_check(&weights, &proof.s_hat_v) != claim {
        return Err(VerifyError::ClaimMismatch);
    }

    // Sample r''.
    let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
    let eq_r_dprime = build_eq(&r_dprime);

    // Compute BaseFold target.
    let s_hat_u = tensor_algebra_transpose(&proof.s_hat_v);
    let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

    // Compute rs_eq_ind (verifier needs it to check BaseFold; reconstructs it
    // from x_outer and r''). The suffix tensor is rebuilt from x_outer[1..].
    let suffix = &x_outer[1..];
    let suffix_tensor = build_eq(suffix);
    debug_assert_eq!(suffix_tensor.len(), l);
    let rs_eq_ind = fold_b128_elems(&suffix_tensor, &eq_r_dprime);

    Ok(RingSwitchOutput {
        rs_eq_ind,
        sumcheck_claim,
    })
}

/// Verifier-side output of [`verify_succinct`]: contains everything the caller
/// needs to drive the BaseFold consistency check, *without* materializing the
/// dense `rs_eq_ind` vector of length `2^(m-7)`.
#[derive(Clone, Debug)]
pub struct RingSwitchVerifierOutput {
    pub sumcheck_claim: F128,
    /// `eq` tensor of length `2^LOG_PACKING = 128` derived from the verifier's
    /// sampled `r''`. Used by [`eval_rs_eq`] at the BaseFold final point.
    pub eq_r_dprime: Vec<F128>,
}

/// Polylog-cost ring-switching verifier.
///
/// Same FS interface as [`verify`] but **does not** build the dense
/// `rs_eq_ind` vector. Pair with [`eval_rs_eq`] at the BaseFold final point to
/// evaluate `MLE(rs_eq_ind)(challenges)` in `O((m − 7) · 128²)` field ops
/// instead of `O(2^(m−7))`.
pub fn verify_succinct<Ch: Challenger>(
    claim: F128,
    z_skip: F128,
    x_outer: &[F128],
    proof: &RingSwitchProof,
    challenger: &mut Ch,
) -> Result<RingSwitchVerifierOutput, VerifyError> {
    assert!(!x_outer.is_empty());
    assert_eq!(proof.s_hat_v.len(), 1 << LOG_PACKING);

    challenger.observe_label(b"flock-ring-switch-v0");
    challenger.observe_f128_slice(&proof.s_hat_v);

    let weights = build_claim_weights(z_skip, x_outer[0]);
    if claim_check(&weights, &proof.s_hat_v) != claim {
        return Err(VerifyError::ClaimMismatch);
    }

    let r_dprime = challenger.sample_f128_vec(LOG_PACKING);
    let eq_r_dprime = build_eq(&r_dprime);

    let s_hat_u = tensor_algebra_transpose(&proof.s_hat_v);
    let sumcheck_claim = inner_product(&s_hat_u, &eq_r_dprime);

    Ok(RingSwitchVerifierOutput {
        sumcheck_claim,
        eq_r_dprime,
    })
}

/// Polylog-cost evaluation of `MLE(rs_eq_ind)(query)` at the BaseFold final
/// challenge point, following [DP24] §1.3 Figure 3.
///
/// The dense alternative — `mle_eval(&fold_b128_elems(build_eq(z_vals),
/// eq_r_dprime), query)` — costs `O(2^|z_vals|)` field operations. This
/// function costs `O(|z_vals| · 2^{2·LOG_PACKING}) = O(|z_vals| · 16384)`
/// field operations: a length-128 `TensorAlgebra` element is iteratively
/// updated by `scale_vertical` / `scale_horizontal` over `|z_vals|`
/// iterations, then folded against `eq_r_dprime` (length 128).
///
/// Ports binius64's `crates/verifier/src/ring_switch.rs::eval_rs_eq`.
///
/// ## Arguments
///
/// * `z_vals` — the suffix-side coords, i.e. `x_outer[1..]` from
///   [`verify_succinct`]. Length `ℓ' = m − 7`.
/// * `query` — the BaseFold sumcheck final challenges, length `ℓ'`.
/// * `eq_r_dprime` — the `eq` tensor over the sampled `r''`, length 128.
///
/// [DP24]: <https://eprint.iacr.org/2024/504>
pub fn eval_rs_eq(z_vals: &[F128], query: &[F128], eq_r_dprime: &[F128]) -> F128 {
    use crate::pcs::tensor_algebra::TensorAlgebra;

    assert_eq!(
        z_vals.len(),
        query.len(),
        "eval_rs_eq: z_vals and query must have equal length"
    );
    assert_eq!(
        eq_r_dprime.len(),
        1 << LOG_PACKING,
        "eval_rs_eq: eq_r_dprime length must be 128"
    );

    let mut eval = TensorAlgebra::from_vertical(F128::ONE);
    for (&z_i, &q_i) in z_vals.iter().zip(query.iter()) {
        // In characteristic 2: eq(z, q) = 1 + z + q + 2·z·q = 1 + z + q.
        // So updating eval ← eval + z·eval + q·eval (with vertical = z-axis,
        // horizontal = q-axis) yields the correct per-step eq tensor update.
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval.fold_vertical(eq_r_dprime)
}

/// **Prefix-only** variant of [`eval_rs_eq`]: walks `prefix_len` of the
/// (z_vals, query) pairs and returns the partially-evolved `TensorAlgebra`.
/// Pair with [`eval_rs_eq_finish_from_prefix`] to share the prefix across
/// many query points (e.g. residual `y_bits` positions).
pub fn eval_rs_eq_prefix(
    z_vals: &[F128],
    query_prefix: &[F128],
) -> crate::pcs::tensor_algebra::TensorAlgebra {
    use crate::pcs::tensor_algebra::TensorAlgebra;
    assert!(query_prefix.len() <= z_vals.len());
    let mut eval = TensorAlgebra::from_vertical(F128::ONE);
    for (&z_i, &q_i) in z_vals.iter().zip(query_prefix.iter()) {
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval
}

/// Finish [`eval_rs_eq`] given a precomputed prefix tensor + the remaining
/// (z, query) suffix. `z_vals_suffix` and `query_suffix` are the parts of
/// the original `z_vals`/`query` past the prefix length.
pub fn eval_rs_eq_finish_from_prefix(
    prefix: &crate::pcs::tensor_algebra::TensorAlgebra,
    z_vals_suffix: &[F128],
    query_suffix: &[F128],
    eq_r_dprime: &[F128],
) -> F128 {
    assert_eq!(z_vals_suffix.len(), query_suffix.len());
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    let mut eval = prefix.clone();
    for (&z_i, &q_i) in z_vals_suffix.iter().zip(query_suffix.iter()) {
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval.fold_vertical(eq_r_dprime)
}

/// Specialized variant of [`eval_rs_eq_finish_from_prefix`] for the case where
/// `query_suffix` is known to be **binary** (each coord is `F128::ZERO` or
/// `F128::ONE`). Used by Ligerito's succinct verifier where the suffix is the
/// bit-decomposition of a residual position `y`.
///
/// When `q_i ∈ {0, 1}`, the general recurrence
/// `new_eval = eval + z·eval + q·eval` collapses (in char 2) to:
/// - `q_i = 0`: `new_eval = (1 + z_i) · eval`
/// - `q_i = 1`: `new_eval = z_i · eval`
///
/// Both reduce to a single in-place `scale_vertical`, eliminating all the
/// per-step clones, transposes, and additions of the general path. Each suffix
/// step becomes one 128-mult instead of ~8 passes.
///
/// `y_bits` encodes the suffix as a bitmask: bit `j` is the j-th suffix coord.
pub fn eval_rs_eq_finish_from_prefix_binary_q(
    prefix: &crate::pcs::tensor_algebra::TensorAlgebra,
    z_vals_suffix: &[F128],
    y_bits: u32,
    eq_r_dprime: &[F128],
) -> F128 {
    assert_eq!(eq_r_dprime.len(), 1 << LOG_PACKING);
    debug_assert!(
        z_vals_suffix.len() <= 32,
        "y_bits is u32; suffix > 32 not supported"
    );
    let mut eval = prefix.clone();
    for (j, &z_i) in z_vals_suffix.iter().enumerate() {
        let scalar = if (y_bits >> j) & 1 == 1 {
            z_i
        } else {
            F128::ONE + z_i
        };
        for e in eval.elems.iter_mut() {
            *e *= scalar;
        }
    }
    eval.fold_vertical(eq_r_dprime)
}