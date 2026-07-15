// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The DP24 iterative `eval_rs_eq_k` is ported from binius64. The module is
// the rectangular (f = 64, e = 192) generalization described in
// the ring-switching-generalized note.

//! Ring-switching reduction for the 64-bit transition: F_2 to K = GF(2^64)
//! packing, opened over E = GF(2^192) (the tower [`F192`]).
//!
//! With f = 64 (packing degree over F_2) and e = 192 (opening degree), this
//! converts one evaluation claim on
//! the bit-witness MLE at an E-point into a Ligerito-K sumcheck claim on the
//! packed multilinear (a `Vec<F64>`, one word per 64 bits, see
//! [`super::pack_k`]) against a transparent E-valued weight vector
//! `rs_eq_ind`.
//!
//! ## Rectangular shape
//!
//! - **Rectangular shape**: `s_hat_v` has 64 entries (one per packing bit),
//!   each an E element; its tensor-algebra transpose `s_hat_u = (t_i)` has
//!   192 K-entries. One challenge `rho in E` batches them with the univariate
//!   weights `(1, rho, ..., rho^191)`. This uses all coordinates directly,
//!   without padding them to a 256-entry Boolean cube.
//! - **No "7 = 6 + 1" prefix split**: with 64-bit packing the packed prefix
//!   is exactly the 6-bit skip domain, and the old 7th bit is an ordinary
//!   suffix coordinate of the packed witness (which has `2^(m-6)` words).
//! - **Generalized prefix weights**: the consumed claim is
//!   `claim == sum_{i in 0..64} prefix_weights[i] * s_hat_v[i]`. For a plain
//!   multilinear point claim the weights are the eq tensor of the 6 prefix
//!   coords ([`eq_prefix_weights`]); for flock's univariate-skip claim (whose
//!   first coordinate ranges over the phi_8 Lagrange domain, not the boolean
//!   cube) the caller passes the 64 phi_8 Lagrange weights
//!   `lagrange_weights_naive(6, z_skip)`.
//!   This module never looks inside the weights, so flock's `z_skip` flows
//!   through unchanged.
//!
//! ## Protocol (prover)
//!
//! 1. Send `s_hat_v[i] = sum_y eq(r_suffix, y) * bit_i(packed[y])`, the MLE
//!    of the i-th bit-slice at the suffix point (i in 0..64, values in E).
//! 2. Verifier checks `claim == sum_i prefix_weights[i] * s_hat_v[i]`.
//! 3. Sample `rho in E`; define `coord_weights[i] = rho^i`. Transpose
//!    `s_hat_v` to `t_i = s_hat_u[i] in K` (see
//!    [`super::tensor_algebra_k::transpose_s_hat`]); the batched target is
//!    `sumcheck_claim = sum_i rho^i * t_i` (K x E via `mul_base`).
//! 4. Both sides define the transparent weights
//!    `rs_eq_ind[y] = Phi(eq(r_suffix, y))` where `Phi : E -> E` is the
//!    F_2-linear map sending basis coordinate `i` to `rho^i`. Completeness:
//!    `sum_y rs_eq_ind[y] * packed[y] == sumcheck_claim`, which is exactly
//!    the claim shape [`super::ligerito_k::recursive_prover_with_basis_k`]
//!    proves (with `b_initial = rs_eq_ind`, `target = sumcheck_claim`).
//!    Soundness follows because any nonzero discrepancy gives a nonzero
//!    polynomial in `rho` of degree at most 191.
//!
//! ## Prover vs. verifier paths for `rs_eq_ind`
//!
//! - [`prove`] / [`verify`] materialize `rs_eq_ind` densely via
//!   [`fold_ext_elems`] (bytewise-table fold, rayon), `2^(m-6)` E entries.
//! - [`verify_succinct`] + [`eval_rs_eq_k`] never materialize it: the MLE of
//!   `rs_eq_ind` at the Ligerito final point is evaluated in
//!   `O((m-6) * 192^2)` bit-ops plus `O((m-6) * 192)` E-multiplications via
//!   the DP24 tensor-algebra iterative algorithm (DP24 section 1.3 Figure 3).
//!
//! [DP24]: <https://eprint.iacr.org/2024/504>

use fiat_shamir::Sponge;
use primitives::bits::transpose_8x8_bits;
use primitives::field::{F64, F192};
use serde::{Deserialize, Serialize};

use super::ligerito_k::{build_eq_table_ext, inner_product_base_ext};
use super::pack_k::{LOG_PACKING_K, PACKING_WIDTH_K};
use super::tensor_algebra_k::{DEGREE_E, TensorAlgebraE, transpose_s_hat};

/// Maximum degree of a nonzero ring-switch discrepancy in the univariate
/// batching challenge. This is a soundness parameter, not merely an
/// implementation detail.
pub const RING_SWITCH_SOUNDNESS_DEGREE: usize = DEGREE_E - 1;

/// Build `(1, rho, ..., rho^191)`, in the coordinate order produced by
/// [`transpose_s_hat`].
pub fn build_coordinate_weights(rho: F192) -> Vec<F192> {
    let mut power = F192::ONE;
    let mut weights = Vec::with_capacity(DEGREE_E);
    weights.push(power);
    for _ in 1..DEGREE_E {
        power *= rho;
        weights.push(power);
    }
    weights
}

// ---------------------------------------------------------------------------
// Sponge helpers: every 24-byte pattern is a valid F192.
// ---------------------------------------------------------------------------

fn observe_ext_slice(sponge: &mut Sponge, values: &[F192]) {
    for &e in values {
        sponge.observe(e);
    }
}

// ---------------------------------------------------------------------------
// Building blocks
// ---------------------------------------------------------------------------

/// Prefix weights for a plain multilinear point claim: the eq tensor of the
/// 6 intra-word coordinates,
/// `weights[i] = prod_j (bit_j(i) ? r_prefix[j] : 1 + r_prefix[j])`.
///
/// The prefix here is a plain boolean 6-cube (the bit index inside a K
/// word), so plain eq weights are correct; the old module needed phi_8
/// Lagrange weights only because its prefix was the univariate-skip domain.
pub fn eq_prefix_weights(r_prefix: &[F192]) -> Vec<F192> {
    assert_eq!(
        r_prefix.len(),
        LOG_PACKING_K,
        "eq_prefix_weights: prefix must have LOG_PACKING_K = 6 coords"
    );
    build_eq_table_ext(r_prefix)
}

/// Standard inner product `sum_i a[i] * b[i]` over E.
pub fn inner_product_ext(a: &[F192], b: &[F192]) -> F192 {
    assert_eq!(a.len(), b.len());
    let mut acc = F192::ZERO;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc += x * y;
    }
    acc
}

/// The verifier's claim check: `sum_i prefix_weights[i] * s_hat_v[i]`.
pub fn claim_check(prefix_weights: &[F192], s_hat_v: &[F192]) -> F192 {
    inner_product_ext(prefix_weights, s_hat_v)
}

/// Tower (`F192`) trace-dual basis: `TRACE_DUAL_BASIS[i]` is the unique element
/// with `bit_i(y) = Tr(TRACE_DUAL_BASIS[i] · y)` for the coordinate bit `i` of
/// `y ∈ F192` (c0 bits 0..64, c1 bits 64..128, c2 bits 128..192), where `Tr` is the absolute
/// trace `F192 → F2`, using the tower's coordinate basis and trace form.
/// The recursion guest replays bit extraction with these.
pub fn trace_dual_basis_k() -> &'static [F192; 192] {
    use std::sync::OnceLock;
    static DUAL: OnceLock<[F192; 192]> = OnceLock::new();
    DUAL.get_or_init(|| {
        let basis = |j: usize| {
            if j < 64 {
                F192::new(1u64 << j, 0, 0)
            } else if j < 128 {
                F192::new(0, 1u64 << (j - 64), 0)
            } else {
                F192::new(0, 0, 1u64 << (j - 128))
            }
        };
        // Absolute trace to F2: Tr(x) = Σ_{k=0}^{191} x^{2^k}.
        let tr = |x: F192| {
            let (mut acc, mut p) = (F192::ZERO, x);
            for _ in 0..192 {
                acc += p;
                p = p.square();
            }
            acc
        };
        // Invert the 192x192 trace Gram matrix over F2. This runs once and is
        // deliberately simple; protocol hot paths only read the cached basis.
        let mut aug = vec![vec![0u8; 2 * DEGREE_E]; DEGREE_E];
        for i in 0..DEGREE_E {
            for j in 0..DEGREE_E {
                if tr(basis(i) * basis(j)) == F192::ONE {
                    aug[i][j] = 1;
                }
            }
            aug[i][DEGREE_E + i] = 1;
        }
        for col in 0..DEGREE_E {
            let piv = (col..DEGREE_E)
                .find(|&r| aug[r][col] == 1)
                .expect("trace Gram matrix is invertible");
            aug.swap(col, piv);
            for r in 0..DEGREE_E {
                if r != col && aug[r][col] == 1 {
                    for j in col..2 * DEGREE_E {
                        aug[r][j] ^= aug[col][j];
                    }
                }
            }
        }
        let mut out = [F192::ZERO; 192];
        for (i, o) in out.iter_mut().enumerate() {
            for j in 0..DEGREE_E {
                if aug[i][DEGREE_E + j] == 1 {
                    *o += basis(j);
                }
            }
        }
        out
    })
}

/// Compute the slice-MLE vector `s_hat_v` (length 64) from a packed witness
/// and a tensor-expanded suffix point.
///
/// `packed_witness[y] in K` for `y in 0..2^L`; `suffix_tensor` is
/// `eq(r_suffix, .)` over the same range (from
/// [`build_eq_table_ext`]).
///
/// Output: `s_hat_v[i] = sum_y bit_i(packed_witness[y]) * suffix_tensor[y]`
/// for `i in 0..64` (bit i = polynomial-basis coordinate of the u64).
///
/// Dispatch: the method-of-four-Russians kernel
/// ([`fold_1b_rows_k_mfr_8wide`]) for lengths divisible by 8 (any real
/// witness), the scalar bit-scan otherwise (tiny test instances). Both
/// compute the same per-bit XOR-sums, only regrouped, and GF(2^192)
/// addition is XOR (commutative, associative, exact), so the output and
/// hence the transcript are byte-identical either way.
pub fn fold_1b_rows_k(packed_witness: &[F64], suffix_tensor: &[F192]) -> Vec<F192> {
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    if !packed_witness.is_empty() && packed_witness.len().is_multiple_of(8) {
        fold_1b_rows_k_mfr_8wide(packed_witness, suffix_tensor)
    } else {
        fold_1b_rows_k_scalar(packed_witness, suffix_tensor)
    }
}

/// Reuse lincheck's partial fold to derive the 64 slice evaluations needed by
/// the K ring switch, avoiding a second pass over the packed witness.
pub fn s_hat_v_from_z_vec(z_vec: &[F192], inner_rest_tail: &[F192]) -> Vec<F192> {
    use rayon::prelude::*;
    let n_packed = PACKING_WIDTH_K;
    let n_tail = 1usize << inner_rest_tail.len();
    assert_eq!(z_vec.len(), n_packed * n_tail);
    if inner_rest_tail.is_empty() {
        return z_vec.to_vec();
    }
    build_eq_table_ext(inner_rest_tail)
        .par_iter()
        .enumerate()
        .fold(
            || vec![F192::ZERO; n_packed],
            |mut acc, (k, &weight)| {
                for (slot, &value) in acc.iter_mut().zip(&z_vec[k * n_packed..(k + 1) * n_packed]) {
                    *slot += weight * value;
                }
                acc
            },
        )
        .reduce(
            || vec![F192::ZERO; n_packed],
            |mut acc, part| {
                for (slot, value) in acc.iter_mut().zip(part) {
                    *slot += value;
                }
                acc
            },
        )
}

/// Scalar reference path of [`fold_1b_rows_k`]: mirror of
/// `ring_switch::fold_1b_rows_naive` at 64-bit width, a rayon bit-scan with
/// per-thread length-64 partial accumulators XOR-reduced at the end.
/// Data-dependent cost: `trailing_zeros` + RMW + branch per set bit
/// (~32/word on a random witness).
fn fold_1b_rows_k_scalar(packed_witness: &[F64], suffix_tensor: &[F192]) -> Vec<F192> {
    use rayon::prelude::*;
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    let n = PACKING_WIDTH_K;
    let zero_acc = || vec![F192::ZERO; n];

    packed_witness
        .par_iter()
        .zip(suffix_tensor.par_iter())
        .fold(zero_acc, |mut acc, (elem, &w)| {
            let mut bits = elem.0;
            while bits != 0 {
                let r = bits.trailing_zeros() as usize;
                acc[r] += w;
                bits &= bits - 1;
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

/// Build the 16-entry subset-sum lookup table over 4 E elements:
/// `sums[mask] = sum_{k in 0..4 : bit_k(mask) = 1} elems[k]`. 15 additions
/// via the standard doubling pattern (mirror of
/// `ring_switch::subset_sums_4` retyped to the tower).
#[inline(always)]
fn subset_sums_4_ext(elems: [F192; 4]) -> [F192; 16] {
    let mut sums = [F192::ZERO; 16];
    for (i, &e) in elems.iter().enumerate() {
        let half = 1 << i;
        for k in 0..half {
            sums[half + k] = sums[k] + e;
        }
    }
    sums
}

/// Method-of-four-Russians [`fold_1b_rows_k`] kernel: the extension-field layer's
/// `fold_1b_rows_1way_mfr_8wide_k4` ported to 8-byte K words (where 8 words
/// per transpose group cover ALL 64 output bits with the 8 byte positions,
/// no wasted transpose rows).
///
/// Per group of 8 words: build two 16-entry subset-sum tables over the 8
/// suffix weights (low nibble = words 0..4, high = words 4..8, 30 adds
/// total); then for each byte position `r_byte` gather that byte of all 8
/// words into a u64 (word `e` in byte slot `e`) and 8x8 bit-transpose it,
/// so transposed byte `p`, bit `e` is bit `r_byte*8 + p` of word `e`: an
/// 8-bit mask over the group for output position `r = r_byte*8 + p`. Each
/// output position then costs two table lookups + one in-register add + one
/// accumulator RMW, regardless of bit density: a constant ~12 adds + 8 RMWs
/// per word vs the scalar path's ~32 data-dependent conditional adds.
/// Per-thread accumulators via rayon fold/reduce (no shared cache lines).
fn fold_1b_rows_k_mfr_8wide(packed_witness: &[F64], suffix_tensor: &[F192]) -> Vec<F192> {
    use rayon::prelude::*;
    let n = PACKING_WIDTH_K;
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    assert!(packed_witness.len().is_multiple_of(8));
    let zero_acc = || vec![F192::ZERO; n];

    packed_witness
        .par_chunks(8)
        .zip(suffix_tensor.par_chunks(8))
        .fold(zero_acc, |mut acc, (m_chunk, t_chunk)| {
            let lo_tbl = subset_sums_4_ext([t_chunk[0], t_chunk[1], t_chunk[2], t_chunk[3]]);
            let hi_tbl = subset_sums_4_ext([t_chunk[4], t_chunk[5], t_chunk[6], t_chunk[7]]);

            let mut m_bytes = [[0u8; 8]; 8];
            for (e, slot) in m_bytes.iter_mut().enumerate() {
                *slot = m_chunk[e].0.to_le_bytes();
            }

            for r_byte in 0..8 {
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
                for (p, &mask) in tb.iter().enumerate() {
                    acc[base + p] += lo_tbl[(mask & 0x0F) as usize] + hi_tbl[(mask >> 4) as usize];
                }
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

/// Compute `rs_eq_ind`, the transparent E-valued weight vector over the
/// suffix domain: `rs_eq_ind[y] = Phi(suffix_tensor[y])` where `Phi` sends
/// E-basis bit w to `coordinate_weights[w]`, i.e.
///
/// `rs_eq_ind[y] = sum_w bit_w(suffix_tensor[y]) * coordinate_weights[w]`
///
/// Naive reference: rayon per-position bit-scan over the three 64-bit limbs.
/// See [`fold_ext_elems`] for the bytewise-table production version.
pub fn fold_ext_elems_naive(suffix_tensor: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
    use rayon::prelude::*;
    assert_eq!(coordinate_weights.len(), DEGREE_E);
    suffix_tensor
        .par_iter()
        .map(|&elem| {
            let mut acc = F192::ZERO;
            let mut c0 = elem.c0;
            while c0 != 0 {
                let w = c0.trailing_zeros() as usize;
                acc += coordinate_weights[w];
                c0 &= c0 - 1;
            }
            let mut c1 = elem.c1;
            while c1 != 0 {
                let w = c1.trailing_zeros() as usize;
                acc += coordinate_weights[64 | w];
                c1 &= c1 - 1;
            }
            let mut c2 = elem.c2;
            while c2 != 0 {
                let w = c2.trailing_zeros() as usize;
                acc += coordinate_weights[128 | w];
                c2 &= c2 - 1;
            }
            acc
        })
        .collect()
}

/// Number of bytes in an E element (= lookup tables for the fold).
const FOLD_N_BYTES: usize = 24;
/// Entries per byte-lookup table.
const FOLD_TABLE_SIZE: usize = 256;

/// Build the 24x256 byte-lookup table for [`fold_ext_elems`]:
/// `table[k * 256 + v] = sum_{bit b set in v} coordinate_weights[k * 8 + b]`.
/// Byte order: bytes 0..8 are the little-endian bytes of `c0` (bits 0..64),
/// bytes 8..16 those of `c1` (bits 64..128), and bytes 16..24 those of `c2`.
fn build_fold_byte_table_ext(coordinate_weights: &[F192]) -> Vec<F192> {
    assert_eq!(coordinate_weights.len(), DEGREE_E);
    let mut tables = vec![F192::ZERO; FOLD_N_BYTES * FOLD_TABLE_SIZE];
    for byte_idx in 0..FOLD_N_BYTES {
        let bit_base = byte_idx * 8;
        for value in 0..FOLD_TABLE_SIZE {
            let mut acc = F192::ZERO;
            for bit_in_byte in 0..8 {
                if (value >> bit_in_byte) & 1 == 1 {
                    acc += coordinate_weights[bit_base + bit_in_byte];
                }
            }
            tables[byte_idx * FOLD_TABLE_SIZE + value] = acc;
        }
    }
    tables
}

/// One folded output slot: `sum_{k=0..24} tables[k * 256 + byte_k(elem)]`,
/// tree-reduced (depth 4) so the XORs pipeline. `tables` MUST be a
/// [`build_fold_byte_table_ext`] output (length 24 * 256). Mirror of
/// `ring_switch::fold_one_slot` with `(c0, c1)` in place of `(lo, hi)`.
#[inline(always)]
fn fold_one_slot_ext(elem: F192, tables: &[F192]) -> F192 {
    debug_assert_eq!(tables.len(), FOLD_N_BYTES * FOLD_TABLE_SIZE);
    let bytes = [elem.c0.to_le_bytes(), elem.c1.to_le_bytes(), elem.c2.to_le_bytes()];
    let mut acc = F192::ZERO;
    for (word, word_bytes) in bytes.iter().enumerate() {
        for (byte, &value) in word_bytes.iter().enumerate() {
            acc += tables[(8 * word + byte) * FOLD_TABLE_SIZE + value as usize];
        }
    }
    acc
}

/// Deferred, gamma-baked ring-switch output used by the stacked opener.
///
/// Keeping the split eq factors and the tiny byte table avoids materializing
/// one full `rs_eq_ind` vector per claim.  The table already contains the
/// claim's batching scalar, so combining several claims needs only additions.
pub(crate) struct DeferredRingSwitchOutputK {
    pub(crate) batched_sumcheck_claim: F192,
    eq_lo: Vec<F192>,
    eq_hi: Vec<F192>,
    table: Vec<F192>,
}

/// Finish a ring-switch claim without materializing its dense weight vector.
/// The batching scalar is baked into both the target and the byte table.
pub(crate) fn prove_finish_deferred(
    state: RingSwitchProveState,
    coordinate_weights: &[F192],
    gamma: F192,
) -> DeferredRingSwitchOutputK {
    let s_hat_u = transpose_s_hat(&state.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, coordinate_weights);
    let scaled_weights: Vec<F192> = coordinate_weights.iter().map(|&x| gamma * x).collect();
    DeferredRingSwitchOutputK {
        batched_sumcheck_claim: gamma * sumcheck_claim,
        eq_lo: state.eq_lo,
        eq_hi: state.eq_hi,
        table: build_fold_byte_table_ext(&scaled_weights),
    }
}

/// Fold several deferred claims directly into their final combined dense
/// basis. Every output slot is written exactly once; no per-claim dense
/// vectors are allocated or read back.
pub(crate) fn combine_deferred_into(outputs: &[DeferredRingSwitchOutputK], out: &mut [F192]) {
    use rayon::prelude::*;

    assert!(!outputs.is_empty());
    let block_len = outputs[0].eq_lo.len();
    assert!(block_len.is_power_of_two());
    assert!(
        outputs
            .iter()
            .all(|o| { o.eq_lo.len() == block_len && o.eq_lo.len() * o.eq_hi.len() == out.len() })
    );

    out.par_chunks_mut(block_len).enumerate().for_each(|(hi, out_block)| {
        for (claim_idx, claim) in outputs.iter().enumerate() {
            let e_hi = claim.eq_hi[hi];
            if claim_idx == 0 {
                for (slot, &e_lo) in out_block.iter_mut().zip(&claim.eq_lo) {
                    *slot = fold_one_slot_ext(e_lo * e_hi, &claim.table);
                }
            } else {
                for (slot, &e_lo) in out_block.iter_mut().zip(&claim.eq_lo) {
                    *slot += fold_one_slot_ext(e_lo * e_hi, &claim.table);
                }
            }
        }
    });
}

/// Bytewise-table accelerated [`fold_ext_elems_naive`] (mirror of
/// the legacy extension fold): 24 lookup tables of 256 E entries each;
/// per position 24 lookups + 23 XORs, no
/// data-dependent bit-scan. Rayon across positions.
/// Split point for the factored eq build: low half sized ~n/2 (min 4, the
/// point where two factor tables beat one full build). Mirror of the extension-field
/// layer's `ring_switch::split_n_lo`.
pub fn split_n_lo(n: usize) -> usize {
    (n / 2).clamp(4.min(n), n)
}

/// Factored eq tensor: `eq(point, y) = eq_lo[y & (2^n_lo - 1)] * eq_hi[y >> n_lo]`
/// (LSB-first indexing, matching `build_eq_table_ext`). Materializes
/// `2^n_lo + 2^(n - n_lo)` entries instead of `2^n`; field multiplication is
/// exact, so the reconstructed entries are bit-identical to the full build.
/// Mirror of the extension-field layer's `ring_switch::build_eq_split`.
pub fn build_eq_split_ext(point: &[F192]) -> (Vec<F192>, Vec<F192>) {
    let n_lo = split_n_lo(point.len());
    (build_eq_table_ext(&point[..n_lo]), build_eq_table_ext(&point[n_lo..]))
}

/// [`fold_ext_elems`] over the FACTORED tensor: each entry is reconstructed on
/// the fly (`eq_lo[a] * eq_hi[b]`, one multiply) and folded — the full
/// `2^n`-entry tensor is never materialized. Bit-identical output.
pub fn fold_ext_elems_split(eq_lo: &[F192], eq_hi: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
    use rayon::prelude::*;
    let tables = build_fold_byte_table_ext(coordinate_weights);
    let n_lo = eq_lo.len();
    debug_assert!(n_lo.is_power_of_two());
    let mask = n_lo - 1;
    let shift = n_lo.trailing_zeros();
    (0..n_lo * eq_hi.len())
        .into_par_iter()
        .map(|y| fold_one_slot_ext(eq_lo[y & mask] * eq_hi[y >> shift], &tables))
        .collect()
}

pub fn fold_ext_elems(suffix_tensor: &[F192], coordinate_weights: &[F192]) -> Vec<F192> {
    use rayon::prelude::*;
    let tables = build_fold_byte_table_ext(coordinate_weights);
    suffix_tensor
        .par_iter()
        .map(|&elem| fold_one_slot_ext(elem, &tables))
        .collect()
}

// ---------------------------------------------------------------------------
// Prover / verifier of the reduction
// ---------------------------------------------------------------------------

/// The prover message: the 64 bit-slice MLEs at the suffix point.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RingSwitchProofK {
    pub s_hat_v: Vec<F192>,
}

/// What both prover and (dense) verifier compute as a result of the
/// reduction: the transparent weight vector and the Ligerito-K target.
#[derive(Clone, Debug)]
pub struct RingSwitchOutputK {
    pub rs_eq_ind: Vec<F192>,
    pub sumcheck_claim: F192,
}

/// Verifier-side output of [`verify_succinct`]: everything needed to drive
/// the Ligerito-K consistency check without materializing `rs_eq_ind`.
#[derive(Clone, Debug)]
pub struct RingSwitchVerifierOutputK {
    pub sumcheck_claim: F192,
    /// Univariate powers derived from the batching challenge; feed them to
    /// [`eval_rs_eq_k`] at the Ligerito final point.
    pub coordinate_weights: Vec<F192>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyErrorK {
    ClaimMismatch,
}

/// Prover side of the reduction.
///
/// Inputs:
/// - `packed_witness`: `2^L` K words (L = m - 6), from
///   [`super::pack_k::pack_witness_k`].
/// - `prefix_weights`: the 64 per-bit-column weights of the consumed claim
///   ([`eq_prefix_weights`] for a plain point; phi_8 Lagrange weights mapped
///   directly in the tower for flock's skip claim).
/// - `suffix_point`: the L outer coords (in E) addressing words.
/// - `claim`: the claimed value `sum_i prefix_weights[i] * s_hat_v[i]`;
///   asserted against the witness (an honest caller always passes a
///   consistent claim, so this is a cheap integration check, 64 E-mults).
/// - `sponge` for sampling the row-batching challenge `rho`.
///
/// Output: the proof message `s_hat_v` (64 E values) plus the Ligerito-K
/// inputs `(rs_eq_ind, sumcheck_claim)`; open with
/// `recursive_prover_with_basis_k(config, packed, rs_eq_ind, sumcheck_claim, ..)`.
pub fn prove(
    packed_witness: &[F64],
    prefix_weights: &[F192],
    suffix_point: &[F192],
    claim: F192,
    precomputed_s_hat_v: Option<&[F192]>,
    sponge: &mut Sponge,
) -> (RingSwitchProofK, RingSwitchOutputK) {
    assert_eq!(prefix_weights.len(), PACKING_WIDTH_K);
    assert_eq!(
        packed_witness.len(),
        1usize << suffix_point.len(),
        "packed witness must have 2^|suffix_point| words"
    );

    // Single-claim wrapper: observe s_hat_v, sample its own rho, finish. The
    // STACKED opener instead calls `prove_observe` for every claim, samples ONE
    // shared rho after all are observed, then `prove_finish` per claim
    // (matching the extension-field opener + the recursion guest).
    let (proof, state) = prove_observe(
        packed_witness,
        prefix_weights,
        suffix_point,
        claim,
        precomputed_s_hat_v,
        sponge,
    );
    let rho = sponge.sample();
    let coordinate_weights = build_coordinate_weights(rho);
    let out = prove_finish(&state, &coordinate_weights);
    (proof, out)
}

/// Prover-side scratch carried between [`prove_observe`] and [`prove_finish`]
/// (the batching-independent data: the slice-MLE vector and the factored eq tensor).
#[derive(Clone)]
pub struct RingSwitchProveState {
    s_hat_v: Vec<F192>,
    eq_lo: Vec<F192>,
    eq_hi: Vec<F192>,
}

/// Phase 1 of the ring-switch prover: compute + observe `s_hat_v` (NO domain
/// label — matches the extension-field opener). Returns the proof and the scratch for
/// [`prove_finish`]. The caller samples the possibly shared `rho` afterwards.
pub fn prove_observe(
    packed_witness: &[F64],
    prefix_weights: &[F192],
    suffix_point: &[F192],
    claim: F192,
    precomputed_s_hat_v: Option<&[F192]>,
    sponge: &mut Sponge,
) -> (RingSwitchProofK, RingSwitchProveState) {
    assert_eq!(prefix_weights.len(), PACKING_WIDTH_K);
    assert_eq!(
        packed_witness.len(),
        1usize << suffix_point.len(),
        "packed witness must have 2^|suffix_point| words"
    );
    let (eq_lo, eq_hi) = build_eq_split_ext(suffix_point);
    let s_hat_v = match precomputed_s_hat_v {
        Some(v) => {
            assert_eq!(v.len(), PACKING_WIDTH_K);
            v.to_vec()
        }
        None => {
            use rayon::prelude::*;
            let mask = eq_lo.len() - 1;
            let shift = eq_lo.len().trailing_zeros();
            let full: Vec<F192> = (0..packed_witness.len())
                .into_par_iter()
                .map(|y| eq_lo[y & mask] * eq_hi[y >> shift])
                .collect();
            fold_1b_rows_k(packed_witness, &full)
        }
    };
    assert_eq!(
        claim_check(prefix_weights, &s_hat_v),
        claim,
        "ring_switch_k::prove: supplied claim does not match the witness"
    );
    observe_ext_slice(sponge, &s_hat_v);
    (
        RingSwitchProofK {
            s_hat_v: s_hat_v.clone(),
        },
        RingSwitchProveState { s_hat_v, eq_lo, eq_hi },
    )
}

/// Phase 2 of the ring-switch prover: given the shared coordinate weights, produce
/// the batched sumcheck claim and the transparent weight vector `rs_eq_ind`.
pub fn prove_finish(state: &RingSwitchProveState, coordinate_weights: &[F192]) -> RingSwitchOutputK {
    let s_hat_u = transpose_s_hat(&state.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, coordinate_weights);
    let rs_eq_ind = fold_ext_elems_split(&state.eq_lo, &state.eq_hi, coordinate_weights);
    RingSwitchOutputK {
        rs_eq_ind,
        sumcheck_claim,
    }
}

/// Verifier side of the reduction (dense: materializes `rs_eq_ind`).
///
/// Mirrors [`prove`]'s transcript exactly; returns `ClaimMismatch` if
/// `sum_i prefix_weights[i] * s_hat_v[i] != claim`.
pub fn verify(
    claim: F192,
    prefix_weights: &[F192],
    suffix_point: &[F192],
    proof: &RingSwitchProofK,
    sponge: &mut Sponge,
) -> Result<RingSwitchOutputK, VerifyErrorK> {
    assert_eq!(prefix_weights.len(), PACKING_WIDTH_K);
    assert_eq!(proof.s_hat_v.len(), PACKING_WIDTH_K);

    // No domain label (matches `prove`'s single-claim wrapper + the extension-field opener).
    observe_ext_slice(sponge, &proof.s_hat_v);

    if claim_check(prefix_weights, &proof.s_hat_v) != claim {
        return Err(VerifyErrorK::ClaimMismatch);
    }

    let rho = sponge.sample();
    let coordinate_weights = build_coordinate_weights(rho);

    let s_hat_u = transpose_s_hat(&proof.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, &coordinate_weights);

    let suffix_tensor = build_eq_table_ext(suffix_point);
    let rs_eq_ind = fold_ext_elems(&suffix_tensor, &coordinate_weights);

    Ok(RingSwitchOutputK {
        rs_eq_ind,
        sumcheck_claim,
    })
}

/// Polylog-cost verifier: same transcript as [`verify`] but does NOT build
/// the dense `rs_eq_ind`. Pair with [`eval_rs_eq_k`] at the Ligerito final
/// point (e.g. inside `recursive_verifier_with_basis_succinct_k`'s
/// `eval_b_residual` closure).
pub fn verify_succinct(
    claim: F192,
    prefix_weights: &[F192],
    proof: &RingSwitchProofK,
    sponge: &mut Sponge,
) -> Result<RingSwitchVerifierOutputK, VerifyErrorK> {
    // Single-claim wrapper (self-rho); the STACKED verifier uses
    // verify_observe per claim, one shared rho, then verify_finish per claim.
    verify_observe(claim, prefix_weights, proof, sponge)?;
    let rho = sponge.sample();
    let coordinate_weights = build_coordinate_weights(rho);
    Ok(verify_finish(proof, &coordinate_weights))
}

/// Phase 1 of the ring-switch verifier: observe `s_hat_v` (NO domain label —
/// matches the extension-field opener) and check the prefix-weight claim. The caller
/// samples the possibly shared `rho` afterwards.
pub fn verify_observe(
    claim: F192,
    prefix_weights: &[F192],
    proof: &RingSwitchProofK,
    sponge: &mut Sponge,
) -> Result<(), VerifyErrorK> {
    assert_eq!(prefix_weights.len(), PACKING_WIDTH_K);
    assert_eq!(proof.s_hat_v.len(), PACKING_WIDTH_K);
    observe_ext_slice(sponge, &proof.s_hat_v);
    if claim_check(prefix_weights, &proof.s_hat_v) != claim {
        return Err(VerifyErrorK::ClaimMismatch);
    }
    Ok(())
}

/// Phase 2 of the ring-switch verifier: given the shared coordinate weights,
/// produce the batched sumcheck claim.
pub fn verify_finish(proof: &RingSwitchProofK, coordinate_weights: &[F192]) -> RingSwitchVerifierOutputK {
    let s_hat_u = transpose_s_hat(&proof.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, coordinate_weights);
    RingSwitchVerifierOutputK {
        sumcheck_claim,
        coordinate_weights: coordinate_weights.to_vec(),
    }
}

// ---------------------------------------------------------------------------
// Polylog evaluation of MLE(rs_eq_ind)
// ---------------------------------------------------------------------------

/// Polylog-cost evaluation of `MLE(rs_eq_ind)(query)` at the Ligerito final
/// challenge point, following DP24 section 1.3 Figure 3 (mirror of
/// `ring_switch::eval_rs_eq` retyped to the tower).
///
/// ## Derivation
///
/// `rs_eq_ind[y] = Phi(eq(z, y))` with `z = suffix_point` and `Phi : E -> E`
/// the F_2-linear map sending basis bit w to `coordinate_weights[w]`. So
///
/// ```text
/// MLE(rs_eq_ind)(q) = sum_y eq(q, y) * Phi(eq(z, y))
///                   = sum_w coordinate_weights[w] * (sum_y A(y, w) * eq(q, y))
/// ```
///
/// where `A(y, w) = bit_w(eq(z, y))`. The inner sums are the components of
/// the tensor-algebra element `Theta = sum_y eq(q, y) (x) eq(z, y)` in
/// `E (x)_F2 E`, decomposed on the second factor's F_2 basis. Theta builds
/// iteratively because eq factorizes per coordinate: in char 2,
/// `sum_{y_j} eq(q_j, y_j) (x) eq(z_j, y_j) = 1 (x) 1 + q_j (x) 1 + 1 (x) z_j`,
/// so each step is `Theta += q_j * Theta|first + z_j * Theta|second`
/// (`scale_horizontal` / `scale_vertical`). The final `fold_vertical`
/// transposes (so rows are indexed by the z-side basis w) and folds with
/// `coordinate_weights`.
///
/// The rectangular twist vs. the old module: the fold length is e = 192
/// (the E-degree over F_2), not the packing width 64; the K side of the
/// reduction never appears here because `rs_eq_ind` is E-valued.
///
/// ## Arguments
///
/// * `z_vals`: the suffix point (`suffix_point` from [`prove`] / [`verify`]),
///   length L = m - 6.
/// * `query`: the Ligerito final challenges, length L, same coordinate order.
/// * `coordinate_weights`: the 192 univariate batching weights (from
///   [`RingSwitchVerifierOutputK`]).
pub fn eval_rs_eq_k(z_vals: &[F192], query: &[F192], coordinate_weights: &[F192]) -> F192 {
    assert_eq!(
        z_vals.len(),
        query.len(),
        "eval_rs_eq_k: z_vals and query must have equal length"
    );
    assert_eq!(
        coordinate_weights.len(),
        DEGREE_E,
        "eval_rs_eq_k: coordinate_weights length must be 192"
    );

    let mut eval = TensorAlgebraE::from_vertical(F192::ONE);
    for (&z_i, &q_i) in z_vals.iter().zip(query.iter()) {
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval.fold_vertical(coordinate_weights)
}

/// Prefix-only variant of [`eval_rs_eq_k`]: walks `query_prefix.len()` of
/// the (z, query) pairs and returns the partially-evolved tensor element.
/// Pair with [`eval_rs_eq_finish_from_prefix_binary_q_k`] to share the
/// prefix across many residual positions (the succinct Ligerito closure).
pub fn eval_rs_eq_prefix_k(z_vals: &[F192], query_prefix: &[F192]) -> TensorAlgebraE {
    assert!(query_prefix.len() <= z_vals.len());
    let mut eval = TensorAlgebraE::from_vertical(F192::ONE);
    for (&z_i, &q_i) in z_vals.iter().zip(query_prefix.iter()) {
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval
}

/// Finish [`eval_rs_eq_k`] from a precomputed prefix when the query suffix
/// is **binary** (bit j of `y_bits` is the j-th suffix coord). With
/// `q_j in {0, 1}` the general step collapses (char 2) to a single vertical
/// scale: `q_j = 0` gives `(1 + z_j) * eval`, `q_j = 1` gives `z_j * eval`.
/// Mirror of `ring_switch::eval_rs_eq_finish_from_prefix_binary_q`.
pub fn eval_rs_eq_finish_from_prefix_binary_q_k(
    prefix: &TensorAlgebraE,
    z_vals_suffix: &[F192],
    y_bits: u32,
    coordinate_weights: &[F192],
) -> F192 {
    assert_eq!(coordinate_weights.len(), DEGREE_E);
    debug_assert!(z_vals_suffix.len() <= 32, "y_bits is u32; suffix > 32 not supported");
    let mut eval = prefix.clone();
    for (j, &z_i) in z_vals_suffix.iter().enumerate() {
        let scalar = if (y_bits >> j) & 1 == 1 { z_i } else { F192::ONE + z_i };
        for e in eval.elems.iter_mut() {
            *e *= scalar;
        }
    }
    eval.fold_vertical(coordinate_weights)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ligerito::{ProverConfig, VerifierConfig, default_config, default_verifier_config};
    use crate::ligerito_k::{
        LigeritoProofK, commit_k, k_configs_for, recursive_prover_with_basis_k, recursive_verifier_with_basis_k,
        recursive_verifier_with_basis_succinct_k,
    };
    use crate::merkle::Hash;
    use crate::pack_k::pack_witness_k;

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    #[test]
    fn deferred_batch_matches_materialized_weights() {
        let mut seed = 0xdec0_de01_2345_6789;
        let point = (0..10)
            .map(|_| F192::new(splitmix64(&mut seed), splitmix64(&mut seed), splitmix64(&mut seed)))
            .collect::<Vec<_>>();
        let coordinate_weights = (0..DEGREE_E)
            .map(|_| F192::new(splitmix64(&mut seed), splitmix64(&mut seed), splitmix64(&mut seed)))
            .collect::<Vec<_>>();
        let gammas = [
            F192::new(splitmix64(&mut seed), splitmix64(&mut seed), splitmix64(&mut seed)),
            F192::new(splitmix64(&mut seed), splitmix64(&mut seed), splitmix64(&mut seed)),
        ];
        let states = (0..2)
            .map(|_| {
                let (eq_lo, eq_hi) = build_eq_split_ext(&point);
                RingSwitchProveState {
                    s_hat_v: (0..PACKING_WIDTH_K)
                        .map(|_| F192::new(splitmix64(&mut seed), splitmix64(&mut seed), splitmix64(&mut seed)))
                        .collect(),
                    eq_lo,
                    eq_hi,
                }
            })
            .collect::<Vec<_>>();

        let dense = states
            .iter()
            .map(|state| prove_finish(state, &coordinate_weights))
            .collect::<Vec<_>>();
        let expected_target = dense
            .iter()
            .zip(gammas)
            .fold(F192::ZERO, |acc, (out, gamma)| acc + gamma * out.sumcheck_claim);
        let expected_basis = (0..1usize << point.len())
            .map(|i| gammas[0] * dense[0].rs_eq_ind[i] + gammas[1] * dense[1].rs_eq_ind[i])
            .collect::<Vec<_>>();

        let deferred = states
            .into_iter()
            .zip(gammas)
            .map(|(state, gamma)| prove_finish_deferred(state, &coordinate_weights, gamma))
            .collect::<Vec<_>>();
        let deferred_target = deferred
            .iter()
            .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim);
        let mut deferred_basis = vec![F192::ZERO; expected_basis.len()];
        combine_deferred_into(&deferred, &mut deferred_basis);

        assert_eq!(deferred_target, expected_target);
        assert_eq!(deferred_basis, expected_basis);
    }

    #[test]
    fn trace_dual_basis_k_is_dual() {
        // Tr(dual[i]·basis(j)) == δ_ij, and bit_i(y) = Tr(dual[i]·y) recovers
        // coordinate bits of a few random elements.
        let dual = trace_dual_basis_k();
        let basis = |j: usize| {
            if j < 64 {
                F192::new(1u64 << j, 0, 0)
            } else if j < 128 {
                F192::new(0, 1u64 << (j - 64), 0)
            } else {
                F192::new(0, 0, 1u64 << (j - 128))
            }
        };
        let tr = |x: F192| {
            let (mut acc, mut p) = (F192::ZERO, x);
            for _ in 0..192 {
                acc += p;
                p = p * p;
            }
            acc
        };
        for i in 0..DEGREE_E {
            for j in 0..DEGREE_E {
                let want = if i == j { F192::ONE } else { F192::ZERO };
                assert_eq!(tr(dual[i] * basis(j)), want, "duality fails at i={i}, j={j}");
            }
        }
        let mut s = 0xDEAD_BEEF_u64;
        for _ in 0..8 {
            let y = F192::new(splitmix64(&mut s), splitmix64(&mut s), splitmix64(&mut s));
            for i in 0..DEGREE_E {
                let bit = if i < 64 {
                    (y.c0 >> i) & 1
                } else if i < 128 {
                    (y.c1 >> (i - 64)) & 1
                } else {
                    (y.c2 >> (i - 128)) & 1
                };
                let want = if bit == 1 { F192::ONE } else { F192::ZERO };
                assert_eq!(tr(dual[i] * y), want, "bit {i} extraction wrong");
            }
        }
    }

    fn rand_ext(s: &mut u64) -> F192 {
        F192::new(splitmix64(s), splitmix64(s), splitmix64(s))
    }

    fn rand_bits(m: usize, s: &mut u64) -> Vec<bool> {
        (0..1usize << m).map(|_| splitmix64(s) & 1 == 1).collect()
    }

    #[test]
    fn coordinate_weights_are_consecutive_powers() {
        let mut s = 0x1234_5678_9abc_def0;
        let rho = rand_ext(&mut s);
        let weights = build_coordinate_weights(rho);

        assert_eq!(weights.len(), DEGREE_E);
        assert_eq!(weights[0], F192::ONE);
        for pair in weights.windows(2) {
            assert_eq!(pair[1], pair[0] * rho);
        }
    }

    /// Reference s_hat_v: brute-force partial evaluation of each bit-column
    /// MLE at the suffix point (direct bit-extract loop, no fold kernel).
    fn s_hat_v_reference(packed: &[F64], suffix_point: &[F192]) -> Vec<F192> {
        let eq_suffix = build_eq_table_ext(suffix_point);
        (0..PACKING_WIDTH_K)
            .map(|i| {
                let mut acc = F192::ZERO;
                for (word, &w) in packed.iter().zip(eq_suffix.iter()) {
                    if (word.0 >> i) & 1 == 1 {
                        acc += w;
                    }
                }
                acc
            })
            .collect()
    }

    /// s_hat_v[i] must equal the MLE of the i-th bit-slice at the suffix
    /// point; cross-check the fold kernel against a from-the-bits brute
    /// force over the full (prefix + suffix) hypercube.
    #[test]
    fn s_hat_v_matches_bruteforce() {
        let m = 9;
        let mut s = 1u64;
        let bits = rand_bits(m, &mut s);
        let packed = pack_witness_k(&bits, m);
        let suffix_point: Vec<F192> = (0..m - LOG_PACKING_K).map(|_| rand_ext(&mut s)).collect();
        let eq_suffix = build_eq_table_ext(&suffix_point);

        let s_hat_v = fold_1b_rows_k(&packed, &eq_suffix);
        assert_eq!(s_hat_v.len(), PACKING_WIDTH_K);

        // From the flat bit layout: column i is z[y * 64 + i].
        for i in 0..PACKING_WIDTH_K {
            let mut expected = F192::ZERO;
            for (y, &w) in eq_suffix.iter().enumerate() {
                if bits[(y << LOG_PACKING_K) | i] {
                    expected += w;
                }
            }
            assert_eq!(s_hat_v[i], expected, "bit column {i}");
        }
        assert_eq!(s_hat_v, s_hat_v_reference(&packed, &suffix_point));
    }

    /// The MFR kernel must equal the scalar bit-scan (same XOR-sums, only
    /// regrouped) on random data, and the dispatcher must route both regimes
    /// correctly (multiple-of-8 lengths to MFR, smaller powers of two to the
    /// scalar path).
    #[test]
    fn fold_1b_rows_mfr_matches_scalar() {
        let mut s = 31u64;
        for log_len in [3usize, 4, 7, 11] {
            let len = 1usize << log_len;
            let packed: Vec<F64> = (0..len).map(|_| F64(splitmix64(&mut s))).collect();
            let tensor: Vec<F192> = (0..len).map(|_| rand_ext(&mut s)).collect();
            let mfr = fold_1b_rows_k_mfr_8wide(&packed, &tensor);
            let scalar = fold_1b_rows_k_scalar(&packed, &tensor);
            assert_eq!(mfr, scalar, "MFR/scalar split at len={len}");
            assert_eq!(fold_1b_rows_k(&packed, &tensor), mfr, "dispatcher at len={len}");
        }
        for len in [1usize, 2, 4] {
            let packed: Vec<F64> = (0..len).map(|_| F64(splitmix64(&mut s))).collect();
            let tensor: Vec<F192> = (0..len).map(|_| rand_ext(&mut s)).collect();
            assert_eq!(
                fold_1b_rows_k(&packed, &tensor),
                fold_1b_rows_k_scalar(&packed, &tensor),
                "scalar fallback at len={len}"
            );
        }
    }

    /// Claim-check completeness (a plain point claim verifies) and soundness
    /// (a wrong claim value or a tampered s_hat_v is rejected).
    #[test]
    fn claim_check_completeness_and_soundness() {
        let m = 10;
        let mut s = 2u64;
        let bits = rand_bits(m, &mut s);
        let packed = pack_witness_k(&bits, m);
        let point: Vec<F192> = (0..m).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&point[..LOG_PACKING_K]);
        let suffix_point = &point[LOG_PACKING_K..];

        // Honest claim from the reference partials; sanity: it equals the
        // full bit-MLE evaluated with the full eq table.
        let s_ref = s_hat_v_reference(&packed, suffix_point);
        let claim = claim_check(&prefix_weights, &s_ref);
        let eq_full = build_eq_table_ext(&point);
        let mut direct = F192::ZERO;
        for (x, &w) in eq_full.iter().enumerate() {
            if bits[x] {
                direct += w;
            }
        }
        assert_eq!(claim, direct, "prefix x suffix split must factor the MLE");

        let mut ch = Sponge::new(b"rs-k-claim-test", &[]);
        let (proof, _out) = prove(&packed, &prefix_weights, suffix_point, claim, None, &mut ch);

        let mut ch = Sponge::new(b"rs-k-claim-test", &[]);
        assert!(verify(claim, &prefix_weights, suffix_point, &proof, &mut ch).is_ok());

        // Wrong claim value.
        let bad_claim = claim + F192::ONE;
        let mut ch = Sponge::new(b"rs-k-claim-test", &[]);
        assert_eq!(
            verify(bad_claim, &prefix_weights, suffix_point, &proof, &mut ch).unwrap_err(),
            VerifyErrorK::ClaimMismatch
        );
        let mut ch = Sponge::new(b"rs-k-claim-test", &[]);
        assert_eq!(
            verify_succinct(bad_claim, &prefix_weights, &proof, &mut ch).unwrap_err(),
            VerifyErrorK::ClaimMismatch
        );

        // Tampered s_hat_v.
        let mut bad = proof.clone();
        bad.s_hat_v[17].c0 ^= 1;
        let mut ch = Sponge::new(b"rs-k-claim-test", &[]);
        assert_eq!(
            verify(claim, &prefix_weights, suffix_point, &bad, &mut ch).unwrap_err(),
            VerifyErrorK::ClaimMismatch
        );
    }

    /// The bytewise-table rs_eq_ind fold must match the naive bit-scan on
    /// arbitrary (not necessarily eq-structured) input.
    #[test]
    fn rs_eq_ind_fast_matches_naive() {
        let mut s = 3u64;
        let tensor: Vec<F192> = (0..1usize << 8).map(|_| rand_ext(&mut s)).collect();
        let coordinate_weights: Vec<F192> = (0..DEGREE_E).map(|_| rand_ext(&mut s)).collect();
        assert_eq!(
            fold_ext_elems(&tensor, &coordinate_weights),
            fold_ext_elems_naive(&tensor, &coordinate_weights)
        );
    }

    /// eval_rs_eq_k must agree with the dense evaluation: materialize
    /// rs_eq_ind, evaluate its MLE at a random query with the eq table.
    /// Also pins the prefix + binary-q variant against the full path.
    #[test]
    fn eval_rs_eq_matches_dense() {
        let l = 6;
        let mut s = 4u64;
        let z: Vec<F192> = (0..l).map(|_| rand_ext(&mut s)).collect();
        let coordinate_weights = build_coordinate_weights(rand_ext(&mut s));
        let rs_eq_ind = fold_ext_elems(&build_eq_table_ext(&z), &coordinate_weights);

        let query: Vec<F192> = (0..l).map(|_| rand_ext(&mut s)).collect();
        let eq_query = build_eq_table_ext(&query);
        let dense = inner_product_ext(&rs_eq_ind, &eq_query);

        assert_eq!(eval_rs_eq_k(&z, &query, &coordinate_weights), dense);

        // Prefix + binary-q path: replace the last 3 query coords by the
        // bits of y and compare against the general path.
        let split = l - 3;
        let prefix = eval_rs_eq_prefix_k(&z, &query[..split]);
        for y in 0..8u32 {
            let mut q_bin = query[..split].to_vec();
            for j in 0..3 {
                q_bin.push(if (y >> j) & 1 == 1 { F192::ONE } else { F192::ZERO });
            }
            assert_eq!(
                eval_rs_eq_finish_from_prefix_binary_q_k(&prefix, &z[split..], y, &coordinate_weights),
                eval_rs_eq_k(&z, &q_bin, &coordinate_weights),
                "binary-q finish mismatch at y={y}"
            );
        }
    }

    /// The core algebraic identity of the reduction: the honest packed
    /// witness satisfies the output claim,
    /// `sum_y rs_eq_ind[y] * packed[y] == sumcheck_claim`.
    #[test]
    fn sumcheck_claim_matches_inner_product() {
        let m = 12;
        let mut s = 5u64;
        let bits = rand_bits(m, &mut s);
        let packed = pack_witness_k(&bits, m);
        let point: Vec<F192> = (0..m).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&point[..LOG_PACKING_K]);
        let suffix_point = &point[LOG_PACKING_K..];
        let claim = claim_check(&prefix_weights, &s_hat_v_reference(&packed, suffix_point));

        let mut ch = Sponge::new(b"rs-k-identity-test", &[]);
        let (_proof, out) = prove(&packed, &prefix_weights, suffix_point, claim, None, &mut ch);
        assert_eq!(
            inner_product_base_ext(&packed, &out.rs_eq_ind),
            out.sumcheck_claim,
            "reduction output claim must hold for the honest witness"
        );
    }

    // -- end-to-end: reduction + ligerito_k opening --------------------------

    /// Configs for a K-witness of `2^log_n` words: prefer the production
    /// Secure-profile derivation; fall back to the ad-hoc default_config
    /// shape at test sizes below its feasibility floor (same fallback the
    /// ligerito_k tests use).
    fn configs_for(log_n: usize) -> (ProverConfig, VerifierConfig) {
        if let Ok(pv) = k_configs_for(log_n) {
            return pv;
        }
        for bs in (1..=5).rev() {
            for rate in 1..=4 {
                if let (Ok(pc), Ok(vc)) = (
                    default_config(log_n, bs, rate),
                    default_verifier_config(log_n, bs, rate),
                ) {
                    return (pc, vc);
                }
            }
        }
        panic!("no feasible ligerito_k config at log_n = {log_n}");
    }

    struct E2e {
        vc: VerifierConfig,
        log_n: usize,
        prefix_weights: Vec<F192>,
        suffix_point: Vec<F192>,
        claim: F192,
        root: Hash,
        rs_proof: RingSwitchProofK,
        lig_proof: LigeritoProofK,
    }

    const E2E_DOMAIN: &[u8] = b"ring-switch-k-e2e-test";

    /// Full prover pipeline: random bit witness, pack, commit, ring switch
    /// (plain-point eq weights or a caller-supplied generalized weight
    /// vector), then the ligerito_k opening on (rs_eq_ind, sumcheck_claim),
    /// all over one continuous transcript.
    fn prove_e2e(m: usize, seed: u64, generalized_weights: bool) -> E2e {
        let mut s = seed;
        let bits = rand_bits(m, &mut s);
        let packed = pack_witness_k(&bits, m);
        let log_n = m - LOG_PACKING_K;
        let (pc, vc) = configs_for(log_n);
        let (cm, pd) = commit_k(&packed, pc.initial_k, pc.log_inv_rates[0]);

        let suffix_point: Vec<F192> = (0..log_n).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights: Vec<F192> = if generalized_weights {
            // Synthetic non-eq weights (e.g. standing in for phi_8 Lagrange
            // weights): any 64 E-values work.
            (0..PACKING_WIDTH_K).map(|_| rand_ext(&mut s)).collect()
        } else {
            let r_prefix: Vec<F192> = (0..LOG_PACKING_K).map(|_| rand_ext(&mut s)).collect();
            eq_prefix_weights(&r_prefix)
        };
        let claim = claim_check(&prefix_weights, &s_hat_v_reference(&packed, &suffix_point));

        let mut ch = Sponge::new(E2E_DOMAIN, &[]);
        let (rs_proof, out) = prove(&packed, &prefix_weights, &suffix_point, claim, None, &mut ch);
        assert_eq!(inner_product_base_ext(&packed, &out.rs_eq_ind), out.sumcheck_claim);
        let lig_proof = recursive_prover_with_basis_k(
            &pc,
            &packed,
            out.rs_eq_ind,
            out.sumcheck_claim,
            &pd.codeword,
            &pd.merkle_tree,
            &mut ch,
        );
        E2e {
            vc,
            log_n,
            prefix_weights,
            suffix_point,
            claim,
            root: cm.root,
            rs_proof,
            lig_proof,
        }
    }

    /// Dense verification: ring-switch verify (rebuilds rs_eq_ind), then the
    /// dense ligerito_k verifier with b_initial = rs_eq_ind.
    fn verify_e2e_dense(e: &E2e) -> bool {
        let mut ch = Sponge::new(E2E_DOMAIN, &[]);
        let out = match verify(e.claim, &e.prefix_weights, &e.suffix_point, &e.rs_proof, &mut ch) {
            Ok(o) => o,
            Err(_) => return false,
        };
        recursive_verifier_with_basis_k(
            &e.vc,
            &e.lig_proof,
            &out.rs_eq_ind,
            out.sumcheck_claim,
            &e.root,
            &mut ch,
        )
    }

    /// Succinct verification: verify_succinct (no rs_eq_ind), then the
    /// succinct ligerito_k verifier whose eval_b_residual closure evaluates
    /// MLE(rs_eq_ind) polylog via eval_rs_eq_k (shared prefix + binary-q
    /// residual finish).
    fn verify_e2e_succinct(e: &E2e) -> bool {
        let mut ch = Sponge::new(E2E_DOMAIN, &[]);
        let out = match verify_succinct(e.claim, &e.prefix_weights, &e.rs_proof, &mut ch) {
            Ok(o) => o,
            Err(_) => return false,
        };
        let z = e.suffix_point.clone();
        let coordinate_weights = out.coordinate_weights.clone();
        recursive_verifier_with_basis_succinct_k(
            &e.vc,
            &e.lig_proof,
            e.log_n,
            out.sumcheck_claim,
            &e.root,
            |ris, yr_log_n| {
                let split = z.len() - yr_log_n;
                assert_eq!(ris.len(), split, "closure gets the full folded ris");
                let prefix = eval_rs_eq_prefix_k(&z, ris);
                (0..1u32 << yr_log_n)
                    .map(|y| eval_rs_eq_finish_from_prefix_binary_q_k(&prefix, &z[split..], y, &coordinate_weights))
                    .collect()
            },
            &mut ch,
        )
    }

    #[test]
    fn end_to_end_plain_point() {
        for (m, seed) in [(13usize, 10u64), (17, 11)] {
            let e = prove_e2e(m, seed, false);
            assert!(verify_e2e_dense(&e), "dense e2e rejected at m={m}");
            assert!(verify_e2e_succinct(&e), "succinct e2e rejected at m={m}");
        }
    }

    #[test]
    fn end_to_end_generalized_weights() {
        let e = prove_e2e(13, 12, true);
        assert!(verify_e2e_dense(&e), "dense e2e (generalized) rejected");
        assert!(verify_e2e_succinct(&e), "succinct e2e (generalized) rejected");
    }

    /// Tampering: a bit-flip in s_hat_v breaks the claim check; a
    /// claim-preserving forgery (two entries adjusted so the weighted sum is
    /// unchanged) passes the claim check but diverges the FS transcript, so
    /// the ligerito opening must reject it. A tampered claim value is
    /// rejected outright. Dense and succinct paths must agree throughout.
    #[test]
    fn end_to_end_rejects_tampering() {
        let e = prove_e2e(13, 13, false);

        // Plain bit flip: caught by the claim check.
        let mut bad = E2e {
            rs_proof: e.rs_proof.clone(),
            lig_proof: e.lig_proof.clone(),
            vc: e.vc.clone(),
            log_n: e.log_n,
            prefix_weights: e.prefix_weights.clone(),
            suffix_point: e.suffix_point.clone(),
            claim: e.claim,
            root: e.root,
        };
        bad.rs_proof.s_hat_v[5].c1 ^= 1;
        assert!(!verify_e2e_dense(&bad), "bit-flipped s_hat_v accepted");
        assert!(!verify_e2e_succinct(&bad), "bit-flipped s_hat_v accepted (succinct)");

        // Claim-preserving forgery: s'_1 = s_1 + d, s'_0 = s_0 + w_1*d/w_0
        // keeps sum_i w_i s'_i = claim, so the claim check passes; the
        // downstream opening must still reject (the batching weights and
        // target diverge from what the ligerito proof was built for).
        let mut s = 99u64;
        let d = rand_ext(&mut s);
        let w0 = e.prefix_weights[0];
        let w1 = e.prefix_weights[1];
        assert!(!w0.is_zero() && !d.is_zero());
        bad.rs_proof = e.rs_proof.clone();
        bad.rs_proof.s_hat_v[1] += d;
        bad.rs_proof.s_hat_v[0] += w1 * d * w0.inv();
        assert_eq!(
            claim_check(&bad.prefix_weights, &bad.rs_proof.s_hat_v),
            e.claim,
            "forgery must be claim-preserving for this test to bite"
        );
        assert!(!verify_e2e_dense(&bad), "claim-preserving forgery accepted (dense)");
        assert!(
            !verify_e2e_succinct(&bad),
            "claim-preserving forgery accepted (succinct)"
        );

        // Tampered claim value.
        bad.rs_proof = e.rs_proof.clone();
        bad.claim = e.claim + F192::ONE;
        assert!(!verify_e2e_dense(&bad), "tampered claim accepted");
        assert!(!verify_e2e_succinct(&bad), "tampered claim accepted (succinct)");
    }
}
