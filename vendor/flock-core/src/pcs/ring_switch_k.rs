// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The DP24 iterative `eval_rs_eq_k` mirrors this crate's F128-era
// `ring_switch::eval_rs_eq` (itself ported from binius64). The rest of the
// module is the rectangular (f = 64, e = 128) generalization described in
// the ring-switching-generalized note.

//! Ring-switching reduction for the 64-bit transition: F_2 to K = GF(2^64)
//! packing, opened over E = GF(2^128) (the tower [`F128T`]).
//!
//! Rectangular mirror of [`super::ring_switch`] with f = 64 (packing degree
//! over F_2) and e = 128 (opening degree). Converts one evaluation claim on
//! the bit-witness MLE at an E-point into a Ligerito-K sumcheck claim on the
//! packed multilinear (a `Vec<F64>`, one word per 64 bits, see
//! [`super::pack_k`]) against a transparent E-valued weight vector
//! `rs_eq_ind`.
//!
//! ## Differences from the F128-era module
//!
//! - **Rectangular shape**: `s_hat_v` has 64 entries (one per packing bit),
//!   each an E element; its tensor-algebra transpose `s_hat_u = (t_w)_w` has
//!   128 K-entries; the row-batching challenge `r''` is 7 E-elements whose
//!   eq tensor has length 128 = e (the E-degree), NOT the packing width.
//! - **No "7 = 6 + 1" prefix split**: with 64-bit packing the packed prefix
//!   is exactly the 6-bit skip domain, and the old 7th bit is an ordinary
//!   suffix coordinate of the packed witness (which has `2^(m-6)` words).
//! - **Generalized prefix weights**: the consumed claim is
//!   `claim == sum_{i in 0..64} prefix_weights[i] * s_hat_v[i]`. For a plain
//!   multilinear point claim the weights are the eq tensor of the 6 prefix
//!   coords ([`eq_prefix_weights`]); for flock's univariate-skip claim (whose
//!   first coordinate ranges over the phi_8 Lagrange domain, not the boolean
//!   cube) the caller passes the 64 phi_8 Lagrange weights
//!   `lagrange_weights_naive(6, z_skip)` mapped through `ghash_to_tower`.
//!   This module never looks inside the weights, so flock's `z_skip` flows
//!   through unchanged.
//!
//! ## Protocol (prover)
//!
//! 1. Send `s_hat_v[i] = sum_y eq(r_suffix, y) * bit_i(packed[y])`, the MLE
//!    of the i-th bit-slice at the suffix point (i in 0..64, values in E).
//! 2. Verifier checks `claim == sum_i prefix_weights[i] * s_hat_v[i]`.
//! 3. Sample `r'' in E^7`; let `eq_rdp = eq(r'')` (length 128). Transpose
//!    `s_hat_v` to `t_w = s_hat_u[w] in K` (see
//!    [`super::tensor_algebra_k::transpose_s_hat`]); the batched target is
//!    `sumcheck_claim = sum_w eq_rdp[w] * t_w` (K x E via `mul_base`).
//! 4. Both sides define the transparent weights
//!    `rs_eq_ind[y] = Phi(eq(r_suffix, y))` where `Phi : E -> E` is the
//!    F_2-linear map sending E-basis bit w to `eq_rdp[w]`. Completeness:
//!    `sum_y rs_eq_ind[y] * packed[y] == sumcheck_claim`, which is exactly
//!    the claim shape [`super::ligerito_k::recursive_prover_with_basis_k`]
//!    proves (with `b_initial = rs_eq_ind`, `target = sumcheck_claim`).
//!
//! ## Prover vs. verifier paths for `rs_eq_ind`
//!
//! - [`prove`] / [`verify`] materialize `rs_eq_ind` densely via
//!   [`fold_ext_elems`] (bytewise-table fold, rayon), `2^(m-6)` E entries.
//! - [`verify_succinct`] + [`eval_rs_eq_k`] never materialize it: the MLE of
//!   `rs_eq_ind` at the Ligerito final point is evaluated in
//!   `O((m-6) * 128^2)` bit-ops plus `O((m-6) * 128)` E-multiplications via
//!   the DP24 tensor-algebra iterative algorithm (DP24 section 1.3 Figure 3).
//!
//! [DP24]: <https://eprint.iacr.org/2024/504>

use crate::challenger::Challenger;
use crate::field::{F64, F128, F128T};
use serde::{Deserialize, Serialize};

use super::ligerito_k::{build_eq_table_ext, inner_product_base_ext};
use super::pack_k::{LOG_PACKING_K, PACKING_WIDTH_K};
use super::tensor_algebra_k::{DEGREE_E, TensorAlgebraE, transpose_s_hat};

/// log2 of the E-degree: the number of row-batching challenges `r''`. Their
/// eq tensor has length `2^LOG_DEGREE_E = 128 = e`.
pub const LOG_DEGREE_E: usize = 7;
const _: () = assert!(1 << LOG_DEGREE_E == DEGREE_E);

// ---------------------------------------------------------------------------
// Challenger shim (same convention as ligerito_k): the Challenger trait
// speaks GHASH F128 as 16 uniform transcript bytes; every 16-byte pattern is
// a valid F128T, so sampling reinterprets bytes and observing ferries the
// two lanes through the (lo, hi) slots. No arithmetic ever happens in the
// GHASH representation here.
// ---------------------------------------------------------------------------

fn sample_ext_vec<Ch: Challenger>(challenger: &mut Ch, n: usize) -> Vec<F128T> {
    challenger
        .sample_f128_vec(n)
        .into_iter()
        .map(|v| F128T::new(v.lo, v.hi))
        .collect()
}

fn observe_ext_slice<Ch: Challenger>(challenger: &mut Ch, values: &[F128T]) {
    for e in values {
        challenger.observe_f128(F128::new(e.c0, e.c1));
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
pub fn eq_prefix_weights(r_prefix: &[F128T]) -> Vec<F128T> {
    assert_eq!(
        r_prefix.len(),
        LOG_PACKING_K,
        "eq_prefix_weights: prefix must have LOG_PACKING_K = 6 coords"
    );
    build_eq_table_ext(r_prefix)
}

/// Standard inner product `sum_i a[i] * b[i]` over E.
pub fn inner_product_ext(a: &[F128T], b: &[F128T]) -> F128T {
    assert_eq!(a.len(), b.len());
    let mut acc = F128T::ZERO;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc += x * y;
    }
    acc
}

/// The verifier's claim check: `sum_i prefix_weights[i] * s_hat_v[i]`.
pub fn claim_check(prefix_weights: &[F128T], s_hat_v: &[F128T]) -> F128T {
    inner_product_ext(prefix_weights, s_hat_v)
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
/// Mirror of `ring_switch::fold_1b_rows_naive` at 64-bit width: rayon
/// bit-scan with per-thread length-64 partial accumulators XOR-reduced at
/// the end. This is the standalone (non-fused) prove path; the
/// univariate-skip-fused variant is a later optimization.
pub fn fold_1b_rows_k(packed_witness: &[F64], suffix_tensor: &[F128T]) -> Vec<F128T> {
    use rayon::prelude::*;
    assert_eq!(packed_witness.len(), suffix_tensor.len());
    let n = PACKING_WIDTH_K;
    let zero_acc = || vec![F128T::ZERO; n];

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

/// Compute `rs_eq_ind`, the transparent E-valued weight vector over the
/// suffix domain: `rs_eq_ind[y] = Phi(suffix_tensor[y])` where `Phi` sends
/// E-basis bit w to `eq_r_dprime[w]`, i.e.
///
/// `rs_eq_ind[y] = sum_w bit_w(suffix_tensor[y]) * eq_r_dprime[w]`
///
/// Naive reference: rayon per-position bit-scan over the two 64-bit lanes.
/// See [`fold_ext_elems`] for the bytewise-table production version.
pub fn fold_ext_elems_naive(suffix_tensor: &[F128T], eq_r_dprime: &[F128T]) -> Vec<F128T> {
    use rayon::prelude::*;
    assert_eq!(eq_r_dprime.len(), DEGREE_E);
    suffix_tensor
        .par_iter()
        .map(|&elem| {
            let mut acc = F128T::ZERO;
            let mut c0 = elem.c0;
            while c0 != 0 {
                let w = c0.trailing_zeros() as usize;
                acc += eq_r_dprime[w];
                c0 &= c0 - 1;
            }
            let mut c1 = elem.c1;
            while c1 != 0 {
                let w = c1.trailing_zeros() as usize;
                acc += eq_r_dprime[64 | w];
                c1 &= c1 - 1;
            }
            acc
        })
        .collect()
}

/// Number of bytes in an E element (= lookup tables for the fold).
const FOLD_N_BYTES: usize = 16;
/// Entries per byte-lookup table.
const FOLD_TABLE_SIZE: usize = 256;

/// Build the 16x256 byte-lookup table for [`fold_ext_elems`]:
/// `table[k * 256 + v] = sum_{bit b set in v} eq_r_dprime[k * 8 + b]`.
/// Byte order: bytes 0..8 are the little-endian bytes of `c0` (bits 0..64),
/// bytes 8..16 those of `c1` (bits 64..128).
fn build_fold_byte_table_ext(eq_r_dprime: &[F128T]) -> Vec<F128T> {
    assert_eq!(eq_r_dprime.len(), DEGREE_E);
    let mut tables = vec![F128T::ZERO; FOLD_N_BYTES * FOLD_TABLE_SIZE];
    for byte_idx in 0..FOLD_N_BYTES {
        let bit_base = byte_idx * 8;
        for value in 0..FOLD_TABLE_SIZE {
            let mut acc = F128T::ZERO;
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

/// One folded output slot: `sum_{k=0..16} tables[k * 256 + byte_k(elem)]`,
/// tree-reduced (depth 4) so the XORs pipeline. `tables` MUST be a
/// [`build_fold_byte_table_ext`] output (length 16 * 256). Mirror of
/// `ring_switch::fold_one_slot` with `(c0, c1)` in place of `(lo, hi)`.
#[inline(always)]
fn fold_one_slot_ext(elem: F128T, tables: &[F128T]) -> F128T {
    debug_assert_eq!(tables.len(), FOLD_N_BYTES * FOLD_TABLE_SIZE);
    let lo_bytes = elem.c0.to_le_bytes();
    let hi_bytes = elem.c1.to_le_bytes();
    let tables_ptr = tables.as_ptr();
    // SAFETY: byte values are u8 (0..256); the max offset is
    // 15 * 256 + 255 = 4095 = 16 * 256 - 1, in-bounds for the asserted length.
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
}

/// Bytewise-table accelerated [`fold_ext_elems_naive`] (mirror of
/// `ring_switch::fold_b128_elems`): 16 lookup tables of 256 E entries each
/// (64 KiB, L1/L2-resident); per position 16 lookups + 15 XORs, no
/// data-dependent bit-scan. Rayon across positions.
pub fn fold_ext_elems(suffix_tensor: &[F128T], eq_r_dprime: &[F128T]) -> Vec<F128T> {
    use rayon::prelude::*;
    let tables = build_fold_byte_table_ext(eq_r_dprime);
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
    pub s_hat_v: Vec<F128T>,
}

/// What both prover and (dense) verifier compute as a result of the
/// reduction: the transparent weight vector and the Ligerito-K target.
#[derive(Clone, Debug)]
pub struct RingSwitchOutputK {
    pub rs_eq_ind: Vec<F128T>,
    pub sumcheck_claim: F128T,
}

/// Verifier-side output of [`verify_succinct`]: everything needed to drive
/// the Ligerito-K consistency check without materializing `rs_eq_ind`.
#[derive(Clone, Debug)]
pub struct RingSwitchVerifierOutputK {
    pub sumcheck_claim: F128T,
    /// eq tensor of length 128 derived from the sampled `r''`; feed it to
    /// [`eval_rs_eq_k`] at the Ligerito final point.
    pub eq_r_dprime: Vec<F128T>,
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
///   through `ghash_to_tower` for flock's skip claim).
/// - `suffix_point`: the L outer coords (in E) addressing words.
/// - `claim`: the claimed value `sum_i prefix_weights[i] * s_hat_v[i]`;
///   asserted against the witness (an honest caller always passes a
///   consistent claim, so this is a cheap integration check, 64 E-mults).
/// - `challenger` for sampling the row-batching `r''`.
///
/// Output: the proof message `s_hat_v` (64 E values) plus the Ligerito-K
/// inputs `(rs_eq_ind, sumcheck_claim)`; open with
/// `recursive_prover_with_basis_k(config, packed, rs_eq_ind, sumcheck_claim, ..)`.
pub fn prove<Ch: Challenger>(
    packed_witness: &[F64],
    prefix_weights: &[F128T],
    suffix_point: &[F128T],
    claim: F128T,
    challenger: &mut Ch,
) -> (RingSwitchProofK, RingSwitchOutputK) {
    assert_eq!(prefix_weights.len(), PACKING_WIDTH_K);
    assert_eq!(
        packed_witness.len(),
        1usize << suffix_point.len(),
        "packed witness must have 2^|suffix_point| words"
    );

    challenger.observe_label(b"flock-ring-switch-k-v0");

    let suffix_tensor = build_eq_table_ext(suffix_point);

    // Compute and send s_hat_v.
    let s_hat_v = fold_1b_rows_k(packed_witness, &suffix_tensor);
    assert_eq!(
        claim_check(prefix_weights, &s_hat_v),
        claim,
        "ring_switch_k::prove: supplied claim does not match the witness"
    );
    observe_ext_slice(challenger, &s_hat_v);

    // Sample row-batching r''; its eq tensor has length 128 = e.
    let r_dprime = sample_ext_vec(challenger, LOG_DEGREE_E);
    let eq_r_dprime = build_eq_table_ext(&r_dprime);

    // Batched target: T = sum_w eq_rdp[w] * t_w with t_w = s_hat_u[w] in K.
    let s_hat_u = transpose_s_hat(&s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, &eq_r_dprime);

    // Transparent weight vector rs_eq_ind = Phi(eq(r_suffix, .)).
    let rs_eq_ind = fold_ext_elems(&suffix_tensor, &eq_r_dprime);

    (
        RingSwitchProofK { s_hat_v },
        RingSwitchOutputK {
            rs_eq_ind,
            sumcheck_claim,
        },
    )
}

/// Verifier side of the reduction (dense: materializes `rs_eq_ind`).
///
/// Mirrors [`prove`]'s transcript exactly; returns `ClaimMismatch` if
/// `sum_i prefix_weights[i] * s_hat_v[i] != claim`.
pub fn verify<Ch: Challenger>(
    claim: F128T,
    prefix_weights: &[F128T],
    suffix_point: &[F128T],
    proof: &RingSwitchProofK,
    challenger: &mut Ch,
) -> Result<RingSwitchOutputK, VerifyErrorK> {
    assert_eq!(prefix_weights.len(), PACKING_WIDTH_K);
    assert_eq!(proof.s_hat_v.len(), PACKING_WIDTH_K);

    challenger.observe_label(b"flock-ring-switch-k-v0");
    observe_ext_slice(challenger, &proof.s_hat_v);

    if claim_check(prefix_weights, &proof.s_hat_v) != claim {
        return Err(VerifyErrorK::ClaimMismatch);
    }

    let r_dprime = sample_ext_vec(challenger, LOG_DEGREE_E);
    let eq_r_dprime = build_eq_table_ext(&r_dprime);

    let s_hat_u = transpose_s_hat(&proof.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, &eq_r_dprime);

    let suffix_tensor = build_eq_table_ext(suffix_point);
    let rs_eq_ind = fold_ext_elems(&suffix_tensor, &eq_r_dprime);

    Ok(RingSwitchOutputK {
        rs_eq_ind,
        sumcheck_claim,
    })
}

/// Polylog-cost verifier: same transcript as [`verify`] but does NOT build
/// the dense `rs_eq_ind`. Pair with [`eval_rs_eq_k`] at the Ligerito final
/// point (e.g. inside `recursive_verifier_with_basis_succinct_k`'s
/// `eval_b_residual` closure).
pub fn verify_succinct<Ch: Challenger>(
    claim: F128T,
    prefix_weights: &[F128T],
    proof: &RingSwitchProofK,
    challenger: &mut Ch,
) -> Result<RingSwitchVerifierOutputK, VerifyErrorK> {
    assert_eq!(prefix_weights.len(), PACKING_WIDTH_K);
    assert_eq!(proof.s_hat_v.len(), PACKING_WIDTH_K);

    challenger.observe_label(b"flock-ring-switch-k-v0");
    observe_ext_slice(challenger, &proof.s_hat_v);

    if claim_check(prefix_weights, &proof.s_hat_v) != claim {
        return Err(VerifyErrorK::ClaimMismatch);
    }

    let r_dprime = sample_ext_vec(challenger, LOG_DEGREE_E);
    let eq_r_dprime = build_eq_table_ext(&r_dprime);

    let s_hat_u = transpose_s_hat(&proof.s_hat_v);
    let sumcheck_claim = inner_product_base_ext(&s_hat_u, &eq_r_dprime);

    Ok(RingSwitchVerifierOutputK {
        sumcheck_claim,
        eq_r_dprime,
    })
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
/// the F_2-linear map sending basis bit w to `eq_r_dprime[w]`. So
///
/// ```text
/// MLE(rs_eq_ind)(q) = sum_y eq(q, y) * Phi(eq(z, y))
///                   = sum_w eq_r_dprime[w] * (sum_y A(y, w) * eq(q, y))
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
/// `eq_r_dprime`.
///
/// The rectangular twist vs. the old module: the fold length is e = 128
/// (the E-degree over F_2), not the packing width 64; the K side of the
/// reduction never appears here because `rs_eq_ind` is E-valued.
///
/// ## Arguments
///
/// * `z_vals`: the suffix point (`suffix_point` from [`prove`] / [`verify`]),
///   length L = m - 6.
/// * `query`: the Ligerito final challenges, length L, same coordinate order.
/// * `eq_r_dprime`: the eq tensor over the sampled `r''`, length 128 (from
///   [`RingSwitchVerifierOutputK`]).
pub fn eval_rs_eq_k(z_vals: &[F128T], query: &[F128T], eq_r_dprime: &[F128T]) -> F128T {
    assert_eq!(
        z_vals.len(),
        query.len(),
        "eval_rs_eq_k: z_vals and query must have equal length"
    );
    assert_eq!(
        eq_r_dprime.len(),
        DEGREE_E,
        "eval_rs_eq_k: eq_r_dprime length must be 128"
    );

    let mut eval = TensorAlgebraE::from_vertical(F128T::ONE);
    for (&z_i, &q_i) in z_vals.iter().zip(query.iter()) {
        let vert_scaled = eval.clone().scale_vertical(z_i);
        let hztl_scaled = eval.clone().scale_horizontal(q_i);
        eval += &vert_scaled;
        eval += &hztl_scaled;
    }
    eval.fold_vertical(eq_r_dprime)
}

/// Prefix-only variant of [`eval_rs_eq_k`]: walks `query_prefix.len()` of
/// the (z, query) pairs and returns the partially-evolved tensor element.
/// Pair with [`eval_rs_eq_finish_from_prefix_binary_q_k`] to share the
/// prefix across many residual positions (the succinct Ligerito closure).
pub fn eval_rs_eq_prefix_k(z_vals: &[F128T], query_prefix: &[F128T]) -> TensorAlgebraE {
    assert!(query_prefix.len() <= z_vals.len());
    let mut eval = TensorAlgebraE::from_vertical(F128T::ONE);
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
    z_vals_suffix: &[F128T],
    y_bits: u32,
    eq_r_dprime: &[F128T],
) -> F128T {
    assert_eq!(eq_r_dprime.len(), DEGREE_E);
    debug_assert!(z_vals_suffix.len() <= 32, "y_bits is u32; suffix > 32 not supported");
    let mut eval = prefix.clone();
    for (j, &z_i) in z_vals_suffix.iter().enumerate() {
        let scalar = if (y_bits >> j) & 1 == 1 { z_i } else { F128T::ONE + z_i };
        for e in eval.elems.iter_mut() {
            *e *= scalar;
        }
    }
    eval.fold_vertical(eq_r_dprime)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::challenger::FsChallenger;
    use crate::merkle::Hash;
    use crate::pcs::ligerito::{ProverConfig, VerifierConfig, default_config, default_verifier_config};
    use crate::pcs::ligerito_k::{
        LigeritoProofK, commit_k, k_configs_for, recursive_prover_with_basis_k, recursive_verifier_with_basis_k,
        recursive_verifier_with_basis_succinct_k,
    };
    use crate::pcs::pack_k::pack_witness_k;

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_ext(s: &mut u64) -> F128T {
        F128T::new(splitmix64(s), splitmix64(s))
    }

    fn rand_bits(m: usize, s: &mut u64) -> Vec<bool> {
        (0..1usize << m).map(|_| splitmix64(s) & 1 == 1).collect()
    }

    /// Reference s_hat_v: brute-force partial evaluation of each bit-column
    /// MLE at the suffix point (direct bit-extract loop, no fold kernel).
    fn s_hat_v_reference(packed: &[F64], suffix_point: &[F128T]) -> Vec<F128T> {
        let eq_suffix = build_eq_table_ext(suffix_point);
        (0..PACKING_WIDTH_K)
            .map(|i| {
                let mut acc = F128T::ZERO;
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
        let suffix_point: Vec<F128T> = (0..m - LOG_PACKING_K).map(|_| rand_ext(&mut s)).collect();
        let eq_suffix = build_eq_table_ext(&suffix_point);

        let s_hat_v = fold_1b_rows_k(&packed, &eq_suffix);
        assert_eq!(s_hat_v.len(), PACKING_WIDTH_K);

        // From the flat bit layout: column i is z[y * 64 + i].
        for i in 0..PACKING_WIDTH_K {
            let mut expected = F128T::ZERO;
            for (y, &w) in eq_suffix.iter().enumerate() {
                if bits[(y << LOG_PACKING_K) | i] {
                    expected += w;
                }
            }
            assert_eq!(s_hat_v[i], expected, "bit column {i}");
        }
        assert_eq!(s_hat_v, s_hat_v_reference(&packed, &suffix_point));
    }

    /// Claim-check completeness (a plain point claim verifies) and soundness
    /// (a wrong claim value or a tampered s_hat_v is rejected).
    #[test]
    fn claim_check_completeness_and_soundness() {
        let m = 10;
        let mut s = 2u64;
        let bits = rand_bits(m, &mut s);
        let packed = pack_witness_k(&bits, m);
        let point: Vec<F128T> = (0..m).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&point[..LOG_PACKING_K]);
        let suffix_point = &point[LOG_PACKING_K..];

        // Honest claim from the reference partials; sanity: it equals the
        // full bit-MLE evaluated with the full eq table.
        let s_ref = s_hat_v_reference(&packed, suffix_point);
        let claim = claim_check(&prefix_weights, &s_ref);
        let eq_full = build_eq_table_ext(&point);
        let mut direct = F128T::ZERO;
        for (x, &w) in eq_full.iter().enumerate() {
            if bits[x] {
                direct += w;
            }
        }
        assert_eq!(claim, direct, "prefix x suffix split must factor the MLE");

        let mut ch = FsChallenger::new(b"rs-k-claim-test");
        let (proof, _out) = prove(&packed, &prefix_weights, suffix_point, claim, &mut ch);

        let mut ch = FsChallenger::new(b"rs-k-claim-test");
        assert!(verify(claim, &prefix_weights, suffix_point, &proof, &mut ch).is_ok());

        // Wrong claim value.
        let bad_claim = claim + F128T::ONE;
        let mut ch = FsChallenger::new(b"rs-k-claim-test");
        assert_eq!(
            verify(bad_claim, &prefix_weights, suffix_point, &proof, &mut ch).unwrap_err(),
            VerifyErrorK::ClaimMismatch
        );
        let mut ch = FsChallenger::new(b"rs-k-claim-test");
        assert_eq!(
            verify_succinct(bad_claim, &prefix_weights, &proof, &mut ch).unwrap_err(),
            VerifyErrorK::ClaimMismatch
        );

        // Tampered s_hat_v.
        let mut bad = proof.clone();
        bad.s_hat_v[17].c0 ^= 1;
        let mut ch = FsChallenger::new(b"rs-k-claim-test");
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
        let tensor: Vec<F128T> = (0..1usize << 8).map(|_| rand_ext(&mut s)).collect();
        let eq_rdp: Vec<F128T> = (0..DEGREE_E).map(|_| rand_ext(&mut s)).collect();
        assert_eq!(fold_ext_elems(&tensor, &eq_rdp), fold_ext_elems_naive(&tensor, &eq_rdp));
    }

    /// eval_rs_eq_k must agree with the dense evaluation: materialize
    /// rs_eq_ind, evaluate its MLE at a random query with the eq table.
    /// Also pins the prefix + binary-q variant against the full path.
    #[test]
    fn eval_rs_eq_matches_dense() {
        let l = 6;
        let mut s = 4u64;
        let z: Vec<F128T> = (0..l).map(|_| rand_ext(&mut s)).collect();
        let r_dprime: Vec<F128T> = (0..LOG_DEGREE_E).map(|_| rand_ext(&mut s)).collect();
        let eq_rdp = build_eq_table_ext(&r_dprime);
        let rs_eq_ind = fold_ext_elems(&build_eq_table_ext(&z), &eq_rdp);

        let query: Vec<F128T> = (0..l).map(|_| rand_ext(&mut s)).collect();
        let eq_query = build_eq_table_ext(&query);
        let dense = inner_product_ext(&rs_eq_ind, &eq_query);

        assert_eq!(eval_rs_eq_k(&z, &query, &eq_rdp), dense);

        // Prefix + binary-q path: replace the last 3 query coords by the
        // bits of y and compare against the general path.
        let split = l - 3;
        let prefix = eval_rs_eq_prefix_k(&z, &query[..split]);
        for y in 0..8u32 {
            let mut q_bin = query[..split].to_vec();
            for j in 0..3 {
                q_bin.push(if (y >> j) & 1 == 1 { F128T::ONE } else { F128T::ZERO });
            }
            assert_eq!(
                eval_rs_eq_finish_from_prefix_binary_q_k(&prefix, &z[split..], y, &eq_rdp),
                eval_rs_eq_k(&z, &q_bin, &eq_rdp),
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
        let point: Vec<F128T> = (0..m).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&point[..LOG_PACKING_K]);
        let suffix_point = &point[LOG_PACKING_K..];
        let claim = claim_check(&prefix_weights, &s_hat_v_reference(&packed, suffix_point));

        let mut ch = FsChallenger::new(b"rs-k-identity-test");
        let (_proof, out) = prove(&packed, &prefix_weights, suffix_point, claim, &mut ch);
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
        prefix_weights: Vec<F128T>,
        suffix_point: Vec<F128T>,
        claim: F128T,
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

        let suffix_point: Vec<F128T> = (0..log_n).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights: Vec<F128T> = if generalized_weights {
            // Synthetic non-eq weights (e.g. standing in for phi_8 Lagrange
            // weights): any 64 E-values work.
            (0..PACKING_WIDTH_K).map(|_| rand_ext(&mut s)).collect()
        } else {
            let r_prefix: Vec<F128T> = (0..LOG_PACKING_K).map(|_| rand_ext(&mut s)).collect();
            eq_prefix_weights(&r_prefix)
        };
        let claim = claim_check(&prefix_weights, &s_hat_v_reference(&packed, &suffix_point));

        let mut ch = FsChallenger::new(E2E_DOMAIN);
        let (rs_proof, out) = prove(&packed, &prefix_weights, &suffix_point, claim, &mut ch);
        assert_eq!(inner_product_base_ext(&packed, &out.rs_eq_ind), out.sumcheck_claim);
        let lig_proof = recursive_prover_with_basis_k(
            &pc,
            packed,
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
        let mut ch = FsChallenger::new(E2E_DOMAIN);
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
        let mut ch = FsChallenger::new(E2E_DOMAIN);
        let out = match verify_succinct(e.claim, &e.prefix_weights, &e.rs_proof, &mut ch) {
            Ok(o) => o,
            Err(_) => return false,
        };
        let z = e.suffix_point.clone();
        let eq_rdp = out.eq_r_dprime.clone();
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
                    .map(|y| eval_rs_eq_finish_from_prefix_binary_q_k(&prefix, &z[split..], y, &eq_rdp))
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
        // downstream opening must still reject (r'' and the target diverge
        // from what the ligerito proof was built for).
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
        bad.claim = e.claim + F128T::ONE;
        assert!(!verify_e2e_dense(&bad), "tampered claim accepted");
        assert!(!verify_e2e_succinct(&bad), "tampered claim accepted (succinct)");
    }
}
