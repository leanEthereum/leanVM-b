// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! LCH novel-basis induction of the per-level sumcheck basis polynomial: the
//! dense per-query expansion, its succinct residual evaluator, and the sparse
//! transposed-NTT fast path with the dispatch between them.

use crate::ntt::AdditiveNttF64;
use crate::whir::build_eq_table_ext;
use primitives::field::{F64, F192};
use zk_alloc::ArenaVec;

// ===================================================================
// LCH novel-basis evaluations over K (mirror of whir's extension-field block)
// ===================================================================
//
// The subspace-polynomial recurrence runs entirely over the K evaluation
// domain (F64 values); results are lifted into E with `mul_base` only where
// they scale E-accumulators. Standard basis only (v_i = x^i = F64(1 << i)).

#[inline]
fn next_s(s: F64, s_at_root: F64) -> F64 {
    s * s + s_at_root * s
}

/// `sks_vks[k] = s_k(v_k)` for `k = 0..=log_n`, over K. Mirror of
/// `whir::eval_sk_at_vks`. Public for the recursion harness, which dumps
/// these vanishing-polynomial values as guest hints (base-field, embedded into
/// the tower with both extension limbs zero).
pub fn eval_sk_at_vks(log_n: usize) -> Vec<F64> {
    let mut sks_vks = vec![F64::ZERO; log_n + 1];
    sks_vks[0] = F64::ONE;
    if log_n == 0 {
        return sks_vks;
    }
    let mut layer: Vec<F64> = (1..=log_n).map(|i| F64(1u64 << i)).collect();
    let mut cur_len = log_n;
    for i in 0..log_n {
        for j in 0..cur_len {
            let sk_at_vk = next_s(layer[j], sks_vks[i]);
            if j == 0 {
                sks_vks[i + 1] = sk_at_vk;
            } else {
                layer[j - 1] = sk_at_vk;
            }
        }
        cur_len -= 1;
    }
    sks_vks
}

/// `out[i] = W-hat_i(x) = s_i(x) / s_i(v_i)`, the normalized LCH basis
/// exponents at the K point `x`. Stays entirely in K.
fn normalized_sks_at(x: F64, sks_vks: &[F64], inv_sks_vks: &[F64], out: &mut [F64]) {
    if out.is_empty() {
        return;
    }
    out[0] = x;
    for i in 1..out.len() {
        out[i] = next_s(out[i - 1], sks_vks[i - 1]);
    }
    for (v, &inv) in out.iter_mut().zip(inv_sks_vks) {
        *v *= inv;
    }
}

/// Write into `basis` the normalized LCH novel-basis polynomials evaluated at
/// `x` (a K point), each scaled by the E-value `alpha`. The `sks_at_x`
/// recurrence stays in K; the basis expansion lifts into E via `mul_base`.
fn evaluate_scaled_basis_inplace(
    sks_at_x: &mut [F64],
    basis: &mut [F192],
    sks_vks: &[F64],
    inv_sks_vks: &[F64],
    x: F64,
    alpha: F192,
) {
    let log_n = basis.len().trailing_zeros() as usize;
    debug_assert_eq!(basis.len(), 1 << log_n);
    debug_assert!(sks_at_x.len() >= log_n);
    debug_assert!(inv_sks_vks.len() > log_n);

    normalized_sks_at(x, sks_vks, inv_sks_vks, &mut sks_at_x[..log_n]);

    basis[0] = alpha;
    for k in 0..log_n {
        let s_at_x = sks_at_x[k];
        let current_len = 1 << k;
        for i in 0..current_len {
            basis[i + current_len] = basis[i].mul_base(s_at_x);
        }
    }
}

/// Row entries of an opened level: `F64` at L0 (mixed `mul_base` dot against
/// the E-valued eq weights), `F192` at every deeper level (full E dot).
pub(crate) trait RowElem: Copy + Sync {
    fn dot(row: &[Self], eq: &[F192]) -> F192;
}

impl RowElem for F64 {
    #[inline]
    fn dot(row: &[Self], eq: &[F192]) -> F192 {
        row.iter()
            .zip(eq.iter())
            .map(|(&r, &e)| e.mul_base(r))
            .fold(F192::ZERO, |a, v| a + v)
    }
}

impl RowElem for F192 {
    #[inline]
    fn dot(row: &[Self], eq: &[F192]) -> F192 {
        row.iter()
            .zip(eq.iter())
            .map(|(&r, &e)| r * e)
            .fold(F192::ZERO, |a, v| a + v)
    }
}

/// `eq(alpha, i)` for `i < n_queries`: the per-query batching weights. `alpha`
/// carries `ceil(log2(n_queries))` challenges, so the eq table always covers
/// the queries.
fn alpha_weights(alpha: &[F192], n_queries: usize) -> Vec<F192> {
    if n_queries == 0 {
        return Vec::new();
    }
    let table = build_eq_table_ext(alpha);
    debug_assert!(table.len() >= n_queries);
    table.into_iter().take(n_queries).collect()
}

fn invert_sks(sks_vks: &[F64]) -> Vec<F64> {
    sks_vks
        .iter()
        .map(|&v| if v.is_zero() { F64::ZERO } else { v.inv() })
        .collect()
}

/// Dense induce: `basis_poly[j] = Σ_i eq(α, i) · W-hat_j(q_i)`,
/// `enforced_sum = Σ_i eq(α, i) · <row_i, eq(v_challenges, ·)>`. Mirror of the
/// dense `whir::induce_sumcheck_poly` (per-thread chunked accumulation).
pub(crate) fn induce_sumcheck_poly<T: RowElem>(
    log_msg_cols: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    alpha: &[F192],
) -> (ArenaVec<F192>, F192) {
    let n = 1usize << log_msg_cols;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);
    debug_assert_eq!(
        v_challenges.len(),
        opened_rows
            .first()
            .map(|r| r.len().trailing_zeros() as usize)
            .unwrap_or(0)
    );

    let eq = build_eq_table_ext(v_challenges);
    let alpha_pows = alpha_weights(alpha, n_queries);
    let inv_sks_vks = invert_sks(sks_vks);

    let n_threads = parallel::num_threads();
    let chunk_size = (n_queries + n_threads - 1) / n_threads.max(1);

    let partials: Vec<(Vec<F192>, F192)> = parallel::map_collect(n_threads, |t| {
        let start = t * chunk_size;
        let end = (start + chunk_size).min(n_queries);
        if start >= end {
            return (vec![F192::ZERO; n], F192::ZERO);
        }
        let mut accum_basis = vec![F192::ZERO; n];
        let mut local_basis = vec![F192::ZERO; n];
        let mut sks_at_x = vec![F64::ZERO; log_msg_cols.max(1)];
        let mut local_sum = F192::ZERO;

        for i in start..end {
            let ap = alpha_pows[i];
            local_sum += T::dot(&opened_rows[i], &eq) * ap;

            let q_field = F64(queries[i] as u64);
            evaluate_scaled_basis_inplace(&mut sks_at_x, &mut local_basis, sks_vks, &inv_sks_vks, q_field, ap);
            for (acc, &v) in accum_basis.iter_mut().zip(local_basis.iter()) {
                *acc += v;
            }
        }
        (accum_basis, local_sum)
    });

    // SAFETY: zero is a valid F192, and the accumulate loop below reads it.
    let mut basis_poly = unsafe { ArenaVec::<F192>::zeroed(n) };
    let mut enforced_sum = F192::ZERO;
    for (lb, ls) in partials {
        for (acc, &v) in basis_poly.iter_mut().zip(lb.iter()) {
            *acc += v;
        }
        enforced_sum += ls;
    }

    (basis_poly, enforced_sum)
}

/// Just the `enforced_sum` half of [`induce_sumcheck_poly`]:
///   `enforced_sum = Σ_i eq(α, i) · <opened_rows[i], eq(v_challenges, ·)>`
/// Cheap: O(num_queries x num_interleaved). The succinct verifier needs this
/// at level intro time (before the residual challenges are known).
pub(crate) fn induce_sumcheck_enforced_sum<T: RowElem>(
    opened_rows: &[Vec<T>],
    v_challenges: &[F192],
    queries: &[usize],
    alpha: &[F192],
) -> F192 {
    assert_eq!(opened_rows.len(), queries.len());
    let eq = build_eq_table_ext(v_challenges);
    let weights = alpha_weights(alpha, queries.len());
    let mut sum = F192::ZERO;
    for (i, row) in opened_rows.iter().enumerate() {
        debug_assert_eq!(row.len(), eq.len());
        sum += weights[i] * T::dot(row, &eq);
    }
    sum
}

/// SUCCINCT evaluator for the induced basis poly's MLE at residual points
/// (mirror of `whir::induce_sumcheck_evaluate_at_residual`). Replaces the
/// dense basis + `partial_eval_lsb` in the verifier via the closed form:
///   `MLE(basis_poly)(p) = Σ_i eq(α, i) · Π_k (1 + p[k] · (1 + W-hat_k(q_i)))`
/// where `q_i = F64(queries[i])` and the K-valued `W-hat_k(q_i)` lifts into E
/// through the char-2 factor. `ris_for_basis` is the fixed residual prefix
/// (length `log_msg_cols - yr_log_n`); returns evaluations at the `2^yr_log_n`
/// points `ris_for_basis ++ y_bits`.
pub(crate) fn induce_sumcheck_evaluate_at_residual(
    log_msg_cols: usize,
    sks_vks: &[F64],
    queries: &[usize],
    alpha: &[F192],
    ris_for_basis: &[F192],
    yr_log_n: usize,
) -> ArenaVec<F192> {
    assert_eq!(ris_for_basis.len() + yr_log_n, log_msg_cols);
    let n_queries = queries.len();
    let yr_len = 1usize << yr_log_n;

    let alpha_pows = alpha_weights(alpha, n_queries);
    let inv_sks_vks = invert_sks(sks_vks);
    let prefix_len = ris_for_basis.len();

    // Per-query precomputation: W-hat_k(q) for all k over K, split into a
    // fixed prefix product (E scalar) and the suffix W-hat values varied per y.
    struct PerQuery {
        prefix_prod: F192,
        suffix_w: Vec<F64>, // length = yr_log_n
    }
    let compute_query = |&q: &usize| -> PerQuery {
        let mut sks_at_x = vec![F64::ZERO; log_msg_cols];
        normalized_sks_at(F64(q as u64), sks_vks, &inv_sks_vks, &mut sks_at_x);
        // Prefix product: Π_{k<prefix_len} (1 + ris[k] · (1 + W-hat_k(q)))
        let mut prefix_prod = F192::ONE;
        for k in 0..prefix_len {
            prefix_prod *= F192::ONE + ris_for_basis[k] * (F192::ONE + F192::from(sks_at_x[k]));
        }
        let suffix_w = if log_msg_cols > prefix_len {
            sks_at_x[prefix_len..].to_vec()
        } else {
            Vec::new()
        };
        PerQuery { prefix_prod, suffix_w }
    };
    // Once per recursion level over verify-sized inputs; stay serial below
    // the dispatch crossover (mirror of the original's PAR_FLOOR).
    const PAR_FLOOR: usize = 1024;
    let per_query: Vec<PerQuery> = if n_queries > PAR_FLOOR {
        parallel::map_collect(n_queries, |i| compute_query(&queries[i]))
    } else {
        queries.iter().map(compute_query).collect()
    };

    // For each residual position y, accumulate the suffix product per query.
    let compute_y = |y: usize| -> F192 {
        let mut sum = F192::ZERO;
        for i in 0..n_queries {
            let pq = &per_query[i];
            let mut suffix_prod = F192::ONE;
            for j in 0..yr_log_n {
                let p_j = if (y >> j) & 1 == 1 { F192::ONE } else { F192::ZERO };
                suffix_prod *= F192::ONE + p_j * (F192::ONE + F192::from(pq.suffix_w[j]));
            }
            sum += alpha_pows[i] * pq.prefix_prod * suffix_prod;
        }
        sum
    };
    if yr_len > PAR_FLOOR {
        <ArenaVec<F192> as primitives::ParCollectArena<F192>>::par_collect(yr_len, compute_y)
    } else {
        (0..yr_len).map(compute_y).collect()
    }
}

/// Transposed forward additive NTT, `F^T`, in place over `2^log_d` E-values
/// with K-twiddles. Forward butterfly is `M = [[1, t], [1, t+1]]`; transpose
/// `M^T = [[1, 1], [t, t+1]]` is `s = a + b; top = s; bot = t*s + b` (here
/// `s.mul_base(t) + b`), applied in reverse layer order. Mirror of
/// `whir::transpose_forward_ntt` (one parallel sweep per layer).
fn transpose_forward_ntt_ext(ntt: &AdditiveNttF64, data: &mut [F192], log_d: usize) {
    debug_assert_eq!(data.len(), 1usize << log_d);
    debug_assert!(log_d <= ntt.log_domain_size());
    transpose_layers_ext(ntt, data, log_d, (0..log_d).rev());
}

/// The transposed-butterfly sweep over `layers`, in the order given: parallel
/// over blocks once there are enough of them, over rows within a block
/// otherwise.
fn transpose_layers_ext(ntt: &AdditiveNttF64, data: &mut [F192], log_d: usize, layers: impl Iterator<Item = usize>) {
    let n_threads = parallel::num_threads();
    let butterfly = |t: F64, top: &mut [F192], bot: &mut [F192]| {
        for (a_ref, b_ref) in top.iter_mut().zip(bot.iter_mut()) {
            let a = *a_ref;
            let b = *b_ref;
            let s = a + b;
            *a_ref = s;
            *b_ref = s.mul_base(t) + b;
        }
    };
    for layer in layers {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let bsh = block_size >> 1;
        if num_blocks >= n_threads {
            parallel::chunks_mut(data, block_size, |block, chunk: &mut [F192]| {
                let (top, bot) = chunk.split_at_mut(bsh);
                butterfly(ntt.twiddle(layer, block), top, bot);
            });
        } else {
            for block in 0..num_blocks {
                let t = ntt.twiddle(layer, block);
                let chunk = &mut data[block * block_size..(block + 1) * block_size];
                let (top, bot) = chunk.split_at_mut(bsh);
                let chunk_len = parallel::recommended_chunk_size(bsh);
                parallel::chunks_mut2(top, bot, chunk_len, |_, top_c, bot_c| butterfly(t, top_c, bot_c));
            }
        }
    }
}

/// Sparse-prefix variant of [`transpose_forward_ntt_ext`]: the input has only
/// `positions.len()` nonzeros and the first `k` transpose steps (forward
/// layers `log_d-1 .. log_d-k`, pairing distances `1 .. 2^(k-1)`) mix only
/// WITHIN `2^k`-aligned windows. We process just the windows that contain a
/// nonzero (a dense `2^k` transpose each, disjoint so window-parallel),
/// densify, then run the remaining steps as full dense sweeps. Output is
/// identical to `transpose_forward_ntt_ext` on the scattered input. Mirror
/// of `whir::transpose_forward_ntt_sparse`.
fn transpose_forward_ntt_sparse_ext(
    ntt: &AdditiveNttF64,
    positions: &[usize],
    values: &[F192],
    log_d: usize,
) -> Vec<F192> {
    let _span = tracing::info_span!(
        "NTT",
        kind = "transpose induce",
        log_domain = log_d,
        nonzero = positions.len()
    )
    .entered();
    use std::collections::HashMap;
    let n = 1usize << log_d;
    // No prefix for small domains: just scatter + full dense transpose.
    let k = if log_d >= 12 { 8usize.min(log_d) } else { 0 };

    if k == 0 {
        let mut data = vec![F192::ZERO; n];
        for (&p, &v) in positions.iter().zip(values) {
            data[p] += v;
        }
        if log_d > 0 {
            transpose_forward_ntt_ext(ntt, &mut data, log_d);
        }
        return data;
    }

    let wmask = (1usize << k) - 1;
    // Group nonzeros into 2^k windows.
    let mut windows: HashMap<usize, Vec<F192>> = HashMap::new();
    for (&p, &v) in positions.iter().zip(values) {
        let buf = windows.entry(p >> k).or_insert_with(|| vec![F192::ZERO; 1 << k]);
        buf[p & wmask] += v;
    }

    // Steps s = 0..k-1 within each active window, in parallel (windows disjoint).
    let mut win_vec: Vec<(usize, Vec<F192>)> = windows.into_iter().collect();
    parallel::chunks_mut(&mut win_vec, 1, |_, win| {
        let (w, buf) = &mut win[0];
        let w = *w;
        for s in 0..k {
            let layer = log_d - 1 - s;
            let bsh = 1usize << s; // pairing distance
            let block_size = bsh << 1;
            let nblocks = (1usize << k) / block_size;
            for jb in 0..nblocks {
                // global block index = ((w<<k) + jb*block_size) >> (s+1).
                let t = ntt.twiddle(layer, (w << (k - s - 1)) + jb);
                let base = jb * block_size;
                for r in 0..bsh {
                    let a = buf[base + r];
                    let b = buf[base + r + bsh];
                    let sab = a + b;
                    buf[base + r] = sab;
                    buf[base + r + bsh] = sab.mul_base(t) + b;
                }
            }
        }
    });

    // Densify (active windows only; the rest stay zero, which is the correct
    // post-step-(k-1) state for an all-zero window).
    let mut data = vec![F192::ZERO; n];
    for (w, buf) in &win_vec {
        data[(w << k)..((w + 1) << k)].copy_from_slice(buf);
    }

    // Remaining steps s = k..log_d-1 = forward layers (log_d-1-k) .. 0, dense.
    transpose_layers_ext(ntt, &mut data, log_d, (0..(log_d - k)).rev());
    data
}

/// `F^T`-based fast path for [`induce_sumcheck_poly`]: scatter per-query
/// E-weights into the codeword domain, apply `F^T` with K-twiddles, keep the
/// low `2^log_msg_cols` outputs. Byte-identical output to the dense path
/// (pinned by `induce_via_ntt_matches_dense`). Mirror of
/// `whir::induce_sumcheck_poly_via_ntt` with the L0 mixed row dot.
pub(crate) fn induce_sumcheck_poly_via_ntt_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    opened_rows: &[Vec<F64>],
    v_challenges: &[F192],
    queries: &[usize],
    alpha: &[F192],
) -> (ArenaVec<F192>, F192) {
    let n = 1usize << log_msg_cols;
    let log_block = log_msg_cols + log_inv_rate;
    let block_len = 1usize << log_block;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);

    let eq = build_eq_table_ext(v_challenges);
    let alpha_pows = alpha_weights(alpha, n_queries);

    let mut enforced_sum = F192::ZERO;
    for i in 0..n_queries {
        enforced_sum += F64::dot(&opened_rows[i], &eq) * alpha_pows[i];
    }

    let mut coeffs = if log_block == 0 {
        // SAFETY: zero is a valid F192, and the loop below reads these slots.
        let mut c = unsafe { ArenaVec::<F192>::zeroed(block_len) };
        for i in 0..n_queries {
            c[queries[i]] += alpha_pows[i];
        }
        c
    } else {
        let ntt = AdditiveNttF64::standard(log_block);
        ArenaVec::from_slice(&transpose_forward_ntt_sparse_ext(&ntt, queries, &alpha_pows, log_block))
    };
    coeffs.truncate(n);
    (coeffs, enforced_sum)
}

/// The original's cost-based dispatch heuristic, verbatim: the dense path
/// costs `O(n_queries * 2^log_msg_cols)`, the NTT path one pass over the
/// `2^log_block` codeword domain, so the NTT wins exactly when
/// `n_queries > 4 * 2^log_inv_rate * log_block`. Same constants as the
/// original so both field versions choose the same strategy at the same
/// shapes.
#[inline]
pub(crate) fn induce_use_ntt_heuristic(log_msg_cols: usize, log_inv_rate: usize, n_queries: usize) -> bool {
    let log_block = log_msg_cols + log_inv_rate;
    log_msg_cols >= 12 && n_queries > 4 * (1usize << log_inv_rate) * log_block.max(1)
}

/// Dispatch between the dense [`induce_sumcheck_poly`] and the sparse
/// [`induce_sumcheck_poly_via_ntt_base`] for L0 (base-field rows). Mirror of
/// `whir::induce_sumcheck_poly_auto`: in the recursive PCS this fires
/// only at the top level (large message domain, many queries); deeper levels
/// stay dense. Both paths produce identical output, so a mis-dispatch only
/// costs time.
pub(crate) fn induce_sumcheck_poly_auto_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<F64>],
    v_challenges: &[F192],
    queries: &[usize],
    alpha: &[F192],
) -> (ArenaVec<F192>, F192) {
    if induce_use_ntt_heuristic(log_msg_cols, log_inv_rate, queries.len()) {
        induce_sumcheck_poly_via_ntt_base(log_msg_cols, log_inv_rate, opened_rows, v_challenges, queries, alpha)
    } else {
        induce_sumcheck_poly(log_msg_cols, sks_vks, opened_rows, v_challenges, queries, alpha)
    }
}
