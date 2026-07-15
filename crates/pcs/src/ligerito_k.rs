// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Ligerito over K = GF(2^64): commit in the base field, challenge in the tower.
//!
//! The committed message is a
//! vector of [`F64`] values; every verifier challenge, sumcheck message, basis
//! poly, and post-fold witness lives in E = GF(2^128) represented as the
//! degree-2 tower [`F128T`] over the very same K.
//!
//! Type map relative to the original:
//! - committed message / L0 codeword / L0 opened rows: `F64` (8 bytes)
//! - challenges, sumcheck messages, folded witnesses, deeper-level codewords
//!   and opened rows, `b_initial`, betas, alphas, `yr`: `F128T` (16 bytes)
//! - the RS-encoding evaluation domain and all LCH twiddles stay in K, so the
//!   deeper-level (E-valued) encodes use K-twiddles via the mixed product
//!   [`F128T::mul_base`] (2 PMULL) instead of a full E multiplication.
//!
//! Deliberate divergences from the original (each noted inline too):
//! - OOD sampling is NOT ported. The `Secure` (UDR) profile that drives this
//!   port takes zero OOD samples at every level (unique-decoding list size 1);
//!   the prover/verifier assert `ood_samples == 0` instead of carrying the
//!   branches.
//! - Buffers use plain `Vec` allocation where the original recycles through
//!   `crate::scratch` (no F64/F128T pool exists yet).
//! - The prover/commit timing instrumentation answers to `LIG_K_TRACE`
//!   (instead of the original's `LIG_PROVE_TRACE` / `FLOCK_COMMIT_TIMING`).
//!
//! Basis induction mirrors the original's two strategies: the dense
//! per-query LCH expansion and the sparse transposed-NTT fast path
//! ([`induce_sumcheck_poly_via_ntt_base`]), with the SAME auto-dispatch size
//! heuristic at L0 (deeper levels stay dense, exactly like the original).
//!
//! Soundness note: the configs use [`LigeritoSecurityConfig`] with
//! `analysis q = 2^128`.
//! The challenge field here is also 2^128-sized, and the shape parameters are
//! field-agnostic, so the reuse is coherent; still, the K parameterization
//! (base-field alphabet in the interleaved code, tower-sampling details) gets
//! its own soundness derivation later. See [`k_configs_for`].

use fiat_shamir::Sponge;
use primitives::field::{F64, F128T, F128TBaseUnreduced, F128TUnreduced};
use crate::merkle::{self, Hash};
use crate::ntt::AdditiveNttF64;
use serde::{Deserialize, Serialize};

use super::ligerito::{LigeritoSecurityConfig, ProverConfig, VerifierConfig, log2_ceil};

// ===================================================================
// Sponge helpers: E = F128T straight off the shared Fiat-Shamir sponge
// ===================================================================
//
// The sponge's scalars ARE E-elements (two K-lanes per 16 transcript bytes),
// so sampling/observing here is the sponge API verbatim; the helpers only
// keep the K files' call sites uniform.

#[inline]
fn sample_ext(sponge: &mut Sponge) -> F128T {
    sponge.sample()
}

fn sample_ext_vec(sponge: &mut Sponge, n: usize) -> Vec<F128T> {
    sponge.sample_vec(n)
}

#[inline]
fn observe_ext(sponge: &mut Sponge, e: F128T) {
    sponge.observe(e);
}


/// Bind a Merkle root into the transcript as two `F128T` scalars rather than
/// as a byte string. Binds the root before any challenge exactly as `absorb_bytes`
/// would; keeping the scalar form matches the recursion guest's replay.
fn observe_root(sponge: &mut Sponge, root: &crate::merkle::Hash) {
    for s in crate::merkle::hash_to_scalars(root) {
        observe_ext(sponge, s);
    }
}

// ===================================================================
// Multilinear helpers over E
// ===================================================================

/// Build the eq-MLE table at `point` in E^d, LSB-first: mirror of
/// `lincheck::build_eq_table` with F128T arithmetic.
pub fn build_eq_table_ext(point: &[F128T]) -> Vec<F128T> {
    let d = point.len();
    let mut out: Vec<F128T> = Vec::with_capacity(1usize << d);
    out.push(F128T::ONE);
    for j in 0..d {
        let r_j = point[j];
        let one_plus_r_j = F128T::ONE + r_j;
        let len = 1usize << j;
        out.resize(2 * len, F128T::ZERO);
        for i in 0..len {
            let v = out[i];
            out[i + len] = v * r_j;
            out[i] = v * one_plus_r_j;
        }
    }
    out
}

/// Parallel mirror of [`build_eq_table_ext`]: identical LSB-first doubling
/// recurrence, byte-identical output, with each level's independent
/// iterations fanned out across rayon threads once the level is large enough
/// to amortize dispatch. Structure copied from the extension-field layer's
/// `ring_switch::build_eq_parallel`.
pub fn build_eq_table_ext_parallel(point: &[F128T]) -> Vec<F128T> {
    // Uninit alloc: the doubling below writes every slot before any is read
    // (level j reads out[..2^j], all written earlier, and writes
    // out[2^j..2^(j+1)] fresh).
    let mut out: Vec<F128T> = primitives::alloc_uninit_vec(1usize << point.len());
    build_eq_table_ext_seeded_into(point, F128T::ONE, &mut out);
    out
}

/// In-place seeded core of [`build_eq_table_ext_parallel`]: fills
/// `out[..2^point.len()]` with `seed * eq(point, .)`.
///
/// Seeding folds a batching scalar into the table for free: every entry is
/// `seed` times a product of point factors, and field multiplication is
/// exact and associative, so the result equals the post-multiplied table
/// byte for byte while skipping one full multiply pass. `out` must have
/// length exactly `2^point.len()`; every slot is written before any is read,
/// so an uninit or reused scratch buffer is fine.
pub fn build_eq_table_ext_seeded_into(point: &[F128T], seed: F128T, out: &mut [F128T]) {
    use rayon::prelude::*;
    let n = point.len();
    assert_eq!(out.len(), 1usize << n, "out must have length 2^point.len()");
    out[0] = seed;
    // Threshold below which rayon dispatch overhead beats the parallel work
    // (same floor as the extension-field layer's `build_eq_parallel`).
    const PAR_THRESHOLD: usize = 1 << 12;
    for j in 0..n {
        let r_j = point[j];
        let one_plus_r_j = F128T::ONE + r_j;
        let half = 1usize << j;
        let (lo, hi_rest) = out.split_at_mut(half);
        let hi = &mut hi_rest[..half];
        if half < PAR_THRESHOLD {
            for (lo_x, hi_x) in lo.iter_mut().zip(hi.iter_mut()) {
                let v = *lo_x;
                *hi_x = v * r_j;
                *lo_x = v * one_plus_r_j;
            }
        } else {
            lo.par_iter_mut()
                .zip(hi.par_iter_mut())
                .for_each(|(lo_x, hi_x)| {
                    let v = *lo_x;
                    *hi_x = v * r_j;
                    *lo_x = v * one_plus_r_j;
                });
        }
    }
}

/// Partially evaluate the multilinear extension of `evals` at the first
/// `rs.len()` (LSB) variables. Mirror of `ligerito::partial_eval_lsb`.
pub(crate) fn partial_eval_lsb_ext(evals: &[F128T], rs: &[F128T]) -> Vec<F128T> {
    let mut cur = evals.to_vec();
    for &r in rs {
        let one_plus_r = F128T::ONE + r;
        let half = cur.len() / 2;
        let mut next = Vec::with_capacity(half);
        for i in 0..half {
            next.push(cur[2 * i] * one_plus_r + cur[2 * i + 1] * r);
        }
        cur = next;
    }
    cur
}

/// Mixed inner product `Σ_i b[i] · witness[i]` (E x K via `mul_base`). The
/// evaluation-claim `target` for a K-witness against an E-basis.
pub fn inner_product_base_ext(witness: &[F64], b: &[F128T]) -> F128T {
    use rayon::prelude::*;
    assert_eq!(witness.len(), b.len());
    const PAR_THRESHOLD: usize = 4096;
    if witness.len() < PAR_THRESHOLD {
        return witness
            .iter()
            .zip(b.iter())
            .map(|(&w, &e)| e.mul_base(w))
            .fold(F128T::ZERO, |a, v| a + v);
    }
    witness
        .par_iter()
        .zip(b.par_iter())
        .with_min_len(PAR_THRESHOLD / 4)
        .map(|(&w, &e)| e.mul_base(w))
        .reduce(|| F128T::ZERO, |a, v| a + v)
}

#[inline]
fn log2_pow2(n: usize) -> usize {
    assert!(
        n.is_power_of_two() && n > 0,
        "length must be a positive power of 2"
    );
    n.trailing_zeros() as usize
}

// ===================================================================
// Config reuse
// ===================================================================

/// Derive `(ProverConfig, VerifierConfig)` for a K-witness of `2^log_n` F64
/// elements, reusing the extension-field-era `Secure` profile at `m = log_n + LOG_PACKING`
/// exactly like the main crate does for its packed witnesses.
///
/// NOTE: the soundness constants behind `derive_config` (query counts,
/// fold-grinding bits, the `q = 2^128` analysis) are extension-field-era. E here is also
/// 2^128-sized and the config is shape-only, but the K parameterization gets
/// its own soundness derivation later; treat these numbers as provisional.
pub fn k_configs_for(log_n: usize) -> Result<(ProverConfig, VerifierConfig), String> {
    let sec = LigeritoSecurityConfig::derive_config(log_n + crate::LOG_PACKING)?;
    sec.to_prover_verifier_configs()
}

// ===================================================================
// Commit: F64 message -> interleaved RS codeword -> Merkle root
// ===================================================================

/// Public commitment for a K-message: the L0 Merkle root plus the shape
/// parameters needed to re-derive block lengths. The extension-field path's `Commitment`
/// carries a full `PcsParams` (packing- and profile-aware), which does not
/// apply to a raw K-message, so this port defines its own minimal type.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommitmentK {
    pub root: Hash,
    /// log2 of the committed message length in F64 elements.
    pub log_msg_len: usize,
    /// Lanes per Merkle leaf (log2); must equal the Ligerito `initial_k`.
    pub log_batch_size: usize,
    pub log_inv_rate: usize,
}

/// Prover-side state retained after commit for the opening phase. The message
/// itself is NOT stored (mirror of the extension-field `ProverData` contract).
pub struct ProverDataK {
    pub codeword: Vec<F64>,
    pub merkle_tree: Vec<Hash>,
}

/// Fill `codeword` with `2^r` replicas of `msg`: the exact state after the
/// first `r` forward-NTT layers on the zero-padded coefficient vector
/// `[msg, 0, ..., 0]`. Pair with `forward_transform_*_from_layer(.., r)`.
/// Mirror of `commit::replicate_message_fill`, generic over the element type.
fn replicate_message_fill_t<T: Copy + Send + Sync>(codeword: &mut [T], msg: &[T]) {
    use rayon::prelude::*;
    let msg_len = msg.len();
    debug_assert!(codeword.len().is_multiple_of(msg_len));
    const COPY_CHUNK: usize = 1 << 16;
    if msg_len >= COPY_CHUNK {
        // Both are powers of two, so chunks never straddle a replica boundary.
        codeword
            .par_chunks_mut(COPY_CHUNK)
            .enumerate()
            .for_each(|(i, dst)| {
                let src_off = (i * COPY_CHUNK) % msg_len;
                dst.copy_from_slice(&msg[src_off..src_off + dst.len()]);
            });
    } else {
        for rep in codeword.chunks_mut(msg_len) {
            rep.copy_from_slice(msg);
        }
    }
}

/// Commit to a K-message (mirror of `commit::commit` / `finalize_commit`):
/// replicate the message `2^log_inv_rate` times, run the interleaved additive
/// NTT over F_{2^64} from layer `log_inv_rate`, then Merkle-commit one leaf
/// per codeword position (= `2^log_batch_size` F64 = `2^log_batch_size * 8`
/// bytes per leaf).
///
/// `message.len()` must be a power of two `>= 2^log_batch_size`.
pub fn commit_k(
    message: &[F64],
    log_batch_size: usize,
    log_inv_rate: usize,
) -> (CommitmentK, ProverDataK) {
    let log_msg_len = log2_pow2(message.len());
    assert!(
        log_msg_len >= log_batch_size,
        "message too small for log_batch_size"
    );
    assert!(
        log_inv_rate >= 1,
        "log_inv_rate must be >= 1 for a non-trivial RS code"
    );
    let log_dim = log_msg_len - log_batch_size;
    let k_code = log_dim + log_inv_rate;
    let num_ntts = 1usize << log_batch_size;
    let n_positions = 1usize << k_code;
    let codeword_len = n_positions * num_ntts;

    // Plain allocation: the extension-field path routes this buffer through the scratch
    // pool; no F64 pool exists (yet). Every slot is written by the replicate
    // fill below, so uninit is fine.
    let mut codeword: Vec<F64> = primitives::alloc_uninit_vec(codeword_len);
    replicate_message_fill_t(&mut codeword, message);

    // Optional phase timing (LIG_K_TRACE): one env lookup per commit, no
    // work when unset.
    let trace = std::env::var_os("LIG_K_TRACE").is_some();
    let t_ntt = std::time::Instant::now();
    let ntt = AdditiveNttF64::standard(k_code);
    ntt.forward_transform_interleaved_from_layer(&mut codeword, num_ntts, log_inv_rate);
    let ntt_elapsed = t_ntt.elapsed();
    let t_merkle = std::time::Instant::now();

    // Merkle commitment, zero-copy over the codeword bytes.
    // SAFETY: F64 is repr(transparent) over u64; a `[F64]` slice is therefore
    // a contiguous little-endian u64 byte image (8 bytes each), identical to
    // an explicit `to_le_bytes()` serialization on this (LE) target. The cast
    // covers exactly `codeword.len() * size_of::<F64>()` initialized bytes.
    let codeword_bytes: &[u8] = unsafe {
        core::slice::from_raw_parts(
            codeword.as_ptr() as *const u8,
            codeword.len() * core::mem::size_of::<F64>(),
        )
    };
    let merkle_tree = merkle::merkle_tree(codeword_bytes, n_positions);
    let root = *merkle_tree.last().expect("merkle tree non-empty");
    if trace {
        eprintln!(
            "[lig-k-commit] k_code={k_code} lanes={num_ntts}: ntt = {:.4} s, merkle = {:.4} s",
            ntt_elapsed.as_secs_f64(),
            t_merkle.elapsed().as_secs_f64(),
        );
    }

    (
        CommitmentK {
            root,
            log_msg_len,
            log_batch_size,
            log_inv_rate,
        },
        ProverDataK {
            codeword,
            merkle_tree,
        },
    )
}

// ===================================================================
// Interleaved forward additive NTT over E with K-twiddles
// ===================================================================
//
// Deeper Ligerito levels RS-encode an E-valued (folded) witness on the SAME
// K-domain: the twiddles are F64, and each butterfly multiply is the mixed
// product `v.mul_base(twiddle)` (2 PMULL). Structure copied from
// `ntt::additive_ntt_f64`'s interleaved transform, with constants re-derived
// for 16-byte elements.

pub(crate) fn forward_transform_interleaved_ext_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F128T],
    num_ntts: usize,
    start_layer: usize,
) {
    assert!(num_ntts.is_power_of_two() && num_ntts > 0);
    let n_total = data.len();
    assert_eq!(n_total % num_ntts, 0);
    let log_d = log2_pow2(n_total / num_ntts);
    assert!(log_d <= ntt.log_domain_size());
    assert!(start_layer <= log_d);

    forward_transform_interleaved_ext_parallel_from_layer(ntt, data, num_ntts, start_layer);
}

/// Scalar reference for the E-valued interleaved forward NTT (test oracle and
/// small-input path).
fn forward_transform_interleaved_ext_scalar_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F128T],
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
            let twiddle = ntt.twiddle(layer, block);
            let block_start = block * block_elems;
            for row in 0..block_size_half {
                let off_top = block_start + row * num_ntts;
                let off_bot = off_top + block_size_half * num_ntts;
                for lane in 0..num_ntts {
                    let v = data[off_bot + lane];
                    let new_u = data[off_top + lane] + v.mul_base(twiddle);
                    data[off_top + lane] = new_u;
                    data[off_bot + lane] = v + new_u;
                }
            }
        }
    }
}

/// Parallel interleaved forward NTT over E, cache-blocked like the F64 twin:
/// top layers sweep the full buffer (fused two-layer passes, row-parallel),
/// deep layers run as cache-resident sub-NTTs in parallel. Constants are
/// re-derived for 16-byte elements.
fn forward_transform_interleaved_ext_parallel_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F128T],
    num_ntts: usize,
    start_layer: usize,
) {
    use rayon::prelude::*;
    let n_total = data.len();
    let log_d = log2_pow2(n_total / num_ntts);

    // Target sub-group ~2 MB; each position is num_ntts x 16 bytes.
    const TARGET_SUBGROUP_LOG_BYTES: usize = 21;
    let log_bytes_per_position = 4 + log2_pow2(num_ntts);
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
        forward_transform_interleaved_ext_scalar_from_layer(ntt, data, num_ntts, start_layer);
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
                let t_outer = ntt.twiddle(layer, block);
                let t_inner_a = ntt.twiddle(layer + 1, 2 * block);
                let t_inner_b = ntt.twiddle(layer + 1, 2 * block + 1);
                let start = block * block_elems;
                butterfly_interleaved_ext_fused_2layer_par_rows(
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
                let t = ntt.twiddle(layer, block);
                let start = block * block_elems;
                butterfly_interleaved_ext_block_par_rows(
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
                    let twiddle = ntt.twiddle(layer, global_block);
                    let block_start = block_in_sub * block_elems;
                    let block = &mut sub_data[block_start..block_start + block_elems];
                    butterfly_interleaved_ext_block(block, twiddle, block_size_half, num_ntts);
                }
            }
        });
}

fn butterfly_interleaved_ext_block_par_rows(
    block: &mut [F128T],
    twiddle: F64,
    block_size_half: usize,
    num_ntts: usize,
) {
    use rayon::prelude::*;
    const PARALLEL_ROW_THRESHOLD: usize = 1024;
    if block_size_half < PARALLEL_ROW_THRESHOLD {
        butterfly_interleaved_ext_block(block, twiddle, block_size_half, num_ntts);
        return;
    }
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    top.par_chunks_mut(num_ntts)
        .zip(bot.par_chunks_mut(num_ntts))
        .for_each(|(top_row, bot_row)| {
            for lane in 0..num_ntts {
                let v = bot_row[lane];
                let new_u = top_row[lane] + v.mul_base(twiddle);
                top_row[lane] = new_u;
                bot_row[lane] = v + new_u;
            }
        });
}

/// Fused 2-layer butterfly, row-parallel; see the F64 twin for the shape.
fn butterfly_interleaved_ext_fused_2layer_par_rows(
    block: &mut [F128T],
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
        |row_a: &mut [F128T], row_b: &mut [F128T], row_c: &mut [F128T], row_d: &mut [F128T]| {
            for lane in 0..num_ntts {
                let mut a = row_a[lane];
                let mut b = row_b[lane];
                let mut c = row_c[lane];
                let mut d = row_d[lane];
                let new_a = a + c.mul_base(t_outer);
                c += new_a;
                a = new_a;
                let new_b = b + d.mul_base(t_outer);
                d += new_b;
                b = new_b;
                let new_a2 = a + b.mul_base(t_inner_a);
                b += new_a2;
                a = new_a2;
                let new_c2 = c + d.mul_base(t_inner_b);
                d += new_c2;
                c = new_c2;
                row_a[lane] = a;
                row_b[lane] = b;
                row_c[lane] = c;
                row_d[lane] = d;
            }
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
fn butterfly_interleaved_ext_block(
    block: &mut [F128T],
    twiddle: F64,
    block_size_half: usize,
    num_ntts: usize,
) {
    let off_bot = block_size_half * num_ntts;
    for r in 0..block_size_half {
        let off_top = r * num_ntts;
        let off_bot_r = off_top + off_bot;
        for lane in 0..num_ntts {
            let v = block[off_bot_r + lane];
            let new_u = block[off_top + lane] + v.mul_base(twiddle);
            block[off_top + lane] = new_u;
            block[off_bot_r + lane] = v + new_u;
        }
    }
}

// ===================================================================
// LCH novel-basis evaluations over K (mirror of ligerito's extension-field block)
// ===================================================================
//
// The subspace-polynomial recurrence runs entirely over the K evaluation
// domain (F64 values); results are lifted into E with `mul_base` only where
// they scale E-accumulators. Standard basis only (v_i = x^i = F64(1 << i)).

#[inline]
fn next_s_k(s: F64, s_at_root: F64) -> F64 {
    s * s + s_at_root * s
}

/// `sks_vks[k] = s_k(v_k)` for `k = 0..=log_n`, over K. Mirror of
/// `ligerito::eval_sk_at_vks`. Public for the recursion harness, which dumps
/// these vanishing-polynomial values as guest hints (base-field, embedded into
/// the tower with high lane zero).
pub fn eval_sk_at_vks_k(log_n: usize) -> Vec<F64> {
    let mut sks_vks = vec![F64::ZERO; log_n + 1];
    sks_vks[0] = F64::ONE;
    if log_n == 0 {
        return sks_vks;
    }
    let mut layer: Vec<F64> = (1..=log_n).map(|i| F64(1u64 << i)).collect();
    let mut cur_len = log_n;
    for i in 0..log_n {
        for j in 0..cur_len {
            let sk_at_vk = next_s_k(layer[j], sks_vks[i]);
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

/// Write into `basis` the normalized LCH novel-basis polynomials evaluated at
/// `x` (a K point), each scaled by the E-value `alpha`. The `sks_at_x`
/// recurrence stays in K; the basis expansion lifts into E via `mul_base`.
fn evaluate_scaled_basis_inplace_k(
    sks_at_x: &mut [F64],
    basis: &mut [F128T],
    sks_vks: &[F64],
    inv_sks_vks: &[F64],
    x: F64,
    alpha: F128T,
) {
    let log_n = basis.len().trailing_zeros() as usize;
    debug_assert_eq!(basis.len(), 1 << log_n);
    debug_assert!(sks_at_x.len() >= log_n);
    debug_assert!(inv_sks_vks.len() > log_n);

    if log_n > 0 {
        sks_at_x[0] = x;
        for i in 1..log_n {
            sks_at_x[i] = next_s_k(sks_at_x[i - 1], sks_vks[i - 1]);
        }
        // Normalize: W-hat_i(x) = s_i(x) / s_i(v_i)
        for i in 0..log_n {
            sks_at_x[i] *= inv_sks_vks[i];
        }
    }

    basis[0] = alpha;
    for k in 0..log_n {
        let s_at_x = sks_at_x[k];
        let current_len = 1 << k;
        for i in 0..current_len {
            basis[i + current_len] = basis[i].mul_base(s_at_x);
        }
    }
}

// ===================================================================
// induce_sumcheck_poly: dense path (base-field rows at L0, E rows deeper)
// ===================================================================
//
// The sparse transposed-NTT fast path plus the auto dispatch that selects it
// at L0 lives in the "Transposed-NTT fast path" section below, mirroring the
// original's strategy split.

/// Level-0 induce: opened rows are F64. `basis_poly[j] = Σ_i eq(α, i) ·
/// W-hat_j(q_i)`, `enforced_sum = Σ_i eq(α, i) · <row_i, eq(v_challenges, ·)>`
/// with the row dot done via `mul_base`. Mirror of the dense
/// `ligerito::induce_sumcheck_poly` (per-thread chunked accumulation).
pub(crate) fn induce_sumcheck_poly_base(
    log_msg_cols: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<F64>],
    v_challenges: &[F128T],
    queries: &[usize],
    alpha: &[F128T],
) -> (Vec<F128T>, F128T) {
    use rayon::prelude::*;
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

    let alpha_pows: Vec<F128T> = if n_queries == 0 {
        Vec::new()
    } else {
        let table = build_eq_table_ext(alpha);
        debug_assert!(table.len() >= n_queries);
        table.into_iter().take(n_queries).collect()
    };

    let inv_sks_vks: Vec<F64> = sks_vks
        .iter()
        .map(|&v| if v.is_zero() { F64::ZERO } else { v.inv() })
        .collect();

    let n_threads = rayon::current_num_threads().max(1);
    let chunk_size = (n_queries + n_threads - 1) / n_threads.max(1);

    let partials: Vec<(Vec<F128T>, F128T)> = (0..n_threads)
        .into_par_iter()
        .map(|t| {
            let start = t * chunk_size;
            let end = (start + chunk_size).min(n_queries);
            if start >= end {
                return (vec![F128T::ZERO; n], F128T::ZERO);
            }
            let mut accum_basis = vec![F128T::ZERO; n];
            let mut local_basis = vec![F128T::ZERO; n];
            let mut sks_at_x = vec![F64::ZERO; log_msg_cols.max(1)];
            let mut local_sum = F128T::ZERO;

            for i in start..end {
                let row = &opened_rows[i];
                let q = queries[i];
                let ap = alpha_pows[i];

                // Mixed dot: E eq-weights times K row entries.
                let dot: F128T = row
                    .iter()
                    .zip(eq.iter())
                    .map(|(&r, &e)| e.mul_base(r))
                    .fold(F128T::ZERO, |a, v| a + v);
                local_sum += dot * ap;

                let q_field = F64(q as u64);
                evaluate_scaled_basis_inplace_k(
                    &mut sks_at_x,
                    &mut local_basis,
                    sks_vks,
                    &inv_sks_vks,
                    q_field,
                    ap,
                );
                for (acc, &v) in accum_basis.iter_mut().zip(local_basis.iter()) {
                    *acc += v;
                }
            }
            (accum_basis, local_sum)
        })
        .collect();

    let mut basis_poly = vec![F128T::ZERO; n];
    let mut enforced_sum = F128T::ZERO;
    for (lb, ls) in partials {
        for (acc, &v) in basis_poly.iter_mut().zip(lb.iter()) {
            *acc += v;
        }
        enforced_sum += ls;
    }

    (basis_poly, enforced_sum)
}

/// Deeper-level induce: opened rows are E-valued. Same structure as
/// [`induce_sumcheck_poly_base`] with a pure-E row dot.
pub(crate) fn induce_sumcheck_poly_ext(
    log_msg_cols: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<F128T>],
    v_challenges: &[F128T],
    queries: &[usize],
    alpha: &[F128T],
) -> (Vec<F128T>, F128T) {
    use rayon::prelude::*;
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

    let alpha_pows: Vec<F128T> = if n_queries == 0 {
        Vec::new()
    } else {
        let table = build_eq_table_ext(alpha);
        debug_assert!(table.len() >= n_queries);
        table.into_iter().take(n_queries).collect()
    };

    let inv_sks_vks: Vec<F64> = sks_vks
        .iter()
        .map(|&v| if v.is_zero() { F64::ZERO } else { v.inv() })
        .collect();

    let n_threads = rayon::current_num_threads().max(1);
    let chunk_size = (n_queries + n_threads - 1) / n_threads.max(1);

    let partials: Vec<(Vec<F128T>, F128T)> = (0..n_threads)
        .into_par_iter()
        .map(|t| {
            let start = t * chunk_size;
            let end = (start + chunk_size).min(n_queries);
            if start >= end {
                return (vec![F128T::ZERO; n], F128T::ZERO);
            }
            let mut accum_basis = vec![F128T::ZERO; n];
            let mut local_basis = vec![F128T::ZERO; n];
            let mut sks_at_x = vec![F64::ZERO; log_msg_cols.max(1)];
            let mut local_sum = F128T::ZERO;

            for i in start..end {
                let row = &opened_rows[i];
                let q = queries[i];
                let ap = alpha_pows[i];

                let dot: F128T = row
                    .iter()
                    .zip(eq.iter())
                    .map(|(&r, &e)| r * e)
                    .fold(F128T::ZERO, |a, v| a + v);
                local_sum += dot * ap;

                let q_field = F64(q as u64);
                evaluate_scaled_basis_inplace_k(
                    &mut sks_at_x,
                    &mut local_basis,
                    sks_vks,
                    &inv_sks_vks,
                    q_field,
                    ap,
                );
                for (acc, &v) in accum_basis.iter_mut().zip(local_basis.iter()) {
                    *acc += v;
                }
            }
            (accum_basis, local_sum)
        })
        .collect();

    let mut basis_poly = vec![F128T::ZERO; n];
    let mut enforced_sum = F128T::ZERO;
    for (lb, ls) in partials {
        for (acc, &v) in basis_poly.iter_mut().zip(lb.iter()) {
            *acc += v;
        }
        enforced_sum += ls;
    }

    (basis_poly, enforced_sum)
}

/// Compute just the `enforced_sum` half of the L0 induce (mirror of
/// `ligerito::induce_sumcheck_enforced_sum`, F64 rows via `mul_base`):
///   `enforced_sum = Σ_i eq(α, i) · <opened_rows[i], eq(v_challenges, ·)>`
/// Cheap: O(num_queries x num_interleaved). The succinct verifier needs this
/// at level intro time (before the residual challenges are known).
pub(crate) fn induce_sumcheck_enforced_sum_base(
    opened_rows: &[Vec<F64>],
    v_challenges: &[F128T],
    queries: &[usize],
    alpha: &[F128T],
) -> F128T {
    assert_eq!(opened_rows.len(), queries.len());
    let eq = build_eq_table_ext(v_challenges);
    let n_queries = queries.len();
    let alpha_weights: Vec<F128T> = if n_queries == 0 {
        Vec::new()
    } else {
        build_eq_table_ext(alpha)
            .into_iter()
            .take(n_queries)
            .collect()
    };
    let mut sum = F128T::ZERO;
    for (i, row) in opened_rows.iter().enumerate() {
        debug_assert_eq!(row.len(), eq.len());
        let dot: F128T = row
            .iter()
            .zip(eq.iter())
            .map(|(&r, &e)| e.mul_base(r))
            .fold(F128T::ZERO, |a, v| a + v);
        sum += alpha_weights[i] * dot;
    }
    sum
}

/// Deeper-level counterpart of [`induce_sumcheck_enforced_sum_base`]:
/// E-valued opened rows, pure-E row dot.
pub(crate) fn induce_sumcheck_enforced_sum_ext(
    opened_rows: &[Vec<F128T>],
    v_challenges: &[F128T],
    queries: &[usize],
    alpha: &[F128T],
) -> F128T {
    assert_eq!(opened_rows.len(), queries.len());
    let eq = build_eq_table_ext(v_challenges);
    let n_queries = queries.len();
    let alpha_weights: Vec<F128T> = if n_queries == 0 {
        Vec::new()
    } else {
        build_eq_table_ext(alpha)
            .into_iter()
            .take(n_queries)
            .collect()
    };
    let mut sum = F128T::ZERO;
    for (i, row) in opened_rows.iter().enumerate() {
        debug_assert_eq!(row.len(), eq.len());
        let dot: F128T = row
            .iter()
            .zip(eq.iter())
            .map(|(&r, &e)| r * e)
            .fold(F128T::ZERO, |a, v| a + v);
        sum += alpha_weights[i] * dot;
    }
    sum
}

/// SUCCINCT evaluator for the induced basis poly's MLE at residual points
/// (mirror of `ligerito::induce_sumcheck_evaluate_at_residual`). Replaces the
/// dense basis + `partial_eval_lsb` in the verifier via the closed form:
///   `MLE(basis_poly)(p) = Σ_i eq(α, i) · Π_k (1 + p[k] · (1 + W-hat_k(q_i)))`
/// where `q_i = F64(queries[i])` and the K-valued `W-hat_k(q_i)` lifts into E
/// through the char-2 factor. `ris_for_basis` is the fixed residual prefix
/// (length `log_msg_cols - yr_log_n`); returns evaluations at the `2^yr_log_n`
/// points `ris_for_basis ++ y_bits`.
pub(crate) fn induce_sumcheck_evaluate_at_residual_k(
    log_msg_cols: usize,
    sks_vks: &[F64],
    queries: &[usize],
    alpha: &[F128T],
    ris_for_basis: &[F128T],
    yr_log_n: usize,
) -> Vec<F128T> {
    use rayon::prelude::*;
    assert_eq!(ris_for_basis.len() + yr_log_n, log_msg_cols);
    let n_queries = queries.len();
    let yr_len = 1usize << yr_log_n;

    let alpha_pows: Vec<F128T> = if n_queries == 0 {
        Vec::new()
    } else {
        let table = build_eq_table_ext(alpha);
        debug_assert!(table.len() >= n_queries);
        table.into_iter().take(n_queries).collect()
    };

    let inv_sks_vks: Vec<F64> = sks_vks
        .iter()
        .map(|&v| if v.is_zero() { F64::ZERO } else { v.inv() })
        .collect();

    let prefix_len = ris_for_basis.len();

    // Per-query precomputation: W-hat_k(q) for all k over K, split into a
    // fixed prefix product (E scalar) and the suffix W-hat values varied per y.
    struct PerQuery {
        prefix_prod: F128T,
        suffix_w: Vec<F64>, // length = yr_log_n
    }
    let compute_query = |&q: &usize| -> PerQuery {
        let q_field = F64(q as u64);
        let mut sks_at_x = Vec::with_capacity(log_msg_cols.max(1));
        if log_msg_cols > 0 {
            sks_at_x.push(q_field);
            for k in 1..log_msg_cols {
                sks_at_x.push(next_s_k(sks_at_x[k - 1], sks_vks[k - 1]));
            }
            for k in 0..log_msg_cols {
                sks_at_x[k] *= inv_sks_vks[k];
            }
        }
        // Prefix product: Π_{k<prefix_len} (1 + ris[k] · (1 + W-hat_k(q)))
        let mut prefix_prod = F128T::ONE;
        for k in 0..prefix_len {
            prefix_prod *=
                F128T::ONE + ris_for_basis[k] * (F128T::ONE + F128T::from(sks_at_x[k]));
        }
        let suffix_w = if log_msg_cols > prefix_len {
            sks_at_x[prefix_len..].to_vec()
        } else {
            Vec::new()
        };
        PerQuery {
            prefix_prod,
            suffix_w,
        }
    };
    // Once per recursion level over verify-sized inputs; stay serial below
    // the rayon dispatch crossover (mirror of the original's PAR_FLOOR).
    const PAR_FLOOR: usize = 1024;
    let per_query: Vec<PerQuery> = if n_queries > PAR_FLOOR {
        queries.par_iter().map(compute_query).collect()
    } else {
        queries.iter().map(compute_query).collect()
    };

    // For each residual position y, accumulate the suffix product per query.
    let compute_y = |y: usize| -> F128T {
        let mut sum = F128T::ZERO;
        for i in 0..n_queries {
            let pq = &per_query[i];
            let mut suffix_prod = F128T::ONE;
            for j in 0..yr_log_n {
                let p_j = if (y >> j) & 1 == 1 {
                    F128T::ONE
                } else {
                    F128T::ZERO
                };
                suffix_prod *= F128T::ONE + p_j * (F128T::ONE + F128T::from(pq.suffix_w[j]));
            }
            sum += alpha_pows[i] * pq.prefix_prod * suffix_prod;
        }
        sum
    };
    if yr_len > PAR_FLOOR {
        (0..yr_len).into_par_iter().map(compute_y).collect()
    } else {
        (0..yr_len).map(compute_y).collect()
    }
}

// ===================================================================
// Transposed-NTT fast path for basis induction (mirror of the original)
// ===================================================================

/// Transposed forward additive NTT, `F^T`, in place over `2^log_d` E-values
/// with K-twiddles. Forward butterfly is `M = [[1, t], [1, t+1]]`; transpose
/// `M^T = [[1, 1], [t, t+1]]` is `s = a + b; top = s; bot = t*s + b` (here
/// `s.mul_base(t) + b`), applied in reverse layer order. Mirror of
/// `ligerito::transpose_forward_ntt` (one parallel sweep per layer).
fn transpose_forward_ntt_ext(ntt: &AdditiveNttF64, data: &mut [F128T], log_d: usize) {
    use rayon::prelude::*;
    debug_assert_eq!(data.len(), 1usize << log_d);
    debug_assert!(log_d <= ntt.log_domain_size());
    let n_threads = rayon::current_num_threads().max(1);
    for layer in (0..log_d).rev() {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let bsh = block_size >> 1;
        if num_blocks >= n_threads {
            data.par_chunks_mut(block_size)
                .enumerate()
                .for_each(|(block, chunk)| {
                    let t = ntt.twiddle(layer, block);
                    let (top, bot) = chunk.split_at_mut(bsh);
                    for (a_ref, b_ref) in top.iter_mut().zip(bot.iter_mut()) {
                        let a = *a_ref;
                        let b = *b_ref;
                        let s = a + b;
                        *a_ref = s;
                        *b_ref = s.mul_base(t) + b;
                    }
                });
        } else {
            for block in 0..num_blocks {
                let t = ntt.twiddle(layer, block);
                let chunk = &mut data[block * block_size..(block + 1) * block_size];
                let (top, bot) = chunk.split_at_mut(bsh);
                top.par_iter_mut()
                    .zip(bot.par_iter_mut())
                    .for_each(|(a_ref, b_ref)| {
                        let a = *a_ref;
                        let b = *b_ref;
                        let s = a + b;
                        *a_ref = s;
                        *b_ref = s.mul_base(t) + b;
                    });
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
/// of `ligerito::transpose_forward_ntt_sparse`.
fn transpose_forward_ntt_sparse_ext(
    ntt: &AdditiveNttF64,
    positions: &[usize],
    values: &[F128T],
    log_d: usize,
) -> Vec<F128T> {
    use rayon::prelude::*;
    use std::collections::HashMap;
    let n = 1usize << log_d;
    // No prefix for small domains: just scatter + full dense transpose.
    let k = if log_d >= 12 { 8usize.min(log_d) } else { 0 };

    if k == 0 {
        let mut data = vec![F128T::ZERO; n];
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
    let mut windows: HashMap<usize, Vec<F128T>> = HashMap::new();
    for (&p, &v) in positions.iter().zip(values) {
        let buf = windows
            .entry(p >> k)
            .or_insert_with(|| vec![F128T::ZERO; 1 << k]);
        buf[p & wmask] += v;
    }

    // Steps s = 0..k-1 within each active window, in parallel (windows disjoint).
    let win_vec: Vec<(usize, Vec<F128T>)> = windows.into_iter().collect();
    let processed: Vec<(usize, Vec<F128T>)> = win_vec
        .into_par_iter()
        .map(|(w, mut buf)| {
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
            (w, buf)
        })
        .collect();

    // Densify (active windows only; the rest stay zero, which is the correct
    // post-step-(k-1) state for an all-zero window).
    let mut data = vec![F128T::ZERO; n];
    for (w, buf) in processed {
        data[(w << k)..((w + 1) << k)].copy_from_slice(&buf);
    }

    // Remaining steps s = k..log_d-1 = forward layers (log_d-1-k) .. 0, dense.
    let n_threads = rayon::current_num_threads().max(1);
    for layer in (0..(log_d - k)).rev() {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let bsh = block_size >> 1;
        if num_blocks >= n_threads {
            data.par_chunks_mut(block_size)
                .enumerate()
                .for_each(|(block, chunk)| {
                    let t = ntt.twiddle(layer, block);
                    let (top, bot) = chunk.split_at_mut(bsh);
                    for (a_ref, b_ref) in top.iter_mut().zip(bot.iter_mut()) {
                        let a = *a_ref;
                        let b = *b_ref;
                        let sab = a + b;
                        *a_ref = sab;
                        *b_ref = sab.mul_base(t) + b;
                    }
                });
        } else {
            for block in 0..num_blocks {
                let t = ntt.twiddle(layer, block);
                let chunk = &mut data[block * block_size..(block + 1) * block_size];
                let (top, bot) = chunk.split_at_mut(bsh);
                top.par_iter_mut()
                    .zip(bot.par_iter_mut())
                    .for_each(|(a_ref, b_ref)| {
                        let a = *a_ref;
                        let b = *b_ref;
                        let sab = a + b;
                        *a_ref = sab;
                        *b_ref = sab.mul_base(t) + b;
                    });
            }
        }
    }
    data
}

/// `F^T`-based fast path for [`induce_sumcheck_poly_base`]: scatter per-query
/// E-weights into the codeword domain, apply `F^T` with K-twiddles, keep the
/// low `2^log_msg_cols` outputs. Byte-identical output to the dense path
/// (pinned by `induce_via_ntt_matches_dense`). Mirror of
/// `ligerito::induce_sumcheck_poly_via_ntt` with the L0 mixed row dot.
pub(crate) fn induce_sumcheck_poly_via_ntt_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    opened_rows: &[Vec<F64>],
    v_challenges: &[F128T],
    queries: &[usize],
    alpha: &[F128T],
) -> (Vec<F128T>, F128T) {
    let n = 1usize << log_msg_cols;
    let log_block = log_msg_cols + log_inv_rate;
    let block_len = 1usize << log_block;
    let n_queries = queries.len();
    assert_eq!(opened_rows.len(), n_queries);

    let eq = build_eq_table_ext(v_challenges);
    let alpha_pows: Vec<F128T> = if n_queries == 0 {
        Vec::new()
    } else {
        let table = build_eq_table_ext(alpha);
        debug_assert!(table.len() >= n_queries);
        table.into_iter().take(n_queries).collect()
    };

    let mut enforced_sum = F128T::ZERO;
    for i in 0..n_queries {
        let dot: F128T = opened_rows[i]
            .iter()
            .zip(eq.iter())
            .map(|(&r, &e)| e.mul_base(r))
            .fold(F128T::ZERO, |a, v| a + v);
        enforced_sum += dot * alpha_pows[i];
    }

    let mut coeffs = if log_block == 0 {
        let mut c = vec![F128T::ZERO; block_len];
        for i in 0..n_queries {
            c[queries[i]] += alpha_pows[i];
        }
        c
    } else {
        let ntt = AdditiveNttF64::standard(log_block);
        transpose_forward_ntt_sparse_ext(&ntt, queries, &alpha_pows, log_block)
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
pub(crate) fn induce_use_ntt_heuristic(
    log_msg_cols: usize,
    log_inv_rate: usize,
    n_queries: usize,
) -> bool {
    let log_block = log_msg_cols + log_inv_rate;
    log_msg_cols >= 12 && n_queries > 4 * (1usize << log_inv_rate) * log_block.max(1)
}

/// Dispatch between the dense [`induce_sumcheck_poly_base`] and the sparse
/// [`induce_sumcheck_poly_via_ntt_base`] for L0 (base-field rows). Mirror of
/// `ligerito::induce_sumcheck_poly_auto`: in the recursive PCS this fires
/// only at the top level (large message domain, many queries); deeper levels
/// stay dense. Both paths produce identical output, so a mis-dispatch only
/// costs time.
pub(crate) fn induce_sumcheck_poly_auto_base(
    log_msg_cols: usize,
    log_inv_rate: usize,
    sks_vks: &[F64],
    opened_rows: &[Vec<F64>],
    v_challenges: &[F128T],
    queries: &[usize],
    alpha: &[F128T],
) -> (Vec<F128T>, F128T) {
    if induce_use_ntt_heuristic(log_msg_cols, log_inv_rate, queries.len()) {
        induce_sumcheck_poly_via_ntt_base(
            log_msg_cols,
            log_inv_rate,
            opened_rows,
            v_challenges,
            queries,
            alpha,
        )
    } else {
        induce_sumcheck_poly_base(
            log_msg_cols,
            sks_vks,
            opened_rows,
            v_challenges,
            queries,
            alpha,
        )
    }
}

// ===================================================================
// ligero_commit for E-valued (folded) witnesses
// ===================================================================

/// Codeword + Merkle tree for one deeper Ligerito commitment level.
/// `mat[pos * num_interleaved + lane]`; each row (one `pos` across all lanes)
/// is one Merkle leaf of `num_interleaved * 16` bytes.
pub(crate) struct LigeroWitnessK {
    pub mat: Vec<F128T>,
    pub tree: Vec<Hash>,
    pub block_len: usize,
    pub num_interleaved: usize,
}

// No Drop/scratch-pool recycling here (divergence from the original's
// `LigeroWitness`): there is no F128T scratch pool, and deeper-level matrices
// are small relative to L0.

impl LigeroWitnessK {
    #[inline]
    pub fn row(&self, pos: usize) -> &[F128T] {
        let start = pos * self.num_interleaved;
        &self.mat[start..start + self.num_interleaved]
    }

    #[inline]
    pub fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
    }
}

/// Mirror of `ligerito::ligero_commit` for an E-valued poly: replicate the
/// LSB-lane-layout message into all `2^log_inv_rate` sub-blocks, RS-encode
/// each lane with the K-twiddle mixed-product NTT, and Merkle over rows.
pub(crate) fn ligero_commit_ext(
    poly: &[F128T],
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
    ntt: &AdditiveNttF64,
) -> LigeroWitnessK {
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);
    assert!(log_block_len <= ntt.log_domain_size());

    // Plain allocation (scratch-pool divergence; see module docs). Every slot
    // is written by the replicate fill.
    let codeword_len = block_len * num_interleaved;
    let mut mat: Vec<F128T> = primitives::alloc_uninit_vec(codeword_len);
    replicate_message_fill_t(&mut mat, poly);

    // Optional per-level NTT/Merkle split (LIG_K_TRACE): one env lookup per
    // commit level, no work when unset.
    let trace = std::env::var_os("LIG_K_TRACE").is_some();
    let t_ntt = std::time::Instant::now();
    forward_transform_interleaved_ext_from_layer(ntt, &mut mat, num_interleaved, log_inv_rate);
    let ntt_elapsed = t_ntt.elapsed();
    let t_merkle = std::time::Instant::now();

    // Merkle over rows, zero-copy.
    // SAFETY: F128T is repr(C) { c0: u64, c1: u64 } (16 bytes, no padding);
    // a `[F128T]` slice is a contiguous little-endian (c0, c1) byte image on
    // this (LE) target. The cast covers exactly `mat.len() * 16` initialized
    // bytes.
    let leaf_size_bytes = num_interleaved * core::mem::size_of::<F128T>();
    let data_bytes: &[u8] = unsafe {
        core::slice::from_raw_parts(
            mat.as_ptr() as *const u8,
            mat.len() * core::mem::size_of::<F128T>(),
        )
    };
    debug_assert_eq!(data_bytes.len(), block_len * leaf_size_bytes);
    let tree = merkle::merkle_tree(data_bytes, block_len);
    if trace {
        eprintln!(
            "[lig-k] ligero_commit(log_block={log_block_len}, lanes={num_interleaved}): \
             ntt = {:.4} s, merkle = {:.4} s",
            ntt_elapsed.as_secs_f64(),
            t_merkle.elapsed().as_secs_f64(),
        );
    }

    LigeroWitnessK {
        mat,
        tree,
        block_len,
        num_interleaved,
    }
}

// ===================================================================
// Stateful sumcheck over E with a two-phase (Base then Ext) witness
// ===================================================================
//
// Same (u_0, u_2) convention as the original: per-round quadratic
// q(X) = u_0 + u_1 X + u_2 X^2 with q(0) + q(1) = T_r, verifier derives
// u_1 = T_r + u_2 (char 2), round eval q(r) = u_0 + r T_r + (r + r^2) u_2.
//
// Round 0 pairs the K-witness with the E-basis via `mul_base`; the first fold
// lifts the witness into E and all later rounds are pure E.

/// (u_0, u_2) per round in E.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SumcheckMessageK {
    pub u_0: F128T,
    pub u_2: F128T,
}

/// Round-quadratic in coefficient form `c + b X + a X^2` (verifier side).
#[derive(Clone, Copy, Debug)]
struct RoundQuadK {
    c: F128T, // u_0
    b: F128T, // u_1 (X coeff), derived from T_r and u_2
    a: F128T, // u_2 (X^2 coeff)
}

impl RoundQuadK {
    #[inline]
    fn from_msg(msg: SumcheckMessageK, t_r: F128T) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
    #[inline]
    fn eval(&self, r: F128T) -> F128T {
        self.c + r * self.b + r * r * self.a
    }
    #[inline]
    fn fold(p1: &Self, p2: &Self, alpha: F128T) -> Self {
        Self {
            c: p1.c + alpha * p2.c,
            b: p1.b + alpha * p2.b,
            a: p1.a + alpha * p2.a,
        }
    }
}

/// Round message for the mixed phase: `f` in K, `b` in E. All products are
/// `mul_base` (2 PMULL each).
fn round_msg_lsb_base(f: &[F64], b: &[F128T]) -> SumcheckMessageK {
    use rayon::prelude::*;
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    const PAR_THRESHOLD: usize = 4096;
    let half = n / 2;
    // Deferred reduction: XOR-accumulate the raw mul_base lane products
    // (2 PMULL per term, no reduction tail) and reduce once per accumulator —
    // reduction commutes with XOR, so the message is bit-identical.
    if half < PAR_THRESHOLD {
        let mut u_0 = F128TBaseUnreduced::ZERO;
        let mut u_2 = F128TBaseUnreduced::ZERO;
        for j in 0..half {
            let f0 = f[2 * j];
            let f1 = f[2 * j + 1];
            let b0 = b[2 * j];
            let b1 = b[2 * j + 1];
            u_0 ^= b0.mul_base_unreduced(f0);
            u_2 ^= (b0 + b1).mul_base_unreduced(f0 + f1);
        }
        return SumcheckMessageK {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        };
    }

    let (u_0, u_2) = (0..half)
        .into_par_iter()
        .with_min_len(PAR_THRESHOLD / 4)
        .fold(
            || (F128TBaseUnreduced::ZERO, F128TBaseUnreduced::ZERO),
            |(a0, a2), j| {
                let f0 = f[2 * j];
                let f1 = f[2 * j + 1];
                let b0 = b[2 * j];
                let b1 = b[2 * j + 1];
                (a0 ^ b0.mul_base_unreduced(f0), a2 ^ (b0 + b1).mul_base_unreduced(f0 + f1))
            },
        )
        .map(|(a0, a2)| (a0.reduce(), a2.reduce()))
        .reduce(
            || (F128T::ZERO, F128T::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );
    SumcheckMessageK { u_0, u_2 }
}

/// Round message for the pure-E phase. Mirror of `ligerito::round_msg_lsb`.
fn round_msg_lsb_ext(f: &[F128T], b: &[F128T]) -> SumcheckMessageK {
    use rayon::prelude::*;
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    const PAR_THRESHOLD: usize = 4096;
    let half = n / 2;
    // Deferred reduction: XOR-accumulate the unreduced Karatsuba parts
    // (3 PMULL per term) and reduce once per accumulator — bit-identical.
    if half < PAR_THRESHOLD {
        let mut u_0 = F128TUnreduced::ZERO;
        let mut u_2 = F128TUnreduced::ZERO;
        for j in 0..half {
            let f0 = f[2 * j];
            let f1 = f[2 * j + 1];
            let b0 = b[2 * j];
            let b1 = b[2 * j + 1];
            u_0 ^= f0.mul_unreduced(b0);
            u_2 ^= (f0 + f1).mul_unreduced(b0 + b1);
        }
        return SumcheckMessageK {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        };
    }

    let (u_0, u_2) = (0..half)
        .into_par_iter()
        .with_min_len(PAR_THRESHOLD / 4)
        .fold(
            || (F128TUnreduced::ZERO, F128TUnreduced::ZERO),
            |(a0, a2), j| {
                let f0 = f[2 * j];
                let f1 = f[2 * j + 1];
                let b0 = b[2 * j];
                let b1 = b[2 * j + 1];
                (a0 ^ f0.mul_unreduced(b0), a2 ^ (f0 + f1).mul_unreduced(b0 + b1))
            },
        )
        .map(|(a0, a2)| (a0.reduce(), a2.reduce()))
        .reduce(
            || (F128T::ZERO, F128T::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );
    SumcheckMessageK { u_0, u_2 }
}

/// Fused fold + next-round message for the FIRST fold (mixed phase): the
/// K-witness folds into E (`(1+r).mul_base(f0) + r.mul_base(f1)`), the basis
/// folds in E, and the next-round message is built over the freshly folded
/// E values in the same pass. Mirror of `ligerito::fold_and_msg_lsb`.
fn fold_and_msg_lsb_base(
    f: &[F64],
    b: &[F128T],
    r: F128T,
) -> (Vec<F128T>, Vec<F128T>, SumcheckMessageK) {
    use rayon::prelude::*;
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;
    let one_plus_r = F128T::ONE + r;

    // Every 2-product sum defers its reduction: the fold writes pay ONE
    // reduction instead of two (`(1+r)·x + r·y` accumulated raw), and the
    // message accumulators reduce once per chunk — bit-identical throughout
    // (reduction commutes with XOR).
    let fold_f = |j: usize| -> F128T {
        (one_plus_r.mul_base_unreduced(f[2 * j]) ^ r.mul_base_unreduced(f[2 * j + 1])).reduce()
    };
    let fold_b = |j: usize| -> F128T {
        (b[2 * j].mul_unreduced(one_plus_r) ^ b[2 * j + 1].mul_unreduced(r)).reduce()
    };
    const PAR_THRESHOLD: usize = 4096;
    if half < PAR_THRESHOLD {
        let mut nf = Vec::with_capacity(half);
        let mut nb = Vec::with_capacity(half);
        for j in 0..half {
            nf.push(fold_f(j));
            nb.push(fold_b(j));
        }
        let mut u_0 = F128TUnreduced::ZERO;
        let mut u_2 = F128TUnreduced::ZERO;
        let mut k = 0;
        while k + 1 < half {
            let f0 = nf[k];
            let f1 = nf[k + 1];
            let b0 = nb[k];
            let b1 = nb[k + 1];
            u_0 ^= f0.mul_unreduced(b0);
            u_2 ^= (f0 + f1).mul_unreduced(b0 + b1);
            k += 2;
        }
        return (
            nf,
            nb,
            SumcheckMessageK {
                u_0: u_0.reduce(),
                u_2: u_2.reduce(),
            },
        );
    }

    // Parallel path: `half` is a power of two >= PAR_THRESHOLD and CHUNK is a
    // power of two, so every chunk has even length and starts at an even
    // global index (message pairs never straddle a chunk boundary).
    const CHUNK: usize = 2048;
    let mut nf: Vec<F128T> = primitives::alloc_uninit_vec(half);
    let mut nb: Vec<F128T> = primitives::alloc_uninit_vec(half);
    let (u_0, u_2) = nf
        .par_chunks_mut(CHUNK)
        .zip(nb.par_chunks_mut(CHUNK))
        .enumerate()
        .map(|(ci, (fc, bc))| {
            let base = ci * CHUNK;
            let len = fc.len();
            let mut u0 = F128TUnreduced::ZERO;
            let mut u2 = F128TUnreduced::ZERO;
            for t in 0..len {
                let j = base + t;
                fc[t] = fold_f(j);
                bc[t] = fold_b(j);
            }
            let mut k = 0;
            while k + 1 < len {
                let f0 = fc[k];
                let f1 = fc[k + 1];
                let b0 = bc[k];
                let b1 = bc[k + 1];
                u0 ^= f0.mul_unreduced(b0);
                u2 ^= (f0 + f1).mul_unreduced(b0 + b1);
                k += 2;
            }
            (u0.reduce(), u2.reduce())
        })
        .reduce(
            || (F128T::ZERO, F128T::ZERO),
            |(a0, a2), (c0, c2)| (a0 + c0, a2 + c2),
        );
    (nf, nb, SumcheckMessageK { u_0, u_2 })
}

/// Fused fold + next-round message for the pure-E phase. Mirror of
/// `ligerito::fold_and_msg_lsb`.
fn fold_and_msg_lsb_ext(
    f: &[F128T],
    b: &[F128T],
    r: F128T,
) -> (Vec<F128T>, Vec<F128T>, SumcheckMessageK) {
    use rayon::prelude::*;
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;
    let one_plus_r = F128T::ONE + r;

    // Deferred throughout, as in [`fold_and_msg_lsb_base`]: fold writes pay
    // one reduction instead of two, message accumulators reduce once per
    // chunk — bit-identical.
    let fold_pair = |x0: F128T, x1: F128T| -> F128T {
        (x0.mul_unreduced(one_plus_r) ^ x1.mul_unreduced(r)).reduce()
    };
    const PAR_THRESHOLD: usize = 4096;
    if half < PAR_THRESHOLD {
        let mut nf = Vec::with_capacity(half);
        let mut nb = Vec::with_capacity(half);
        for j in 0..half {
            nf.push(fold_pair(f[2 * j], f[2 * j + 1]));
            nb.push(fold_pair(b[2 * j], b[2 * j + 1]));
        }
        let mut u_0 = F128TUnreduced::ZERO;
        let mut u_2 = F128TUnreduced::ZERO;
        let mut k = 0;
        while k + 1 < half {
            let f0 = nf[k];
            let f1 = nf[k + 1];
            let b0 = nb[k];
            let b1 = nb[k + 1];
            u_0 ^= f0.mul_unreduced(b0);
            u_2 ^= (f0 + f1).mul_unreduced(b0 + b1);
            k += 2;
        }
        return (
            nf,
            nb,
            SumcheckMessageK {
                u_0: u_0.reduce(),
                u_2: u_2.reduce(),
            },
        );
    }

    const CHUNK: usize = 2048;
    let mut nf: Vec<F128T> = primitives::alloc_uninit_vec(half);
    let mut nb: Vec<F128T> = primitives::alloc_uninit_vec(half);
    let (u_0, u_2) = nf
        .par_chunks_mut(CHUNK)
        .zip(nb.par_chunks_mut(CHUNK))
        .enumerate()
        .map(|(ci, (fc, bc))| {
            let base = ci * CHUNK;
            let len = fc.len();
            let mut u0 = F128TUnreduced::ZERO;
            let mut u2 = F128TUnreduced::ZERO;
            for t in 0..len {
                let j = base + t;
                fc[t] = fold_pair(f[2 * j], f[2 * j + 1]);
                bc[t] = fold_pair(b[2 * j], b[2 * j + 1]);
            }
            let mut k = 0;
            while k + 1 < len {
                let f0 = fc[k];
                let f1 = fc[k + 1];
                let b0 = bc[k];
                let b1 = bc[k + 1];
                u0 ^= f0.mul_unreduced(b0);
                u2 ^= (f0 + f1).mul_unreduced(b0 + b1);
                k += 2;
            }
            (u0.reduce(), u2.reduce())
        })
        .reduce(
            || (F128T::ZERO, F128T::ZERO),
            |(a0, a2), (c0, c2)| (a0 + c0, a2 + c2),
        );
    (nf, nb, SumcheckMessageK { u_0, u_2 })
}

/// Two-phase witness: the committed K-message (borrowed from the caller, it
/// is only read until the first fold) before the first fold, an owned
/// E-vector afterwards.
enum WitnessK<'a> {
    Base(&'a [F64]),
    Ext(Vec<F128T>),
}

/// Mirror of `ligerito::SumcheckProver` with the two-phase witness. The
/// `introduce_new_with_eval` fusion (OOD-only) is not ported; see module docs.
pub struct SumcheckProverK<'a> {
    f: WitnessK<'a>,
    /// Single combined basis poly: after every `glue(beta)` the introduced
    /// basis is folded in as `combined_basis += beta * b_new`.
    combined_basis: Vec<F128T>,
    t_r: F128T,
    transcript: Vec<SumcheckMessageK>,
    pending_glue: Option<(Vec<F128T>, F128T)>,
}

impl<'a> SumcheckProverK<'a> {
    pub fn new(f: &'a [F64], b1: Vec<F128T>, h1: F128T) -> (Self, SumcheckMessageK) {
        assert_eq!(f.len(), b1.len());
        let msg = round_msg_lsb_base(f, &b1);
        let mut inst = Self {
            f: WitnessK::Base(f),
            combined_basis: b1,
            t_r: h1,
            transcript: Vec::new(),
            pending_glue: None,
        };
        inst.transcript.push(msg);
        (inst, msg)
    }

    pub fn fold(&mut self, r: F128T) -> SumcheckMessageK {
        let (nf, nb, msg) = match &self.f {
            WitnessK::Base(f) => fold_and_msg_lsb_base(f, &self.combined_basis, r),
            WitnessK::Ext(f) => fold_and_msg_lsb_ext(f, &self.combined_basis, r),
        };
        self.f = WitnessK::Ext(nf);
        self.combined_basis = nb;
        self.transcript.push(msg);
        msg
    }

    /// Introduce a fresh basis poly with claimed sum `h_new`; sends the
    /// (u_0, u_2) for `Σ_x f(x) · b_new(x)` at the current dim.
    pub fn introduce_new(&mut self, b_new: Vec<F128T>, h_new: F128T) -> SumcheckMessageK {
        let msg = match &self.f {
            WitnessK::Base(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb_base(f, &b_new)
            }
            WitnessK::Ext(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb_ext(f, &b_new)
            }
        };
        self.transcript.push(msg);
        self.pending_glue = Some((b_new, h_new));
        msg
    }

    /// Combine the introduced basis into `combined_basis` with separation
    /// `alpha`: `combined_basis[j] += alpha * b_new[j]`, `T_r += alpha * h_new`.
    pub fn glue(&mut self, alpha: F128T) {
        use rayon::prelude::*;
        let (b_new, h_new) = self
            .pending_glue
            .take()
            .expect("glue without introduce_new");
        assert_eq!(b_new.len(), self.combined_basis.len());
        const PAR_THRESHOLD: usize = 4096;
        if self.combined_basis.len() < PAR_THRESHOLD {
            for (acc, &v) in self.combined_basis.iter_mut().zip(b_new.iter()) {
                *acc += alpha * v;
            }
        } else {
            self.combined_basis
                .par_iter_mut()
                .zip(b_new.par_iter())
                .with_min_len(PAR_THRESHOLD / 4)
                .for_each(|(acc, &v)| *acc += alpha * v);
        }
        self.t_r += alpha * h_new;
    }

    /// The folded witness (post-first-fold: always E). Panics if called
    /// before the first fold (the base phase never reaches a commit).
    pub fn f_ext(&self) -> &[F128T] {
        match &self.f {
            WitnessK::Ext(f) => f,
            WitnessK::Base(_) => panic!("witness still in base phase (no fold yet)"),
        }
    }

    pub fn transcript(&self) -> &[SumcheckMessageK] {
        &self.transcript
    }
}

// ===================================================================
// Proof
// ===================================================================

/// L0 opened rows: F64 (the commitment field).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InitialProofK {
    /// One row per query (`num_interleaved` F64 entries), sorted by query
    /// position to align with the Merkle multi-proof.
    pub opened_rows: Vec<Vec<F64>>,
    pub merkle_proof: Vec<Hash>,
}

/// Deeper-level opened rows: E-valued.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveProofK {
    pub opened_rows: Vec<Vec<F128T>>,
    pub merkle_proof: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalProofK {
    /// Remaining polynomial sent in clear at the last recursive step.
    pub yr: Vec<F128T>,
    pub opened_rows: Vec<Vec<F128T>>,
    pub merkle_proof: Vec<Hash>,
}

/// Mirror of `LigeritoProof` minus `ood_values` (OOD is not ported; the UDR
/// profile takes none). The L0 root is the caller's statement, not proof data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LigeritoProofK {
    pub initial_proof: InitialProofK,
    pub recursive_roots: Vec<Hash>,
    pub recursive_proofs: Vec<RecursiveProofK>,
    pub final_proof: FinalProofK,
    pub sumcheck_transcript: Vec<SumcheckMessageK>,
    /// Per-level query-phase PoW nonces (0 when the level grinds 0 bits).
    pub grinding_nonces: Vec<u64>,
    /// Fold-challenge PoW nonces, flattened in transcript order (one per fold
    /// challenge at every level with `fold_grinding_bits > 0`).
    pub fold_grinding_nonces: Vec<u64>,
}

impl LigeritoProofK {
    pub fn size_bytes(&self) -> usize {
        const EXT: usize = core::mem::size_of::<F128T>();
        const BASE: usize = core::mem::size_of::<F64>();
        let mut total = 0usize;
        total += self.recursive_roots.len() * 32;
        total += self
            .initial_proof
            .opened_rows
            .iter()
            .map(|r| r.len() * BASE)
            .sum::<usize>()
            + self.initial_proof.merkle_proof.len() * 32;
        for p in &self.recursive_proofs {
            total += p.opened_rows.iter().map(|r| r.len() * EXT).sum::<usize>()
                + p.merkle_proof.len() * 32;
        }
        total += self.final_proof.yr.len() * EXT
            + self
                .final_proof
                .opened_rows
                .iter()
                .map(|r| r.len() * EXT)
                .sum::<usize>()
            + self.final_proof.merkle_proof.len() * 32;
        total += self.sumcheck_transcript.len() * 2 * EXT;
        total += (self.grinding_nonces.len() + self.fold_grinding_nonces.len()) * 8;
        total
    }
}

// ===================================================================
// Prover
// ===================================================================

/// Sample `count` distinct positions in `[0, block_len)`. Same sponge
/// pattern as the original (`sample().c0 % block_len`).
/// Sample `count` query positions in transcript order — no dedup, no sort.
/// `block_len = 2^d`; each squeezed field element yields `⌊128/d⌋` positions as
/// its disjoint d-bit chunks (low bits first). Mirror of
/// `ligerito::sample_queries_ordered` so the K opener uses the exact
/// recursion-friendly scheme the harness/guest re-derive (fixed `128/d` per
/// squeeze, dup-tolerant — soundness matches the deployed extension-field PCS with the same
/// `config.queries`). Duplicates are harmless: a repeated position re-opens the
/// same Merkle-authenticated row.
fn sample_queries_ordered_k(sponge: &mut Sponge, block_len: usize, count: usize) -> Vec<usize> {
    let d = block_len.trailing_zeros() as usize;
    let per = 128 / d;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        let v = sponge.sample();
        let bits = (v.c0 as u128) | ((v.c1 as u128) << 64);
        for j in 0..per.min(count - out.len()) {
            out.push(((bits >> (j * d)) as usize) & (block_len - 1));
        }
    }
    out
}

/// [`sample_queries_ordered_k`] that ALSO returns the raw squeezed words `v`
/// (as native `F128T` — the recursion harness reads
/// `.c0/.c1` off them to re-derive positions). One raw word per squeeze.
fn sample_queries_ordered_with_raw_k(
    sponge: &mut Sponge,
    block_len: usize,
    count: usize,
) -> (Vec<usize>, Vec<F128T>) {
    let d = block_len.trailing_zeros() as usize;
    let per = 128 / d;
    let mut out = Vec::with_capacity(count);
    let mut raw = Vec::with_capacity(count.div_ceil(per));
    while out.len() < count {
        let v = sponge.sample();
        raw.push(v);
        let bits = (v.c0 as u128) | ((v.c1 as u128) << 64);
        for j in 0..per.min(count - out.len()) {
            out.push(((bits >> (j * d)) as usize) & (block_len - 1));
        }
    }
    (out, raw)
}

/// Fan stored sorted-unique rows back to transcript (ordered, dup-possible)
/// order, so the induce math sees `opened_rows[i]` ↔ `queries[i]`. The rows must
/// already be authenticated (via the octopus check) against the level root.
fn fan_rows_to_ordered<T: Clone>(queries: &[usize], rows_sorted: &[Vec<T>]) -> Option<Vec<Vec<T>>> {
    let sorted = sorted_unique_queries_k(queries);
    if sorted.len() != rows_sorted.len() {
        return None;
    }
    let mut out = Vec::with_capacity(queries.len());
    for &q in queries {
        let slot = sorted.binary_search(&q).ok()?;
        out.push(rows_sorted[slot].clone());
    }
    Some(out)
}

fn merkle_multi_proof_for(tree: &[Hash], block_len: usize, queries: &[usize]) -> Vec<Hash> {
    merkle::merkle_multi_proof(tree, block_len, queries)
}

/// K-witness mirror of `ligerito::recursive_prover_with_basis`: proves the
/// claim `Σ_x witness(x) · b_initial(x) = target` against the L0 commitment
/// produced by [`commit_k`] (with `log_batch_size = config.initial_k` and
/// `log_inv_rate = config.log_inv_rates[0]`).
///
/// `witness` is borrowed: it is only READ (round-0 message + the first lane
/// fold, which lifts it into an owned E-vector), so callers with a large
/// committed stack pass the slice directly instead of paying a full copy.
///
/// Transcript order is identical to the original (label, target, root,
/// (u_0, u_2) stream, tapered fold grinds, query grinds, queries, alphas,
/// betas, `yr` in the clear at the end), with OOD blocks elided because the
/// config is asserted to take zero OOD samples.
pub fn recursive_prover_with_basis_k(
    config: &ProverConfig,
    witness: &[F64],
    b_initial: Vec<F128T>,
    target: F128T,
    l0_codeword: &[F64],
    l0_tree: &[Hash],
    sponge: &mut Sponge,
) -> LigeritoProofK {
    let log_n = witness.len().trailing_zeros() as usize;
    let r = config.level_steps;
    let initial_k = config.initial_k;

    assert_eq!(witness.len(), 1usize << log_n);
    assert_eq!(b_initial.len(), 1usize << log_n);
    assert_eq!(config.level_ks.len(), r);
    assert_eq!(config.log_inv_rates.len(), r + 1);
    assert!(r >= 1);
    assert!(initial_k >= 1);
    // OOD sampling is not ported (module docs): the UDR (`Secure`) profile
    // takes none at any level.
    assert!(
        config.ood_samples.iter().all(|&s| s == 0),
        "ligerito_k: OOD sampling is not ported; config must take 0 OOD samples"
    );

    let log_inv_rate_0 = config.log_inv_rates[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
    let num_interleaved_0 = 1usize << initial_k;
    assert_eq!(l0_codeword.len(), block_len_0 * num_interleaved_0);
    assert_eq!(l0_tree.len(), 2 * block_len_0 - 1);

    // Optional per-phase timing (LIG_K_TRACE): mirror of the original's
    // LIG_PROVE_TRACE. One env lookup per prove; the Instant reads are
    // negligible and the accumulation/printing is gated on `trace`.
    let trace = std::env::var_os("LIG_K_TRACE").is_some();
    let mut t_init_sumcheck = std::time::Duration::ZERO;
    let mut t_commits = std::time::Duration::ZERO;
    let mut t_opens = std::time::Duration::ZERO;
    let mut t_induce = std::time::Duration::ZERO;
    let mut t_sumcheck_folds = std::time::Duration::ZERO;
    let mut t_intro_glue = std::time::Duration::ZERO;
    let t_total = std::time::Instant::now();

    // (No opener domain-label absorb: the extension-field opener has none and the recursion
    // guest replays a label-free opening transcript; the observed `target` +
    // outer transcript context provide domain separation.)
    observe_ext(sponge, target);

    // L0 codeword + tree are borrowed (reused from `commit_k`).
    let initial_root: Hash = l0_tree[l0_tree.len() - 1];
    let l0_row = |q: usize| -> &[F64] {
        let start = q * num_interleaved_0;
        &l0_codeword[start..start + num_interleaved_0]
    };
    observe_root(sponge, &initial_root);

    let mut fold_grinding_nonces: Vec<u64> = Vec::new();
    let fold_bits =
        |lvl: usize| -> u32 { config.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as u32 };

    let _t = std::time::Instant::now();
    let (mut sc_prover, start_msg) = SumcheckProverK::new(witness, b_initial, target);
    observe_ext(sponge, start_msg.u_0);
    observe_ext(sponge, start_msg.u_2);

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        // Tapered fold-challenge grinding: round j of the lane fold needs
        // (fold_bits - j) bits (worst round j=0 carries the full budget); see
        // the original's App. C.3 `mca-commutes` comment.
        let bits = fold_bits(0).saturating_sub(j as u32);
        if bits > 0 {
            fold_grinding_nonces.push(sponge.grind_pow(bits));
        }
        let r_j = sample_ext(sponge);
        let msg = sc_prover.fold(r_j);
        observe_ext(sponge, msg.u_0);
        observe_ext(sponge, msg.u_2);
        r_lane_fold.push(r_j);
    }
    if trace {
        t_init_sumcheck += _t.elapsed();
    }

    // Commit f^1 = folded (now E-valued) witness as wtns_1.
    let n1 = log_n - initial_k;
    let log_num_interleaved_1 = config.level_ks[0];
    assert!(n1 >= log_num_interleaved_1);
    let log_msg_cols_1 = n1 - log_num_interleaved_1;
    let log_inv_rate_1 = config.log_inv_rates[1];
    let _t = std::time::Instant::now();
    let ntt_1 = AdditiveNttF64::standard(log_msg_cols_1 + log_inv_rate_1);
    let f1 = sc_prover.f_ext().to_vec();
    let wtns_1 = ligero_commit_ext(
        &f1,
        log_msg_cols_1,
        log_num_interleaved_1,
        log_inv_rate_1,
        &ntt_1,
    );
    if trace {
        t_commits += _t.elapsed();
    }
    observe_root(sponge, &wtns_1.root());

    // (OOD binding block elided: zero samples asserted above.)

    // Query-phase PoW grinding for L0 (0 bits in the Secure profile; the
    // canonical 0 nonce is still absorbed to keep the transcript in lockstep).
    let pow_nonce_0 = sponge.grind_pow(config.grinding_bits[0] as u32);
    let mut grinding_nonces: Vec<u64> = vec![pow_nonce_0];

    // Open L0; lane-fold weights = r_lane_fold.
    let num_queries_0 = config.queries[0];
    let queries_0 = sample_queries_ordered_k(sponge, block_len_0, num_queries_0);
    let alpha_0 = sample_ext_vec(sponge, log2_ceil(num_queries_0));
    let _t = std::time::Instant::now();
    // Ordered (dup-possible) rows for the local induce math ...
    let opened_rows_0: Vec<Vec<F64>> = queries_0.iter().map(|&q| l0_row(q).to_vec()).collect();
    // ... but the stored proof carries the sorted-unique rows + one octopus over
    // the sorted-unique positions (the verifier re-fans them to ordered).
    let sq_0 = sorted_unique_queries_k(&queries_0);
    let stored_rows_0: Vec<Vec<F64>> = sq_0.iter().map(|&q| l0_row(q).to_vec()).collect();
    let merkle_proof_0 = merkle_multi_proof_for(l0_tree, block_len_0, &sq_0);
    if trace {
        t_opens += _t.elapsed();
    }
    let initial_proof = InitialProofK {
        opened_rows: stored_rows_0,
        merkle_proof: merkle_proof_0,
    };

    // Induce basis_0 from the L0 opens. L0 dominates the induce phase, where
    // the sparse-prefix transposed-NTT path wins; the dispatcher auto-selects
    // it (deeper levels stay dense), mirroring the original.
    let sks_vks_n1 = eval_sk_at_vks_k(n1);
    let _t = std::time::Instant::now();
    let (basis_0_induced, enforced_sum_0) = induce_sumcheck_poly_auto_base(
        n1,
        log_inv_rate_0,
        &sks_vks_n1,
        &opened_rows_0,
        &r_lane_fold,
        &queries_0,
        &alpha_0,
    );
    if trace {
        t_induce += _t.elapsed();
    }

    // Introduce + glue basis_0.
    let _t = std::time::Instant::now();
    let intro_msg_0 = sc_prover.introduce_new(basis_0_induced, enforced_sum_0);
    observe_ext(sponge, intro_msg_0.u_0);
    observe_ext(sponge, intro_msg_0.u_2);
    let beta_0 = sample_ext(sponge);
    sc_prover.glue(beta_0);
    if trace {
        t_intro_glue += _t.elapsed();
    }

    // Recursive levels.
    let mut wtns_prev = wtns_1;
    let mut recursive_roots: Vec<Hash> = vec![wtns_prev.root()];
    let mut recursive_proofs: Vec<RecursiveProofK> = Vec::new();

    for i in 0..r {
        let k_i = config.level_ks[i];
        let mut level_rs = Vec::with_capacity(k_i);
        let _t = std::time::Instant::now();
        for j in 0..k_i {
            // These folds fold level i+1's commitment; tapered grinding as in
            // the L0 loop.
            let bits = fold_bits(i + 1).saturating_sub(j as u32);
            if bits > 0 {
                fold_grinding_nonces.push(sponge.grind_pow(bits));
            }
            let ri = sample_ext(sponge);
            let msg = sc_prover.fold(ri);
            observe_ext(sponge, msg.u_0);
            observe_ext(sponge, msg.u_2);
            level_rs.push(ri);
        }
        if trace {
            t_sumcheck_folds += _t.elapsed();
        }

        if i == r - 1 {
            let yr = sc_prover.f_ext().to_vec();
            for v in &yr {
                observe_ext(sponge, *v);
            }
            // PoW grinding for the last level before sampling its queries.
            let nonce_last = sponge.grind_pow(config.grinding_bits[i + 1] as u32);
            grinding_nonces.push(nonce_last);
            let num_queries_last = config.queries[i + 1];
            let queries_last =
                sample_queries_ordered_k(sponge, wtns_prev.block_len, num_queries_last);
            let _t = std::time::Instant::now();
            // Final level: stored (sorted-unique) only — no local induce; the
            // verifier fans these to ordered for its last-level induce.
            let sq_last = sorted_unique_queries_k(&queries_last);
            let opened_rows_last: Vec<Vec<F128T>> = sq_last
                .iter()
                .map(|&q| wtns_prev.row(q).to_vec())
                .collect();
            let merkle_proof_last =
                merkle_multi_proof_for(&wtns_prev.tree, wtns_prev.block_len, &sq_last);
            if trace {
                t_opens += _t.elapsed();
                let total = t_total.elapsed();
                eprintln!("[lig-k-prove] total = {:.4} s", total.as_secs_f64());
                eprintln!(
                    "  initial sumcheck (initial_k folds + SC build): {:.4} s",
                    t_init_sumcheck.as_secs_f64()
                );
                eprintln!(
                    "  recursive commits (NTT + merkle):              {:.4} s",
                    t_commits.as_secs_f64()
                );
                eprintln!(
                    "  opens (rows + multi-proof, incl. final):      {:.4} s",
                    t_opens.as_secs_f64()
                );
                eprintln!(
                    "  induce_sumcheck_poly:                          {:.4} s",
                    t_induce.as_secs_f64()
                );
                eprintln!(
                    "  sumcheck recursive folds:                      {:.4} s",
                    t_sumcheck_folds.as_secs_f64()
                );
                eprintln!(
                    "  introduce_new + glue:                          {:.4} s",
                    t_intro_glue.as_secs_f64()
                );
            }
            return LigeritoProofK {
                initial_proof,
                recursive_roots,
                recursive_proofs,
                final_proof: FinalProofK {
                    yr,
                    opened_rows: opened_rows_last,
                    merkle_proof: merkle_proof_last,
                },
                sumcheck_transcript: sc_prover.transcript().to_vec(),
                grinding_nonces,
                fold_grinding_nonces,
            };
        }

        let n_next = sc_prover.f_ext().len().trailing_zeros() as usize;
        let log_num_interleaved_next = config.level_ks[i + 1];
        assert!(n_next >= log_num_interleaved_next);
        let log_msg_cols_next = n_next - log_num_interleaved_next;
        let log_inv_rate_next = config.log_inv_rates[i + 2];
        let _t = std::time::Instant::now();
        let ntt_next = AdditiveNttF64::standard(log_msg_cols_next + log_inv_rate_next);
        let f_evals = sc_prover.f_ext().to_vec();
        let wtns_next = ligero_commit_ext(
            &f_evals,
            log_msg_cols_next,
            log_num_interleaved_next,
            log_inv_rate_next,
            &ntt_next,
        );
        if trace {
            t_commits += _t.elapsed();
        }
        let root_next = wtns_next.root();
        observe_root(sponge, &root_next);
        recursive_roots.push(root_next);

        // (OOD binding block elided: zero samples asserted above.)

        // PoW grinding for this iteration's query phase.
        let nonce_i = sponge.grind_pow(config.grinding_bits[i + 1] as u32);
        grinding_nonces.push(nonce_i);
        let num_queries_i = config.queries[i + 1];
        let queries_i = sample_queries_ordered_k(sponge, wtns_prev.block_len, num_queries_i);
        let alpha_i = sample_ext_vec(sponge, log2_ceil(num_queries_i));
        let _t = std::time::Instant::now();
        // Ordered rows for the local induce; sorted-unique rows + octopus stored.
        let opened_rows_i: Vec<Vec<F128T>> = queries_i
            .iter()
            .map(|&q| wtns_prev.row(q).to_vec())
            .collect();
        let sq_i = sorted_unique_queries_k(&queries_i);
        let stored_rows_i: Vec<Vec<F128T>> = sq_i
            .iter()
            .map(|&q| wtns_prev.row(q).to_vec())
            .collect();
        let merkle_proof_i =
            merkle_multi_proof_for(&wtns_prev.tree, wtns_prev.block_len, &sq_i);
        if trace {
            t_opens += _t.elapsed();
        }
        recursive_proofs.push(RecursiveProofK {
            opened_rows: stored_rows_i,
            merkle_proof: merkle_proof_i,
        });

        let sks_vks_i = eval_sk_at_vks_k(n_next);
        let _t = std::time::Instant::now();
        let (basis_i_induced, enforced_sum_i) = induce_sumcheck_poly_ext(
            n_next,
            &sks_vks_i,
            &opened_rows_i,
            &level_rs,
            &queries_i,
            &alpha_i,
        );
        if trace {
            t_induce += _t.elapsed();
        }

        let _t = std::time::Instant::now();
        let intro_msg_i = sc_prover.introduce_new(basis_i_induced, enforced_sum_i);
        observe_ext(sponge, intro_msg_i.u_0);
        observe_ext(sponge, intro_msg_i.u_2);
        let beta_i = sample_ext(sponge);
        sc_prover.glue(beta_i);
        if trace {
            t_intro_glue += _t.elapsed();
        }

        wtns_prev = wtns_next;
    }

    unreachable!()
}

// ===================================================================
// Dense verifier
// ===================================================================

/// Verify all opened L0 (F64) rows against one root via a single multi-proof.
fn verify_level_opens_base(
    root: &Hash,
    block_len: usize,
    queries: &[usize],
    opened_rows: &[Vec<F64>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> bool {
    if queries.len() != opened_rows.len() {
        return false;
    }
    let mut leaf_hashes: Vec<Hash> = Vec::with_capacity(opened_rows.len());
    for row in opened_rows {
        if row.len() != expected_num_interleaved {
            return false;
        }
        // SAFETY: F64 is repr(transparent) over u64 (8 bytes, no padding);
        // the row's byte image is exactly `row.len() * 8` initialized bytes.
        let bytes: &[u8] = unsafe {
            core::slice::from_raw_parts(
                row.as_ptr() as *const u8,
                row.len() * core::mem::size_of::<F64>(),
            )
        };
        leaf_hashes.push(merkle::hash_leaf(bytes));
    }
    merkle::verify_merkle_multi_proof(root, block_len, queries, &leaf_hashes, multi_proof)
}

/// Verify all opened deeper-level (F128T) rows against one root.
fn verify_level_opens_ext(
    root: &Hash,
    block_len: usize,
    queries: &[usize],
    opened_rows: &[Vec<F128T>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> bool {
    if queries.len() != opened_rows.len() {
        return false;
    }
    let mut leaf_hashes: Vec<Hash> = Vec::with_capacity(opened_rows.len());
    for row in opened_rows {
        if row.len() != expected_num_interleaved {
            return false;
        }
        // SAFETY: F128T is repr(C) { c0: u64, c1: u64 } (16 bytes, no
        // padding); the row's byte image is exactly `row.len() * 16`
        // initialized bytes.
        let bytes: &[u8] = unsafe {
            core::slice::from_raw_parts(
                row.as_ptr() as *const u8,
                row.len() * core::mem::size_of::<F128T>(),
            )
        };
        leaf_hashes.push(merkle::hash_leaf(bytes));
    }
    merkle::verify_merkle_multi_proof(root, block_len, queries, &leaf_hashes, multi_proof)
}

/// Transcript-order queries with duplicates removed, ascending. The K opening
/// stores one opened row per distinct query position (sorted); the recursion
/// harness expands back to per-query order below.
fn sorted_unique_queries_k(queries: &[usize]) -> Vec<usize> {
    let mut s = queries.to_vec();
    s.sort_unstable();
    s.dedup();
    s
}

/// Expand a base-level (`F64`, level 0) [`InitialProofK`] into the flat per-query
/// form the recursion guest re-hashes: one row and one full Merkle path per
/// query, in transcript order (duplicates included). Mirror of
/// [`crate::ligerito::expand_level_opening`] for the K stacked opening's `F64`
/// leaf level. Authenticates nothing itself; the caller re-checks each restored
/// path against the root.
pub fn expand_level_opening_base_k(
    block_len: usize,
    queries: &[usize],
    rows_sorted: &[Vec<F64>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> Option<(Vec<Vec<F64>>, Vec<Hash>)> {
    let sorted = sorted_unique_queries_k(queries);
    if sorted.len() != rows_sorted.len() {
        return None;
    }
    let mut leaf_hashes = Vec::with_capacity(rows_sorted.len());
    for row in rows_sorted {
        if row.len() != expected_num_interleaved {
            return None;
        }
        // SAFETY: F64 is repr(transparent) over u64 (8 bytes, no padding).
        let bytes: &[u8] = unsafe {
            core::slice::from_raw_parts(row.as_ptr() as *const u8, row.len() * core::mem::size_of::<F64>())
        };
        leaf_hashes.push(merkle::hash_leaf(bytes));
    }
    let flat_paths = merkle::restore_multi_proof(block_len, queries, &leaf_hashes, multi_proof)?;
    let mut rows_ordered = Vec::with_capacity(queries.len());
    for &q in queries {
        let slot = sorted.binary_search(&q).ok()?;
        rows_ordered.push(rows_sorted[slot].clone());
    }
    Some((rows_ordered, flat_paths))
}

/// Extension-level (`F128T`, levels ≥ 1) counterpart of
/// [`expand_level_opening_base_k`], hashing 16-byte `F128T` leaf rows.
pub fn expand_level_opening_ext_k(
    block_len: usize,
    queries: &[usize],
    rows_sorted: &[Vec<F128T>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> Option<(Vec<Vec<F128T>>, Vec<Hash>)> {
    let sorted = sorted_unique_queries_k(queries);
    if sorted.len() != rows_sorted.len() {
        return None;
    }
    let mut leaf_hashes = Vec::with_capacity(rows_sorted.len());
    for row in rows_sorted {
        if row.len() != expected_num_interleaved {
            return None;
        }
        // SAFETY: F128T is repr(C) { u64, u64 } (16 bytes, no padding).
        let bytes: &[u8] = unsafe {
            core::slice::from_raw_parts(row.as_ptr() as *const u8, row.len() * core::mem::size_of::<F128T>())
        };
        leaf_hashes.push(merkle::hash_leaf(bytes));
    }
    let flat_paths = merkle::restore_multi_proof(block_len, queries, &leaf_hashes, multi_proof)?;
    let mut rows_ordered = Vec::with_capacity(queries.len());
    for &q in queries {
        let slot = sorted.binary_search(&q).ok()?;
        rows_ordered.push(rows_sorted[slot].clone());
    }
    Some((rows_ordered, flat_paths))
}

/// Dense verifier for [`recursive_prover_with_basis_k`] (mirror of
/// `ligerito::recursive_verifier_with_basis`): materializes `b_initial` and
/// every induced basis poly, replays the transcript, and checks the residual
/// inner product against the running sum-claim. Production callers should
/// prefer [`recursive_verifier_with_basis_succinct_k`]; this one exists for
/// correctness testing (dense/succinct agreement) and benchmarking.
pub fn recursive_verifier_with_basis_k(
    config: &VerifierConfig,
    proof: &LigeritoProofK,
    b_initial: &[F128T],
    target: F128T,
    expected_initial_root: &Hash,
    sponge: &mut Sponge,
) -> bool {
    let log_n = b_initial.len().trailing_zeros() as usize;
    let initial_k = config.initial_k;
    let r = config.level_steps;

    if r < 1 || config.level_ks.len() != r || config.log_inv_rates.len() != r + 1 {
        return false;
    }
    if b_initial.len() != 1usize << log_n {
        return false;
    }
    // OOD is not ported; reject configs that would require it.
    if config.ood_samples.iter().any(|&s| s != 0) {
        return false;
    }

    // The L0 root is the caller's statement (not proof data): absorb it in the
    // prover's slot and check L0 opens against it below.
    // (No opener domain-label absorb: the extension-field opener has none and the recursion
    // guest replays a label-free opening transcript; the observed `target` +
    // outer transcript context provide domain separation.)
    observe_ext(sponge, target);
    observe_root(sponge, expected_initial_root);

    let log_inv_rate_0 = config.log_inv_rates[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
    let num_interleaved_0 = 1usize << initial_k;

    // Replay sumcheck: start msg, then initial_k folds.
    let mut t_r = target;
    let mut tx_idx = 0usize;
    if tx_idx >= proof.sumcheck_transcript.len() {
        return false;
    }
    let start_msg = proof.sumcheck_transcript[tx_idx];
    tx_idx += 1;
    observe_ext(sponge, start_msg.u_0);
    observe_ext(sponge, start_msg.u_2);
    let mut running_quad = RoundQuadK::from_msg(start_msg, t_r);

    let fold_bits =
        |lvl: usize| -> u32 { config.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as u32 };
    let mut fold_nonce_idx = 0usize;

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        // Fold-challenge PoW mirror (L0's lane folds), tapered per round.
        let bits = fold_bits(0).saturating_sub(j as u32);
        if bits > 0 {
            if fold_nonce_idx >= proof.fold_grinding_nonces.len() {
                return false;
            }
            if !sponge.verify_pow(proof.fold_grinding_nonces[fold_nonce_idx], bits) {
                return false;
            }
            fold_nonce_idx += 1;
        }
        let ri = sample_ext(sponge);
        r_lane_fold.push(ri);
        t_r = running_quad.eval(ri);
        if tx_idx >= proof.sumcheck_transcript.len() {
            return false;
        }
        let msg = proof.sumcheck_transcript[tx_idx];
        tx_idx += 1;
        observe_ext(sponge, msg.u_0);
        observe_ext(sponge, msg.u_2);
        running_quad = RoundQuadK::from_msg(msg, t_r);
    }

    // Observe wtns_1 root + open wtns_0.
    if proof.recursive_roots.is_empty() {
        return false;
    }
    let root_1 = proof.recursive_roots[0];
    observe_root(sponge, &root_1);

    // (OOD binding mirror elided: zero samples enforced above.)

    // PoW grinding check for L0's query phase (no-op at 0 bits but keeps the
    // FS state in lockstep with the prover).
    let mut nonce_idx = 0usize;
    if nonce_idx >= proof.grinding_nonces.len() {
        return false;
    }
    if !sponge.verify_pow(
        proof.grinding_nonces[nonce_idx],
        config.grinding_bits[0] as u32,
    ) {
        return false;
    }
    nonce_idx += 1;

    let num_queries_0 = config.queries[0];
    let queries_0 = sample_queries_ordered_k(sponge, block_len_0, num_queries_0);
    let alpha_0 = sample_ext_vec(sponge, log2_ceil(num_queries_0));
    let sq_0 = sorted_unique_queries_k(&queries_0);
    if !verify_level_opens_base(
        expected_initial_root,
        block_len_0,
        &sq_0,
        &proof.initial_proof.opened_rows,
        num_interleaved_0,
        &proof.initial_proof.merkle_proof,
    ) {
        return false;
    }
    // Fan the authenticated sorted-unique rows back to transcript order for induce.
    let ordered_rows_0 = match fan_rows_to_ordered(&queries_0, &proof.initial_proof.opened_rows) {
        Some(x) => x,
        None => return false,
    };

    // L0 induce with the same auto dispatch as the prover (dense vs sparse
    // transposed-NTT; identical outputs either way).
    let n1 = log_n - initial_k;
    let sks_vks_n1 = eval_sk_at_vks_k(n1);
    let (basis_0_induced, enforced_sum_0) = induce_sumcheck_poly_auto_base(
        n1,
        log_inv_rate_0,
        &sks_vks_n1,
        &ordered_rows_0,
        &r_lane_fold,
        &queries_0,
        &alpha_0,
    );

    // Intro + glue.
    if tx_idx >= proof.sumcheck_transcript.len() {
        return false;
    }
    let intro_msg_0 = proof.sumcheck_transcript[tx_idx];
    tx_idx += 1;
    observe_ext(sponge, intro_msg_0.u_0);
    observe_ext(sponge, intro_msg_0.u_2);
    let intro_quad_0 = RoundQuadK::from_msg(intro_msg_0, enforced_sum_0);
    let beta_0 = sample_ext(sponge);
    running_quad = RoundQuadK::fold(&running_quad, &intro_quad_0, beta_0);
    t_r += beta_0 * enforced_sum_0;

    // Basis poly tracking for the residual check. b_initial folds at ALL ris;
    // basis_0_induced starts after the lane folds.
    let mut basis_polys: Vec<Vec<F128T>> = vec![b_initial.to_vec(), basis_0_induced];
    let mut basis_ris_starts: Vec<usize> = vec![0, initial_k];
    let mut basis_separations: Vec<F128T> = vec![beta_0];
    let mut ris: Vec<F128T> = r_lane_fold.clone();

    let mut prev_root = root_1;
    let mut prev_log_num_interleaved = config.level_ks[0];
    let mut prev_log_msg_cols = n1 - prev_log_num_interleaved;
    let mut prev_log_inv_rate = config.log_inv_rates[1];
    let mut next_root_idx = 1usize;
    let mut recursive_proof_idx = 0usize;
    let mut n_current = n1;

    for i in 0..r {
        let k_i = config.level_ks[i];
        if n_current < k_i {
            return false;
        }
        let mut level_rs = Vec::with_capacity(k_i);
        for j in 0..k_i {
            // Fold-challenge PoW mirror (level i+1's folds), tapered.
            let bits = fold_bits(i + 1).saturating_sub(j as u32);
            if bits > 0 {
                if fold_nonce_idx >= proof.fold_grinding_nonces.len() {
                    return false;
                }
                if !sponge.verify_pow(proof.fold_grinding_nonces[fold_nonce_idx], bits) {
                    return false;
                }
                fold_nonce_idx += 1;
            }
            let ri = sample_ext(sponge);
            ris.push(ri);
            level_rs.push(ri);
            t_r = running_quad.eval(ri);
            if tx_idx >= proof.sumcheck_transcript.len() {
                return false;
            }
            let msg = proof.sumcheck_transcript[tx_idx];
            tx_idx += 1;
            observe_ext(sponge, msg.u_0);
            observe_ext(sponge, msg.u_2);
            running_quad = RoundQuadK::from_msg(msg, t_r);
        }
        n_current -= k_i;

        if i == r - 1 {
            if tx_idx != proof.sumcheck_transcript.len() {
                return false;
            }
            if fold_nonce_idx != proof.fold_grinding_nonces.len() {
                return false;
            }
            let yr = &proof.final_proof.yr;
            if yr.len() != 1 << n_current {
                return false;
            }
            for v in yr {
                observe_ext(sponge, *v);
            }
            // PoW grinding check for the last level.
            if nonce_idx >= proof.grinding_nonces.len() {
                return false;
            }
            if !sponge.verify_pow(
                proof.grinding_nonces[nonce_idx],
                config.grinding_bits[i + 1] as u32,
            ) {
                return false;
            }
            // (last nonce: nonce_idx is not advanced past it)

            let prev_block_len = 1usize << (prev_log_msg_cols + prev_log_inv_rate);
            let prev_num_interleaved = 1usize << prev_log_num_interleaved;
            let num_queries_last = config.queries[i + 1];
            let queries_last =
                sample_queries_ordered_k(sponge, prev_block_len, num_queries_last);
            // Final-level basis-induction challenge: sampled AFTER `yr` was
            // observed and the queries are fixed, so a forged `yr` cannot be
            // adapted to it (mirror of the original).
            let alpha_last = sample_ext_vec(sponge, log2_ceil(num_queries_last));
            let sq_last = sorted_unique_queries_k(&queries_last);
            if !verify_level_opens_ext(
                &prev_root,
                prev_block_len,
                &sq_last,
                &proof.final_proof.opened_rows,
                prev_num_interleaved,
                &proof.final_proof.merkle_proof,
            ) {
                return false;
            }
            let ordered_rows_last =
                match fan_rows_to_ordered(&queries_last, &proof.final_proof.opened_rows) {
                    Some(x) => x,
                    None => return false,
                };

            // Bind the LAST commitment to `yr`: induce its opened rows into
            // the sumcheck like every non-final level, batched with a fresh
            // `beta_last` (see the original's binding-fix comment).
            let sks_vks_last = eval_sk_at_vks_k(n_current);
            let (basis_last_induced, enforced_sum_last) = induce_sumcheck_poly_ext(
                n_current,
                &sks_vks_last,
                &ordered_rows_last,
                &level_rs,
                &queries_last,
                &alpha_last,
            );
            let beta_last = sample_ext(sponge);
            t_r += beta_last * enforced_sum_last;
            basis_polys.push(basis_last_induced);
            basis_ris_starts.push(ris.len());
            basis_separations.push(beta_last);

            // Residual check.
            let yr_len = yr.len();
            let mut combined = vec![F128T::ZERO; yr_len];
            for (k, basis) in basis_polys.iter().enumerate() {
                let start = basis_ris_starts[k];
                let residual = partial_eval_lsb_ext(basis, &ris[start..]);
                if residual.len() != yr_len {
                    return false;
                }
                let sep = if k == 0 {
                    F128T::ONE
                } else {
                    basis_separations[k - 1]
                };
                for (c, &rr) in combined.iter_mut().zip(residual.iter()) {
                    *c += sep * rr;
                }
            }
            let inner: F128T = yr
                .iter()
                .zip(combined.iter())
                .map(|(&y, &c)| y * c)
                .fold(F128T::ZERO, |a, v| a + v);
            return inner == t_r;
        }

        if next_root_idx >= proof.recursive_roots.len() {
            return false;
        }
        let root_next = proof.recursive_roots[next_root_idx];
        next_root_idx += 1;
        observe_root(sponge, &root_next);

        // (OOD binding mirror elided.)

        // PoW grinding check for this iteration's query phase.
        if nonce_idx >= proof.grinding_nonces.len() {
            return false;
        }
        if !sponge.verify_pow(
            proof.grinding_nonces[nonce_idx],
            config.grinding_bits[i + 1] as u32,
        ) {
            return false;
        }
        nonce_idx += 1;

        let prev_block_len = 1usize << (prev_log_msg_cols + prev_log_inv_rate);
        let prev_num_interleaved = 1usize << prev_log_num_interleaved;
        let num_queries_i = config.queries[i + 1];
        let queries_i = sample_queries_ordered_k(sponge, prev_block_len, num_queries_i);
        let sq_i = sorted_unique_queries_k(&queries_i);
        let alpha_i = sample_ext_vec(sponge, log2_ceil(num_queries_i));
        if recursive_proof_idx >= proof.recursive_proofs.len() {
            return false;
        }
        let rp = &proof.recursive_proofs[recursive_proof_idx];
        recursive_proof_idx += 1;
        if !verify_level_opens_ext(
            &prev_root,
            prev_block_len,
            &sq_i,
            &rp.opened_rows,
            prev_num_interleaved,
            &rp.merkle_proof,
        ) {
            return false;
        }
        let ordered_rows_i = match fan_rows_to_ordered(&queries_i, &rp.opened_rows) {
            Some(x) => x,
            None => return false,
        };

        let sks_vks_i = eval_sk_at_vks_k(n_current);
        let (basis_i_induced, enforced_sum_i) = induce_sumcheck_poly_ext(
            n_current,
            &sks_vks_i,
            &ordered_rows_i,
            &level_rs,
            &queries_i,
            &alpha_i,
        );

        if tx_idx >= proof.sumcheck_transcript.len() {
            return false;
        }
        let intro_msg_i = proof.sumcheck_transcript[tx_idx];
        tx_idx += 1;
        observe_ext(sponge, intro_msg_i.u_0);
        observe_ext(sponge, intro_msg_i.u_2);
        let intro_quad_i = RoundQuadK::from_msg(intro_msg_i, enforced_sum_i);
        let beta_i = sample_ext(sponge);
        running_quad = RoundQuadK::fold(&running_quad, &intro_quad_i, beta_i);
        t_r += beta_i * enforced_sum_i;
        basis_polys.push(basis_i_induced);
        basis_ris_starts.push(ris.len());
        basis_separations.push(beta_i);

        prev_root = root_next;
        let k_next = config.level_ks[i + 1];
        if n_current < k_next {
            return false;
        }
        prev_log_num_interleaved = k_next;
        prev_log_msg_cols = n_current - k_next;
        prev_log_inv_rate = config.log_inv_rates[i + 2];
    }

    unreachable!()
}

// ===================================================================
// Succinct verifier
// ===================================================================

/// Succinct verifier for [`recursive_prover_with_basis_k`] (mirror of
/// `ligerito::recursive_verifier_with_basis_succinct`): instead of a dense
/// `b_initial` (2^log_n E-values) it takes a closure `eval_b_residual` that
/// evaluates b's multilinear extension at the residual. The closure is called
/// ONCE at the final check with the full `ris` and `yr_log_n`, and must
/// return the `2^yr_log_n` values `eval_b(ris ++ y_bits)` for
/// `y in [0, 2^yr_log_n)` (batching lets callers amortize prefix work).
///
/// Per-level induced bases are never materialized: intro time uses the cheap
/// enforced-sum recomputation, and the residual uses the closed-form
/// [`induce_sumcheck_evaluate_at_residual_k`]. `log_n` is the committed
/// K-witness log size (b's logical dimension). Transcript replay is
/// byte-identical to the dense verifier (OOD elided; config must take zero
/// OOD samples, as asserted by the prover).
/// Thin wrapper of [`recursive_verifier_with_basis_succinct_k_with_squeezes`]
/// that discards the query squeezes — the signature every non-recursion caller
/// uses.
pub fn recursive_verifier_with_basis_succinct_k<F>(
    config: &VerifierConfig,
    proof: &LigeritoProofK,
    log_n: usize,
    target: F128T,
    expected_initial_root: &Hash,
    eval_b_residual: F,
    sponge: &mut Sponge,
) -> bool
where
    F: Fn(&[F128T], usize) -> Vec<F128T>,
{
    let mut discard = Vec::new();
    recursive_verifier_with_basis_succinct_k_with_squeezes(
        config,
        proof,
        log_n,
        target,
        expected_initial_root,
        eval_b_residual,
        sponge,
        &mut discard,
    )
}

/// As [`recursive_verifier_with_basis_succinct_k`], but on accept fills
/// `query_squeezes_out` with the raw query-sampling squeezes per level in
/// transcript order (the recursion harness reads `.c0/.c1` off them to re-derive
/// query positions). Left partially filled on reject; use it only on `true`.
pub fn recursive_verifier_with_basis_succinct_k_with_squeezes<F>(
    config: &VerifierConfig,
    proof: &LigeritoProofK,
    log_n: usize,
    target: F128T,
    expected_initial_root: &Hash,
    eval_b_residual: F,
    sponge: &mut Sponge,
    query_squeezes_out: &mut Vec<Vec<F128T>>,
) -> bool
where
    // Called ONCE at the residual check with the full ris and yr_log_n.
    F: Fn(&[F128T], usize) -> Vec<F128T>,
{
    let initial_k = config.initial_k;
    let r = config.level_steps;
    if r < 1 || config.level_ks.len() != r || config.log_inv_rates.len() != r + 1 {
        return false;
    }
    // OOD is not ported; reject configs that would require it.
    if config.ood_samples.iter().any(|&s| s != 0) {
        return false;
    }

    // The L0 root is the caller's statement (not proof data): absorb it
    // exactly where the prover absorbed its own.
    // (No opener domain-label absorb: the extension-field opener has none and the recursion
    // guest replays a label-free opening transcript; the observed `target` +
    // outer transcript context provide domain separation.)
    observe_ext(sponge, target);
    observe_root(sponge, expected_initial_root);

    let log_inv_rate_0 = config.log_inv_rates[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
    let num_interleaved_0 = 1usize << initial_k;

    let mut t_r = target;
    let mut tx_idx = 0usize;
    if tx_idx >= proof.sumcheck_transcript.len() {
        return false;
    }
    let start_msg = proof.sumcheck_transcript[tx_idx];
    tx_idx += 1;
    observe_ext(sponge, start_msg.u_0);
    observe_ext(sponge, start_msg.u_2);
    let mut running_quad = RoundQuadK::from_msg(start_msg, t_r);

    let fold_bits =
        |lvl: usize| -> u32 { config.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as u32 };
    let mut fold_nonce_idx = 0usize;

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        // Fold-challenge PoW mirror (L0's lane folds), tapered per round.
        let bits = fold_bits(0).saturating_sub(j as u32);
        if bits > 0 {
            if fold_nonce_idx >= proof.fold_grinding_nonces.len() {
                return false;
            }
            if !sponge.verify_pow(proof.fold_grinding_nonces[fold_nonce_idx], bits) {
                return false;
            }
            fold_nonce_idx += 1;
        }
        let ri = sample_ext(sponge);
        r_lane_fold.push(ri);
        t_r = running_quad.eval(ri);
        if tx_idx >= proof.sumcheck_transcript.len() {
            return false;
        }
        let msg = proof.sumcheck_transcript[tx_idx];
        tx_idx += 1;
        observe_ext(sponge, msg.u_0);
        observe_ext(sponge, msg.u_2);
        running_quad = RoundQuadK::from_msg(msg, t_r);
    }

    if proof.recursive_roots.is_empty() {
        return false;
    }
    let root_1 = proof.recursive_roots[0];
    observe_root(sponge, &root_1);

    // (OOD binding mirror elided: zero samples enforced above.)

    // PoW grinding check for L0's query phase.
    let mut nonce_idx = 0usize;
    if nonce_idx >= proof.grinding_nonces.len() {
        return false;
    }
    if !sponge.verify_pow(
        proof.grinding_nonces[nonce_idx],
        config.grinding_bits[0] as u32,
    ) {
        return false;
    }
    nonce_idx += 1;

    let num_queries_0 = config.queries[0];
    let (queries_0, raw_0) =
        sample_queries_ordered_with_raw_k(sponge, block_len_0, num_queries_0);
    query_squeezes_out.push(raw_0);
    let alpha_0 = sample_ext_vec(sponge, log2_ceil(num_queries_0));
    let sq_0 = sorted_unique_queries_k(&queries_0);
    if !verify_level_opens_base(
        expected_initial_root,
        block_len_0,
        &sq_0,
        &proof.initial_proof.opened_rows,
        num_interleaved_0,
        &proof.initial_proof.merkle_proof,
    ) {
        return false;
    }
    let ordered_rows_0 = match fan_rows_to_ordered(&queries_0, &proof.initial_proof.opened_rows) {
        Some(x) => x,
        None => return false,
    };

    // Compute enforced_sum cheaply at intro time. The induced basis poly's
    // residual evaluations are deferred to the final closed-form check.
    let n1 = log_n - initial_k;
    let enforced_sum_0 = induce_sumcheck_enforced_sum_base(
        &ordered_rows_0,
        &r_lane_fold,
        &queries_0,
        &alpha_0,
    );

    if tx_idx >= proof.sumcheck_transcript.len() {
        return false;
    }
    let intro_msg_0 = proof.sumcheck_transcript[tx_idx];
    tx_idx += 1;
    observe_ext(sponge, intro_msg_0.u_0);
    observe_ext(sponge, intro_msg_0.u_2);
    let intro_quad_0 = RoundQuadK::from_msg(intro_msg_0, enforced_sum_0);
    let beta_0 = sample_ext(sponge);
    running_quad = RoundQuadK::fold(&running_quad, &intro_quad_0, beta_0);
    t_r += beta_0 * enforced_sum_0;

    // Per-level induced-basis evaluation context: small (no dense vec).
    struct LevelCtx {
        log_msg_cols: usize,
        queries: Vec<usize>,
        alpha: Vec<F128T>, // ceil(log2 Q) elements (eq-tensor combination)
        ris_start: usize,
        beta: F128T,
    }
    let mut level_ctxs: Vec<LevelCtx> = vec![LevelCtx {
        log_msg_cols: n1,
        queries: queries_0.clone(),
        alpha: alpha_0,
        ris_start: initial_k,
        beta: beta_0,
    }];
    let mut ris: Vec<F128T> = r_lane_fold.clone();

    let mut prev_root = root_1;
    let mut prev_log_num_interleaved = config.level_ks[0];
    let mut prev_log_msg_cols = n1 - prev_log_num_interleaved;
    let mut prev_log_inv_rate = config.log_inv_rates[1];
    let mut next_root_idx = 1usize;
    let mut recursive_proof_idx = 0usize;
    let mut n_current = n1;

    for i in 0..r {
        let k_i = config.level_ks[i];
        if n_current < k_i {
            return false;
        }
        let mut level_rs = Vec::with_capacity(k_i);
        for j in 0..k_i {
            // Fold-challenge PoW mirror (level i+1's folds), tapered.
            let bits = fold_bits(i + 1).saturating_sub(j as u32);
            if bits > 0 {
                if fold_nonce_idx >= proof.fold_grinding_nonces.len() {
                    return false;
                }
                if !sponge.verify_pow(proof.fold_grinding_nonces[fold_nonce_idx], bits) {
                    return false;
                }
                fold_nonce_idx += 1;
            }
            let ri = sample_ext(sponge);
            ris.push(ri);
            level_rs.push(ri);
            t_r = running_quad.eval(ri);
            if tx_idx >= proof.sumcheck_transcript.len() {
                return false;
            }
            let msg = proof.sumcheck_transcript[tx_idx];
            tx_idx += 1;
            observe_ext(sponge, msg.u_0);
            observe_ext(sponge, msg.u_2);
            running_quad = RoundQuadK::from_msg(msg, t_r);
        }
        n_current -= k_i;

        if i == r - 1 {
            if tx_idx != proof.sumcheck_transcript.len() {
                return false;
            }
            if fold_nonce_idx != proof.fold_grinding_nonces.len() {
                return false;
            }
            let yr = &proof.final_proof.yr;
            if yr.len() != 1 << n_current {
                return false;
            }
            for v in yr {
                observe_ext(sponge, *v);
            }
            // PoW grinding check for the last level's query phase.
            if nonce_idx >= proof.grinding_nonces.len() {
                return false;
            }
            if !sponge.verify_pow(
                proof.grinding_nonces[nonce_idx],
                config.grinding_bits[i + 1] as u32,
            ) {
                return false;
            }
            // (last nonce: nonce_idx is not advanced past it)

            let prev_block_len = 1usize << (prev_log_msg_cols + prev_log_inv_rate);
            let prev_num_interleaved = 1usize << prev_log_num_interleaved;
            let num_queries_last = config.queries[i + 1];
            let (queries_last, raw_last) =
                sample_queries_ordered_with_raw_k(sponge, prev_block_len, num_queries_last);
            query_squeezes_out.push(raw_last);
            // Basis-induction challenge for the LAST commitment, sampled after
            // `yr` was observed and the queries are fixed (mirror of the
            // dense verifier, so both stay in lockstep).
            let alpha_last = sample_ext_vec(sponge, log2_ceil(num_queries_last));
            let sq_last = sorted_unique_queries_k(&queries_last);
            if !verify_level_opens_ext(
                &prev_root,
                prev_block_len,
                &sq_last,
                &proof.final_proof.opened_rows,
                prev_num_interleaved,
                &proof.final_proof.merkle_proof,
            ) {
                return false;
            }
            let ordered_rows_last =
                match fan_rows_to_ordered(&queries_last, &proof.final_proof.opened_rows) {
                    Some(x) => x,
                    None => return false,
                };

            // Bind the LAST commitment to `yr` (same tie as the dense
            // verifier): its induced basis is already at the residual
            // dimension (zero further folds), so it joins `combined` below
            // via this LevelCtx.
            let enforced_sum_last = induce_sumcheck_enforced_sum_ext(
                &ordered_rows_last,
                &level_rs,
                &queries_last,
                &alpha_last,
            );
            let beta_last = sample_ext(sponge);
            t_r += beta_last * enforced_sum_last;
            level_ctxs.push(LevelCtx {
                log_msg_cols: n_current,
                queries: queries_last.clone(),
                alpha: alpha_last,
                ris_start: ris.len(),
                beta: beta_last,
            });

            // Succinct residual check: per-level induced basis evaluations
            // via closed-form (no dense materialization).
            let yr_len = yr.len();
            let yr_log_n = n_current;

            let induced_residuals: Vec<Vec<F128T>> = level_ctxs
                .iter()
                .map(|ctx| {
                    let sks_vks = eval_sk_at_vks_k(ctx.log_msg_cols);
                    let ris_for_basis =
                        &ris[ctx.ris_start..ctx.ris_start + ctx.log_msg_cols - yr_log_n];
                    induce_sumcheck_evaluate_at_residual_k(
                        ctx.log_msg_cols,
                        &sks_vks,
                        &ctx.queries,
                        &ctx.alpha,
                        ris_for_basis,
                        yr_log_n,
                    )
                })
                .collect();
            for resid in &induced_residuals {
                if resid.len() != yr_len {
                    return false;
                }
            }

            // Batch-evaluate b at all yr positions in one call so the caller
            // can amortize prefix work.
            let evb_vec = eval_b_residual(&ris, yr_log_n);
            if evb_vec.len() != yr_len {
                return false;
            }
            let mut inner = F128T::ZERO;
            for y in 0..yr_len {
                let mut combined_y = evb_vec[y];
                for (k, residual) in induced_residuals.iter().enumerate() {
                    combined_y += level_ctxs[k].beta * residual[y];
                }
                inner += yr[y] * combined_y;
            }
            return inner == t_r;
        }

        if next_root_idx >= proof.recursive_roots.len() {
            return false;
        }
        let root_next = proof.recursive_roots[next_root_idx];
        next_root_idx += 1;
        observe_root(sponge, &root_next);

        // (OOD binding mirror elided.)

        // PoW grinding check for this iteration's query phase.
        if nonce_idx >= proof.grinding_nonces.len() {
            return false;
        }
        if !sponge.verify_pow(
            proof.grinding_nonces[nonce_idx],
            config.grinding_bits[i + 1] as u32,
        ) {
            return false;
        }
        nonce_idx += 1;

        let prev_block_len = 1usize << (prev_log_msg_cols + prev_log_inv_rate);
        let prev_num_interleaved = 1usize << prev_log_num_interleaved;
        let num_queries_i = config.queries[i + 1];
        let (queries_i, raw_i) =
            sample_queries_ordered_with_raw_k(sponge, prev_block_len, num_queries_i);
        query_squeezes_out.push(raw_i);
        let sq_i = sorted_unique_queries_k(&queries_i);
        let alpha_i = sample_ext_vec(sponge, log2_ceil(num_queries_i));
        if recursive_proof_idx >= proof.recursive_proofs.len() {
            return false;
        }
        let rp = &proof.recursive_proofs[recursive_proof_idx];
        recursive_proof_idx += 1;
        if !verify_level_opens_ext(
            &prev_root,
            prev_block_len,
            &sq_i,
            &rp.opened_rows,
            prev_num_interleaved,
            &rp.merkle_proof,
        ) {
            return false;
        }
        let ordered_rows_i = match fan_rows_to_ordered(&queries_i, &rp.opened_rows) {
            Some(x) => x,
            None => return false,
        };

        let enforced_sum_i =
            induce_sumcheck_enforced_sum_ext(&ordered_rows_i, &level_rs, &queries_i, &alpha_i);

        if tx_idx >= proof.sumcheck_transcript.len() {
            return false;
        }
        let intro_msg_i = proof.sumcheck_transcript[tx_idx];
        tx_idx += 1;
        observe_ext(sponge, intro_msg_i.u_0);
        observe_ext(sponge, intro_msg_i.u_2);
        let intro_quad_i = RoundQuadK::from_msg(intro_msg_i, enforced_sum_i);
        let beta_i = sample_ext(sponge);
        running_quad = RoundQuadK::fold(&running_quad, &intro_quad_i, beta_i);
        t_r += beta_i * enforced_sum_i;
        level_ctxs.push(LevelCtx {
            log_msg_cols: n_current,
            queries: queries_i.clone(),
            alpha: alpha_i,
            ris_start: ris.len(),
            beta: beta_i,
        });

        prev_root = root_next;
        let k_next = config.level_ks[i + 1];
        if n_current < k_next {
            return false;
        }
        prev_log_num_interleaved = k_next;
        prev_log_msg_cols = n_current - k_next;
        prev_log_inv_rate = config.log_inv_rates[i + 2];
    }

    unreachable!()
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ligerito::{default_config, default_verifier_config};

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

    /// Configs for a K-witness of `2^log_n` elements. Prefers the strict
    /// Secure-profile derivation (the production path, [`k_configs_for`]);
    /// its ladder needs L0 block_len >= ~300 queries, i.e. log_n >= 14, so
    /// smaller test sizes fall back to the ad-hoc `default_config` shape
    /// (test-only; same fallback the main crate uses for small instances).
    fn configs_for(log_n: usize) -> (ProverConfig, VerifierConfig) {
        match k_configs_for(log_n) {
            Ok(pv) => pv,
            Err(_) => {
                let pc = default_config(log_n, 5, 1).unwrap();
                let vc = default_verifier_config(log_n, 5, 1).unwrap();
                (pc, vc)
            }
        }
    }

    struct Instance {
        vc: VerifierConfig,
        log_n: usize,
        /// The eq-point behind `b_initial` (for the succinct closure).
        point: Vec<F128T>,
        b_initial: Vec<F128T>,
        target: F128T,
        root: Hash,
        proof: LigeritoProofK,
    }

    fn prove_instance(log_n: usize, seed: u64) -> Instance {
        let (pc, vc) = configs_for(log_n);
        let mut s = seed;
        let witness: Vec<F64> = (0..1usize << log_n)
            .map(|_| F64(splitmix64(&mut s)))
            .collect();
        let (cm, pd) = commit_k(&witness, pc.initial_k, pc.log_inv_rates[0]);
        let point: Vec<F128T> = (0..log_n).map(|_| rand_ext(&mut s)).collect();
        let b_initial = build_eq_table_ext(&point);
        let target = inner_product_base_ext(&witness, &b_initial);
        let mut ch = Sponge::new(b"ligerito-k-test", &[]);
        let proof = recursive_prover_with_basis_k(
            &pc,
            &witness,
            b_initial.clone(),
            target,
            &pd.codeword,
            &pd.merkle_tree,
            &mut ch,
        );
        Instance {
            vc,
            log_n,
            point,
            b_initial,
            target,
            root: cm.root,
            proof,
        }
    }

    fn verify_instance(inst: &Instance, proof: &LigeritoProofK) -> bool {
        let mut ch = Sponge::new(b"ligerito-k-test", &[]);
        recursive_verifier_with_basis_k(
            &inst.vc,
            proof,
            &inst.b_initial,
            inst.target,
            &inst.root,
            &mut ch,
        )
    }

    /// Succinct verify with the eq-point residual closure: for b = eq(point, ·)
    /// (LSB-first), `eval_b(ris ++ y_bits)` factors into the char-2 eq prefix
    /// over the folded variables times the eq table over the residual tail:
    ///   `Π_{j<split} (1 + point[j] + ris[j]) · eq_table(point[split..])[y]`.
    fn verify_succinct_instance(inst: &Instance, proof: &LigeritoProofK) -> bool {
        let mut ch = Sponge::new(b"ligerito-k-test", &[]);
        let point = &inst.point;
        let log_n = inst.log_n;
        recursive_verifier_with_basis_succinct_k(
            &inst.vc,
            proof,
            log_n,
            inst.target,
            &inst.root,
            |ris, yr_log_n| {
                let split = log_n - yr_log_n;
                assert_eq!(ris.len(), split, "closure gets the full folded ris");
                let mut prefix = F128T::ONE;
                for j in 0..split {
                    prefix *= F128T::ONE + point[j] + ris[j];
                }
                let mut tail = build_eq_table_ext(&point[split..]);
                for v in tail.iter_mut() {
                    *v *= prefix;
                }
                tail
            },
            &mut ch,
        )
    }

    /// Both verifiers on the same proof, asserting they agree; returns the
    /// shared verdict.
    fn verify_both_agree(inst: &Instance, proof: &LigeritoProofK, what: &str) -> bool {
        let dense = verify_instance(inst, proof);
        let succinct = verify_succinct_instance(inst, proof);
        assert_eq!(dense, succinct, "dense/succinct verdict split on {what}");
        dense
    }

    /// Pin that the log_n = 16 roundtrip exercises the strict Secure-profile
    /// derivation (not the small-size fallback): the ladder must exist and
    /// carry the L0 lane fold at initial_k = 6 with nonzero L0 fold grinding.
    #[test]
    fn k_configs_secure_profile_shape() {
        let (pc, vc) = k_configs_for(16).expect("Secure profile feasible at log_n = 16");
        assert_eq!(pc.initial_k, 6);
        assert!(pc.level_steps >= 1);
        assert_eq!(vc.initial_k, pc.initial_k);
        assert!(pc.ood_samples.iter().all(|&s| s == 0));
        // And log_n = 12 is below the Secure ladder's feasibility floor, so
        // the tests there use the default_config fallback.
        assert!(k_configs_for(12).is_err());
    }

    /// The parallel eq builder must be byte-identical to the serial one, and
    /// the seeded variant must equal the gamma-scaled table, at sizes on both
    /// sides of the internal parallel level floor (2^12 halves, so n = 15
    /// exercises parallel levels; n = 6 stays fully serial).
    #[test]
    fn eq_table_parallel_and_seeded_match_serial() {
        let mut s = 21u64;
        for n in [0usize, 1, 6, 13, 15] {
            let point: Vec<F128T> = (0..n).map(|_| rand_ext(&mut s)).collect();
            let serial = build_eq_table_ext(&point);
            assert_eq!(build_eq_table_ext_parallel(&point), serial, "parallel mismatch at n={n}");
            let g = rand_ext(&mut s);
            let mut seeded = vec![F128T::ZERO; 1 << n];
            build_eq_table_ext_seeded_into(&point, g, &mut seeded);
            let scaled: Vec<F128T> = serial.iter().map(|&e| g * e).collect();
            assert_eq!(seeded, scaled, "seeded mismatch at n={n}");
        }
    }

    #[test]
    fn roundtrip_log_n_12() {
        let inst = prove_instance(12, 1);
        assert!(verify_instance(&inst, &inst.proof), "honest proof rejected");
    }

    #[test]
    fn roundtrip_log_n_16() {
        let inst = prove_instance(16, 2);
        assert!(verify_instance(&inst, &inst.proof), "honest proof rejected");
    }

    /// At log_n = 18 (Secure profile) L0 has log_msg_cols = 12 and ~290
    /// queries, which trips the sparse transposed-NTT dispatch in BOTH the
    /// prover and the dense verifier; pin the heuristic, then roundtrip.
    #[test]
    fn roundtrip_log_n_18_sparse_induce() {
        let (pc, _) = k_configs_for(18).expect("Secure profile feasible at log_n = 18");
        assert!(
            induce_use_ntt_heuristic(18 - pc.initial_k, pc.log_inv_rates[0], pc.queries[0]),
            "shape must select the sparse transposed-NTT induce at L0"
        );
        // And the smaller roundtrips stay on the dense path (cols < 12).
        let (pc16, _) = k_configs_for(16).unwrap();
        assert!(!induce_use_ntt_heuristic(
            16 - pc16.initial_k,
            pc16.log_inv_rates[0],
            pc16.queries[0]
        ));
        let inst = prove_instance(18, 8);
        assert!(verify_instance(&inst, &inst.proof), "honest proof rejected");
    }

    /// The succinct verifier accepts the same honest proofs the dense one
    /// does, driven through the eq-point residual closure (LSB-first).
    #[test]
    fn succinct_roundtrips() {
        for (log_n, seed) in [(16usize, 2u64), (18, 8)] {
            let inst = prove_instance(log_n, seed);
            assert!(
                verify_succinct_instance(&inst, &inst.proof),
                "succinct verifier rejected an honest proof at log_n={log_n}"
            );
        }
    }

    /// The succinct verifier rejects the same tamper cases the dense one does.
    #[test]
    fn succinct_rejects_tampered() {
        let inst = prove_instance(12, 3);
        let mut bad = inst.proof.clone();
        bad.initial_proof.opened_rows[0][0].0 ^= 1;
        assert!(
            !verify_succinct_instance(&inst, &bad),
            "bit-flipped L0 opened row must be rejected"
        );
        let mut bad2 = inst.proof.clone();
        bad2.final_proof.opened_rows[0][0].c0 ^= 1;
        assert!(
            !verify_succinct_instance(&inst, &bad2),
            "bit-flipped final-level opened row must be rejected"
        );
        let mut bad3 = inst.proof.clone();
        bad3.sumcheck_transcript[0].u_0.c0 ^= 1;
        assert!(
            !verify_succinct_instance(&inst, &bad3),
            "bit-flipped sumcheck u_0 must be rejected"
        );
    }

    /// Dense and succinct must return the same verdict on every proof:
    /// honest plus a spread of randomized single-bit tampers, at both a
    /// fallback-config shape (log_n = 12) and a Secure-profile shape with a
    /// fold-grinding nonce (log_n = 16).
    #[test]
    fn dense_and_succinct_agree() {
        for (log_n, seed) in [(12usize, 11u64), (16, 12)] {
            let inst = prove_instance(log_n, seed);
            assert!(verify_both_agree(&inst, &inst.proof, "honest proof"));

            let mut s = seed ^ 0xABCD;
            type Tamper = fn(&mut LigeritoProofK, u64);
            let tampers: &[(&str, Tamper)] = &[
                ("L0 opened row", |p, r| {
                    let row = (r as usize) % p.initial_proof.opened_rows.len();
                    p.initial_proof.opened_rows[row][0].0 ^= 1;
                }),
                ("sumcheck u_2", |p, r| {
                    let idx = (r as usize) % p.sumcheck_transcript.len();
                    p.sumcheck_transcript[idx].u_2.c1 ^= 1;
                }),
                ("yr value", |p, r| {
                    let idx = (r as usize) % p.final_proof.yr.len();
                    p.final_proof.yr[idx].c0 ^= 1;
                }),
                ("recursive root", |p, _| {
                    p.recursive_roots[0][0] ^= 1;
                }),
                ("merkle proof node", |p, r| {
                    let idx = (r as usize) % p.initial_proof.merkle_proof.len();
                    p.initial_proof.merkle_proof[idx][0] ^= 1;
                }),
                ("grinding nonce", |p, _| {
                    p.grinding_nonces[0] ^= 1;
                }),
            ];
            for (what, tamper) in tampers {
                let mut bad = inst.proof.clone();
                tamper(&mut bad, splitmix64(&mut s));
                assert!(
                    !verify_both_agree(&inst, &bad, what),
                    "tampered {what} accepted at log_n={log_n}"
                );
            }
            // Fold-grinding nonce tamper (present only under the Secure
            // profile's nonzero L0 fold grinding, i.e. log_n = 16 here).
            if !inst.proof.fold_grinding_nonces.is_empty() {
                let mut bad = inst.proof.clone();
                bad.fold_grinding_nonces[0] ^= 1;
                assert!(
                    !verify_both_agree(&inst, &bad, "fold-grinding nonce"),
                    "tampered fold-grinding nonce accepted at log_n={log_n}"
                );
            }
        }
    }

    #[test]
    fn proving_is_deterministic() {
        let a = prove_instance(12, 7);
        let b = prove_instance(12, 7);
        assert_eq!(a.proof, b.proof, "same inputs must yield identical proofs");
    }

    #[test]
    fn tampered_opened_row_rejects() {
        let inst = prove_instance(12, 3);
        let mut bad = inst.proof.clone();
        bad.initial_proof.opened_rows[0][0].0 ^= 1;
        assert!(
            !verify_instance(&inst, &bad),
            "bit-flipped L0 opened row must be rejected"
        );
        // Also flip a deeper (E-valued) row for good measure.
        let mut bad2 = inst.proof.clone();
        bad2.final_proof.opened_rows[0][0].c0 ^= 1;
        assert!(
            !verify_instance(&inst, &bad2),
            "bit-flipped final-level opened row must be rejected"
        );
    }

    #[test]
    fn tampered_sumcheck_u0_rejects() {
        let inst = prove_instance(12, 4);
        let mut bad = inst.proof.clone();
        bad.sumcheck_transcript[0].u_0.c0 ^= 1;
        assert!(
            !verify_instance(&inst, &bad),
            "bit-flipped sumcheck u_0 must be rejected"
        );
    }

    /// The E-valued interleaved NTT with K-twiddles must act lane-wise on the
    /// tower coordinates: transforming (c0, c1) packed as F128T equals two
    /// independent F64 transforms of the c0 and c1 lanes.
    #[test]
    fn ext_ntt_matches_two_base_ntts() {
        let mut s = 5u64;
        for (log_d, lanes, start_layer) in [(6usize, 4usize, 0usize), (9, 2, 2), (10, 1, 1)] {
            let ntt = AdditiveNttF64::standard(log_d);
            let n = (1usize << log_d) * lanes;
            let ext: Vec<F128T> = (0..n).map(|_| rand_ext(&mut s)).collect();
            let mut c0: Vec<F64> = ext.iter().map(|e| F64(e.c0)).collect();
            let mut c1: Vec<F64> = ext.iter().map(|e| F64(e.c1)).collect();
            let mut ext_t = ext.clone();
            forward_transform_interleaved_ext_from_layer(&ntt, &mut ext_t, lanes, start_layer);
            ntt.forward_transform_interleaved_from_layer(&mut c0, lanes, start_layer);
            ntt.forward_transform_interleaved_from_layer(&mut c1, lanes, start_layer);
            for i in 0..n {
                assert_eq!(ext_t[i], F128T::new(c0[i].0, c1[i].0), "mismatch at {i}");
            }
        }
    }

    /// The sparse transposed-NTT induce must be byte-identical to the dense
    /// LCH-expansion induce (same guarantee the original pins). Covers both
    /// the windowed sparse-prefix path (log_block >= 12, k = 8) and the
    /// scatter + full-dense-transpose path (log_block < 12, k = 0).
    #[test]
    fn induce_via_ntt_matches_dense() {
        let mut s = 9u64;
        for (log_msg_cols, log_inv_rate, lanes_log, n_queries) in
            [(12usize, 1usize, 5usize, 130usize), (6, 2, 3, 40)]
        {
            let block_len = 1usize << (log_msg_cols + log_inv_rate);
            let lanes = 1usize << lanes_log;
            // Distinct sorted query positions plus one aligned random row each.
            let mut qs: Vec<usize> = Vec::new();
            let mut seen = std::collections::HashSet::new();
            while qs.len() < n_queries {
                let q = (splitmix64(&mut s) as usize) % block_len;
                if seen.insert(q) {
                    qs.push(q);
                }
            }
            qs.sort_unstable();
            let rows: Vec<Vec<F64>> = (0..n_queries)
                .map(|_| (0..lanes).map(|_| F64(splitmix64(&mut s))).collect())
                .collect();
            let v_challenges: Vec<F128T> = (0..lanes_log).map(|_| rand_ext(&mut s)).collect();
            let alpha: Vec<F128T> = (0..log2_ceil(n_queries)).map(|_| rand_ext(&mut s)).collect();

            let sks_vks = eval_sk_at_vks_k(log_msg_cols);
            let dense = induce_sumcheck_poly_base(
                log_msg_cols,
                &sks_vks,
                &rows,
                &v_challenges,
                &qs,
                &alpha,
            );
            let via_ntt = induce_sumcheck_poly_via_ntt_base(
                log_msg_cols,
                log_inv_rate,
                &rows,
                &v_challenges,
                &qs,
                &alpha,
            );
            assert_eq!(dense.1, via_ntt.1, "enforced_sum mismatch");
            assert_eq!(dense.0, via_ntt.0, "basis_poly mismatch");
        }
    }

    /// The scalar and parallel ext transforms agree (parallel path is only
    /// taken for larger inputs; force both on the same data).
    #[test]
    fn ext_ntt_scalar_matches_parallel() {
        let mut s = 6u64;
        let log_d = 13;
        let lanes = 2;
        let ntt = AdditiveNttF64::standard(log_d);
        let n = (1usize << log_d) * lanes;
        let orig: Vec<F128T> = (0..n).map(|_| rand_ext(&mut s)).collect();
        let mut a = orig.clone();
        let mut b = orig;
        forward_transform_interleaved_ext_scalar_from_layer(&ntt, &mut a, lanes, 1);
        forward_transform_interleaved_ext_parallel_from_layer(&ntt, &mut b, lanes, 1);
        assert_eq!(a, b);
    }
}
