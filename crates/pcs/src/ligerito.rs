// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Ligerito with `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` and
//! `E = K[y]/(y^3+y+1)`.
//!
//! The committed message is a
//! vector of [`F64`] values; every verifier challenge, sumcheck message, basis
//! poly, and post-fold witness is [`F192`]-valued.
//!
//! Type map relative to the original:
//! - committed message / L0 codeword / L0 opened rows: `F64` (8 bytes)
//! - challenges, sumcheck messages, folded witnesses, deeper-level codewords
//!   and opened rows, `b_initial`, betas, alphas, `yr`: `F192` (24 bytes)
//! - the RS-encoding evaluation domain and all LCH twiddles stay in K, so the
//!   deeper-level (E-valued) encodes use K-twiddles via the mixed product
//!   [`F192::mul_base`] (3 PMULL) instead of a full E multiplication.
//!
//! Deliberate divergences from the original (each noted inline too):
//! - Buffers use plain `Vec` allocation where the original recycles through
//!   `crate::scratch` (no F64/F192 pool exists yet).
//! - The prover/commit timing instrumentation answers to `LIGERITO_TRACE`
//!   (instead of the original's `LIG_PROVE_TRACE` / `FLOCK_COMMIT_TIMING`).
//!
//! Basis induction mirrors the original's two strategies: the dense
//! per-query LCH expansion and the sparse transposed-NTT fast path
//! (`induce_sumcheck_poly_via_ntt_base`), with the SAME auto-dispatch size
//! heuristic at L0 (deeper levels stay dense, exactly like the original).
//!
//! Soundness note: [`LigeritoSecurityConfig`] analyzes the actual challenge
//! field size `q = 2^192`; the committed alphabet remains `K = GF(2^64)`.

use crate::merkle::{self, Hash};
use crate::ntt::AdditiveNttF64;
use fiat_shamir::sponge::Sponge;
use primitives::{
    field::{F64, F192, F192BaseUnreduced, F192Unreduced},
    multilinear::eq_eval,
    pretty_integer,
};
use serde::{Deserialize, Serialize};
use zk_alloc::ArenaVec;

pub use super::ligerito_config::{
    FinalBlockConfig, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0, LevelShapes, LigeritoLevelConfig, LigeritoSecurityConfig,
    MAX_LOG_INV_RATE, MIN_LOG_INV_RATE, ProverConfig, QUERY_GRINDING_BITS, RESIDUAL_MAX_LOG,
    RS_DOMAIN_INITIAL_REDUCTION_FACTOR, SECURITY_BITS, SUBSEQUENT_FOLDING_FACTOR, VerifierConfig,
    validate_log_inv_rate,
};
#[cfg(test)]
pub use super::ligerito_config::{default_config, default_verifier_config, udr_queries};
// Transitional: `rec_aggregation` still imports `pcs::ligerito::log2_ceil`.
// Drop this alias once it moves to `primitives::log2_ceil_usize`.
pub use primitives::log2_ceil_usize as log2_ceil;

pub use crate::ligerito_induce::*;
use crate::ligerito_ntt_ext::*;

/// Bind a Merkle root into the transcript as two `F192` scalars rather than
/// as a byte string. Binds the root before any challenge exactly as `absorb_bytes`
/// would; keeping the scalar form matches the recursion guest's replay.
fn observe_root(sponge: &mut Sponge, root: &crate::merkle::Hash) {
    for s in crate::merkle::hash_to_scalars(root) {
        sponge.observe(s);
    }
}

// ===================================================================
// Multilinear helpers over E
// ===================================================================

/// Build the eq-MLE table at `point` in E^d, LSB-first: mirror of
/// `lincheck::build_eq_table` with F192 arithmetic.
pub fn build_eq_table_ext(point: &[F192]) -> Vec<F192> {
    let d = point.len();
    let mut out: Vec<F192> = Vec::with_capacity(1usize << d);
    out.push(F192::ONE);
    for j in 0..d {
        let r_j = point[j];
        let len = 1usize << j;
        out.resize(2 * len, F192::ZERO);
        for i in 0..len {
            let v = out[i];
            let high = v * r_j;
            out[i + len] = high;
            out[i] = v + high;
        }
    }
    out
}

/// Evaluate an E-valued multilinear table at an E-valued point, LSB-first.
fn mle_eval_ext(table: &[F192], point: &[F192]) -> F192 {
    assert_eq!(table.len(), 1usize << point.len());
    let mut folded = table.to_vec();
    for &challenge in point {
        let half = folded.len() / 2;
        for row in 0..half {
            let lo = folded[2 * row];
            let hi = folded[2 * row + 1];
            folded[row] = lo + challenge * (lo + hi);
        }
        folded.truncate(half);
    }
    folded[0]
}

/// Parallel mirror of [`build_eq_table_ext`]: identical LSB-first doubling
/// recurrence, byte-identical output, with each level's independent
/// iterations fanned out across the pool once the level is large enough
/// to amortize dispatch. Structure copied from the extension-field layer's
/// `ring_switch::build_eq_parallel`.
pub(crate) fn build_eq_table_ext_parallel(point: &[F192]) -> ArenaVec<F192> {
    let mut out = zk_alloc::alloc_uninit(1usize << point.len());
    build_eq_table_ext_seeded(point, F192::ONE, &mut out);
    // SAFETY: the doubling recurrence initializes every table entry.
    unsafe { zk_alloc::assume_init(out) }
}

trait EqTableSlot {
    fn put(&mut self, value: F192);
    unsafe fn get(&self) -> F192;
}

impl EqTableSlot for F192 {
    #[inline(always)]
    fn put(&mut self, value: F192) {
        *self = value;
    }

    #[inline(always)]
    unsafe fn get(&self) -> F192 {
        *self
    }
}

impl EqTableSlot for std::mem::MaybeUninit<F192> {
    #[inline(always)]
    fn put(&mut self, value: F192) {
        self.write(value);
    }

    #[inline(always)]
    unsafe fn get(&self) -> F192 {
        // SAFETY: the doubling recurrence reads only the prefix initialized by
        // earlier levels.
        unsafe { self.assume_init_read() }
    }
}

pub(crate) fn build_eq_table_ext_seeded_uninit(point: &[F192], seed: F192, out: &mut [std::mem::MaybeUninit<F192>]) {
    build_eq_table_ext_seeded(point, seed, out);
}

/// In-place seeded core of [`build_eq_table_ext_parallel`]: fills
/// `out[..2^point.len()]` with `seed * eq(point, .)`.
///
/// Seeding folds a batching scalar into the table for free: every entry is
/// `seed` times a product of point factors, and field multiplication is
/// exact and associative, so the result equals the post-multiplied table
/// byte for byte while skipping one full multiply pass. `out` must have
/// length exactly `2^point.len()`; every slot is written before any is read, so
/// a reused scratch buffer is fine.
fn build_eq_table_ext_seeded<S: EqTableSlot + Send>(point: &[F192], seed: F192, out: &mut [S]) {
    let n = point.len();
    assert_eq!(out.len(), 1usize << n, "out must have length 2^point.len()");
    out[0].put(seed);
    // Threshold below which dispatch overhead beats the parallel work
    // (same floor as the extension-field layer's `build_eq_parallel`).
    const PAR_THRESHOLD: usize = 1 << 12;
    for j in 0..n {
        let r_j = point[j];
        let half = 1usize << j;
        let (lo, hi_rest) = out.split_at_mut(half);
        let hi = &mut hi_rest[..half];
        if half < PAR_THRESHOLD {
            for (lo_x, hi_x) in lo.iter_mut().zip(hi.iter_mut()) {
                // SAFETY: `lo` was initialized before this level starts.
                let v = unsafe { lo_x.get() };
                let high = v * r_j;
                hi_x.put(high);
                lo_x.put(v + high);
            }
        } else {
            let chunk = parallel::recommended_chunk_size(half);
            parallel::chunks_mut2(lo, hi, chunk, |_, lo_c, hi_c| {
                for (lo_x, hi_x) in lo_c.iter_mut().zip(hi_c.iter_mut()) {
                    // SAFETY: `lo` was initialized before this level starts.
                    let v = unsafe { lo_x.get() };
                    let high = v * r_j;
                    hi_x.put(high);
                    lo_x.put(v + high);
                }
            });
        }
    }
}

/// Partially evaluate the multilinear extension of `evals` at the first
/// `rs.len()` (LSB) variables. Mirror of `ligerito::partial_eval_lsb`.
#[cfg(test)]
pub(crate) fn partial_eval_lsb_ext(evals: &[F192], rs: &[F192]) -> Vec<F192> {
    let mut cur = evals.to_vec();
    for &r in rs {
        let one_plus_r = F192::ONE + r;
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
pub fn inner_product_base_ext(witness: &[F64], b: &[F192]) -> F192 {
    assert_eq!(witness.len(), b.len());
    const PAR_THRESHOLD: usize = 4096;
    if witness.len() < PAR_THRESHOLD {
        return witness
            .iter()
            .zip(b.iter())
            .map(|(&w, &e)| e.mul_base(w))
            .fold(F192::ZERO, |a, v| a + v);
    }
    parallel::map_reduce(
        witness.len(),
        || F192::ZERO,
        |i| b[i].mul_base(witness[i]),
        |a, v| a + v,
    )
}

#[inline]
pub(crate) fn log2_pow2(n: usize) -> usize {
    assert!(n.is_power_of_two() && n > 0, "length must be a positive power of 2");
    n.trailing_zeros() as usize
}

// ===================================================================
// Config reuse
// ===================================================================

/// Derive `(ProverConfig, VerifierConfig)` for a K-witness of `2^log_n` F64
/// elements, using the production 128-bit Johnson/OOD profile at
/// `m = log_n + LOG_PACKING`.
pub fn configs_for(log_n: usize) -> Result<(ProverConfig, VerifierConfig), String> {
    configs_for_rate(log_n, crate::ligerito::LOG_INV_RATE_0)
}

/// As [`configs_for`], with an explicit L0 inverse-rate logarithm.
pub fn configs_for_rate(log_n: usize, log_inv_rate: usize) -> Result<(ProverConfig, VerifierConfig), String> {
    let sec = LigeritoSecurityConfig::derive_config_with_log_inv_rate(log_n + crate::LOG_PACKING, log_inv_rate)?;
    sec.to_prover_verifier_configs()
}

// ===================================================================
// Commit: F64 message -> interleaved RS codeword -> Merkle root
// ===================================================================

/// Public commitment for an `F64` message: the L0 Merkle root.
#[derive(Clone, Debug)]
pub struct Commitment {
    pub root: Hash,
}

/// Prover-side state retained after commit for the opening phase. The message
/// itself is not stored; the caller retains it for opening.
pub struct ProverData {
    pub codeword: ArenaVec<F64>,
    pub merkle_tree: ArenaVec<Hash>,
}

/// Fill `codeword` with `2^r` replicas of `msg`: the exact state after the
/// first `r` forward-NTT layers on the zero-padded coefficient vector
/// `[msg, 0, ..., 0]`. Pair with `forward_transform_*_from_layer(.., r)`.
fn replicate_message_fill_uninit<T: Copy + Send + Sync>(codeword: &mut [std::mem::MaybeUninit<T>], msg: &[T]) {
    let msg_len = msg.len();
    debug_assert!(codeword.len().is_multiple_of(msg_len));
    const COPY_CHUNK: usize = 1 << 16;
    let copy = |dst: &mut [std::mem::MaybeUninit<T>], src: &[T]| {
        // SAFETY: source and destination are disjoint, have the same length,
        // and each destination slot is written exactly once.
        unsafe { std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast(), dst.len()) };
    };
    if msg_len >= COPY_CHUNK {
        parallel::chunks_mut(codeword, COPY_CHUNK, |i, dst| {
            let src_off = (i * COPY_CHUNK) % msg_len;
            copy(dst, &msg[src_off..src_off + dst.len()]);
        });
    } else {
        for replica in codeword.chunks_mut(msg_len) {
            copy(replica, msg);
        }
    }
}

/// Commit to an `F64` message: replicate it `2^log_inv_rate` times, run the interleaved additive
/// NTT over F_{2^64} from layer `log_inv_rate`, then Merkle-commit one leaf
/// per codeword position (= `2^log_batch_size` F64 = `2^log_batch_size * 8`
/// bytes per leaf).
///
/// `message.len()` must be a power of two `>= 2^log_batch_size`.
pub fn commit(message: &[F64], log_batch_size: usize, log_inv_rate: usize) -> (Commitment, ProverData) {
    let log_msg_len = log2_pow2(message.len());
    assert!(log_msg_len >= log_batch_size, "message too small for log_batch_size");
    assert!(log_inv_rate >= 1, "log_inv_rate must be >= 1 for a non-trivial RS code");
    let log_dim = log_msg_len - log_batch_size;
    let k_code = log_dim + log_inv_rate;
    let num_ntts = 1usize << log_batch_size;
    let n_positions = 1usize << k_code;
    let codeword_len = n_positions * num_ntts;

    let mut codeword = zk_alloc::alloc_uninit(codeword_len);
    replicate_message_fill_uninit(&mut codeword, message);
    // SAFETY: the replicate fill initializes every codeword element.
    let mut codeword = unsafe { zk_alloc::assume_init(codeword) };

    // Optional phase timing (LIGERITO_TRACE): one env lookup per commit, no
    // work when unset.
    let trace = std::env::var_os("LIGERITO_TRACE").is_some();
    let t_ntt = std::time::Instant::now();
    tracing::info_span!("NTT", kind = "base encode", log_domain = k_code, lanes = num_ntts).in_scope(|| {
        let ntt = AdditiveNttF64::standard(k_code);
        ntt.forward_transform_interleaved_from_layer(&mut codeword, num_ntts, log_inv_rate);
    });
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
        let k_code = pretty_integer(k_code);
        let num_ntts = pretty_integer(num_ntts);
        eprintln!(
            "[lig-commit] k_code={k_code} lanes={num_ntts}: ntt = {:.4} s, merkle = {:.4} s",
            ntt_elapsed.as_secs_f64(),
            t_merkle.elapsed().as_secs_f64(),
        );
    }

    (Commitment { root }, ProverData { codeword, merkle_tree })
}

/// Codeword + Merkle tree for one deeper Ligerito commitment level.
/// `mat[pos * num_interleaved + lane]`; each row (one `pos` across all lanes)
/// is one Merkle leaf of `num_interleaved * 16` bytes.
pub(crate) struct LigeroWitness {
    pub mat: ArenaVec<F192>,
    pub tree: ArenaVec<Hash>,
    pub block_len: usize,
    pub num_interleaved: usize,
}

impl LigeroWitness {
    #[inline]
    pub fn row(&self, pos: usize) -> &[F192] {
        let start = pos * self.num_interleaved;
        &self.mat[start..start + self.num_interleaved]
    }

    #[inline]
    pub fn root(&self) -> Hash {
        self.tree[self.tree.len() - 1]
    }
}

/// Commit an extension-field polynomial at a recursive level: replicate the
/// LSB-lane-layout message into all `2^log_inv_rate` sub-blocks, RS-encode
/// each lane with the K-twiddle mixed-product NTT, and Merkle over rows.
pub(crate) fn ligero_commit_ext(
    poly: &[F192],
    log_msg_cols: usize,
    log_num_interleaved: usize,
    log_inv_rate: usize,
    ntt: &AdditiveNttF64,
) -> LigeroWitness {
    let msg_cols = 1usize << log_msg_cols;
    let num_interleaved = 1usize << log_num_interleaved;
    let block_len = msg_cols << log_inv_rate;
    let log_block_len = log_msg_cols + log_inv_rate;
    assert_eq!(poly.len(), num_interleaved * msg_cols);
    assert!(log_block_len <= ntt.log_domain_size());

    let codeword_len = block_len * num_interleaved;
    let mut mat = zk_alloc::alloc_uninit(codeword_len);
    replicate_message_fill_uninit(&mut mat, poly);
    // SAFETY: the replicate fill initializes every matrix element.
    let mut mat = unsafe { zk_alloc::assume_init(mat) };

    // Optional per-level NTT/Merkle split (LIGERITO_TRACE): one env lookup per
    // commit level, no work when unset.
    let trace = std::env::var_os("LIGERITO_TRACE").is_some();
    let t_ntt = std::time::Instant::now();
    tracing::info_span!(
        "NTT",
        kind = "extension encode",
        log_domain = log_block_len,
        lanes = num_interleaved
    )
    .in_scope(|| forward_transform_interleaved_ext_from_layer(ntt, &mut mat, num_interleaved, log_inv_rate));
    let ntt_elapsed = t_ntt.elapsed();
    let t_merkle = std::time::Instant::now();

    // Merkle over rows, zero-copy.
    // SAFETY: F192 is repr(C) with three u64 limbs (24 bytes, no padding);
    // a `[F192]` slice is its contiguous byte image. The cast covers exactly
    // `mat.len() * size_of::<F192>()` initialized
    // bytes.
    let leaf_size_bytes = num_interleaved * core::mem::size_of::<F192>();
    let data_bytes: &[u8] =
        unsafe { core::slice::from_raw_parts(mat.as_ptr() as *const u8, mat.len() * core::mem::size_of::<F192>()) };
    debug_assert_eq!(data_bytes.len(), block_len * leaf_size_bytes);
    let tree = merkle::merkle_tree(data_bytes, block_len);
    if trace {
        let log_block_len = pretty_integer(log_block_len);
        let num_interleaved = pretty_integer(num_interleaved);
        eprintln!(
            "[lig] recursive_commit(log_block={log_block_len}, lanes={num_interleaved}): \
             ntt = {:.4} s, merkle = {:.4} s",
            ntt_elapsed.as_secs_f64(),
            t_merkle.elapsed().as_secs_f64(),
        );
    }

    LigeroWitness {
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
pub struct SumcheckMessage {
    pub u_0: F192,
    pub u_2: F192,
}

/// Round-quadratic in coefficient form `c + b X + a X^2` (verifier side).
#[derive(Clone, Copy, Debug)]
struct RoundQuad {
    c: F192, // u_0
    b: F192, // u_1 (X coeff), derived from T_r and u_2
    a: F192, // u_2 (X^2 coeff)
}

impl RoundQuad {
    #[inline]
    fn from_msg(msg: SumcheckMessage, t_r: F192) -> Self {
        Self {
            c: msg.u_0,
            b: t_r + msg.u_2,
            a: msg.u_2,
        }
    }
    #[inline]
    fn eval(&self, r: F192) -> F192 {
        (self.a * r + self.b) * r + self.c
    }
    #[inline]
    fn fold(p1: &Self, p2: &Self, alpha: F192) -> Self {
        Self {
            c: p1.c + alpha * p2.c,
            b: p1.b + alpha * p2.b,
            a: p1.a + alpha * p2.a,
        }
    }
}

/// Sumcheck witness element: `F64` before the first fold (each product against
/// the E basis is a mixed `mul_base`, 2 PMULL), `F192` after it (full E
/// products, 3 PMULL). The associated accumulator is the matching
/// deferred-reduction type.
trait RoundWitness: Copy + Sync + std::ops::Add<Output = Self> {
    type Acc: Copy + Send + core::ops::BitXorAssign;
    const ZERO_ACC: Self::Acc;
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc;
    fn reduce(acc: Self::Acc) -> F192;
    /// Characteristic-two interpolation `x0·(1+r) + x1·r = x0 + r·(x0+x1)`,
    /// lifting the witness into E. One product rather than two, bit-identical
    /// to the two-product form and still just one reduction.
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192;
}

impl RoundWitness for F64 {
    type Acc = F192BaseUnreduced;
    const ZERO_ACC: Self::Acc = F192BaseUnreduced::ZERO;
    #[inline]
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc {
        b.mul_base_unreduced(self)
    }
    #[inline]
    fn reduce(acc: Self::Acc) -> F192 {
        acc.reduce()
    }
    #[inline]
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192 {
        F192::from(x0) + r.mul_base(x0 + x1)
    }
}

impl RoundWitness for F192 {
    type Acc = F192Unreduced;
    const ZERO_ACC: Self::Acc = F192Unreduced::ZERO;
    #[inline]
    fn mul_basis_unreduced(self, b: F192) -> Self::Acc {
        self.mul_unreduced(b)
    }
    #[inline]
    fn reduce(acc: Self::Acc) -> F192 {
        acc.reduce()
    }
    #[inline]
    fn fold_pair(x0: Self, x1: Self, r: F192) -> F192 {
        x0 + r * (x0 + x1)
    }
}

/// Round message over a witness `f` and an E basis `b`. Mirror of
/// `ligerito::round_msg_lsb`.
///
/// Deferred reduction: XOR-accumulate the raw lane products (no reduction tail
/// per term) and reduce once per accumulator. Reduction commutes with XOR, so
/// the message is bit-identical to reducing every term.
fn round_msg_lsb<T: RoundWitness>(f: &[T], b: &[F192]) -> SumcheckMessage {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    const PAR_THRESHOLD: usize = 4096;
    let half = n / 2;
    let term = |j: usize| -> (T::Acc, T::Acc) {
        let (f0, f1) = (f[2 * j], f[2 * j + 1]);
        let (b0, b1) = (b[2 * j], b[2 * j + 1]);
        (f0.mul_basis_unreduced(b0), (f0 + f1).mul_basis_unreduced(b0 + b1))
    };
    let (u_0, u_2) = if half < PAR_THRESHOLD {
        let mut u_0 = T::ZERO_ACC;
        let mut u_2 = T::ZERO_ACC;
        for j in 0..half {
            let (t0, t2) = term(j);
            u_0 ^= t0;
            u_2 ^= t2;
        }
        (u_0, u_2)
    } else {
        parallel::map_reduce(
            half,
            || (T::ZERO_ACC, T::ZERO_ACC),
            term,
            // Unreduced accumulators combine by XOR just as they do within a
            // worker, and `reduce` is linear, so one reduction at the very end
            // matches the sequential path above exactly.
            |(mut a0, mut a2), (c0, c2)| {
                a0 ^= c0;
                a2 ^= c2;
                (a0, a2)
            },
        )
    };
    SumcheckMessage {
        u_0: T::reduce(u_0),
        u_2: T::reduce(u_2),
    }
}

/// Build the round message and the full inner product in one pass. For an OOD
/// basis `b = eq(z, ·)`, the inner product is the claimed MLE evaluation.
fn round_msg_and_eval_lsb_ext(f: &[F192], b: &[F192]) -> (SumcheckMessage, F192) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);

    let term = |j: usize| {
        let f0 = f[2 * j];
        let f1 = f[2 * j + 1];
        let b0 = b[2 * j];
        let b1 = b[2 * j + 1];
        let e0 = f0 * b0;
        (e0, (f0 + f1) * (b0 + b1), e0 + f1 * b1)
    };
    const PAR_THRESHOLD: usize = 4096;
    let half = n / 2;
    let (u_0, u_2, y) = if half < PAR_THRESHOLD {
        (0..half)
            .map(term)
            .fold((F192::ZERO, F192::ZERO, F192::ZERO), |(a0, a2, ay), (b0, b2, by)| {
                (a0 + b0, a2 + b2, ay + by)
            })
    } else {
        parallel::map_reduce(
            half,
            || (F192::ZERO, F192::ZERO, F192::ZERO),
            term,
            |(a0, a2, ay), (b0, b2, by)| (a0 + b0, a2 + b2, ay + by),
        )
    };
    (SumcheckMessage { u_0, u_2 }, y)
}

/// Output buffer for an initial-sumcheck fold: ~100 MB of `F192` per round, all
/// of it dead by the end of the proof. A slab bump costs a pointer add and
/// reuses pages the previous proof already faulted in, so there is no
/// target-specific pooling decision left to make.
///
/// # Safety
/// Every element must be written before it is read, which every fold kernel
/// below does: one output slot per input pair.
#[inline]
unsafe fn fold_out_buf(n: usize) -> ArenaVec<F192> {
    // SAFETY: forwarded to the caller's obligation, documented above.
    unsafe { ArenaVec::uninitialized(n) }
}

/// Unreduced `(u_0, u_2)` over the already-folded E buffers, pair by pair. A
/// trailing odd element contributes nothing, exactly as in the pre-fold
/// message: at the last round `half = 1` and the message is zero.
#[inline]
fn fold_msg_terms(nf: &[F192], nb: &[F192]) -> (F192Unreduced, F192Unreduced) {
    let mut u_0 = F192Unreduced::ZERO;
    let mut u_2 = F192Unreduced::ZERO;
    let mut k = 0;
    while k + 1 < nf.len() {
        let f0 = nf[k];
        let f1 = nf[k + 1];
        let b0 = nb[k];
        let b1 = nb[k + 1];
        u_0 ^= f0.mul_unreduced(b0);
        u_2 ^= (f0 + f1).mul_unreduced(b0 + b1);
        k += 2;
    }
    (u_0, u_2)
}

/// Fused fold + next-round message: the witness folds into E, the basis folds
/// in E, and the next-round message is built over the freshly folded E values
/// in the same pass. Mirror of `ligerito::fold_and_msg_lsb`.
fn fold_and_msg_lsb<T: RoundWitness>(
    f: &[T],
    b: &[F192],
    r: F192,
) -> (ArenaVec<F192>, ArenaVec<F192>, SumcheckMessage) {
    let n = f.len();
    debug_assert!(n.is_power_of_two() && n >= 2);
    debug_assert_eq!(b.len(), n);
    let half = n / 2;

    let fold_f = |j: usize| -> F192 { T::fold_pair(f[2 * j], f[2 * j + 1], r) };
    let fold_b = |j: usize| -> F192 { F192::fold_pair(b[2 * j], b[2 * j + 1], r) };
    const PAR_THRESHOLD: usize = 4096;
    if half < PAR_THRESHOLD {
        let mut nf = ArenaVec::with_capacity(half);
        let mut nb = ArenaVec::with_capacity(half);
        for j in 0..half {
            nf.push(fold_f(j));
            nb.push(fold_b(j));
        }
        let (u_0, u_2) = fold_msg_terms(&nf, &nb);
        return (
            nf,
            nb,
            SumcheckMessage {
                u_0: u_0.reduce(),
                u_2: u_2.reduce(),
            },
        );
    }

    // Parallel path: `half` is a power of two >= PAR_THRESHOLD and CHUNK is a
    // power of two, so every chunk has even length and starts at an even
    // global index (message pairs never straddle a chunk boundary).
    const CHUNK: usize = 2048;
    // SAFETY (x2): every slot of `nf`/`nb` is written by the chunked loop below
    // (one output per input pair) before any is read.
    let mut nf = unsafe { fold_out_buf(half) };
    let mut nb = unsafe { fold_out_buf(half) };
    // The fold writes and the message accumulate share one pass per chunk, so
    // the freshly folded values are still in L1 when they are multiplied.
    let nf_base = parallel::SendPtr(nf.as_mut_ptr());
    let nb_base = parallel::SendPtr(nb.as_mut_ptr());
    let (u_0, u_2) = parallel::map_reduce(
        half.div_ceil(CHUNK),
        || (F192Unreduced::ZERO, F192Unreduced::ZERO),
        |ci| {
            let base = ci * CHUNK;
            let len = CHUNK.min(half - base);
            // SAFETY: distinct `ci` own disjoint in-bounds `CHUNK`-windows of
            // `nf`/`nb`, and both buffers stay borrowed for the whole dispatch.
            let fc = unsafe { nf_base.slice(base, len) };
            let bc = unsafe { nb_base.slice(base, len) };
            for t in 0..len {
                let j = base + t;
                fc[t] = fold_f(j);
                bc[t] = fold_b(j);
            }
            fold_msg_terms(fc, bc)
        },
        |(mut a0, mut a2), (c0, c2)| {
            a0 ^= c0;
            a2 ^= c2;
            (a0, a2)
        },
    );
    (
        nf,
        nb,
        SumcheckMessage {
            u_0: u_0.reduce(),
            u_2: u_2.reduce(),
        },
    )
}

/// Two-phase witness: the committed K-message (borrowed from the caller, it
/// is only read until the first fold) before the first fold, an owned
/// E-vector afterwards.
enum Witness<'a> {
    Base(&'a [F64]),
    Ext(ArenaVec<F192>),
}

/// Mirror of `ligerito::SumcheckProver` with the two-phase witness.
struct SumcheckProver<'a> {
    f: Witness<'a>,
    /// Single combined basis poly: after every `glue(beta)` the introduced
    /// basis is folded in as `combined_basis += beta * b_new`.
    combined_basis: ArenaVec<F192>,
    t_r: F192,
    transcript: Vec<SumcheckMessage>,
    round: usize,
    pending_glue: Option<(ArenaVec<F192>, F192)>,
}

impl<'a> SumcheckProver<'a> {
    fn new(f: &'a [F64], b1: ArenaVec<F192>, h1: F192) -> (Self, SumcheckMessage) {
        let _span = tracing::info_span!("Sumcheck round", round = 0, log_size = f.len().trailing_zeros()).entered();
        assert_eq!(f.len(), b1.len());
        let msg = round_msg_lsb(f, &b1);
        let mut inst = Self {
            f: Witness::Base(f),
            combined_basis: b1,
            t_r: h1,
            transcript: Vec::new(),
            round: 0,
            pending_glue: None,
        };
        inst.transcript.push(msg);
        (inst, msg)
    }

    fn fold(&mut self, r: F192) -> SumcheckMessage {
        self.round += 1;
        let log_size = match &self.f {
            Witness::Base(f) => f.len().trailing_zeros(),
            Witness::Ext(f) => f.len().trailing_zeros(),
        };
        let _span = tracing::info_span!("Sumcheck round", round = self.round, log_size).entered();
        let (nf, nb, msg) = match &self.f {
            Witness::Base(f) => fold_and_msg_lsb(f, &self.combined_basis, r),
            Witness::Ext(f) => fold_and_msg_lsb(f, &self.combined_basis, r),
        };
        // Swap the freshly folded buffers in and drop the consumed ones. Their
        // slab space is not reclaimed until the phase ends, which is exactly what
        // makes the next round's `fold_out_buf` a bump instead of a fresh mapping.
        drop(std::mem::replace(&mut self.f, Witness::Ext(nf)));
        drop(std::mem::replace(&mut self.combined_basis, nb));
        self.transcript.push(msg);
        msg
    }

    /// Introduce a fresh basis poly with claimed sum `h_new`; sends the
    /// (u_0, u_2) for `Σ_x f(x) · b_new(x)` at the current dim.
    fn introduce_new(&mut self, b_new: ArenaVec<F192>, h_new: F192) -> SumcheckMessage {
        let msg = match &self.f {
            Witness::Base(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb(f, &b_new)
            }
            Witness::Ext(f) => {
                assert_eq!(b_new.len(), f.len());
                round_msg_lsb(f, &b_new)
            }
        };
        self.transcript.push(msg);
        self.pending_glue = Some((b_new, h_new));
        msg
    }

    /// Introduce `b_new` and compute its claimed inner product in the same
    /// pass as the round message. OOD claims only occur after the first fold,
    /// when the witness has already been lifted from K to E.
    fn introduce_new_with_eval(&mut self, b_new: ArenaVec<F192>) -> (SumcheckMessage, F192) {
        let f = match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) => panic!("OOD claim introduced before the first fold"),
        };
        assert_eq!(b_new.len(), f.len());
        let (msg, h_new) = round_msg_and_eval_lsb_ext(f, &b_new);
        self.transcript.push(msg);
        self.pending_glue = Some((b_new, h_new));
        (msg, h_new)
    }

    /// Combine the introduced basis into `combined_basis` with separation
    /// `alpha`: `combined_basis[j] += alpha * b_new[j]`, `T_r += alpha * h_new`.
    fn glue(&mut self, alpha: F192) {
        let (b_new, h_new) = self.pending_glue.take().expect("glue without introduce_new");
        assert_eq!(b_new.len(), self.combined_basis.len());
        const PAR_THRESHOLD: usize = 4096;
        if self.combined_basis.len() < PAR_THRESHOLD {
            for (acc, &v) in self.combined_basis.iter_mut().zip(b_new.iter()) {
                *acc += alpha * v;
            }
        } else {
            let chunk = parallel::recommended_chunk_size(self.combined_basis.len());
            parallel::chunks_mut_zip(&mut self.combined_basis, &b_new, chunk, |_, accs, news| {
                for (acc, &v) in accs.iter_mut().zip(news) {
                    *acc += alpha * v;
                }
            });
        }
        self.t_r += alpha * h_new;
    }

    /// The folded witness (post-first-fold: always E). Panics if called
    /// before the first fold (the base phase never reaches a commit).
    fn f_ext(&self) -> &[F192] {
        match &self.f {
            Witness::Ext(f) => f,
            Witness::Base(_) => panic!("witness still in base phase (no fold yet)"),
        }
    }

    fn transcript(&self) -> &[SumcheckMessage] {
        &self.transcript
    }
}

/// L0 opened rows: F64 (the commitment field).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InitialProof {
    /// One row per query (`num_interleaved` F64 entries), sorted by query
    /// position to align with the Merkle multi-proof.
    pub opened_rows: Vec<Vec<F64>>,
    pub merkle_proof: Vec<Hash>,
}

/// Deeper-level opened rows: E-valued.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveProof {
    pub opened_rows: Vec<Vec<F192>>,
    pub merkle_proof: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalProof {
    /// Remaining polynomial sent in clear at the last recursive step.
    pub yr: Vec<F192>,
    pub opened_rows: Vec<Vec<F192>>,
    pub merkle_proof: Vec<Hash>,
}

/// The L0 root is the caller's statement, not proof data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LigeritoProof {
    pub initial_proof: InitialProof,
    pub recursive_roots: Vec<Hash>,
    pub recursive_proofs: Vec<RecursiveProof>,
    pub final_proof: FinalProof,
    pub sumcheck_transcript: Vec<SumcheckMessage>,
    /// Per-level query-phase PoW nonces (0 when the level grinds 0 bits).
    pub grinding_nonces: Vec<u64>,
    /// Claimed multilinear OOD evaluations, flattened in transcript order.
    #[serde(default)]
    pub ood_values: Vec<F192>,
    /// Fold-challenge PoW nonces, flattened in transcript order (one per fold
    /// challenge at every level with `fold_grinding_bits > 0`).
    pub fold_grinding_nonces: Vec<u64>,
}

/// Sample `count` query positions in transcript order: no dedup, no sort.
/// `block_len = 2^d`; each squeezed field element yields `⌊192/d⌋` positions as
/// its disjoint d-bit chunks (low bits first). Mirror of
/// `ligerito::sample_queries_ordered` so the K opener uses the exact
/// recursion-friendly scheme the harness/guest re-derive (fixed `192/d` per
/// squeeze, dup-tolerant: soundness matches the deployed PCS with the same
/// `config.queries`). Duplicates are harmless, a repeated position re-opens the
/// same Merkle-authenticated row.
///
/// Also returns the raw squeezed words `v` (native `F192`, one per squeeze):
/// the recursion harness reads all three limbs off them to re-derive positions.
/// There is deliberately no position-only variant, because two copies of this
/// loop would let the prover and the verifier drift apart silently.
fn sample_queries_ordered_with_raw(sponge: &mut Sponge, block_len: usize, count: usize) -> (Vec<usize>, Vec<F192>) {
    let d = block_len.trailing_zeros() as usize;
    let per = 192 / d;
    let mut out = Vec::with_capacity(count);
    let mut raw = Vec::with_capacity(count.div_ceil(per));
    while out.len() < count {
        let v = sponge.sample();
        raw.push(v);
        for j in 0..per.min(count - out.len()) {
            let off = j * d;
            let limbs = [v.c0, v.c1, v.c2];
            let (li, sh) = (off / 64, off % 64);
            let mut chunk = limbs[li] >> sh;
            if sh + d > 64 {
                chunk |= limbs[li + 1] << (64 - sh);
            }
            out.push(chunk as usize & (block_len - 1));
        }
    }
    (out, raw)
}

/// Fan stored sorted-unique rows back to transcript (ordered, dup-possible)
/// order, so the induce math sees `opened_rows[i]` ↔ `queries[i]`. The rows must
/// already be authenticated (via the octopus check) against the level root.
fn fan_rows_to_ordered<T: Clone>(queries: &[usize], rows_sorted: &[Vec<T>]) -> Option<Vec<Vec<T>>> {
    let sorted = sorted_unique_queries(queries);
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

/// Prover side of the OOD claims taken right after a level's root enters the
/// transcript: sample `z`, evaluate the folded witness there, absorb the claim
/// and its intro message, glue with a fresh separation. Mirror of the
/// verifiers' [`replay_ood`], operation for operation.
fn absorb_ood(
    sc: &mut SumcheckProver<'_>,
    sponge: &mut Sponge,
    n_vars: usize,
    count: usize,
    ood_values: &mut Vec<F192>,
) {
    for _ in 0..count {
        let z = sponge.sample_vec(n_vars);
        let (intro, y) = sc.introduce_new_with_eval(build_eq_table_ext_parallel(&z));
        sponge.observe(y);
        ood_values.push(y);
        sponge.observe(intro.u_0);
        sponge.observe(intro.u_2);
        sc.glue(sponge.sample());
    }
}

/// The stored half of one level's opening: the sorted-unique rows plus one
/// octopus over those positions. The verifier re-fans them to transcript order.
fn stored_opening<T: Copy>(
    queries: &[usize],
    row: impl Fn(usize) -> Vec<T>,
    tree: &[Hash],
    block_len: usize,
) -> (Vec<Vec<T>>, Vec<Hash>) {
    let sorted = sorted_unique_queries(queries);
    let rows = sorted.iter().map(|&q| row(q)).collect();
    let multi_proof = merkle::merkle_multi_proof(tree, block_len, &sorted);
    (rows, multi_proof)
}

/// Prove `Σ_x witness(x) · b_initial(x) = target` against the L0 commitment
/// produced by [`commit`] (with `log_batch_size = config.initial_k` and
/// `log_inv_rate = config.log_inv_rates[0]`).
///
/// `witness` is borrowed: it is only READ (round-0 message + the first lane
/// fold, which lifts it into an owned E-vector), so callers with a large
/// committed stack pass the slice directly instead of paying a full copy.
///
/// Transcript order is identical to the original (target, roots, OOD claims,
/// `(u_0, u_2)` stream, tapered fold grinds, query grinds, queries, alphas,
/// betas, and `yr` in the clear at the end).
pub fn recursive_prover_with_basis(
    config: &ProverConfig,
    witness: &[F64],
    b_initial: ArenaVec<F192>,
    target: F192,
    l0_codeword: &[F64],
    l0_tree: &[Hash],
    sponge: &mut Sponge,
) -> LigeritoProof {
    let log_n = witness.len().trailing_zeros() as usize;
    let r = config.level_steps;
    let initial_k = config.initial_k;

    assert_eq!(witness.len(), 1usize << log_n);
    assert_eq!(b_initial.len(), 1usize << log_n);
    assert_eq!(config.level_ks.len(), r);
    assert_eq!(config.log_inv_rates.len(), r + 1);
    assert!(r >= 1);
    assert!(initial_k >= 1);
    assert_eq!(config.ood_samples.first().copied().unwrap_or(0), 0);

    let log_inv_rate_0 = config.log_inv_rates[0];
    let log_msg_cols_0 = log_n - initial_k;
    let block_len_0 = 1usize << (log_msg_cols_0 + log_inv_rate_0);
    let num_interleaved_0 = 1usize << initial_k;
    assert_eq!(l0_codeword.len(), block_len_0 * num_interleaved_0);
    assert_eq!(l0_tree.len(), 2 * block_len_0 - 1);

    // Optional per-phase timing (LIGERITO_TRACE): mirror of the original's
    // LIG_PROVE_TRACE. One env lookup per prove; the Instant reads are
    // negligible and the accumulation/printing is gated on `trace`.
    let trace = std::env::var_os("LIGERITO_TRACE").is_some();
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
    sponge.observe(target);

    // L0 codeword + tree are borrowed (reused from `commit`).
    let initial_root: Hash = l0_tree[l0_tree.len() - 1];
    let l0_row = |q: usize| -> &[F64] {
        let start = q * num_interleaved_0;
        &l0_codeword[start..start + num_interleaved_0]
    };
    observe_root(sponge, &initial_root);

    let mut fold_grinding_nonces: Vec<u64> = Vec::new();
    let mut ood_values: Vec<F192> = Vec::new();
    let fold_bits = |lvl: usize| -> u32 { config.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as u32 };
    let ood_count = |lvl: usize| -> usize { config.ood_samples.get(lvl).copied().unwrap_or(0) };

    let _t = std::time::Instant::now();
    let sumcheck_span = tracing::info_span!("Sumcheck");
    let (mut sc_prover, start_msg) = sumcheck_span.in_scope(|| SumcheckProver::new(witness, b_initial, target));
    sponge.observe(start_msg.u_0);
    sponge.observe(start_msg.u_2);

    let mut r_lane_fold = Vec::with_capacity(initial_k);
    for j in 0..initial_k {
        // Tapered fold-challenge grinding: round j of the lane fold needs
        // (fold_bits - j) bits (worst round j=0 carries the full budget); see
        // the original's App. C.3 `mca-commutes` comment.
        let bits = fold_bits(0).saturating_sub(j as u32);
        if bits > 0 {
            fold_grinding_nonces.push(sponge.grind_pow(bits));
        }
        let r_j = sponge.sample();
        let msg = sumcheck_span.in_scope(|| sc_prover.fold(r_j));
        sponge.observe(msg.u_0);
        sponge.observe(msg.u_2);
        r_lane_fold.push(r_j);
    }
    drop(sumcheck_span);
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
    let wtns_1 = ligero_commit_ext(&f1, log_msg_cols_1, log_num_interleaved_1, log_inv_rate_1, &ntt_1);
    if trace {
        t_commits += _t.elapsed();
    }
    observe_root(sponge, &wtns_1.root());

    // Bind the L1 Johnson list before drawing L0 queries. Each claimed random
    // MLE evaluation is introduced into the running sumcheck.
    absorb_ood(&mut sc_prover, sponge, n1, ood_count(1), &mut ood_values);

    // Query-phase PoW grinding for L0 (0 bits in the production profile; the
    // canonical 0 nonce is still absorbed to keep the transcript in lockstep).
    let pow_nonce_0 = sponge.grind_pow(config.grinding_bits[0] as u32);
    let mut grinding_nonces: Vec<u64> = vec![pow_nonce_0];

    // Open L0; lane-fold weights = r_lane_fold.
    let num_queries_0 = config.queries[0];
    let queries_0 = sample_queries_ordered_with_raw(sponge, block_len_0, num_queries_0).0;
    let alpha_0 = sponge.sample_vec(log2_ceil(num_queries_0));
    let _t = std::time::Instant::now();
    // Ordered (dup-possible) rows for the local induce math ...
    let opened_rows_0: Vec<Vec<F64>> = queries_0.iter().map(|&q| l0_row(q).to_vec()).collect();
    // ... but the stored proof carries the sorted-unique rows + one octopus over
    // the sorted-unique positions (the verifier re-fans them to ordered).
    let (stored_rows_0, merkle_proof_0) = stored_opening(&queries_0, |q| l0_row(q).to_vec(), l0_tree, block_len_0);
    if trace {
        t_opens += _t.elapsed();
    }
    let initial_proof = InitialProof {
        opened_rows: stored_rows_0,
        merkle_proof: merkle_proof_0,
    };

    // Induce basis_0 from the L0 opens. L0 dominates the induce phase, where
    // the sparse-prefix transposed-NTT path wins; the dispatcher auto-selects
    // it (deeper levels stay dense), mirroring the original.
    let sks_vks_n1 = eval_sk_at_vks(n1);
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
    sponge.observe(intro_msg_0.u_0);
    sponge.observe(intro_msg_0.u_2);
    let beta_0 = sponge.sample();
    sc_prover.glue(beta_0);
    if trace {
        t_intro_glue += _t.elapsed();
    }

    // Recursive levels.
    let mut wtns_prev = wtns_1;
    let mut recursive_roots: Vec<Hash> = vec![wtns_prev.root()];
    let mut recursive_proofs: Vec<RecursiveProof> = Vec::new();

    for i in 0..r {
        let k_i = config.level_ks[i];
        let mut level_rs = Vec::with_capacity(k_i);
        let _t = std::time::Instant::now();
        let sumcheck_span = tracing::info_span!("Sumcheck");
        for j in 0..k_i {
            // These folds fold level i+1's commitment; tapered grinding as in
            // the L0 loop.
            let bits = fold_bits(i + 1).saturating_sub(j as u32);
            if bits > 0 {
                fold_grinding_nonces.push(sponge.grind_pow(bits));
            }
            let ri = sponge.sample();
            let msg = sumcheck_span.in_scope(|| sc_prover.fold(ri));
            sponge.observe(msg.u_0);
            sponge.observe(msg.u_2);
            level_rs.push(ri);
        }
        drop(sumcheck_span);
        if trace {
            t_sumcheck_folds += _t.elapsed();
        }

        if i == r - 1 {
            let yr = sc_prover.f_ext().to_vec();
            for v in &yr {
                sponge.observe(*v);
            }
            // PoW grinding for the last level before sampling its queries.
            let nonce_last = sponge.grind_pow(config.grinding_bits[i + 1] as u32);
            grinding_nonces.push(nonce_last);
            let num_queries_last = config.queries[i + 1];
            let queries_last = sample_queries_ordered_with_raw(sponge, wtns_prev.block_len, num_queries_last).0;
            // The final commitment's basis challenge is drawn only after `yr`
            // and its queries are bound, matching the verifier exactly.
            let alpha_last = sponge.sample_vec(log2_ceil(num_queries_last));
            let _t = std::time::Instant::now();
            // Final level: stored (sorted-unique) only, no local induce; the
            // verifier fans these to ordered for its last-level induce.
            let (opened_rows_last, merkle_proof_last) = stored_opening(
                &queries_last,
                |q| wtns_prev.row(q).to_vec(),
                &wtns_prev.tree,
                wtns_prev.block_len,
            );
            // Tie the last commitment into the running claim through the same
            // intro/glue step as every other level, then finish the remaining
            // sumcheck rounds. This closes on one weight evaluation instead of
            // a sweep over the residual cube.
            let rows_last: Vec<Vec<F192>> = queries_last.iter().map(|&q| wtns_prev.row(q).to_vec()).collect();
            let enforced_sum_last = induce_sumcheck_enforced_sum(&rows_last, &level_rs, &queries_last, &alpha_last);
            let n_res = sc_prover.f_ext().len().trailing_zeros() as usize;
            let basis_last = induce_sumcheck_evaluate_at_residual(
                n_res,
                &eval_sk_at_vks(n_res),
                &queries_last,
                &alpha_last,
                &[],
                n_res,
            );
            let intro_msg_last = sc_prover.introduce_new(basis_last, enforced_sum_last);
            sponge.observe(intro_msg_last.u_0);
            sponge.observe(intro_msg_last.u_2);
            sc_prover.glue(sponge.sample());
            for j in 0..n_res {
                let ri = sponge.sample();
                let msg = sc_prover.fold(ri);
                if j + 1 < n_res {
                    sponge.observe(msg.u_0);
                    sponge.observe(msg.u_2);
                }
            }
            let transmitted_sumcheck_len = sc_prover.transcript().len() - usize::from(n_res > 0);
            if trace {
                t_opens += _t.elapsed();
                let total = t_total.elapsed();
                eprintln!("[lig-prove] total = {:.4} s", total.as_secs_f64());
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
            return LigeritoProof {
                initial_proof,
                recursive_roots,
                recursive_proofs,
                final_proof: FinalProof {
                    yr,
                    opened_rows: opened_rows_last,
                    merkle_proof: merkle_proof_last,
                },
                sumcheck_transcript: sc_prover.transcript()[..transmitted_sumcheck_len].to_vec(),
                grinding_nonces,
                ood_values,
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

        absorb_ood(&mut sc_prover, sponge, n_next, ood_count(i + 2), &mut ood_values);

        // PoW grinding for this iteration's query phase.
        let nonce_i = sponge.grind_pow(config.grinding_bits[i + 1] as u32);
        grinding_nonces.push(nonce_i);
        let num_queries_i = config.queries[i + 1];
        let queries_i = sample_queries_ordered_with_raw(sponge, wtns_prev.block_len, num_queries_i).0;
        let alpha_i = sponge.sample_vec(log2_ceil(num_queries_i));
        let _t = std::time::Instant::now();
        // Ordered rows for the local induce; sorted-unique rows + octopus stored.
        let opened_rows_i: Vec<Vec<F192>> = queries_i.iter().map(|&q| wtns_prev.row(q).to_vec()).collect();
        let (stored_rows_i, merkle_proof_i) = stored_opening(
            &queries_i,
            |q| wtns_prev.row(q).to_vec(),
            &wtns_prev.tree,
            wtns_prev.block_len,
        );
        if trace {
            t_opens += _t.elapsed();
        }
        recursive_proofs.push(RecursiveProof {
            opened_rows: stored_rows_i,
            merkle_proof: merkle_proof_i,
        });

        let sks_vks_i = eval_sk_at_vks(n_next);
        let _t = std::time::Instant::now();
        let (basis_i_induced, enforced_sum_i) =
            induce_sumcheck_poly(n_next, &sks_vks_i, &opened_rows_i, &level_rs, &queries_i, &alpha_i);
        if trace {
            t_induce += _t.elapsed();
        }

        let _t = std::time::Instant::now();
        let intro_msg_i = sc_prover.introduce_new(basis_i_induced, enforced_sum_i);
        sponge.observe(intro_msg_i.u_0);
        sponge.observe(intro_msg_i.u_2);
        let beta_i = sponge.sample();
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

/// Hash one opened row as its raw little-endian byte image, the same image the
/// committer fed to `merkle_tree`. `F64` is repr(transparent) over u64 and
/// `F192` is repr(C) over three u64 limbs, so in both cases the row occupies
/// exactly `row.len() * size_of::<T>()` initialized bytes with no padding.
fn hash_row<T: Copy>(row: &[T]) -> Hash {
    // SAFETY: see above; `size_of_val` is `row.len() * size_of::<T>()`, so the
    // cast covers exactly the initialized bytes of `row`.
    let bytes: &[u8] = unsafe { core::slice::from_raw_parts(row.as_ptr() as *const u8, core::mem::size_of_val(row)) };
    merkle::hash_leaf(bytes)
}

/// Leaf hashes for the opened rows, or `None` if any row has the wrong width.
fn leaf_hashes_of<T: Copy>(rows: &[Vec<T>], expected_num_interleaved: usize) -> Option<Vec<Hash>> {
    rows.iter()
        .map(|row| (row.len() == expected_num_interleaved).then(|| hash_row(row)))
        .collect()
}

/// Verify all opened rows of one level against its root via a single
/// multi-proof.
fn verify_level_opens<T: Copy>(
    root: &Hash,
    block_len: usize,
    queries: &[usize],
    opened_rows: &[Vec<T>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> bool {
    if queries.len() != opened_rows.len() {
        return false;
    }
    let Some(leaf_hashes) = leaf_hashes_of(opened_rows, expected_num_interleaved) else {
        return false;
    };
    merkle::verify_merkle_multi_proof(root, block_len, queries, &leaf_hashes, multi_proof)
}

/// Transcript-order queries with duplicates removed, ascending. The initial opening
/// stores one opened row per distinct query position (sorted); the recursion
/// harness expands back to per-query order below.
fn sorted_unique_queries(queries: &[usize]) -> Vec<usize> {
    let mut s = queries.to_vec();
    s.sort_unstable();
    s.dedup();
    s
}

/// Expand one level's stored opening into the flat per-query form the recursion
/// guest re-hashes: one row and one full Merkle path per query, in transcript
/// order (duplicates included). Authenticates nothing itself; the caller
/// re-checks each restored path against the root.
pub fn expand_level_opening<T: Clone + Copy>(
    block_len: usize,
    queries: &[usize],
    rows_sorted: &[Vec<T>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> Option<(Vec<Vec<T>>, Vec<Hash>)> {
    let leaf_hashes = leaf_hashes_of(rows_sorted, expected_num_interleaved)?;
    let flat_paths = merkle::restore_multi_proof(block_len, queries, &leaf_hashes, multi_proof)?;
    Some((fan_rows_to_ordered(queries, rows_sorted)?, flat_paths))
}

/// Level-0 (`F64` rows) instance of [`expand_level_opening`]; the recursion
/// harness calls the two element types by name.
pub fn expand_level_opening_base(
    block_len: usize,
    queries: &[usize],
    rows_sorted: &[Vec<F64>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> Option<(Vec<Vec<F64>>, Vec<Hash>)> {
    expand_level_opening(block_len, queries, rows_sorted, expected_num_interleaved, multi_proof)
}

/// Deeper-level (`F192` rows) instance of [`expand_level_opening`].
pub fn expand_level_opening_ext(
    block_len: usize,
    queries: &[usize],
    rows_sorted: &[Vec<F192>],
    expected_num_interleaved: usize,
    multi_proof: &[Hash],
) -> Option<(Vec<Vec<F192>>, Vec<Hash>)> {
    expand_level_opening(block_len, queries, rows_sorted, expected_num_interleaved, multi_proof)
}

/// The already-committed level whose rows the next query phase opens: its root
/// plus the shape both verifiers re-derive the block length and leaf width from.
struct PrevLevel {
    root: Hash,
    log_num_interleaved: usize,
    log_msg_cols: usize,
    log_inv_rate: usize,
}

impl PrevLevel {
    #[inline]
    fn block_len(&self) -> usize {
        1usize << (self.log_msg_cols + self.log_inv_rate)
    }

    #[inline]
    fn num_interleaved(&self) -> usize {
        1usize << self.log_num_interleaved
    }

    /// Step to the level just committed, which folds `k_next` of the
    /// `n_current` remaining variables. `None` when the announced shape cannot
    /// hold them.
    fn advance(&mut self, root: Hash, k_next: usize, n_current: usize, log_inv_rate: usize) -> Option<()> {
        self.root = root;
        self.log_num_interleaved = k_next;
        self.log_msg_cols = n_current.checked_sub(k_next)?;
        self.log_inv_rate = log_inv_rate;
        Some(())
    }
}

/// Replay one level's fold challenges: the tapered fold-challenge PoW, the
/// challenge itself, then the round message that follows it. Both verifiers
/// call this so the sponge sees exactly the operations the prover performed, in
/// the prover's order. Returns the challenges in order, `None` on any
/// transcript or PoW mismatch.
fn replay_fold_rounds(
    sponge: &mut Sponge,
    proof: &LigeritoProof,
    k: usize,
    level_fold_bits: u32,
    fold_nonce_idx: &mut usize,
    tx_idx: &mut usize,
    t_r: &mut F192,
    running_quad: &mut RoundQuad,
) -> Option<Vec<F192>> {
    let mut rs = Vec::with_capacity(k);
    for j in 0..k {
        let bits = level_fold_bits.saturating_sub(j as u32);
        if bits > 0 {
            let &nonce = proof.fold_grinding_nonces.get(*fold_nonce_idx)?;
            if !sponge.verify_pow(nonce, bits) {
                return None;
            }
            *fold_nonce_idx += 1;
        }
        let ri = sponge.sample();
        rs.push(ri);
        *t_r = running_quad.eval(ri);
        let &msg = proof.sumcheck_transcript.get(*tx_idx)?;
        *tx_idx += 1;
        sponge.observe(msg.u_0);
        sponge.observe(msg.u_2);
        *running_quad = RoundQuad::from_msg(msg, *t_r);
    }
    Some(rs)
}

/// One replayed OOD claim: the point `z` it was taken at and the separation
/// `beta` it was glued with. The caller keeps whichever form it needs for the
/// terminal weight (a dense eq table, or `z` itself).
struct OodReplay {
    z: Vec<F192>,
    beta: F192,
}

/// Replay one OOD claim: draw `z`, read the claimed evaluation off the proof,
/// absorb it and the intro message, then glue with a fresh `beta`. Mirror of
/// the prover's [`absorb_ood`], operation for operation.
fn replay_ood(
    sponge: &mut Sponge,
    proof: &LigeritoProof,
    n_vars: usize,
    ood_idx: &mut usize,
    tx_idx: &mut usize,
    t_r: &mut F192,
    running_quad: &mut RoundQuad,
) -> Option<OodReplay> {
    let z = sponge.sample_vec(n_vars);
    let &y = proof.ood_values.get(*ood_idx)?;
    *ood_idx += 1;
    sponge.observe(y);
    let &intro_msg = proof.sumcheck_transcript.get(*tx_idx)?;
    *tx_idx += 1;
    sponge.observe(intro_msg.u_0);
    sponge.observe(intro_msg.u_2);
    let intro_quad = RoundQuad::from_msg(intro_msg, y);
    let beta = sponge.sample();
    *running_quad = RoundQuad::fold(running_quad, &intro_quad, beta);
    *t_r += beta * y;
    Some(OodReplay { z, beta })
}

/// Dense verifier for [`recursive_prover_with_basis`] (mirror of
/// `ligerito::recursive_verifier_with_basis`): materializes `b_initial` and
/// every induced basis poly, replays the transcript, and checks the residual
/// inner product against the running sum-claim. Production callers should
/// prefer [`recursive_verifier_with_basis_succinct`]; this one exists for
/// correctness testing (dense/succinct agreement) and benchmarking.
#[cfg(test)]
pub fn recursive_verifier_with_basis(
    config: &VerifierConfig,
    proof: &LigeritoProof,
    b_initial: &[F192],
    target: F192,
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
    if config.ood_samples.first().copied().unwrap_or(0) != 0 {
        return false;
    }

    // The L0 root is the caller's statement (not proof data): absorb it in the
    // prover's slot and check L0 opens against it below.
    // (No opener domain-label absorb: the extension-field opener has none and the recursion
    // guest replays a label-free opening transcript; the observed `target` +
    // outer transcript context provide domain separation.)
    sponge.observe(target);
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
    sponge.observe(start_msg.u_0);
    sponge.observe(start_msg.u_2);
    let mut running_quad = RoundQuad::from_msg(start_msg, t_r);

    let fold_bits = |lvl: usize| -> u32 { config.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as u32 };
    let ood_count = |lvl: usize| -> usize { config.ood_samples.get(lvl).copied().unwrap_or(0) };
    let mut fold_nonce_idx = 0usize;
    let mut ood_idx = 0usize;
    let mut ood_bases: Vec<(Vec<F192>, usize, F192)> = Vec::new();

    let Some(r_lane_fold) = replay_fold_rounds(
        sponge,
        proof,
        initial_k,
        fold_bits(0),
        &mut fold_nonce_idx,
        &mut tx_idx,
        &mut t_r,
        &mut running_quad,
    ) else {
        return false;
    };

    // Observe wtns_1 root + open wtns_0.
    if proof.recursive_roots.is_empty() {
        return false;
    }
    let root_1 = proof.recursive_roots[0];
    observe_root(sponge, &root_1);

    for _ in 0..ood_count(1) {
        let Some(ood) = replay_ood(
            sponge,
            proof,
            log_n - initial_k,
            &mut ood_idx,
            &mut tx_idx,
            &mut t_r,
            &mut running_quad,
        ) else {
            return false;
        };
        ood_bases.push((build_eq_table_ext(&ood.z), initial_k, ood.beta));
    }

    // PoW grinding check for L0's query phase (no-op at 0 bits but keeps the
    // FS state in lockstep with the prover).
    let mut nonce_idx = 0usize;
    if nonce_idx >= proof.grinding_nonces.len() {
        return false;
    }
    if !sponge.verify_pow(proof.grinding_nonces[nonce_idx], config.grinding_bits[0] as u32) {
        return false;
    }
    nonce_idx += 1;

    let num_queries_0 = config.queries[0];
    let queries_0 = sample_queries_ordered_with_raw(sponge, block_len_0, num_queries_0).0;
    let alpha_0 = sponge.sample_vec(log2_ceil(num_queries_0));
    let sq_0 = sorted_unique_queries(&queries_0);
    if !verify_level_opens(
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
    let sks_vks_n1 = eval_sk_at_vks(n1);
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
    sponge.observe(intro_msg_0.u_0);
    sponge.observe(intro_msg_0.u_2);
    let intro_quad_0 = RoundQuad::from_msg(intro_msg_0, enforced_sum_0);
    let beta_0 = sponge.sample();
    running_quad = RoundQuad::fold(&running_quad, &intro_quad_0, beta_0);
    t_r += beta_0 * enforced_sum_0;

    // Basis poly tracking for the residual check. b_initial folds at ALL ris;
    // basis_0_induced starts after the lane folds.
    let mut basis_polys: Vec<ArenaVec<F192>> = vec![ArenaVec::from_slice(b_initial), basis_0_induced];
    let mut basis_ris_starts: Vec<usize> = vec![0, initial_k];
    let mut basis_separations: Vec<F192> = vec![beta_0];
    let mut ris: Vec<F192> = r_lane_fold.clone();

    let mut prev = PrevLevel {
        root: root_1,
        log_num_interleaved: config.level_ks[0],
        log_msg_cols: n1 - config.level_ks[0],
        log_inv_rate: config.log_inv_rates[1],
    };
    let mut next_root_idx = 1usize;
    let mut recursive_proof_idx = 0usize;
    let mut n_current = n1;

    // The two indices advance independently of `i` (roots start at 1, recursive
    // proofs at 0), so they are not loop counters clippy can fold into `i`.
    #[allow(clippy::explicit_counter_loop)]
    for i in 0..r {
        let k_i = config.level_ks[i];
        if n_current < k_i {
            return false;
        }
        let Some(level_rs) = replay_fold_rounds(
            sponge,
            proof,
            k_i,
            fold_bits(i + 1),
            &mut fold_nonce_idx,
            &mut tx_idx,
            &mut t_r,
            &mut running_quad,
        ) else {
            return false;
        };
        ris.extend_from_slice(&level_rs);
        n_current -= k_i;

        if i == r - 1 {
            if ood_idx != proof.ood_values.len() || fold_nonce_idx != proof.fold_grinding_nonces.len() {
                return false;
            }
            let yr = &proof.final_proof.yr;
            if yr.len() != 1 << n_current {
                return false;
            }
            for v in yr {
                sponge.observe(*v);
            }
            // PoW grinding check for the last level.
            if nonce_idx >= proof.grinding_nonces.len() {
                return false;
            }
            if !sponge.verify_pow(proof.grinding_nonces[nonce_idx], config.grinding_bits[i + 1] as u32) {
                return false;
            }
            // (last nonce: nonce_idx is not advanced past it)

            let num_queries_last = config.queries[i + 1];
            let queries_last = sample_queries_ordered_with_raw(sponge, prev.block_len(), num_queries_last).0;
            // Final-level basis-induction challenge: sampled AFTER `yr` was
            // observed and the queries are fixed, so a forged `yr` cannot be
            // adapted to it (mirror of the original).
            let alpha_last = sponge.sample_vec(log2_ceil(num_queries_last));
            let sq_last = sorted_unique_queries(&queries_last);
            if !verify_level_opens(
                &prev.root,
                prev.block_len(),
                &sq_last,
                &proof.final_proof.opened_rows,
                prev.num_interleaved(),
                &proof.final_proof.merkle_proof,
            ) {
                return false;
            }
            let ordered_rows_last = match fan_rows_to_ordered(&queries_last, &proof.final_proof.opened_rows) {
                Some(x) => x,
                None => return false,
            };

            // Bind the LAST commitment to `yr`: induce its opened rows into
            // the sumcheck like every non-final level, batched with a fresh
            // `beta_last` (see the original's binding-fix comment).
            let sks_vks_last = eval_sk_at_vks(n_current);
            let (basis_last_induced, enforced_sum_last) = induce_sumcheck_poly(
                n_current,
                &sks_vks_last,
                &ordered_rows_last,
                &level_rs,
                &queries_last,
                &alpha_last,
            );
            let Some(&intro_msg_last) = proof.sumcheck_transcript.get(tx_idx) else {
                return false;
            };
            tx_idx += 1;
            sponge.observe(intro_msg_last.u_0);
            sponge.observe(intro_msg_last.u_2);
            let intro_quad_last = RoundQuad::from_msg(intro_msg_last, enforced_sum_last);
            let beta_last = sponge.sample();
            running_quad = RoundQuad::fold(&running_quad, &intro_quad_last, beta_last);
            t_r += beta_last * enforced_sum_last;
            basis_polys.push(basis_last_induced);
            basis_ris_starts.push(ris.len());
            basis_separations.push(beta_last);

            // Finish the residual sumcheck rounds, then evaluate every dense
            // basis and the transmitted final message at the one terminal point.
            let mut ris_tail = Vec::with_capacity(n_current);
            for j in 0..n_current {
                let ri = sponge.sample();
                t_r = running_quad.eval(ri);
                ris_tail.push(ri);
                if j + 1 < n_current {
                    let Some(&msg) = proof.sumcheck_transcript.get(tx_idx) else {
                        return false;
                    };
                    tx_idx += 1;
                    sponge.observe(msg.u_0);
                    sponge.observe(msg.u_2);
                    running_quad = RoundQuad::from_msg(msg, t_r);
                }
            }
            if tx_idx != proof.sumcheck_transcript.len() {
                return false;
            }
            ris.extend_from_slice(&ris_tail);
            let mut weight = F192::ZERO;
            for (k, basis) in basis_polys.iter().enumerate() {
                let start = basis_ris_starts[k];
                let at = partial_eval_lsb_ext(basis, &ris[start..]);
                if at.len() != 1 {
                    return false;
                }
                let sep = if k == 0 { F192::ONE } else { basis_separations[k - 1] };
                weight += sep * at[0];
            }
            for (basis, start, beta) in &ood_bases {
                let at = partial_eval_lsb_ext(basis, &ris[*start..]);
                if at.len() != 1 {
                    return false;
                }
                weight += *beta * at[0];
            }
            return weight * mle_eval_ext(yr, &ris_tail) == t_r;
        }

        if next_root_idx >= proof.recursive_roots.len() {
            return false;
        }
        let root_next = proof.recursive_roots[next_root_idx];
        next_root_idx += 1;
        observe_root(sponge, &root_next);

        for _ in 0..ood_count(i + 2) {
            let Some(ood) = replay_ood(
                sponge,
                proof,
                n_current,
                &mut ood_idx,
                &mut tx_idx,
                &mut t_r,
                &mut running_quad,
            ) else {
                return false;
            };
            ood_bases.push((build_eq_table_ext(&ood.z), ris.len(), ood.beta));
        }

        // PoW grinding check for this iteration's query phase.
        if nonce_idx >= proof.grinding_nonces.len() {
            return false;
        }
        if !sponge.verify_pow(proof.grinding_nonces[nonce_idx], config.grinding_bits[i + 1] as u32) {
            return false;
        }
        nonce_idx += 1;

        let num_queries_i = config.queries[i + 1];
        let queries_i = sample_queries_ordered_with_raw(sponge, prev.block_len(), num_queries_i).0;
        let sq_i = sorted_unique_queries(&queries_i);
        let alpha_i = sponge.sample_vec(log2_ceil(num_queries_i));
        if recursive_proof_idx >= proof.recursive_proofs.len() {
            return false;
        }
        let rp = &proof.recursive_proofs[recursive_proof_idx];
        recursive_proof_idx += 1;
        if !verify_level_opens(
            &prev.root,
            prev.block_len(),
            &sq_i,
            &rp.opened_rows,
            prev.num_interleaved(),
            &rp.merkle_proof,
        ) {
            return false;
        }
        let ordered_rows_i = match fan_rows_to_ordered(&queries_i, &rp.opened_rows) {
            Some(x) => x,
            None => return false,
        };

        let sks_vks_i = eval_sk_at_vks(n_current);
        let (basis_i_induced, enforced_sum_i) =
            induce_sumcheck_poly(n_current, &sks_vks_i, &ordered_rows_i, &level_rs, &queries_i, &alpha_i);

        if tx_idx >= proof.sumcheck_transcript.len() {
            return false;
        }
        let intro_msg_i = proof.sumcheck_transcript[tx_idx];
        tx_idx += 1;
        sponge.observe(intro_msg_i.u_0);
        sponge.observe(intro_msg_i.u_2);
        let intro_quad_i = RoundQuad::from_msg(intro_msg_i, enforced_sum_i);
        let beta_i = sponge.sample();
        running_quad = RoundQuad::fold(&running_quad, &intro_quad_i, beta_i);
        t_r += beta_i * enforced_sum_i;
        basis_polys.push(basis_i_induced);
        basis_ris_starts.push(ris.len());
        basis_separations.push(beta_i);

        if prev
            .advance(
                root_next,
                config.level_ks[i + 1],
                n_current,
                config.log_inv_rates[i + 2],
            )
            .is_none()
        {
            return false;
        }
    }

    unreachable!()
}

// ===================================================================
// Succinct verifier
// ===================================================================

/// Thin wrapper of [`recursive_verifier_with_basis_succinct_with_squeezes`]
/// that discards the query squeezes: the signature every non-recursion caller
/// uses.
pub fn recursive_verifier_with_basis_succinct<F>(
    config: &VerifierConfig,
    proof: &LigeritoProof,
    log_n: usize,
    target: F192,
    expected_initial_root: &Hash,
    eval_b_at: F,
    sponge: &mut Sponge,
) -> bool
where
    F: Fn(&[F192]) -> F192,
{
    let mut discard = Vec::new();
    recursive_verifier_with_basis_succinct_with_squeezes(
        config,
        proof,
        log_n,
        target,
        expected_initial_root,
        eval_b_at,
        sponge,
        &mut discard,
    )
}

/// Succinct verifier for [`recursive_prover_with_basis`] (mirror of
/// `ligerito::recursive_verifier_with_basis_succinct`): instead of a dense
/// `b_initial` (2^log_n E-values) it takes a closure `eval_b_at` that evaluates
/// b's multilinear extension once, at the final fold point.
///
/// Per-level induced bases are never materialized: intro time uses the cheap
/// enforced-sum recomputation, and the residual uses the closed-form
/// `induce_sumcheck_evaluate_at_residual`. `log_n` is the committed
/// K-witness log size (b's logical dimension). Transcript replay is
/// byte-identical to the dense verifier.
///
/// On accept, fills `query_squeezes_out` with the raw query-sampling squeezes
/// per level in transcript order (the recursion harness reads `.c0/.c1` off
/// them to re-derive query positions). Left partially filled on reject; use it
/// only on `true`.
pub fn recursive_verifier_with_basis_succinct_with_squeezes<F>(
    config: &VerifierConfig,
    proof: &LigeritoProof,
    log_n: usize,
    target: F192,
    expected_initial_root: &Hash,
    eval_b_at: F,
    sponge: &mut Sponge,
    query_squeezes_out: &mut Vec<Vec<F192>>,
) -> bool
where
    // Called once at the terminal check with the full fold point.
    F: Fn(&[F192]) -> F192,
{
    let initial_k = config.initial_k;
    let r = config.level_steps;
    if r < 1 || config.level_ks.len() != r || config.log_inv_rates.len() != r + 1 {
        return false;
    }
    if config.ood_samples.first().copied().unwrap_or(0) != 0 {
        return false;
    }

    // The L0 root is the caller's statement (not proof data): absorb it
    // exactly where the prover absorbed its own.
    // (No opener domain-label absorb: the extension-field opener has none and the recursion
    // guest replays a label-free opening transcript; the observed `target` +
    // outer transcript context provide domain separation.)
    sponge.observe(target);
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
    sponge.observe(start_msg.u_0);
    sponge.observe(start_msg.u_2);
    let mut running_quad = RoundQuad::from_msg(start_msg, t_r);

    let fold_bits = |lvl: usize| -> u32 { config.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as u32 };
    let ood_count = |lvl: usize| -> usize { config.ood_samples.get(lvl).copied().unwrap_or(0) };
    let mut fold_nonce_idx = 0usize;
    let mut ood_idx = 0usize;
    struct OodCtx {
        z: Vec<F192>,
        ris_start: usize,
        beta: F192,
    }
    let mut ood_ctxs: Vec<OodCtx> = Vec::new();

    let Some(r_lane_fold) = replay_fold_rounds(
        sponge,
        proof,
        initial_k,
        fold_bits(0),
        &mut fold_nonce_idx,
        &mut tx_idx,
        &mut t_r,
        &mut running_quad,
    ) else {
        return false;
    };

    if proof.recursive_roots.is_empty() {
        return false;
    }
    let root_1 = proof.recursive_roots[0];
    observe_root(sponge, &root_1);

    for _ in 0..ood_count(1) {
        let Some(ood) = replay_ood(
            sponge,
            proof,
            log_n - initial_k,
            &mut ood_idx,
            &mut tx_idx,
            &mut t_r,
            &mut running_quad,
        ) else {
            return false;
        };
        ood_ctxs.push(OodCtx {
            z: ood.z,
            ris_start: initial_k,
            beta: ood.beta,
        });
    }

    // PoW grinding check for L0's query phase.
    let mut nonce_idx = 0usize;
    if nonce_idx >= proof.grinding_nonces.len() {
        return false;
    }
    if !sponge.verify_pow(proof.grinding_nonces[nonce_idx], config.grinding_bits[0] as u32) {
        return false;
    }
    nonce_idx += 1;

    let num_queries_0 = config.queries[0];
    let (queries_0, raw_0) = sample_queries_ordered_with_raw(sponge, block_len_0, num_queries_0);
    query_squeezes_out.push(raw_0);
    let alpha_0 = sponge.sample_vec(log2_ceil(num_queries_0));
    let sq_0 = sorted_unique_queries(&queries_0);
    if !verify_level_opens(
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
    let enforced_sum_0 = induce_sumcheck_enforced_sum(&ordered_rows_0, &r_lane_fold, &queries_0, &alpha_0);

    if tx_idx >= proof.sumcheck_transcript.len() {
        return false;
    }
    let intro_msg_0 = proof.sumcheck_transcript[tx_idx];
    tx_idx += 1;
    sponge.observe(intro_msg_0.u_0);
    sponge.observe(intro_msg_0.u_2);
    let intro_quad_0 = RoundQuad::from_msg(intro_msg_0, enforced_sum_0);
    let beta_0 = sponge.sample();
    running_quad = RoundQuad::fold(&running_quad, &intro_quad_0, beta_0);
    t_r += beta_0 * enforced_sum_0;

    // Per-level induced-basis evaluation context: small (no dense vec).
    struct LevelCtx {
        log_msg_cols: usize,
        queries: Vec<usize>,
        alpha: Vec<F192>, // ceil(log2 Q) elements (eq-tensor combination)
        ris_start: usize,
        beta: F192,
    }
    let mut level_ctxs: Vec<LevelCtx> = vec![LevelCtx {
        log_msg_cols: n1,
        queries: queries_0.clone(),
        alpha: alpha_0,
        ris_start: initial_k,
        beta: beta_0,
    }];
    let mut ris: Vec<F192> = r_lane_fold.clone();

    let mut prev = PrevLevel {
        root: root_1,
        log_num_interleaved: config.level_ks[0],
        log_msg_cols: n1 - config.level_ks[0],
        log_inv_rate: config.log_inv_rates[1],
    };
    let mut next_root_idx = 1usize;
    let mut recursive_proof_idx = 0usize;
    let mut n_current = n1;

    // Two independent counters, advanced at different points inside the body.
    #[allow(clippy::explicit_counter_loop)]
    for i in 0..r {
        let k_i = config.level_ks[i];
        if n_current < k_i {
            return false;
        }
        let Some(level_rs) = replay_fold_rounds(
            sponge,
            proof,
            k_i,
            fold_bits(i + 1),
            &mut fold_nonce_idx,
            &mut tx_idx,
            &mut t_r,
            &mut running_quad,
        ) else {
            return false;
        };
        ris.extend_from_slice(&level_rs);
        n_current -= k_i;

        if i == r - 1 {
            if ood_idx != proof.ood_values.len() || fold_nonce_idx != proof.fold_grinding_nonces.len() {
                return false;
            }
            let yr = &proof.final_proof.yr;
            if yr.len() != 1 << n_current {
                return false;
            }
            for v in yr {
                sponge.observe(*v);
            }
            // PoW grinding check for the last level's query phase.
            if nonce_idx >= proof.grinding_nonces.len() {
                return false;
            }
            if !sponge.verify_pow(proof.grinding_nonces[nonce_idx], config.grinding_bits[i + 1] as u32) {
                return false;
            }
            // (last nonce: nonce_idx is not advanced past it)

            let num_queries_last = config.queries[i + 1];
            let (queries_last, raw_last) = sample_queries_ordered_with_raw(sponge, prev.block_len(), num_queries_last);
            query_squeezes_out.push(raw_last);
            // Basis-induction challenge for the LAST commitment, sampled after
            // `yr` was observed and the queries are fixed (mirror of the
            // dense verifier, so both stay in lockstep).
            let alpha_last = sponge.sample_vec(log2_ceil(num_queries_last));
            let sq_last = sorted_unique_queries(&queries_last);
            if !verify_level_opens(
                &prev.root,
                prev.block_len(),
                &sq_last,
                &proof.final_proof.opened_rows,
                prev.num_interleaved(),
                &proof.final_proof.merkle_proof,
            ) {
                return false;
            }
            let ordered_rows_last = match fan_rows_to_ordered(&queries_last, &proof.final_proof.opened_rows) {
                Some(x) => x,
                None => return false,
            };

            let enforced_sum_last =
                induce_sumcheck_enforced_sum(&ordered_rows_last, &level_rs, &queries_last, &alpha_last);
            let Some(&intro_msg_last) = proof.sumcheck_transcript.get(tx_idx) else {
                return false;
            };
            tx_idx += 1;
            sponge.observe(intro_msg_last.u_0);
            sponge.observe(intro_msg_last.u_2);
            let intro_quad_last = RoundQuad::from_msg(intro_msg_last, enforced_sum_last);
            let beta_last = sponge.sample();
            running_quad = RoundQuad::fold(&running_quad, &intro_quad_last, beta_last);
            t_r += beta_last * enforced_sum_last;
            level_ctxs.push(LevelCtx {
                log_msg_cols: n_current,
                queries: queries_last.clone(),
                alpha: alpha_last,
                ris_start: ris.len(),
                beta: beta_last,
            });

            // Finish the sumcheck over the residual cube. Each basis and the
            // caller's weight are then evaluated once at `ris ++ ris_tail`.
            let yr_log_n = n_current;
            let mut ris_tail = Vec::with_capacity(yr_log_n);
            for j in 0..yr_log_n {
                let ri = sponge.sample();
                t_r = running_quad.eval(ri);
                ris_tail.push(ri);
                if j + 1 < yr_log_n {
                    let Some(&msg) = proof.sumcheck_transcript.get(tx_idx) else {
                        return false;
                    };
                    tx_idx += 1;
                    sponge.observe(msg.u_0);
                    sponge.observe(msg.u_2);
                    running_quad = RoundQuad::from_msg(msg, t_r);
                }
            }
            if tx_idx != proof.sumcheck_transcript.len() {
                return false;
            }

            let mut weight = F192::ZERO;
            for ctx in &level_ctxs {
                if ctx.log_msg_cols < yr_log_n || ctx.ris_start + (ctx.log_msg_cols - yr_log_n) > ris.len() {
                    return false;
                }
                let folded = ctx.log_msg_cols - yr_log_n;
                let mut point = ris[ctx.ris_start..ctx.ris_start + folded].to_vec();
                point.extend_from_slice(&ris_tail);
                let at = induce_sumcheck_evaluate_at_residual(
                    ctx.log_msg_cols,
                    &eval_sk_at_vks(ctx.log_msg_cols),
                    &ctx.queries,
                    &ctx.alpha,
                    &point,
                    0,
                );
                if at.len() != 1 {
                    return false;
                }
                weight += ctx.beta * at[0];
            }
            for ctx in &ood_ctxs {
                if ctx.z.len() < yr_log_n || ctx.ris_start + (ctx.z.len() - yr_log_n) > ris.len() {
                    return false;
                }
                let folded = ctx.z.len() - yr_log_n;
                let mut scalar = ctx.beta;
                for b in 0..folded {
                    scalar *= F192::ONE + ctx.z[b] + ris[ctx.ris_start + b];
                }
                weight += scalar * eq_eval(&ctx.z[folded..], &ris_tail);
            }

            let mut full_point = ris.clone();
            full_point.extend_from_slice(&ris_tail);
            weight += eval_b_at(&full_point);
            return weight * mle_eval_ext(yr, &ris_tail) == t_r;
        }

        if next_root_idx >= proof.recursive_roots.len() {
            return false;
        }
        let root_next = proof.recursive_roots[next_root_idx];
        next_root_idx += 1;
        observe_root(sponge, &root_next);

        for _ in 0..ood_count(i + 2) {
            let Some(ood) = replay_ood(
                sponge,
                proof,
                n_current,
                &mut ood_idx,
                &mut tx_idx,
                &mut t_r,
                &mut running_quad,
            ) else {
                return false;
            };
            ood_ctxs.push(OodCtx {
                z: ood.z,
                ris_start: ris.len(),
                beta: ood.beta,
            });
        }

        // PoW grinding check for this iteration's query phase.
        if nonce_idx >= proof.grinding_nonces.len() {
            return false;
        }
        if !sponge.verify_pow(proof.grinding_nonces[nonce_idx], config.grinding_bits[i + 1] as u32) {
            return false;
        }
        nonce_idx += 1;

        let num_queries_i = config.queries[i + 1];
        let (queries_i, raw_i) = sample_queries_ordered_with_raw(sponge, prev.block_len(), num_queries_i);
        query_squeezes_out.push(raw_i);
        let sq_i = sorted_unique_queries(&queries_i);
        let alpha_i = sponge.sample_vec(log2_ceil(num_queries_i));
        if recursive_proof_idx >= proof.recursive_proofs.len() {
            return false;
        }
        let rp = &proof.recursive_proofs[recursive_proof_idx];
        recursive_proof_idx += 1;
        if !verify_level_opens(
            &prev.root,
            prev.block_len(),
            &sq_i,
            &rp.opened_rows,
            prev.num_interleaved(),
            &rp.merkle_proof,
        ) {
            return false;
        }
        let ordered_rows_i = match fan_rows_to_ordered(&queries_i, &rp.opened_rows) {
            Some(x) => x,
            None => return false,
        };

        let enforced_sum_i = induce_sumcheck_enforced_sum(&ordered_rows_i, &level_rs, &queries_i, &alpha_i);

        if tx_idx >= proof.sumcheck_transcript.len() {
            return false;
        }
        let intro_msg_i = proof.sumcheck_transcript[tx_idx];
        tx_idx += 1;
        sponge.observe(intro_msg_i.u_0);
        sponge.observe(intro_msg_i.u_2);
        let intro_quad_i = RoundQuad::from_msg(intro_msg_i, enforced_sum_i);
        let beta_i = sponge.sample();
        running_quad = RoundQuad::fold(&running_quad, &intro_quad_i, beta_i);
        t_r += beta_i * enforced_sum_i;
        level_ctxs.push(LevelCtx {
            log_msg_cols: n_current,
            queries: queries_i.clone(),
            alpha: alpha_i,
            ris_start: ris.len(),
            beta: beta_i,
        });

        if prev
            .advance(
                root_next,
                config.level_ks[i + 1],
                n_current,
                config.log_inv_rates[i + 2],
            )
            .is_none()
        {
            return false;
        }
    }

    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ligerito::{QUERY_GRINDING_BITS, default_config, default_verifier_config};
    use primitives::test_rng::Rng;

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[test]
    fn fused_ext_butterfly_avx512_matches_scalar() {
        let mut rng = Rng::new(0x56c8_1b92_d4a7_30ef);
        for _ in 0..100 {
            let mut a: [F192; 8] = std::array::from_fn(|_| rng.ext());
            let mut b: [F192; 8] = std::array::from_fn(|_| rng.ext());
            let mut c: [F192; 8] = std::array::from_fn(|_| rng.ext());
            let mut d: [F192; 8] = std::array::from_fn(|_| rng.ext());
            let (mut want_a, mut want_b, mut want_c, mut want_d) = (a, b, c, d);
            let t_outer = F64(rng.next_u64());
            let t_inner_a = F64(rng.next_u64());
            let t_inner_b = F64(rng.next_u64());

            for lane in 0..8 {
                let new_a = want_a[lane] + want_c[lane].mul_base(t_outer);
                want_c[lane] += new_a;
                want_a[lane] = new_a;
                let new_b = want_b[lane] + want_d[lane].mul_base(t_outer);
                want_d[lane] += new_b;
                want_b[lane] = new_b;
                let new_a = want_a[lane] + want_b[lane].mul_base(t_inner_a);
                want_b[lane] += new_a;
                want_a[lane] = new_a;
                let new_c = want_c[lane] + want_d[lane].mul_base(t_inner_b);
                want_d[lane] += new_c;
                want_c[lane] = new_c;
            }

            butterfly_ext_fused_lanes(&mut a, &mut b, &mut c, &mut d, t_outer, t_inner_a, t_inner_b);
            assert_eq!(a, want_a);
            assert_eq!(b, want_b);
            assert_eq!(c, want_c);
            assert_eq!(d, want_d);
        }
    }

    /// Configs for a K-witness of `2^log_n` elements. Prefers the strict
    /// Secure-profile derivation (the production path, [`configs_for`]);
    /// its ladder needs L0 block_len >= ~300 queries, i.e. log_n >= 14, so
    /// smaller test sizes fall back to the ad-hoc `default_config` shape
    /// (test-only; same fallback the main crate uses for small instances).
    fn test_configs_for(log_n: usize) -> (ProverConfig, VerifierConfig) {
        match super::configs_for(log_n) {
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
        point: Vec<F192>,
        b_initial: Vec<F192>,
        target: F192,
        root: Hash,
        proof: LigeritoProof,
    }

    fn prove_instance(log_n: usize, seed: u64) -> Instance {
        let (pc, vc) = test_configs_for(log_n);
        let mut rng = Rng::new(seed);
        let witness: Vec<F64> = (0..1usize << log_n).map(|_| F64(rng.next_u64())).collect();
        let (cm, pd) = commit(&witness, pc.initial_k, pc.log_inv_rates[0]);
        let point: Vec<F192> = (0..log_n).map(|_| rng.ext()).collect();
        let b_initial = build_eq_table_ext(&point);
        let target = inner_product_base_ext(&witness, &b_initial);
        let mut ch = Sponge::new(b"ligerito-test", &[]);
        let proof = recursive_prover_with_basis(
            &pc,
            &witness,
            ArenaVec::from_slice(&b_initial),
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

    fn verify_instance(inst: &Instance, proof: &LigeritoProof) -> bool {
        let mut ch = Sponge::new(b"ligerito-test", &[]);
        recursive_verifier_with_basis(&inst.vc, proof, &inst.b_initial, inst.target, &inst.root, &mut ch)
    }

    /// Succinct verify with the eq weight evaluated at the terminal fold point.
    fn verify_succinct_instance(inst: &Instance, proof: &LigeritoProof) -> bool {
        let mut ch = Sponge::new(b"ligerito-test", &[]);
        let point = &inst.point;
        recursive_verifier_with_basis_succinct(
            &inst.vc,
            proof,
            inst.log_n,
            inst.target,
            &inst.root,
            |fold_point| eq_eval(point, fold_point),
            &mut ch,
        )
    }

    /// Both verifiers on the same proof, asserting they agree; returns the
    /// shared verdict.
    fn verify_both_agree(inst: &Instance, proof: &LigeritoProof, what: &str) -> bool {
        let dense = verify_instance(inst, proof);
        let succinct = verify_succinct_instance(inst, proof);
        assert_eq!(dense, succinct, "dense/succinct verdict split on {what}");
        dense
    }

    /// Pin the production 128-bit Johnson/OOD profile rather than the small-
    /// size test fallback.
    #[test]
    fn configs_johnson_profile_shape() {
        let (pc, vc) = configs_for(16).expect("Johnson profile feasible at log_n = 16");
        assert_eq!(pc.initial_k, 6);
        assert!(pc.level_steps >= 1);
        assert_eq!(vc.initial_k, pc.initial_k);
        assert_eq!(pc.ood_samples[0], 0);
        assert!(pc.ood_samples.iter().skip(1).all(|&s| s >= 1));
        assert!(pc.grinding_bits.iter().all(|&b| b == QUERY_GRINDING_BITS));
        assert!(pc.fold_grinding_bits.iter().all(|&b| b == 0));
        // And log_n = 12 is below the production ladder's feasibility floor, so
        // the tests there use the default_config fallback.
        assert!(configs_for(12).is_err());
    }

    /// The parallel eq builder must be byte-identical to the serial one, and
    /// the seeded variant must equal the gamma-scaled table, at sizes on both
    /// sides of the internal parallel level floor (2^12 halves, so n = 15
    /// exercises parallel levels; n = 6 stays fully serial).
    #[test]
    fn eq_table_parallel_and_seeded_match_serial() {
        let mut rng = Rng::new(21);
        for n in [0usize, 1, 6, 13, 15] {
            let point: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let serial = build_eq_table_ext(&point);
            assert_eq!(
                &*build_eq_table_ext_parallel(&point),
                &serial[..],
                "parallel mismatch at n={n}"
            );
            let g = rng.ext();
            let mut seeded = vec![F192::ZERO; 1 << n];
            build_eq_table_ext_seeded(&point, g, &mut seeded);
            let scaled: Vec<F192> = serial.iter().map(|&e| g * e).collect();
            assert_eq!(seeded, scaled, "seeded mismatch at n={n}");
        }
    }

    /// At log_n = 18 the production profile's L0 has log_msg_cols = 12 and
    /// enough queries to trip the sparse transposed-NTT dispatch in BOTH the
    /// prover and the dense verifier; pin the heuristic, then roundtrip.
    #[test]
    fn roundtrip_log_n_18_sparse_induce() {
        let (pc, _) = configs_for(18).expect("Johnson profile feasible at log_n = 18");
        assert!(
            induce_use_ntt_heuristic(18 - pc.initial_k, pc.log_inv_rates[0], pc.queries[0]),
            "shape must select the sparse transposed-NTT induce at L0"
        );
        // And the smaller roundtrips stay on the dense path (cols < 12).
        let (pc16, _) = configs_for(16).unwrap();
        assert!(!induce_use_ntt_heuristic(
            16 - pc16.initial_k,
            pc16.log_inv_rates[0],
            pc16.queries[0]
        ));
        let inst = prove_instance(18, 8);
        assert!(verify_instance(&inst, &inst.proof), "honest proof rejected");
    }

    /// The succinct verifier accepts an honest proof at log_n = 18, the one
    /// shape whose L0 takes the sparse transposed-NTT path. Smaller shapes are
    /// covered by `dense_and_succinct_agree`.
    #[test]
    fn succinct_roundtrips() {
        let inst = prove_instance(18, 8);
        assert!(
            verify_succinct_instance(&inst, &inst.proof),
            "succinct verifier rejected an honest proof at log_n=18"
        );
    }

    /// Dense and succinct must return the same verdict on every proof:
    /// honest plus a spread of randomized single-bit tampers, at both a
    /// fallback-config shape (log_n = 12) and the Johnson/OOD production
    /// shape (log_n = 16).
    #[test]
    fn dense_and_succinct_agree() {
        for (log_n, seed) in [(12usize, 11u64), (16, 12)] {
            let inst = prove_instance(log_n, seed);
            assert!(verify_both_agree(&inst, &inst.proof, "honest proof"));

            let mut rng = Rng::new(seed ^ 0xABCD);
            type Tamper = fn(&mut LigeritoProof, u64);
            let tampers: &[(&str, Tamper)] = &[
                ("L0 opened row", |p, r| {
                    let row = (r as usize) % p.initial_proof.opened_rows.len();
                    p.initial_proof.opened_rows[row][0].0 ^= 1;
                }),
                ("final-level opened row", |p, r| {
                    let row = (r as usize) % p.final_proof.opened_rows.len();
                    p.final_proof.opened_rows[row][0].c0 ^= 1;
                }),
                ("sumcheck u_0", |p, r| {
                    let idx = (r as usize) % p.sumcheck_transcript.len();
                    p.sumcheck_transcript[idx].u_0.c0 ^= 1;
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
                tamper(&mut bad, rng.next_u64());
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
            if !inst.proof.ood_values.is_empty() {
                let mut bad = inst.proof.clone();
                bad.ood_values[0] += F192::ONE;
                assert!(
                    !verify_both_agree(&inst, &bad, "OOD value"),
                    "tampered OOD value accepted at log_n={log_n}"
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

    /// The E-valued interleaved NTT with K-twiddles must act lane-wise on the
    /// tower coordinates: transforming (c0, c1) packed as F192 equals two
    /// independent F64 transforms of the c0 and c1 lanes.
    #[test]
    fn ext_ntt_matches_two_base_ntts() {
        let mut rng = Rng::new(5);
        for (log_d, lanes, start_layer) in [(6usize, 4usize, 0usize), (9, 2, 2), (10, 1, 1)] {
            let ntt = AdditiveNttF64::standard(log_d);
            let n = (1usize << log_d) * lanes;
            let ext: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
            let mut c0: Vec<F64> = ext.iter().map(|e| F64(e.c0)).collect();
            let mut c1: Vec<F64> = ext.iter().map(|e| F64(e.c1)).collect();
            let mut c2: Vec<F64> = ext.iter().map(|e| F64(e.c2)).collect();
            let mut ext_t = ext.clone();
            forward_transform_interleaved_ext_from_layer(&ntt, &mut ext_t, lanes, start_layer);
            ntt.forward_transform_interleaved_from_layer(&mut c0, lanes, start_layer);
            ntt.forward_transform_interleaved_from_layer(&mut c1, lanes, start_layer);
            ntt.forward_transform_interleaved_from_layer(&mut c2, lanes, start_layer);
            for i in 0..n {
                assert_eq!(ext_t[i], F192::new(c0[i].0, c1[i].0, c2[i].0), "mismatch at {i}");
            }
        }
    }

    /// The sparse transposed-NTT induce must be byte-identical to the dense
    /// LCH-expansion induce (same guarantee the original pins). Covers both
    /// the windowed sparse-prefix path (log_block >= 12, k = 8) and the
    /// scatter + full-dense-transpose path (log_block < 12, k = 0).
    #[test]
    fn induce_via_ntt_matches_dense() {
        let mut rng = Rng::new(9);
        for (log_msg_cols, log_inv_rate, lanes_log, n_queries) in [(12usize, 1usize, 5usize, 130usize), (6, 2, 3, 40)] {
            let block_len = 1usize << (log_msg_cols + log_inv_rate);
            let lanes = 1usize << lanes_log;
            // Distinct sorted query positions plus one aligned random row each.
            let mut qs: Vec<usize> = Vec::new();
            let mut seen = std::collections::HashSet::new();
            while qs.len() < n_queries {
                let q = (rng.next_u64() as usize) % block_len;
                if seen.insert(q) {
                    qs.push(q);
                }
            }
            qs.sort_unstable();
            let rows: Vec<Vec<F64>> = (0..n_queries)
                .map(|_| (0..lanes).map(|_| F64(rng.next_u64())).collect())
                .collect();
            let v_challenges: Vec<F192> = (0..lanes_log).map(|_| rng.ext()).collect();
            let alpha: Vec<F192> = (0..log2_ceil(n_queries)).map(|_| rng.ext()).collect();

            let sks_vks = eval_sk_at_vks(log_msg_cols);
            let dense = induce_sumcheck_poly(log_msg_cols, &sks_vks, &rows, &v_challenges, &qs, &alpha);
            let via_ntt =
                induce_sumcheck_poly_via_ntt_base(log_msg_cols, log_inv_rate, &rows, &v_challenges, &qs, &alpha);
            assert_eq!(dense.1, via_ntt.1, "enforced_sum mismatch");
            assert_eq!(&*dense.0, &*via_ntt.0, "basis_poly mismatch");
        }
    }

    /// The scalar and parallel ext transforms agree (parallel path is only
    /// taken for larger inputs; force both on the same data).
    #[test]
    fn ext_ntt_scalar_matches_parallel() {
        let mut rng = Rng::new(6);
        let log_d = 13;
        let lanes = 2;
        let ntt = AdditiveNttF64::standard(log_d);
        let n = (1usize << log_d) * lanes;
        let orig: Vec<F192> = (0..n).map(|_| rng.ext()).collect();
        let mut a = orig.clone();
        let mut b = orig;
        forward_transform_interleaved_ext_scalar_from_layer(&ntt, &mut a, lanes, 1);
        forward_transform_interleaved_ext_parallel_from_layer(&ntt, &mut b, lanes, 1);
        assert_eq!(a, b);
    }
}
