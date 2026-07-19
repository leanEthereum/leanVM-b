// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from bolt-rs (https://github.com/bcc-research/bolt-rs,
// `ligerito_recursive.rs`).

//! Field-independent configuration and soundness analysis for Ligerito.
//!
//! Soundness regimes (our paper App. C.3): unique decoding (Thm `ca-udr`,
//! BCHKS25 Cor. 1.4 — the ONE shipped configuration, see [`SECURITY_BITS`])
//! and Johnson list decoding with out-of-domain binding (Thm `ca-johnson`,
//! BCHKS25 Thm 4.6 + Johnson interleaved list bound — hand-built configs
//! only). See [`SoundnessRegime`].
//!
use serde::{Deserialize, Serialize};

// ===================================================================
// Config
// ===================================================================

// The ONE Ligerito configuration this repo ships: a UDR/LDR hybrid at 120-bit
// round-by-round soundness. Rounds 1–2 are unique-decoding (L0 rate 1/2, L1
// rate 1/16); from round 3 the levels are Johnson list-decoding with one
// OOD-challenge-ground out-of-domain sample, at the lowest rate whose fold grind
// fits `max_fold_grind`. See `LigeritoSecurityConfig::derive_config` and
// `level_log_inv_rate`.

/// Round-by-round soundness target (bits): every round must individually
/// clear this level (total security = min over rounds, per the Fiat-Shamir /
/// `soundcalc` convention).
pub const SECURITY_BITS: usize = 120;

/// L0 code rate index: `rho_0 = 2^-LOG_INV_RATE_0` (rate 1/2).
pub const LOG_INV_RATE_0: usize = 1;

/// Query-phase grinding bits: with `g` bits ground, the per-level queries only
/// need to cover `SECURITY_BITS - g` bits (validation rule 3) — about 15%
/// fewer queries, which recursion feels directly (the query walk dominates a
/// guest).
pub const QUERY_GRINDING_BITS: usize = 18;

pub const INITIAL_FOLDING_FATOR: usize = 6;
pub const SUBSEQUENT_FOLDING_FACTORS: usize = 3;

/// Folding stops once at most this many variables remain: the residual
/// polynomial (`yr`, at most `2^RESIDUAL_MAX_LOG` coefficients) is sent in
/// clear instead of committed and folded further.
pub const RESIDUAL_MAX_LOG: usize = 5;

#[derive(Clone, Debug)]
pub struct ProverConfig {
    pub log_inv_rates: Vec<usize>,
    pub level_steps: usize,
    pub initial_log_msg_cols: usize,
    pub initial_log_num_interleaved: usize,
    pub initial_k: usize,
    pub level_log_msg_cols: Vec<usize>,
    pub level_ks: Vec<usize>,
    /// Per-level query counts (L0, L1, ..., L_r). Length = level_steps + 1.
    /// [`LigeritoSecurityConfig::derive_config`] fills these from the
    /// per-level soundness analysis.
    pub queries: Vec<usize>,
    /// Per-level **query-phase** PoW grinding bits (L0, L1, ..., L_r), ground
    /// post-commit/pre-queries. Length = level_steps + 1. Each bit here
    /// substitutes for ~1/log₂(1/(1−γ)) queries at that level.
    pub grinding_bits: Vec<usize>,
    /// Per-level **fold-challenge** PoW grinding bits (L0, ..., L_r), ground
    /// immediately before EACH of the level's fold challenges (so a level
    /// with `k` folds does `k` grinds of this many bits). Boosts the
    /// proximity-gap term, which lives on the fold challenges. Length =
    /// level_steps + 1.
    pub fold_grinding_bits: Vec<usize>,
    /// Per-level OOD-challenge PoW grinding bits (0 for UDR levels).
    pub ood_grinding_bits: Vec<usize>,
    /// Per-commit-level out-of-domain samples (L0, ..., L_r), taken right
    /// after the level's Merkle root enters the transcript. `[0]` must be 0:
    /// L0 is bound by the opening's own (post-commit, random-point)
    /// evaluation claim. Length = level_steps + 1.
    pub ood_samples: Vec<usize>,
}

/// The per-level shape table a [`VerifierConfig`] implies for a
/// `log_n`-variable opening — the numbers every consumer of the multilevel
/// protocol (the verifier itself, recursion harnesses) otherwise re-derives.
#[derive(Clone, Debug)]
pub struct LevelShapes {
    /// Level count (`level_steps + 1`).
    pub levels: usize,
    /// Fold count per level: `initial_k` then `level_ks`.
    pub ks: Vec<usize>,
    /// Log message columns entering each level's fold (`log_n - initial_k`,
    /// then descending by each level's `k`).
    pub log_msg_cols: Vec<usize>,
    /// Committed block length per level (`msg_cols * inv_rate`).
    pub block_len: Vec<usize>,
    /// The residual cube dimension left after every fold.
    pub yr_log_n: usize,
}

#[derive(Clone, Debug)]
pub struct VerifierConfig {
    pub log_inv_rates: Vec<usize>,
    pub level_steps: usize,
    pub initial_log_msg_cols: usize,
    pub initial_log_num_interleaved: usize,
    pub initial_k: usize,
    pub level_log_msg_cols: Vec<usize>,
    pub level_ks: Vec<usize>,
    /// Per-level query counts. Length = level_steps + 1.
    pub queries: Vec<usize>,
    /// Per-level query-phase PoW grinding bits. Length = level_steps + 1.
    pub grinding_bits: Vec<usize>,
    /// Per-level fold-challenge PoW grinding bits (one grind per fold
    /// challenge of the level). Length = level_steps + 1.
    pub fold_grinding_bits: Vec<usize>,
    /// Per-level OOD-challenge PoW grinding bits (0 for UDR levels).
    pub ood_grinding_bits: Vec<usize>,
    /// Per-commit-level OOD samples. Length = level_steps + 1.
    pub ood_samples: Vec<usize>,
}

impl VerifierConfig {
    /// See [`LevelShapes`].
    pub fn level_shapes(&self, log_n: usize) -> LevelShapes {
        let r = self.level_steps;
        let ks: Vec<usize> = std::iter::once(self.initial_k).chain(self.level_ks.iter().copied()).collect();
        let mut log_msg_cols = vec![log_n - self.initial_k];
        for i in 0..r {
            log_msg_cols.push(log_msg_cols[i] - self.level_ks[i]);
        }
        let mut block_len = vec![1usize << (self.initial_log_msg_cols + self.log_inv_rates[0])];
        for i in 0..r {
            block_len.push(1usize << (self.level_log_msg_cols[i] + self.log_inv_rates[i + 1]));
        }
        LevelShapes {
            levels: r + 1,
            ks,
            yr_log_n: *log_msg_cols.last().unwrap(),
            log_msg_cols,
            block_len,
        }
    }
}


/// Proximity loss `ε*` for the UDR (unique-decoding regime) analysis. It
/// would back the proximity radius off to `γ = δ/2 − ε*` (δ = 1 − ρ the
/// code's relative distance); set to `0`, so we decode to the full
/// unique-decoding radius `γ = δ/2` with no backoff. Per our paper's Appendix
/// C.3 (Theorem `ca-udr`, BCHKS25 Cor. 1.4) the proximity-gap exceptional set
/// is then `a = γ·n + 1` — length-dependent (see [`paper_thm_1_4_log_a`]), so
/// `eps_pg = 128 − log₂ a` shrinks ~1 bit per witness doubling and is
/// recovered by `fold_grinding_bits`.
pub const UDR_PROXIMITY_LOSS: f64 = 0.0;

/// Soundness (in bits) the query phase must close on its own at every level
/// (the "100 bits from queries always" policy).
#[cfg(test)]
const UDR_TARGET_BITS: f64 = 100.0;

/// Number of queries for 100-bit soundness in the **unique-decoding regime**
/// at rate `2^(-log_inv_rate)`: `γ = δ/2 = (1−ρ)/2`, per-query soundness
/// `log₂(1/(1−γ))` (see [`udr_per_query_bits`]). Within the unique decoding
/// radius the prover is pinned to a single codeword, so there is no list and
/// no union-bound term — queries close the full target by themselves.
/// Per-query soundness saturates below 1 bit (`γ < 1/2`), so slimmer codes
/// bottom out near `UDR_TARGET_BITS` queries: 243 at rate 1/2, 148 at 1/4,
/// 121 at 1/8, 110 at 1/16, 105 at 1/32.
#[cfg(test)]
pub fn udr_queries(log_inv_rate: usize) -> usize {
    assert!(log_inv_rate > 0, "log_inv_rate=0 (rate 1) has no soundness");
    let per_q = udr_per_query_bits_asymptotic(log_inv_rate);
    (UDR_TARGET_BITS / per_q).ceil() as usize
}

/// Build an ad-hoc Ligerito config from the raw PCS shape, WITHOUT the
/// per-level soundness derivation of [`LigeritoSecurityConfig::derive_config`].
/// `log_n` is the packed-witness log size (= `m - LOG_PACKING`).
///
/// Strategy: 3-bit recursive folds (`k_i = 3`) with **decreasing rate** (one
/// rate step per level) until the residual is small (`≤ 5` bits), asserting
/// `block_len ≥ udr_queries(rate)` at every level. Returns `Err` when no
/// feasible config exists (e.g. `log_n` too small for the chosen rate).
///
/// Test-support only: the K PCS tests exercise sizes below `derive_config`'s
/// feasibility floor, where they fall back to this shape. Production callers
/// use `derive_config` (the audited, per-level-sound path).
#[cfg(test)]
pub fn default_config(
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
) -> Result<ProverConfig, &'static str> {
    let initial_k = log_batch_size;
    if log_n <= initial_k {
        return Err("log_n must be > initial_k");
    }

    let mut log_inv_rates = vec![log_inv_rate];
    let mut level_ks = Vec::new();
    let mut level_log_msg_cols = Vec::new();

    let mut n_running = log_n - initial_k;
    let mut rate_running = log_inv_rate;

    // L0 feasibility check.
    {
        let block_len_log = n_running + rate_running;
        let qs = udr_queries(rate_running);
        if (1usize << block_len_log) < qs {
            return Err("L0 block_len < udr_queries — log_n too small for chosen rate");
        }
    }

    while n_running > 5 {
        let k = 3.min(n_running);
        let log_msg_cols_next = n_running - k;
        // Pick the smallest rate ≥ rate_running+1 such that block_len ≥ queries.
        let mut next_rate = rate_running + 1;
        loop {
            let bl = 1usize << (log_msg_cols_next + next_rate);
            let qs = udr_queries(next_rate);
            if bl >= qs {
                break;
            }
            next_rate += 1;
            if next_rate > 20 {
                return Err("could not find feasible recursive rate (level too deep)");
            }
        }
        level_log_msg_cols.push(log_msg_cols_next);
        level_ks.push(k);
        log_inv_rates.push(next_rate);
        n_running -= k;
        rate_running = next_rate;
    }

    if level_ks.is_empty() {
        return Err("log_n too small — no recursive levels needed (use BaseFold directly)");
    }

    let queries: Vec<usize> = log_inv_rates.iter().map(|&r| udr_queries(r)).collect();
    let n_levels = log_inv_rates.len();
    let grinding_bits = vec![0usize; n_levels];

    Ok(ProverConfig {
        log_inv_rates: log_inv_rates.clone(),
        level_steps: level_ks.len(),
        initial_log_msg_cols: log_n - initial_k,
        initial_log_num_interleaved: initial_k,
        initial_k,
        level_log_msg_cols,
        level_ks,
        queries,
        grinding_bits,
        fold_grinding_bits: vec![0usize; n_levels],
        ood_samples: vec![0usize; n_levels],
        ood_grinding_bits: vec![0usize; n_levels],
    })
}

/// The [`VerifierConfig`] matching [`default_config`] (test-support only).
#[cfg(test)]
pub fn default_verifier_config(
    log_n: usize,
    log_batch_size: usize,
    log_inv_rate: usize,
) -> Result<VerifierConfig, &'static str> {
    let p = default_config(log_n, log_batch_size, log_inv_rate)?;
    Ok(VerifierConfig {
        log_inv_rates: p.log_inv_rates,
        level_steps: p.level_steps,
        initial_log_msg_cols: p.initial_log_msg_cols,
        initial_log_num_interleaved: p.initial_log_num_interleaved,
        initial_k: p.initial_k,
        level_log_msg_cols: p.level_log_msg_cols,
        level_ks: p.level_ks,
        queries: p.queries,
        grinding_bits: p.grinding_bits,
        fold_grinding_bits: p.fold_grinding_bits,
        ood_samples: p.ood_samples,
        ood_grinding_bits: p.ood_grinding_bits,
    })
}

/// Level-ladder shape: per-level dims (index 0 = L0) plus the residual.
struct LadderShape {
    log_inv_rates: Vec<usize>,
    log_msg_cols: Vec<usize>,
    log_num_interleaved: Vec<usize>,
    k_levels: Vec<usize>,
    yr_log_n: usize,
}

/// Shared shape derivation behind [`LigeritoSecurityConfig::derive_config`]:
/// `SUBSEQUENT_FOLDING_FACTORS`-bit level folds with the per-level inverse-rate
/// index supplied by `rate_for_level` (index 0 = L0). Unlike a monotone rate
/// ladder, the caller picks each level's rate directly — the shipped schedule
/// (see [`level_log_inv_rate`]) descends to a very low rate on the deep Johnson
/// levels, where the list-decoding radius is near-maximal (few queries) and the
/// larger block comfortably holds them. Query-feasibility (queries ≤ block
/// length) is enforced per level in `derive_config`.
fn derive_ladder_shape(
    log_n: usize,
    initial_k: usize,
    rate_for_level: impl Fn(usize) -> usize,
) -> Result<LadderShape, String> {
    if log_n <= initial_k {
        return Err("log_n must be > initial_k".into());
    }
    let mut shape = LadderShape {
        log_inv_rates: vec![rate_for_level(0)],
        log_msg_cols: vec![log_n - initial_k],
        log_num_interleaved: vec![initial_k],
        k_levels: vec![initial_k],
        yr_log_n: 0,
    };
    let mut n_running = log_n - initial_k;
    let mut level = 0usize;
    while n_running > RESIDUAL_MAX_LOG {
        level += 1;
        let k = SUBSEQUENT_FOLDING_FACTORS.min(n_running);
        let log_msg_cols_next = n_running - k;
        shape.log_inv_rates.push(rate_for_level(level));
        shape.log_msg_cols.push(log_msg_cols_next);
        shape.log_num_interleaved.push(k);
        shape.k_levels.push(k);
        n_running -= k;
    }
    if shape.k_levels.len() < 2 {
        return Err("log_n too small: needs at least 2 fold levels".into());
    }
    shape.yr_log_n = n_running;
    Ok(shape)
}

/// Round-2 (L1) inverse-rate index: 1/16. A low-rate unique-decoding proximity
/// round after the initial commit (L0 = [`LOG_INV_RATE_0`], 1/2).
const ROUND2_LOG_INV_RATE: usize = 4;

/// The shipped regime by level: unique-decoding for rounds 1–2 (L0, L1),
/// Johnson list-decoding from round 3 (L2) on.
fn level_is_johnson(level_idx: usize) -> bool {
    level_idx >= 2
}

/// Shipped inverse-rate for a level of `cols` message columns and `ilv`
/// interleaved lanes, the heart of the UDR/LDR hybrid:
///   L0 (round 1): 1/2   — the initial commit's rate.
///   L1 (round 2): 1/16  — a low-rate unique-decoding proximity round.
///   L2+ (round 3+): the **lowest** rate (largest Johnson radius γ ≈ 1−√ρ,
///        hence fewest queries) whose length-dependent fold grind still fits
///        `MAX_FOLD_GRINDING_BITS`. Because the proximity-gap set grows like
///        `2^(cols + 2.5·log_inv_rate)`, the wide early Johnson levels are held
///        to a higher rate and the deep (small-`cols`) levels are pushed to
///        very low rates (1/64, 1/128 …) where a handful of queries suffice and
///        the large block trivially holds them.
/// Returns `None` for a Johnson level where no rate fits the grind cap.
fn level_log_inv_rate(
    level_idx: usize,
    cols: usize,
    ilv: usize,
    target_bits: usize,
    query_grind: usize,
) -> Option<usize> {
    if level_idx == 0 {
        return Some(LOG_INV_RATE_0);
    }
    if !level_is_johnson(level_idx) {
        return Some(ROUND2_LOG_INV_RATE);
    }
    // Highest inverse-rate index (lowest rate ⇒ fewest queries) that is Johnson-
    // feasible: fold/OOD grind within cap AND query count within the block.
    (1..=MAX_LOG_INV_RATE).rev().find(|&lir| {
        best_johnson_candidate(level_idx, lir, cols, ilv, target_bits, query_grind, max_fold_grind(level_idx))
            .is_some_and(|j| j.queries <= (1usize << (cols + lir)))
    })
}

/// Ceiling on the inverse-rate index the deep-level rate search will consider.
const MAX_LOG_INV_RATE: usize = 12;

// ===================================================================
// Security configuration schema
// ===================================================================
//
// Auditable, per-level spec for a Ligerito instance: query count, grinding
// bits, slack-from-Johnson, and the proximity-gap analysis the parameters
// were derived under. Designed to be (de)serializable so it can live in a
// TOML/JSON file alongside the prover/verifier code.

/// Which proximity-gap analysis a level's parameters were derived under.
/// Determines which formulas the implementation should verify against the
/// declared (η, queries, grinding) tuple.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SoundnessRegime {
    /// Unique decoding radius: γ = δ/2 (δ = 1 − ρ the code's relative
    /// distance; no proximity-loss backoff). Theorem `ca-udr` of our paper's
    /// Appendix C.3 (adapted from Ben-Sasson–Carmon–Haböck–Kopparty–Saraf
    /// "On Proximity Gaps for Reed–Solomon Codes", 2025, Corollary 1.4): the
    /// exceptional set is `a = γ·n + 1`, growing with the codeword length `n`,
    /// so the proximity-gap term is recovered per level by `fold_grinding_bits`
    /// rather than coming out 0. `eta` is `None` for this regime.
    Udr,
    /// Johnson radius with explicit slack `η` (γ = (1 − √ρ) − η) **with
    /// out-of-domain binding**. Theorem 1.5 of the same paper gives the
    /// proximity-gap exceptional set `a = O_ρ(n / η^5)`; the level's
    /// `fold_grinding_bits` should be ≥ (target_bits − log₂(q/a)).
    /// Binding to a single codeword of the (Johnson-bounded) interleaved list
    /// is via `ood_samples` explicit multilinear OOD evaluations — except at
    /// L0, where the opening's own post-commit random evaluation claim plays
    /// the OOD role (union over the list, `L·μ/q`), so `ood_samples = 0`.
    ///
    /// Note there is deliberately no plain `Johnson` variant: without OOD
    /// binding the query phase pays a union bound over the interleaved list
    /// (≈ 19–52 bits here), which our query counts do not include. A config
    /// claiming Johnson soundness without OOD accounting would be unsound.
    JohnsonOod,
}

/// Where in a level's Fiat-Shamir transcript the grinding step lands.
/// Currently only one choice; reserved for future protocol variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GrindingStep {
    /// Grind happens after the level's Merkle root is observed but before
    /// query positions are sampled. Standard FRI/STARK pattern.
    PostCommitPreQueries,
}

/// Parameters for a single level in the multilevel Ligerito ladder.
/// L0 = the upstream `pcs::commit` output (reused, not re-committed);
/// L1 .. L_{r−1} are the level commits; the final residual `yr` block
/// is described separately in [`FinalBlockConfig`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LigeritoLevelConfig {
    /// PCS rate at this level: codeword expansion factor = 2^log_inv_rate.
    pub log_inv_rate: usize,
    /// Message dimension at this level (log of the number of field columns in
    /// the codeword). `log_msg_cols + log_inv_rate = log_2(block_len)`.
    pub log_msg_cols: usize,
    /// Log of lane width per Merkle leaf at this level. For L0 = `initial_k`;
    /// for L_i (i ≥ 1) = the previous level's `k`.
    pub log_num_interleaved: usize,
    /// Number of sumcheck folds taken at this level. For L0 = `initial_k`
    /// (the lane fold); for L_i (i ≥ 1) = the level fold k_{i−1}.
    pub k: usize,
    /// Which proximity-gap analysis the (eta, queries, grinding_bits)
    /// tuple was derived under. Determines the formulas the implementation
    /// validates against.
    pub regime: SoundnessRegime,
    /// Slack from the Johnson radius. Required for the `JohnsonOod` regime;
    /// must be `None` for `Udr`.
    pub eta: Option<f64>,
    /// Proximity loss `ε*` for the UDR radius `γ = δ/2 − ε*` (our paper
    /// App. C.3 / BCHKS25 Cor. 1.4); `0` in the shipped configs (full
    /// unique-decoding radius δ/2, no backoff). Required for `Udr`; must be
    /// `None` for `JohnsonOod`. The exceptional set is `a = γ·n + 1`,
    /// length-dependent (see [`paper_thm_1_4_log_a`]).
    #[serde(default)]
    pub proximity_loss: Option<f64>,
    /// Number of codeword position queries opened at this level (the FRI
    /// query phase). Bounds the per-query soundness term `(1−γ)^Q`.
    pub queries: usize,
    /// **Query-phase** PoW grinding bits, ground post-commit/pre-queries
    /// (see [`GrindingStep`]). Each bit substitutes for
    /// ~1/log₂(1/(1−γ)) queries at this level.
    pub grinding_bits: usize,
    /// **Fold-challenge** PoW grinding bits, ground immediately before EACH
    /// of this level's `k` fold challenges. Boosts the
    /// proximity-gap term (which lives on the fold challenges):
    /// `eps_pg + fold_grinding_bits ≥ target`.
    #[serde(default)]
    pub fold_grinding_bits: usize,
    /// Out-of-domain samples taken right after this level's commit enters
    /// the transcript (`JohnsonOod` only). Each binds the prover to a single
    /// codeword of the interleaved list via a multilinear evaluation claim.
    /// Must be 0 at L0 (bound by the opening's own post-commit evaluation
    /// claim) and ≥ 1 at deeper `JohnsonOod` levels.
    #[serde(default)]
    pub ood_samples: usize,
    /// **OOD-challenge** PoW grinding bits, ground on the out-of-domain point so
    /// a single sample binds the whole Johnson list: `eps_ood +
    /// ood_grinding_bits ≥ target`. 0 for UDR levels (no OOD).
    #[serde(default)]
    pub ood_grinding_bits: usize,
    /// Security target this level guarantees, post-grinding.
    pub target_security_bits: usize,
    /// Diagnostic — `log₂(q/a)` under the chosen regime. The implementation
    /// should assert this matches the formula at startup, modulo rounding.
    pub expected_eps_pg_bits: f64,
    /// Diagnostic — `Q · log₂(1/(1−γ))`. Should be ≥
    /// `target_security_bits − grinding_bits`.
    pub expected_eps_query_bits: f64,
    /// Diagnostic — OOD binding bits (`JohnsonOod` only):
    /// `s·(128 − log₂μ) − (2·log₂L − 1)` for explicit samples, or
    /// `128 − log₂L − log₂μ` for the implicit L0 binding, where `L` is the
    /// Johnson interleaved list size and `μ` the level's variable count.
    #[serde(default)]
    pub expected_eps_ood_bits: Option<f64>,
}

/// Descriptor for the final-residual block (`yr`) sent in the clear at the
/// end of the last fold level. It has no commit and no queries, so the
/// only meaningful parameter is its dimension.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FinalBlockConfig {
    /// `log_2(|yr|)` — number of extension-field values sent in the clear. The last
    /// fold level's sumcheck stops at this dim instead of folding to 1.
    pub yr_log_n: usize,
}

/// Complete security spec for one Ligerito instance, covering a single
/// `(hash, m)` pair. Designed to round-trip cleanly via serde (TOML/JSON).
///
/// **Validation invariants** (checked by [`Self::validate`]):
/// 1. `initial_k + Σ levels[1..].k + final_block.yr_log_n == log_n`.
/// 2. Each level's `expected_eps_pg_bits` is consistent with the declared
///    regime and `eta` (within tolerance).
/// 3. Each level's `expected_eps_query_bits ≥ target_security_bits −
///    grinding_bits` (queries cover what grinding doesn't).
/// 4. `eta` is `Some` iff regime ∈ {Johnson, JohnsonOod}; `None` for Udr.
/// 5. `log_msg_cols`, `log_num_interleaved`, `k` match the
///    level-shape constraint (each level's input dim equals the
///    previous level's `log_msg_cols`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LigeritoSecurityConfig {
    /// Block-encoder log size: m = log₂(witness bit count).
    pub m: usize,
    /// Committed-witness log dimension.
    pub log_n: usize,
    /// L0 lane fold. Must equal the upstream `PcsParams::log_batch_size` so
    /// the L0 commit can be reused without re-committing.
    pub initial_k: usize,
    /// Round-by-round security target (bits): validate() asserts every error
    /// term at every round (round-by-round soundness) clears at least this
    /// much. Total security is the *minimum* over rounds — the notion that
    /// governs Fiat-Shamir security (cf. Ethereum's `soundcalc`) — so there is
    /// deliberately no whole-protocol union bound over terms.
    pub target_security_bits: usize,
    /// Identifier of the proximity-gap analysis used. Self-documents which
    /// theorem the per-level parameters were derived from. Example:
    /// `"ben_sasson_2025_thm_4_6"`.
    pub analysis_version: String,
    /// Field of the protocol. Example: `"f128"`.
    pub field: String,
    /// Hash function used by Merkle + FS sponge. Example: `"sha256"`.
    pub hash: String,
    /// Where in the per-level FS transcript grinding is placed.
    pub grinding_step: GrindingStep,
    /// Per-level parameters, in order L0, L1, L2, ....
    pub levels: Vec<LigeritoLevelConfig>,
    /// Final residual block descriptor.
    pub final_block: FinalBlockConfig,
}

/// Extension-field size used for soundness analysis: `q = 2^128`.
const ANALYSIS_LOG_Q: f64 = 128.0;

/// Round a float to one decimal place. Used to round paper-predicted
/// soundness diagnostics so the generated TOMLs stay readable.
fn round1(x: f64) -> f64 {
    (x * 10.0).round() / 10.0
}

/// Bit-level tolerance when comparing declared diagnostics
/// (`expected_eps_pg_bits` / `expected_eps_query_bits`) against the value
/// computed from the regime's formulas. Set generously enough that rounding
/// in the TOML doesn't cause spurious failures, but tightly enough that an
/// incorrect declaration of η, Q, or grinding can't slip through.
const PAPER_COMPAT_TOL_BITS: f64 = 0.6;

/// Proximity-gap exceptional set for the list-decoding (Johnson) regime, per
/// our paper's Appendix C.3 (Theorem `ca-johnson`, adapted from BCHKS25
/// Theorem 4.6). For a Reed–Solomon code of rate `ρ`, codeword length `n`,
/// and Johnson slack `η` (proximity radius `γ = 1 − √ρ − η`), the MCA error is
/// `a/|F|` with
///
///   `a = [2(m+½)^5 + 3(m+½)·γ·ρ] / (3·ρ^{3/2}) · n + (m+½)/√ρ`,
///
/// where `η = 1 − √ρ − γ` and `m = max(⌈√ρ/(2η)⌉, 3)`. Returns `log₂ a`.
///
/// This is the per-fold-step MCA error, stated for a two-row interleaved word
/// (`C ∈ F^{2×n}`). The ℓ-round lane fold of a `2^ℓ`-interleaved word adds a
/// row-union factor via App. C.3's Lemma `mca-commutes`; see
/// [`paper_johnson_log_a`].
fn paper_thm_ca_johnson_log_a(log_inv_rate: usize, eta: f64, log_msg_cols: usize) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let sqrt_rho = rho.sqrt();
    let gamma = 1.0 - sqrt_rho - eta;
    // m = ⌈√ρ/(2η)⌉ where η = 1−√ρ−γ, floored at 3.
    let m_param = ((sqrt_rho / (2.0 * eta)).ceil() as usize).max(3) as f64;
    let half = m_param + 0.5;
    let half5 = half.powi(5);
    let numerator = 2.0 * half5 + 3.0 * half * gamma * rho;
    let denominator = 3.0 * rho.powf(1.5);
    let n = ((log_msg_cols + log_inv_rate) as f64).exp2();
    let a = (numerator / denominator) * n + half / sqrt_rho;
    a.log2()
}

/// Johnson-regime proximity-gap `log₂ a` for a level, including the row-union
/// factor from our paper's Appendix C.3 (Lemma `mca-commutes`, "MCA commutes
/// with list decoding").
///
/// The base MCA error `ε = a_RLC/|F|` from [`paper_thm_ca_johnson_log_a`] is
/// stated for a two-row interleaved word (one fold step). Folding a
/// `2^ℓ`-interleaved word (ℓ = `log_num_interleaved`) over its ℓ lane-fold
/// rounds pays a row union: by the lemma, round `i` incurs `2^{ℓ-i}·ε`, so the
/// worst round (`i = 1`) pays the factor `2^{ℓ-1}` = (interleaving factor)/2.
/// We bind the per-level grinding to that worst round, returning
/// `log₂(2^{ℓ-1}·a_RLC) = log₂ a_RLC + (ℓ-1)`.
///
/// `ℓ ≤ 1` (`L ≤ 2`) means no row union; the `(ℓ-1)` penalty clamps to 0.
fn paper_johnson_log_a(
    log_inv_rate: usize,
    eta: f64,
    log_msg_cols: usize,
    log_num_interleaved: usize,
) -> f64 {
    let base = paper_thm_ca_johnson_log_a(log_inv_rate, eta, log_msg_cols);
    // Row-union factor 2^{ℓ-1} (worst round i=1 of the ℓ-round lane fold),
    // ℓ = log_num_interleaved. In bits: (ℓ-1), clamped ≥ 0.
    let row_union_penalty = (log_num_interleaved as f64 - 1.0).max(0.0);
    base + row_union_penalty
}

/// Per-query log₂(1/(1−γ)) under the Johnson regime: each query closes
/// `log_2(1/(1-γ))` bits of soundness against a γ-far adversary.
fn paper_per_query_bits(log_inv_rate: usize, eta: f64) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let gamma = 1.0 - rho.sqrt() - eta;
    (1.0 / (1.0 - gamma)).log2()
}

/// UDR proximity radius: the **maximum** allowed by our paper's App. C.3
/// (Theorem `ca-udr`, BCHKS25 Cor. 1.4), whose valid range is
/// `[δ/3, δ/2 − 3/(δ·n)]`. We take the top of the range,
///
///   `γ = δ/2 − 3/(δ·n) − ε*`,
///
/// where `δ = 1 − ρ` is the code's relative minimum distance,
/// `n = 2^(log_msg_cols + log_inv_rate)` the codeword length, and `ε*`
/// (`proximity_loss`) optional extra slack below the maximum (`0` in shipped
/// configs → exactly the maximal radius). The `3/(δ·n)` backoff is the
/// theorem-mandated minimum and shrinks with the codeword length.
fn udr_gamma(log_inv_rate: usize, log_msg_cols: usize, proximity_loss: f64) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let delta = 1.0 - rho;
    let n = ((log_msg_cols + log_inv_rate) as f64).exp2();
    delta / 2.0 - 3.0 / (delta * n) - proximity_loss
}

/// Per-query log₂(1/(1−γ)) under the UDR regime at the maximal radius
/// `γ = δ/2 − 3/(δ·n) − ε*` (see [`udr_gamma`]).
fn udr_per_query_bits(log_inv_rate: usize, log_msg_cols: usize, proximity_loss: f64) -> f64 {
    let gamma = udr_gamma(log_inv_rate, log_msg_cols, proximity_loss);
    (1.0 / (1.0 - gamma)).log2()
}

/// Asymptotic (n → ∞) UDR per-query soundness at `γ = δ/2`, dropping the
/// finite-length `3/(δ·n)` backoff. Length-agnostic; the per-level configs use
/// the n-aware [`udr_per_query_bits`]. Backs the test-only `udr_queries`
/// reference table — the dropped backoff slightly *under*-counts queries, but
/// the per-level block-length check in `derive_config` catches any shape that
/// wouldn't hold the real, n-aware query count.
#[cfg(test)]
fn udr_per_query_bits_asymptotic(log_inv_rate: usize) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let gamma = (1.0 - rho) / 2.0;
    (1.0 / (1.0 - gamma)).log2()
}

/// UDR proximity-gap exceptional set, per our paper's Appendix C.3
/// (Theorem `ca-udr`, adapted from BCHKS25 Corollary 1.4): at proximity
/// radius `γ` (here the maximal `γ = δ/2 − 3/(δ·n)`; see [`udr_gamma`]) the
/// exceptional set is
///
///   `a = γ·n + 1`,
///
/// where `n = 2^(log_msg_cols + log_inv_rate)` is the codeword length at this
/// level. The `log₂ a ≈ log₂(γ·n)` term therefore **grows with the codeword
/// length**, so larger witnesses give a smaller `eps_pg = 128 − log₂ a` and
/// need proportionally more `fold_grinding_bits` to hold a fixed target.
/// Callers add **no** row-union penalty in this regime: the unique-decoding
/// list has size 1, so (per Diamond and Gruen) MCA-commutes holds with error
/// ε directly, unlike the Johnson regime's `2^{ℓ-1}` factor. This replaced an
/// earlier length-independent `a ≤ 2/ε*` form, which did not match the paper's
/// stated bound.
fn paper_thm_1_4_log_a(log_inv_rate: usize, log_msg_cols: usize, proximity_loss: f64) -> f64 {
    let gamma = udr_gamma(log_inv_rate, log_msg_cols, proximity_loss);
    let n = ((log_msg_cols + log_inv_rate) as f64).exp2();
    (gamma * n + 1.0).log2()
}

/// Johnson-bound list size of the *interleaved* RS code at radius
/// `θ = 1 − √ρ − η`, in log₂. Independent of the interleaving factor.
///
/// Interleaving preserves relative distance — `V^{⊙m}` has the base code's
/// distance `δ = 1 − ρ` — and only enlarges the alphabet (to `q^m`). The
/// Johnson bound depends solely on (distance, radius, alphabet size), so the
/// interleaved list size at any radius *below* the Johnson radius `1 − √ρ`
/// is bounded by the very same single-code Johnson list size
///
///   `L_int ≤ L_base ≤ 1/(2·η·√ρ)`,
///
/// with no dependence on `m` and, crucially, no `L_base^r` blow-up.
///
/// The general GGR (Gopalan–Guruswami–Raghavendra, Thm 2.5) interleaved bound
/// `L_int ≤ C(b+r, r)·L_base^r` is only needed to push the list-decoding
/// radius *past* the Johnson bound toward `δ`. Ligerito deliberately sits at
/// `θ = 1 − √ρ − η`, strictly below the Johnson radius by slack `η > 0`, so
/// that regime never applies and the plain Johnson bound is both correct and
/// far tighter (it dominates GGR throughout the regime RS can reach).
fn johnson_interleaved_list_log2(log_inv_rate: usize, eta: f64) -> f64 {
    debug_assert!(
        eta > 0.0,
        "η must be > 0 to stay strictly below the Johnson radius"
    );
    let rho = (-(log_inv_rate as f64)).exp2();
    let sqrt_rho = rho.sqrt();
    let l_base = 1.0 / (2.0 * eta * sqrt_rho);
    l_base.log2()
}

/// OOD binding bits for a `JohnsonOod` level. `mu_vars` is the level's
/// multilinear variable count (`log_msg_cols + log_num_interleaved`).
///
/// - `ood_samples ≥ 1` (explicit samples): the bad event is two distinct
///   list elements agreeing on all `s` random points of `F^μ`
///   (Schwartz–Zippel, total degree ≤ μ), union over pairs:
///   `bits = s·(128 − log₂ μ) − (2·log₂ L_int − 1)`.
/// - `ood_samples = 0` (L0's implicit binding): the opening's own evaluation
///   claim at a post-commit random point pins the prover to one claimed
///   value, so the union is over the list (not pairs):
///   `bits = 128 − log₂ L_int − log₂ μ`.
fn paper_ood_bits(log_inv_rate: usize, eta: f64, mu_vars: usize, ood_samples: usize) -> f64 {
    let log2_l = johnson_interleaved_list_log2(log_inv_rate, eta);
    let log2_mu = (mu_vars as f64).log2();
    if ood_samples == 0 {
        ANALYSIS_LOG_Q - log2_l - log2_mu
    } else {
        ood_samples as f64 * (ANALYSIS_LOG_Q - log2_mu) - (2.0 * log2_l - 1.0)
    }
}

/// Absolute ceiling on any per-level grinding (fold or OOD). The per-round
/// Johnson fold-grind budgets ([`max_fold_grind`]) sit at or below this; it also
/// bounds the OOD grind and backs the `validate` sanity assert.
pub const MAX_FOLD_GRINDING_BITS: usize = 24;

/// Per-round fold-challenge PoW budget for a Johnson (round 3+) level. Johnson
/// buys a bigger proximity radius — hence fewer queries — but its
/// length-dependent proximity-gap term must be ground back to target, and that
/// grinding is real prover work (a PoW before every fold challenge).
///
/// This budget is the pivotal proof-size lever: the deep-level rate search
/// ([`level_log_inv_rate`]) takes the *lowest* rate whose grind fits here, and
/// lower rate ⇒ far fewer queries. Because the proximity-gap set grows like
/// `2^(cols + 2.5·log_inv_rate)`, one bit of budget at a wide level is worth a
/// large rate step: at round 3 (cols≈15) a 24-bit budget affords rate 1/4
/// (~130 queries) while 22 bits forces rate 1/2 (~370 queries). We therefore
/// spend the full [`MAX_FOLD_GRINDING_BITS`] on every Johnson level — that is
/// what buys the small proof.
fn max_fold_grind(_level_idx: usize) -> usize {
    MAX_FOLD_GRINDING_BITS
}

/// Best Johnson (list-decoding + OOD) analysis for one recursive level: the
/// slack `η` minimizing the query count whose fold-grinding stays within
/// `grind_cap` and whose OOD term clears `target_bits`. Returns `None` when no
/// `η` fits (the caller then keeps the level's UDR analysis). Level 0 is never
/// a Johnson candidate: it carries no OOD sample (bound by the opening's own
/// evaluation claim), and UDR is both cheaper and list-size-1 there.
struct JohnsonCandidate {
    eta: f64,
    queries: usize,
    ood_samples: usize,
    fold_grinding_bits: usize,
    ood_grinding_bits: usize,
    eps_pg: f64,
    eps_query: f64,
    eps_ood: f64,
}

fn best_johnson_candidate(
    level_idx: usize,
    log_inv_rate: usize,
    log_msg_cols: usize,
    log_num_interleaved: usize,
    target_bits: usize,
    query_grind: usize,
    grind_cap: usize,
) -> Option<JohnsonCandidate> {
    if level_idx == 0 {
        return None;
    }
    let target = target_bits as f64;
    let query_target = target_bits.saturating_sub(query_grind).max(1) as f64;
    let mu = log_msg_cols + log_num_interleaved;
    let block_len = 1usize << (log_msg_cols + log_inv_rate);
    let sqrt_rho = (-(log_inv_rate as f64)).exp2().sqrt();
    let max_eta = 1.0 - sqrt_rho;
    let mut best: Option<JohnsonCandidate> = None;

    // Sweep the Johnson slack η over (η_knee, 1−√ρ). The proximity-gap set is
    //   a ∝ (m+½)^5,   m = ⌈√ρ/(2η)⌉ (floored at 3),
    // so shrinking η below the point where `m` bottoms out at 3 (η_knee = √ρ/6)
    // buys only a few fewer queries while exploding `a` — hence the fold grind.
    // We therefore floor the sweep at the knee: there, `m = 3` and the grind is
    // at its plateau minimum, and (since queries fall with radius) min-queries
    // lands right at the knee. Above the knee the list L = 1/(2η√ρ) is small and
    // one OOD sample (grinding its challenge by target − eps_ood) binds it. A
    // fine grid suffices — the terms are smooth in η.
    let eta_knee = sqrt_rho / 6.0;
    const STEPS: usize = 4000;
    for k in 1..STEPS {
        let eta = max_eta * (k as f64) / (STEPS as f64);
        if eta < eta_knee || eta >= max_eta {
            continue;
        }
        let eps_pg =
            ANALYSIS_LOG_Q - paper_johnson_log_a(log_inv_rate, eta, log_msg_cols, log_num_interleaved);
        let fold_grinding_bits = (target - eps_pg).ceil().max(0.0) as usize;
        if fold_grinding_bits > grind_cap {
            continue;
        }
        // One OOD sample; grind the OOD challenge by (target − eps_ood) bits to
        // bind the (possibly large) Johnson list to a single codeword.
        let eps_ood = paper_ood_bits(log_inv_rate, eta, mu, 1);
        let ood_grinding_bits = (target - eps_ood).ceil().max(0.0) as usize;
        if ood_grinding_bits > grind_cap {
            continue;
        }
        let per_q = paper_per_query_bits(log_inv_rate, eta);
        if !per_q.is_finite() || per_q <= 0.0 {
            continue;
        }
        let queries = (query_target / per_q).ceil() as usize;
        if queries > block_len {
            continue;
        }
        let cand = JohnsonCandidate {
            eta,
            queries,
            ood_samples: 1,
            fold_grinding_bits,
            ood_grinding_bits,
            eps_pg,
            eps_query: queries as f64 * per_q,
            eps_ood,
        };
        if best.as_ref().is_none_or(|b| cand.queries < b.queries) {
            best = Some(cand);
        }
    }
    best
}

impl LigeritoLevelConfig {
    /// Compute the proximity-gap and per-query soundness bits this level is
    /// expected to deliver under its declared regime. Returns
    /// `(eps_pg_bits, eps_query_bits)` where:
    ///   eps_pg_bits   = log₂(q/a) under the regime's threshold-a formula
    ///   eps_query_bits = Q · log₂(1/(1−γ))
    ///
    /// Used by [`LigeritoSecurityConfig::validate`] to assert the declared
    /// `expected_*_bits` diagnostics are consistent with the regime's
    /// canonical formulas (i.e., the config is compatible with the paper).
    pub fn paper_predicted_bits(&self) -> (f64, f64) {
        match self.regime {
            SoundnessRegime::JohnsonOod => {
                let eta = self.eta.expect("JohnsonOod must have eta");
                // App. C.3 Lemma `mca-commutes`: the ℓ-round lane fold of a
                // 2^ℓ-interleaved word (ℓ = log_num_interleaved) pays a
                // row-union factor 2^{ℓ-i} at round i; the worst round (i=1)
                // gives 2^{ℓ-1}, on top of the base ca-johnson MCA error.
                let log_a = paper_johnson_log_a(
                    self.log_inv_rate,
                    eta,
                    self.log_msg_cols,
                    self.log_num_interleaved,
                );
                let eps_pg = ANALYSIS_LOG_Q - log_a;
                // Per-query soundness WITHOUT a list union bound — the OOD
                // binding (see `paper_ood_bits`) pins the prover to a single
                // codeword of the interleaved list before queries are drawn.
                let per_q = paper_per_query_bits(self.log_inv_rate, eta);
                let eps_query = self.queries as f64 * per_q;
                (eps_pg, eps_query)
            }
            SoundnessRegime::Udr => {
                // App. C.3 Thm `ca-udr` (BCHKS25 Cor. 1.4): a = γ·n + 1 for
                // radius γ = δ/2 (ε* = 0, no backoff).
                let proximity_loss = self
                    .proximity_loss
                    .expect("Udr regime must carry proximity_loss");
                // No row-union penalty in the unique-decoding regime: the list
                // has size 1, so (per Diamond and Gruen) the MCA-commutes step
                // holds with error ε directly — the Johnson regime's 2^{ℓ-1}
                // row union is unnecessary. So eps_pg = 128 − log₂ a.
                let log_a =
                    paper_thm_1_4_log_a(self.log_inv_rate, self.log_msg_cols, proximity_loss);
                let eps_pg = ANALYSIS_LOG_Q - log_a;
                let per_q =
                    udr_per_query_bits(self.log_inv_rate, self.log_msg_cols, proximity_loss);
                let eps_query = self.queries as f64 * per_q;
                (eps_pg, eps_query)
            }
        }
    }

    /// OOD binding bits this level is expected to deliver (`JohnsonOod`
    /// only; `None` for `Udr`, where the unique-decoding list has size 1 and
    /// no binding step exists). See [`paper_ood_bits`].
    pub fn paper_predicted_ood_bits(&self) -> Option<f64> {
        match self.regime {
            SoundnessRegime::JohnsonOod => {
                let eta = self.eta.expect("JohnsonOod must have eta");
                let mu = self.log_msg_cols + self.log_num_interleaved;
                Some(paper_ood_bits(self.log_inv_rate, eta, mu, self.ood_samples))
            }
            SoundnessRegime::Udr => None,
        }
    }
}

impl LigeritoSecurityConfig {
    /// Validate that the config is internally consistent and matches the
    /// declared analysis. Returns the first violation found, if any.
    pub fn validate(&self) -> Result<(), String> {
        if self.log_n + crate::LOG_PACKING != self.m {
            return Err(format!(
                "log_n ({}) + LOG_PACKING ({}) != m ({})",
                self.log_n, crate::LOG_PACKING, self.m
            ));
        }

        // Level shape: initial_k + Σ k (L1+) + yr_log_n = log_n.
        let levels_level_k_sum: usize = self.levels.iter().skip(1).map(|lv| lv.k).sum();
        let yr_log_n = self.final_block.yr_log_n;
        if self.initial_k + levels_level_k_sum + yr_log_n != self.log_n {
            return Err(format!(
                "shape mismatch: initial_k ({}) + Σ k ({}) + yr_log_n ({}) = {} ≠ log_n ({})",
                self.initial_k,
                levels_level_k_sum,
                yr_log_n,
                self.initial_k + levels_level_k_sum + yr_log_n,
                self.log_n,
            ));
        }

        // L0 must have k = initial_k and log_num_interleaved = initial_k.
        let l0 = self
            .levels
            .first()
            .ok_or_else(|| "empty levels".to_string())?;
        if l0.k != self.initial_k {
            return Err(format!(
                "L0.k ({}) must equal initial_k ({})",
                l0.k, self.initial_k
            ));
        }
        if l0.log_num_interleaved != self.initial_k {
            return Err(format!(
                "L0.log_num_interleaved ({}) must equal initial_k ({})",
                l0.log_num_interleaved, self.initial_k
            ));
        }

        // Per-level checks.
        let mut dim_in = self.log_n;
        for (i, lv) in self.levels.iter().enumerate() {
            // Shape: log_msg_cols + log_num_interleaved = dim_in.
            if lv.log_msg_cols + lv.log_num_interleaved != dim_in {
                return Err(format!(
                    "L{i}: log_msg_cols ({}) + log_num_interleaved ({}) ≠ input dim ({dim_in})",
                    lv.log_msg_cols, lv.log_num_interleaved
                ));
            }

            // eta presence matches regime.
            match (lv.regime, lv.eta) {
                (SoundnessRegime::Udr, Some(_)) => {
                    return Err(format!("L{i}: regime=udr but eta is set"));
                }
                (SoundnessRegime::JohnsonOod, None) => {
                    return Err(format!("L{i}: regime requires eta but eta is None"));
                }
                _ => {}
            }

            // proximity_loss presence matches regime (UDR-only).
            match (lv.regime, lv.proximity_loss) {
                (SoundnessRegime::Udr, None) => {
                    return Err(format!("L{i}: regime=udr but proximity_loss is missing"));
                }
                (SoundnessRegime::Udr, Some(eps)) if eps < 0.0 => {
                    return Err(format!("L{i}: proximity_loss must be ≥ 0, got {eps}"));
                }
                (SoundnessRegime::JohnsonOod, Some(_)) => {
                    return Err(format!("L{i}: proximity_loss is only valid for regime=udr"));
                }
                _ => {}
            }

            // OOD samples match regime: UDR has no list, so no OOD; under
            // JohnsonOod every level past L0 needs explicit samples, while
            // L0 is bound by the opening's own post-commit evaluation claim.
            match lv.regime {
                SoundnessRegime::Udr if lv.ood_samples != 0 => {
                    return Err(format!(
                        "L{i}: regime=udr but ood_samples={} (unique decoding \
                         has list size 1 — no OOD binding step exists)",
                        lv.ood_samples
                    ));
                }
                SoundnessRegime::JohnsonOod if i == 0 && lv.ood_samples != 0 => {
                    return Err(format!(
                        "L0: ood_samples={} but L0 is bound by the opening's \
                         own evaluation claim (must be 0)",
                        lv.ood_samples
                    ));
                }
                SoundnessRegime::JohnsonOod if i > 0 && lv.ood_samples == 0 => {
                    return Err(format!(
                        "L{i}: regime=johnson_ood requires ood_samples ≥ 1 \
                         past L0 (the query counts assume single-codeword \
                         binding)"
                    ));
                }
                _ => {}
            }

            // OOD diagnostic matches regime + formula.
            match (lv.regime, lv.expected_eps_ood_bits) {
                (SoundnessRegime::Udr, Some(_)) => {
                    return Err(format!("L{i}: regime=udr but expected_eps_ood_bits is set"));
                }
                (SoundnessRegime::JohnsonOod, None) => {
                    return Err(format!(
                        "L{i}: regime=johnson_ood requires expected_eps_ood_bits"
                    ));
                }
                (SoundnessRegime::JohnsonOod, Some(declared)) => {
                    let pred = lv
                        .paper_predicted_ood_bits()
                        .expect("JohnsonOod has an OOD prediction");
                    if (declared - pred).abs() > PAPER_COMPAT_TOL_BITS {
                        return Err(format!(
                            "L{i}: expected_eps_ood_bits ({declared:.2}) doesn't \
                             match prediction ({pred:.2}); tolerance ±{:.2} bits.",
                            PAPER_COMPAT_TOL_BITS
                        ));
                    }
                }
                _ => {}
            }

            // Paper-compatibility: the declared expected_*_bits must agree
            // with what the regime's formula predicts (within tolerance).
            // Asserts the config was actually derived from the paper, not
            // hand-waved into compliance.
            let (pg_pred, q_pred) = lv.paper_predicted_bits();
            if (lv.expected_eps_pg_bits - pg_pred).abs() > PAPER_COMPAT_TOL_BITS {
                return Err(format!(
                    "L{i}: expected_eps_pg_bits ({:.2}) doesn't match \
                     {analysis} prediction ({:.2}); tolerance ±{:.2} bits. \
                     Re-derive Q, eta, or grinding so the declared diagnostic \
                     matches the formula.",
                    lv.expected_eps_pg_bits,
                    pg_pred,
                    PAPER_COMPAT_TOL_BITS,
                    analysis = self.analysis_version,
                ));
            }
            if (lv.expected_eps_query_bits - q_pred).abs() > PAPER_COMPAT_TOL_BITS {
                return Err(format!(
                    "L{i}: expected_eps_query_bits ({:.2}) doesn't match \
                     {analysis} prediction ({:.2}); tolerance ±{:.2} bits.",
                    lv.expected_eps_query_bits,
                    q_pred,
                    PAPER_COMPAT_TOL_BITS,
                    analysis = self.analysis_version,
                ));
            }

            // Security: queries cover the gap left by grinding.
            if lv.target_security_bits > lv.grinding_bits
                && lv.expected_eps_query_bits + 1e-3
                    < (lv.target_security_bits - lv.grinding_bits) as f64
            {
                return Err(format!(
                    "L{i}: expected_eps_query_bits ({:.2}) < target ({}) - grinding ({}) = {}",
                    lv.expected_eps_query_bits,
                    lv.target_security_bits,
                    lv.grinding_bits,
                    lv.target_security_bits - lv.grinding_bits
                ));
            }

            // Per-application proximity gap + fold-challenge grinding must
            // reach target. (The pg bad event lives on the fold challenges,
            // so only the fold grind — done before each fold challenge —
            // boosts it; the query-phase grind does not.)
            if lv.expected_eps_pg_bits + lv.fold_grinding_bits as f64 + 1e-3
                < lv.target_security_bits as f64
            {
                return Err(format!(
                    "L{i}: expected_eps_pg_bits ({:.2}) + fold_grinding ({}) < target ({})",
                    lv.expected_eps_pg_bits, lv.fold_grinding_bits, lv.target_security_bits
                ));
            }

            // OOD binding, boosted by the OOD-challenge grind, must reach
            // target: `eps_ood + ood_grinding_bits ≥ target`. The grind lets a
            // single OOD sample bind a large Johnson list (each PoW bit adds one
            // bit of binding soundness, as on the fold and query challenges).
            if let Some(ood) = lv.expected_eps_ood_bits
                && ood + lv.ood_grinding_bits as f64 + 1e-3 < lv.target_security_bits as f64
            {
                return Err(format!(
                    "L{i}: expected_eps_ood_bits ({ood:.2}) + ood_grinding ({}) < target ({})",
                    lv.ood_grinding_bits, lv.target_security_bits
                ));
            }

            if lv.target_security_bits < self.target_security_bits {
                return Err(format!(
                    "L{i}: target_security_bits ({}) < global target ({})",
                    lv.target_security_bits, self.target_security_bits
                ));
            }

            // Advance dim_in for next level: subtract k (the folds at this level).
            dim_in -= lv.k;
        }

        if dim_in != yr_log_n {
            return Err(format!(
                "after consuming all levels, dim_in ({dim_in}) ≠ yr_log_n ({yr_log_n})"
            ));
        }

        // Round-by-round soundness: each error term at each round is checked
        // against `target_security_bits` in the per-level loop above. Total
        // security is the minimum over rounds (the Fiat-Shamir-relevant notion;
        // cf. Ethereum's `soundcalc`), so there is intentionally no
        // whole-protocol union bound summed across terms.
        Ok(())
    }

    /// Derive THE security config at witness size `m`: a UDR/LDR hybrid targeting
    /// [`SECURITY_BITS`] bits per round under **round-by-round soundness** — every
    /// error term (pg + fold grinding, query + query grinding, and the OOD bind on
    /// Johnson levels) clears the target individually, and the protocol's security
    /// is the *minimum* over rounds — the notion that governs Fiat-Shamir security
    /// (cf. Ethereum's `soundcalc`), not a whole-protocol union bound over terms.
    ///
    /// The shipped schedule (see [`level_log_inv_rate`]): rounds 1–2 (L0 at 1/2,
    /// L1 at 1/16) are unique-decoding proximity rounds; from round 3 on, Johnson
    /// list-decoding (one OOD sample bound by an OOD-challenge grind) takes the
    /// *lowest* rate whose fold grind fits [`max_fold_grind`] — so the wide early
    /// Johnson levels sit at a moderate rate and the deep levels descend to very
    /// low rates (1/64, 1/128 …) where the near-maximal radius needs a handful of
    /// queries. The prover and both verifiers execute both regimes.
    pub fn derive_config(m: usize) -> Result<Self, String> {
        let target_bits = SECURITY_BITS;
        let log_inv_rate = LOG_INV_RATE_0;
        // Query-phase grinding trades prover PoW for query count (see
        // [`QUERY_GRINDING_BITS`]): 120-bit rounds with 18 bits ground, so
        // queries cover 102.
        let query_grind: usize = QUERY_GRINDING_BITS;
        let log_n = m
            .checked_sub(crate::LOG_PACKING)
            .ok_or_else(|| format!("m ({m}) < LOG_PACKING ({})", crate::LOG_PACKING))?;
        let initial_k = INITIAL_FOLDING_FATOR;

        // The fold structure (columns per level) is rate-independent, so derive
        // it with a placeholder rate, then assign each level's shipped rate from
        // its column count via `level_log_inv_rate` (L0 = LOG_INV_RATE_0, L1 =
        // ROUND2, L2+ = the lowest Johnson-feasible rate for that width).
        let mut shape = derive_ladder_shape(log_n, initial_k, |_| log_inv_rate)?;
        for i in 0..shape.log_inv_rates.len() {
            let cols = shape.log_msg_cols[i];
            let ilv = shape.log_num_interleaved[i];
            shape.log_inv_rates[i] = level_log_inv_rate(i, cols, ilv, target_bits, query_grind)
                .ok_or_else(|| {
                    format!(
                        "L{i}: no Johnson-feasible rate within {}-bit fold \
                         grind cap (cols={cols}); the round-3+ list-decoding tail cannot be placed.",
                        max_fold_grind(i)
                    )
                })?;
        }
        let n_levels = shape.log_inv_rates.len();

        // Round-by-round target: every error term (pg, query, ood) at every
        // round must individually clear `target_bits`. Round-by-round soundness
        // — the notion that governs the Fiat-Shamir security of the IOP — is the
        // *minimum* security level over rounds, not the sum, so there is
        // deliberately NO `log₂(#terms)` union-bound headroom. This matches the
        // convention Ethereum's `soundcalc` uses for hash-based zkEVM IOPs
        // (total security = min over rounds). It also keeps the proximity-gap
        // fold grinding (especially L0's, the dominant prover cost) at the
        // round-by-round minimum rather than paying ~4 bits of union slack that
        // buys nothing.
        let t = target_bits as f64;

        let mut levels = Vec::with_capacity(n_levels);
        for i in 0..n_levels {
            let rate = shape.log_inv_rates[i];
            let cols = shape.log_msg_cols[i];
            let ilv = shape.log_num_interleaved[i];
            // UDR candidate: list size 1 (no OOD, no `2^{ℓ-1}` row union),
            // cheapest fold-grinding, but a modest radius (`γ = δ/2`).
            let udr_per_q = udr_per_query_bits(rate, cols, UDR_PROXIMITY_LOSS);
            let udr_queries = ((t - query_grind as f64).max(1.0) / udr_per_q).ceil() as usize;
            let udr_eps_pg = ANALYSIS_LOG_Q - paper_thm_1_4_log_a(rate, cols, UDR_PROXIMITY_LOSS);
            let udr_fold_grind = (t - udr_eps_pg).ceil().max(0.0) as usize;

            // The regime is fixed by round (see `level_is_johnson`): UDR for
            // rounds 1–2, Johnson from round 3. Johnson's far larger radius
            // (`γ = 1 − √ρ − η`, near-maximal at the deep levels' low rate) cuts
            // the query count; its length-dependent fold grind must fit
            // `MAX_FOLD_GRINDING_BITS`, else the schedule is infeasible here.
            let john = if level_is_johnson(i) {
                best_johnson_candidate(i, rate, cols, ilv, target_bits, query_grind, max_fold_grind(i))
            } else {
                None
            };
            let use_john = level_is_johnson(i)
                && john.as_ref().is_some_and(|j| j.queries <= (1usize << (cols + rate)));
            if level_is_johnson(i) && !use_john {
                return Err(format!(
                    "L{i}: Johnson infeasible at rate 1/2^{rate} (cols={cols}): no η within \
                     {}-bit fold grind holds a block-fitting query count.",
                    max_fold_grind(i)
                ));
            }

            let (
                regime,
                eta,
                proximity_loss,
                queries,
                ood_samples,
                fold_grinding_bits,
                ood_grinding_bits,
                eps_pg,
                eps_query,
                eps_ood,
            ) = if use_john {
                let j = john.unwrap();
                (
                    SoundnessRegime::JohnsonOod,
                    Some(j.eta),
                    None,
                    j.queries,
                    j.ood_samples,
                    j.fold_grinding_bits,
                    j.ood_grinding_bits,
                    j.eps_pg,
                    j.eps_query,
                    Some(j.eps_ood),
                )
            } else {
                if udr_queries > (1usize << (cols + rate)) {
                    return Err(format!(
                        "L{i}: {udr_queries} queries exceed block length 2^{}",
                        cols + rate
                    ));
                }
                (
                    SoundnessRegime::Udr,
                    None,
                    Some(UDR_PROXIMITY_LOSS),
                    udr_queries,
                    0usize,
                    udr_fold_grind,
                    0usize,
                    udr_eps_pg,
                    udr_queries as f64 * udr_per_q,
                    None,
                )
            };

            levels.push(LigeritoLevelConfig {
                log_inv_rate: rate,
                log_msg_cols: cols,
                log_num_interleaved: ilv,
                k: shape.k_levels[i],
                regime,
                eta,
                proximity_loss,
                queries,
                grinding_bits: query_grind,
                fold_grinding_bits,
                ood_samples,
                ood_grinding_bits,
                target_security_bits: target_bits,
                expected_eps_pg_bits: round1(eps_pg),
                expected_eps_query_bits: round1(eps_query),
                expected_eps_ood_bits: eps_ood.map(round1),
            });
        }

        let analysis_version = "no_row_union_over_ben_sasson_2025_cor_1_4";
        let cfg = Self {
            m,
            log_n,
            initial_k,
            target_security_bits: target_bits,
            analysis_version: analysis_version.into(),
            field: "f128".into(),
            hash: "sha256".into(),
            grinding_step: GrindingStep::PostCommitPreQueries,
            levels,
            final_block: FinalBlockConfig {
                yr_log_n: shape.yr_log_n,
            },
        };
        cfg.validate()?;
        Ok(cfg)
    }

    /// Build a `(ProverConfig, VerifierConfig)` pair from this security config.
    /// Drops the security-only fields (eta, queries, grinding, expected_*) but
    /// preserves the level shape so the existing prover/verifier code path
    /// works unchanged.
    pub fn to_prover_verifier_configs(&self) -> Result<(ProverConfig, VerifierConfig), String> {
        self.validate()?;
        let log_inv_rates: Vec<usize> = self.levels.iter().map(|lv| lv.log_inv_rate).collect();
        let level_ks: Vec<usize> = self
            .levels
            .iter()
            .skip(1)
            .map(|lv| lv.k)
            .collect();
        let level_log_msg_cols: Vec<usize> = self
            .levels
            .iter()
            .skip(1)
            .map(|lv| lv.log_msg_cols)
            .collect();
        let queries: Vec<usize> = self.levels.iter().map(|lv| lv.queries).collect();
        let grinding_bits: Vec<usize> = self.levels.iter().map(|lv| lv.grinding_bits).collect();
        let fold_grinding_bits: Vec<usize> =
            self.levels.iter().map(|lv| lv.fold_grinding_bits).collect();
        let ood_samples: Vec<usize> = self.levels.iter().map(|lv| lv.ood_samples).collect();
        let ood_grinding_bits: Vec<usize> =
            self.levels.iter().map(|lv| lv.ood_grinding_bits).collect();
        let prover = ProverConfig {
            log_inv_rates: log_inv_rates.clone(),
            level_steps: level_ks.len(),
            initial_log_msg_cols: self.levels[0].log_msg_cols,
            initial_log_num_interleaved: self.initial_k,
            initial_k: self.initial_k,
            level_log_msg_cols: level_log_msg_cols.clone(),
            level_ks: level_ks.clone(),
            queries: queries.clone(),
            grinding_bits: grinding_bits.clone(),
            fold_grinding_bits: fold_grinding_bits.clone(),
            ood_samples: ood_samples.clone(),
            ood_grinding_bits: ood_grinding_bits.clone(),
        };
        let verifier = VerifierConfig {
            log_inv_rates: log_inv_rates.clone(),
            level_steps: level_ks.len(),
            initial_log_msg_cols: self.levels[0].log_msg_cols,
            initial_log_num_interleaved: self.initial_k,
            initial_k: self.initial_k,
            level_log_msg_cols,
            level_ks,
            queries,
            grinding_bits,
            fold_grinding_bits,
            ood_samples,
            ood_grinding_bits,
        };
        Ok((prover, verifier))
    }
}

/// `ceil(log2(n))`, used to size per-query batching challenges.
#[inline]
pub fn log2_ceil(n: usize) -> usize {
    if n <= 1 { 0 } else { (n - 1).ilog2() as usize + 1 }
}

#[cfg(test)]
mod hybrid_tests {
    use super::*;

    fn print_schedule(tag: &str, cfg: &LigeritoSecurityConfig) -> (usize, usize) {
        eprintln!(
            "\n[{tag}] m={}: {} levels, target {} bits (field 2^{})",
            cfg.m,
            cfg.levels.len(),
            cfg.target_security_bits,
            ANALYSIS_LOG_Q as usize,
        );
        eprintln!(
            "  {:>2} {:>6} {:>5} {:>4} {:>10} {:>8} {:>8} {:>8}",
            "L", "rate", "cols", "ilv", "regime", "queries", "foldgrd", "eps_pg"
        );
        for (i, lv) in cfg.levels.iter().enumerate() {
            eprintln!(
                "  {:>2} 1/{:<4} {:>5} {:>4} {:>10?} {:>8} {:>8} {:>8?}",
                i,
                1usize << lv.log_inv_rate,
                lv.log_msg_cols,
                lv.log_num_interleaved,
                lv.regime,
                lv.queries,
                lv.fold_grinding_bits,
                lv.expected_eps_pg_bits,
            );
        }
        let total_q: usize = cfg.levels.iter().map(|l| l.queries).sum();
        let max_fg = cfg.levels.iter().map(|l| l.fold_grinding_bits).max().unwrap_or(0);
        eprintln!("  total queries {total_q}, max fold-grind {max_fg} bits");
        (total_q, max_fg)
    }

    /// The shipped UDR/LDR hybrid derives, validates at the target, and obeys
    /// the per-level invariants: UDR levels take 0 OOD samples, Johnson levels
    /// take exactly 1 (bound by an OOD grind), and no grind exceeds the cap.
    #[test]
    fn hybrid_config_is_sound_and_well_formed() {
        let cfg = LigeritoSecurityConfig::derive_config(26).expect("hybrid config derives");
        print_schedule("hybrid (shipped)", &cfg);

        assert_eq!(cfg.levels[0].ood_samples, 0, "L0 takes no OOD sample");
        for l in &cfg.levels {
            match l.regime {
                SoundnessRegime::Udr => {
                    assert_eq!(l.ood_samples, 0);
                    assert_eq!(l.ood_grinding_bits, 0);
                }
                SoundnessRegime::JohnsonOod => assert_eq!(l.ood_samples, 1),
            }
            assert!(l.fold_grinding_bits <= MAX_FOLD_GRINDING_BITS);
            assert!(l.ood_grinding_bits <= MAX_FOLD_GRINDING_BITS);
        }
    }
}
