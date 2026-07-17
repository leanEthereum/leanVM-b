// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Ported from bolt-rs (https://github.com/bcc-research/bolt-rs,
// `ligerito_recursive.rs`).

//! Field-independent configuration and soundness analysis for Ligerito.
//!
//! Source of truth: `misc/pcs.tex` ("A note on WHIR/Ligerito over binary
//! fields"), Theorem `thm:rbr`. Its per-verifier-message error table maps
//! onto the per-level checks in [`LigeritoSecurityConfig::validate`]:
//!
//! - batching challenges -> [`johnson_algebraic_bits`] (this implementation
//!   batches with an eq-vector challenge plus scalar glue challenges instead
//!   of the doc's powers of a single alpha; see that function),
//! - fold challenge `s_j` -> `2 L/|F| + 2^(l-j) eps`: the MCA part via
//!   [`paper_johnson_log_a`] (worst round `j = 1`), the `2 L/|F|` part
//!   under [`johnson_algebraic_bits`],
//! - OOD challenge -> [`paper_ood_bits`],
//! - query message -> `(1 - gamma)^t`, plus [`QUERY_GRINDING_BITS`].
//!
//! Round-by-round (RBR) soundness means every entry individually clears
//! [`SECURITY_BITS`]: the Fiat--Shamir error per random-oracle query is the
//! MAX of the entries, not their sum.
//!
use serde::{Deserialize, Serialize};

// ===================================================================
// Config
// ===================================================================

// The production Ligerito configuration: rate-1/2 Johnson list decoding with
// OOD binding and 128-bit round-by-round soundness over F192.

/// Round-by-round soundness target (bits): every verifier-challenge transition
/// must have conditional failure probability at most `2^-SECURITY_BITS`.
pub const SECURITY_BITS: usize = 128;

/// L0 code rate index: `rho_0 = 2^-LOG_INV_RATE_0` (rate 1/2).
pub const LOG_INV_RATE_0: usize = 1;

/// CLI-selectable L0 rates are `2^-r` for `r = 1, 2, 3, 4`.
pub const MIN_LOG_INV_RATE: usize = 1;
pub const MAX_LOG_INV_RATE: usize = 4;

/// Validate a production Ligerito inverse-rate logarithm.
pub fn validate_log_inv_rate(log_inv_rate: usize) -> Result<(), String> {
    if !(MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(format!(
            "log_inv_rate must be in {MIN_LOG_INV_RATE}..={MAX_LOG_INV_RATE}, got {log_inv_rate}"
        ));
    }
    Ok(())
}

/// Per-level query-phase proof-of-work budget. These bits are ground after the
/// level commitment and before its query positions are sampled, so the query
/// count only needs to close the remaining `SECURITY_BITS - 17` bits.
pub const QUERY_GRINDING_BITS: usize = 17;

/// Maximum BCHKS25 integer parameter considered by the per-level eta search.
/// Production configurations hit the proximity-gap boundary far below this;
/// the generous cap makes the optimizer deterministic even if sizes expand.
const JOHNSON_ETA_SEARCH_MAX_M: usize = 4096;

pub const INITIAL_FOLDING_FACTOR: usize = 6;
pub const SUBSEQUENT_FOLDING_FACTOR: usize = 3;

/// Logarithmic reduction of the total Reed--Solomon domain after the initial
/// fold. With the production six-variable initial fold, `3` changes the
/// inverse-rate logarithm by `6 - 3 = 3` at the first recursive level.
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;

/// After each subsequent fold, shrink the total Reed--Solomon domain by one
/// bit. This mirrors WHIR's recursive-domain schedule; unlike the initial
/// reduction, it is deliberately fixed rather than a tuning parameter.
const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;

const _: () = assert!(RS_DOMAIN_INITIAL_REDUCTION_FACTOR <= INITIAL_FOLDING_FACTOR);
const _: () = assert!(RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR <= SUBSEQUENT_FOLDING_FACTOR);

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

/// Shared shape derivation behind [`LigeritoSecurityConfig::derive_config`].
/// The total RS domain loses [`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`] bits after
/// the initial fold, then exactly one bit per subsequent fold. Consequently a
/// fold of `k` variables raises the inverse-rate logarithm by `k - reduction`.
fn derive_ladder_shape(
    log_n: usize,
    initial_k: usize,
    log_inv_rate: usize,
) -> Result<LadderShape, String> {
    if log_n <= initial_k {
        return Err("log_n must be > initial_k".into());
    }
    let mut shape = LadderShape {
        log_inv_rates: vec![log_inv_rate],
        log_msg_cols: vec![log_n - initial_k],
        log_num_interleaved: vec![initial_k],
        k_levels: vec![initial_k],
        yr_log_n: 0,
    };
    let mut n_running = log_n - initial_k;
    let mut rate_running = log_inv_rate;
    let mut fold_running = initial_k;
    let mut domain_reduction = RS_DOMAIN_INITIAL_REDUCTION_FACTOR;
    while n_running > RESIDUAL_MAX_LOG {
        let k = SUBSEQUENT_FOLDING_FACTOR.min(n_running);
        let log_msg_cols_next = n_running - k;
        let rate_increase = fold_running.checked_sub(domain_reduction).ok_or_else(|| {
            format!(
                "folding factor {fold_running} is smaller than RS domain reduction {domain_reduction}"
            )
        })?;
        let next_rate = rate_running + rate_increase;
        shape.log_inv_rates.push(next_rate);
        shape.log_msg_cols.push(log_msg_cols_next);
        shape.log_num_interleaved.push(k);
        shape.k_levels.push(k);
        n_running -= k;
        rate_running = next_rate;
        fold_running = k;
        domain_reduction = RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR;
    }
    if shape.k_levels.len() < 2 {
        return Err("log_n too small: needs at least 2 fold levels".into());
    }
    shape.yr_log_n = n_running;
    Ok(shape)
}

// ===================================================================
// Security configuration schema
// ===================================================================
//
// Auditable, per-level spec for a Ligerito instance: query count, grinding
// bits, slack-from-Johnson, and the proximity-gap analysis the parameters
// were derived under. Designed to be (de)serializable so it can live in a
// TOML/JSON file alongside the prover/verifier code.

/// Which proximity-gap analysis a level's parameters were derived under.
/// Single-variant by design: it self-documents the analysis in serialized
/// configs and rejects configs claiming an analysis this code cannot check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SoundnessRegime {
    /// Johnson radius with explicit slack `η` (γ = (1 − √ρ) − η) **with
    /// out-of-domain binding** (`misc/pcs.tex`, Thm `thm:rbr`). The MCA
    /// theorem (`thm:mca-johnson` = BCHKS25 Thm 4.6) gives the proximity-gap
    /// exceptional set `a = O_ρ(n / η^5)`; the level's `fold_grinding_bits`
    /// should be ≥ (target_bits − log₂(q/a)).
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
    /// Slack from the Johnson radius: γ = (1 − √ρ) − η.
    pub eta: f64,
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
    /// the transcript. Each binds the prover to a single codeword of the
    /// interleaved list via a multilinear evaluation claim.
    /// Must be 0 at L0 (bound by the opening's own post-commit evaluation
    /// claim) and ≥ 1 at deeper levels.
    #[serde(default)]
    pub ood_samples: usize,
    /// Security target this level guarantees, post-grinding.
    pub target_security_bits: usize,
    /// Diagnostic — `log₂(q/a)` under the chosen regime. The implementation
    /// should assert this matches the formula at startup, modulo rounding.
    pub expected_eps_pg_bits: f64,
    /// Diagnostic — `Q · log₂(1/(1−γ))`. Should be ≥
    /// `target_security_bits − grinding_bits`.
    pub expected_eps_query_bits: f64,
    /// Diagnostic — OOD binding bits:
    /// `s·(192 − log₂μ) − (2·log₂L − 1)` for explicit samples, or
    /// `192 − log₂L − log₂μ` for the implicit L0 binding, where `L` is the
    /// Johnson interleaved list size and `μ` the level's variable count.
    pub expected_eps_ood_bits: f64,
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
/// 4. `eta` is finite and inside the Johnson range for the level's rate.
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
    /// Round-by-round security target (bits): `validate()` asserts that every
    /// error term associated with a verifier challenge clears at least this
    /// much. This is an RBR target, not a claim that the sum of all interactive
    /// failure probabilities is bounded by `2^-target_security_bits`.
    pub target_security_bits: usize,
    /// Identifier of the proximity-gap analysis used. Self-documents which
    /// theorem the per-level parameters were derived from. Example:
    /// `"ben_sasson_2025_thm_4_6"`.
    pub analysis_version: String,
    /// Field of the protocol. Example: `"f192"`.
    pub field: String,
    /// Hash function used by Merkle + FS sponge. Example: `"blake3"`.
    pub hash: String,
    /// Where in the per-level FS transcript grinding is placed.
    pub grinding_step: GrindingStep,
    /// Per-level parameters, in order L0, L1, L2, ....
    pub levels: Vec<LigeritoLevelConfig>,
    /// Final residual block descriptor.
    pub final_block: FinalBlockConfig,
}

/// Extension-field size used for soundness analysis: `q = 2^192`.
const ANALYSIS_LOG_Q: f64 = 192.0;

/// BCHKS25 parameter `rho = k/n` for an RS code of dimension `k + 1`.
/// Our message has `2^log_msg_cols` coefficients (degree strictly below that
/// value), so `k = 2^log_msg_cols - 1`. This differs perceptibly from the
/// nominal code rate at the small recursive levels.
fn reduced_rate(log_inv_rate: usize, log_msg_cols: usize) -> f64 {
    let dimension = (log_msg_cols as f64).exp2();
    (dimension - 1.0) / ((log_msg_cols + log_inv_rate) as f64).exp2()
}

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
/// `misc/pcs.tex` Thm `thm:mca-johnson` = BCHKS25 Theorem 4.6 (list
/// correlated agreement). For a Reed–Solomon code of (slightly reduced) rate
/// `ρ`, codeword length `n`, and Johnson slack `η` (proximity radius
/// `γ = 1 − √ρ − η`), the MCA error is `a/|F|` with
///
///   `a = [2(m+½)^5 + 3(m+½)·γ·ρ] / (3·ρ^{3/2}) · n + (m+½)/√ρ`,
///
/// where `η = 1 − √ρ − γ` and `m = max(⌈√ρ/η⌉, 3)`. Returns `log₂ a`.
///
/// This is the per-fold-step MCA error, stated for a two-row interleaved word
/// (`C ∈ F^{2×n}`). The ℓ-round lane fold of a `2^ℓ`-interleaved word adds a
/// row-union factor via `pcs.tex` Lemma `lem:fold-list`; see
/// [`paper_johnson_log_a`].
fn paper_thm_ca_johnson_log_a(log_inv_rate: usize, eta: f64, log_msg_cols: usize) -> f64 {
    let rho = reduced_rate(log_inv_rate, log_msg_cols);
    let sqrt_rho = rho.sqrt();
    let gamma = 1.0 - sqrt_rho - eta;
    // BCHKS25 Thm 4.6: m = ⌈√ρ/(1−√ρ−γ)⌉ = ⌈√ρ/η⌉, floored at 3.
    let m_param = johnson_m_param(log_inv_rate, log_msg_cols, eta);
    let half = m_param + 0.5;
    let half5 = half.powi(5);
    let numerator = 2.0 * half5 + 3.0 * half * gamma * rho;
    let denominator = 3.0 * rho.powf(1.5);
    let n = ((log_msg_cols + log_inv_rate) as f64).exp2();
    let a = (numerator / denominator) * n + half / sqrt_rho;
    a.log2()
}

/// Integer parameter `m = max(⌈√ρ/η⌉, 3)` of BCHKS25 Thm 4.6 (list
/// correlated agreement), represented as `f64` for the bound. Beware: the
/// plain, non-list Thm 1.5 has the factor-two-smaller `⌈√ρ/(2η)⌉`, and
/// Flock's Thm 8 quotes Thm 4.6 with that non-list parameter; the list form
/// costs a factor 2 of slack (see the footnote in `pcs.tex`
/// Thm `thm:mca-johnson`).
fn johnson_m_param(log_inv_rate: usize, log_msg_cols: usize, eta: f64) -> f64 {
    let sqrt_rho = reduced_rate(log_inv_rate, log_msg_cols).sqrt();
    ((sqrt_rho / eta).ceil() as usize).max(3) as f64
}

/// Johnson-regime proximity-gap `log₂ a` for a level, including the row-union
/// factor from `pcs.tex` Lemma `lem:fold-list` ("Folding preserves lists").
///
/// The base MCA error `ε = a_RLC/|F|` from [`paper_thm_ca_johnson_log_a`] is
/// stated for a two-row interleaved word (one fold step). Folding a
/// `2^ℓ`-interleaved word (ℓ = `log_num_interleaved`) over its ℓ lane-fold
/// rounds pays a row union: `thm:rbr`'s fold row is `2L/|F| + 2^{ℓ-j}·ε` at
/// round `j`, so the worst round (`j = 1`) pays the factor `2^{ℓ-1}` =
/// (interleaving factor)/2 (the `2L/|F|` part is checked separately, under
/// [`johnson_algebraic_bits`]). We bind the per-level grinding to that worst
/// round, returning `log₂(2^{ℓ-1}·a_RLC) = log₂ a_RLC + (ℓ-1)`.
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
fn paper_per_query_bits(log_inv_rate: usize, log_msg_cols: usize, eta: f64) -> f64 {
    let rho = reduced_rate(log_inv_rate, log_msg_cols);
    let gamma = 1.0 - rho.sqrt() - eta;
    (1.0 / (1.0 - gamma)).log2()
}

/// Unique-decoding-regime per-query soundness at `γ = δ/2` (`δ = 1 − ρ`).
/// Test-support only, backing [`udr_queries`] and the ad-hoc
/// [`default_config`] shape used by small K PCS tests.
#[cfg(test)]
fn udr_per_query_bits_asymptotic(log_inv_rate: usize) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    let gamma = (1.0 - rho) / 2.0;
    (1.0 / (1.0 - gamma)).log2()
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
fn johnson_interleaved_list_log2(
    log_inv_rate: usize,
    log_msg_cols: usize,
    eta: f64,
) -> f64 {
    debug_assert!(
        eta > 0.0,
        "η must be > 0 to stay strictly below the Johnson radius"
    );
    let rho = reduced_rate(log_inv_rate, log_msg_cols);
    let sqrt_rho = rho.sqrt();
    let l_base = 1.0 / (2.0 * eta * sqrt_rho);
    l_base.log2()
}

/// Worst algebraic verifier-challenge transition in the production opening —
/// the implementation's counterpart of `thm:rbr`'s batch row (`(T−1)·L/|F|`
/// for powers-of-alpha batching) and of the `2L/|F|` part of its fold row.
/// This codebase batches differently from the doc: the per-level query
/// consistency claims are combined with a multilinear eq-vector challenge,
/// and each new claim (OOD, induced) is glued into the single running
/// sumcheck with a fresh scalar challenge. A degree-`d` identity test
/// unioned over a Johnson list of size `L` fails with probability at most
/// `dL/|F|`. The relevant degrees are:
///
/// - 191 for GF64-to-GF192 ring-switch batching (L0 only, but included at
///   every level so the bound also dominates the eq-vector batch entering
///   the NEXT level's list, whatever its query count);
/// - `ceil(log2(queries))` for the multilinear query-row batching; and
/// - 2 for quadratic sumcheck (glue challenges have degree 1).
fn johnson_algebraic_bits_for(
    log_inv_rate: usize,
    log_msg_cols: usize,
    eta: f64,
    queries: usize,
) -> f64 {
    let log2_l = johnson_interleaved_list_log2(log_inv_rate, log_msg_cols, eta);
    let degree = crate::ring_switch_k::RING_SWITCH_SOUNDNESS_DEGREE
        .max(log2_ceil(queries))
        .max(2);
    ANALYSIS_LOG_Q - (degree as f64).log2() - log2_l
}

fn johnson_algebraic_bits(level: &LigeritoLevelConfig) -> f64 {
    johnson_algebraic_bits_for(level.log_inv_rate, level.log_msg_cols, level.eta, level.queries)
}

/// OOD binding bits for a level. `mu_vars` is the level's multilinear
/// variable count (`log_msg_cols + log_num_interleaved`).
///
/// - `ood_samples ≥ 1` (explicit samples): `pcs.tex` Lemma `lem:ood` /
///   `thm:rbr`'s OOD row `binom(L,2)·μ/|F|`, generalized to `s` samples: the
///   bad event is two distinct list elements agreeing on all `s` random
///   points of `F^μ` (Schwartz–Zippel, total degree ≤ μ), union over pairs:
///   `bits = s·(192 − log₂ μ) − (2·log₂ L_int − 1)`.
/// - `ood_samples = 0` (L0): the protocol takes no OOD sample at commitment,
///   so the PCS itself is only list binding (`pcs.tex`, abstract). What this
///   term materializes is the OUTER protocol's binding: the opening's own
///   evaluation claim sits at a post-commit random point, so at most one
///   list member matches it except with `L·μ/|F|` (union over the list, not
///   pairs): `bits = 192 − log₂ L_int − log₂ μ`.
fn paper_ood_bits(
    log_inv_rate: usize,
    log_msg_cols: usize,
    eta: f64,
    mu_vars: usize,
    ood_samples: usize,
) -> f64 {
    let log2_l = johnson_interleaved_list_log2(log_inv_rate, log_msg_cols, eta);
    let log2_mu = (mu_vars as f64).log2();
    if ood_samples == 0 {
        ANALYSIS_LOG_Q - log2_l - log2_mu
    } else {
        ood_samples as f64 * (ANALYSIS_LOG_Q - log2_mu) - (2.0 * log2_l - 1.0)
    }
}

/// Result of the WHIR-style per-level Johnson-slack search. The search
/// minimizes queries; ties keep the smallest theorem parameter `m`, which has
/// the largest eta and therefore the smallest list bound.
struct OptimizedJohnsonLevel {
    eta: f64,
    queries: usize,
    ood_samples: usize,
    eps_pg: f64,
    eps_query: f64,
    eps_ood: f64,
}

/// Eta at the lower boundary for a fixed BCHKS25 theorem parameter
/// `m = ceil(sqrt(rho) / eta)`. Moving eta lower would increase `m` and worsen
/// the proximity-gap bound; this boundary maximizes query soundness for the
/// given `m`. Step upward by an ulp if floating-point division lands just
/// below the intended ceil boundary.
fn johnson_eta_for_m(log_inv_rate: usize, log_msg_cols: usize, m: usize) -> f64 {
    debug_assert!(m >= 3);
    let sqrt_rho = reduced_rate(log_inv_rate, log_msg_cols).sqrt();
    let mut eta = sqrt_rho / m as f64;
    while johnson_m_param(log_inv_rate, log_msg_cols, eta) > m as f64 {
        eta = f64::from_bits(eta.to_bits() + 1);
    }
    debug_assert_eq!(johnson_m_param(log_inv_rate, log_msg_cols, eta), m as f64);
    eta
}

/// Choose eta independently for one recursive level, following leanVM's
/// discrete `m` search but using this implementation's exact reduced rate and
/// corrected BCHKS25 parameter. Candidates must satisfy every non-grindable
/// 128-bit term and the proximity-gap target without fold grinding.
fn optimize_johnson_level(
    level: usize,
    log_inv_rate: usize,
    log_msg_cols: usize,
    log_num_interleaved: usize,
    target_bits: usize,
    query_grinding_bits: usize,
) -> Result<OptimizedJohnsonLevel, String> {
    let target = target_bits as f64;
    let query_target = target_bits.saturating_sub(query_grinding_bits).max(1) as f64;
    let mu = log_msg_cols + log_num_interleaved;
    let block_len = 1usize << (log_msg_cols + log_inv_rate);
    let mut best: Option<OptimizedJohnsonLevel> = None;

    for m in 3..=JOHNSON_ETA_SEARCH_MAX_M {
        let eta = johnson_eta_for_m(log_inv_rate, log_msg_cols, m);
        let max_eta = 1.0 - reduced_rate(log_inv_rate, log_msg_cols).sqrt();
        if eta >= max_eta {
            continue;
        }

        let eps_pg = ANALYSIS_LOG_Q
            - paper_johnson_log_a(log_inv_rate, eta, log_msg_cols, log_num_interleaved);
        // At the theorem-parameter boundaries a grows monotonically with m;
        // no later candidate can recover once the proximity-gap target fails.
        if eps_pg + 1e-12 < target {
            break;
        }

        let per_q = paper_per_query_bits(log_inv_rate, log_msg_cols, eta);
        if !per_q.is_finite() || per_q <= 0.0 {
            continue;
        }
        let queries = (query_target / per_q).ceil() as usize;
        if queries > block_len {
            continue;
        }
        let eps_query = queries as f64 * per_q;

        let ood_samples = if level == 0 {
            0
        } else {
            match (1..=8usize).find(|&s| {
                paper_ood_bits(log_inv_rate, log_msg_cols, eta, mu, s) + 1e-12 >= target
            }) {
                Some(samples) => samples,
                None => continue,
            }
        };
        let eps_ood = paper_ood_bits(log_inv_rate, log_msg_cols, eta, mu, ood_samples);
        if eps_ood + 1e-12 < target
            || johnson_algebraic_bits_for(log_inv_rate, log_msg_cols, eta, queries) + 1e-12 < target
        {
            continue;
        }

        let candidate = OptimizedJohnsonLevel {
            eta,
            queries,
            ood_samples,
            eps_pg,
            eps_query,
            eps_ood,
        };
        if best.as_ref().is_none_or(|current| candidate.queries < current.queries) {
            best = Some(candidate);
        }
    }

    best.ok_or_else(|| {
        format!(
            "L{level}: no eta candidate satisfies {target_bits}-bit Johnson/OOD soundness at rate 1/2^{log_inv_rate}"
        )
    })
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
        // Fold row of `thm:rbr`, MCA part: the ℓ-round fold of a
        // 2^ℓ-interleaved word (ℓ = log_num_interleaved) pays a row-union
        // factor 2^{ℓ-j} at round j (`lem:fold-list`); the worst round (j=1)
        // gives 2^{ℓ-1}, on top of the base Thm 4.6 MCA error.
        let log_a = paper_johnson_log_a(
            self.log_inv_rate,
            self.eta,
            self.log_msg_cols,
            self.log_num_interleaved,
        );
        let eps_pg = ANALYSIS_LOG_Q - log_a;
        // Per-query soundness WITHOUT a list union bound — the OOD
        // binding (see `paper_ood_bits`) pins the prover to a single
        // codeword of the interleaved list before queries are drawn.
        let per_q = paper_per_query_bits(self.log_inv_rate, self.log_msg_cols, self.eta);
        let eps_query = self.queries as f64 * per_q;
        (eps_pg, eps_query)
    }

    /// OOD binding bits this level is expected to deliver.
    /// See [`paper_ood_bits`].
    pub fn paper_predicted_ood_bits(&self) -> f64 {
        let mu = self.log_msg_cols + self.log_num_interleaved;
        paper_ood_bits(
            self.log_inv_rate,
            self.log_msg_cols,
            self.eta,
            mu,
            self.ood_samples,
        )
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
            if lv.log_inv_rate == 0 {
                return Err(format!("L{i}: log_inv_rate=0 gives a rate-one code"));
            }
            if lv.log_msg_cols == 0 {
                return Err(format!("L{i}: log_msg_cols must be positive"));
            }

            // Shape: log_msg_cols + log_num_interleaved = dim_in.
            if lv.log_msg_cols + lv.log_num_interleaved != dim_in {
                return Err(format!(
                    "L{i}: log_msg_cols ({}) + log_num_interleaved ({}) ≠ input dim ({dim_in})",
                    lv.log_msg_cols, lv.log_num_interleaved
                ));
            }

            // Folding `lv.k` variables changes the next level's total RS
            // domain logarithm from `dim_in + rate_i` to
            // `dim_in - lv.k + rate_{i+1}`. Pin that difference to the public
            // initial reduction and to one bit at every later transition.
            if let Some(next) = self.levels.get(i + 1) {
                let domain_reduction = if i == 0 {
                    RS_DOMAIN_INITIAL_REDUCTION_FACTOR
                } else {
                    RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
                };
                let expected_next_rate = lv
                    .log_inv_rate
                    .checked_add(lv.k)
                    .and_then(|r| r.checked_sub(domain_reduction))
                    .ok_or_else(|| format!("L{i}: invalid RS domain reduction {domain_reduction}"))?;
                if next.log_inv_rate != expected_next_rate {
                    return Err(format!(
                        "L{}: log_inv_rate ({}) does not reduce the preceding RS domain by {} bit(s); expected {}",
                        i + 1,
                        next.log_inv_rate,
                        domain_reduction,
                        expected_next_rate,
                    ));
                }
            }

            // eta within the Johnson range for this level's (reduced) rate.
            let max_eta = 1.0 - reduced_rate(lv.log_inv_rate, lv.log_msg_cols).sqrt();
            if !lv.eta.is_finite() || lv.eta <= 0.0 || lv.eta >= max_eta {
                return Err(format!(
                    "L{i}: Johnson eta must be finite and in (0, {max_eta}), got {}",
                    lv.eta
                ));
            }

            // OOD samples: every level past L0 needs explicit samples, while
            // L0 is bound by the opening's own post-commit evaluation claim.
            if i == 0 && lv.ood_samples != 0 {
                return Err(format!(
                    "L0: ood_samples={} but L0 is bound by the opening's \
                     own evaluation claim (must be 0)",
                    lv.ood_samples
                ));
            }
            if i > 0 && lv.ood_samples == 0 {
                return Err(format!(
                    "L{i}: ood_samples ≥ 1 required past L0 (the query \
                     counts assume single-codeword binding)"
                ));
            }

            // OOD diagnostic matches the formula and clears the target.
            let declared = lv.expected_eps_ood_bits;
            if !declared.is_finite() {
                return Err(format!(
                    "L{i}: expected_eps_ood_bits must be finite, got {declared}"
                ));
            }
            let ood_pred = lv.paper_predicted_ood_bits();
            if (declared - ood_pred).abs() > PAPER_COMPAT_TOL_BITS {
                return Err(format!(
                    "L{i}: expected_eps_ood_bits ({declared:.2}) doesn't \
                     match prediction ({ood_pred:.2}); tolerance ±{:.2} bits.",
                    PAPER_COMPAT_TOL_BITS
                ));
            }
            if ood_pred + 1e-12 < lv.target_security_bits as f64 {
                return Err(format!(
                    "L{i}: OOD binding ({ood_pred:.2} bits) < target ({})",
                    lv.target_security_bits
                ));
            }

            // Paper-compatibility: the declared expected_*_bits must agree
            // with what the regime's formula predicts (within tolerance).
            // Asserts the config was actually derived from the paper, not
            // hand-waved into compliance.
            let (pg_pred, q_pred) = lv.paper_predicted_bits();
            if !lv.expected_eps_pg_bits.is_finite() || !lv.expected_eps_query_bits.is_finite() {
                return Err(format!("L{i}: expected soundness diagnostics must be finite"));
            }
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
                && q_pred + 1e-12 < (lv.target_security_bits - lv.grinding_bits) as f64
            {
                return Err(format!(
                    "L{i}: query soundness ({q_pred:.2} bits) < target ({}) - grinding ({}) = {}",
                    lv.target_security_bits,
                    lv.grinding_bits,
                    lv.target_security_bits - lv.grinding_bits
                ));
            }

            // Per-application proximity gap + fold-challenge grinding must
            // reach target. (The pg bad event lives on the fold challenges,
            // so only the fold grind — done before each fold challenge —
            // boosts it; the query-phase grind does not.)
            if pg_pred + lv.fold_grinding_bits as f64 + 1e-12
                < lv.target_security_bits as f64
            {
                return Err(format!(
                    "L{i}: proximity-gap soundness ({pg_pred:.2} bits) + fold_grinding ({}) < target ({})",
                    lv.fold_grinding_bits, lv.target_security_bits
                ));
            }

            // The largest list-unioned algebraic identity test (currently the
            // degree-191 ring-switch batching) is not grindable and must clear
            // the target.
            let algebraic = johnson_algebraic_bits(lv);
            if algebraic + 1e-12 < lv.target_security_bits as f64 {
                return Err(format!(
                    "L{i}: list-unioned algebraic soundness ({algebraic:.2} bits) < target ({})",
                    lv.target_security_bits
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

        // Round-by-round soundness (misc/pcs.tex, Thm `thm:rbr`): each
        // verifier-challenge transition is checked against
        // `target_security_bits` in the per-level loop above, so the
        // Fiat--Shamir error per random-oracle query is their MAX; ordinary
        // interactive soundness may additionally union-bound over transitions.
        Ok(())
    }

    /// Derive the production security config at witness size `m`: Johnson
    /// list decoding with OOD binding, rate `2^-LOG_INV_RATE_0`, and
    /// [`SECURITY_BITS`] bits per round under
    /// **round-by-round soundness** — every verifier-challenge error term (pg
    /// + fold grinding, query + query grinding, OOD, and algebraic checks)
    /// clears the target individually.
    pub fn derive_config(m: usize) -> Result<Self, String> {
        Self::derive_config_with_log_inv_rate(m, LOG_INV_RATE_0)
    }

    /// Derive a configuration for an explicit L0 rate `2^-log_inv_rate`.
    /// This side-effect-free entry point is used by parameter tooling and
    /// tests and production callers that accept a transcript-bound rate.
    pub fn derive_config_with_log_inv_rate(m: usize, log_inv_rate: usize) -> Result<Self, String> {
        validate_log_inv_rate(log_inv_rate)?;
        let target_bits = SECURITY_BITS;
        let query_grind: usize = QUERY_GRINDING_BITS;
        let log_n = m
            .checked_sub(crate::LOG_PACKING)
            .ok_or_else(|| format!("m ({m}) < LOG_PACKING ({})", crate::LOG_PACKING))?;
        let initial_k = INITIAL_FOLDING_FACTOR;

        // The ladder geometry is independent of eta. Exact block-length
        // feasibility is checked below by the same per-level optimizer that
        // supplies the production eta and query count.
        let shape = derive_ladder_shape(log_n, initial_k, log_inv_rate)?;
        let n_levels = shape.log_inv_rates.len();

        // Round-by-round target: every verifier-challenge error term (pg,
        // query, OOD, and algebraic checks) must individually clear
        // `target_bits`. We do not add a whole-transcript union-bound margin:
        // this configuration targets 128-bit RBR soundness, as required by the
        // Fiat--Shamir analysis, rather than 128-bit interactive soundness after
        // summing every transition probability.
        let mut levels = Vec::with_capacity(n_levels);
        for i in 0..n_levels {
            let rate = shape.log_inv_rates[i];
            let cols = shape.log_msg_cols[i];
            let ilv = shape.log_num_interleaved[i];
            let optimized = optimize_johnson_level(i, rate, cols, ilv, target_bits, query_grind)?;

            levels.push(LigeritoLevelConfig {
                log_inv_rate: rate,
                log_msg_cols: cols,
                log_num_interleaved: ilv,
                k: shape.k_levels[i],
                regime: SoundnessRegime::JohnsonOod,
                eta: optimized.eta,
                queries: optimized.queries,
                grinding_bits: query_grind,
                fold_grinding_bits: 0,
                ood_samples: optimized.ood_samples,
                target_security_bits: target_bits,
                expected_eps_pg_bits: round1(optimized.eps_pg),
                expected_eps_query_bits: round1(optimized.eps_query),
                expected_eps_ood_bits: round1(optimized.eps_ood),
            });
        }

        let analysis_version = "bchks25_thm_4_6_exact_reduced_rate_row_union_optimized_eta";
        let cfg = Self {
            m,
            log_n,
            initial_k,
            target_security_bits: target_bits,
            analysis_version: analysis_version.into(),
            field: "f192".into(),
            hash: "blake3".into(),
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
mod tests {
    use super::*;

    #[test]
    fn johnson_bound_uses_theorem_parameter_and_reduced_rate() {
        // BCHKS25 Thm 4.6 (list correlated agreement) uses
        // m = ceil(sqrt(rho) / eta). The factor-two-smaller ceil(sqrt(rho) / (2 eta))
        // belongs to the plain, non-list Thm 1.5; Flock's Thm 8 quotes Thm 4.6
        // with that non-list parameter, which would overstate eps_pg by ~5 bits.
        assert_eq!(johnson_m_param(1, 16, 0.02), 36.0);

        // A message of dimension 16 has maximum degree 15, so the theorem's
        // reduced rate at block length 512 is 15/512, not the nominal 1/32.
        assert_eq!(reduced_rate(5, 4), 15.0 / 512.0);
    }

    #[test]
    fn production_profile_is_128_bit_johnson_with_query_grinding() {
        let mut min_pg_bits = f64::INFINITY;
        for log_inv_rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            for m in 22 + crate::LOG_PACKING..=28 + crate::LOG_PACKING {
                let cfg = LigeritoSecurityConfig::derive_config_with_log_inv_rate(m, log_inv_rate)
                    .unwrap();
                assert_eq!(cfg.target_security_bits, 128);
                assert_eq!(cfg.levels[0].log_inv_rate, log_inv_rate);
                assert_eq!(cfg.levels[0].ood_samples, 0);
                for (i, level) in cfg.levels.iter().enumerate() {
                    let (pg_bits, query_bits) = level.paper_predicted_bits();
                    let ood_bits = level.paper_predicted_ood_bits();
                    let algebraic_bits = johnson_algebraic_bits(level);
                    min_pg_bits = min_pg_bits.min(pg_bits);
                    assert_eq!(level.grinding_bits, QUERY_GRINDING_BITS);
                    assert_eq!(level.fold_grinding_bits, 0);
                    assert!(query_bits + level.grinding_bits as f64 >= 128.0);
                    assert!(pg_bits >= 128.0);
                    assert!(ood_bits >= 128.0);
                    assert!(algebraic_bits >= 128.0);
                    if i > 0 {
                        assert_eq!(level.ood_samples, 1);
                    }
                }
            }
        }
        assert!(
            (128.0..129.0).contains(&min_pg_bits),
            "eta search should use, but not exceed, the one-bit PG margin: {min_pg_bits}"
        );
    }

    #[test]
    fn optimized_eta_query_and_rate_profile_is_stable() {
        let cfg = LigeritoSecurityConfig::derive_config_with_log_inv_rate(
            22 + crate::LOG_PACKING,
            1,
        )
        .unwrap();
        assert_eq!(
            cfg.levels.iter().map(|level| level.log_inv_rate).collect::<Vec<_>>(),
            [1, 4, 6, 8, 10]
        );
        assert_eq!(
            cfg.levels.iter().map(|level| level.queries).collect::<Vec<_>>(),
            [225, 56, 38, 28, 23]
        );
        assert_eq!(
            cfg.levels
                .iter()
                .map(|level| {
                    johnson_m_param(
                        level.log_inv_rate,
                        level.log_msg_cols,
                        level.eta,
                    ) as usize
                })
                .collect::<Vec<_>>(),
            [216, 80, 18, 35, 7]
        );
    }

    #[test]
    fn recursive_rs_domain_reduction_schedule_is_stable() {
        for starting_rate in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
            let cfg = LigeritoSecurityConfig::derive_config_with_log_inv_rate(
                27 + crate::LOG_PACKING,
                starting_rate,
            )
            .unwrap();
            let mut dim_in = cfg.log_n;
            let mut previous_domain_log = dim_in + cfg.levels[0].log_inv_rate;
            for (i, level) in cfg.levels.iter().enumerate() {
                dim_in -= level.k;
                if let Some(next) = cfg.levels.get(i + 1) {
                    let next_domain_log = dim_in + next.log_inv_rate;
                    let expected_reduction = if i == 0 {
                        RS_DOMAIN_INITIAL_REDUCTION_FACTOR
                    } else {
                        1
                    };
                    assert_eq!(
                        previous_domain_log - next_domain_log,
                        expected_reduction,
                        "transition L{i} -> L{} at starting rate 1/{}",
                        i + 1,
                        1usize << starting_rate,
                    );
                    previous_domain_log = next_domain_log;
                }
            }
        }
    }

    /// Parameter-report helper:
    /// `LIGERITO_LOG_INV_RATE=2 LIGERITO_NUM_VARS=22 cargo test --release -p pcs print_ligerito_query_counts -- --ignored --nocapture`
    #[test]
    #[ignore = "manual parameter report; configure it through environment variables"]
    fn print_ligerito_query_counts() {
        let env_usize = |name: &str| {
            std::env::var(name)
                .unwrap_or_else(|_| panic!("missing {name}"))
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("{name} must be a non-negative integer"))
        };
        let log_inv_rate = env_usize("LIGERITO_LOG_INV_RATE");
        let num_vars = env_usize("LIGERITO_NUM_VARS");
        let cfg = LigeritoSecurityConfig::derive_config_with_log_inv_rate(
            num_vars + crate::LOG_PACKING,
            log_inv_rate,
        )
        .unwrap();

        println!("num_vars={num_vars}, rate=1/{}", 1usize << log_inv_rate);
        for (level, params) in cfg.levels.iter().enumerate() {
            let eta = params.eta;
            println!(
                "L{level}: rate=1/{}, queries={}, eta={eta:.12e}, m={}",
                1usize << params.log_inv_rate,
                params.queries,
                johnson_m_param(params.log_inv_rate, params.log_msg_cols, eta) as usize,
            );
        }
    }
}
