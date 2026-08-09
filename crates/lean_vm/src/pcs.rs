//! Witness commitment: an inner-product PCS committing over `K = F_{2^64}` and
//! opening over `E = F_{2^192}` (doc §sec:stacking, §annex:pcs), reusing flock's **WHIR**. An
//! opening proves `Σ_x q(x)·W(x) = C` against any verifier-evaluable `E`-valued
//! weight `W` (a point evaluation `q̂(r)` is `W = eq(r,·)`). A batch of claims
//! `q̂(point_j) = value_j` folds with random `γ`s into one weight and target,
//! opened in a single WHIR run: the verifier evaluates the weight itself,
//! so it never travels. flock's ring-switched `q_flock` claims join the same batch
//! ([`::pcs::stack_open`]).
//!
//! Security: the K configs use rate-1/2 Johnson list decoding with OOD binding
//! and 128-bit round-by-round soundness ([`::pcs::whir::SECURITY_BITS`]).
//! L0's opening claim supplies its binding evaluation; each deeper commitment
//! takes one explicit OOD sample. The base-field
//! commitment only shrinks the level-0 symbols to 8 bytes; every random
//! ingredient is sampled from `E` with the same error terms as before.

use crate::transcript::{ProverState, VerifierState};
use primitives::field::F64;

pub use ::pcs::stack_open::{
    RingSwitchClaim, RingSwitchOpen, RingSwitchVerify, StackClaim as SlotClaim, StackedOpeningSummary,
};
use ::pcs::stack_open::{open_batch_mixed_whir_stacked, verify_opening_batch_mixed_whir_stacked};
use ::pcs::whir::{Commitment, ProverData, commit as whir_commit, configs_for_rate};
use ::pcs::whir::{ProverConfig, VerifierConfig};

/// Row-batch lanes `2^LOG_BATCH`: the Merkle leaf width (`2^LOG_BATCH` F64
/// = 512 bytes/leaf) IS WHIR's INITIAL folding factor: the L0 commit is
/// reused, so the two are one knob ([`::pcs::whir::INITIAL_FOLDING_FACTOR`]).
/// Larger ⇒ far fewer Merkle nodes to hash at the cost of fatter query openings.
const LOG_BATCH: usize = ::pcs::whir::INITIAL_FOLDING_FACTOR;
/// Default L0 rate index.
pub const LOG_INV_RATE: usize = ::pcs::whir::LOG_INV_RATE_0;
// The PCS and the unground F192 bus argument both target `SECURITY_BITS`.
const _: () = assert!(::pcs::whir::SECURITY_BITS == crate::SECURITY_BITS as usize);
/// Minimum committed-witness log-size: WHIR's level ladder needs every level's
/// block length to accommodate its Johnson-radius query count, feasible from
/// `μ = 14`; we set `μ = 15` for a
/// one-level margin. `witness::placements_of` zero-pads smaller stacks up to
/// this floor (256 KB of F64, negligible; real workloads are far above it).
pub const MIN_MU: usize = 15;

/// The WHIR (prover, verifier) config pair for a `2^μ`-word witness,
/// derived from the security analysis and memoized per `(μ, log_inv_rate)`.
fn whir_configs(mu: usize, log_inv_rate: usize) -> std::sync::Arc<(ProverConfig, VerifierConfig)> {
    use std::collections::HashMap;
    use std::sync::{Arc, Mutex, OnceLock};
    type Cache = Mutex<HashMap<(usize, usize), Arc<(ProverConfig, VerifierConfig)>>>;
    static CACHE: OnceLock<Cache> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut map = cache.lock().expect("whir config cache poisoned");
    Arc::clone(map.entry((mu, log_inv_rate)).or_insert_with(|| {
        assert!(
            mu >= MIN_MU,
            "witness must be ≥ 2^{MIN_MU} elements (padded by placements_of)"
        );
        let pair = configs_for_rate(mu, log_inv_rate)
            .unwrap_or_else(|e| panic!("whir config for mu={mu}, log_inv_rate={log_inv_rate}: {e}"));
        Arc::new(pair)
    }))
}

/// A committed `K`-valued witness plus the data needed to open it. The witness
/// itself is not retained (the caller still owns it and passes it back to
/// [`open`]), so committing costs no extra full-trace copy.
pub struct Committed {
    pub commitment: Commitment,
    /// Codeword + Merkle tree retained for opening. Public so the single stacked
    /// WHIR opening (which also discharges flock's `(ab, c)` claims over
    /// this same commitment, §blake3_flock) can reuse it.
    pub prover_data: ProverData,
    /// `log2` of the witness length in F64 words.
    pub mu: usize,
    /// L0 inverse-rate logarithm bound into the transcript before this commitment.
    pub log_inv_rate: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Whir,
}

/// Commit a `K`-valued witness of length `2^μ` (`μ ≥ MIN_MU`; smaller stacks
/// are zero-padded up by [`crate::witness::placements_of`]) and bind its root
/// into the transcript, before any challenge is sampled. The verifier reads it
/// with [`read_commitment`].
pub fn commit(ps: &mut ProverState, witness: &[F64], log_inv_rate: usize) -> Committed {
    let n = witness.len();
    let mu = crate::log2_strict_usize(n);
    assert!(
        mu >= MIN_MU,
        "witness must be ≥ 2^{MIN_MU} elements (padded by placements_of)"
    );
    let (commitment, prover_data) = whir_commit(witness, LOG_BATCH, log_inv_rate);
    ps.add_scalars(&::pcs::merkle::hash_to_scalars(&commitment.root));
    Committed {
        commitment,
        prover_data,
        mu,
        log_inv_rate,
    }
}

// The batching challenges are just `sample()`d inside the stacked opener: every
// claim they combine is already bound: the values rode the stream
// (`add_scalar`) during the bus / constraint / public-input sub-protocols, the
// points are prior challenges, and the offsets are public (reconstructed
// identically from the announced layout).

/// Verifier counterpart of [`commit`]'s root binding: read the committed root
/// from the stream at the start of verification, before sampling any challenge.
pub fn read_commitment(vs: &mut VerifierState) -> Result<[u8; 32], crate::transcript::Error> {
    let root_s = vs.next_scalars(2)?;
    if root_s.iter().any(|word| word.c2 != 0) {
        return Err(crate::transcript::Error::NonCanonicalEncoding);
    }
    Ok(::pcs::merkle::scalars_to_hash(&root_s))
}

/// Open the committed witness: discharge the `points` (leanVM's bus / constraint /
/// public-input claims, as block-sparse slot evaluations) AND flock's
/// ring-switched BLAKE3 `(ab, c)` validity (`ring`) in ONE stacked WHIR.
/// The points become the opener's `point_claims`; the returned proof is placed
/// on the `openings` hint channel by the caller (`ps.hint_opening`), not on the
/// scalar stream. The commitment root was already bound by [`commit`], and the
/// point *values* rode the stream during their sub-protocols, so nothing extra
/// is bound here.
///
/// There is no plain (non-ring-switch) path: the witness ALWAYS carries a `q_flock`
/// sub-block (≥ 1 padding instance, §cpu), so every opening is stacked.
pub fn open(
    ps: &mut ProverState,
    c: &Committed,
    q: &[F64],
    points: &[SlotClaim],
    ring: &RingSwitchOpen,
) -> ::pcs::whir::WhirProof {
    debug_assert_eq!(q.len(), 1usize << c.mu, "witness length must match the commitment");
    let cfg = whir_configs(c.mu, c.log_inv_rate);
    open_batch_mixed_whir_stacked(ps, q, &c.prover_data, &cfg.0, points, ring)
}

/// Verify the opening (mirror of [`open`]): flock's ring-switched `(ab, c)` claims
/// and every `points` slot evaluation are checked together in the ONE stacked
/// WHIR against `root`. `open` is the transmitted proof, read off the
/// `openings` hint channel at its protocol point by the caller.
pub fn verify(
    vs: &mut VerifierState,
    points: &[SlotClaim],
    ring: &RingSwitchVerify,
    open: &::pcs::whir::WhirProof,
    mu: usize,
    log_inv_rate: usize,
    root: &[u8; 32],
) -> Result<StackedOpeningSummary, Error> {
    let cfg = whir_configs(mu, log_inv_rate);
    verify_opening_batch_mixed_whir_stacked(vs, &cfg.1, mu, root, points, ring, open).ok_or(Error::Whir)
}
