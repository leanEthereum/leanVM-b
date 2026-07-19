//! Witness commitment: an inner-product PCS committing over `K = F_{2^64}` and
//! opening over `E = F_{2^128}` (doc §3), reusing flock's **Ligerito-K**. An
//! opening proves `Σ_x q(x)·W(x) = C` against any verifier-evaluable `E`-valued
//! weight `W` (a point evaluation `q̂(r)` is `W = eq(r,·)`). A batch of claims
//! `q̂(point_j) = value_j` folds with random `γ`s into one weight and target,
//! opened in a single Ligerito-K run — the verifier evaluates the weight itself,
//! so it never travels. flock's ring-switched `q_pkd` claims join the same batch
//! ([`::pcs::stack_open_k`]).
//!
//! Security: the K configs reuse Ligerito's one shipped configuration — a
//! UDR/LDR hybrid (unique-decoding for the low-rate early levels, Johnson
//! list-decoding with a single OOD-challenge-ground out-of-domain sample for the
//! deep high-rate levels), 120-bit round-by-round soundness
//! ([`::pcs::ligerito::SECURITY_BITS`]). The base-field commitment only shrinks
//! the level-0 symbols to 8 bytes; every random ingredient is sampled from `E`
//! with the same error terms as before.

use primitives::field::{F64, F128T};
use crate::transcript::{ProverState, VerifierState};

use ::pcs::ligerito::{ProverConfig, VerifierConfig};
use ::pcs::ligerito_k::{CommitmentK, ProverDataK, commit_k, k_configs_for};
pub use ::pcs::stack_open_k::{
    BatchOpeningProofK, RingSwitchClaimK, RingSwitchOpenK as RingSwitchOpen, RingSwitchVerifyK as RingSwitchVerify,
    StackClaimK as SlotClaim, StackedOpeningSummaryK as StackedOpeningSummary,
};
use ::pcs::stack_open_k::{open_batch_mixed_ligerito_stacked_k, verify_opening_batch_mixed_ligerito_stacked_k};

/// The bit-packing width of `q_pkd` (`2^6` bits per committed `F64` word); only
/// bookkeeping here, since the K configs take the witness log-size directly.
pub const LOG_PACKING: usize = ::pcs::pack_k::LOG_PACKING_K;
/// Row-batch lanes `2^LOG_BATCH`: the Merkle leaf width (`2^LOG_BATCH` F64
/// = 512 bytes/leaf) IS Ligerito's INITIAL folding factor — the L0 commit is
/// reused, so the two are one knob ([`::pcs::ligerito::INITIAL_FOLDING_FATOR`]).
/// Larger ⇒ far fewer Merkle nodes to hash at the cost of fatter query openings.
const LOG_BATCH: usize = ::pcs::ligerito::INITIAL_FOLDING_FATOR;
/// L0 rate (doc §3) — the one knob [`::pcs::ligerito::LOG_INV_RATE_0`].
pub const LOG_INV_RATE: usize = ::pcs::ligerito::LOG_INV_RATE_0;
// The PCS and the bus grinding both target `SECURITY_BITS`; keep them in
// sync — a stronger PCS target without bumping the constant (or vice versa)
// would leave one round below the intended level.
const _: () = assert!(::pcs::ligerito::SECURITY_BITS == crate::SECURITY_BITS as usize);
/// Minimum committed-witness log-size: Ligerito's level ladder needs every level's
/// block length to accommodate its query count under the unique-decoding
/// regime's query counts — feasible from `μ = 14`; we set `μ = 15` for a
/// one-level margin. `witness::placements_of` zero-pads smaller stacks up to
/// this floor (256 KB of F64 — negligible; real workloads are far above it).
pub const MIN_MU: usize = 15;

/// The Ligerito-K (prover, verifier) config pair for a `2^μ`-word witness,
/// derived from the security analysis and memoized per `μ` (the derivation is
/// a pure function of `μ`, so both sides agree).
fn lig_configs(mu: usize) -> std::sync::Arc<(ProverConfig, VerifierConfig)> {
    use std::collections::HashMap;
    use std::sync::{Arc, Mutex, OnceLock};
    type Cache = Mutex<HashMap<usize, Arc<(ProverConfig, VerifierConfig)>>>;
    static CACHE: OnceLock<Cache> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut map = cache.lock().expect("ligerito config cache poisoned");
    Arc::clone(map.entry(mu).or_insert_with(|| {
        assert!(
            mu >= MIN_MU,
            "witness must be ≥ 2^{MIN_MU} elements (padded by placements_of)"
        );
        let pair = k_configs_for(mu).unwrap_or_else(|e| panic!("ligerito K config for mu={mu}: {e}"));
        Arc::new(pair)
    }))
}

/// A committed `K`-valued witness plus the data needed to open it. The witness
/// itself is not retained (the caller still owns it and passes it back to
/// [`open`]), so committing costs no extra full-trace copy.
pub struct Committed {
    pub commitment: CommitmentK,
    /// Codeword + Merkle tree retained for opening. Public so the single stacked
    /// Ligerito-K opening (which also discharges flock's `(ab, c)` claims over
    /// this same commitment, §blake3_flock) can reuse it.
    pub prover_data: ProverDataK,
    /// `log2` of the witness length in F64 words.
    pub mu: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Ligerito,
}

/// Commit a `K`-valued witness of length `2^μ` (`μ ≥ MIN_MU`; smaller stacks
/// are zero-padded up by [`crate::witness::placements_of`]) and bind its root
/// into the transcript, before any challenge is sampled. The verifier reads it
/// with [`read_commitment`].
pub fn commit(ps: &mut ProverState, witness: &[F64]) -> Committed {
    let n = witness.len();
    let mu = crate::log2_strict_usize(n);
    assert!(
        mu >= MIN_MU,
        "witness must be ≥ 2^{MIN_MU} elements (padded by placements_of)"
    );
    let (commitment, prover_data) = commit_k(witness, LOG_BATCH, LOG_INV_RATE);
    ps.add_scalars(&root_to_scalars(&commitment.root));
    Committed {
        commitment,
        prover_data,
        mu,
    }
}

// The batching challenges are just `sample()`d inside the stacked opener: every
// claim they combine is already bound — the values rode the stream
// (`add_scalar`) during the bus / constraint / public-input sub-protocols, the
// points are prior challenges, and the offsets are public (reconstructed
// identically from the announced layout).

/// A Merkle root (32 bytes) as two field scalars, so it travels the transcript
/// stream like any other transmitted value (leanVM parses its root the same way).
fn root_to_scalars(root: &[u8; 32]) -> [F128T; 2] {
    let w = |o: usize| u64::from_le_bytes(root[o..o + 8].try_into().unwrap());
    [F128T::new(w(0), w(8)), F128T::new(w(16), w(24))]
}

fn scalars_to_root(s: &[F128T]) -> [u8; 32] {
    let mut root = [0u8; 32];
    root[0..8].copy_from_slice(&s[0].c0.to_le_bytes());
    root[8..16].copy_from_slice(&s[0].c1.to_le_bytes());
    root[16..24].copy_from_slice(&s[1].c0.to_le_bytes());
    root[24..32].copy_from_slice(&s[1].c1.to_le_bytes());
    root
}

/// Verifier counterpart of [`commit`]'s root binding: read the committed root
/// from the stream at the start of verification, before sampling any challenge.
pub fn read_commitment(vs: &mut VerifierState) -> Result<[u8; 32], crate::transcript::Error> {
    let root_s = vs.next_scalars(2)?;
    Ok(scalars_to_root(&root_s))
}

/// Open the committed witness: discharge the `points` (leanVM's bus / constraint /
/// public-input claims, as block-sparse slot evaluations) AND flock's
/// ring-switched BLAKE3 `(ab, c)` validity (`ring`) in ONE stacked Ligerito-K.
/// The points become the opener's `point_claims`; the returned proof is placed
/// on the `openings` hint channel by the caller (`ps.hint_opening`), not on the
/// scalar stream. The commitment root was already bound by [`commit`], and the
/// point *values* rode the stream during their sub-protocols, so nothing extra
/// is bound here.
///
/// There is no plain (non-ring-switch) path: the witness ALWAYS carries a `q_pkd`
/// sub-block (≥ 1 padding instance, §cpu), so every opening is stacked.
pub fn open(
    ps: &mut ProverState,
    c: &Committed,
    q: &[F64],
    points: &[SlotClaim],
    ring: &RingSwitchOpen,
) -> BatchOpeningProofK {
    debug_assert_eq!(q.len(), 1usize << c.mu, "witness length must match the commitment");
    let cfg = lig_configs(c.mu);
    open_batch_mixed_ligerito_stacked_k(ps.sponge_mut(), q, &c.prover_data, &cfg.0, points, ring)
}

/// Verify the opening (mirror of [`open`]): flock's ring-switched `(ab, c)` claims
/// and every `points` slot evaluation are checked together in the ONE stacked
/// Ligerito-K against `root`. `open` is the transmitted proof, read off the
/// `openings` hint channel at its protocol point by the caller.
pub fn verify(
    vs: &mut VerifierState,
    points: &[SlotClaim],
    ring: &RingSwitchVerify,
    open: &BatchOpeningProofK,
    mu: usize,
    root: &[u8; 32],
) -> Result<StackedOpeningSummary, Error> {
    let cfg = lig_configs(mu);
    verify_opening_batch_mixed_ligerito_stacked_k(vs.sponge_mut(), &cfg.1, mu, root, points, ring, open)
        .ok_or(Error::Ligerito)
}
