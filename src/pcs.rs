//! Witness commitment: an inner-product PCS committing over `K = F_{2^64}` and
//! opening over `E = F_{2^128}` (doc §3), reusing flock's **Ligerito-K**. An
//! opening proves `Σ_x q(x)·W(x) = C` against any verifier-evaluable `E`-valued
//! weight `W` (a point evaluation `q̂(r)` is `W = eq(r,·)`). A batch of claims
//! `q̂(point_j) = value_j` folds with random `γ`s into one weight and target,
//! opened in a single Ligerito-K run — the verifier evaluates the weight itself,
//! so it never travels. flock's ring-switched `q_pkd` claims join the same batch
//! ([`flare::pcs::stack_open_k`]).
//!
//! Security: the [`PROFILE`] is Ligerito `Secure` — rate 1/2, unique-decoding
//! regime (list size 1, no out-of-domain binding), 120-bit round-by-round
//! soundness. The base-field commitment only shrinks the level-0 symbols to
//! 8 bytes; every random ingredient is sampled from `E` with the same error
//! terms as before.

use crate::field::{F64, F128T};
use crate::transcript::{ProverState, VerifierState};

use flare::pcs::ligerito::{LigeritoProfile, ProverConfig, VerifierConfig};
use flare::pcs::ligerito_k::{CommitmentK, ProverDataK, commit_k, k_configs_for};
pub use flare::pcs::stack_open_k::{
    BatchOpeningProofK, RingSwitchClaimK, RingSwitchOpenK as RingSwitchOpen, RingSwitchVerifyK as RingSwitchVerify,
    StackClaimK as SlotClaim,
};
use flare::pcs::stack_open_k::{open_batch_mixed_ligerito_stacked_k, verify_opening_batch_mixed_ligerito_stacked_k};

/// The bit-packing width of `q_pkd` (`2^6` bits per committed `F64` word); only
/// bookkeeping here, since the K configs take the witness log-size directly.
pub const LOG_PACKING: usize = flare::pcs::pack_k::LOG_PACKING_K;
/// Row-batch lanes `2^LOG_BATCH`: also the Merkle leaf width (`2^LOG_BATCH` F64
/// = 512 bytes/leaf) and Ligerito's L0 fold count (`initial_k` — the shipped
/// configs require exactly 6). Larger ⇒ far fewer Merkle nodes to hash at the
/// cost of fatter query openings. Must match [`k_configs_for`]'s `initial_k`.
const LOG_BATCH: usize = 6;
/// L0 rate `2^-1` — the profile's rate (doc §3).
pub const LOG_INV_RATE: usize = 1;
/// Ligerito security profile: rate 1/2, unique-decoding regime (list size 1,
/// no out-of-domain binding), **120-bit** round-by-round soundness (the same
/// derivation [`k_configs_for`] uses). Its bit target must match the crate-wide
/// [`crate::SECURITY_BITS`] (checked below).
pub const PROFILE: LigeritoProfile = LigeritoProfile::Secure;

// The PCS profile and the bus grinding both target `SECURITY_BITS`; keep them
// in sync — a stronger profile without bumping the constant (or vice versa)
// would leave one round below the intended level.
const _: () = assert!(PROFILE.security_bits() == crate::SECURITY_BITS as usize);
/// Minimum committed-witness log-size: Ligerito's recursion needs every level's
/// block length to accommodate its query count. The `Secure` profile's
/// unique-decoding regime uses more queries than `Fast`, so its floor is higher
/// — `k_configs_for` is feasible from `μ = 14`; we set `μ = 15` for a one-level
/// margin. `witness::placements_of` zero-pads smaller stacks up to this floor
/// (256 KB of F64 — negligible; real workloads are far above it).
pub const MIN_MU: usize = 15;

/// The Ligerito-K (prover, verifier) config pair for a `2^μ`-word witness,
/// derived from the [`PROFILE`]'s security analysis and memoized per `μ` (the
/// derivation is a pure function of `μ`, so both sides agree).
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

/// Rebuild the public GHASH-typed [`flock_prover::pcs::Commitment`] flock's
/// reduction binds its statement to (`bind_statement` observes only the ROOT;
/// the params are shape metadata built the same deterministic way on both
/// sides, so prove/verify stay symmetric). The K commitment itself is a
/// [`CommitmentK`]; this wrapper exists solely because flock's zerocheck /
/// lincheck (GHASH world, untouched) take their commitment in the F128 type.
pub fn commitment_from_root(root: [u8; 32], mu: usize) -> flock_prover::pcs::Commitment {
    flock_prover::pcs::Commitment {
        root,
        params: flock_prover::pcs::PcsParams {
            m: mu + LOG_PACKING,
            log_inv_rate: LOG_INV_RATE,
            log_batch_size: LOG_BATCH,
            profile: PROFILE,
        },
    }
}

/// A committed `K`-valued witness plus the data needed to open it. The witness
/// itself is not retained (the caller still owns it and passes it back to
/// [`open`]), so committing costs no extra full-trace copy.
pub struct Committed {
    pub commitment: CommitmentK,
    /// Codeword + Merkle tree retained for opening.
    pub prover_data: ProverDataK,
    /// `log2` of the witness length in F64 words.
    pub mu: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Ligerito,
}

/// Commit a `K`-valued witness of length `2^μ` (`μ ≥ MIN_MU`) and bind its root
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
/// public-input / pin claims, as block-sparse slot evaluations) AND flock's
/// ring-switched BLAKE3 `(ab, c)` validity (`ring`) in ONE stacked Ligerito-K. The
/// returned proof rides the BLAKE3 sub-proof channels (`write_stack_proof`), not
/// the `ps` hint channel here. The commitment root was already bound by
/// [`commit`], and the point *values* rode the stream during their
/// sub-protocols, so nothing extra is bound here.
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
    open_batch_mixed_ligerito_stacked_k(ps, q, &c.prover_data, &cfg.0, points, ring)
}

/// Verify the opening (mirror of [`open`]): flock's ring-switched `(ab, c)` claims
/// and every `points` slot evaluation are checked together in the ONE stacked
/// Ligerito-K against `root`.
pub fn verify(
    vs: &mut VerifierState,
    points: &[SlotClaim],
    ring: &RingSwitchVerify,
    proof: &BatchOpeningProofK,
    mu: usize,
    root: &[u8; 32],
) -> Result<(), Error> {
    let cfg = lig_configs(mu);
    if verify_opening_batch_mixed_ligerito_stacked_k(vs, &cfg.1, mu, root, points, ring, proof) {
        Ok(())
    } else {
        Err(Error::Ligerito)
    }
}
