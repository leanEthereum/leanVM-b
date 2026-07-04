//! Witness commitment: an inner-product PCS over F_{2^128} (doc §3), reusing
//! flock's **Ligerito**. An opening proves `Σ_x q(x)·W(x) = C` against any
//! verifier-evaluable weight `W` (a point evaluation `q̂(r)` is `W = eq(r,·)`). A
//! batch of claims `q̂(point_j) = value_j` folds with a random `λ` into one weight
//! `W_λ = Σ_j λ^j eq(point_j,·)` and target `C_λ = Σ_j λ^j value_j`, opened in a
//! single Ligerito run — the verifier evaluates `W_λ` itself, so it never travels.
//!
//! Security: the [`PROFILE`] is Ligerito `Secure` — rate 1/2, unique-decoding
//! regime (list size 1, no out-of-domain binding), 120-bit round-by-round soundness.

use crate::field::F128;
use crate::transcript::{ProverState, VerifierState};

use flare::pcs::ligerito::{LigeritoProfile, LigeritoSecurityConfig, ProverConfig, VerifierConfig};
pub use flare::pcs::{BatchOpeningProofLigerito, Commitment, PcsParams, ProverData};
use flare::pcs::{StackClaim, open_batch_mixed_ligerito_stacked, verify_opening_batch_mixed_ligerito_stacked};
use flare::zerocheck::PaddingSpec;

/// flock frames `commit` as `m = log2(len) + LOG_PACKING`; the message length is
/// `2^(m - LOG_PACKING)`, so for an F-valued witness of `2^μ` elements we set
/// `m = μ + LOG_PACKING`.
const LOG_PACKING: usize = 7;
/// Row-batch lanes `2^LOG_BATCH`: also the Merkle leaf width (`2^LOG_BATCH`
/// F128/leaf) and Ligerito's L0 fold count (`initial_k` — the shipped configs
/// require exactly 6). Larger ⇒ far fewer Merkle nodes to hash at the cost of
/// fatter query openings.
const LOG_BATCH: usize = 6;
/// L0 rate `2^-1` — the `Fast` profile's rate (doc §3).
pub const LOG_INV_RATE: usize = 1;
/// Ligerito security profile: rate 1/2, unique-decoding regime (list size 1,
/// no out-of-domain binding), **120-bit** round-by-round soundness. Same rate
/// as `Fast` (so `LOG_INV_RATE` is unchanged); the extra soundness comes from
/// more queries per level, i.e. a somewhat larger proof. Its bit target must
/// match the crate-wide [`crate::SECURITY_BITS`] (checked below).
pub const PROFILE: LigeritoProfile = LigeritoProfile::Secure;

// The PCS profile and the bus grinding both target `SECURITY_BITS`; keep them
// in sync — a stronger profile without bumping the constant (or vice versa)
// would leave one round below the intended level.
const _: () = assert!(PROFILE.security_bits() == crate::SECURITY_BITS as usize);
/// Minimum committed-witness log-size: Ligerito's recursion needs every level's
/// block length to accommodate its query count. The `Secure` profile's
/// unique-decoding regime uses more queries than `Fast`, so its floor is higher
/// — feasible from `μ = 14` (flock `m = 21`); we set `μ = 15` (`m = 22`, the
/// shipped-config minimum) for a one-level margin. `witness::placements_of`
/// zero-pads smaller stacks up to this floor (512 KB — negligible; real
/// workloads are far above it).
pub const MIN_MU: usize = 15;

fn params_for(mu: usize) -> PcsParams {
    assert!(
        mu >= MIN_MU,
        "witness must be ≥ 2^{MIN_MU} elements (padded by placements_of)"
    );
    PcsParams {
        m: mu + LOG_PACKING,
        log_inv_rate: LOG_INV_RATE,
        log_batch_size: LOG_BATCH,
        profile: PROFILE,
    }
}

/// The Ligerito (prover, verifier) config pair for a `2^μ`-element witness,
/// derived from the [`PROFILE`]'s security analysis and memoized per `μ` (the
/// derivation is a pure function of `(m, profile)`, so both sides agree).
fn lig_configs(mu: usize) -> std::sync::Arc<(ProverConfig, VerifierConfig)> {
    use std::collections::HashMap;
    use std::sync::{Arc, Mutex, OnceLock};
    type Cache = Mutex<HashMap<usize, Arc<(ProverConfig, VerifierConfig)>>>;
    static CACHE: OnceLock<Cache> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut map = cache.lock().expect("ligerito config cache poisoned");
    Arc::clone(map.entry(mu).or_insert_with(|| {
        let pair = LigeritoSecurityConfig::derive_profile(mu + LOG_PACKING, PROFILE)
            .and_then(|sec| sec.to_prover_verifier_configs())
            .unwrap_or_else(|e| panic!("ligerito {PROFILE:?} config for mu={mu}: {e}"));
        Arc::new(pair)
    }))
}

/// Rebuild the public [`Commitment`] (root + params) for a witness of `2^mu`
/// elements. The verifier reconstructs the params from `mu` exactly as `commit`
/// did, so the BLAKE3↔flock validity open (§blake3_flock) can verify its second
/// Ligerito against this same commitment.
pub fn commitment_from_root(root: [u8; 32], mu: usize) -> Commitment {
    Commitment {
        root,
        params: params_for(mu),
    }
}

/// A committed field-valued witness plus the data needed to open it. The witness
/// itself is not retained (the caller still owns it and passes it back to
/// [`open`]), so committing costs no extra full-trace copy.
pub struct Committed {
    pub commitment: Commitment,
    /// Codeword + Merkle tree retained for opening. Public so the BLAKE3↔flock
    /// validity open (a second Ligerito over this same commitment, §blake3_flock)
    /// can reuse it.
    pub prover_data: ProverData,
    /// `log2` of the witness length.
    pub mu: usize,
}

/// An evaluation claim located in a sub-cube (column slot) of the witness:
/// `q̂(low_point, sel) = value`, where the slot occupies `[offset, offset +
/// 2^{low_point.len()})` and `sel = offset >> low_point.len()` are its (boolean)
/// high-bit selector coordinates. Because the selector is boolean, the claim's
/// weight `eq(point,·)` is supported only inside the slot, where it equals
/// `eq(low_point,·)` — so W_λ is built block-sparsely in O(Σ_j 2^{n_vars_j})
/// rather than O(J·2^μ).
///
/// A [`SlotClaim::Strided`] is a further-sparse special case for **boolean-selector
/// slots on a packed column** (a BLAKE3 value word inside `q_pkd`): the low
/// `stride_log` within-block coords are frozen to `slot`'s bits, so `eq` is nonzero
/// only at `offset + slot + j·2^stride_log` — folded in `O(2^{point.len()})` rather
/// than the full `O(2^{stride_log + point.len()})` block. Equivalent to a `Slot`
/// with `low_point = slot_bits ++ point`.
#[derive(Clone, Debug)]
pub enum SlotClaim {
    Slot {
        offset: usize,
        low_point: Vec<F128>,
        value: F128,
    },
    Strided {
        offset: usize,
        slot: usize,
        stride_log: usize,
        point: Vec<F128>,
        value: F128,
    },
}

impl SlotClaim {
    pub fn value(&self) -> F128 {
        match self {
            SlotClaim::Slot { value, .. } | SlotClaim::Strided { value, .. } => *value,
        }
    }

    /// This claim as a borrowed flock [`StackClaim`] — `Strided` maps to the sparse
    /// [`StackClaim::StridedSlot`], `Slot` to the dense [`StackClaim::Slot`].
    fn as_stack(&self) -> StackClaim<'_> {
        match self {
            SlotClaim::Slot {
                offset,
                low_point,
                value,
            } => StackClaim::Slot {
                offset: *offset,
                low_point,
                value: *value,
            },
            SlotClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                value,
            } => StackClaim::StridedSlot {
                offset: *offset,
                slot: *slot,
                stride_log: *stride_log,
                point,
                value: *value,
            },
        }
    }
}

/// A batch of **ring-switched** evaluation claims discharged in the SAME opening
/// as the plain [`SlotClaim`]s (prover side). Unlike a `SlotClaim` — a plain
/// `eq`-point evaluation of the committed stack — these are claims on a packed
/// sub-block `qpkd` produced at the univariate-skip/packed level (flock's BLAKE3
/// R1CS validity `(ab, c)`), so they carry the ring-switch tensor front-end.
/// [`crate::blake3_flock`] builds this from its reduction's claims; [`open`]
/// slices `qpkd` from the committed stack and folds it into the one Ligerito.
pub struct RingSwitchOpen {
    /// `qpkd`'s offset inside the committed stack.
    pub offset: usize,
    /// `log2` of `qpkd`'s length; the opener slices `qpkd = stack[offset ..
    /// offset + 2^qpkd_vars]` (the committed sub-block, so no separate copy).
    pub qpkd_vars: usize,
    /// Per-claim `x_outer_full` (the multilinear tail of each quirky point).
    pub x_outers: Vec<Vec<F128>>,
    /// Per-claim optional precomputed ring-switch weight `s_hat_v`.
    pub s_hat_v: Vec<Option<Vec<F128>>>,
    /// flock's padding spec for the ring-switch weight (`k_log`, `useful_bits`).
    pub padding: PaddingSpec,
}

/// Verifier counterpart of [`RingSwitchOpen`]: the recovered `(ab, c)` claims and
/// the transmitted mixed opening proof.
pub struct RingSwitchVerify<'a> {
    /// `qpkd`'s offset inside the committed stack.
    pub offset: usize,
    /// `log2` of `qpkd`'s length (flock's `m − LOG_PACKING`).
    pub qpkd_vars: usize,
    /// Per-claim value, univariate-skip coord, and `x_outer_full`.
    pub values: Vec<F128>,
    pub z_skips: Vec<F128>,
    pub x_outers: Vec<Vec<F128>>,
    /// The stacked mixed opening proof (carried in the BLAKE3 attachment).
    pub open: &'a BatchOpeningProofLigerito,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Ligerito,
}

/// Commit a field-valued witness of length `2^μ` (`μ ≥ 2`) and bind its root into
/// the transcript, before any challenge is sampled. The verifier reads it with
/// [`read_commitment`].
pub fn commit(ps: &mut ProverState, witness: &[F128]) -> Committed {
    let n = witness.len();
    let mu = crate::log2_strict_usize(n);
    let params = params_for(mu);
    let (commitment, prover_data) = flare::pcs::commit(witness, &params);
    ps.add_scalars(&root_to_scalars(&commitment.root));
    Committed {
        commitment,
        prover_data,
        mu,
    }
}

// The folding scalar `λ` is just `sample()`d: every claim it combines is already
// bound — the values rode the stream (`add_scalar`) during the bus / constraint /
// public-input sub-protocols, the points are prior challenges, and the offsets are
// public (reconstructed identically from the announced layout). So `λ` sampled
// here is already bound to all of them; no re-observe is needed.

/// A Merkle root (32 bytes) as two field scalars, so it travels the transcript
/// stream like any other transmitted value (leanVM parses its root the same way).
fn root_to_scalars(root: &[u8; 32]) -> [F128; 2] {
    let w = |o: usize| u64::from_le_bytes(root[o..o + 8].try_into().unwrap());
    [F128::new(w(0), w(8)), F128::new(w(16), w(24))]
}

fn scalars_to_root(s: &[F128]) -> [u8; 32] {
    let mut root = [0u8; 32];
    root[0..8].copy_from_slice(&s[0].lo.to_le_bytes());
    root[8..16].copy_from_slice(&s[0].hi.to_le_bytes());
    root[16..24].copy_from_slice(&s[1].lo.to_le_bytes());
    root[24..32].copy_from_slice(&s[1].hi.to_le_bytes());
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
/// ring-switched BLAKE3 `(ab, c)` validity (`ring`) in ONE stacked Ligerito. The
/// points become the opener's `stack_pd`; the returned proof rides the BLAKE3
/// sub-proof channel (`write_stack_proof`), not the `ps` hint channel. The
/// commitment root was already bound by [`commit`], and the point *values* rode
/// the stream during their sub-protocols, so nothing extra is bound here.
///
/// There is no plain (non-ring-switch) path: the witness ALWAYS carries a `q_pkd`
/// sub-block (≥ 1 padding instance, §cpu), so every opening is stacked.
pub fn open(
    ps: &mut ProverState,
    c: &Committed,
    q: &[F128],
    points: &[SlotClaim],
    ring: &RingSwitchOpen,
) -> BatchOpeningProofLigerito {
    debug_assert_eq!(q.len(), 1usize << c.mu, "witness length must match the commitment");
    // The packed sub-block is exactly the committed slice — no separate copy.
    let qpkd = &q[ring.offset..ring.offset + (1usize << ring.qpkd_vars)];
    let stack_pd: Vec<StackClaim> = points.iter().map(|s| s.as_stack()).collect();
    let x_refs: Vec<&[F128]> = ring.x_outers.iter().map(|v| v.as_slice()).collect();
    let s_refs: Vec<Option<&[F128]>> = ring.s_hat_v.iter().map(|o| o.as_deref()).collect();
    let cfg = lig_configs(c.mu);
    open_batch_mixed_ligerito_stacked(
        qpkd,
        &x_refs,
        &s_refs,
        &ring.padding,
        q,
        ring.offset,
        &c.prover_data,
        &c.commitment,
        &stack_pd,
        &cfg.0,
        ps,
    )
}

/// Verify the opening (mirror of [`open`]): flock's ring-switched `(ab, c)` claims
/// and every `points` slot evaluation are checked together in the ONE stacked
/// Ligerito against `root`.
pub fn verify(
    vs: &mut VerifierState,
    points: &[SlotClaim],
    ring: &RingSwitchVerify,
    mu: usize,
    root: &[u8; 32],
) -> Result<(), Error> {
    let commitment = commitment_from_root(*root, mu);
    let stack_pd: Vec<StackClaim> = points.iter().map(|s| s.as_stack()).collect();
    let x_refs: Vec<&[F128]> = ring.x_outers.iter().map(|v| v.as_slice()).collect();
    let cfg = lig_configs(mu);
    verify_opening_batch_mixed_ligerito_stacked(
        &commitment,
        ring.offset,
        ring.qpkd_vars,
        &ring.values,
        &ring.z_skips,
        &x_refs,
        &stack_pd,
        ring.open,
        &cfg.1,
        vs,
    )
    .map_err(|_| Error::Ligerito)
}
