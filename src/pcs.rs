//! Witness commitment: an inner-product PCS over F_{2^128} (doc §3).
//!
//! We reuse flock's **Ligerito** (interleaved Reed-Solomon + Merkle, recursively
//! folded — see flock.tex §app:ligerito) as the scheme: `commit` encodes the F128
//! message, and an opening proves the inner product `Σ_x q(x)·W(x) = C` against
//! any verifier-evaluable weight `W`, by a sumcheck folded in lockstep with the
//! recursive code folds (a plain point evaluation `q̂(r)` is the case
//! `W = eq(r,·)`).
//!
//! For a batch of claims `q̂(point_j) = value_j` we fold them with a random `λ`
//! into one weight `W_λ = Σ_j λ^j eq(point_j,·)` and target `C_λ = Σ_j λ^j
//! value_j`, and run a single Ligerito opening on `Σ_x q(x)·W_λ(x) = C_λ`
//! directly, with no separate reduction sumcheck. The verifier evaluates `W_λ`
//! itself at the residual points (the succinct-verifier closure), so `W_λ` never
//! travels.
//!
//! Security: the [`PROFILE`] is Ligerito `Fast` — rate 1/2, **Johnson
//! list-decoding regime with out-of-domain binding, 100-bit** round-by-round
//! soundness (flock.tex §app:ligerito extends Ligerito to the list-decoding
//! regime; parameters derived by `LigeritoSecurityConfig::derive_profile`).

use crate::field::F128;
use crate::multilinear::{eq_eval, eq_table};
use crate::transcript::{ProverState, VerifierState};
use rayon::prelude::*;

use flare::pcs::ligerito::{self, LigeritoProfile, LigeritoSecurityConfig, ProverConfig, VerifierConfig};
use flare::pcs::{StackClaim, open_batch_mixed_ligerito_stacked, verify_opening_batch_mixed_ligerito_stacked};
pub use flare::pcs::{BatchOpeningProofLigerito, Commitment, PcsParams, ProverData};
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
/// Ligerito security profile: rate 1/2, Johnson **list-decoding** regime with
/// out-of-domain binding, 100-bit round-by-round soundness.
pub const PROFILE: LigeritoProfile = LigeritoProfile::Fast;
/// Minimum committed-witness log-size: Ligerito's recursion needs every level's
/// block length to accommodate its query count, which for the `Fast` profile
/// bottoms out at `μ = 13` (flock `m = 20`). `witness::placements_of` zero-pads
/// smaller stacks up to this floor (128 KB — negligible; real workloads are far
/// above it).
pub const MIN_MU: usize = 13;

fn params_for(mu: usize) -> PcsParams {
    assert!(mu >= MIN_MU, "witness must be ≥ 2^{MIN_MU} elements (padded by placements_of)");
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
            SlotClaim::Slot { offset, low_point, value } => StackClaim::Slot {
                offset: *offset,
                low_point,
                value: *value,
            },
            SlotClaim::Strided { offset, slot, stride_log, point, value } => StackClaim::StridedSlot {
                offset: *offset,
                slot: *slot,
                stride_log: *stride_log,
                point,
                value: *value,
            },
        }
    }

    /// The equivalent dense `(offset, low_point, value)`. `Strided` materializes
    /// `slot_bits ++ point`; used only by the plain λ-opener (non-BLAKE3), where
    /// every claim is already a dense `Slot`, so no materialization occurs.
    fn dense(&self) -> (usize, std::borrow::Cow<'_, [F128]>, F128) {
        match self {
            SlotClaim::Slot { offset, low_point, value } => (*offset, std::borrow::Cow::Borrowed(low_point), *value),
            SlotClaim::Strided { offset, slot, stride_log, point, value } => {
                let mut lp: Vec<F128> = (0..*stride_log)
                    .map(|k| if (slot >> k) & 1 == 1 { F128::ONE } else { F128::ZERO })
                    .collect();
                lp.extend_from_slice(point);
                (*offset, std::borrow::Cow::Owned(lp), *value)
            }
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

/// One claim in the witness opening's unified list ([`open`]): either a plain
/// point evaluation of the committed stack ([`SlotClaim`]), or the ring-switched
/// packed bundle carrying a sub-proof front-end ([`RingSwitchOpen`] — flock's
/// BLAKE3 `(ab, c)` validity). All claims in the list are discharged by ONE
/// Ligerito; when a ring-switch bundle is present the combine is delegated to
/// flock's mixed opener (which folds the point claims as `stack_pd`), otherwise
/// the plain block-sparse λ-opener runs. The list holds at most one `RingSwitch`.
pub enum OpenClaim {
    Point(SlotClaim),
    RingSwitch(RingSwitchOpen),
}

/// Verifier counterpart of [`OpenClaim`] (see [`verify`]).
pub enum VerifyClaim<'a> {
    Point(SlotClaim),
    RingSwitch(RingSwitchVerify<'a>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Ligerito,
    MissingHint,
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

/// Open the witness against a unified list of [`OpenClaim`]s: hint the Ligerito
/// opening (the hash-bearing data) and bind the claims. The commitment root was
/// already bound at the protocol's start by [`commit`]; the claim *values*
/// themselves already travelled the stream as part of the bus/constraint
/// arguments.
///
/// When the list carries a [`OpenClaim::RingSwitch`] bundle (BLAKE3 present),
/// flock's ring-switched `(ab, c)` validity is discharged in the SAME Ligerito as
/// the point claims — the latter become full-stack `stack_pd` evaluations — and
/// the mixed opening proof is returned (it rides the BLAKE3 attachment, not the
/// `ps` hint channel). Otherwise the plain block-sparse λ-opener runs, hinting
/// into `ps` and returning `None`.
pub fn open(ps: &mut ProverState, c: &Committed, q: &[F128], claims: &[OpenClaim]) -> Option<BatchOpeningProofLigerito> {
    let n = 1usize << c.mu;
    debug_assert_eq!(q.len(), n, "witness length must match the commitment");

    // Split the unified list: the plain point claims and the (≤1) ring-switch
    // bundle. The point order is preserved, so the λ-combine / `stack_pd` order
    // is unchanged.
    let points: Vec<SlotClaim> = claims
        .iter()
        .filter_map(|cl| match cl {
            OpenClaim::Point(s) => Some(s.clone()),
            OpenClaim::RingSwitch(_) => None,
        })
        .collect();
    let ring = claims.iter().find_map(|cl| match cl {
        OpenClaim::RingSwitch(r) => Some(r),
        OpenClaim::Point(_) => None,
    });

    if let Some(rs) = ring {
        // The packed sub-block is exactly the committed slice — no separate copy.
        let qpkd = &q[rs.offset..rs.offset + (1usize << rs.qpkd_vars)];
        // leanVM point claims are block-sparse slots (offset + within-column point);
        // the opener builds `eq` over just each slot, not the whole 2^m stack.
        let stack_pd: Vec<StackClaim> = points.iter().map(|s| s.as_stack()).collect();
        let x_refs: Vec<&[F128]> = rs.x_outers.iter().map(|v| v.as_slice()).collect();
        let s_refs: Vec<Option<&[F128]>> = rs.s_hat_v.iter().map(|o| o.as_deref()).collect();
        let cfg = lig_configs(c.mu);
        return Some(open_batch_mixed_ligerito_stacked(
            qpkd,
            &x_refs,
            &s_refs,
            &rs.padding,
            q,
            rs.offset,
            &c.prover_data,
            &c.commitment,
            &stack_pd,
            &cfg.0,
            ps,
        ));
    }

    let lambda = ps.sample();

    // W_λ over the cube and C_λ, built block-sparsely: each claim only writes
    // its column's slot, and eq-tables are cached across claims that share a
    // point (e.g. every column of one constraint table shares `rho`).
    let mut weight = vec![F128::ZERO; n];
    let mut target = F128::ZERO;
    let mut lambda_pow = F128::ONE; // running λ^j
    let mut eq_cache: Vec<(Vec<F128>, Vec<F128>)> = Vec::new();
    for claim in &points {
        // The non-BLAKE3 λ-opener only ever sees dense `Slot`s (`Strided`
        // claims come from BLAKE3, which takes the ring-switch path above).
        let (offset, low_point, value) = claim.dense();
        let n_vars = low_point.len();
        debug_assert!(offset + (1 << n_vars) <= n, "slot out of range");
        let cache_idx = match eq_cache.iter().position(|(point, _)| point.as_slice() == low_point.as_ref()) {
            Some(i) => i,
            None => {
                eq_cache.push((low_point.to_vec(), eq_table(&low_point)));
                eq_cache.len() - 1
            }
        };
        let eq_block = &eq_cache[cache_idx].1;
        weight[offset..offset + eq_block.len()]
            .par_iter_mut()
            .zip(eq_block.par_iter())
            .for_each(|(w, eq)| *w += lambda_pow * *eq);
        target += lambda_pow * value;
        lambda_pow *= lambda;
    }

    let cfg = lig_configs(c.mu);
    let lig = ligerito::recursive_prover_with_basis(
        &cfg.0,
        q.to_vec(),
        weight,
        target,
        &c.prover_data.codeword,
        &c.prover_data.merkle_tree,
        ps,
    );
    ps.hint_opening(lig);
    None
}

/// Verify the witness opening against a unified list of [`VerifyClaim`]s (mirror
/// of [`open`]). When the list carries a [`VerifyClaim::RingSwitch`] bundle
/// (BLAKE3 present), flock's ring-switched `(ab, c)` claims are verified in the
/// SAME stacked Ligerito as the point claims; otherwise the plain hinted opening
/// is verified.
pub fn verify(vs: &mut VerifierState, claims: &[VerifyClaim], mu: usize, root: &[u8; 32]) -> Result<(), Error> {
    // Split the unified list (order-preserving, mirroring `open`).
    let points: Vec<SlotClaim> = claims
        .iter()
        .filter_map(|cl| match cl {
            VerifyClaim::Point(s) => Some(s.clone()),
            VerifyClaim::RingSwitch(_) => None,
        })
        .collect();
    let ring = claims.iter().find_map(|cl| match cl {
        VerifyClaim::RingSwitch(r) => Some(r),
        VerifyClaim::Point(_) => None,
    });

    if let Some(rs) = ring {
        let commitment = commitment_from_root(*root, mu);
        let stack_pd: Vec<StackClaim> = points.iter().map(|s| s.as_stack()).collect();
        let x_refs: Vec<&[F128]> = rs.x_outers.iter().map(|v| v.as_slice()).collect();
        let cfg = lig_configs(mu);
        return verify_opening_batch_mixed_ligerito_stacked(
            &commitment,
            rs.offset,
            rs.qpkd_vars,
            &rs.values,
            &rs.z_skips,
            &x_refs,
            &stack_pd,
            rs.open,
            &cfg.1,
            vs,
        )
        .map_err(|_| Error::Ligerito);
    }

    // The commitment root was bound at the protocol's start (read_commitment);
    // λ is sampled bound to every claim (values already on the stream).
    let lambda = vs.sample();

    let mut target = F128::ZERO;
    let mut lambda_pow = F128::ONE;
    for c in &points {
        target += lambda_pow * c.value();
        lambda_pow *= lambda;
    }

    let lig = vs.next_opening().map_err(|_| Error::MissingHint)?;
    let cfg = lig_configs(mu);
    // The succinct Ligerito verifier calls back for `W_λ` at the residual points
    // `x = ris ++ y_bits`: `W_λ(x) = Σ_j λ^j eq(point_j, x)`, where each claim's
    // full point is its low point followed by the slot's boolean selector bits
    // (the same formula the old Ligerito `final_b` check used at its folding point).
    let eval_b_residual = |ris: &[F128], yr_log_n: usize| -> Vec<F128> {
        (0..1usize << yr_log_n)
            .map(|y| {
                let mut x = Vec::with_capacity(mu);
                x.extend_from_slice(ris);
                for k in 0..yr_log_n {
                    x.push(F128::new(((y >> k) & 1) as u64, 0));
                }
                let mut acc = F128::ZERO;
                let mut lambda_pow = F128::ONE;
                for claim in &points {
                    let (offset, low_point, _) = claim.dense();
                    let n_vars = low_point.len();
                    let mut eq = eq_eval(&low_point, &x[..n_vars]);
                    let selector = offset >> n_vars;
                    for (bit, &xi) in x[n_vars..mu].iter().enumerate() {
                        // eq(sel_bit, x): x if the bit is 1, else 1+x (char 2).
                        eq *= if (selector >> bit) & 1 == 1 { xi } else { F128::ONE + xi };
                    }
                    acc += lambda_pow * eq;
                    lambda_pow *= lambda;
                }
                acc
            })
            .collect()
    };
    let ok = ligerito::recursive_verifier_with_basis_succinct(&cfg.1, lig, mu, target, root, eval_b_residual, vs);
    if !ok {
        return Err(Error::Ligerito);
    }
    Ok(())
}
