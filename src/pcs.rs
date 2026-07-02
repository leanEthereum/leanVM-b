//! Witness commitment: an inner-product PCS over F_{2^128} (doc §3).
//!
//! We reuse flock's BaseFold (Reed-Solomon + Merkle + FRI) as the scheme:
//! `commit` encodes the F128 message, and an opening proves the inner product
//! `Σ_x q(x)·W(x) = C` against any verifier-evaluable weight `W`, by sumcheck
//! folding in lockstep with the FRI folds (a plain point evaluation `q̂(r)` is
//! the case `W = eq(r,·)`).
//!
//! For a batch of claims `q̂(point_j) = value_j` we fold them with a random `λ`
//! into one weight `W_λ = Σ_j λ^j eq(point_j,·)` and target `C_λ = Σ_j λ^j
//! value_j`, and run a single BaseFold opening on `Σ_x q(x)·W_λ(x) = C_λ`
//! directly, with no separate reduction sumcheck. Its final weight value
//! `final_b` is checked against `W_λ(ρ) = Σ_j λ^j eq(point_j, ρ)` at the folding
//! point `ρ`.

use crate::field::F128;
use crate::multilinear::{eq_eval, eq_table};
use crate::transcript::{Absorb, ProverState, VerifierState};
use rayon::prelude::*;

use flare::ntt::AdditiveNttF128;
use flare::pcs::basefold::{self, default_fri_queries};
pub use flare::pcs::{Commitment, PcsParams, ProverData};

/// flock frames `commit` as `m = log2(len) + LOG_PACKING`; the message length is
/// `2^(m - LOG_PACKING)`, so for an F-valued witness of `2^μ` elements we set
/// `m = μ + LOG_PACKING`.
const LOG_PACKING: usize = 7;
/// Row-batch lanes `2^LOG_BATCH`: also the Merkle leaf width (`2^LOG_BATCH`
/// F128/leaf). Larger ⇒ far fewer Merkle nodes to hash (faster commit/open) at
/// the cost of fatter query openings (proof size); soundness is unaffected
/// (rate + query count are fixed). 6 is flock's own default and the speed/size
/// knee at the 1–2M-instruction target scale.
const LOG_BATCH: usize = 6;
/// Rate `2^-1` ⇒ 243 FRI queries ⇒ 100-bit provable soundness (doc §3).
pub const LOG_INV_RATE: usize = 1;

fn params_for(mu: usize) -> PcsParams {
    assert!(mu >= 2, "witness needs ≥ 4 elements");
    // Clamp the batch (leaf width) to the witness; both parties derive the same
    // value from `mu`, so the commitment stays consistent.
    let log_batch_size = LOG_BATCH.min(mu - 1);
    // `profile` drives only the Ligerito opening; we use the BaseFold backend,
    // which ignores it. `Fast` is rate 1/2 (= our `log_inv_rate`).
    PcsParams {
        m: mu + LOG_PACKING,
        log_inv_rate: LOG_INV_RATE,
        log_batch_size,
        profile: flare::pcs::ligerito::LigeritoProfile::Fast,
    }
}

/// Rebuild the public [`Commitment`] (root + params) for a witness of `2^mu`
/// elements. The verifier reconstructs the params from `mu` exactly as `commit`
/// did, so the BLAKE3↔flock validity open (§blake3_flock) can verify its second
/// BaseFold against this same commitment.
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
    /// validity open (a second BaseFold over this same commitment, §blake3_flock)
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
#[derive(Clone, Debug)]
pub struct SlotClaim {
    pub offset: usize,
    pub low_point: Vec<F128>,
    pub value: F128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    BaseFold,
    FinalWeightMismatch,
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
    ps.write_scalars(&root_to_scalars(&commitment.root));
    Committed {
        commitment,
        prover_data,
        mu,
    }
}

/// Bind the batch of located claims (their values already rode the stream) and
/// derive the folding scalar `λ`. Shared shape so prover/verifier agree.
fn absorb_claims<T: Absorb>(s: &mut T, claims: &[SlotClaim]) -> F128 {
    s.observe_u64(claims.len() as u64);
    for c in claims {
        s.observe_scalars(&c.low_point);
        s.observe_u64(c.offset as u64);
        s.observe_scalars(std::slice::from_ref(&c.value));
    }
    s.sample()
}

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

/// Open a batch of located evaluation claims: hint the BaseFold opening (the
/// hash-bearing data) and bind the claims. The commitment root was already bound
/// at the protocol's start by [`commit`]; the claim *values* themselves already
/// travelled the stream as part of the bus/constraint arguments.
pub fn open(ps: &mut ProverState, c: &Committed, q: &[F128], claims: &[SlotClaim]) {
    let n = 1usize << c.mu;
    debug_assert_eq!(q.len(), n, "witness length must match the commitment");
    let lambda = absorb_claims(ps, claims);

    // W_λ over the cube and C_λ, built block-sparsely: each claim only writes
    // its column's slot, and eq-tables are cached across claims that share a
    // point (e.g. every column of one constraint table shares `rho`).
    let mut weight = vec![F128::ZERO; n];
    let mut target = F128::ZERO;
    let mut lambda_pow = F128::ONE; // running λ^j
    let mut eq_cache: Vec<(Vec<F128>, Vec<F128>)> = Vec::new();
    for claim in claims {
        let n_vars = claim.low_point.len();
        debug_assert!(claim.offset + (1 << n_vars) <= n, "slot out of range");
        let cache_idx = match eq_cache
            .iter()
            .position(|(point, _)| point.as_slice() == claim.low_point.as_slice())
        {
            Some(i) => i,
            None => {
                eq_cache.push((claim.low_point.clone(), eq_table(&claim.low_point)));
                eq_cache.len() - 1
            }
        };
        let offset = claim.offset;
        let eq_block = &eq_cache[cache_idx].1;
        weight[offset..offset + eq_block.len()]
            .par_iter_mut()
            .zip(eq_block.par_iter())
            .for_each(|(w, eq)| *w += lambda_pow * *eq);
        target += lambda_pow * claim.value;
        lambda_pow *= lambda;
    }

    let params = params_for(c.mu);
    let ntt = AdditiveNttF128::standard(params.k_code());
    let bf = basefold::prove(
        q,
        weight,
        target,
        &c.prover_data.codeword,
        &c.prover_data.merkle_tree,
        &ntt,
        params.log_inv_rate,
        params.log_batch_size,
        default_fri_queries(params.log_inv_rate),
        ps,
    );
    ps.hint_opening(bf);
}

/// Verify a batch opening read from `vs` against the hinted commitment.
pub fn verify(vs: &mut VerifierState, claims: &[SlotClaim], mu: usize, root: &[u8; 32]) -> Result<(), Error> {
    // The commitment root was bound at the protocol's start (read_commitment);
    // here we bind the claims and pull the BaseFold opening hint.
    let lambda = absorb_claims(vs, claims);

    let mut target = F128::ZERO;
    let mut lambda_pow = F128::ONE;
    for c in claims {
        target += lambda_pow * c.value;
        lambda_pow *= lambda;
    }

    let bf = vs.next_opening().map_err(|_| Error::MissingHint)?;
    let final_b = bf.final_b;
    let params = params_for(mu);
    let ntt = AdditiveNttF128::standard(params.k_code());
    let challenges = basefold::verify(target, bf, root, &ntt, params.log_inv_rate, params.log_batch_size, vs)
        .map_err(|_| Error::BaseFold)?;

    // final_b must equal W_λ(ρ) = Σ_j λ^j eq(point_j, ρ), where the point is the
    // low point followed by the slot's boolean selector bits.
    let mut weight_at_rho = F128::ZERO;
    let mut lambda_pow = F128::ONE;
    for claim in claims {
        let n_vars = claim.low_point.len();
        let mut eq = eq_eval(&claim.low_point, &challenges[..n_vars]);
        let selector = claim.offset >> n_vars;
        for (bit, &x) in challenges[n_vars..mu].iter().enumerate() {
            // eq(sel_bit, x): x if the bit is 1, else 1+x (char 2).
            eq *= if (selector >> bit) & 1 == 1 { x } else { F128::ONE + x };
        }
        weight_at_rho += lambda_pow * eq;
        lambda_pow *= lambda;
    }
    if final_b != weight_at_rho {
        return Err(Error::FinalWeightMismatch);
    }
    Ok(())
}
