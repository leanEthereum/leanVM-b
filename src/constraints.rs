//! Per-table local constraints (§4.1): a zerocheck for a batch of degree-≤2
//! field identities over the row's committed columns.
//!
//! A table's constraints (the fp-relative addresses `addr = fp·o`, `XOR`'s sum,
//! `MUL_NATIVE`'s product, `JUMP`'s nonzero indicator and selection) are combined with
//! a verifier scalar `η` into one polynomial `C` over the columns, of degree
//! `≤ 2`. The parties run `Σ_x C(x)·eq(r,x) = 0` by sumcheck; the `eq` weight is
//! factored out (eq-trick), so each round univariate is degree 2, sent as 3
//! evaluations and reweighted by the verifier. The final claim needs the involved
//! columns' evaluations at the random point `ρ`; those are prover-supplied and
//! certified against the witness commitment by `crate::pcs`.
//!
//! `c_eval(η, vals)` is the public batched constraint: given the column values
//! at a row (in a fixed order) it returns `Σ_t η^{t-1} C_t`. Both parties share
//! it; the prover folds the columns through it, the verifier checks `C(ρ)`.

use crate::PAR_THRESHOLD;
use crate::field::F128;
use crate::multilinear::{add3, eq_table, fold_low_inplace, interp, lagrange_eval, tri_nodes};
use crate::transcript::{ProverState, VerifierState};
use rayon::prelude::*;

/// The involved columns' evaluations at the zerocheck point `ρ` (in the fixed
/// column order), plus `ρ`. Reconstructed identically by prover and verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub rho: Vec<F128>,
    pub evals: Vec<F128>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    RoundInconsistent { round: usize },
    FinalMismatch,
}

/// Prove the batched constraint vanishes on every row. `cols` are the involved
/// columns (each `2^τ` values, in the order `c_eval` expects). The batched
/// constraint is degree ≤2 and the `eq` weight is factored out, so each round
/// sends 3 evaluations (eq-trick, §sec:gkr).
pub fn prove<F: Fn(F128, &[F128]) -> F128 + Sync>(cols: &[Vec<F128>], c_eval: F, ps: &mut ProverState) -> Claims {
    let tau = crate::log2_strict_usize(cols[0].len());
    let eta = ps.sample();
    let r = ps.sample_vec(tau);

    let ncols = cols.len();
    let mut tables = cols.to_vec();
    let nd = tri_nodes();
    let mut rho = Vec::with_capacity(tau);

    for j in 0..tau {
        let half = tables[0].len() / 2;
        // The eq weight factors out (eq-trick, §sec:gkr): the round message is the
        // degree-2 `Σ_{x'} eq(r_{>j}, x')·C(t, x')` at the 3 nodes, and the verifier
        // multiplies `eq(r_{≤j}, ·)` back. `eqr` is eq over the variables after the
        // one bound this round; `vals` is a reused scratch buffer (the columns
        // interpolated to node `tt`), so there is no per-row allocation.
        let eqr = eq_table(&r[j + 1..]);
        let summand = |i: usize, vals: &mut [F128]| -> [F128; 3] {
            let mut acc = [F128::ZERO; 3];
            let e = eqr[i];
            for (ti, &tt) in nd.iter().enumerate() {
                for (ci, c) in tables.iter().enumerate() {
                    vals[ci] = interp(c[2 * i], c[2 * i + 1], tt);
                }
                acc[ti] = e * c_eval(eta, vals);
            }
            acc
        };
        let p = if half >= PAR_THRESHOLD {
            (0..half)
                .into_par_iter()
                .fold(
                    || ([F128::ZERO; 3], vec![F128::ZERO; ncols]),
                    |(acc, mut vals), i| (add3(acc, summand(i, &mut vals)), vals),
                )
                .map(|(acc, _)| acc)
                .reduce(|| [F128::ZERO; 3], add3)
        } else {
            let mut vals = vec![F128::ZERO; ncols];
            (0..half).fold([F128::ZERO; 3], |acc, i| add3(acc, summand(i, &mut vals)))
        };
        ps.write_scalars(&p);
        let rk = ps.sample();
        rho.push(rk);
        for c in tables.iter_mut() {
            fold_low_inplace(c, rk);
        }
    }

    let evals: Vec<F128> = tables.iter().map(|c| c[0]).collect();
    ps.write_scalars(&evals);
    Claims { rho, evals }
}

/// Verify the constraint zerocheck, reading the proof from `vs`. `ncols` is the
/// number of involved columns. Returns the reconstructed claims (`ρ` and the
/// column evals) for the caller to settle against the commitment.
pub fn verify<F: Fn(F128, &[F128]) -> F128>(
    tau: usize,
    ncols: usize,
    c_eval: F,
    vs: &mut VerifierState,
) -> Result<Claims, Error> {
    let eta = vs.sample();
    let r = vs.sample_vec(tau);

    let nd = tri_nodes();
    let mut claim = F128::ZERO;
    let mut rho = Vec::with_capacity(tau);
    let mut eq_acc = F128::ONE; // ∏_{l<round} eq(r_l, ρ_l)
    for round in 0..tau {
        let p = vs.next_scalars(3).map_err(|_| Error::Truncated)?;
        // The prover sent only the product part; the full round univariate is
        // `q(t) = eq_acc·eq(r_round, t)·p(t)`, so `q(0)+q(1)` must equal the claim.
        let rj = r[round];
        if eq_acc * ((F128::ONE + rj) * p[0] + rj * p[1]) != claim {
            return Err(Error::RoundInconsistent { round });
        }
        let rk = vs.sample();
        rho.push(rk);
        eq_acc *= F128::ONE + rj + rk; // ·= eq(r_round, ρ_round)
        claim = eq_acc * lagrange_eval(&nd, &p, rk); // = q(ρ_round)
    }
    let evals = vs.next_scalars(ncols).map_err(|_| Error::Truncated)?;
    // claim = eq(r,ρ)·C(ρ) now (eq_acc = eq(r,ρ)); bind the sent column evals.
    if claim != eq_acc * c_eval(eta, &evals) {
        return Err(Error::FinalMismatch);
    }
    Ok(Claims { rho, evals })
}
