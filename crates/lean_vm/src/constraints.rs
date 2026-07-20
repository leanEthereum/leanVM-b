//! Per-table local constraints (§4.1): a zerocheck of the row's degree-≤2 field
//! identities, batched by a verifier scalar `η` and run by sumcheck. The `eq`
//! weight is factored out (eq-trick), so each round univariate is degree 2, sent
//! as 3 evaluations and reweighted by the verifier. Columns are `K`-valued and
//! challenges `E`-valued: round 0 pairs `K`-entries with the `E`-tensor through
//! the mixed `mul_base` kernels, then folds every column into `E`; the later
//! rounds are pure `E`.

use crate::PAR_THRESHOLD;
use crate::transcript::{ProverState, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, mul_by_g, mul_by_g_e};
use primitives::multilinear::{eq_table, fold_low_inplace, fold_low_k, lagrange_eval, tri_nodes, xor3};
use rayon::prelude::*;

/// The involved columns' evaluations at the zerocheck point `rho` (fixed column
/// order), reconstructed identically by prover and verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub rho: Vec<F192>,
    /// Full-table evaluations used by the AIR formula (short committed columns
    /// are multiplied by their zero-suffix selector).
    pub evals: Vec<F192>,
    /// Evaluations actually opened against each committed column prefix.
    pub opening_evals: Vec<F192>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    RoundInconsistent { round: usize },
    FinalMismatch,
}

/// Prove the batched constraint vanishes on every row. `cols` are full-table,
/// zero-extended `K`-valued views (`2^tau` values each, in the order `c_eval`
/// expects); `claim_kappas` records the possibly shorter committed prefixes.
pub fn prove<F: Fn(F192, &[F192]) -> F192 + Sync>(
    cols: &[Vec<F64>],
    claim_kappas: &[usize],
    c_eval: F,
    ps: &mut ProverState,
) -> Claims {
    let tau = crate::log2_strict_usize(cols[0].len());
    assert_eq!(cols.len(), claim_kappas.len());
    assert!(claim_kappas.iter().all(|&k| k <= tau));
    let eta = ps.sample();
    let r = ps.sample_vec(tau);

    let ncols = cols.len();
    let mut rho = Vec::with_capacity(tau);

    // Round 0 (mixed): the round message is evaluated at the 3 nodes {0, 1, g},
    // where the interpolation of the K columns to each node is FREE (char-2): at
    // 0 it is `lo`, at 1 it is `hi`, and at the generator `g = x` it is
    // `lo + mul_by_g(lo+hi)` — a shift-fold, no PMULL. The three column-vectors
    // `v0..v2` (one contiguous scratch, split three ways) fill in a single pass
    // with no interpolation multiplies, then the constraint evaluates at each
    // node. Afterwards each column folds K-by-E into the E tables the remaining
    // rounds consume. A single-row table (tau = 0) just lifts.
    let mut tables: Vec<Vec<F192>> = if tau == 0 {
        cols.iter().map(|c| vec![F192::from(c[0])]).collect()
    } else {
        let half = cols[0].len() / 2;
        let eqr = eq_table(&r[1..]);
        // The outer eq·C products are deferred: XOR-accumulate the unreduced
        // Karatsuba parts and reduce once per node after the sum (reduction
        // commutes with XOR — bit-identical round messages).
        let summand = |i: usize, scratch: &mut [F192]| -> [F192Unreduced; 3] {
            let e = eqr[i];
            let (v0, rest) = scratch.split_at_mut(ncols);
            let (v1, v2) = rest.split_at_mut(ncols);
            for (ci, c) in cols.iter().enumerate() {
                let lo = c[2 * i];
                let hi = c[2 * i + 1];
                v0[ci] = F192::from(lo);
                v1[ci] = F192::from(hi);
                v2[ci] = F192::from(lo + mul_by_g(lo + hi));
            }
            [
                e.mul_unreduced(c_eval(eta, v0)),
                e.mul_unreduced(c_eval(eta, v1)),
                e.mul_unreduced(c_eval(eta, v2)),
            ]
        };
        let p_u = if half >= PAR_THRESHOLD {
            (0..half)
                .into_par_iter()
                .fold(
                    || ([F192Unreduced::ZERO; 3], vec![F192::ZERO; 3 * ncols]),
                    |(acc, mut scratch), i| (xor3(acc, summand(i, &mut scratch)), scratch),
                )
                .map(|(acc, _)| acc)
                .reduce(|| [F192Unreduced::ZERO; 3], xor3)
        } else {
            let mut scratch = vec![F192::ZERO; 3 * ncols];
            (0..half).fold([F192Unreduced::ZERO; 3], |acc, i| xor3(acc, summand(i, &mut scratch)))
        };
        let p = [p_u[0].reduce(), p_u[1].reduce(), p_u[2].reduce()];
        ps.add_scalars(&p);
        let rk = ps.sample();
        rho.push(rk);
        cols.iter().map(|c| fold_low_k(c, rk)).collect()
    };

    // Rounds 1.. (pure E): the same message over the folded E tables.
    for j in 1..tau {
        let half = tables[0].len() / 2;
        // Round message: the degree-2 product part `Σ_{x'} eq(r_{>j}, x')·C(t, x')`
        // at the 3 nodes {0, 1, g}; the verifier multiplies `eq(r_{≤j}, ·)` back.
        // The interpolation to each node is free (char-2): at 0 it is `lo`, at 1
        // it is `hi`, and at the generator `g = x` it is `lo + mul_by_g_e(lo+hi)`
        // — two shift-folds, no PMULL. So we fill the three column-vectors
        // `v0..v2` (one contiguous scratch, split three ways) in a single pass
        // with no interpolation multiplies, then evaluate the constraint at each
        // node.
        let eqr = eq_table(&r[j + 1..]);
        // Deferred as in round 0: unreduced eq·C accumulation, one reduction
        // per node per round message.
        let summand = |i: usize, scratch: &mut [F192]| -> [F192Unreduced; 3] {
            let e = eqr[i];
            let (v0, rest) = scratch.split_at_mut(ncols);
            let (v1, v2) = rest.split_at_mut(ncols);
            for (ci, c) in tables.iter().enumerate() {
                let lo = c[2 * i];
                let hi = c[2 * i + 1];
                v0[ci] = lo;
                v1[ci] = hi;
                v2[ci] = lo + mul_by_g_e(lo + hi);
            }
            [
                e.mul_unreduced(c_eval(eta, v0)),
                e.mul_unreduced(c_eval(eta, v1)),
                e.mul_unreduced(c_eval(eta, v2)),
            ]
        };
        let p_u = if half >= PAR_THRESHOLD {
            (0..half)
                .into_par_iter()
                .fold(
                    || ([F192Unreduced::ZERO; 3], vec![F192::ZERO; 3 * ncols]),
                    |(acc, mut scratch), i| (xor3(acc, summand(i, &mut scratch)), scratch),
                )
                .map(|(acc, _)| acc)
                .reduce(|| [F192Unreduced::ZERO; 3], xor3)
        } else {
            let mut scratch = vec![F192::ZERO; 3 * ncols];
            (0..half).fold([F192Unreduced::ZERO; 3], |acc, i| xor3(acc, summand(i, &mut scratch)))
        };
        let p = [p_u[0].reduce(), p_u[1].reduce(), p_u[2].reduce()];
        ps.add_scalars(&p);
        let rk = ps.sample();
        rho.push(rk);
        for c in tables.iter_mut() {
            fold_low_inplace(c, rk);
        }
    }

    let opening_evals: Vec<F192> = cols
        .iter()
        .zip(claim_kappas)
        .map(|(c, &k)| primitives::multilinear::mle_eval(&c[..1 << k], &rho[..k]))
        .collect();
    let evals: Vec<F192> = opening_evals
        .iter()
        .zip(claim_kappas)
        .map(|(&v, &k)| rho[k..].iter().fold(v, |acc, &r| acc * (F192::ONE + r)))
        .collect();
    debug_assert_eq!(evals, tables.iter().map(|c| c[0]).collect::<Vec<_>>());
    ps.add_scalars(&opening_evals);
    Claims {
        rho,
        evals,
        opening_evals,
    }
}

/// Verify the constraint zerocheck, returning the reconstructed claims (`rho` and
/// the column evals) for the caller to settle against the commitment.
pub fn verify<F: Fn(F192, &[F192]) -> F192>(
    tau: usize,
    ncols: usize,
    claim_kappas: &[usize],
    c_eval: F,
    vs: &mut VerifierState,
) -> Result<Claims, Error> {
    if claim_kappas.len() != ncols || claim_kappas.iter().any(|&k| k > tau) {
        return Err(Error::FinalMismatch);
    }
    let eta = vs.sample();
    let r = vs.sample_vec(tau);

    let nd = tri_nodes();
    let mut claim = F192::ZERO;
    let mut rho = Vec::with_capacity(tau);
    let mut eq_acc = F192::ONE; // ∏_{l<round} eq(r_l, ρ_l)
    for (round, &rj) in r.iter().enumerate() {
        let p = vs.next_scalars(3).map_err(|_| Error::Truncated)?;
        // The prover sent only the product part; the full round univariate is
        // `q(t) = eq_acc·eq(r_round, t)·p(t)`, so `q(0)+q(1)` must equal the claim.
        if eq_acc * ((F192::ONE + rj) * p[0] + rj * p[1]) != claim {
            return Err(Error::RoundInconsistent { round });
        }
        let rk = vs.sample();
        rho.push(rk);
        eq_acc *= F192::ONE + rj + rk;
        claim = eq_acc * lagrange_eval(&nd, &p, rk);
    }
    let opening_evals = vs.next_scalars(ncols).map_err(|_| Error::Truncated)?;
    let evals: Vec<F192> = opening_evals
        .iter()
        .zip(claim_kappas)
        .map(|(&v, &k)| rho[k..].iter().fold(v, |acc, &r| acc * (F192::ONE + r)))
        .collect();
    if claim != eq_acc * c_eval(eta, &evals) {
        return Err(Error::FinalMismatch);
    }
    Ok(Claims {
        rho,
        evals,
        opening_evals,
    })
}
