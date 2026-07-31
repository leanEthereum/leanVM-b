//! The tables' local constraints (§4.1), proven by one sumcheck for all tables.
//!
//! Each table uses a disjoint range of one `η`'s powers. Tables of different
//! heights are combined by back-loaded batching: table `t` is lifted to the
//! common `n`-cube by `∏_{i ≥ τ_t} X_i`, then joins when the top-down sumcheck
//! reaches its highest variable. The resulting opening points are nested
//! prefixes of one `ρ`. Committed columns are `K`-valued (`F64`); the first
//! active fold lifts each table into the challenge field `E` (`F192`).

use crate::PAR_THRESHOLD;
use crate::transcript::{ProverState, VerifierState};
use crate::witness::Column;
use primitives::field::{F192, F192Unreduced, mul_by_g, mul_by_g_e};
use primitives::multilinear::{
    add3, eq_table, fold_high_inplace, fold_high_k, lagrange_eval, shrink_eq_high, tri_nodes, xor3,
};
use rayon::prelude::*;

/// One table's involved columns' evaluations at its zerocheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub rho: Vec<F192>,
    pub evals: Vec<F192>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    RoundInconsistent { round: usize },
    FinalMismatch,
}

/// One table's row constraint: identity `i` is weighted by `pows[i]`.
pub type Constraint<'a> = Box<dyn Fn(&[F192], &[F192]) -> F192 + Sync + 'a>;

/// One table's place in the shared batch.
pub struct Air<'a> {
    pub tau: usize,
    pub n_cols: usize,
    pub n_constraints: usize,
    pub eval: Constraint<'a>,
}

/// Start of each table's disjoint range of `η`-powers.
pub fn eta_offsets(n_constraints: impl Iterator<Item = usize>) -> Vec<usize> {
    n_constraints
        .scan(0usize, |off, n| {
            let start = *off;
            *off += n;
            Some(start)
        })
        .collect()
}

fn eta_powers(eta: F192, total: usize) -> Vec<F192> {
    let mut pows = Vec::with_capacity(total);
    let mut p = F192::ONE;
    for _ in 0..total {
        pows.push(p);
        p *= eta;
    }
    pows
}

/// First active round for a table: evaluate its `K` columns at `{0,1,g}`.
fn table_message_k(
    cols: &[Column],
    eval: &(dyn Fn(&[F192], &[F192]) -> F192 + Sync),
    pows: &[F192],
    half: usize,
    eqr: &[F192],
) -> [F192; 3] {
    let ncols = cols.len();
    let summand = |i: usize, scratch: &mut [F192]| -> [F192Unreduced; 3] {
        let e = eqr[i];
        let (v0, rest) = scratch.split_at_mut(ncols);
        let (v1, v2) = rest.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            v0[ci] = F192::from(lo);
            v1[ci] = F192::from(hi);
            v2[ci] = F192::from(lo + mul_by_g(lo + hi));
        }
        [
            e.mul_unreduced(eval(pows, v0)),
            e.mul_unreduced(eval(pows, v1)),
            e.mul_unreduced(eval(pows, v2)),
        ]
    };
    let acc = if half >= PAR_THRESHOLD {
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
    [acc[0].reduce(), acc[1].reduce(), acc[2].reduce()]
}

/// Later active rounds after the table has been lifted into `E`.
fn table_message_e(
    cols: &[Vec<F192>],
    eval: &(dyn Fn(&[F192], &[F192]) -> F192 + Sync),
    pows: &[F192],
    half: usize,
    eqr: &[F192],
) -> [F192; 3] {
    let ncols = cols.len();
    let summand = |i: usize, scratch: &mut [F192]| -> [F192Unreduced; 3] {
        let e = eqr[i];
        let (v0, rest) = scratch.split_at_mut(ncols);
        let (v1, v2) = rest.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            v0[ci] = lo;
            v1[ci] = hi;
            v2[ci] = lo + mul_by_g_e(lo + hi);
        }
        [
            e.mul_unreduced(eval(pows, v0)),
            e.mul_unreduced(eval(pows, v1)),
            e.mul_unreduced(eval(pows, v2)),
        ]
    };
    let acc = if half >= PAR_THRESHOLD {
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
    [acc[0].reduce(), acc[1].reduce(), acc[2].reduce()]
}

/// Prove all table constraints with one top-down sumcheck over `max τ_t` variables.
pub fn prove(airs: &[Air<'_>], cols: &mut [Vec<Column>], ps: &mut ProverState) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let eta = ps.sample();
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());
    let zeta = ps.sample_vec(n);
    let mut weights = vec![F192::ONE; airs.len()];
    let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
    let mut rho = vec![F192::ZERO; n];
    let mut folded: Vec<Option<Vec<Vec<F192>>>> = (0..airs.len()).map(|_| None).collect();

    for j in 0..n {
        let m = n - 1 - j;
        let mut msg = [F192::ZERO; 3];
        for (t, air) in airs.iter().enumerate() {
            if air.tau <= m {
                continue;
            }
            let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
            let p = if let Some(table) = &folded[t] {
                table_message_e(table, &*air.eval, w, 1 << m, &eqr)
            } else {
                table_message_k(&cols[t], &*air.eval, w, 1 << m, &eqr)
            };
            msg = add3(msg, p.map(|x| weights[t] * x));
        }
        shrink_eq_high(&mut eqr);
        ps.add_scalars(&msg);
        let rk = ps.sample();
        rho[m] = rk;
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
            if air.tau <= m {
                continue;
            }
            if let Some(table) = &mut folded[t] {
                if m >= PAR_THRESHOLD.trailing_zeros() as usize {
                    table.par_iter_mut().for_each(|c| fold_high_inplace(c, rk));
                } else {
                    table.iter_mut().for_each(|c| fold_high_inplace(c, rk));
                }
            } else {
                folded[t] = Some(cols[t].iter().map(|c| fold_high_k(c, rk)).collect());
            }
        }
    }

    airs.iter()
        .enumerate()
        .map(|(t, air)| {
            let evals: Vec<F192> = if let Some(table) = &folded[t] {
                table.iter().map(|c| c[0]).collect()
            } else {
                cols[t].iter().map(|c| F192::from(c[0])).collect()
            };
            ps.add_scalars(&evals);
            Claims {
                rho: rho[..air.tau].to_vec(),
                evals,
            }
        })
        .collect()
}

/// Verify the shared batched zerocheck and reconstruct its nested opening claims.
pub fn verify(airs: &[Air<'_>], vs: &mut VerifierState) -> Result<Vec<Claims>, Error> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let eta = vs.sample();
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());
    let zeta = vs.sample_vec(n);
    let nd = tri_nodes();
    let mut claim = F192::ZERO;
    let mut weights = vec![F192::ONE; airs.len()];
    let mut rho = vec![F192::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        let p = vs.next_scalars(3).map_err(|_| Error::Truncated)?;
        if (F192::ONE + zeta[m]) * p[0] + zeta[m] * p[1] != claim {
            return Err(Error::RoundInconsistent { round: j });
        }
        let rk = vs.sample();
        rho[m] = rk;
        let eq_k = F192::ONE + zeta[m] + rk;
        claim = eq_k * lagrange_eval(&nd, &p, rk);
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
        }
    }

    let mut acc = F192::ZERO;
    let mut claims = Vec::with_capacity(airs.len());
    for (t, air) in airs.iter().enumerate() {
        let evals = vs.next_scalars(air.n_cols).map_err(|_| Error::Truncated)?;
        let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
        acc += weights[t] * (air.eval)(w, &evals);
        claims.push(Claims {
            rho: rho[..air.tau].to_vec(),
            evals,
        });
    }
    if acc != claim {
        return Err(Error::FinalMismatch);
    }
    Ok(claims)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::{Proof, ProverState, VerifierState};
    use primitives::field::F64;

    fn synth_eval(pows: &[F192], v: &[F192]) -> F192 {
        pows[0] * (v[0] * v[1] + v[2]) + pows[1] * (v[0] + v[3])
    }

    fn good_table(tau: usize, salt: u64) -> Vec<Column> {
        let n = 1usize << tau;
        let a: Vec<F64> = (0..n).map(|i| F64(i as u64 + salt)).collect();
        let b: Vec<F64> = (0..n).map(|i| F64(3 * i as u64 + 1 + salt)).collect();
        let ab: Vec<F64> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        vec![a.clone(), b, ab, a]
    }

    fn airs_for(taus: &[usize]) -> Vec<Air<'static>> {
        taus.iter()
            .map(|&tau| Air {
                tau,
                n_cols: 4,
                n_constraints: 2,
                eval: Box::new(synth_eval),
            })
            .collect()
    }

    const SEED: [F192; 2] = [F192::ONE, F192::ZERO];

    fn run(taus: &[usize], mut cols: Vec<Vec<Column>>) -> (Proof, Result<Vec<Claims>, Error>) {
        let airs = airs_for(taus);
        let mut ps = ProverState::new(b"zc-test", &SEED);
        let pclaims = prove(&airs, &mut cols, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::new(b"zc-test", &proof, &SEED);
        let vclaims = verify(&airs, &mut vs);
        if let Ok(vc) = &vclaims {
            assert_eq!(&pclaims, vc);
        }
        (proof, vclaims)
    }

    #[test]
    fn ragged_batch_verifies() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let claims = run(&taus, cols).1.expect("honest batch verifies");
        let tallest = claims.iter().max_by_key(|c| c.rho.len()).unwrap().rho.clone();
        for (c, &tau) in claims.iter().zip(&taus) {
            assert_eq!(c.rho, tallest[..tau]);
        }
    }

    #[test]
    fn one_bad_row_in_any_table_is_rejected() {
        let taus = [5usize, 3, 5, 0, 1];
        for bad in 0..taus.len() {
            for col in [2usize, 3] {
                let mut cols: Vec<Vec<Column>> =
                    taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
                cols[bad][col][(1usize << taus[bad]) - 1] += F64::ONE;
                assert!(run(&taus, cols).1.is_err());
            }
        }
    }

    #[test]
    fn tampered_transcript_is_rejected() {
        let taus = [4usize, 2, 4];
        let cols = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (proof, ok) = run(&taus, cols);
        assert!(ok.is_ok());
        let airs = airs_for(&taus);
        for i in 0..proof.stream.len() {
            let mut bad = proof.clone();
            bad.stream[i] += F192::ONE;
            let mut vs = VerifierState::new(b"zc-test", &bad, &SEED);
            assert!(verify(&airs, &mut vs).is_err());
        }
    }
}
