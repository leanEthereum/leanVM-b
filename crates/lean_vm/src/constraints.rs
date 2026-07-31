//! The tables' local constraints (§4.1), proven by ONE sumcheck for all tables.
//!
//! Each table folds its identities with a DISJOINT range of one `η`'s powers, so
//! the batch is a polynomial in `η` whose coefficients are the individual sums and
//! a vanishing batch still pins each one. Tables of different heights are combined
//! by back-loaded batching: table `t`'s summand is lifted onto the common `n`-cube
//! by `∏_{i ≥ τ_t} X_i`, which leaves its hypercube sum alone. Rounds bind
//! `X_{n-1}` first, so table `t` sits out the first `n − τ_t` (contributing a
//! multiple of its claimed sum, which is zero) and joins at round `n − τ_t`
//! weighted by the challenges it sat out. Two payoffs: every table active in a
//! round binds the same variable, so one eq table serves the round and the message
//! stays 3 evaluations; and the claims land on nested points `ρ[..τ_t]`.
//!
//! Derivation in `misc/doc.tex` §sec:air. Both sides take `n = max τ_t` from the
//! announced heights; a recursive verifier certifies that maximum with one hinted
//! `g`-power (§recursion), so there are no rounds in which no table has joined.

use crate::PAR_THRESHOLD;
use primitives::field::{F128, mul_by_x};
use primitives::multilinear::{add3, build_eq, fold_high_inplace, lagrange_eval, shrink_eq_high, tri_nodes};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::Column;
use rayon::prelude::*;

/// One table's involved columns' evaluations at its zerocheck point (fixed column
/// order), reconstructed identically by prover and verifier.
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

/// A table's row constraint: identity `i` weighted by `pows[i]` (its slice of the
/// batch's `η`-powers), read off the involved columns' values.
pub type Constraint<'a> = Box<dyn Fn(&[F128], &[F128]) -> F128 + Sync + 'a>;

/// One table's place in the batch. Both sides build this list identically
/// ([`crate::cpu`]), so their rounds cannot drift apart.
pub struct Air<'a> {
    pub tau: usize,
    pub n_cols: usize,
    pub n_constraints: usize,
    pub eval: Constraint<'a>,
}

/// Where each table's disjoint range of `η`-powers starts: the exclusive prefix
/// sum of the identity counts. The recursion guest bakes these same offsets.
pub fn eta_offsets(n_constraints: impl Iterator<Item = usize>) -> Vec<usize> {
    n_constraints
        .scan(0usize, |off, n| {
            let start = *off;
            *off += n;
            Some(start)
        })
        .collect()
}

/// The batch's `η`-powers: `η^0 … η^{total-1}`, sliced per table by [`eta_offsets`].
fn eta_powers(eta: F128, total: usize) -> Vec<F128> {
    let mut pows = Vec::with_capacity(total);
    let mut p = F128::ONE;
    for _ in 0..total {
        pows.push(p);
        p *= eta;
    }
    pows
}

/// One table's degree-2 round message at the nodes `{0, 1, g}`; `half` is the
/// stride to the bound (highest) variable's `1` half. Char-2 makes the nodes free:
/// `lo`, `hi`, and `lo + mul_by_x(lo+hi)` — a shift-fold, no PMULL.
fn table_message(
    cols: &[Column],
    eval: &(dyn Fn(&[F128], &[F128]) -> F128 + Sync),
    pows: &[F128],
    half: usize,
    eqr: &[F128],
) -> [F128; 3] {
    let ncols = cols.len();
    let summand = |i: usize, scratch: &mut [F128]| -> [F128; 3] {
        let e = eqr[i];
        let (v0, rest) = scratch.split_at_mut(ncols);
        let (v1, v2) = rest.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            v0[ci] = lo;
            v1[ci] = hi;
            v2[ci] = lo + mul_by_x(lo + hi);
        }
        [e * eval(pows, v0), e * eval(pows, v1), e * eval(pows, v2)]
    };
    if half >= PAR_THRESHOLD {
        (0..half)
            .into_par_iter()
            .fold(
                || ([F128::ZERO; 3], vec![F128::ZERO; 3 * ncols]),
                |(acc, mut scratch), i| (add3(acc, summand(i, &mut scratch)), scratch),
            )
            .map(|(acc, _)| acc)
            .reduce(|| [F128::ZERO; 3], add3)
    } else {
        let mut scratch = vec![F128::ZERO; 3 * ncols];
        (0..half).fold([F128::ZERO; 3], |acc, i| add3(acc, summand(i, &mut scratch)))
    }
}

/// Prove that every table's batched constraint vanishes on all of its rows, as ONE
/// sumcheck over `max τ_t` variables. `cols[t]` holds table `t`'s involved columns
/// (`2^{τ_t}` values each, folded in place). Returns the per-table claims, in input
/// order, on the nested points `ρ[..τ_t]`.
pub fn prove(airs: &[Air<'_>], cols: &mut [Vec<Column>], ps: &mut ProverState) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let eta = ps.sample();
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());
    let zeta = ps.sample_vec(n);

    // η^{offset_t}, already inside `pows`; the rounds then fold in the pre-join
    // challenges and the eq factor, so `weights` is the whole per-table state.
    let mut weights = vec![F128::ONE; airs.len()];
    // ONE eq table over the low (still free) variables serves every active table.
    let mut eqr = build_eq(&zeta[..n.saturating_sub(1)]);
    let mut rho = vec![F128::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j; // the variable this round binds
        let mut msg = [F128::ZERO; 3];
        for (t, air) in airs.iter().enumerate() {
            if air.tau > m {
                let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
                let p = table_message(&cols[t], &*air.eval, w, 1 << m, &eqr);
                for k in 0..3 {
                    msg[k] += weights[t] * p[k];
                }
            }
        }
        shrink_eq_high(&mut eqr);
        // A separate pass: the challenge only exists once the message is bound.
        ps.add_scalars(&msg);
        let rk = ps.sample();
        rho[m] = rk;
        let eq_k = F128::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
            if air.tau > m {
                if m >= PAR_THRESHOLD.trailing_zeros() as usize {
                    cols[t].par_iter_mut().for_each(|c| fold_high_inplace(c, rk));
                } else {
                    cols[t].iter_mut().for_each(|c| fold_high_inplace(c, rk));
                }
            }
        }
    }

    airs.iter()
        .zip(cols.iter())
        .map(|(air, c)| {
            let evals: Vec<F128> = c.iter().map(|col| col[0]).collect();
            ps.add_scalars(&evals);
            Claims {
                rho: rho[..air.tau].to_vec(),
                evals,
            }
        })
        .collect()
}

/// Verify the batched zerocheck, returning the per-table claims for the caller to
/// settle against the commitment.
pub fn verify(airs: &[Air<'_>], vs: &mut VerifierState) -> Result<Vec<Claims>, Error> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let eta = vs.sample();
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());
    let zeta = vs.sample_vec(n);

    let nd = tri_nodes();
    let mut claim = F128::ZERO; // the batch's claimed sum: a zerocheck's is zero
    let mut weights = vec![F128::ONE; airs.len()];
    let mut rho = vec![F128::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        let p = vs.next_scalars(3).map_err(|_| Error::Truncated)?;
        // Only the product part travels; the round univariate is `eq(ζ[m], ·)·p`.
        if (F128::ONE + zeta[m]) * p[0] + zeta[m] * p[1] != claim {
            return Err(Error::RoundInconsistent { round: j });
        }
        let rk = vs.sample();
        rho[m] = rk;
        let eq_k = F128::ONE + zeta[m] + rk;
        claim = eq_k * lagrange_eval(&nd, &p, rk);
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
        }
    }

    let mut acc = F128::ZERO;
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

    /// Two identities, `c0·c1 + c2` and `c0 + c3`, so a table is satisfied exactly
    /// when `c2 = c0·c1` and `c3 = c0` on every row (characteristic 2).
    fn synth_eval(pows: &[F128], v: &[F128]) -> F128 {
        pows[0] * (v[0] * v[1] + v[2]) + pows[1] * (v[0] + v[3])
    }

    /// Rows satisfying both identities, from an arbitrary `(a, b)` per row.
    fn good_table(tau: usize, salt: u64) -> Vec<Column> {
        let n = 1usize << tau;
        let a: Vec<F128> = (0..n).map(|i| F128::new(i as u64 + salt, 7 * salt + 1)).collect();
        let b: Vec<F128> = (0..n).map(|i| F128::new(3 * i as u64 + 1, salt)).collect();
        let ab: Vec<F128> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
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

    const SEED: [F128; 2] = [F128::ONE, F128::ZERO];

    fn run(taus: &[usize], mut cols: Vec<Vec<Column>>) -> (Proof, Result<Vec<Claims>, Error>) {
        let airs = airs_for(taus);
        let mut ps = ProverState::new(b"zc-test", &SEED);
        let pclaims = prove(&airs, &mut cols, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::new(b"zc-test", &proof, &SEED);
        let vclaims = verify(&airs, &mut vs);
        if let Ok(vc) = &vclaims {
            assert_eq!(&pclaims, vc, "prover and verifier reconstruct the same claims");
        }
        (proof, vclaims)
    }

    /// Tables of DIFFERENT heights batch into one sumcheck, every claim landing on
    /// a prefix of the tallest table's point.
    #[test]
    fn ragged_batch_verifies() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols: Vec<Vec<Column>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let claims = run(&taus, cols).1.expect("honest batch verifies");
        let tallest = claims.iter().max_by_key(|c| c.rho.len()).unwrap().rho.clone();
        for (c, &tau) in claims.iter().zip(&taus) {
            assert_eq!(c.rho.len(), tau);
            assert_eq!(c.rho, tallest[..tau], "claims land on nested points");
        }
    }

    /// A single violated row in ANY table, including one whose padding rounds
    /// dominate, must be caught: the disjoint `eta` ranges stop the tables from
    /// cancelling.
    #[test]
    fn one_bad_row_in_any_table_is_rejected() {
        let taus = [5usize, 3, 5, 0, 1];
        for bad in 0..taus.len() {
            for col in [2usize, 3] {
                let mut cols: Vec<Vec<Column>> =
                    taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
                let row = (1usize << taus[bad]) - 1;
                cols[bad][col][row] += F128::ONE;
                assert!(
                    run(&taus, cols).1.is_err(),
                    "table {bad} column {col} violation must be rejected"
                );
            }
        }
    }

    /// Tampering any transmitted word breaks the chain: the batch is one sumcheck,
    /// so there is no per-table slack.
    #[test]
    fn tampered_transcript_is_rejected() {
        let taus = [4usize, 2, 4];
        let cols: Vec<Vec<Column>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (proof, ok) = run(&taus, cols);
        assert!(ok.is_ok());
        let airs = airs_for(&taus);
        for i in 0..proof.stream.len() {
            let mut bad = proof.clone();
            bad.stream[i] += F128::ONE;
            let mut vs = VerifierState::new(b"zc-test", &bad, &SEED);
            assert!(verify(&airs, &mut vs).is_err(), "tampered word {i} must be rejected");
        }
    }
}
