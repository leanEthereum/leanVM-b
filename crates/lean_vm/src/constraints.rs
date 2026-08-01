//! The tables' local constraints (§4.1), proven by ONE sumcheck for all tables.
//!
//! Each table folds its identities with a DISJOINT range of one `η`'s powers, so
//! the batch is a polynomial in `η` whose coefficients are the individual sums and
//! matching the batch's target still pins each one. The three bus forms are the
//! exception: they SHARE their three powers across tables
//! ([`crate::cpu::eta_form_base`]), so those coefficients are per-side totals and
//! the target pins the total, which is all the bus needs. The identities vanish on a
//! valid row, but a table also attaches its three bus forms, whose sums are the
//! values the bus is owed, so the target is those rather than zero. It is the
//! caller's, not read off the stream: see [`crate::cpu::verify`].
//!
//! Tables of different heights are combined by back-loaded batching: table `t`'s
//! summand is lifted onto the common `n`-cube by `∏_{i ≥ τ_t} X_i`, which leaves
//! its hypercube sum alone. Rounds bind `X_{n-1}` first, so table `t` sits out the
//! first `n − τ_t` and joins at round `n − τ_t` weighted by the challenges it sat
//! out. Two payoffs: every table active in a round binds the same variable, so one
//! eq table serves the round; and the claims land on nested points `ρ[..τ_t]`.
//!
//! With nonzero sums the waiting tables stop dropping out: in a round it sits out, a
//! table's variable reaches its summand once, through the padding product, so its
//! contribution is degree 1 in that variable and vanishes at 0, and all of them
//! share the same challenge product. The round polynomial is therefore the cubic
//! `eq(ζ_m, Y)·p(Y) + Y·u`, and it is sent WHOLE, at four nodes. That costs one
//! field element more than the degree-2 cofactor alone, and buys a verifier that
//! reapplies nothing: `h(0) + h(1) = claim`, then interpolate at the challenge. No
//! round CHECK depends on a height or on `ζ`: those enter only the per-table
//! `weights`, which a verifier may accumulate as it goes or defer wholesale to the
//! end, as the recursion guest does. That is what a recursive verifier needs.
//!
//! The eq point is the caller's, not a fresh one — the bus's GKR point `ζ` — which
//! is what lets the forms' sums settle the bus. Batching derived in `misc/doc.tex`
//! §sec:air. Both sides take `n = max τ_t` from the announced heights; a recursive
//! verifier certifies that maximum with one hinted `g`-power (§recursion), so there
//! are no rounds in which no table has joined.

use crate::PAR_THRESHOLD;
use primitives::field::{F128, mul_by_x};
use primitives::multilinear::{add3, build_eq, fold_high_inplace, lagrange_eval, quad_nodes, shrink_eq_high, tri_nodes};
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
/// The caller needs these too, to weight the claims it attaches.
pub fn eta_powers(eta: F128, total: usize) -> Vec<F128> {
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
pub fn prove(
    airs: &[Air<'_>],
    cols: &mut [Vec<Column>],
    eta: F128,
    zeta: &[F128],
    sigma: &[F128],
    ps: &mut ProverState,
) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());

    // η^{offset_t}, already inside `pows`; the rounds then fold in the pre-join
    // challenges and the eq factor, so `weights` is the whole per-table state.
    let mut weights = vec![F128::ONE; airs.len()];
    // ONE eq table over the low (still free) variables serves every active table.
    let mut eqr = build_eq(&zeta[..n.saturating_sub(1)]);
    let nd = tri_nodes();
    let mut rho = vec![F128::ZERO; n];
    // `k`, the challenges drawn so far, common to every air that is still waiting.
    let mut k = F128::ONE;
    for j in 0..n {
        let m = n - 1 - j; // the variable this round binds
        // The waiting airs contribute the line `Y·k·Σσ`, whose slope `u` is all there
        // is to it. It is NOT sent on its own: it folds into `h` below, and only `h`
        // travels. `msg` is the joined airs' degree-2 cofactor, `h`'s multiplicand.
        let waiting = airs.iter().zip(sigma).filter(|(a, _)| a.tau <= m).fold(F128::ZERO, |acc, (_, &s)| acc + s);
        let u = k * waiting;
        let mut msg = [F128::ZERO; 3];
        for (t, air) in airs.iter().enumerate() {
            if air.tau > m {
                let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
                let p = table_message(&cols[t], &*air.eval, w, 1 << m, &eqr);
                for i in 0..3 {
                    msg[i] += weights[t] * p[i];
                }
            }
        }
        shrink_eq_high(&mut eqr);
        // Assemble `h` and send it whole. The cofactor `p` is degree 2, so its value
        // at the fourth node is an interpolation of three scalars, NOT another pass
        // over the rows: the cheap message stays cheap and the verifier gets a
        // polynomial it can use as it stands. `eq(a, b) = 1 + a + b` in char 2.
        let q = quad_nodes();
        debug_assert_eq!(q[..3], nd[..], "the cubic's first three nodes are the cofactor's");
        let p4 = [msg[0], msg[1], msg[2], lagrange_eval(&nd, &msg, q[3])];
        let h: [F128; 4] = std::array::from_fn(|i| (F128::ONE + zeta[m] + q[i]) * p4[i] + q[i] * u);
        // A separate pass: the challenge only exists once the message is bound.
        ps.add_scalars(&h);
        let rk = ps.sample();
        rho[m] = rk;
        k *= rk;
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
pub fn verify(
    airs: &[Air<'_>],
    eta: F128,
    zeta: &[F128],
    target: F128,
    vs: &mut VerifierState,
) -> Result<Vec<Claims>, Error> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    if zeta.len() < n {
        return Err(Error::Truncated);
    }
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());

    let nd = quad_nodes();
    let mut weights = vec![F128::ONE; airs.len()];
    // An ordinary sumcheck for `target`, which the caller supplies. Each round
    // arrives as the round polynomial itself at `nd`, so the two steps are the
    // textbook ones and nothing has to be reapplied: no eq factor, no separate
    // waiting term. `ζ` and the heights enter only `weights`, never the check.
    let mut claim = target;
    let mut rho = vec![F128::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        let h = vs.next_scalars(4).map_err(|_| Error::Truncated)?;
        if h[0] + h[1] != claim {
            return Err(Error::RoundInconsistent { round: j });
        }
        let rk = vs.sample();
        rho[m] = rk;
        claim = lagrange_eval(&nd, &h, rk);
        let eq_k = F128::ONE + zeta[m] + rk;
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

    /// A third, attached "identity": the linear form `vals[1]`, whose claimed sum
    /// is an evaluation of column 1 rather than zero.
    fn synth_eval_attached(pows: &[F128], v: &[F128]) -> F128 {
        synth_eval(pows, v) + pows[2] * v[1]
    }

    fn airs_for(taus: &[usize], attached: bool) -> Vec<Air<'static>> {
        taus.iter()
            .map(|&tau| Air {
                tau,
                n_cols: 4,
                n_constraints: if attached { 3 } else { 2 },
                eval: Box::new(if attached { synth_eval_attached } else { synth_eval }),
            })
            .collect()
    }

    const SEED: [F128; 2] = [F128::ONE, F128::ZERO];

    /// The eq point and `η` are the caller's; the tests fix them.
    fn eta_zeta(taus: &[usize]) -> (F128, Vec<F128>) {
        let n = taus.iter().copied().max().unwrap_or(0);
        let eta = F128::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0);
        let zeta = (0..n).map(|i| F128::new(i as u64 + 3, 0x5555 * (i as u64 + 1))).collect();
        (eta, zeta)
    }

    fn run(taus: &[usize], mut cols: Vec<Vec<Column>>) -> (Proof, Result<Vec<Claims>, Error>) {
        let airs = airs_for(taus, false);
        let (eta, zeta) = eta_zeta(taus);
        let zeros = vec![F128::ZERO; taus.len()];
        let mut ps = ProverState::new(b"zc-test", &SEED);
        let pclaims = prove(&airs, &mut cols, eta, &zeta, &zeros, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::new(b"zc-test", &proof, &SEED);
        let vclaims = verify(&airs, eta, &zeta, F128::ZERO, &mut vs);
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

    /// An ATTACHED evaluation claim: the extra identity's claimed
    /// sum is `η^2 · col_1(ζ[..τ])`, not zero, so the batch's target is nonzero and
    /// every table that has not joined yet rides a deferred line. Checks the honest
    /// batch verifies and that perturbing ANY table's claimed sum is caught,
    /// including a short table whose line is carried through most of the rounds.
    #[test]
    fn attached_eval_claims_verify_and_bind() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols: Vec<Vec<Column>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (eta, zeta) = eta_zeta(&taus);
        let pows = eta_powers(eta, 3 * taus.len());
        // σ_t = η^{offset_t + 2} · col_1(ζ[..τ_t]): the attached identity is `vals[1]`,
        // so its eq-weighted sum over the table's cube is that column's evaluation.
        let sigmas: Vec<F128> = taus
            .iter()
            .enumerate()
            .map(|(t, &tau)| pows[3 * t + 2] * primitives::multilinear::mle_eval(&cols[t][1], &zeta[..tau]))
            .collect();

        let settle = |sig: &[F128], mut cols: Vec<Vec<Column>>| -> Result<Vec<Claims>, Error> {
            let airs = airs_for(&taus, true);
            let target = sig.iter().fold(F128::ZERO, |a, &b| a + b);
            let mut ps = ProverState::new(b"zc-test", &SEED);
            let pclaims = prove(&airs, &mut cols, eta, &zeta, sig, &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::new(b"zc-test", &proof, &SEED);
            let out = verify(&airs, eta, &zeta, target, &mut vs);
            if let Ok(vc) = &out {
                assert_eq!(&pclaims, vc);
            }
            out
        };
        settle(&sigmas, cols.clone()).expect("honest attached claims verify");
        for bad in 0..taus.len() {
            let mut wrong = sigmas.clone();
            wrong[bad] += F128::ONE;
            assert!(
                settle(&wrong, cols.clone()).is_err(),
                "a wrong claimed sum for table {bad} must be rejected"
            );
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
        let airs = airs_for(&taus, false);
        let (eta, zeta) = eta_zeta(&taus);
        for i in 0..proof.stream.len() {
            let mut bad = proof.clone();
            bad.stream[i] += F128::ONE;
            let mut vs = VerifierState::new(b"zc-test", &bad, &SEED);
            assert!(
                verify(&airs, eta, &zeta, F128::ZERO, &mut vs).is_err(),
                "tampered word {i} must be rejected"
            );
        }
    }
}
