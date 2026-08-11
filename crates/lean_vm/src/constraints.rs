//! The tables' local constraints (§sec:air), proven by one sumcheck for all tables.
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
//! The eq point is the caller's, not a fresh one (the bus's GKR point `ζ`), which
//! is what lets the forms' sums settle the bus. Batching derived in `doc/leanvm/main.tex`
//! §sec:air. Both sides take `n = max τ_t` from the announced heights; a recursive
//! verifier certifies that maximum with one hinted `g`-power (§recursion), so there
//! are no rounds in which no table has joined.

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, powers};
use primitives::multilinear::{
    eq_table_arena, fold_high_inplace, fold_high_k, lagrange_eval, quad_nodes, shrink_eq_high, tri_nodes,
};
use zk_alloc::ArenaVec;

/// One table's involved columns' evaluations at its table-sumcheck point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub rho: Vec<F192>,
    pub evals: Vec<F192>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    FinalMismatch,
}

/// One table's row constraint: identity `i` is weighted by `pows[i]`.
pub type Constraint<'a> = Box<dyn Fn(&[F192], &[F192]) -> F192 + Sync + 'a>;
/// The same form over `K`-valued columns, for the round a table joins the batch.
pub type ConstraintK<'a> = Box<dyn Fn(&[F192], &[F64]) -> F192 + Sync + 'a>;

/// One table's place in the shared batch.
pub struct Air<'a> {
    pub tau: usize,
    pub n_cols: usize,
    pub n_constraints: usize,
    pub eval: Constraint<'a>,
    pub eval_k: ConstraintK<'a>,
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

/// An active round for a table: evaluate its columns at ONE Boolean node and at `g`.
///
/// The round's other Boolean value is never evaluated. `h(0) + h(1)` is the running
/// claim, so one endpoint of the cofactor `p` determines the other, and a row only
/// has to be read at the endpoint that is not derived. `at_one` picks it: normally
/// `p(1)`, since `h(0) = (1 + ζ_m)·p(0)` is what the claim then hands back, and at
/// `ζ_m = 1` that coefficient vanishes, so `p(0)` is evaluated and `p(1)` derived.
/// Both nodes still have to be GATHERED, `g` being their interpolation, but the
/// identity is evaluated twice per row instead of three times.
///
/// Generic twice over: in the column element, `K` before a table's columns are
/// folded and `E` after ([`ColVal`]), and in the container, `Vec` for the former
/// and `ArenaVec` for the latter. `#[inline(always)]` matters here, on this and on
/// every `ColVal` method: this is the body of the constraint sumcheck's innermost
/// loop, and without it the generic stops inlining and costs measurable prover
/// time. Nothing is lifted into `E`, so a `K` round evaluates the identity and the
/// bus forms in 64-bit arithmetic, and its scratch is a third the size.
#[inline(always)]
fn table_message<T: ColVal, C: std::ops::Deref<Target = [T]> + Sync>(
    cols: &[C],
    eval: &(dyn Fn(&[F192], &[T]) -> F192 + Sync),
    pows: &[F192],
    half: usize,
    eqr: &[F192],
    at_one: bool,
) -> [F192; 2] {
    let ncols = cols.len();
    let summand = |i: usize, scratch: &mut [T]| -> [F192Unreduced; 2] {
        let e = eqr[i];
        let (vb, vg) = scratch.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            vb[ci] = if at_one { hi } else { lo };
            vg[ci] = T::at_g(lo, hi);
        }
        [e.mul_unreduced(eval(pows, vb)), e.mul_unreduced(eval(pows, vg))]
    };
    let xor2 = |mut x: [F192Unreduced; 2], y: [F192Unreduced; 2]| {
        x[0] ^= y[0];
        x[1] ^= y[1];
        x
    };
    let acc = if half >= PAR_THRESHOLD {
        // The `2 * ncols` scratch is per-worker, not per-row: `map_reduce_with_state`
        // creates it once and threads it through every row that worker claims.
        parallel::map_reduce_with_state(
            half,
            || vec![T::ZERO; 2 * ncols],
            || [F192Unreduced::ZERO; 2],
            |scratch, acc, i| *acc = xor2(*acc, summand(i, scratch)),
            xor2,
        )
    } else {
        let mut scratch = vec![T::ZERO; 2 * ncols];
        (0..half).fold([F192Unreduced::ZERO; 2], |acc, i| xor2(acc, summand(i, &mut scratch)))
    };
    [acc[0].reduce(), acc[1].reduce()]
}

/// Prove that every table's batched constraint vanishes on all of its rows, as ONE
/// sumcheck over `max τ_t` variables. `cols[t]` holds table `t`'s involved columns
/// (`2^{τ_t}` values each, folded in place). Returns the per-table claims, in input
/// order, on the nested points `ρ[..τ_t]`.
pub fn prove(
    airs: &[Air<'_>],
    cols: &[Vec<&[F64]>],
    eta: F192,
    zeta: &[F192],
    sigma: &[F192],
    ps: &mut ProverState,
) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = powers(eta, airs.iter().map(|a| a.n_constraints).sum());
    // η^{offset_t}, already inside `pows`; the rounds then fold in the pre-join
    // challenges and the eq factor, so `weights` is the whole per-table state.
    let mut weights = vec![F192::ONE; airs.len()];
    // ONE eq table over the low (still free) variables serves every active table.
    let mut eqr = eq_table_arena(&zeta[..n.saturating_sub(1)]);
    let nd = tri_nodes();
    let mut rho = vec![F192::ZERO; n];
    // The folded tables are the batch's largest transients: one E-lifted copy of
    // every column of every still-active table. Arena-backed, so they are bumped
    // rather than mapped afresh each round.
    let mut folded: Vec<Option<Vec<ArenaVec<F192>>>> = (0..airs.len()).map(|_| None).collect();
    // `k`, the challenges drawn so far, common to every air that is still waiting.
    let mut k = F192::ONE;
    // The verifier's running claim, tracked here too: it is what supplies the
    // Boolean endpoint this round does not evaluate.
    let mut claim = sigma.iter().fold(F192::ZERO, |acc, &s| acc + s);
    for j in 0..n {
        let m = n - 1 - j; // the variable this round binds
        // The waiting airs contribute the line `Y·k·Σσ`, whose slope `u` is all there
        // is to it. It is NOT sent on its own: it folds into `h` below, and only `h`
        // travels. `msg` is the joined airs' degree-2 cofactor, `h`'s multiplicand.
        let waiting = airs
            .iter()
            .zip(sigma)
            .filter(|(a, _)| a.tau <= m)
            .fold(F192::ZERO, |acc, (_, &s)| acc + s);
        let u = k * waiting;
        // `h(0) = (1+ζ_m)·p(0)` and `h(1) = ζ_m·p(1) + u`, and the two sum to the
        // claim, so the rows only have to answer for one of them. `1+ζ_m` is the
        // coefficient that has to be inverted to recover `p(0)`, so the evaluated
        // node flips at the one point where it vanishes.
        let at_one = zeta[m] != F192::ONE;
        let mut sent = [F192::ZERO; 2];
        for (t, air) in airs.iter().enumerate() {
            if air.tau > m {
                let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
                let p = if let Some(table) = &folded[t] {
                    table_message(table, &*air.eval, w, 1 << m, &eqr, at_one)
                } else {
                    table_message(&cols[t], &*air.eval_k, w, 1 << m, &eqr, at_one)
                };
                sent[0] += weights[t] * p[0];
                sent[1] += weights[t] * p[1];
            }
        }
        let msg = if at_one {
            let p1 = sent[0];
            [(claim + zeta[m] * p1 + u) * (F192::ONE + zeta[m]).inv(), p1, sent[1]]
        } else {
            // `1 + ζ_m = 0` kills `h(0)` outright, leaving `h(1)` alone to carry the claim.
            [sent[0], claim + u, sent[1]]
        };
        shrink_eq_high(&mut eqr);
        // Assemble `h` and send it whole. The cofactor `p` is degree 2, so its value
        // at the fourth node is an interpolation of three scalars, NOT another pass
        // over the rows: the cheap message stays cheap and the verifier gets a
        // polynomial it can use as it stands. `eq(a, b) = 1 + a + b` in char 2.
        let q = quad_nodes();
        debug_assert_eq!(q[..3], nd[..], "the cubic's first three nodes are the cofactor's");
        let p4 = [msg[0], msg[1], msg[2], lagrange_eval(&nd, &msg, q[3])];
        let h: [F192; 4] = std::array::from_fn(|i| (F192::ONE + zeta[m] + q[i]) * p4[i] + q[i] * u);
        debug_assert_eq!(h[0] + h[1], claim, "the derived endpoint must close the round");
        // A separate pass: the challenge only exists once the message is bound.
        // `h(0)` does not ride the wire; `h(0) + h(1) = claim` fixes it.
        ps.add_round_poly(&h);
        let rk = ps.sample();
        claim = lagrange_eval(&q, &h, rk);
        rho[m] = rk;
        k *= rk;
        let eq_k = F192::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
            if air.tau <= m {
                continue;
            }
            if let Some(table) = &mut folded[t] {
                if m >= PAR_THRESHOLD.trailing_zeros() as usize {
                    let cols = parallel::Chunks::new(table, 1);
                    parallel::for_each(cols.count(), |ci| {
                        // SAFETY: column `ci` is folded by exactly one task.
                        let col = unsafe { &mut cols.get(ci)[0] };
                        fold_high_inplace(col, rk);
                    });
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

/// Verify the table sumcheck, returning the per-table claims for the caller to
/// settle against the commitment.
pub fn verify(
    airs: &[Air<'_>],
    eta: F192,
    zeta: &[F192],
    target: F192,
    vs: &mut VerifierState,
) -> Result<Vec<Claims>, Error> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    if zeta.len() < n {
        return Err(Error::Truncated);
    }
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = powers(eta, airs.iter().map(|a| a.n_constraints).sum());
    let nd = quad_nodes();
    let mut weights = vec![F192::ONE; airs.len()];
    // An ordinary sumcheck for `target`, which the caller supplies. Each round
    // arrives as the round polynomial itself at `nd`, so the two steps are the
    // textbook ones and nothing has to be reapplied: no eq factor, no separate
    // waiting term. `ζ` and the heights enter only `weights`, never the check.
    let mut claim = target;
    let mut rho = vec![F192::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        // `h(0)` is derived from the running claim rather than transmitted, so
        // the round-consistency check it used to enable holds by construction.
        let h = vs.next_round_poly(4, claim, None).map_err(|_| Error::Truncated)?;
        let rk = vs.sample();
        rho[m] = rk;
        claim = lagrange_eval(&nd, &h, rk);
        let eq_k = F192::ONE + zeta[m] + rk;
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

    fn synth_eval<T: crate::colval::ColVal>(pows: &[F192], v: &[T]) -> F192 {
        (v[0] * v[1] + v[2]).mul_e(pows[0]) + (v[0] + v[3]).mul_e(pows[1])
    }

    fn good_table(tau: usize, salt: u64) -> Vec<Vec<F64>> {
        let n = 1usize << tau;
        let a: Vec<F64> = (0..n).map(|i| F64(i as u64 + salt)).collect();
        let b: Vec<F64> = (0..n).map(|i| F64(3 * i as u64 + 1 + salt)).collect();
        let ab: Vec<F64> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        vec![a.clone(), b, ab, a]
    }

    /// A third, attached "identity": the linear form `vals[1]`, whose claimed sum
    /// is an evaluation of column 1 rather than zero.
    fn synth_eval_attached<T: crate::colval::ColVal>(pows: &[F192], v: &[T]) -> F192 {
        synth_eval(pows, v) + v[1].mul_e(pows[2])
    }

    fn airs_for(taus: &[usize], attached: bool) -> Vec<Air<'static>> {
        taus.iter()
            .map(|&tau| Air {
                tau,
                n_cols: 4,
                n_constraints: if attached { 3 } else { 2 },
                eval: Box::new(if attached {
                    synth_eval_attached::<F192>
                } else {
                    synth_eval::<F192>
                }),
                eval_k: Box::new(if attached {
                    synth_eval_attached::<F64>
                } else {
                    synth_eval::<F64>
                }),
            })
            .collect()
    }

    const SEED: [F192; 2] = [F192::ONE, F192::ZERO];

    /// The eq point and `η` are the caller's; the tests fix them.
    fn eta_zeta(taus: &[usize]) -> (F192, Vec<F192>) {
        let n = taus.iter().copied().max().unwrap_or(0);
        let eta = F192::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0, 7);
        let zeta = (0..n)
            .map(|i| F192::new(i as u64 + 3, 0x5555 * (i as u64 + 1), i as u64 + 11))
            .collect();
        (eta, zeta)
    }

    fn run(taus: &[usize], cols: Vec<Vec<Vec<F64>>>) -> (Proof, Result<Vec<Claims>, Error>) {
        let airs = airs_for(taus, false);
        let (eta, zeta) = eta_zeta(taus);
        let zeros = vec![F192::ZERO; taus.len()];
        let mut ps = ProverState::new(b"zc-test", &SEED);
        let views: Vec<Vec<&[F64]>> = cols.iter().map(|t| t.iter().map(|c| &c[..]).collect()).collect();
        let pclaims = prove(&airs, &views, eta, &zeta, &zeros, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::new(b"zc-test", &proof, &SEED);
        let vclaims = verify(&airs, eta, &zeta, F192::ZERO, &mut vs);
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
                let mut cols: Vec<Vec<Vec<F64>>> =
                    taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
                cols[bad][col][(1usize << taus[bad]) - 1] += F64::ONE;
                assert!(run(&taus, cols).1.is_err());
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
        let cols: Vec<Vec<Vec<F64>>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (eta, zeta) = eta_zeta(&taus);
        let pows = powers(eta, 3 * taus.len());
        // σ_t = η^{offset_t + 2} · col_1(ζ[..τ_t]): the attached identity is `vals[1]`,
        // so its eq-weighted sum over the table's cube is that column's evaluation.
        let sigmas: Vec<F192> = taus
            .iter()
            .enumerate()
            .map(|(t, &tau)| pows[3 * t + 2] * primitives::multilinear::mle_eval(&cols[t][1], &zeta[..tau]))
            .collect();

        let settle = |sig: &[F192], cols: Vec<Vec<Vec<F64>>>| -> Result<Vec<Claims>, Error> {
            let airs = airs_for(&taus, true);
            let target = sig.iter().fold(F192::ZERO, |a, &b| a + b);
            let mut ps = ProverState::new(b"zc-test", &SEED);
            let views: Vec<Vec<&[F64]>> = cols.iter().map(|t| t.iter().map(|c| &c[..]).collect()).collect();
            let pclaims = prove(&airs, &views, eta, &zeta, sig, &mut ps);
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
            wrong[bad] += F192::ONE;
            assert!(
                settle(&wrong, cols.clone()).is_err(),
                "a wrong claimed sum for table {bad} must be rejected"
            );
        }
    }

    /// `ζ_m = 1` is the one point where the round cannot derive `p(0)`, and a
    /// sampled `ζ` never lands on it, so the flipped branch is only ever reached
    /// here. `τ = 12` also puts the first round's half-table exactly at
    /// `PAR_THRESHOLD`, covering the parallel reducer alongside the serial one.
    #[test]
    fn unit_eq_coordinates_verify() {
        let taus = [12usize, 3, 5, 0, 1];
        let cols: Vec<Vec<Vec<F64>>> = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (eta, mut zeta) = eta_zeta(&taus);
        // First round, a middle round, and the last: the branch has to hold wherever
        // it falls, including a round in which short tables are still waiting.
        for m in [11usize, 3, 0] {
            zeta[m] = F192::ONE;
        }
        let pows = powers(eta, 3 * taus.len());
        let sigmas: Vec<F192> = taus
            .iter()
            .enumerate()
            .map(|(t, &tau)| pows[3 * t + 2] * primitives::multilinear::mle_eval(&cols[t][1], &zeta[..tau]))
            .collect();
        let airs = airs_for(&taus, true);
        let target = sigmas.iter().fold(F192::ZERO, |a, &b| a + b);
        let mut ps = ProverState::new(b"zc-test", &SEED);
        let views: Vec<Vec<&[F64]>> = cols.iter().map(|t| t.iter().map(|c| &c[..]).collect()).collect();
        let pclaims = prove(&airs, &views, eta, &zeta, &sigmas, &mut ps);
        let proof = ps.into_proof();
        let mut vs = VerifierState::new(b"zc-test", &proof, &SEED);
        assert_eq!(verify(&airs, eta, &zeta, target, &mut vs), Ok(pclaims));
    }

    /// Tampering any transmitted word breaks the chain: the batch is one sumcheck,
    /// so there is no per-table slack.
    #[test]
    fn tampered_transcript_is_rejected() {
        let taus = [4usize, 2, 4];
        let cols = taus.iter().enumerate().map(|(i, &t)| good_table(t, i as u64)).collect();
        let (proof, ok) = run(&taus, cols);
        assert!(ok.is_ok());
        let airs = airs_for(&taus, false);
        let (eta, zeta) = eta_zeta(&taus);
        for i in 0..proof.stream.len() {
            let mut bad = proof.clone();
            bad.stream[i] += F192::ONE;
            let mut vs = VerifierState::new(b"zc-test", &bad, &SEED);
            assert!(
                verify(&airs, eta, &zeta, F192::ZERO, &mut vs).is_err(),
                "tampered word {i} must be rejected"
            );
        }
    }
}
