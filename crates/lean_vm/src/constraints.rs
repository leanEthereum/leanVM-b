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
//! is what lets the forms' sums settle the bus. Batching derived in `doc/main.tex`
//! §sec:air. Both sides take `n = max τ_t` from the announced heights; a recursive
//! verifier certifies that maximum with one hinted `g`-power (§recursion), so there
//! are no rounds in which no table has joined.

use crate::PAR_THRESHOLD;
use crate::colval::ColVal;
use crate::transcript::{ProverState, VerifierState};
use primitives::field::{F64, F192, F192Unreduced, powers};
use primitives::multilinear::{
    add3, eq_table_arena, fold_high_inplace, fold_high_k, lagrange_eval, quad_nodes, shrink_eq_high, tri_nodes, xor3,
};
use zk_alloc::ArenaVec;

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

/// An active round for a table: evaluate its columns at the three nodes `{0,1,g}`.
///
/// Generic twice over: in the column element, `K` before a table's columns are
/// folded and `E` after ([`ColVal`]), and in the container, `Vec` for the former
/// and `ArenaVec` for the latter. `#[inline(always)]` matters here, on this and on
/// every `ColVal` method: this is the body of the constraint sumcheck's innermost
/// loop, and without it the generic stops inlining and costs measurable prover
/// time. Nothing is lifted into `E`, so a `K` round evaluates the identity and the
/// bus forms in 64-bit arithmetic, and its scratch is a third the size.
#[inline(always)]
fn table_message_all_nodes<T: ColVal, C: std::ops::Deref<Target = [T]> + Sync>(
    cols: &[C],
    eval: &(dyn Fn(&[F192], &[T]) -> F192 + Sync),
    pows: &[F192],
    half: usize,
    eqr: &[F192],
) -> [F192; 3] {
    let ncols = cols.len();
    let summand = |i: usize, scratch: &mut [T]| -> [F192Unreduced; 3] {
        let e = eqr[i];
        let (v0, rest) = scratch.split_at_mut(ncols);
        let (v1, v2) = rest.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            v0[ci] = lo;
            v1[ci] = hi;
            v2[ci] = T::at_g(lo, hi);
        }
        [
            e.mul_unreduced(eval(pows, v0)),
            e.mul_unreduced(eval(pows, v1)),
            e.mul_unreduced(eval(pows, v2)),
        ]
    };
    let acc = if half >= PAR_THRESHOLD {
        // The `3 * ncols` scratch is per-worker, not per-row: `map_reduce_with_state`
        // creates it once and threads it through every row that worker claims.
        parallel::map_reduce_with_state(
            half,
            || vec![T::ZERO; 3 * ncols],
            || [F192Unreduced::ZERO; 3],
            |scratch, acc, i| *acc = xor3(*acc, summand(i, scratch)),
            xor3,
        )
    } else {
        let mut scratch = vec![T::ZERO; 3 * ncols];
        (0..half).fold([F192Unreduced::ZERO; 3], |acc, i| xor3(acc, summand(i, &mut scratch)))
    };
    [acc[0].reduce(), acc[1].reduce(), acc[2].reduce()]
}

/// Evaluate one Boolean node and `g`. The other Boolean node is recovered from
/// the running sumcheck claim, so this removes one constraint evaluation at
/// every active row while preserving the four transmitted round values exactly.
#[inline(always)]
fn table_message_with_derived_boolean<T: ColVal, C: std::ops::Deref<Target = [T]> + Sync>(
    cols: &[C],
    eval: &(dyn Fn(&[F192], &[T]) -> F192 + Sync),
    pows: &[F192],
    half: usize,
    eqr: &[F192],
    derive_zero: bool,
) -> [F192; 2] {
    let ncols = cols.len();
    let summand = |i: usize, scratch: &mut [T]| -> [F192Unreduced; 2] {
        let e = eqr[i];
        let (vb, vg) = scratch.split_at_mut(ncols);
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            vb[ci] = if derive_zero { hi } else { lo };
            vg[ci] = T::at_g(lo, hi);
        }
        [e.mul_unreduced(eval(pows, vb)), e.mul_unreduced(eval(pows, vg))]
    };
    let acc = if half >= PAR_THRESHOLD {
        parallel::map_reduce_with_state(
            half,
            || vec![T::ZERO; 2 * ncols],
            || [F192Unreduced::ZERO; 2],
            |scratch, acc, i| {
                let value = summand(i, scratch);
                acc[0] ^= value[0];
                acc[1] ^= value[1];
            },
            |mut left, right| {
                left[0] ^= right[0];
                left[1] ^= right[1];
                left
            },
        )
    } else {
        let mut scratch = vec![T::ZERO; 2 * ncols];
        (0..half).fold([F192Unreduced::ZERO; 2], |mut acc, i| {
            let value = summand(i, &mut scratch);
            acc[0] ^= value[0];
            acc[1] ^= value[1];
            acc
        })
    };
    [acc[0].reduce(), acc[1].reduce()]
}

fn node_skip_mode(value: Option<&std::ffi::OsStr>) -> Result<bool, &'static str> {
    match value {
        None => Ok(false),
        Some(value) if value == std::ffi::OsStr::new("0") => Ok(false),
        Some(value) if value == std::ffi::OsStr::new("1") => Ok(true),
        Some(_) => Err("expected the literal value 0 or 1"),
    }
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
    let requested = std::env::var_os("LEANVM_CONSTRAINT_NODE_SKIP");
    let enabled = node_skip_mode(requested.as_deref())
        .unwrap_or_else(|reason| panic!("invalid LEANVM_CONSTRAINT_NODE_SKIP override: {reason}"));
    if requested.is_some() {
        eprintln!("LEANVM_CONSTRAINT_NODE_SKIP schema=1 enabled={enabled}");
    }
    prove_with_node_skip(airs, cols, eta, zeta, sigma, ps, enabled)
}

fn prove_with_node_skip(
    airs: &[Air<'_>],
    cols: &[Vec<&[F64]>],
    eta: F192,
    zeta: &[F192],
    sigma: &[F192],
    ps: &mut ProverState,
    node_skip: bool,
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
    let mut claim = sigma.iter().copied().fold(F192::ZERO, |acc, value| acc + value);
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
        let msg = if node_skip {
            // Normally recover p(0). If ζ_m = 1, its eq coefficient at zero
            // vanishes, so recover p(1) instead. One Boolean endpoint and g are
            // therefore sufficient for every field value without a fallback pass.
            let derive_zero = zeta[m] != F192::ONE;
            let mut sent = [F192::ZERO; 2];
            for (t, air) in airs.iter().enumerate() {
                if air.tau > m {
                    let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
                    let p = if let Some(table) = &folded[t] {
                        table_message_with_derived_boolean(table, &*air.eval, w, 1 << m, &eqr, derive_zero)
                    } else {
                        table_message_with_derived_boolean(&cols[t], &*air.eval_k, w, 1 << m, &eqr, derive_zero)
                    };
                    sent[0] += weights[t] * p[0];
                    sent[1] += weights[t] * p[1];
                }
            }
            if derive_zero {
                let p1 = sent[0];
                let h1 = zeta[m] * p1 + u;
                let p0 = (claim + h1) * (F192::ONE + zeta[m]).inv();
                [p0, p1, sent[1]]
            } else {
                debug_assert_eq!(zeta[m], F192::ONE);
                let p0 = sent[0];
                let h0 = (F192::ONE + zeta[m]) * p0;
                let p1 = claim + h0 + u;
                [p0, p1, sent[1]]
            }
        } else {
            let mut msg = [F192::ZERO; 3];
            for (t, air) in airs.iter().enumerate() {
                if air.tau > m {
                    let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
                    let p = if let Some(table) = &folded[t] {
                        table_message_all_nodes(table, &*air.eval, w, 1 << m, &eqr)
                    } else {
                        table_message_all_nodes(&cols[t], &*air.eval_k, w, 1 << m, &eqr)
                    };
                    msg = add3(msg, p.map(|x| weights[t] * x));
                }
            }
            msg
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
        debug_assert_eq!(h[0] + h[1], claim);
        // A separate pass: the challenge only exists once the message is bound.
        ps.add_scalars(&h);
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

/// Verify the batched zerocheck, returning the per-table claims for the caller to
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
        let h = vs.next_scalars(4).map_err(|_| Error::Truncated)?;
        if h[0] + h[1] != claim {
            return Err(Error::RoundInconsistent { round: j });
        }
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

    fn attached_proof_with_mode(
        taus: &[usize],
        cols: &[Vec<Vec<F64>>],
        eta: F192,
        zeta: &[F192],
        node_skip: bool,
    ) -> (Proof, Vec<Claims>, Vec<F192>) {
        let airs = airs_for(taus, true);
        let pows = powers(eta, 3 * taus.len());
        let sigmas: Vec<F192> = taus
            .iter()
            .enumerate()
            .map(|(t, &tau)| pows[3 * t + 2] * primitives::multilinear::mle_eval(&cols[t][1], &zeta[..tau]))
            .collect();
        let views: Vec<Vec<&[F64]>> = cols
            .iter()
            .map(|table| table.iter().map(|col| &col[..]).collect())
            .collect();
        let mut ps = ProverState::new(b"zc-node-skip-exactness", &SEED);
        let claims = prove_with_node_skip(&airs, &views, eta, zeta, &sigmas, &mut ps, node_skip);
        (ps.into_proof(), claims, sigmas)
    }

    #[test]
    fn claim_derived_node_skip_preserves_the_transcript() {
        let taus = [5usize, 3, 5, 0, 1];
        let cols: Vec<Vec<Vec<F64>>> = taus
            .iter()
            .enumerate()
            .map(|(i, &tau)| good_table(tau, i as u64))
            .collect();
        let (eta, ordinary_zeta) = eta_zeta(&taus);
        let mut exceptional_zeta = ordinary_zeta.clone();
        exceptional_zeta[0] = F192::ONE;
        exceptional_zeta[3] = F192::ONE;

        for zeta in [&ordinary_zeta, &exceptional_zeta] {
            let (all_nodes, all_claims, sigmas) = attached_proof_with_mode(&taus, &cols, eta, zeta, false);
            let (node_skip, skip_claims, skip_sigmas) = attached_proof_with_mode(&taus, &cols, eta, zeta, true);

            assert_eq!(sigmas, skip_sigmas);
            assert_eq!(all_nodes.stream, node_skip.stream);
            assert!(all_nodes.openings.is_empty());
            assert!(node_skip.openings.is_empty());
            assert_eq!(all_claims, skip_claims);

            let airs = airs_for(&taus, true);
            let target = sigmas.iter().copied().fold(F192::ZERO, |acc, value| acc + value);
            let mut vs = VerifierState::new(b"zc-node-skip-exactness", &node_skip, &SEED);
            assert_eq!(verify(&airs, eta, zeta, target, &mut vs), Ok(skip_claims));
        }
    }

    #[test]
    fn node_skip_override_parser_fails_closed() {
        use std::ffi::OsStr;

        assert_eq!(node_skip_mode(None), Ok(false));
        assert_eq!(node_skip_mode(Some(OsStr::new("0"))), Ok(false));
        assert_eq!(node_skip_mode(Some(OsStr::new("1"))), Ok(true));
        assert!(node_skip_mode(Some(OsStr::new("true"))).is_err());
        assert!(node_skip_mode(Some(OsStr::new("2"))).is_err());
        assert!(node_skip_mode(Some(OsStr::new(""))).is_err());
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
