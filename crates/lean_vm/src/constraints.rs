//! The tables' local constraints (§4.1), proven by ONE sumcheck for all tables.
//!
//! Each table folds its identities with a DISJOINT range of one `η`'s powers, so
//! the batch is a polynomial in `η` whose coefficients are the individual sums and
//! matching the batch's target still pins each one. The three bus forms are the
//! exception: they SHARE their three powers across tables
//! ([`crate::cpu::eta_form_base`]), so those coefficients are per-side totals and
//! the target pins the total, which is all the bus needs.
//!
//! Tables of different heights are combined by back-loaded batching: table `t`'s
//! summand is lifted onto the common `n`-cube by `∏_{i ≥ τ_t} X_i`, which leaves
//! its hypercube sum alone. Rounds bind `X_{n-1}` first, so table `t` sits out the
//! first `n − τ_t` and joins at round `n − τ_t` weighted by the challenges it sat
//! out. Two payoffs: every table active in a round has folded to the same size, so
//! ONE eq table serves the round; and the claims land on nested points `ρ[..τ_t]`.
//!
//! With nonzero sums the waiting tables stop dropping out: a waiting table's
//! variable reaches its summand once, through the padding product, so its
//! contribution is degree 1 in that variable and vanishes at 0, and all of them
//! share the same challenge product. The round polynomial is therefore the cubic
//! `eq(ζ_m, Y)·p(Y) + Y·u`, and it is sent WHOLE, at four nodes. That costs one
//! field element more than the degree-2 cofactor alone, and buys a verifier that
//! reapplies nothing: `h(0) + h(1) = claim`, then interpolate at the challenge.
//!
//! Two fields (§transition-to-64-bits): committed columns are `K`-valued and every
//! challenge is `E`-valued. A table's columns are still `K` on the round it JOINS,
//! so that round pairs `K` entries with the `E` eq-table through `mul_base` and
//! folds `K`-by-`E` into the `E` tables its later rounds consume. Back-loading
//! means the mixed round happens per table, at its own join round, rather than
//! once globally.

use crate::PAR_THRESHOLD;
use primitives::field::{F64, F128T, F128TUnreduced, mul_by_g, mul_by_g_e};
use primitives::multilinear::{
    eq_table, fold_high_inplace, fold_high_k, lagrange_eval, quad_nodes, shrink_eq_high, tri_nodes, xor3,
};
use crate::transcript::{ProverState, VerifierState};
use rayon::prelude::*;

/// One table's committed columns' evaluations at its zerocheck point (fixed column
/// order), reconstructed identically by prover and verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub rho: Vec<F128T>,
    pub evals: Vec<F128T>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    RoundInconsistent { round: usize },
    FinalMismatch,
}

/// A table's row constraint: identity `i` weighted by `pows[i]` (its slice of the
/// batch's `η`-powers), read off the involved columns' values.
pub type Constraint<'a> = Box<dyn Fn(&[F128T], &[F128T]) -> F128T + Sync + 'a>;

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
pub fn eta_powers(eta: F128T, total: usize) -> Vec<F128T> {
    let mut pows = Vec::with_capacity(total);
    let mut p = F128T::ONE;
    for _ in 0..total {
        pows.push(p);
        p *= eta;
    }
    pows
}

/// Sum `eq(ζ_lo, ·)·C` over the round's rows at the three nodes `{0, 1, g}`, with
/// `nodes` filling one row's three column-vectors. The outer `eq·C` products are
/// deferred: XOR-accumulate the unreduced Karatsuba parts and reduce once per node
/// after the sum (reduction commutes with XOR, so the message is bit-identical).
fn accumulate<N>(
    eval: &(dyn Fn(&[F128T], &[F128T]) -> F128T + Sync),
    pows: &[F128T],
    half: usize,
    ncols: usize,
    eqr: &[F128T],
    nodes: N,
) -> [F128T; 3]
where
    N: Fn(usize, &mut [F128T], &mut [F128T], &mut [F128T]) + Sync,
{
    let summand = |i: usize, scratch: &mut [F128T]| -> [F128TUnreduced; 3] {
        let e = eqr[i];
        let (v0, rest) = scratch.split_at_mut(ncols);
        let (v1, v2) = rest.split_at_mut(ncols);
        nodes(i, v0, v1, v2);
        [
            e.mul_unreduced(eval(pows, v0)),
            e.mul_unreduced(eval(pows, v1)),
            e.mul_unreduced(eval(pows, v2)),
        ]
    };
    let p_u = if half >= PAR_THRESHOLD {
        (0..half)
            .into_par_iter()
            .fold(
                || ([F128TUnreduced::ZERO; 3], vec![F128T::ZERO; 3 * ncols]),
                |(acc, mut scratch), i| (xor3(acc, summand(i, &mut scratch)), scratch),
            )
            .map(|(acc, _)| acc)
            .reduce(|| [F128TUnreduced::ZERO; 3], xor3)
    } else {
        let mut scratch = vec![F128T::ZERO; 3 * ncols];
        (0..half).fold([F128TUnreduced::ZERO; 3], |acc, i| xor3(acc, summand(i, &mut scratch)))
    };
    [p_u[0].reduce(), p_u[1].reduce(), p_u[2].reduce()]
}

/// The MIXED message, for the round a table joins on: its columns are still
/// `K`-valued. Interpolating to each node is free in char 2 (`lo`, `hi`, and
/// `lo + mul_by_g(lo+hi)`, a shift-fold, no PMULL), then each node's row lifts
/// into `E` for the constraint.
fn message_k(
    cols: &[Vec<F64>],
    eval: &(dyn Fn(&[F128T], &[F128T]) -> F128T + Sync),
    pows: &[F128T],
    half: usize,
    eqr: &[F128T],
) -> [F128T; 3] {
    accumulate(eval, pows, half, cols.len(), eqr, |i, v0, v1, v2| {
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            v0[ci] = F128T::from(lo);
            v1[ci] = F128T::from(hi);
            v2[ci] = F128T::from(lo + mul_by_g(lo + hi));
        }
    })
}

/// The pure-`E` message, for a table's rounds after it has joined.
fn message_e(
    cols: &[Vec<F128T>],
    eval: &(dyn Fn(&[F128T], &[F128T]) -> F128T + Sync),
    pows: &[F128T],
    half: usize,
    eqr: &[F128T],
) -> [F128T; 3] {
    accumulate(eval, pows, half, cols.len(), eqr, |i, v0, v1, v2| {
        for (ci, c) in cols.iter().enumerate() {
            let (lo, hi) = (c[i], c[i + half]);
            v0[ci] = lo;
            v1[ci] = hi;
            v2[ci] = lo + mul_by_g_e(lo + hi);
        }
    })
}

/// Prove that every table's batched constraint sums to its `sigma` over its own
/// rows, as ONE sumcheck over `max τ_t` variables. `cols[t]` holds table `t`'s
/// committed columns (`2^{τ_t}` `K`-values each), consumed destructively. Returns
/// the per-table claims, in input order, on the nested points `ρ[..τ_t]`.
pub fn prove(
    airs: &[Air<'_>],
    cols: Vec<Vec<Vec<F64>>>,
    eta: F128T,
    zeta: &[F128T],
    sigma: &[F128T],
    ps: &mut ProverState,
) -> Vec<Claims> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    debug_assert!(zeta.len() >= n, "the eq point must cover the tallest table");
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());

    let k_cols = cols;
    // `e_cols[t]` is empty until table `t` joins and its columns fold into `E`.
    let mut e_cols: Vec<Vec<Vec<F128T>>> = (0..airs.len()).map(|_| Vec::new()).collect();
    // η^{offset_t}, already inside `pows`; the rounds then fold in the pre-join
    // challenges and the eq factor, so `weights` is the whole per-table state.
    let mut weights = vec![F128T::ONE; airs.len()];
    // ONE eq table over the low (still free) variables serves every active table.
    let mut eqr = eq_table(&zeta[..n.saturating_sub(1)]);
    let mut rho = vec![F128T::ZERO; n];
    // `k`, the challenges drawn so far, common to every air that is still waiting.
    let mut k = F128T::ONE;
    let nd = tri_nodes();
    let q = quad_nodes();
    debug_assert_eq!(q[..3], nd[..], "the cubic's first three nodes are the cofactor's");
    for j in 0..n {
        let m = n - 1 - j; // the variable this round binds
        // The waiting airs contribute the line `Y·k·Σσ`, whose slope `u` is all
        // there is to it. It is NOT sent on its own: it folds into `h` below, and
        // only `h` travels.
        let waiting = airs.iter().zip(sigma).filter(|(a, _)| a.tau <= m).fold(F128T::ZERO, |acc, (_, &s)| acc + s);
        let u = k * waiting;
        let mut msg = [F128T::ZERO; 3];
        for (t, air) in airs.iter().enumerate() {
            if air.tau > m {
                let w = &pows[offsets[t]..offsets[t] + air.n_constraints];
                // `air.tau == m + 1` is this table's join round: still `K`-valued.
                let p = if air.tau == m + 1 {
                    message_k(&k_cols[t], &*air.eval, w, 1 << m, &eqr)
                } else {
                    message_e(&e_cols[t], &*air.eval, w, 1 << m, &eqr)
                };
                for i in 0..3 {
                    msg[i] += weights[t] * p[i];
                }
            }
        }
        shrink_eq_high(&mut eqr);
        // Assemble `h` and send it whole. The cofactor `p` is degree 2, so its
        // value at the fourth node is an interpolation of three scalars, NOT
        // another pass over the rows. `eq(a, b) = 1 + a + b` in char 2.
        let p4 = [msg[0], msg[1], msg[2], lagrange_eval(&nd, &msg, q[3])];
        let h: [F128T; 4] = std::array::from_fn(|i| (F128T::ONE + zeta[m] + q[i]) * p4[i] + q[i] * u);
        // A separate pass: the challenge only exists once the message is bound.
        ps.add_scalars(&h);
        let rk = ps.sample();
        rho[m] = rk;
        k *= rk;
        let eq_k = F128T::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
            if air.tau > m {
                if air.tau == m + 1 {
                    // The K-by-E fold, once per table, on the round it joins.
                    e_cols[t] = if (1 << m) >= PAR_THRESHOLD {
                        k_cols[t].par_iter().map(|c| fold_high_k(c, rk)).collect()
                    } else {
                        k_cols[t].iter().map(|c| fold_high_k(c, rk)).collect()
                    };
                } else if (1 << m) >= PAR_THRESHOLD {
                    e_cols[t].par_iter_mut().for_each(|c| fold_high_inplace(c, rk));
                } else {
                    e_cols[t].iter_mut().for_each(|c| fold_high_inplace(c, rk));
                }
            }
        }
    }

    airs.iter()
        .enumerate()
        .map(|(t, air)| {
            // A table of height 0 never joins, so its single row only lifts.
            let evals: Vec<F128T> = if air.tau == 0 {
                k_cols[t].iter().map(|c| F128T::from(c[0])).collect()
            } else {
                e_cols[t].iter().map(|c| c[0]).collect()
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
    eta: F128T,
    zeta: &[F128T],
    target: F128T,
    vs: &mut VerifierState,
) -> Result<Vec<Claims>, Error> {
    let n = airs.iter().map(|a| a.tau).max().unwrap_or(0);
    if zeta.len() < n {
        return Err(Error::Truncated);
    }
    let offsets = eta_offsets(airs.iter().map(|a| a.n_constraints));
    let pows = eta_powers(eta, airs.iter().map(|a| a.n_constraints).sum());

    let nd = quad_nodes();
    let mut weights = vec![F128T::ONE; airs.len()];
    // An ordinary sumcheck for `target`, which the caller supplies. Each round
    // arrives as the round polynomial itself at `nd`, so the two steps are the
    // textbook ones and nothing has to be reapplied: no eq factor, no separate
    // waiting term. `ζ` and the heights enter only `weights`, never the check.
    let mut claim = target;
    let mut rho = vec![F128T::ZERO; n];
    for j in 0..n {
        let m = n - 1 - j;
        let h = vs.next_scalars(4).map_err(|_| Error::Truncated)?;
        if h[0] + h[1] != claim {
            return Err(Error::RoundInconsistent { round: j });
        }
        let rk = vs.sample();
        rho[m] = rk;
        claim = lagrange_eval(&nd, &h, rk);
        let eq_k = F128T::ONE + zeta[m] + rk;
        for (t, air) in airs.iter().enumerate() {
            weights[t] *= if air.tau > m { eq_k } else { rk };
        }
    }

    let mut acc = F128T::ZERO;
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
