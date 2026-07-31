// CREDIT: The common-point opening reduction is adapted from Succinct Labs
// SP1's Hypercube shard zerocheck (MIT OR Apache-2.0):
// https://github.com/succinctlabs/sp1/tree/main/crates/hypercube/src
//! Local constraints (§4.1): a zerocheck of the row's degree-≤2 field
//! identities, batched by a verifier scalar `η` and run by sumcheck. The `eq`
//! weight is factored out (eq-trick), so each round univariate is degree 2.
//! Its consistency equation eliminates one coefficient, leaving two scalars.

use crate::PAR_THRESHOLD;
use crate::leaf::ColumnClaim;
use crate::tables::{self, Table};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::{Column, Placement};
use primitives::field::{F128, mul_by_x};
use primitives::multilinear::{
    add3, build_eq, fold_low_inplace, mle_eval, quadratic_coefficient,
    quadratic_eval_from_eq,
};
use rayon::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    FinalMismatch,
}

fn shifted_prefix(column: &[F128], pad: F128, height: usize, vars: usize) -> Vec<F128> {
    let mut out = vec![F128::ZERO; 1usize << vars];
    for (dst, &src) in out.iter_mut().zip(column).take(height) {
        *dst = src + pad;
    }
    out
}

fn opening_columns(bus_claims: &[ColumnClaim]) -> Vec<usize> {
    let sch = crate::cpu::schema();
    let mut columns = Vec::new();
    for claim in bus_claims.iter().filter(|claim| claim.prefix_shifted) {
        if !columns.contains(&claim.col) {
            columns.push(claim.col);
        }
    }
    for (t, table) in tables::tables().iter().enumerate() {
        for &local in table.constraint_columns() {
            let col = sch.base[t] + local;
            if !columns.contains(&col) {
                columns.push(col);
            }
        }
    }
    columns
}

struct GlobalTableWork<'a> {
    table: &'a dyn Table,
    eta: F128,
    coefficient: F128,
    pads: Vec<F128>,
    position: Vec<usize>,
    columns: Vec<Vec<F128>>,
    vars: usize,
}

struct GlobalBusWork {
    column: Vec<F128>,
    vars: usize,
}

/// SP1-style opening reduction: fold every ordinary bus evaluation into the
/// AIR zerocheck, so all ordinary columns are finally opened at one point.
/// The common `eq(z, x)` factor stays outside the degree-two product part, hence
/// each round still sends only two independent coefficients.
pub fn prove_global(
    cols: &[Column],
    pad: &[F128],
    placements: &[Placement],
    bus_claims: &[ColumnClaim],
    ps: &mut ProverState,
) -> Vec<ColumnClaim> {
    let ordinary: Vec<&ColumnClaim> = bus_claims.iter().filter(|claim| claim.prefix_shifted).collect();
    let z = ordinary
        .first()
        .expect("the bus has ordinary committed claims")
        .point
        .clone();
    assert!(ordinary.iter().all(|claim| claim.point == z));
    let rounds = z.len();

    let table_set = tables::tables();
    let etas: Vec<F128> = (0..tables::tables().len()).map(|_| ps.sample()).collect();
    let theta = ps.sample();
    let mut power = F128::ONE;
    let mut claim = F128::ZERO;
    let mut bus_by_vars: std::collections::BTreeMap<usize, Vec<F128>> = std::collections::BTreeMap::new();
    for opening in ordinary {
        claim += power * opening.value;
        let placement = placements[opening.col];
        let vars = primitives::log2_ceil_usize(placement.height.max(1));
        let aggregate = bus_by_vars
            .entry(vars)
            .or_insert_with(|| vec![F128::ZERO; 1 << vars]);
        for (row, &value) in cols[opening.col].iter().take(placement.height).enumerate() {
            aggregate[row] += power * (value + pad[opening.col]);
        }
        power *= theta;
    }
    let mut bus_work: Vec<GlobalBusWork> = bus_by_vars
        .into_iter()
        .map(|(vars, column)| GlobalBusWork { column, vars })
        .collect();

    let sch = crate::cpu::schema();
    let mut table_work = Vec::with_capacity(table_set.len());
    for (t, table) in table_set.iter().enumerate() {
        let involved = table.constraint_columns();
        let vars = placements[sch.base[t] + involved[0]].n_vars;
        let position = tables::column_positions(involved);
        let mut work_cols = Vec::with_capacity(involved.len());
        let mut pads = Vec::with_capacity(involved.len());
        for &local in involved {
            let col = sch.base[t] + local;
            let placement = placements[col];
            work_cols.push(shifted_prefix(&cols[col], pad[col], placement.height, vars));
            pads.push(pad[col]);
        }
        table_work.push(GlobalTableWork {
            table: *table,
            eta: etas[t],
            coefficient: power,
            pads,
            position,
            columns: work_cols,
            vars,
        });
        power *= theta;
    }

    let mut rho = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let mut message = [F128::ZERO; 3];
        for work in &table_work {
            let future_zero = z[work.vars.max(round + 1)..]
                .iter()
                .fold(F128::ONE, |acc, &r| acc * (F128::ONE + r));
            let part = if round < work.vars {
                let half = work.columns[0].len() / 2;
                let eqr = build_eq(&z[round + 1..work.vars]);
                let summand = |row: usize, values: &mut [F128]| {
                    let (v0, rest) = values.split_at_mut(work.columns.len());
                    let (v1, vg) = rest.split_at_mut(work.columns.len());
                    for (c, column) in work.columns.iter().enumerate() {
                        let lo = column[2 * row];
                        let hi = column[2 * row + 1];
                        v0[c] = lo + work.pads[c];
                        v1[c] = hi + work.pads[c];
                        vg[c] = lo + mul_by_x(lo + hi) + work.pads[c];
                    }
                    let weight = eqr[row] * future_zero;
                    [
                        weight
                            * work
                                .table
                                .eval_constraint(work.eta, &tables::Cols::new(v0, &work.position)),
                        weight
                            * work
                                .table
                                .eval_constraint(work.eta, &tables::Cols::new(v1, &work.position)),
                        weight
                            * work
                                .table
                                .eval_constraint(work.eta, &tables::Cols::new(vg, &work.position)),
                    ]
                };
                if half >= PAR_THRESHOLD {
                    (0..half)
                        .into_par_iter()
                        .fold(
                            || ([F128::ZERO; 3], vec![F128::ZERO; 3 * work.columns.len()]),
                            |(acc, mut scratch), row| (add3(acc, summand(row, &mut scratch)), scratch),
                        )
                        .map(|(acc, _)| acc)
                        .reduce(|| [F128::ZERO; 3], add3)
                } else {
                    let mut scratch = vec![F128::ZERO; 3 * work.columns.len()];
                    (0..half).fold([F128::ZERO; 3], |acc, row| add3(acc, summand(row, &mut scratch)))
                }
            } else {
                let mut values = vec![F128::ZERO; 3 * work.columns.len()];
                let (v0, rest) = values.split_at_mut(work.columns.len());
                let (v1, vg) = rest.split_at_mut(work.columns.len());
                for (c, column) in work.columns.iter().enumerate() {
                    let h = column[0];
                    v0[c] = h + work.pads[c];
                    v1[c] = work.pads[c];
                    vg[c] = (F128::ONE + F128::generator()) * h + work.pads[c];
                }
                [
                    future_zero
                        * work
                            .table
                            .eval_constraint(work.eta, &tables::Cols::new(v0, &work.position)),
                    future_zero
                        * work
                            .table
                            .eval_constraint(work.eta, &tables::Cols::new(v1, &work.position)),
                    future_zero
                        * work
                            .table
                            .eval_constraint(work.eta, &tables::Cols::new(vg, &work.position)),
                ]
            };
            for i in 0..3 {
                message[i] += work.coefficient * part[i];
            }
        }
        for work in &bus_work {
            let future_zero = z[work.vars.max(round + 1)..]
                .iter()
                .fold(F128::ONE, |acc, &r| acc * (F128::ONE + r));
            let part = if round < work.vars {
                let half = work.column.len() / 2;
                let eqr = build_eq(&z[round + 1..work.vars]);
                let summand = |row: usize| {
                    let lo = work.column[2 * row];
                    let hi = work.column[2 * row + 1];
                    let weight = eqr[row] * future_zero;
                    [weight * lo, weight * hi, weight * (lo + mul_by_x(lo + hi))]
                };
                if half >= PAR_THRESHOLD {
                    (0..half).into_par_iter().map(summand).reduce(|| [F128::ZERO; 3], add3)
                } else {
                    (0..half).fold([F128::ZERO; 3], |acc, row| add3(acc, summand(row)))
                }
            } else {
                let h = work.column[0] * future_zero;
                [h, F128::ZERO, (F128::ONE + F128::generator()) * h]
            };
            for i in 0..3 {
                message[i] += part[i];
            }
        }
        assert_eq!(
            (F128::ONE + z[round]) * message[0] + z[round] * message[1],
            claim
        );
        let compact = [message[0] + message[1], quadratic_coefficient(message)];
        ps.add_scalars(&compact);
        let challenge = ps.sample();
        claim =
            quadratic_eval_from_eq(claim, z[round], compact[0], compact[1], challenge);
        rho.push(challenge);
        rayon::join(
            || {
                table_work.par_iter_mut().for_each(|work| {
                    if round < work.vars {
                        for column in &mut work.columns {
                            fold_low_inplace(column, challenge);
                        }
                    } else {
                        for column in &mut work.columns {
                            column[0] *= F128::ONE + challenge;
                        }
                    }
                });
            },
            || {
                bus_work.par_iter_mut().for_each(|work| {
                    if round < work.vars {
                        fold_low_inplace(&mut work.column, challenge);
                    } else {
                        work.column[0] *= F128::ONE + challenge;
                    }
                });
            },
        );
    }

    let columns = opening_columns(bus_claims);
    let mut values = Vec::with_capacity(columns.len());
    for &col in &columns {
        let placement = placements[col];
        let vars = primitives::log2_ceil_usize(placement.height.max(1));
        let local = shifted_prefix(&cols[col], pad[col], placement.height, vars);
        let value =
            mle_eval(&local, &rho[..vars]) * rho[vars..].iter().fold(F128::ONE, |acc, &r| acc * (F128::ONE + r));
        ps.add_scalar(value);
        values.push(value);
    }

    let mut by_col = std::collections::HashMap::new();
    for (&col, &value) in columns.iter().zip(&values) {
        by_col.insert(col, value);
    }
    power = F128::ONE;
    let mut terminal = F128::ZERO;
    for opening in bus_claims.iter().filter(|claim| claim.prefix_shifted) {
        terminal += power * by_col[&opening.col];
        power *= theta;
    }
    for (t, table) in table_set.iter().enumerate() {
        let involved = table.constraint_columns();
        let position = tables::column_positions(involved);
        let evals: Vec<F128> = involved
            .iter()
            .map(|&local| by_col[&(sch.base[t] + local)] + pad[sch.base[t] + local])
            .collect();
        terminal += power * table.eval_constraint(etas[t], &tables::Cols::new(&evals, &position));
        power *= theta;
    }
    assert_eq!(claim, terminal);

    columns
        .into_iter()
        .zip(values)
        .map(|(col, value)| ColumnClaim {
            col,
            point: rho.clone(),
            value,
            prefix_shifted: true,
        })
        .collect()
}

pub fn verify_global(
    pad: &[F128],
    bus_claims: &[ColumnClaim],
    vs: &mut VerifierState,
) -> Result<Vec<ColumnClaim>, Error> {
    let ordinary: Vec<&ColumnClaim> = bus_claims.iter().filter(|claim| claim.prefix_shifted).collect();
    let z = ordinary
        .first()
        .expect("the bus has ordinary committed claims")
        .point
        .clone();
    if !ordinary.iter().all(|claim| claim.point == z) {
        return Err(Error::FinalMismatch);
    }
    let etas: Vec<F128> = (0..tables::tables().len()).map(|_| vs.sample()).collect();
    let theta = vs.sample();
    let mut power = F128::ONE;
    let mut claim = F128::ZERO;
    for opening in &ordinary {
        claim += power * opening.value;
        power *= theta;
    }

    let mut rho = Vec::with_capacity(z.len());
    for &zj in &z {
        let message = vs.next_scalars(2).map_err(|_| Error::Truncated)?;
        let challenge = vs.sample();
        rho.push(challenge);
        claim = quadratic_eval_from_eq(claim, zj, message[0], message[1], challenge);
    }

    let columns = opening_columns(bus_claims);
    let values = vs.next_scalars(columns.len()).map_err(|_| Error::Truncated)?;
    let by_col: std::collections::HashMap<usize, F128> = columns.iter().copied().zip(values.iter().copied()).collect();
    power = F128::ONE;
    let mut terminal = F128::ZERO;
    for opening in ordinary {
        terminal += power * by_col[&opening.col];
        power *= theta;
    }
    let sch = crate::cpu::schema();
    for (t, table) in tables::tables().iter().enumerate() {
        let involved = table.constraint_columns();
        let position = tables::column_positions(involved);
        let evals: Vec<F128> = involved
            .iter()
            .map(|&local| by_col[&(sch.base[t] + local)] + pad[sch.base[t] + local])
            .collect();
        terminal += power * table.eval_constraint(etas[t], &tables::Cols::new(&evals, &position));
        power *= theta;
    }
    if claim != terminal {
        return Err(Error::FinalMismatch);
    }

    Ok(columns
        .into_iter()
        .zip(values)
        .map(|(col, value)| ColumnClaim {
            col,
            point: rho.clone(),
            value,
            prefix_shifted: true,
        })
        .collect())
}
