// CREDIT: The Jagged assist was cross-checked against Succinct Labs SP1's
// `slop/crates/jagged` implementation (MIT OR Apache-2.0):
// https://github.com/succinctlabs/sp1
//! Batch evaluations of the Basic-Jagged branching program.

use crate::{ProverState, VerifierState, VerifyError, jagged};
use primitives::{
    field::{F128, G},
    multilinear::{lagrange_eval, tri_nodes},
};

#[derive(Clone, Debug)]
pub(crate) struct Query {
    pub coefficient: F128,
    point: Vec<F128>,
}

impl Query {
    pub(crate) fn new(
        coefficient: F128,
        mut row_point: Vec<F128>,
        start: usize,
        end: usize,
        index_vars: usize,
    ) -> Option<Self> {
        if row_point.len() > index_vars {
            return None;
        }
        row_point.resize(index_vars, F128::ZERO);
        for value in [start, end] {
            row_point.extend(
                (0..=index_vars)
                    .map(|bit| F128::new(((value >> bit) & 1) as u64, 0)),
            );
        }
        Some(Self {
            coefficient,
            point: row_point,
        })
    }

    fn function_eval(
        &self,
        index_vars: usize,
        index_prefix: &[F128],
        final_message: &[F128],
    ) -> F128 {
        function_eval(&self.point, index_vars, index_prefix, final_message)
    }
}

fn function_eval(
    point: &[F128],
    index_vars: usize,
    index_prefix: &[F128],
    final_message: &[F128],
) -> F128 {
    let (row, endpoints) = point.split_at(index_vars);
    let (start, end) = endpoints.split_at(index_vars + 1);
    jagged::assisted_terminal_eval(row, start, end, index_prefix, final_message)
}

#[allow(clippy::too_many_arguments)]
fn round_eval(
    queries: &[Query],
    index_vars: usize,
    index_prefix: &[F128],
    final_message: &[F128],
    prefix: &[F128],
    prefix_weights: &[F128],
    round: usize,
    node: F128,
) -> F128 {
    use rayon::prelude::*;
    queries
        .par_iter()
        .zip(prefix_weights.par_iter())
        .map(|(query, &prefix_equality)| {
            let mut hybrid = query.point.clone();
            hybrid[..prefix.len()].copy_from_slice(prefix);
            hybrid[round] = node;
            query.coefficient
                * prefix_equality
                * (F128::ONE + node + query.point[round])
                * function_eval(&hybrid, index_vars, index_prefix, final_message)
        })
        .reduce(|| F128::ZERO, |a, b| a + b)
}

pub(crate) fn claimed_sum(
    queries: &[Query],
    index_vars: usize,
    index_prefix: &[F128],
    final_message: &[F128],
) -> F128 {
    queries.iter().fold(F128::ZERO, |acc, query| {
        acc + query.coefficient * query.function_eval(index_vars, index_prefix, final_message)
    })
}

pub(crate) fn prove(
    queries: &[Query],
    index_vars: usize,
    index_prefix: &[F128],
    final_message: &[F128],
    ps: &mut ProverState,
) {
    assert!(!queries.is_empty(), "Jagged assist needs at least one query");
    let dimensions = 3 * index_vars + 2;
    let mut claim = claimed_sum(queries, index_vars, index_prefix, final_message);
    ps.add_scalar(claim);
    let nodes = tri_nodes();
    let mut prefix = Vec::with_capacity(dimensions);
    let mut prefix_weights = vec![F128::ONE; queries.len()];
    for round in 0..dimensions {
        let at_zero = round_eval(
            queries,
            index_vars,
            index_prefix,
            final_message,
            &prefix,
            &prefix_weights,
            round,
            F128::ZERO,
        );
        let at_generator = round_eval(
            queries,
            index_vars,
            index_prefix,
            final_message,
            &prefix,
            &prefix_weights,
            round,
            G,
        );
        ps.add_scalars(&[at_zero, at_generator]);
        let challenge = ps.sample();
        claim = lagrange_eval(
            &nodes,
            &[at_zero, claim + at_zero, at_generator],
            challenge,
        );
        prefix.push(challenge);
        for (query, weight) in queries.iter().zip(&mut prefix_weights) {
            *weight *= F128::ONE + challenge + query.point[round];
        }
    }
    let batch_weight = queries.iter().fold(F128::ZERO, |acc, query| {
        acc + query.coefficient
            * query
                .point
                .iter()
                .zip(&prefix)
                .fold(F128::ONE, |weight, (&x, &r)| weight * (F128::ONE + x + r))
    });
    assert_eq!(
        claim,
        batch_weight * function_eval(&prefix, index_vars, index_prefix, final_message),
        "Jagged assist terminal",
    );
}

pub(crate) fn verify(
    required_claim: F128,
    queries: &[Query],
    index_vars: usize,
    index_prefix: &[F128],
    final_message: &[F128],
    vs: &mut VerifierState<'_>,
) -> Result<(), VerifyError> {
    let mut claim = vs.next_scalar().map_err(|_| VerifyError::JaggedAssist)?;
    if claim != required_claim {
        return Err(VerifyError::JaggedAssist);
    }
    let dimensions = 3 * index_vars + 2;
    let nodes = tri_nodes();
    let mut point = Vec::with_capacity(dimensions);
    for _ in 0..dimensions {
        let message = vs.next_scalars(2).map_err(|_| VerifyError::JaggedAssist)?;
        let challenge = vs.sample();
        claim = lagrange_eval(
            &nodes,
            &[message[0], claim + message[0], message[1]],
            challenge,
        );
        point.push(challenge);
    }
    let batch_weight = queries.iter().fold(F128::ZERO, |acc, query| {
        acc + query.coefficient
            * query
                .point
                .iter()
                .zip(&point)
                .fold(F128::ONE, |weight, (&x, &r)| weight * (F128::ONE + x + r))
    });
    let expected =
        batch_weight * function_eval(&point, index_vars, index_prefix, final_message);
    if claim != expected {
        return Err(VerifyError::JaggedAssist);
    }
    Ok(())
}
