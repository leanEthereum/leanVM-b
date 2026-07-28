// CREDIT: The width-four branching-program formulation was cross-checked
// against Succinct Labs SP1's `slop/crates/jagged` implementation
// (MIT OR Apache-2.0): https://github.com/succinctlabs/sp1
//! Basic Jagged PCS adapter primitives.
//!
//! A collection of columns with (possibly non-power-of-two) heights is packed
//! consecutively into one dense vector.  For a column occupying
//! `[start, end)`, [`indicator_eval`] evaluates the multilinear extension of
//! the map
//!
//! ```text
//! dense index i  ->  (row = i - start, column)
//! ```
//!
//! at an arbitrary row point and dense-index point.  This is the width-four
//! read-once branching program from the Basic Jagged construction: it checks
//! `index = start + row` and `index < end`, one little-endian bit at a time.

use primitives::field::F128;

#[inline]
fn step_fixed(
    [s0, s1, s2, s3]: [F128; 4],
    [w0, w1, w2, w3]: [F128; 4],
    start_bit: usize,
    end_bit: usize,
) -> [F128; 4] {
    match (start_bit, end_bit) {
        (0, 0) => [
            s0 * (w0 + w3) + (s1 + s3) * w2 + s2 * w3,
            s1 * w1,
            s2 * w0,
            s3 * w1,
        ],
        (0, 1) => [
            s0 * w3 + s1 * w2,
            F128::ZERO,
            s0 * w0 + s2 * (w0 + w3) + s3 * w2,
            (s1 + s3) * w1,
        ],
        (1, 0) => [
            (s0 + s2) * w2,
            s0 * w1 + s1 * (w0 + w3) + s3 * w3,
            F128::ZERO,
            s2 * w1 + s3 * w0,
        ],
        (1, 1) => [
            s0 * w2,
            s1 * w3,
            s2 * w2,
            (s0 + s2) * w1 + s1 * w0 + s3 * (w0 + w3),
        ],
        _ => unreachable!(),
    }
}

#[inline]
fn step_points(
    state: [F128; 4],
    row: F128,
    index: F128,
    start: F128,
    end: F128,
) -> [F128; 4] {
    let ri = row * index;
    let weights = [
        F128::ONE + row + index + ri,
        row + ri,
        index + ri,
        ri,
    ];
    let z0 = step_fixed(state, weights, 0, 0);
    let z1 = step_fixed(state, weights, 0, 1);
    let o0 = step_fixed(state, weights, 1, 0);
    let o1 = step_fixed(state, weights, 1, 1);
    std::array::from_fn(|out| {
        let at_start_zero = z0[out] + end * (z0[out] + z1[out]);
        let at_start_one = o0[out] + end * (o0[out] + o1[out]);
        at_start_zero + start * (at_start_zero + at_start_one)
    })
}

fn transition_matrix(
    row: F128,
    index: F128,
    start: F128,
    end: F128,
) -> [[F128; 4]; 4] {
    let mut matrix = [[F128::ZERO; 4]; 4];
    for input in 0..4 {
        let mut basis = [F128::ZERO; 4];
        basis[input] = F128::ONE;
        let output = step_points(basis, row, index, start, end);
        for out in 0..4 {
            matrix[out][input] = output[out];
        }
    }
    matrix
}

#[inline]
fn pull(matrix: &[[F128; 4]; 4], sink: &[F128; 4]) -> [F128; 4] {
    std::array::from_fn(|input| {
        (0..4).fold(F128::ZERO, |acc, out| {
            acc + matrix[out][input] * sink[out]
        })
    })
}

/// Evaluate the multilinear extension of the Basic-Jagged indicator when both
/// interval endpoints are arbitrary field points.
pub fn indicator_eval_with_endpoint_points(
    row_point: &[F128],
    start_point: &[F128],
    end_point: &[F128],
    index_point: &[F128],
) -> F128 {
    assert!(row_point.len() <= index_point.len());
    assert_eq!(start_point.len(), index_point.len() + 1);
    assert_eq!(end_point.len(), index_point.len() + 1);
    let mut state = [F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO];
    for bit in 0..=index_point.len() {
        state = step_points(
            state,
            row_point.get(bit).copied().unwrap_or(F128::ZERO),
            index_point.get(bit).copied().unwrap_or(F128::ZERO),
            start_point[bit],
            end_point[bit],
        );
    }
    state[2]
}

/// Contract one generalized Basic-Jagged evaluation against Ligerito's final
/// message. `index_prefix` contains the already-folded low coordinates; the
/// remaining index coordinates range over the Boolean entries of
/// `final_message`.
pub fn assisted_terminal_eval(
    row_point: &[F128],
    start_point: &[F128],
    end_point: &[F128],
    index_prefix: &[F128],
    final_message: &[F128],
) -> F128 {
    assert!(final_message.len().is_power_of_two());
    let residual_vars = final_message.len().trailing_zeros() as usize;
    let index_vars = index_prefix.len() + residual_vars;
    assert!(row_point.len() <= index_vars);
    assert_eq!(start_point.len(), index_vars + 1);
    assert_eq!(end_point.len(), index_vars + 1);

    let mut prefix_state = [F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO];
    for bit in 0..index_prefix.len() {
        prefix_state = step_points(
            prefix_state,
            row_point.get(bit).copied().unwrap_or(F128::ZERO),
            index_prefix[bit],
            start_point[bit],
            end_point[bit],
        );
    }

    // Pull the accepting state backwards through the fixed-zero overflow bit.
    let top = transition_matrix(
        F128::ZERO,
        F128::ZERO,
        start_point[index_vars],
        end_point[index_vars],
    );
    let accept = [F128::ZERO, F128::ZERO, F128::ONE, F128::ZERO];
    let top_sink = pull(&top, &accept);
    let mut layer: Vec<[F128; 4]> = final_message
        .iter()
        .map(|&message| top_sink.map(|value| message * value))
        .collect();

    // Pull the message tree backwards, one residual index bit at a time.
    for stage in 0..residual_vars {
        let bit = index_vars - 1 - stage;
        let half = layer.len() / 2;
        let row = row_point.get(bit).copied().unwrap_or(F128::ZERO);
        let left_matrix = transition_matrix(row, F128::ZERO, start_point[bit], end_point[bit]);
        let right_matrix = transition_matrix(row, F128::ONE, start_point[bit], end_point[bit]);
        let mut next = Vec::with_capacity(half);
        for i in 0..half {
            let left = pull(&left_matrix, &layer[i]);
            let right = pull(&right_matrix, &layer[i + half]);
            next.push(std::array::from_fn(|state| left[state] + right[state]));
        }
        layer = next;
    }

    (0..4).fold(F128::ZERO, |acc, state| {
        acc + prefix_state[state] * layer[0][state]
    })
}

/// Evaluate the MLE of `1[index = start + row && index < end]`.
///
/// `row_point` contains the low row coordinates; omitted high row coordinates
/// are fixed to zero. `index_point` is the point of the dense committed cube.
/// `start` and `end` are public cumulative column heights and must fit in that
/// cube.  `end == 2^index_point.len()` is supported by the extra top bit.
pub fn indicator_eval(row_point: &[F128], start: usize, end: usize, index_point: &[F128]) -> F128 {
    let row_weights: Vec<[F128; 2]> = row_point.iter().map(|&a| [F128::ONE + a, a]).collect();
    indicator_eval_with_row_weights(&row_weights, start, end, index_point)
}

/// [`indicator_eval`] with explicit `(zero, one)` weights for each logical-row
/// coordinate. The pairs need not sum to one. This lets a geometric column
/// batch use selector weights `(1, gamma^(2^b))` directly, absorbing all
/// normalization factors and avoiding exceptional inversions.
pub fn indicator_eval_with_row_weights(
    row_weights: &[[F128; 2]],
    start: usize,
    end: usize,
    index_point: &[F128],
) -> F128 {
    assert!(start <= end, "jagged column interval must be ordered");
    assert!(row_weights.len() <= index_point.len());
    assert!(end <= (1usize << index_point.len()));

    // State = (carry, comparison_so_far), indexed carry + 2*comparison.
    // `comparison_so_far` is the strict comparison index < end over the bits
    // processed so far; a more-significant differing bit overwrites it.
    let mut state = [F128::ZERO; 4];
    state[0] = F128::ONE;

    // One extra fixed-zero top bit handles an interval ending at 2^m and also
    // rejects an addition that carries out of the committed cube.
    for bit in 0..=index_point.len() {
        let b = index_point.get(bit).copied().unwrap_or(F128::ZERO);
        let c_bit = ((start >> bit) & 1) != 0;
        let d_bit = ((end >> bit) & 1) != 0;
        let a_weights = row_weights.get(bit).copied().unwrap_or([F128::ONE, F128::ZERO]);
        let b_weights = [F128::ONE + b, b];
        let mut next = [F128::ZERO; 4];

        for (state_idx, &state_weight) in state.iter().enumerate() {
            let carry = (state_idx & 1) != 0;
            let comparison = (state_idx & 2) != 0;
            for a_bit in 0..2 {
                for b_bit in 0..2 {
                    let sum = a_bit + usize::from(carry) + usize::from(c_bit);
                    if b_bit != (sum & 1) {
                        continue;
                    }
                    let next_carry = (sum >> 1) != 0;
                    let next_comparison = if (b_bit != 0) == d_bit { comparison } else { d_bit };
                    let next_idx = usize::from(next_carry) + 2 * usize::from(next_comparison);
                    next[next_idx] += state_weight * a_weights[a_bit] * b_weights[b_bit];
                }
            }
        }
        state = next;
    }

    // No final addition carry, and index < end.
    state[2]
}

/// Evaluate the MLE of the prefix indicator `1[index < height]` at `point`.
///
/// This is useful when a logical column has a public nonzero padding value:
/// the committed Jagged column contains only its real prefix, and the padding
/// contribution is removed from an evaluation claim in logarithmic time.
pub fn prefix_indicator_eval(height: usize, point: &[F128]) -> F128 {
    assert!(height <= (1usize << point.len()));
    if height == (1usize << point.len()) {
        return F128::ONE;
    }

    // MSB-first digit DP with two states: the sampled index is already less
    // than `height`, or it is still equal to the scanned prefix.
    let mut less = F128::ZERO;
    let mut equal = F128::ONE;
    for bit in (0..point.len()).rev() {
        let x = point[bit];
        if ((height >> bit) & 1) == 0 {
            equal *= F128::ONE + x;
        } else {
            less += equal * (F128::ONE + x);
            equal *= x;
        }
    }
    less
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::{build_eq, mle_eval};

    fn f(x: u64) -> F128 {
        F128::new(x, x.rotate_left(17))
    }

    #[test]
    fn indicator_matches_dense_table_mle() {
        for m in 1usize..=6 {
            let n = 1usize << m;
            for start in 0..n {
                for end in start..=n {
                    let row_vars = m.saturating_sub(1);
                    if end - start > (1usize << row_vars) {
                        continue;
                    }
                    let row_point: Vec<_> = (0..row_vars).map(|i| f((17 * start + 31 * end + i) as u64)).collect();
                    let index_point: Vec<_> = (0..m).map(|i| f((43 * start + 59 * end + i + 1) as u64)).collect();
                    let row_eq = build_eq(&row_point);
                    let mut table = vec![F128::ZERO; n];
                    table[start..end].copy_from_slice(&row_eq[..end - start]);
                    assert_eq!(
                        indicator_eval(&row_point, start, end, &index_point),
                        mle_eval(&table, &index_point),
                        "m={m}, interval=[{start},{end})",
                    );
                }
            }
        }
    }

    #[test]
    fn indicator_accepts_unnormalized_row_weights() {
        let index_point = [f(3), f(5), f(7), f(11)];
        let row_weights = [[F128::ONE, f(13)], [F128::ONE, F128::ONE], [f(17), f(19)]];
        let (start, end) = (3usize, 11usize);
        let index_eq = build_eq(&index_point);
        let mut expected = F128::ZERO;
        for index in start..end {
            let row = index - start;
            if row >= 1 << row_weights.len() {
                continue;
            }
            let mut weight = index_eq[index];
            for (bit, pair) in row_weights.iter().enumerate() {
                weight *= pair[(row >> bit) & 1];
            }
            expected += weight;
        }
        assert_eq!(
            indicator_eval_with_row_weights(&row_weights, start, end, &index_point),
            expected
        );
    }

    #[test]
    fn endpoint_point_evaluator_matches_boolean_intervals() {
        for m in 1usize..=6 {
            let n = 1usize << m;
            let row_point: Vec<_> = (0..m).map(|i| f((13 * m + i + 1) as u64)).collect();
            let index_point: Vec<_> = (0..m).map(|i| f((29 * m + i + 1) as u64)).collect();
            for start in 0..n {
                for end in start..=n {
                    let endpoint = |value: usize| {
                        (0..=m)
                            .map(|bit| F128::new(((value >> bit) & 1) as u64, 0))
                            .collect::<Vec<_>>()
                    };
                    assert_eq!(
                        indicator_eval_with_endpoint_points(
                            &row_point,
                            &endpoint(start),
                            &endpoint(end),
                            &index_point,
                        ),
                        indicator_eval(&row_point, start, end, &index_point),
                        "m={m}, interval=[{start},{end})",
                    );
                }
            }
        }
    }

    #[test]
    fn assisted_terminal_matches_explicit_residual_contraction() {
        for m in 3usize..=7 {
            let residual_vars = 2usize.min(m);
            let folded = m - residual_vars;
            let row_point: Vec<_> = (0..m).map(|i| f((41 * m + i + 1) as u64)).collect();
            let index_prefix: Vec<_> =
                (0..folded).map(|i| f((53 * m + i + 1) as u64)).collect();
            let final_message: Vec<_> =
                (0..1usize << residual_vars).map(|i| f((67 * m + i + 1) as u64)).collect();
            let start = (1usize << (m - 2)) - 1;
            let end = (3usize << (m - 2)).min(1usize << m);
            let endpoint = |value: usize| {
                (0..=m)
                    .map(|bit| F128::new(((value >> bit) & 1) as u64, 0))
                    .collect::<Vec<_>>()
            };
            let start_point = endpoint(start);
            let end_point = endpoint(end);
            let mut direct = F128::ZERO;
            for (y, &message) in final_message.iter().enumerate() {
                let mut index = index_prefix.clone();
                index.extend(
                    (0..residual_vars)
                        .map(|bit| F128::new(((y >> bit) & 1) as u64, 0)),
                );
                direct += message
                    * indicator_eval_with_endpoint_points(
                        &row_point,
                        &start_point,
                        &end_point,
                        &index,
                    );
            }
            assert_eq!(
                assisted_terminal_eval(
                    &row_point,
                    &start_point,
                    &end_point,
                    &index_prefix,
                    &final_message,
                ),
                direct,
                "m={m}",
            );
        }
    }

    #[test]
    fn prefix_indicator_matches_dense_table_mle() {
        for m in 0usize..=7 {
            let n = 1usize << m;
            let point: Vec<_> = (0..m).map(|i| f((11 * m + i + 1) as u64)).collect();
            for height in 0..=n {
                let mut table = vec![F128::ZERO; n];
                table[..height].fill(F128::ONE);
                assert_eq!(
                    prefix_indicator_eval(height, &point),
                    mle_eval(&table, &point),
                    "m={m}, height={height}",
                );
            }
        }
    }

    #[test]
    fn zero_residual_contract_uses_only_two_message_entries() {
        fn prefix_state(row_weights: &[[F128; 2]], start: usize, end: usize, index_point: &[F128]) -> [F128; 4] {
            let mut state = [F128::ZERO; 4];
            state[0] = F128::ONE;
            for (bit, &b) in index_point.iter().enumerate() {
                let start_bit = ((start >> bit) & 1) != 0;
                let end_bit = ((end >> bit) & 1) != 0;
                let b_weights = [F128::ONE + b, b];
                let mut next = [F128::ZERO; 4];
                for (state_idx, &state_weight) in state.iter().enumerate() {
                    let carry = (state_idx & 1) != 0;
                    let comparison = (state_idx & 2) != 0;
                    for a_bit in 0..2 {
                        for b_bit in 0..2 {
                            let sum = a_bit + usize::from(carry) + usize::from(start_bit);
                            if b_bit != (sum & 1) {
                                continue;
                            }
                            let next_carry = (sum >> 1) != 0;
                            let next_comparison = if (b_bit != 0) == end_bit { comparison } else { end_bit };
                            next[usize::from(next_carry) + 2 * usize::from(next_comparison)] +=
                                state_weight * row_weights[bit][a_bit] * b_weights[b_bit];
                        }
                    }
                }
                state = next;
            }
            state
        }

        for m in 1usize..=6 {
            let n = 1usize << m;
            for residual_log in 1..=m.min(4) {
                let folded = m - residual_log;
                let row_weights: Vec<_> = (0..folded)
                    .map(|i| [F128::ONE + f((3 * m + i) as u64), f((3 * m + i) as u64)])
                    .collect();
                let index_low: Vec<_> = (0..folded).map(|i| f((17 * m + 5 * residual_log + i) as u64)).collect();
                let final_msg: Vec<_> = (0..1usize << residual_log)
                    .map(|i| f((31 * m + 7 * residual_log + i) as u64))
                    .collect();

                for start in 0..n {
                    for end in start..=n {
                        let state = prefix_state(&row_weights, start, end, &index_low);
                        let start_hi = start >> folded;
                        let end_hi = end >> folded;
                        let msg = |i: usize| final_msg.get(i).copied().unwrap_or(F128::ZERO);
                        let direct = msg(start_hi)
                            * (state[0] * F128::new((start_hi < end_hi) as u64, 0)
                                + state[2] * F128::new((start_hi <= end_hi) as u64, 0))
                            + msg(start_hi + 1)
                                * (state[1] * F128::new((start_hi + 1 < end_hi) as u64, 0)
                                    + state[3] * F128::new((start_hi + 1 <= end_hi) as u64, 0));

                        let mut expected = F128::ZERO;
                        for (y, &message) in final_msg.iter().enumerate() {
                            let mut point = index_low.clone();
                            point.extend((0..residual_log).map(|bit| F128::new(((y >> bit) & 1) as u64, 0)));
                            expected += message * indicator_eval_with_row_weights(&row_weights, start, end, &point);
                        }
                        assert_eq!(direct, expected, "m={m}, folded={folded}, interval=[{start},{end})",);
                    }
                }
            }
        }
    }
}
