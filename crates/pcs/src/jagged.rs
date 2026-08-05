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

use primitives::field::F192;

/// Evaluate the MLE of `1[index = start + row && index < end]`.
///
/// `row_point` contains the low row coordinates; omitted high row coordinates
/// are fixed to zero. `index_point` is the point of the dense committed cube.
/// `start` and `end` are public cumulative column heights and must fit in that
/// cube.  `end == 2^index_point.len()` is supported by the extra top bit.
pub fn indicator_eval(row_point: &[F192], start: usize, end: usize, index_point: &[F192]) -> F192 {
    let row_weights: Vec<[F192; 2]> = row_point.iter().map(|&a| [F192::ONE + a, a]).collect();
    indicator_eval_with_row_weights(&row_weights, start, end, index_point)
}

/// [`indicator_eval`] with explicit `(zero, one)` weights for each logical-row
/// coordinate. The pairs need not sum to one. This lets a geometric column
/// batch use selector weights `(1, gamma^(2^b))` directly, absorbing all
/// normalization factors and avoiding exceptional inversions.
pub fn indicator_eval_with_row_weights(
    row_weights: &[[F192; 2]],
    start: usize,
    end: usize,
    index_point: &[F192],
) -> F192 {
    assert!(start <= end, "jagged column interval must be ordered");
    assert!(row_weights.len() <= index_point.len());
    assert!(end <= (1usize << index_point.len()));

    // State = (carry, comparison_so_far), indexed carry + 2*comparison.
    // `comparison_so_far` is the strict comparison index < end over the bits
    // processed so far; a more-significant differing bit overwrites it.
    let mut state = [F192::ZERO; 4];
    state[0] = F192::ONE;

    // One extra fixed-zero top bit handles an interval ending at 2^m and also
    // rejects an addition that carries out of the committed cube.
    for bit in 0..=index_point.len() {
        let b = index_point.get(bit).copied().unwrap_or(F192::ZERO);
        let c_bit = ((start >> bit) & 1) != 0;
        let d_bit = ((end >> bit) & 1) != 0;
        let a_weights = row_weights.get(bit).copied().unwrap_or([F192::ONE, F192::ZERO]);
        let b_weights = [F192::ONE + b, b];
        let mut next = [F192::ZERO; 4];

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
pub fn prefix_indicator_eval(height: usize, point: &[F192]) -> F192 {
    assert!(height <= (1usize << point.len()));
    if height == (1usize << point.len()) {
        return F192::ONE;
    }

    // MSB-first digit DP with two states: the sampled index is already less
    // than `height`, or it is still equal to the scanned prefix.
    let mut less = F192::ZERO;
    let mut equal = F192::ONE;
    for bit in (0..point.len()).rev() {
        let x = point[bit];
        if ((height >> bit) & 1) == 0 {
            equal *= F192::ONE + x;
        } else {
            less += equal * (F192::ONE + x);
            equal *= x;
        }
    }
    less
}

#[cfg(test)]
mod tests {
    use super::super::whir::build_eq_table_ext as build_eq;
    use super::super::ring_switch::inner_product_ext;
    use super::*;

    /// MLE of an E-valued table, the shape jagged's reference checks need
    /// (`primitives::multilinear::mle_eval` takes a K-valued table).
    fn mle_eval(table: &[F192], point: &[F192]) -> F192 {
        inner_product_ext(table, &build_eq(point))
    }

    fn f(x: u64) -> F192 {
        F192::new(x, x.rotate_left(17), 0)
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
                    let mut table = vec![F192::ZERO; n];
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
        let row_weights = [[F192::ONE, f(13)], [F192::ONE, F192::ONE], [f(17), f(19)]];
        let (start, end) = (3usize, 11usize);
        let index_eq = build_eq(&index_point);
        let mut expected = F192::ZERO;
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
    fn prefix_indicator_matches_dense_table_mle() {
        for m in 0usize..=7 {
            let n = 1usize << m;
            let point: Vec<_> = (0..m).map(|i| f((11 * m + i + 1) as u64)).collect();
            for height in 0..=n {
                let mut table = vec![F192::ZERO; n];
                table[..height].fill(F192::ONE);
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
        fn prefix_state(row_weights: &[[F192; 2]], start: usize, end: usize, index_point: &[F192]) -> [F192; 4] {
            let mut state = [F192::ZERO; 4];
            state[0] = F192::ONE;
            for (bit, &b) in index_point.iter().enumerate() {
                let start_bit = ((start >> bit) & 1) != 0;
                let end_bit = ((end >> bit) & 1) != 0;
                let b_weights = [F192::ONE + b, b];
                let mut next = [F192::ZERO; 4];
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
                    .map(|i| [F192::ONE + f((3 * m + i) as u64), f((3 * m + i) as u64)])
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
                        let msg = |i: usize| final_msg.get(i).copied().unwrap_or(F192::ZERO);
                        let direct = msg(start_hi)
                            * (state[0] * F192::new((start_hi < end_hi) as u64, 0, 0)
                                + state[2] * F192::new((start_hi <= end_hi) as u64, 0, 0))
                            + msg(start_hi + 1)
                                * (state[1] * F192::new((start_hi + 1 < end_hi) as u64, 0, 0)
                                    + state[3] * F192::new((start_hi < end_hi) as u64, 0, 0));

                        let mut expected = F192::ZERO;
                        for (y, &message) in final_msg.iter().enumerate() {
                            let mut point = index_low.clone();
                            point.extend((0..residual_log).map(|bit| F192::new(((y >> bit) & 1) as u64, 0, 0)));
                            expected += message * indicator_eval_with_row_weights(&row_weights, start, end, &point);
                        }
                        assert_eq!(direct, expected, "m={m}, folded={folded}, interval=[{start},{end})",);
                    }
                }
            }
        }
    }
}
