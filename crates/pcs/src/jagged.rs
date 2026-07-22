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

/// Evaluate the MLE of `1[index = start + row && index < end]`.
///
/// `row_point` contains the low row coordinates; omitted high row coordinates
/// are fixed to zero. `index_point` is the point of the dense committed cube.
/// `start` and `end` are public cumulative column heights and must fit in that
/// cube.  `end == 2^index_point.len()` is supported by the extra top bit.
pub fn indicator_eval(row_point: &[F128], start: usize, end: usize, index_point: &[F128]) -> F128 {
    assert!(start <= end, "jagged column interval must be ordered");
    assert!(row_point.len() <= index_point.len());
    assert!(end <= (1usize << index_point.len()));

    // State = (carry, comparison_so_far), indexed carry + 2*comparison.
    // `comparison_so_far` is the strict comparison index < end over the bits
    // processed so far; a more-significant differing bit overwrites it.
    let mut state = [F128::ZERO; 4];
    state[0] = F128::ONE;

    // One extra fixed-zero top bit handles an interval ending at 2^m and also
    // rejects an addition that carries out of the committed cube.
    for bit in 0..=index_point.len() {
        let a = row_point.get(bit).copied().unwrap_or(F128::ZERO);
        let b = index_point.get(bit).copied().unwrap_or(F128::ZERO);
        let c_bit = ((start >> bit) & 1) != 0;
        let d_bit = ((end >> bit) & 1) != 0;
        let a_weights = [F128::ONE + a, a];
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
                    for i in start..end {
                        table[i] = row_eq[i - start];
                    }
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
}
