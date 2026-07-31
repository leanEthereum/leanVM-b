// `build_eq` and `lagrange_weights_naive` come from https://github.com/succinctlabs/flock (MIT OR Apache-2.0).
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`); folding binds the lowest free variable, the order sumcheck
//! rounds consume.

use crate::field::F128;

/// Multilinear interpolation in one variable: `lo + t·(lo+hi)`, the char-2 form of
/// `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F128, hi: F128, t: F128) -> F128 {
    lo + t * (lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)` — 1 at `x = r`, 0 at every other Boolean point.
pub fn eq_eval(r: &[F128], x: &[F128]) -> F128 {
    debug_assert_eq!(r.len(), x.len());
    let mut acc = F128::ONE;
    for i in 0..r.len() {
        acc *= F128::ONE + r[i] + x[i];
    }
    acc
}

/// Standard inner product of two equal-length field vectors.
#[inline]
pub fn inner_product(a: &[F128], b: &[F128]) -> F128 {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).fold(F128::ZERO, |acc, (&x, &y)| acc + x * y)
}

/// Bind the lowest free variable of `table` to `rho` in place: `table[i] =
/// interp(table[2i], table[2i+1], rho)` (no reallocation; `i ≤ 2i`, so unread
/// entries survive).
pub fn fold_low_inplace(table: &mut Vec<F128>, rho: F128) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = interp(table[2 * i], table[2 * i + 1], rho);
    }
    table.truncate(half);
}

/// Lagrange evaluation: given distinct `nodes` and a polynomial's `values` there,
/// evaluate the interpolant at `p`. Reads a sumcheck round's univariate (sent as
/// evaluations) at the verifier's challenge.
pub fn lagrange_eval(nodes: &[F128], values: &[F128], p: F128) -> F128 {
    debug_assert_eq!(nodes.len(), values.len());
    let n = nodes.len();
    let mut acc = F128::ZERO;
    for i in 0..n {
        let mut num = F128::ONE;
        let mut den = F128::ONE;
        for k in 0..n {
            if k == i {
                continue;
            }
            num *= p + nodes[k];
            den *= nodes[i] + nodes[k];
        }
        acc += values[i] * num * den.inv();
    }
    acc
}

/// `(g²+g)⁻¹`, used to recover the quadratic coefficient from evaluations at
/// `{0,1,g}`.
pub const QUADRATIC_DENOMINATOR_INV: F128 =
    F128::new(0xffff_ffff_ffff_ffc1, 0x7fff_ffff_ffff_ffff);

/// The `X²` coefficient of the quadratic taking `values` at `{0,1,g}`.
#[inline]
pub fn quadratic_coefficient(values: [F128; 3]) -> F128 {
    let difference = values[0] + values[1];
    (values[0] + values[2] + crate::field::mul_by_x(difference))
        * QUADRATIC_DENOMINATOR_INV
}

/// Evaluate `q(X)=u₀+bX+u₂X²` from `u₀`, `u₂`, and the sumcheck relation
/// `q(0)+q(1)=sum` (hence `b=sum+u₂` in characteristic two).
#[inline]
pub fn quadratic_eval_from_sum(u_0: F128, u_2: F128, sum: F128, point: F128) -> F128 {
    u_0 + point * (sum + u_2 + point * u_2)
}

/// Evaluate an eq-trick round from its normalized incoming claim. If
/// `difference=q(0)+q(1)` and the equality coordinate is `eq_point`, then
/// `q(0)=claim+eq_point·difference`.
#[inline]
pub fn quadratic_eval_from_eq(
    claim: F128,
    eq_point: F128,
    difference: F128,
    quadratic: F128,
    point: F128,
) -> F128 {
    claim
        + eq_point * difference
        + point * (difference + quadratic + point * quadratic)
}

/// Evaluate a degree-four eq-trick round from the four independent
/// coefficients sent by the prover.
#[inline]
pub fn quartic_eval_from_eq(
    claim: F128,
    eq_point: F128,
    difference: F128,
    c2: F128,
    c3: F128,
    c4: F128,
    point: F128,
) -> F128 {
    let c0 = claim + eq_point * difference;
    let c1 = difference + c2 + c3 + c4;
    c0 + point * (c1 + point * (c2 + point * (c3 + point * c4)))
}

/// Add two 3-coefficient sumcheck accumulators componentwise.
#[inline]
pub fn add3(mut x: [F128; 3], y: [F128; 3]) -> [F128; 3] {
    for i in 0..3 {
        x[i] += y[i];
    }
    x
}

/// Evaluate the MLE with truth table `table` at `point` (length `log2(len)`),
/// binding variables LSB-first. One copy, then folded in place.
pub fn mle_eval(table: &[F128], point: &[F128]) -> F128 {
    debug_assert_eq!(table.len(), 1 << point.len());
    let mut cur = table.to_vec();
    let mut len = cur.len();
    for &p in point {
        len /= 2;
        for i in 0..len {
            cur[i] = interp(cur[2 * i], cur[2 * i + 1], p);
        }
    }
    cur[0]
}

/// Build the multilinear-eq evaluation table over `r`:
/// `table[x] = ∏_i ((1 + r_i) · (1 ⊕ bit_i(x)) + r_i · bit_i(x))` for `x ∈ {0,1}^n`,
/// where `n = r.len()`. Standard in-place power-of-two doubling.
pub fn build_eq(r: &[F128]) -> Vec<F128> {
    let n = r.len();
    // Uninit alloc — same invariant as `build_eq_parallel` in ring_switch:
    // every slot in t[0..2^n] is written exactly once before any read.
    let mut t = crate::alloc_uninit_vec::<crate::field::F128>(1usize << n);
    t[0] = F128::ONE;
    for i in 0..n {
        let r_i = r[i];
        let one_minus_r = F128::ONE + r_i;
        // Iterate downward so we read t[x] before overwriting it as t[x | (1<<i)].
        for x in (0..(1usize << i)).rev() {
            t[x | (1 << i)] = t[x] * r_i;
            t[x] *= one_minus_r;
        }
    }
    t
}

/// O(2^{2·k_skip}) field multiplies — one-time cost.
pub fn lagrange_weights_naive(k_skip: usize, z: F128) -> Vec<F128> {
    let ell = 1usize << k_skip;
    assert!(ell <= 256, "k_skip > 8 would exceed PHI_8_TABLE");
    let mut weights = vec![F128::ZERO; ell];
    for i in 0..ell {
        let si = crate::field::phi8::PHI_8_TABLE[i];
        let mut num = F128::ONE;
        let mut den = F128::ONE;
        for j in 0..ell {
            if j == i {
                continue;
            }
            let sj = crate::field::phi8::PHI_8_TABLE[j];
            num *= z + sj;
            den *= si + sj;
        }
        weights[i] = num * den.inv();
    }
    weights
}

#[cfg(test)]
mod coefficient_tests {
    use super::*;

    #[test]
    fn compact_quadratic_and_quartic_evaluations_match_coefficients() {
        let mut x = F128::generator();
        for _ in 0..64 {
            let c0 = x;
            x *= F128::generator();
            let c1 = x;
            x *= F128::generator();
            let c2 = x;
            x *= F128::generator();
            let point = x;
            x *= F128::generator();
            let eq_point = x;
            x *= F128::generator();

            let q = |z: F128| c0 + z * (c1 + z * c2);
            let values = [q(F128::ZERO), q(F128::ONE), q(F128::generator())];
            assert_eq!(quadratic_coefficient(values), c2);
            let difference = c1 + c2;
            assert_eq!(
                quadratic_eval_from_sum(c0, c2, difference, point),
                q(point)
            );
            let claim = c0 + eq_point * difference;
            assert_eq!(
                quadratic_eval_from_eq(claim, eq_point, difference, c2, point),
                q(point)
            );

            let c3 = x;
            x *= F128::generator();
            let c4 = x;
            x *= F128::generator();
            let quartic =
                |z: F128| c0 + z * (c1 + z * (c2 + z * (c3 + z * c4)));
            let difference4 = c1 + c2 + c3 + c4;
            let claim4 = c0 + eq_point * difference4;
            assert_eq!(
                quartic_eval_from_eq(
                    claim4,
                    eq_point,
                    difference4,
                    c2,
                    c3,
                    c4,
                    point,
                ),
                quartic(point)
            );
        }
    }
}
