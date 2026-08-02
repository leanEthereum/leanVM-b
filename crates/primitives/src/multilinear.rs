// `build_eq` and `lagrange_weights_naive` come from https://github.com/succinctlabs/flock (MIT OR Apache-2.0).
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in a low and a high variant.

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

/// Bind the highest free variable of `table` to `rho` in place: `table[i] =
/// interp(table[i], table[i + half], rho)`. Binding from the top down leaves the
/// low variables, the ones every table of a batch shares, for last.
pub fn fold_high_inplace(table: &mut Vec<F128>, rho: F128) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = interp(table[i], table[i + half], rho);
    }
    table.truncate(half);
}

/// Marginalize the lowest variable out of an `eq` table (in place). `eq(r_0, 0) +
/// eq(r_0, 1) = 1`, so summing adjacent entries drops `r_0` with no multiplies,
/// versus `2^{n-1}` to rebuild the table.
pub fn shrink_eq_low(table: &mut Vec<F128>) {
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = table[2 * i] + table[2 * i + 1];
    }
    table.truncate(half);
}

/// Marginalize the highest variable out of an `eq` table (in place), the
/// [`shrink_eq_low`] counterpart for a top-down sumcheck.
pub fn shrink_eq_high(table: &mut Vec<F128>) {
    let half = table.len() / 2;
    for i in 0..half {
        let hi = table[i + half];
        table[i] += hi;
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

/// The 3 nodes {0, 1, g} at which a degree-2 sumcheck round univariate is sent
/// (the eq weight is factored out). Shared by `lean_vm::constraints` and `lean_vm::gkr`.
#[inline]
pub fn tri_nodes() -> [F128; 3] {
    [F128::ZERO, F128::ONE, F128::generator()]
}

/// The 4 nodes {0, 1, g, g²} at which a degree-3 sumcheck round univariate is sent
/// WHOLE, eq weight included. Costs one field element more than [`tri_nodes`] and
/// buys a verifier that reapplies nothing: `h(0) + h(1) = claim`, then interpolate.
#[inline]
pub fn quad_nodes() -> [F128; 4] {
    let g = F128::generator();
    [F128::ZERO, F128::ONE, g, g * g]
}

/// Evaluate a degree-four eq-trick round from its four independent transcript
/// coefficients. If `difference = q(0) + q(1)`, the incoming claim fixes the
/// constant coefficient, and characteristic two fixes the linear coefficient.
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
///
/// Each doubling level needs only ONE field multiply per pair: in
/// characteristic 2, `v · (1 + r) = v + v · r`, so the low child is the high
/// child XOR the parent. Levels are independent within themselves and
/// parallelize once they are large enough to cover rayon's dispatch.
pub fn build_eq(r: &[F128]) -> Vec<F128> {
    use rayon::prelude::*;

    let n = r.len();
    // Uninit alloc — at level `i` the loop reads `t[..2^i]` (written by an
    // earlier level or the `t[0] = ONE` seed) and writes `t[2^i..2^(i+1)]`
    // (purely written), so every slot is written before any read.
    let mut t = crate::alloc_uninit_vec::<crate::field::F128>(1usize << n);
    t[0] = F128::ONE;
    const PAR_THRESHOLD: usize = 1 << 12;
    for (i, &r_i) in r.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi_rest) = t.split_at_mut(half);
        let hi = &mut hi_rest[..half];
        let build_pair = |lo_x: &mut F128, hi_x: &mut F128| {
            let v = *lo_x;
            let high = v * r_i;
            *hi_x = high;
            *lo_x = v + high;
        };
        if half < PAR_THRESHOLD {
            lo.iter_mut()
                .zip(hi.iter_mut())
                .for_each(|(l, h)| build_pair(l, h));
        } else {
            lo.par_iter_mut()
                .zip(hi.par_iter_mut())
                .for_each(|(l, h)| build_pair(l, h));
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
