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

/// The `eq(r, ·)` table over `n = r.len()` variables, expanded in place: descending
/// `i` keeps the unread low half intact while the high half is written from it.
pub fn eq_table(r: &[F128]) -> Vec<F128> {
    let mut eq = vec![F128::ZERO; 1usize << r.len()];
    eq[0] = F128::ONE;
    let mut half = 1usize;
    for &rk in r {
        let one_plus = F128::ONE + rk;
        for i in (0..half).rev() {
            let e = eq[i];
            eq[i + half] = e * rk;
            eq[i] = e * one_plus;
        }
        half <<= 1;
    }
    eq
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

/// The 3 nodes {0, 1, γ} at which a degree-2 sumcheck round univariate is sent
/// (the eq weight is factored out). Shared by [`crate::constraints`] and [`crate::gkr`].
#[inline]
pub fn tri_nodes() -> [F128; 3] {
    [F128::ZERO, F128::ONE, F128::generator()]
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
