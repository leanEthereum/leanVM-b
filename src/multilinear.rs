//! Multilinear-extension utilities shared across the protocol: the equality
//! polynomial, single-variable folding, and full MLE evaluation.
//!
//! Convention: a length-`2^n` truth table is indexed little-endian — variable
//! `k` is bit `k` of the index. Folding binds the lowest free variable (the
//! LSB), halving the table, which is the order the sumcheck rounds consume.

use crate::field::F128;

/// Multilinear interpolation in one variable: value at `t` given the X=0 (`lo`)
/// and X=1 (`hi`) values. `lo + t·(lo+hi)` is the char-2 form of `(1−t)lo+t·hi`.
#[inline]
pub fn interp(lo: F128, hi: F128, t: F128) -> F128 {
    lo + t * (lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)` — the multilinear that is 1 at `x = r` and 0
/// at every other Boolean point. Both arguments are full coordinate vectors.
pub fn eq_eval(r: &[F128], x: &[F128]) -> F128 {
    debug_assert_eq!(r.len(), x.len());
    let mut acc = F128::ONE;
    for i in 0..r.len() {
        acc *= F128::ONE + r[i] + x[i];
    }
    acc
}

/// The `eq(r, ·)` table over `n = r.len()` variables: `table[x] = eq(r, x)` for
/// every Boolean point `x` (indexed little-endian). Expanded in place in one
/// `2^n` buffer (no per-level reallocation): descending `i` keeps the unread
/// low half intact while the high half is written from it.
pub fn eq_table(r: &[F128]) -> Vec<F128> {
    let mut eq = vec![F128::ZERO; 1usize << r.len()];
    eq[0] = F128::ONE;
    let mut half = 1usize;
    for &rk in r {
        let one_plus = F128::ONE + rk;
        for i in (0..half).rev() {
            let e = eq[i];
            eq[i + half] = e * rk; // bit k = 1
            eq[i] = e * one_plus; // bit k = 0
        }
        half <<= 1;
    }
    eq
}

/// Bind the lowest free variable of `table` to `rho`, returning the half-size
/// table: `out[i] = interp(table[2i], table[2i+1], rho)`.
pub fn fold_low(table: &[F128], rho: F128) -> Vec<F128> {
    debug_assert_eq!(table.len() % 2, 0);
    (0..table.len() / 2)
        .map(|i| interp(table[2 * i], table[2 * i + 1], rho))
        .collect()
}

/// In-place [`fold_low`]: halve `table`, binding its lowest variable to `rho`,
/// with no reallocation (`i ≤ 2i`, so unread entries are never clobbered).
pub fn fold_low_inplace(table: &mut Vec<F128>, rho: F128) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = interp(table[2 * i], table[2 * i + 1], rho);
    }
    table.truncate(half);
}

/// Generic Lagrange evaluation: given distinct `nodes` and a polynomial's
/// `values` at them, evaluate the interpolant at `p`. Used to read a sumcheck
/// round's univariate (sent as evaluations) at the verifier's challenge.
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

/// The 3 evaluation nodes {0, 1, γ} (γ = the field generator) at which a degree-2
/// sumcheck round univariate is sent. With the `eq` weight factored out, each
/// round univariate is degree 2, so 3 evaluations determine it. Shared by the
/// per-table zerocheck ([`crate::constraints`]) and the GKR product ([`crate::gkr`]).
#[inline]
pub fn tri_nodes() -> [F128; 3] {
    [F128::ZERO, F128::ONE, F128::generator()]
}

/// Add two 3-coefficient sumcheck accumulators componentwise (the reduce/fold
/// identity for a degree-2 round's running sum over the [`tri_nodes`]).
#[inline]
pub fn add3(mut x: [F128; 3], y: [F128; 3]) -> [F128; 3] {
    for i in 0..3 {
        x[i] += y[i];
    }
    x
}

/// Evaluate the multilinear extension whose truth table is `table` at `point`
/// (length `log2(table.len())`), by binding variables LSB-first. One copy, then
/// folded in place (no per-round reallocation).
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
