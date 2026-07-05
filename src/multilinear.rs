//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`); folding binds the lowest free variable, the order sumcheck
//! rounds consume. Committed data is `K`-valued (`F64`), all randomness is
//! `E`-valued (`F128T`), so the workhorses come in two flavors: pure-`E`
//! folding, and the mixed first fold that lifts a `K`-table into `E` via
//! `mul_base` (2 PMULL per term).

use crate::field::{F64, F128T};

/// Multilinear interpolation in one variable over `E`: `lo + t·(lo+hi)`, the
/// char-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F128T, hi: F128T, t: F128T) -> F128T {
    lo + t * (lo + hi)
}

/// Mixed interpolation: two `K` endpoints against an `E` parameter, one
/// `mul_base` (`lo + t·(lo+hi)` with `lo, hi ∈ K`).
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F128T) -> F128T {
    F128T::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)` — 1 at `x = r`, 0 at every other Boolean point.
pub fn eq_eval(r: &[F128T], x: &[F128T]) -> F128T {
    debug_assert_eq!(r.len(), x.len());
    let mut acc = F128T::ONE;
    for i in 0..r.len() {
        acc *= F128T::ONE + r[i] + x[i];
    }
    acc
}

/// The `eq(r, ·)` table over `n = r.len()` variables, expanded in place: descending
/// `i` keeps the unread low half intact while the high half is written from it.
pub fn eq_table(r: &[F128T]) -> Vec<F128T> {
    let mut eq = vec![F128T::ZERO; 1usize << r.len()];
    eq[0] = F128T::ONE;
    let mut half = 1usize;
    for &rk in r {
        let one_plus = F128T::ONE + rk;
        for i in (0..half).rev() {
            // Deliberately scalar: `rk`/`one_plus` are loop-invariant and the
            // scalar pair beats an `F128T::mul2` here (3.37 vs 3.73 ns/entry).
            let e = eq[i];
            eq[i + half] = e * rk;
            eq[i] = e * one_plus;
        }
        half <<= 1;
    }
    eq
}

/// Bind the lowest free variable of `table` to `rho`: `out[i] = interp(table[2i],
/// table[2i+1], rho)`.
pub fn fold_low(table: &[F128T], rho: F128T) -> Vec<F128T> {
    debug_assert_eq!(table.len() % 2, 0);
    (0..table.len() / 2)
        .map(|i| interp(table[2 * i], table[2 * i + 1], rho))
        .collect()
}

/// The mixed [`fold_low`]: bind the lowest variable of a `K`-table to an
/// `E`-challenge, producing the `E`-table the remaining rounds fold. One
/// `mul_base` per output entry.
pub fn fold_low_k(table: &[F64], rho: F128T) -> Vec<F128T> {
    debug_assert_eq!(table.len() % 2, 0);
    (0..table.len() / 2)
        .map(|i| interp_k(table[2 * i], table[2 * i + 1], rho))
        .collect()
}

/// In-place [`fold_low`], no reallocation (`i ≤ 2i`, so unread entries survive).
pub fn fold_low_inplace(table: &mut Vec<F128T>, rho: F128T) {
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
pub fn lagrange_eval(nodes: &[F128T], values: &[F128T], p: F128T) -> F128T {
    debug_assert_eq!(nodes.len(), values.len());
    let n = nodes.len();
    let mut acc = F128T::ZERO;
    for i in 0..n {
        let mut num = F128T::ONE;
        let mut den = F128T::ONE;
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

/// The 3 nodes {0, 1, x} at which a degree-2 sumcheck round univariate is sent
/// (the eq weight is factored out); `x = g` embedded into `E`. Shared by
/// [`crate::constraints`] and [`crate::gkr`].
#[inline]
pub fn tri_nodes() -> [F128T; 3] {
    [F128T::ZERO, F128T::ONE, F128T::from(crate::field::G)]
}

/// Add two 3-coefficient sumcheck accumulators componentwise.
#[inline]
pub fn add3(mut x: [F128T; 3], y: [F128T; 3]) -> [F128T; 3] {
    for i in 0..3 {
        x[i] += y[i];
    }
    x
}

/// Evaluate the MLE of a `K`-valued truth table at an `E`-point (length
/// `log2(len)`), binding variables LSB-first: the first fold is mixed
/// ([`fold_low_k`]), the rest pure `E` in place.
pub fn mle_eval(table: &[F64], point: &[F128T]) -> F128T {
    debug_assert_eq!(table.len(), 1 << point.len());
    if point.is_empty() {
        return F128T::from(table[0]);
    }
    let mut cur = fold_low_k(table, point[0]);
    let mut len = cur.len();
    for &p in &point[1..] {
        len /= 2;
        // Deliberately scalar: the fold's mul has the loop-invariant `p` on
        // one side, and pairing outputs through `F128T::mul2` measures slower
        // (1.75 vs 2.14 ns/output, same shape as the GKR `par_fold`).
        for i in 0..len {
            cur[i] = interp(cur[2 * i], cur[2 * i + 1], p);
        }
    }
    cur[0]
}
