// `build_eq` and `lagrange_weights_naive` come from https://github.com/succinctlabs/flock (MIT OR Apache-2.0).
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`); folding binds the lowest free variable, the order sumcheck
//! rounds consume. Committed data is `K`-valued (`F64`), all randomness is
//! `E`-valued (`F192`), so the workhorses come in two flavors: pure-`E`
//! folding, and the mixed first fold that lifts a `K`-table into `E` via
//! `mul_base` (2 PMULL per term).

use crate::field::{F64, F192, F192Unreduced};

/// Multilinear interpolation in one variable over `E`: `lo + t·(lo+hi)`, the
/// char-2 form of `(1−t)·lo + t·hi`.
#[inline]
pub fn interp(lo: F192, hi: F192, t: F192) -> F192 {
    lo + t * (lo + hi)
}

/// Mixed interpolation: two `K` endpoints against an `E` parameter, one
/// `mul_base` (`lo + t·(lo+hi)` with `lo, hi ∈ K`).
#[inline]
pub fn interp_k(lo: F64, hi: F64, t: F192) -> F192 {
    F192::from(lo) + t.mul_base(lo + hi)
}

/// `eq(r, x) = ∏_i (1 + r_i + x_i)` — 1 at `x = r`, 0 at every other Boolean point.
pub fn eq_eval(r: &[F192], x: &[F192]) -> F192 {
    debug_assert_eq!(r.len(), x.len());
    let mut acc = F192::ONE;
    for i in 0..r.len() {
        acc *= F192::ONE + r[i] + x[i];
    }
    acc
}

/// The `eq(r, ·)` table over `n = r.len()` variables, expanded in place: descending
/// `i` keeps the unread low half intact while the high half is written from it.
pub fn eq_table(r: &[F192]) -> Vec<F192> {
    let mut eq = vec![F192::ZERO; 1usize << r.len()];
    eq[0] = F192::ONE;
    let mut half = 1usize;
    for &rk in r {
        let one_plus = F192::ONE + rk;
        for i in (0..half).rev() {
            // Deliberately scalar: `rk`/`one_plus` are loop-invariant and the
            // scalar pair beats an `F192::mul2` here (3.37 vs 3.73 ns/entry).
            let e = eq[i];
            eq[i + half] = e * rk;
            eq[i] = e * one_plus;
        }
        half <<= 1;
    }
    eq
}

/// The mixed fold: bind the lowest variable of a `K`-table to an
/// `E`-challenge, producing the `E`-table the remaining rounds fold. One
/// `mul_base` per output entry.
pub fn fold_low_k(table: &[F64], rho: F192) -> Vec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    (0..table.len() / 2)
        .map(|i| interp_k(table[2 * i], table[2 * i + 1], rho))
        .collect()
}

/// Bind the lowest free variable of `table` to `rho` in place: `table[i] =
/// interp(table[2i], table[2i+1], rho)` (no reallocation; `i ≤ 2i`, so unread
/// entries survive).
pub fn fold_low_inplace(table: &mut Vec<F192>, rho: F192) {
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
pub fn lagrange_eval(nodes: &[F192], values: &[F192], p: F192) -> F192 {
    debug_assert_eq!(nodes.len(), values.len());
    let n = nodes.len();
    let mut acc = F192::ZERO;
    for i in 0..n {
        let mut num = F192::ONE;
        let mut den = F192::ONE;
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
/// (the eq weight is factored out); `g` embedded into `E`. Shared by
/// `lean_vm::constraints` and `lean_vm::gkr`.
#[inline]
pub fn tri_nodes() -> [F192; 3] {
    [F192::ZERO, F192::ONE, F192::from(crate::field::G)]
}

/// Add two 3-coefficient sumcheck accumulators componentwise.
#[inline]
pub fn add3(mut x: [F192; 3], y: [F192; 3]) -> [F192; 3] {
    for i in 0..3 {
        x[i] += y[i];
    }
    x
}

/// XOR two 3-slot deferred-reduction accumulators componentwise (the unreduced
/// counterpart of [`add3`]; XOR IS addition on the unreduced parts).
#[inline]
pub fn xor3(mut x: [F192Unreduced; 3], y: [F192Unreduced; 3]) -> [F192Unreduced; 3] {
    for i in 0..3 {
        x[i] ^= y[i];
    }
    x
}

/// Evaluate the MLE of a `K`-valued truth table at an `E`-point (length
/// `log2(len)`), binding variables LSB-first: the first fold is mixed
/// ([`fold_low_k`]), the rest pure `E` in place.
pub fn mle_eval(table: &[F64], point: &[F192]) -> F192 {
    debug_assert_eq!(table.len(), 1 << point.len());
    if point.is_empty() {
        return F192::from(table[0]);
    }
    let mut cur = fold_low_k(table, point[0]);
    let mut len = cur.len();
    for &p in &point[1..] {
        len /= 2;
        // Deliberately scalar: the fold's mul has the loop-invariant `p` on
        // one side, and pairing outputs through `F192::mul2` measures slower
        // (1.75 vs 2.14 ns/output, same shape as the GKR `par_fold`).
        for i in 0..len {
            cur[i] = interp(cur[2 * i], cur[2 * i + 1], p);
        }
    }
    cur[0]
}

/// O(2^{2·k_skip}) field multiplies — one-time cost.
pub fn lagrange_weights_naive(k_skip: usize, z: F192) -> Vec<F192> {
    use crate::field::PHI_8_TABLE_192 as PHI_8_TABLE;
    let ell = 1usize << k_skip;
    assert!(ell <= 256, "k_skip > 8 would exceed PHI_8_TABLE");
    let mut weights = vec![F192::ZERO; ell];
    for i in 0..ell {
        let si = PHI_8_TABLE[i];
        let mut num = F192::ONE;
        let mut den = F192::ONE;
        for j in 0..ell {
            if j == i {
                continue;
            }
            let sj = PHI_8_TABLE[j];
            num *= z + sj;
            den *= si + sj;
        }
        weights[i] = num * den.inv();
    }
    weights
}
