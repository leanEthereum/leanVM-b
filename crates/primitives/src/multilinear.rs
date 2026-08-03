// CREDIT: https://github.com/succinctlabs/flock (`build_eq` and `lagrange_weights_naive`), MIT OR Apache-2.0.
//! Multilinear-extension utilities: the equality polynomial, single-variable
//! folding, and MLE evaluation. Truth tables are indexed little-endian (variable
//! `k` is bit `k`). Sumchecks here consume variables from either end, so folding
//! and `eq`-marginalization come in low and high variants. Committed data is
//! `K`-valued (`F64`) while randomness is `E`-valued (`F192`), so the first
//! fold of a committed table also lifts it into `E`.

use std::ops::DerefMut;

use crate::field::{F64, F192, F192Unreduced};
use zk_alloc::ArenaVec;

/// The one thing the in-place folds need beyond a mutable slice: the ability to
/// drop a suffix. Implemented for `Vec` and `ArenaVec`, so a fold works on either
/// without duplicating the kernel or naming a container in its signature.
pub trait Shrink<T>: DerefMut<Target = [T]> {
    /// Keep the first `len` elements, dropping the rest.
    fn shrink_to(&mut self, len: usize);
}

impl<T> Shrink<T> for Vec<T> {
    #[inline]
    fn shrink_to(&mut self, len: usize) {
        self.truncate(len);
    }
}

impl<T> Shrink<T> for ArenaVec<T> {
    #[inline]
    fn shrink_to(&mut self, len: usize) {
        self.truncate(len);
    }
}

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

/// `eq(r, x) = ∏_i (1 + r_i + x_i)`. For Boolean `r`, this is the indicator
/// of `x = r`; for arbitrary `r`, it is the multilinear interpolation weight.
pub fn eq_eval(r: &[F192], x: &[F192]) -> F192 {
    debug_assert_eq!(r.len(), x.len());
    let mut acc = F192::ONE;
    for i in 0..r.len() {
        acc *= F192::ONE + r[i] + x[i];
    }
    acc
}

/// The `eq(r, ·)` table over `n = r.len()` variables, expanded a level at a
/// time: each level writes the new high half from the low half and rewrites
/// the low half in place.
///
/// One multiply per pair, not two. In characteristic 2,
/// `e · (1 + r) = e + e · r`, so the low child is the high child XOR the
/// parent — the second product is redundant. (This is orthogonal to batching:
/// `rk` is loop-invariant, and the scalar product still beats `F192::mul2`
/// here, 3.37 vs 3.73 ns/entry.)
///
/// A level's pairs are independent, so levels wide enough to cover the
/// dispatch are split across threads.
pub fn eq_table(r: &[F192]) -> Vec<F192> {
    let mut eq = vec![F192::ZERO; 1usize << r.len()];
    fill_eq_table(r, &mut eq);
    eq
}

/// Arena-backed [`eq_table`], for the prover's large tables. Identical output.
pub fn eq_table_arena(r: &[F192]) -> ArenaVec<F192> {
    // SAFETY: `fill_eq_table` writes every one of the `2^r.len()` entries.
    let mut eq = unsafe { ArenaVec::<F192>::uninitialized(1usize << r.len()) };
    fill_eq_table(r, &mut eq);
    eq
}

/// The doubling recurrence itself, over a caller-supplied `2^r.len()` buffer.
fn fill_eq_table(r: &[F192], eq: &mut [F192]) {
    debug_assert_eq!(eq.len(), 1usize << r.len());
    eq[0] = F192::ONE;
    const PAR_THRESHOLD: usize = 1 << 12;
    for (i, &rk) in r.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi_rest) = eq.split_at_mut(half);
        let hi = &mut hi_rest[..half];
        let build_pair = |lo_x: &mut F192, hi_x: &mut F192| {
            let e = *lo_x;
            let high = e * rk;
            *hi_x = high;
            *lo_x = e + high;
        };
        if half < PAR_THRESHOLD {
            lo.iter_mut().zip(hi.iter_mut()).for_each(|(l, h)| build_pair(l, h));
        } else {
            let chunk = parallel::recommended_chunk_size(half);
            parallel::chunks_mut2(lo, hi, chunk, |_, lo_c, hi_c| {
                lo_c.iter_mut().zip(hi_c.iter_mut()).for_each(|(l, h)| build_pair(l, h));
            });
        }
    }
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

/// Bind the highest variable of a `K`-table and lift the result into `E`.
pub fn fold_high_k(table: &[F64], rho: F192) -> ArenaVec<F192> {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    (0..half).map(|i| interp_k(table[i], table[i + half], rho)).collect()
}

/// Bind the highest free variable of `table` to `rho` in place: `table[i] =
/// interp(table[i], table[i + half], rho)`. Binding from the top down leaves the
/// low variables, the ones every table of a batch shares, for last.
pub fn fold_high_inplace<B: Shrink<F192>>(table: &mut B, rho: F192) {
    debug_assert_eq!(table.len() % 2, 0);
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = interp(table[i], table[i + half], rho);
    }
    table.shrink_to(half);
}

/// Marginalize the lowest variable out of an `eq` table (in place). `eq(r_0, 0) +
/// eq(r_0, 1) = 1`, so summing adjacent entries drops `r_0` with no multiplies,
/// versus `2^{n-1}` to rebuild the table.
pub fn shrink_eq_low<B: Shrink<F192>>(table: &mut B) {
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = table[2 * i] + table[2 * i + 1];
    }
    table.shrink_to(half);
}

/// Marginalize the highest variable out of an `eq` table (in place), the
/// [`shrink_eq_low`] counterpart for a top-down sumcheck.
pub fn shrink_eq_high<B: Shrink<F192>>(table: &mut B) {
    let half = table.len() / 2;
    for i in 0..half {
        let hi = table[i + half];
        table[i] += hi;
    }
    table.shrink_to(half);
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

/// The 4 nodes {0, 1, g, g²} at which a degree-3 sumcheck round univariate is sent
/// WHOLE, eq weight included. Costs one field element more than [`tri_nodes`] and
/// buys a verifier that reapplies nothing: `h(0) + h(1) = claim`, then interpolate.
#[inline]
pub fn quad_nodes() -> [F192; 4] {
    let g = F192::from(crate::field::G);
    [F192::ZERO, F192::ONE, g, g * g]
}

/// Evaluate a degree-four eq-trick round from its four independent transcript
/// coefficients. If `difference = q(0) + q(1)`, the incoming claim fixes the
/// constant coefficient, and characteristic two fixes the linear coefficient.
#[inline]
pub fn quartic_eval_from_eq(
    claim: F192,
    eq_point: F192,
    difference: F192,
    c2: F192,
    c3: F192,
    c4: F192,
    point: F192,
) -> F192 {
    let c0 = claim + eq_point * difference;
    let c1 = difference + c2 + c3 + c4;
    c0 + point * (c1 + point * (c2 + point * (c3 + point * c4)))
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
