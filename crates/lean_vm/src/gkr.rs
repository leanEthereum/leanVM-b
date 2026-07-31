//! The grand product via GKR (§4.3): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.

use crate::PAR_THRESHOLD;
use crate::transcript::{ProverState, VerifierState};
use primitives::field::{F128, F256Unreduced};
use primitives::multilinear::{build_eq, interp, quartic_eval_from_eq};
use rayon::prelude::*;

/// Bind the lowest variable of `src` into `dst` (in parallel for large tables):
/// `dst[i] = interp(src[2i], src[2i+1], rho)`. Writing into a caller-owned
/// scratch buffer instead of a fresh Vec lets each layer's rounds ping-pong two
/// allocations instead of allocating (and page-faulting) per round.
fn par_fold_into(src: &[F128], rho: F128, dst: &mut Vec<F128>) {
    let half = src.len() / 2;
    if half >= PAR_THRESHOLD {
        (0..half)
            .into_par_iter()
            .map(|i| interp(src[2 * i], src[2 * i + 1], rho))
            .collect_into_vec(dst);
    } else {
        dst.clear();
        dst.extend((0..half).map(|i| interp(src[2 * i], src[2 * i + 1], rho)));
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GkrError {
    Truncated,
    LayerMismatch { layer: usize },
}

/// Build only the layers consumed by the radix-four protocol: levels
/// `0,2,4,…`, plus a final binary root when `μ` is odd.
fn build_layers(leaves: Vec<F128>) -> Vec<Vec<F128>> {
    let mu = crate::log2_strict_usize(leaves.len());
    let mut layers: Vec<Vec<F128>> = (0..=mu).map(|_| Vec::new()).collect();
    layers[0] = leaves;
    let mut level = 0;
    while level + 2 <= mu {
        let cur = &layers[level];
        let quarter = cur.len() / 4;
        let next: Vec<F128> = if quarter >= PAR_THRESHOLD {
            (0..quarter)
                .into_par_iter()
                .map(|j| {
                    cur[4 * j]
                        * cur[4 * j + 1]
                        * cur[4 * j + 2]
                        * cur[4 * j + 3]
                })
                .collect()
        } else {
            (0..quarter)
                .map(|j| {
                    cur[4 * j]
                        * cur[4 * j + 1]
                        * cur[4 * j + 2]
                        * cur[4 * j + 3]
                })
                .collect()
        };
        level += 2;
        layers[level] = next;
    }
    if level < mu {
        debug_assert_eq!(layers[level].len(), 2);
        layers[mu] = vec![layers[level][0] * layers[level][1]];
    }
    layers
}

/// Two binary product levels contracted into one degree-four layer.
struct QuaternaryLayerState {
    child: [Vec<F128>; 4],
    child_next: [Vec<F128>; 4],
}

impl QuaternaryLayerState {
    fn new(below: &[F128], width: usize) -> Self {
        let child = [0, 1, 2, 3].map(|off| {
            if width >= PAR_THRESHOLD {
                (0..width)
                    .into_par_iter()
                    .map(|j| below[4 * j + off])
                    .collect()
            } else {
                (0..width).map(|j| below[4 * j + off]).collect()
            }
        });
        Self {
            child,
            child_next: std::array::from_fn(|_| Vec::new()),
        }
    }

    /// `(q(0)+q(1), [X²]q, [X³]q, [X⁴]q)`.
    fn round_message(&self, eqr: &[F128]) -> [F128; 4] {
        let half = self.child[0].len() / 2;
        let summand = |idx: usize| -> [F256Unreduced; 4] {
            let (lo, hi) = (2 * idx, 2 * idx + 1);
            let linear = self.child.each_ref().map(|table| {
                let a = table[lo];
                [a, a + table[hi]]
            });
            let pair = |a: [[F128; 2]; 2]| {
                let c0 = a[0][0] * a[1][0];
                let c2 = a[0][1] * a[1][1];
                [
                    c0,
                    (a[0][0] + a[0][1]) * (a[1][0] + a[1][1]) + c0 + c2,
                    c2,
                ]
            };
            let left = pair([linear[0], linear[1]]);
            let right = pair([linear[2], linear[3]]);
            let c0 = left[0] * right[0];
            let c4 = left[2] * right[2];
            let middle = left[1] * right[1];
            let c2 =
                (left[0] + left[2]) * (right[0] + right[2]) + c0 + c4 + middle;
            let c3 =
                (left[1] + left[2]) * (right[1] + right[2]) + middle + c4;
            let at_one =
                (left[0] + left[1] + left[2]) * (right[0] + right[1] + right[2]);
            let eq = eqr[idx];
            [
                eq.mul_unreduced(c0 + at_one),
                eq.mul_unreduced(c2),
                eq.mul_unreduced(c3),
                eq.mul_unreduced(c4),
            ]
        };
        let xor4 = |mut x: [F256Unreduced; 4], y: [F256Unreduced; 4]| {
            for i in 0..4 {
                x[i] ^= y[i];
            }
            x
        };
        let acc = if half >= PAR_THRESHOLD {
            (0..half)
                .into_par_iter()
                .map(summand)
                .reduce(|| [F256Unreduced::ZERO; 4], xor4)
        } else {
            (0..half)
                .map(summand)
                .fold([F256Unreduced::ZERO; 4], xor4)
        };
        acc.map(F256Unreduced::reduce)
    }

    fn fold(&mut self, rk: F128) {
        for i in 0..4 {
            par_fold_into(&self.child[i], rk, &mut self.child_next[i]);
            std::mem::swap(&mut self.child[i], &mut self.child_next[i]);
        }
    }
}

/// Shrink `eqr` to the next round's suffix table (in place: the read cursor
/// `2·idx` stays ahead of the write cursor `idx`). `eq(r_j,0) + eq(r_j,1) = 1`,
/// so summing adjacent entries marginalizes the bound variable with no
/// multiplies (vs rebuilding with ~2^{k-j} muls per round).
fn shrink_eq(eqr: &mut Vec<F128>) {
    let eq_half = eqr.len() / 2;
    for idx in 0..eq_half {
        eqr[idx] = eqr[2 * idx] + eqr[2 * idx + 1];
    }
    eqr.truncate(eq_half);
}

/// The result of a batched grand-product proof ([`prove_product_triple`]):
/// the per-tree roots and leaf values, all reduced to ONE shared evaluation
/// point (`Ṽ_t(point) = values[t]`).
pub struct ProductTriple {
    pub roots: [F128; 3],
    pub point: Vec<F128>,
    pub values: [F128; 3],
}

/// Prove THREE equal-size grand products as ONE RLC-batched GKR: the roots
/// are bound, a combiner λ is sampled, and each layer runs a SINGLE sumcheck
/// on the RLC of their gate polynomials. Each radix-four round sends four
/// independent coefficients. A fresh `λ` after every layer pins the individual
/// tail values inside their bound combination.
pub fn prove_product_triple(leaves: [Vec<F128>; 3], ps: &mut ProverState) -> ProductTriple {
    let mu = crate::log2_strict_usize(leaves[0].len());
    assert!(leaves.iter().all(|l| l.len() == 1 << mu), "batched trees must have equal size");
    let layers = leaves.map(build_layers);
    let roots = [layers[0][mu][0], layers[1][mu][0], layers[2][mu][0]];
    for root in roots {
        ps.add_scalar(root);
    }
    let mut lambda = ps.sample();

    let mut r: Vec<F128> = Vec::new();
    let mut values = roots;

    let mut i = mu;
    while i > 0 {
        let k = mu - i;
        let width = 1usize << k;
        if i % 2 == 1 {
            // Only the root can be binary: after it, the remaining depth is
            // even and every subsequent layer consumes two levels.
            debug_assert_eq!(k, 0);
            let evals = [0, 1, 2].map(|t| {
                let below = &layers[t][i - 1];
                debug_assert_eq!(below.len(), 2);
                [below[0], below[1]]
            });
            for eval in &evals {
                ps.add_scalars(eval);
            }
            let c = ps.sample();
            for (value, [e0, e1]) in values.iter_mut().zip(evals) {
                *value = interp(e0, e1, c);
            }
            lambda = ps.sample();
            r = vec![c];
            i -= 1;
        } else {
            let mut trees = [0, 1, 2]
                .map(|t| QuaternaryLayerState::new(&layers[t][i - 2], width));
            let mut eqr = if k > 0 {
                build_eq(&r[1..])
            } else {
                Vec::new()
            };
            let mut rho = Vec::with_capacity(k);
            for _ in 0..k {
                let msgs = [0, 1, 2].map(|t| trees[t].round_message(&eqr));
                ps.add_scalars(
                    &[0, 1, 2, 3].map(|n| {
                        msgs[0][n]
                            + lambda * (msgs[1][n] + lambda * msgs[2][n])
                    }),
                );
                let rk = ps.sample();
                rho.push(rk);
                for tree in &mut trees {
                    tree.fold(rk);
                }
                shrink_eq(&mut eqr);
            }
            for tree in &trees {
                ps.add_scalars(&tree.child.each_ref().map(|table| table[0]));
            }
            let c0 = ps.sample();
            let c1 = ps.sample();
            for (value, tree) in values.iter_mut().zip(&trees) {
                let lo = interp(tree.child[0][0], tree.child[1][0], c0);
                let hi = interp(tree.child[2][0], tree.child[3][0], c0);
                *value = interp(lo, hi, c1);
            }
            lambda = ps.sample();
            let mut next_point = Vec::with_capacity(k + 2);
            next_point.push(c0);
            next_point.push(c1);
            next_point.extend_from_slice(&rho);
            r = next_point;
            i -= 2;
        }
    }

    ProductTriple { roots, point: r, values }
}

/// Verify an RLC-batched triple proof ([`prove_product_triple`]): the roots,
/// a combiner `λ`, then the normalized radix-four layer sumchecks.
pub fn verify_product_triple(mu: usize, vs: &mut VerifierState) -> Result<ProductTriple, GkrError> {
    let mut roots = [F128::ZERO; 3];
    for root in &mut roots {
        *root = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    }
    let mut lambda = vs.sample();
    let mut r: Vec<F128> = Vec::new();
    let mut values = roots;

    let mut i = mu;
    while i > 0 {
        let k = mu - i;
        let mut claim = values[0] + lambda * (values[1] + lambda * values[2]);
        if i % 2 == 1 {
            debug_assert_eq!(k, 0);
            let mut evals = [[F128::ZERO; 2]; 3];
            for eval in evals.iter_mut().flatten() {
                *eval = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
            }
            let products = evals.map(|[e0, e1]| e0 * e1);
            if claim
                != products[0] + lambda * (products[1] + lambda * products[2])
            {
                return Err(GkrError::LayerMismatch { layer: i });
            }
            let c = vs.sample();
            for (value, [e0, e1]) in values.iter_mut().zip(evals) {
                *value = interp(e0, e1, c);
            }
            lambda = vs.sample();
            r = vec![c];
            i -= 1;
        } else {
            let mut rho = Vec::with_capacity(k);
            for &rj in r.iter().take(k) {
                let message =
                    vs.next_scalars(4).map_err(|_| GkrError::Truncated)?;
                let rk = vs.sample();
                rho.push(rk);
                claim = quartic_eval_from_eq(
                    claim, rj, message[0], message[1], message[2], message[3],
                    rk,
                );
            }
            let mut evals = [[F128::ZERO; 4]; 3];
            for eval in evals.iter_mut().flatten() {
                *eval = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
            }
            let products = evals.map(|e| e[0] * e[1] * e[2] * e[3]);
            if claim
                != products[0] + lambda * (products[1] + lambda * products[2])
            {
                return Err(GkrError::LayerMismatch { layer: i });
            }
            let c0 = vs.sample();
            let c1 = vs.sample();
            for (value, e) in values.iter_mut().zip(evals) {
                *value = interp(
                    interp(e[0], e[1], c0),
                    interp(e[2], e[3], c0),
                    c1,
                );
            }
            lambda = vs.sample();
            let mut next_point = Vec::with_capacity(k + 2);
            next_point.push(c0);
            next_point.push(c1);
            next_point.extend_from_slice(&rho);
            r = next_point;
            i -= 2;
        }
    }

    Ok(ProductTriple { roots, point: r, values })
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::multilinear::mle_eval;

    #[test]
    fn quartic_round_message_matches_direct_evaluation() {
        for width in [2, 4, 8, 16] {
            let below: Vec<F128> = (0..4 * width)
                .map(|i| F128::new((17 * i + width + 1) as u64, (i * i + 3) as u64))
                .collect();
            let state = QuaternaryLayerState::new(&below, width);
            let eqr: Vec<F128> = (0..width / 2)
                .map(|i| F128::new((31 * i + 5) as u64, (7 * i + 1) as u64))
                .collect();
            let [difference, c2, c3, c4] = state.round_message(&eqr);
            let direct = |z: F128| {
                (0..width / 2).fold(F128::ZERO, |sum, row| {
                    let values = state.child.each_ref().map(|child| {
                        interp(child[2 * row], child[2 * row + 1], z)
                    });
                    sum + eqr[row] * values[0] * values[1] * values[2] * values[3]
                })
            };
            let c0 = direct(F128::ZERO);
            let c1 = difference + c2 + c3 + c4;
            for z in [
                F128::ZERO,
                F128::ONE,
                F128::generator(),
                F128::generator() * F128::generator(),
            ] {
                assert_eq!(
                    c0 + z * (c1 + z * (c2 + z * (c3 + z * c4))),
                    direct(z)
                );
            }
        }
    }

    #[test]
    fn radix_four_roundtrip_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let leaves: [Vec<F128>; 3] = [0, 1, 2].map(|lane| {
                (0..1usize << mu)
                    .map(|row| F128::new((1 + row + lane * 100_003) as u64, 0))
                    .collect()
            });
            let expected_roots = leaves.each_ref().map(|lane| {
                lane.iter()
                    .copied()
                    .fold(F128::ONE, |product, value| product * value)
            });
            let mut ps = ProverState::new(b"radix-four-gkr-test", &[]);
            let proved = prove_product_triple(leaves.clone(), &mut ps);
            assert_eq!(proved.roots, expected_roots);
            for lane in 0..3 {
                assert_eq!(
                    proved.values[lane],
                    mle_eval(&leaves[lane], &proved.point)
                );
            }

            let proof = ps.into_proof();
            let mut vs = VerifierState::new(b"radix-four-gkr-test", &proof, &[]);
            let verified = verify_product_triple(mu, &mut vs).expect("GKR verifies");
            assert_eq!(verified.roots, proved.roots);
            assert_eq!(verified.point, proved.point);
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }
}
