//! The grand product via GKR (§sec:gkr): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the product tree, reducing the root to one leaf evaluation
//! `Ṽ_0(ζ)`. Two binary levels are contracted at a time: a radix-four layer has
//! relation `V_i(x)=∏_{a,b∈{0,1}}V_{i-2}(a,b,x)`. Its normalized eq-trick
//! sumcheck has degree four. An odd-depth tree starts with one binary layer.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).

use crate::PAR_THRESHOLD;
use crate::transcript::{Challenger, ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F192, F192Unreduced};
use primitives::multilinear::{eq_table, interp, quartic_eval_from_eq, shrink_eq_low};
use zk_alloc::ArenaVec;

#[inline]
fn mul_pair(a: [F192; 2], b: [F192; 2]) -> [F192; 2] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"))]
    {
        // SAFETY: both features are enabled for the whole crate.
        unsafe { primitives::field::gf2_64x3::x86_64::mul_vec2(a, b) }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: PMULL is enabled for the whole crate.
        unsafe {
            [
                primitives::field::gf2_64x3::aarch64::mul_karatsuba(a[0], b[0]),
                primitives::field::gf2_64x3::aarch64::mul_karatsuba(a[1], b[1]),
            ]
        }
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    {
        [a[0] * b[0], a[1] * b[1]]
    }
}

#[inline]
fn mul_four(a: [F192; 4], b: [F192; 4]) -> [F192; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        // SAFETY: both features are enabled for the whole crate.
        unsafe { primitives::field::gf2_64x3::x86_64::mul_vec4(a, b) }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    {
        let low = mul_pair([a[0], a[1]], [b[0], b[1]]);
        let high = mul_pair([a[2], a[3]], [b[2], b[3]]);
        [low[0], low[1], high[0], high[1]]
    }
}

#[inline]
fn mul_unreduced_four(a: F192, b: [F192; 4]) -> [F192Unreduced; 4] {
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        // SAFETY: both features are enabled for the whole crate.
        unsafe { primitives::field::gf2_64x3::x86_64::mul_unreduced_vec4([a; 4], b) }
    }
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "vpclmulqdq",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    {
        // SAFETY: both features are enabled for the whole crate.
        unsafe {
            let low = primitives::field::gf2_64x3::x86_64::mul_unreduced_vec2([a; 2], [b[0], b[1]]);
            let high = primitives::field::gf2_64x3::x86_64::mul_unreduced_vec2([a; 2], [b[2], b[3]]);
            [low[0], low[1], high[0], high[1]]
        }
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: PMULL is enabled for the whole crate.
        unsafe { b.map(|value| primitives::field::gf2_64x3::aarch64::mul_unreduced_neon(a, value)) }
    }
    #[cfg(not(any(
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"),
        all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx2"),
        all(target_arch = "aarch64", target_feature = "aes")
    )))]
    {
        b.map(|value| a.mul_unreduced(value))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GkrError {
    Truncated,
    LayerMismatch { layer: usize },
}

/// Rows per parallel window: enough tasks to keep every thread fed, but not so few
/// rows per task that dispatch dominates.
fn window_rows(total: usize) -> usize {
    let tasks = parallel::num_threads() * 4;
    total.div_ceil(tasks).clamp(32, 1 << 12)
}

/// Build only the levels consumed by radix four: `0,2,4,…`, plus a final
/// binary root when the logical depth is odd.
fn build_layers(leaves: ArenaVec<F192>, mu: usize) -> Vec<ArenaVec<F192>> {
    assert!(!leaves.is_empty());
    assert!(leaves.len() <= 1usize << mu);
    // At mu = 22 the leaf level alone is hundreds of megabytes, and every level
    // dies with the proof.
    let mut layers: Vec<ArenaVec<F192>> = (0..=mu).map(|_| ArenaVec::new()).collect();
    layers[0] = leaves;
    let mut level = 0;
    while level + 2 <= mu {
        let current = &layers[level];
        let full_rows = current.len() / 4;
        let product = |row: usize| {
            let [left, right] = mul_pair(
                [current[4 * row], current[4 * row + 2]],
                [current[4 * row + 1], current[4 * row + 3]],
            );
            left * right
        };
        let mut next: ArenaVec<F192> = if current.len() == 1 {
            ArenaVec::from_iter([current[0]])
        } else if current.len() == 2 {
            ArenaVec::from_iter([current[0] * current[1]])
        } else if full_rows >= PAR_THRESHOLD {
            primitives::par_collect_arena(full_rows, product)
        } else {
            (0..full_rows).map(product).collect()
        };
        if !current.len().is_multiple_of(4) && current.len() > 2 {
            let row = full_rows;
            let child = |index| current.get(4 * row + index).copied().unwrap_or(F192::ONE);
            let [left, right] = mul_pair([child(0), child(2)], [child(1), child(3)]);
            next.push(left * right);
        }
        level += 2;
        layers[level] = next;
    }
    if level < mu {
        layers[mu] = match layers[level].as_slice() {
            [root] => ArenaVec::from_iter([*root]),
            [left, right] => ArenaVec::from_iter([*left * *right]),
            _ => unreachable!("the final binary layer has at most two explicit nodes"),
        };
    }
    layers
}

#[inline]
fn quartic_summand(lines: [[F192; 2]; 4], equality: F192) -> [F192Unreduced; 4] {
    let [left0, left2, right0, right2] = mul_four(
        [lines[0][0], lines[0][1], lines[2][0], lines[2][1]],
        [lines[1][0], lines[1][1], lines[3][0], lines[3][1]],
    );
    let [left_at_one, right_at_one, c0, c4] = mul_four(
        [lines[0][0] + lines[0][1], lines[2][0] + lines[2][1], left0, left2],
        [lines[1][0] + lines[1][1], lines[3][0] + lines[3][1], right0, right2],
    );
    let left1 = left_at_one + left0 + left2;
    let right1 = right_at_one + right0 + right2;
    let [middle, at_one, cross_even, cross_high] = mul_four(
        [left1, left0 + left1 + left2, left0 + left2, left1 + left2],
        [right1, right0 + right1 + right2, right0 + right2, right1 + right2],
    );
    let c2 = cross_even + c0 + c4 + middle;
    let c3 = cross_high + middle + c4;
    mul_unreduced_four(equality, [c0 + at_one, c2, c3, c4])
}

/// Two binary product levels contracted into one degree-four layer.
struct QuaternaryLayerState {
    /// Four child tables interleaved in their original order. This lets the
    /// prover consume a product-tree level without first transposing it.
    values: ArenaVec<F192>,
    next: ArenaVec<F192>,
    /// Logical row count after identity padding. `values` stores an arbitrary
    /// prefix; every omitted row is the constant four-tuple one.
    logical_rows: usize,
}

impl QuaternaryLayerState {
    fn new(mut values: ArenaVec<F192>, width: usize) -> Self {
        // Materialize only the incomplete final four-tuple. Every complete
        // all-one row after the arbitrary explicit prefix remains implicit.
        values.resize(4 * values.len().max(1).div_ceil(4), F192::ONE);
        debug_assert_eq!(values.len() % 4, 0);
        debug_assert!(values.len() <= 4 * width);
        let rows = (values.len() / 4).div_ceil(2);
        Self {
            values,
            // SAFETY: the first `fold` writes every slot of `next[..4 * rows]` before
            // any read (its windows cover the full pairs, its tail block the odd row),
            // and neither `round_message` nor `children` reads `next`.
            next: unsafe { ArenaVec::uninitialized(4 * rows) },
            logical_rows: width,
        }
    }

    /// `(q(0)+q(1), [X²]q, [X³]q, [X⁴]q)`.
    fn round_message(&self, equality: &[F192]) -> [F192; 4] {
        let stored_rows = self.values.len() / 4;
        let full_pairs = stored_rows / 2;
        let summand = |row: usize| -> [F192Unreduced; 4] {
            let (lo, hi) = (8 * row, 8 * row + 4);
            let lines = [0, 1, 2, 3].map(|child| {
                let at_zero = self.values[lo + child];
                [at_zero, at_zero + self.values[hi + child]]
            });
            quartic_summand(lines, equality[row])
        };
        let xor = |mut left: [F192Unreduced; 4], right: [F192Unreduced; 4]| {
            for coefficient in 0..4 {
                left[coefficient] ^= right[coefficient];
            }
            left
        };
        let rows = window_rows(full_pairs);
        let window = |index: usize| -> [F192Unreduced; 4] {
            let base = index * rows;
            (base..(base + rows).min(full_pairs)).fold([F192Unreduced::ZERO; 4], |sum, row| xor(sum, summand(row)))
        };
        let windows = full_pairs.div_ceil(rows);
        let mut message = if full_pairs >= PAR_THRESHOLD {
            parallel::map_reduce(windows, || [F192Unreduced::ZERO; 4], window, xor)
        } else {
            (0..windows).map(window).fold([F192Unreduced::ZERO; 4], xor)
        };
        if !stored_rows.is_multiple_of(2) {
            let lo = 8 * full_pairs;
            let lines = [0, 1, 2, 3].map(|child| {
                let at_zero = self.values[lo + child];
                [at_zero, at_zero + F192::ONE]
            });
            message = xor(message, quartic_summand(lines, equality[full_pairs]));
        }
        message.map(F192Unreduced::reduce)
    }

    fn fold(&mut self, challenge: F192) {
        let stored_rows = self.values.len() / 4;
        let full_rows = stored_rows / 2;
        let rows = stored_rows.div_ceil(2);
        self.next.truncate(4 * rows);
        let (values, next) = (&self.values, &mut self.next);
        let fold_row = |row: usize, destination: &mut [F192]| {
            let lo = 8 * row;
            let hi = lo + 4;
            let folds = mul_four(
                [0, 1, 2, 3].map(|child| values[lo + child] + values[hi + child]),
                [challenge; 4],
            );
            for child in 0..4 {
                destination[child] = values[lo + child] + folds[child];
            }
        };
        let window = |base: usize, destination: &mut [F192]| {
            for (row, slot) in destination.chunks_exact_mut(4).enumerate() {
                fold_row(base + row, slot);
            }
        };
        if full_rows >= PAR_THRESHOLD {
            let rows = window_rows(full_rows);
            parallel::chunks_mut(&mut next[..4 * full_rows], 4 * rows, |index, destination| {
                window(index * rows, destination);
            });
        } else {
            window(0, &mut next[..4 * full_rows]);
        }
        if !stored_rows.is_multiple_of(2) {
            let lo = 8 * full_rows;
            let folds = mul_four(
                [0, 1, 2, 3].map(|child| self.values[lo + child] + F192::ONE),
                [challenge; 4],
            );
            for child in 0..4 {
                self.next[4 * full_rows + child] = self.values[lo + child] + folds[child];
            }
        }
        std::mem::swap(&mut self.values, &mut self.next);
        self.logical_rows /= 2;
    }

    fn children(&self) -> [F192; 4] {
        debug_assert_eq!(self.values.len(), 4);
        debug_assert_eq!(self.logical_rows, 1);
        self.values[..4].try_into().unwrap()
    }
}

/// The result of a batched grand-product proof: the three roots and leaf
/// evaluations, all reduced to one shared point.
pub struct ProductTriple {
    pub roots: [F192; 3],
    pub point: Vec<F192>,
    pub values: [F192; 3],
}

/// Prove three identity-padded grand products as one RLC-batched radix-four GKR.
pub fn prove_product_triple(leaves: [ArenaVec<F192>; 3], ps: &mut ProverState) -> ProductTriple {
    let mu = crate::log2_ceil_usize(leaves[0].len());
    assert!(
        leaves.iter().all(|lane| !lane.is_empty() && lane.len() <= 1 << mu),
        "batched trees must be nonempty prefixes of the first tree's logical tree"
    );
    let mut layers = leaves.map(|lane| build_layers(lane, mu));
    let roots = [layers[0][mu][0], layers[1][mu][0], layers[2][mu][0]];
    for root in roots {
        ps.add_scalar(root);
    }
    let mut lambda = ps.sample();
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let tails = [0, 1, 2].map(|tree| {
                let below = &layers[tree][layer - 1];
                match below.as_slice() {
                    [left, right] => [*left, *right],
                    [left] => [*left, F192::ONE],
                    _ => unreachable!("the root's children have at most two explicit nodes"),
                }
            });
            for tail in &tails {
                ps.add_scalars(tail);
            }
            let challenge = ps.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = interp(left, right, challenge);
            }
            lambda = ps.sample();
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let width = 1usize << round_count;
        let mut trees =
            [0, 1, 2].map(|tree| QuaternaryLayerState::new(std::mem::take(&mut layers[tree][layer - 2]), width));
        let mut equality = if round_count > 0 {
            eq_table(&point[1..])
        } else {
            Vec::new()
        };
        let mut round_point = Vec::with_capacity(round_count);
        for _ in 0..round_count {
            let messages = [0, 1, 2].map(|tree| trees[tree].round_message(&equality));
            ps.add_scalars(&[0, 1, 2, 3].map(|coefficient| {
                messages[0][coefficient] + lambda * (messages[1][coefficient] + lambda * messages[2][coefficient])
            }));
            let challenge = ps.sample();
            round_point.push(challenge);
            for tree in &mut trees {
                tree.fold(challenge);
            }
            shrink_eq_low(&mut equality);
        }

        for tree in &trees {
            ps.add_scalars(&tree.children());
        }
        let low_challenge = ps.sample();
        let high_challenge = ps.sample();
        for (value, tree) in values.iter_mut().zip(&trees) {
            let tail = tree.children();
            *value = interp(
                interp(tail[0], tail[1], low_challenge),
                interp(tail[2], tail[3], low_challenge),
                high_challenge,
            );
        }
        lambda = ps.sample();
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    ProductTriple { roots, point, values }
}

/// Verify the RLC-batched radix-four proof.
pub fn verify_product_triple(mu: usize, vs: &mut VerifierState) -> Result<ProductTriple, GkrError> {
    let mut roots = [F192::ZERO; 3];
    for root in &mut roots {
        *root = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    }
    let mut lambda = vs.sample();
    let mut point = Vec::new();
    let mut values = roots;

    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        let mut claim = values[0] + lambda * (values[1] + lambda * values[2]);
        if layer % 2 == 1 {
            debug_assert_eq!(round_count, 0, "only the root-most layer may be binary");
            let mut tails = [[F192::ZERO; 2]; 3];
            for value in tails.iter_mut().flatten() {
                *value = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
            }
            let products = tails.map(|[left, right]| left * right);
            if claim != products[0] + lambda * (products[1] + lambda * products[2]) {
                return Err(GkrError::LayerMismatch { layer });
            }
            let challenge = vs.sample();
            for (value, [left, right]) in values.iter_mut().zip(tails) {
                *value = interp(left, right, challenge);
            }
            lambda = vs.sample();
            point = vec![challenge];
            layer -= 1;
            continue;
        }

        let mut round_point = Vec::with_capacity(round_count);
        for &equality_point in point.iter().take(round_count) {
            let message = vs.next_scalars(4).map_err(|_| GkrError::Truncated)?;
            let challenge = vs.sample();
            round_point.push(challenge);
            claim = quartic_eval_from_eq(
                claim,
                equality_point,
                message[0],
                message[1],
                message[2],
                message[3],
                challenge,
            );
        }
        let mut tails = [[F192::ZERO; 4]; 3];
        for value in tails.iter_mut().flatten() {
            *value = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        }
        let products = tails.map(|tail| tail[0] * tail[1] * tail[2] * tail[3]);
        if claim != products[0] + lambda * (products[1] + lambda * products[2]) {
            return Err(GkrError::LayerMismatch { layer });
        }
        let low_challenge = vs.sample();
        let high_challenge = vs.sample();
        for (value, tail) in values.iter_mut().zip(tails) {
            *value = interp(
                interp(tail[0], tail[1], low_challenge),
                interp(tail[2], tail[3], low_challenge),
                high_challenge,
            );
        }
        lambda = vs.sample();
        point = vec![low_challenge, high_challenge];
        point.extend_from_slice(&round_point);
        layer -= 2;
    }

    Ok(ProductTriple { roots, point, values })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mle_eval_e(table: &[F192], point: &[F192]) -> F192 {
        assert_eq!(table.len(), 1 << point.len());
        let mut folded = table.to_vec();
        for &challenge in point {
            let half = folded.len() / 2;
            for row in 0..half {
                folded[row] = interp(folded[2 * row], folded[2 * row + 1], challenge);
            }
            folded.truncate(half);
        }
        folded[0]
    }

    #[test]
    fn quartic_round_message_matches_direct_evaluation() {
        for width in [2, 4, 8, 16] {
            let below: ArenaVec<F192> = (0..4 * width)
                .map(|i| F192::new((17 * i + width + 1) as u64, (i * i + 3) as u64, (5 * i + 7) as u64))
                .collect();
            let state = QuaternaryLayerState::new(below, width);
            let equality: Vec<F192> = (0..width / 2)
                .map(|i| F192::new((31 * i + 5) as u64, (7 * i + 1) as u64, (11 * i + 9) as u64))
                .collect();
            let [difference, c2, c3, c4] = state.round_message(&equality);
            let direct = |point: F192| {
                (0..width / 2).fold(F192::ZERO, |sum, row| {
                    let values = [0, 1, 2, 3]
                        .map(|child| interp(state.values[8 * row + child], state.values[8 * row + 4 + child], point));
                    sum + equality[row] * values[0] * values[1] * values[2] * values[3]
                })
            };
            let c0 = direct(F192::ZERO);
            let c1 = difference + c2 + c3 + c4;
            for point in [F192::ZERO, F192::ONE, F192::Y, F192::Y.square()] {
                assert_eq!(
                    c0 + point * (c1 + point * (c2 + point * (c3 + point * c4))),
                    direct(point)
                );
            }
        }
    }

    #[test]
    fn radix_four_roundtrip_at_even_and_odd_depths() {
        for mu in 0..=10 {
            let leaves: [Vec<F192>; 3] = [0, 1, 2].map(|lane| {
                (0..1usize << mu)
                    .map(|row| F192::new((1 + row + lane * 100_003) as u64, row as u64, lane as u64))
                    .collect()
            });
            let expected_roots = leaves
                .each_ref()
                .map(|lane| lane.iter().copied().fold(F192::ONE, |product, value| product * value));
            let mut ps = ProverState::new(b"radix-four-gkr-test", &[]);
            let proved = prove_product_triple(leaves.each_ref().map(|l| ArenaVec::from_slice(l.as_slice())), &mut ps);
            assert_eq!(proved.roots, expected_roots);
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&leaves[lane], &proved.point));
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

    #[test]
    fn implicit_identity_suffix_matches_dense_padding() {
        for mu in 3..=10 {
            let lengths = [(1usize << mu) - 3, (1usize << (mu - 1)) + 1, (1usize << (mu - 2)) + 3];
            let leaves: [Vec<F192>; 3] = std::array::from_fn(|lane| {
                (0..lengths[lane])
                    .map(|row| F192::new((3 + row + lane * 10_007) as u64, row as u64, lane as u64))
                    .collect()
            });
            let dense = leaves.each_ref().map(|lane| {
                let mut padded = lane.clone();
                padded.resize(1 << mu, F192::ONE);
                padded
            });
            let mut sparse_ps = ProverState::new(b"sparse-radix-four-gkr-test", &[]);
            let proved = prove_product_triple(
                leaves.each_ref().map(|l| ArenaVec::from_slice(l.as_slice())),
                &mut sparse_ps,
            );
            for lane in 0..3 {
                assert_eq!(proved.values[lane], mle_eval_e(&dense[lane], &proved.point));
                assert_eq!(
                    proved.roots[lane],
                    dense[lane]
                        .iter()
                        .copied()
                        .fold(F192::ONE, |product, value| product * value)
                );
            }
            let proof = sparse_ps.into_proof();
            let mut dense_ps = ProverState::new(b"sparse-radix-four-gkr-test", &[]);
            let dense_proved = prove_product_triple(
                dense.each_ref().map(|l| ArenaVec::from_slice(l.as_slice())),
                &mut dense_ps,
            );
            assert_eq!(dense_proved.roots, proved.roots);
            assert_eq!(dense_proved.point, proved.point);
            assert_eq!(dense_proved.values, proved.values);
            assert_eq!(dense_ps.into_proof().stream, proof.stream);
            let mut vs = VerifierState::new(b"sparse-radix-four-gkr-test", &proof, &[]);
            let verified = verify_product_triple(mu, &mut vs).expect("GKR verifies");
            assert_eq!(verified.roots, proved.roots);
            assert_eq!(verified.point, proved.point);
            assert_eq!(verified.values, proved.values);
            vs.finish().expect("proof stream is consumed");
        }
    }
}
