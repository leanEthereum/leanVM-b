//! The grand product via GKR (§4.3): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the binary product tree, reducing one claim per layer down
//! to a single leaf evaluation `Ṽ_0(ζ)`. Layer relation (low-bit split): `V_i(x)
//! = V_{i-1}(0,x)·V_{i-1}(1,x)`; each layer's sumcheck uses the eq-trick, so its
//! round univariate is degree 2 (3 evaluations) plus a degree-1 fold-back line.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).

use crate::PAR_THRESHOLD;
use crate::transcript::{ProverState, VerifierState};
use primitives::field::{F192, F192Unreduced, mul_by_g_e};
use primitives::multilinear::lagrange_eval;
use primitives::multilinear::{eq_table, interp, tri_nodes, xor3};
use rayon::prelude::*;

/// Bind the lowest variable of `src` into `dst` (in parallel for large tables):
/// `dst[i] = interp(src[2i], src[2i+1], rho)`. Writing into a caller-owned
/// scratch buffer instead of a fresh Vec lets each layer's rounds ping-pong two
/// allocations instead of allocating (and page-faulting) per round.
/// Deliberately scalar: pairing adjacent outputs through [`F192::mul2`]
/// measures slower (2.14 vs 1.75 ns/output). The mul has the loop-invariant
/// `rho` on one side, the OoO core already overlaps the independent
/// iterations, and the pair kernel's third NEON fold outweighs its 2-PMULL
/// saving once nothing is latency-bound.
fn par_fold_into(src: &[F192], rho: F192, dst: &mut Vec<F192>) {
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
    SumcheckInconsistent { layer: usize, round: usize },
    LayerMismatch { layer: usize },
}

/// Build every product-tree layer: `layers[0]` = leaves, `layers[μ]` = `[root]`.
/// Deliberately scalar: routing adjacent output pairs through [`F192::mul2`]
/// wins ~4% single-threaded but loses ~2% end to end (interleaved A/B: 1339 vs
/// 1370 ms bus-GKR at `LEANVM_XMSS_N=1024`, 10 threads); at full parallelism
/// this loop is memory-bandwidth-bound and the paired form only adds overhead.
fn build_layers(leaves: Vec<F192>) -> Vec<Vec<F192>> {
    let mut layers = vec![leaves];
    while layers.last().unwrap().len() > 1 {
        let cur = layers.last().unwrap();
        let half = cur.len() / 2;
        let next: Vec<F192> = if half >= PAR_THRESHOLD {
            (0..half).into_par_iter().map(|j| cur[2 * j] * cur[2 * j + 1]).collect()
        } else {
            (0..half).map(|j| cur[2 * j] * cur[2 * j + 1]).collect()
        };
        layers.push(next);
    }
    layers
}

/// One tree's per-layer sumcheck state: the strided even/odd tables plus the
/// ping-pong fold scratch (allocated once per layer, reused every round).
struct LayerState {
    even: Vec<F192>,
    odd: Vec<F192>,
    even_next: Vec<F192>,
    odd_next: Vec<F192>,
}

impl LayerState {
    fn new(below: &[F192], width: usize) -> Self {
        let strided_copy = |off: usize| -> Vec<F192> {
            if width >= PAR_THRESHOLD {
                (0..width).into_par_iter().map(|j| below[2 * j + off]).collect()
            } else {
                (0..width).map(|j| below[2 * j + off]).collect()
            }
        };
        Self {
            even: strided_copy(0),
            odd: strided_copy(1),
            even_next: Vec::new(),
            odd_next: Vec::new(),
        }
    }

    /// The layer sumcheck's degree-2 round univariate at nodes `{0, 1, g}`.
    fn round_message(&self, eqr: &[F192]) -> [F192; 3] {
        let half = self.even.len() / 2;
        let (even, odd) = (&self.even, &self.odd);
        let acc_u = round_message_acc(even, odd, eqr, half);
        [acc_u[0].reduce(), acc_u[1].reduce(), acc_u[2].reduce()]
    }

    /// Bind this round's variable at the (shared) challenge `rk`.
    fn fold(&mut self, rk: F192) {
        par_fold_into(&self.even, rk, &mut self.even_next);
        std::mem::swap(&mut self.even, &mut self.even_next);
        par_fold_into(&self.odd, rk, &mut self.odd_next);
        std::mem::swap(&mut self.odd, &mut self.odd_next);
    }
}

#[inline]
fn round_message_summand(even: &[F192], odd: &[F192], eqr: &[F192], idx: usize) -> [F192Unreduced; 3] {
    let (lo, hi) = (2 * idx, 2 * idx + 1);
    let eq = eqr[idx];
    let t0 = even[lo] * odd[lo];
    let t1 = even[hi] * odd[hi];
    // Node 2 is the generator `g = x`, so `g·diff = mul_by_g_e(diff)` — two
    // shift-folds, not a carry-less mul (bit-identical to `nodes[2] * diff`).
    let (even_diff, odd_diff) = (even[lo] + even[hi], odd[lo] + odd[hi]);
    let (even_at2, odd_at2) = (even[lo] + mul_by_g_e(even_diff), odd[lo] + mul_by_g_e(odd_diff));
    let t2 = even_at2 * odd_at2;
    // Defer the mod-P reduction of the outer eq·(…) products: XOR-accumulate
    // the unreduced Karatsuba parts and reduce once per round accumulator.
    [eq.mul_unreduced(t0), eq.mul_unreduced(t1), eq.mul_unreduced(t2)]
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
fn round_message_acc_scalar(even: &[F192], odd: &[F192], eqr: &[F192], half: usize) -> [F192Unreduced; 3] {
    let summand = |idx| round_message_summand(even, odd, eqr, idx);
    if half >= PAR_THRESHOLD {
        (0..half)
            .into_par_iter()
            .map(summand)
            .reduce(|| [F192Unreduced::ZERO; 3], xor3)
    } else {
        (0..half).map(summand).fold([F192Unreduced::ZERO; 3], xor3)
    }
}

fn round_message_acc(even: &[F192], odd: &[F192], eqr: &[F192], half: usize) -> [F192Unreduced; 3] {
    debug_assert!(even.len() >= 2 * half);
    debug_assert!(odd.len() >= 2 * half);
    debug_assert!(eqr.len() >= half);

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let batches = half / 8;
        let batch = |i: usize| {
            // SAFETY: every batch consumes sixteen even/odd values and eight
            // eq values inside the lengths asserted above; target features are
            // enabled at compile time.
            unsafe {
                round_message_batch_avx512(
                    even.as_ptr().add(16 * i),
                    odd.as_ptr().add(16 * i),
                    eqr.as_ptr().add(8 * i),
                )
            }
        };
        let mut acc = if half >= PAR_THRESHOLD {
            (0..batches)
                .into_par_iter()
                .map(batch)
                .reduce(|| [F192Unreduced::ZERO; 3], xor3)
        } else {
            (0..batches).map(batch).fold([F192Unreduced::ZERO; 3], xor3)
        };
        for idx in 8 * batches..half {
            acc = xor3(acc, round_message_summand(even, odd, eqr, idx));
        }
        acc
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    {
        round_message_acc_scalar(even, odd, eqr, half)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Copy)]
struct F192x8 {
    c0: core::arch::x86_64::__m512i,
    c1: core::arch::x86_64::__m512i,
    c2: core::arch::x86_64::__m512i,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Copy)]
struct Clmulx8 {
    /// Products for input lanes 0, 2, 4, 6, one u128 per 128-bit lane.
    even: core::arch::x86_64::__m512i,
    /// Products for input lanes 1, 3, 5, 7, one u128 per 128-bit lane.
    odd: core::arch::x86_64::__m512i,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn gather_f192x8_avx512(ptr: *const F192, element_stride: i64) -> F192x8 {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn gather_coeff(ptr: *const F192, stride_qwords: i64, coefficient: i64) -> __m512i {
        let offsets = _mm512_set_epi64(
            7 * stride_qwords + coefficient,
            6 * stride_qwords + coefficient,
            5 * stride_qwords + coefficient,
            4 * stride_qwords + coefficient,
            3 * stride_qwords + coefficient,
            2 * stride_qwords + coefficient,
            stride_qwords + coefficient,
            coefficient,
        );
        // SAFETY: the caller guarantees all indexed F192 elements are valid.
        unsafe { _mm512_i64gather_epi64::<8>(offsets, ptr.cast()) }
    }

    let stride_qwords = 3 * element_stride;
    // SAFETY: inherited from the caller; coefficient offsets 0..2 are within
    // each repr(C) F192 value.
    unsafe {
        F192x8 {
            c0: gather_coeff(ptr, stride_qwords, 0),
            c1: gather_coeff(ptr, stride_qwords, 1),
            c2: gather_coeff(ptr, stride_qwords, 2),
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn xor_f192x8_avx512(a: F192x8, b: F192x8) -> F192x8 {
    use core::arch::x86_64::_mm512_xor_si512;
    F192x8 {
        c0: _mm512_xor_si512(a.c0, b.c0),
        c1: _mm512_xor_si512(a.c1, b.c1),
        c2: _mm512_xor_si512(a.c2, b.c2),
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn clmul_x8_avx512(a: core::arch::x86_64::__m512i, b: core::arch::x86_64::__m512i) -> Clmulx8 {
    use core::arch::x86_64::*;
    Clmulx8 {
        even: _mm512_clmulepi64_epi128::<0x00>(a, b),
        odd: _mm512_clmulepi64_epi128::<0x11>(a, b),
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn xor_clmul_x8_avx512(a: Clmulx8, b: Clmulx8) -> Clmulx8 {
    use core::arch::x86_64::_mm512_xor_si512;
    Clmulx8 {
        even: _mm512_xor_si512(a.even, b.even),
        odd: _mm512_xor_si512(a.odd, b.odd),
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn mul_unreduced_f192x8_avx512(a: F192x8, b: F192x8) -> [Clmulx8; 5] {
    // Six-product Karatsuba over the three base-field coefficients.
    unsafe {
        let p0 = clmul_x8_avx512(a.c0, b.c0);
        let p1 = clmul_x8_avx512(a.c1, b.c1);
        let p2 = clmul_x8_avx512(a.c2, b.c2);
        let p01 = clmul_x8_avx512(
            core::arch::x86_64::_mm512_xor_si512(a.c0, a.c1),
            core::arch::x86_64::_mm512_xor_si512(b.c0, b.c1),
        );
        let p02 = clmul_x8_avx512(
            core::arch::x86_64::_mm512_xor_si512(a.c0, a.c2),
            core::arch::x86_64::_mm512_xor_si512(b.c0, b.c2),
        );
        let p12 = clmul_x8_avx512(
            core::arch::x86_64::_mm512_xor_si512(a.c1, a.c2),
            core::arch::x86_64::_mm512_xor_si512(b.c1, b.c2),
        );
        let c1 = xor_clmul_x8_avx512(xor_clmul_x8_avx512(p01, p0), p1);
        let c2 = xor_clmul_x8_avx512(xor_clmul_x8_avx512(xor_clmul_x8_avx512(p02, p0), p1), p2);
        let c3 = xor_clmul_x8_avx512(xor_clmul_x8_avx512(p12, p1), p2);
        [p0, c1, c2, c3, p2]
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn reduce_clmul_x8_avx512(product: Clmulx8) -> core::arch::x86_64::__m512i {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn reduce_half(product: __m512i, r: __m512i) -> __m512i {
        let t = _mm512_clmulepi64_epi128::<0x01>(product, r);
        let u = _mm512_clmulepi64_epi128::<0x01>(t, r);
        _mm512_xor_si512(_mm512_xor_si512(product, t), u)
    }

    let r = _mm512_set1_epi64(0x1b);
    unsafe {
        let even = reduce_half(product.even, r);
        let odd = _mm512_shuffle_epi32::<0x4e>(reduce_half(product.odd, r));
        _mm512_mask_blend_epi64(0xaa, even, odd)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn reduce_f192x8_avx512(product: [Clmulx8; 5]) -> F192x8 {
    unsafe {
        let d0 = xor_clmul_x8_avx512(product[0], product[3]);
        let d1 = xor_clmul_x8_avx512(xor_clmul_x8_avx512(product[1], product[3]), product[4]);
        let d2 = xor_clmul_x8_avx512(product[2], product[4]);
        F192x8 {
            c0: reduce_clmul_x8_avx512(d0),
            c1: reduce_clmul_x8_avx512(d1),
            c2: reduce_clmul_x8_avx512(d2),
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn mul_f192x8_avx512(a: F192x8, b: F192x8) -> F192x8 {
    unsafe { reduce_f192x8_avx512(mul_unreduced_f192x8_avx512(a, b)) }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn mul_by_g_f192x8_avx512(value: F192x8) -> F192x8 {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn mul_coeff(value: __m512i) -> __m512i {
        let carry = _mm512_srli_epi64::<63>(value);
        let fold = _mm512_xor_si512(
            _mm512_xor_si512(carry, _mm512_slli_epi64::<1>(carry)),
            _mm512_xor_si512(_mm512_slli_epi64::<3>(carry), _mm512_slli_epi64::<4>(carry)),
        );
        _mm512_xor_si512(_mm512_slli_epi64::<1>(value), fold)
    }

    unsafe {
        F192x8 {
            c0: mul_coeff(value.c0),
            c1: mul_coeff(value.c1),
            c2: mul_coeff(value.c2),
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn horizontal_xor_f192_product_avx512(product: [Clmulx8; 5]) -> F192Unreduced {
    use core::arch::x86_64::*;

    let mut w = [0u64; 10];
    for (coefficient, product) in product.into_iter().enumerate() {
        let combined = _mm512_xor_si512(product.even, product.odd);
        let mut lanes = [0u64; 8];
        // SAFETY: lanes has exactly one ZMM register of writable storage.
        unsafe { _mm512_storeu_si512(lanes.as_mut_ptr().cast(), combined) };
        w[2 * coefficient] = lanes[0] ^ lanes[2] ^ lanes[4] ^ lanes[6];
        w[2 * coefficient + 1] = lanes[1] ^ lanes[3] ^ lanes[5] ^ lanes[7];
    }
    F192Unreduced { w }
}

/// Eight independent GKR round summands, XOR-reduced into the same three
/// deferred-reduction accumulators as the scalar path.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX-512F. `even` and `odd` must each address sixteen
/// F192 values; `eqr` must address eight.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn round_message_batch_avx512(even: *const F192, odd: *const F192, eqr: *const F192) -> [F192Unreduced; 3] {
    unsafe {
        let even_lo = gather_f192x8_avx512(even, 2);
        let even_hi = gather_f192x8_avx512(even.add(1), 2);
        let odd_lo = gather_f192x8_avx512(odd, 2);
        let odd_hi = gather_f192x8_avx512(odd.add(1), 2);
        let eq = gather_f192x8_avx512(eqr, 1);

        let t0 = mul_f192x8_avx512(even_lo, odd_lo);
        let t1 = mul_f192x8_avx512(even_hi, odd_hi);
        let even_at2 = xor_f192x8_avx512(even_lo, mul_by_g_f192x8_avx512(xor_f192x8_avx512(even_lo, even_hi)));
        let odd_at2 = xor_f192x8_avx512(odd_lo, mul_by_g_f192x8_avx512(xor_f192x8_avx512(odd_lo, odd_hi)));
        let t2 = mul_f192x8_avx512(even_at2, odd_at2);

        [
            horizontal_xor_f192_product_avx512(mul_unreduced_f192x8_avx512(eq, t0)),
            horizontal_xor_f192_product_avx512(mul_unreduced_f192x8_avx512(eq, t1)),
            horizontal_xor_f192_product_avx512(mul_unreduced_f192x8_avx512(eq, t2)),
        ]
    }
}

/// Shrink `eqr` to the next round's suffix table (in place: the read cursor
/// `2·idx` stays ahead of the write cursor `idx`). `eq(r_j,0) + eq(r_j,1) = 1`,
/// so summing adjacent entries marginalizes the bound variable with no
/// multiplies (vs rebuilding with ~2^{k-j} muls per round).
fn shrink_eq(eqr: &mut Vec<F192>) {
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
    pub roots: [F192; 3],
    pub point: Vec<F192>,
    pub values: [F192; 3],
}

/// Prove THREE equal-size grand products as ONE RLC-batched GKR: the roots
/// are bound, a combiner λ is sampled, and each layer runs a SINGLE sumcheck
/// on the combined summand `eq·Σ_t λᵗ·eᵗ·oᵗ` (one message triple per round,
/// one shared challenge), so all trees reduce to leaf claims at the SAME
/// point. Each layer binds the six tail evaluations and then samples a FRESH
/// λ for the next layer, which pins the individual values inside the bound
/// combination (Schwartz–Zippel); the last layer's individuals are pinned by
/// the decompose identities. Used for the bus push/pull/count trees: push and
/// pull match block-for-block, and the caller pads the count tree with
/// identity leaves up to their μ.
pub fn prove_product_triple(leaves: [Vec<F192>; 3], ps: &mut ProverState) -> ProductTriple {
    let mu = crate::log2_strict_usize(leaves[0].len());
    assert!(
        leaves.iter().all(|l| l.len() == 1 << mu),
        "batched trees must have equal size"
    );
    let layers = leaves.map(build_layers);
    let roots = [layers[0][mu][0], layers[1][mu][0], layers[2][mu][0]];
    for root in roots {
        ps.add_scalar(root);
    }
    let mut lambda = ps.sample();

    let mut r: Vec<F192> = Vec::new();
    let mut values = roots;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let width = 1usize << k;
        let mut trees = [0, 1, 2].map(|t| LayerState::new(&layers[t][i - 1], width));
        // The challenges are shared, so ONE eq table serves all trees.
        let mut eqr: Vec<F192> = if k > 0 { eq_table(&r[1..]) } else { Vec::new() };

        let mut rho = Vec::with_capacity(k);
        for _ in 0..k {
            let msgs = [0, 1, 2].map(|t| trees[t].round_message(&eqr));
            ps.add_scalars(&[0, 1, 2].map(|n| msgs[0][n] + lambda * (msgs[1][n] + lambda * msgs[2][n])));
            let rk = ps.sample();
            rho.push(rk);
            for tree in &mut trees {
                tree.fold(rk);
            }
            shrink_eq(&mut eqr);
        }

        for tree in &trees {
            ps.add_scalar(tree.even[0]);
            ps.add_scalar(tree.odd[0]);
        }
        let c = ps.sample();
        for (value, tree) in values.iter_mut().zip(&trees) {
            *value = interp(tree.even[0], tree.odd[0], c);
        }
        lambda = ps.sample(); // fresh combiner: pins the individual tail values

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    ProductTriple {
        roots,
        point: r,
        values,
    }
}

/// Verify an RLC-batched triple proof ([`prove_product_triple`]): the roots,
/// a combiner λ, then per layer ONE standard sumcheck on the combined claim,
/// six tail evaluations checked as `eq·Σ_t λᵗ·e₀ᵗ·e₁ᵗ`, a line challenge, and
/// a fresh λ. Returns the roots and the shared-point leaf claims.
pub fn verify_product_triple(mu: usize, vs: &mut VerifierState) -> Result<ProductTriple, GkrError> {
    let mut roots = [F192::ZERO; 3];
    for root in &mut roots {
        *root = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    }
    let mut lambda = vs.sample();
    let nodes = tri_nodes();
    let mut r: Vec<F192> = Vec::new();
    let mut values = roots;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let mut claim = values[0] + lambda * (values[1] + lambda * values[2]);
        let mut rho = Vec::with_capacity(k);
        let mut eq_acc = F192::ONE; // ∏_{l<round} eq(r_l, ρ_l)
        for (round, &rj) in r.iter().enumerate().take(k) {
            let msg = vs.next_scalars(3).map_err(|_| GkrError::Truncated)?;
            if eq_acc * ((F192::ONE + rj) * msg[0] + rj * msg[1]) != claim {
                return Err(GkrError::SumcheckInconsistent { layer: i, round });
            }
            let rk = vs.sample();
            rho.push(rk);
            eq_acc *= F192::ONE + rj + rk;
            claim = eq_acc * lagrange_eval(&nodes, &msg, rk);
        }
        let mut evals = [[F192::ZERO; 2]; 3];
        for eval in evals.iter_mut().flatten() {
            *eval = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        }
        let products = evals.map(|[e0, e1]| e0 * e1);
        if claim != eq_acc * (products[0] + lambda * (products[1] + lambda * products[2])) {
            return Err(GkrError::LayerMismatch { layer: i });
        }
        let c = vs.sample();
        for (value, [e0, e1]) in values.iter_mut().zip(evals) {
            *value = interp(e0, e1, c);
        }
        lambda = vs.sample(); // fresh combiner: pins the individual tail values

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    Ok(ProductTriple {
        roots,
        point: r,
        values,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_ext(state: &mut u64) -> F192 {
        F192::new(splitmix64(state), splitmix64(state), splitmix64(state))
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[test]
    fn round_message_avx512_matches_scalar() {
        let mut state = 0x91e1_0da5_c79b_6432;
        for half in [8usize, 9, 16, 17] {
            for _ in 0..50 {
                let even: Vec<F192> = (0..2 * half).map(|_| rand_ext(&mut state)).collect();
                let odd: Vec<F192> = (0..2 * half).map(|_| rand_ext(&mut state)).collect();
                let eqr: Vec<F192> = (0..half).map(|_| rand_ext(&mut state)).collect();
                let want = (0..half)
                    .map(|idx| round_message_summand(&even, &odd, &eqr, idx))
                    .fold([F192Unreduced::ZERO; 3], xor3);
                assert_eq!(round_message_acc(&even, &odd, &eqr, half), want, "half={half}");
            }
        }
    }
}
