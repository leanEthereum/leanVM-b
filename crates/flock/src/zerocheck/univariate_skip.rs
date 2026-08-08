// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Round-1 (univariate skip): live helpers, plus the reference oracles the optimized kernels are
//! checked against.
//!
//! The module is two disjoint halves:
//!
//! - **Live in production**: the [`build_eq`] re-export, [`pack_bits`], [`SplitEq`] and
//!   [`ntt_extend_vec`]. The optimized round-1 kernel
//!   ([`super::univariate_skip_optimized`]) and the round-2 kernel ([`super::multilinear`])
//!   are built on these.
//! - **Test-only oracles**, below the banner and all `#[cfg(test)]`: `round1_naive`,
//!   `round1_extract_c`, `round1_extract_c_packed`, `round1_extract_c_packed_with_s_hat_v` and
//!   `round1_evals_on_s`. They translate the protocol formula directly, so the optimized kernels
//!   can be diffed against something obviously correct.
//!
//! The round-1 message is `(P^{AB}, P^C)`, each a length-`2^k_skip` vector
//! of F192 values. They are evaluations on the NTT domain `Λ` of the
//! polynomial (over λ) defined by
//!
//!   P^{AB}(λ) = Σ_{x ∈ {0,1}^{m-k_skip}} eq(r_rest, x) · φ₈(â(λ, x) · b̂(λ, x))
//!   P^C(λ)   = Σ_{x ∈ {0,1}^{m-k_skip}} eq(r_rest, x) · φ₈(ĉ(λ, x))
//!
//! where â(λ, x), b̂(λ, x), ĉ(λ, x) ∈ F₂⁸ are the values at λ of the
//! univariate polynomial whose evaluations on `S = {0,…,2^k_skip − 1}` are
//! the boolean witness values `a(s, x), b(s, x), c(s, x)`. The polynomial is
//! recovered via `inv_NTT_S`; we then evaluate on `Λ = {2^k_skip, …}` via
//! `fwd_NTT_Λ`.
//!
//! The oracles keep the constant F₈ factor `C_s = φ₈(0x1C)` in the eq-on-S weights;
//! [`super::univariate_skip_optimized`] drops it and the caller restores it before the message
//! goes on the wire.

#[cfg(test)]
use pcs::ntt::AdditiveNttGf8;
use pcs::ntt::InvNttTableByteSingleGf8;
use primitives::field::{F8, F192, phi8_192 as phi8};

// ---------------------------------------------------------------------------
// Live helpers.
// ---------------------------------------------------------------------------

pub use primitives::multilinear::eq_table as build_eq;

/// Pack a bit vector LSB-first into bytes.
pub fn pack_bits(bits: &[bool]) -> Vec<u8> {
    let n_bytes = bits.len().div_ceil(8);
    // Each output byte depends on 8 contiguous input bits — disjoint, so
    // process bytes in parallel.
    parallel::map_collect(n_bytes, |byte_idx| {
        let mut byte = 0u8;
        let base = byte_idx * 8;
        for j in 0..8 {
            let bit_idx = base + j;
            if bit_idx < bits.len() && bits[bit_idx] {
                byte |= 1u8 << j;
            }
        }
        byte
    })
}

/// Eq table split into a lo half (large, L2-resident) and a hi half (small,
/// kept in registers across the inner loop).
#[derive(Clone, Debug)]
pub struct SplitEq {
    pub n_lo: usize,
    pub n_hi: usize,
    pub lo: Vec<F192>,
    pub hi: Vec<F192>,
}

impl SplitEq {
    /// C++-default cap on the hi half size — keeps outer F192 muls cheap.
    pub const MAX_N_HI: usize = 7;

    pub fn new(r: &[F192]) -> Self {
        let n = r.len();
        let n_hi = n.min(Self::MAX_N_HI);
        let n_lo = n - n_hi;
        Self {
            n_lo,
            n_hi,
            lo: build_eq(&r[..n_lo]),
            hi: build_eq(&r[n_lo..]),
        }
    }
}

/// Extend a length-`ell` F192 vector from the input domain S to the extension
/// domain Λ using bit-plane decomposition: for each of the 192 bit positions
/// of F192, run the bit-input NTT (`inv_NTT_S` then `fwd_NTT_Λ` via the
/// precomputed table) on that bit-plane, scale by γ^b, and accumulate.
///
/// Ports `ntt_extend_vec` (scalar form). The NTT is F_2-linear and
/// φ_8 commutes with that linearity, which is what makes the bit-by-bit
/// decomposition equal to the direct F_8-valued NTT extension.
pub fn ntt_extend_vec(in_s: &[F192], inv_table: &InvNttTableByteSingleGf8) -> Vec<F192> {
    let ell = inv_table.ell;
    assert_eq!(in_s.len(), ell);
    assert_eq!(ell, 1usize << inv_table.k);

    let mut out = vec![F192::ZERO; ell];
    let n_chunks = inv_table.n_chunks;

    let mut input_bits = vec![0u8; n_chunks];
    let mut out_bytes = vec![F8::ZERO; ell];

    for b in 0..192 {
        // Pack bit b of each in_s[z] into z-indexed LSB-first byte form.
        input_bits.iter_mut().for_each(|x| *x = 0);
        for z in 0..ell {
            let bit = match b / 64 {
                0 => (in_s[z].c0 >> b) & 1,
                1 => (in_s[z].c1 >> (b - 64)) & 1,
                2 => (in_s[z].c2 >> (b - 128)) & 1,
                _ => unreachable!(),
            };
            if bit != 0 {
                input_bits[z / 8] |= 1u8 << (z % 8);
            }
        }

        // Bit-input NTT.
        inv_table.apply(&input_bits, &mut out_bytes);

        let basis = match b / 64 {
            0 => F192::new(1u64 << b, 0, 0),
            1 => F192::new(0, 1u64 << (b - 64), 0),
            2 => F192::new(0, 0, 1u64 << (b - 128)),
            _ => unreachable!(),
        };
        for lambda in 0..ell {
            out[lambda] += basis * phi8(out_bytes[lambda]);
        }
    }

    out
}

// ===========================================================================
// Test-only oracles. Everything below is `#[cfg(test)]`: direct translations of
// the protocol formula, kept only so the optimized kernels have something
// obviously correct to be diffed against.
// ===========================================================================

/// Compute the round-1 prover message naively (no shift-reduce, no fused
/// inner, no deferred reduction — direct algorithmic translation of the
/// protocol formula).
///
/// Returns `(p_ab, p_c)`, each a length-`2^k_skip` F192 vector of evaluations
/// on Λ.
///
/// Preconditions:
/// - `a.len() == b.len() == c.len() == 2^m`
/// - `r_rest.len() == m - k_skip`
/// - `k_skip <= m`
///
/// Index convention: for index `i ∈ 0..2^m`, the low `k_skip` bits address
/// the *skip* variables (`y_skip ∈ S`), the high `m - k_skip` bits address
/// the *rest* variables (`y_rest`).
#[cfg(test)]
pub fn round1_naive(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
) -> (Vec<F192>, Vec<F192>) {
    assert!(k_skip <= m, "k_skip must be ≤ m");
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert_eq!(c.len(), 1usize << m);
    assert_eq!(r_rest.len(), m - k_skip);

    let ell = 1usize << k_skip;
    let n_chunks_x = 1usize << (m - k_skip);

    // NTT for evaluating-on-Λ via inv-on-S then fwd-on-Λ.
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(ell as u8));

    let eq_full = build_eq(r_rest);

    let mut p_ab = vec![F192::ZERO; ell];
    let mut p_c = vec![F192::ZERO; ell];

    let mut a_col = vec![F8::ZERO; ell];
    let mut b_col = vec![F8::ZERO; ell];
    let mut c_col = vec![F8::ZERO; ell];

    for x_rest in 0..n_chunks_x {
        let base = x_rest * ell;
        for s in 0..ell {
            a_col[s] = F8(a[base + s] as u8);
            b_col[s] = F8(b[base + s] as u8);
            c_col[s] = F8(c[base + s] as u8);
        }
        // Extend the row polynomial from S to Λ.
        ntt_s.inverse(&mut a_col);
        ntt_l.forward(&mut a_col);
        ntt_s.inverse(&mut b_col);
        ntt_l.forward(&mut b_col);
        ntt_s.inverse(&mut c_col);
        ntt_l.forward(&mut c_col);

        let eq_x = eq_full[x_rest];
        for i in 0..ell {
            let ab = a_col[i] * b_col[i];
            p_ab[i] += eq_x * phi8(ab);
            p_c[i] += eq_x * phi8(c_col[i]);
        }
    }

    (p_ab, p_c)
}

/// Round-1 prover message (extract_c form, scalar, algorithmically optimized
/// but without the geometric-eq shift_reduce trick).
///
/// Same output as [`round1_naive`], but it uses `InvNttTableByteSingleGf8::apply`
/// (one L1 lookup pass) instead of two F8 NTT calls per row, splits the eq table
/// into lo/hi halves, and accumulates C on S so it NTT-extends to Λ once at the
/// end rather than per row.
///
/// Output: `(res_AB, res_C_lifted)`, each length `2^k_skip` F192 vector.
/// Both are evaluations on Λ. Output equals `round1_naive(..)` byte-for-byte
/// (no C_s factor — see module-level comment).
#[cfg(test)]
pub fn round1_extract_c(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F192>, Vec<F192>) {
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert_eq!(c.len(), 1usize << m);
    let a_packed = pack_bits(a);
    let b_packed = pack_bits(b);
    let c_packed = pack_bits(c);
    round1_extract_c_packed(&a_packed, &b_packed, &c_packed, m, k_skip, r_rest, inv_table)
}

/// Packed-input variant of [`round1_extract_c`]. Skips the bool→byte packing —
/// caller passes pre-packed bytes (LSB-first within each byte, as produced
/// by [`pack_bits`]). Use this when the caller already has packed witnesses
/// or wants to factor packing out of timed work.
#[cfg(test)]
pub fn round1_extract_c_packed(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F192>, Vec<F192>) {
    let (res_ab, res_c_lifted, _) =
        round1_extract_c_packed_with_s_hat_v(a_packed, b_packed, c_packed, m, k_skip, r_rest, inv_table);
    (res_ab, res_c_lifted)
}

/// Same as [`round1_extract_c_packed`] but **also returns `s_hat_v_c`** — the
/// 128-entry vector ring-switch would otherwise produce via `fold_1b_rows` for
/// the c-claim's PCS opening at point `r_rest`.
///
/// # Trick
///
/// Round 1's c-side already does the witness scan needed for `s_hat_v_c`; it
/// just collapses one too many dims. The first friendly constant `r_rest[0]`
/// (= φ_8(α)) applies to bit `i_inner[k_skip]` of the witness, which is also
/// bit 0 of `x_rest` in this function's loop nest. So splitting the `partial_c`
/// accumulator into **two banks**, one per value of that bit, gives us the
/// per-`b_7`-slice partial folds that `s_hat_v_c` indexes by.
///
/// Specifically, for `b_7 ∈ {0, 1}`:
/// ```text
/// res_c_s_{b_7}[lane] = Σ_{x_rest with bit-0 = b_7}
///                        eq(r_rest, x_rest) · c_bit(lane, x_rest)
/// ```
/// The wire output `res_c_s` is recovered by `res_c_s_0 + res_c_s_1` (the eq
/// factor for `r_rest[0]` is already absorbed in each bank), then NTT-extended
/// as before to produce `res_c_lifted`.
///
/// To get the canonical `s_hat_v_c` (eq weight WITHOUT the `r_rest[0]` factor),
/// divide bank 0 by `1 + r_rest[0]` (= `eq(r_rest[0], 0)`) and bank 1 by
/// `r_rest[0]` (= `eq(r_rest[0], 1)`):
/// ```text
/// s_hat_v_c[(lane, b_7)] = res_c_s_{b_7}[lane] / eq(r_rest[0], b_7)
/// ```
/// Output layout (matches `fold_1b_rows`): `s_hat_v_c[lane | (b_7 << k_skip)]`
/// for `lane ∈ [0, 2^k_skip)`, `b_7 ∈ {0, 1}`. Length = `2 · 2^k_skip` =
/// `2^LOG_PACKING = 128` when `k_skip = 6`.
#[cfg(test)]
pub fn round1_extract_c_packed_with_s_hat_v(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F192>, Vec<F192>, Vec<F192>) {
    assert!(k_skip <= m);
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r_rest.len(), m - k_skip);
    assert_eq!(inv_table.k, k_skip);

    let ell = 1usize << k_skip;
    let n_chunks = ell / 8;

    let eq = SplitEq::new(r_rest);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;

    let mut res_ab = vec![F192::ZERO; ell];
    // Two C banks, one per value of bit 0 of `x_rest` = bit `k_skip` of the
    // flat witness index (= `b_7` in ring-switch's parlance).
    let mut res_c_s_0 = vec![F192::ZERO; ell];
    let mut res_c_s_1 = vec![F192::ZERO; ell];

    let mut partial_ab = vec![F192::ZERO; ell];
    let mut partial_c_0 = vec![F192::ZERO; ell];
    let mut partial_c_1 = vec![F192::ZERO; ell];

    let mut a_col = vec![F8::ZERO; ell];
    let mut b_col = vec![F8::ZERO; ell];

    for x_hi in 0..hi_size {
        partial_ab.iter_mut().for_each(|p| *p = F192::ZERO);
        partial_c_0.iter_mut().for_each(|p| *p = F192::ZERO);
        partial_c_1.iter_mut().for_each(|p| *p = F192::ZERO);

        for x_lo in 0..lo_size {
            let x_rest = (x_hi << eq.n_lo) | x_lo;
            let chunk_offset = x_rest * n_chunks;
            let b_7 = x_rest & 1;

            // A, B → Λ-domain via table lookup.
            inv_table.apply(&a_packed[chunk_offset..chunk_offset + n_chunks], &mut a_col);
            inv_table.apply(&b_packed[chunk_offset..chunk_offset + n_chunks], &mut b_col);

            let eq_lo = eq.lo[x_lo];

            // AB on Λ — unchanged.
            for lambda in 0..ell {
                let ab = a_col[lambda] * b_col[lambda];
                partial_ab[lambda] += eq_lo * phi8(ab);
            }

            // C on S — route into bank 0 or bank 1 based on b_7. The eq
            // factor `eq(r_rest[0], b_7)` is implicit in eq_lo because the
            // SplitEq builds the tensor for r_rest; we strip that
            // factor out at the end via division.
            let target = if b_7 == 0 { &mut partial_c_0 } else { &mut partial_c_1 };
            for s in 0..ell {
                let c_bit = (c_packed[chunk_offset + s / 8] >> (s % 8)) & 1;
                if c_bit != 0 {
                    target[s] += eq_lo;
                }
            }
        }

        let eq_hi = eq.hi[x_hi];
        for lambda in 0..ell {
            res_ab[lambda] += eq_hi * partial_ab[lambda];
            res_c_s_0[lambda] += eq_hi * partial_c_0[lambda];
            res_c_s_1[lambda] += eq_hi * partial_c_1[lambda];
        }
    }

    // Wire output: combined bank sum = original res_c_s. (The eq(r_rest[0], 0)
    // factor (= 1 + r_rest[0]) is baked into bank 0, eq(r_rest[0], 1) (= r_rest[0])
    // into bank 1. Summing reconstitutes the eq(r_rest, x_rest) sum.)
    let mut res_c_s = vec![F192::ZERO; ell];
    for s in 0..ell {
        res_c_s[s] = res_c_s_0[s] + res_c_s_1[s];
    }
    let res_c_lifted = ntt_extend_vec(&res_c_s, inv_table);

    // s_hat_v_c: strip the eq(r_rest[0], ·) factor from each bank by dividing
    // by 1 + r_rest[0] (bank 0) and r_rest[0] (bank 1). No NTT extension —
    // lanes are already boolean indices, which is what ring-switch consumes.
    let inv_zero = (F192::ONE + r_rest[0]).inv();
    let inv_one = r_rest[0].inv();
    let mut s_hat_v_c = vec![F192::ZERO; 2 * ell];
    for lane in 0..ell {
        s_hat_v_c[lane] = res_c_s_0[lane] * inv_zero;
        s_hat_v_c[ell + lane] = res_c_s_1[lane] * inv_one;
    }

    (res_ab, res_c_lifted, s_hat_v_c)
}

/// Round-1 polynomial values evaluated AT S.
///
/// Returns `(P^{AB} at S, P^C at S)` — i.e. evaluations of the same round-1
/// polynomial on the input domain S instead of the extension domain Λ.
/// Computed directly from the boolean witness, skipping the NTT extension.
///
/// For an honest prover (`a·b = c` everywhere on the hypercube),
/// `P^{AB}(λ) + P^C(λ) = 0` for every `λ ∈ S`.
#[cfg(test)]
pub fn round1_evals_on_s(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    m: usize,
    k_skip: usize,
    r_rest: &[F192],
) -> (Vec<F192>, Vec<F192>) {
    assert!(k_skip <= m);
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert_eq!(c.len(), 1usize << m);
    assert_eq!(r_rest.len(), m - k_skip);

    let ell = 1usize << k_skip;
    let n_chunks_x = 1usize << (m - k_skip);
    let eq_full = build_eq(r_rest);

    let mut p_ab = vec![F192::ZERO; ell];
    let mut p_c = vec![F192::ZERO; ell];

    for x_rest in 0..n_chunks_x {
        let base = x_rest * ell;
        let eq_x = eq_full[x_rest];
        for s in 0..ell {
            if a[base + s] && b[base + s] {
                p_ab[s] += eq_x;
            }
            if c[base + s] {
                p_c[s] += eq_x;
            }
        }
    }

    (p_ab, p_c)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    #[test]
    fn build_eq_basic() {
        // Empty r → table = [1].
        assert_eq!(build_eq(&[]), vec![F192::ONE]);
        // Single r = [r0] → table = [(1+r0), r0].
        let r0 = F192::new(0xCAFEBABE, 0x12345678, 0x87654321);
        let t = build_eq(&[r0]);
        assert_eq!(t.len(), 2);
        assert_eq!(t[0], F192::ONE + r0);
        assert_eq!(t[1], r0);
        // Sum of all eq values is 1 (a defining property of the multilinear eq).
        let n = 5;
        let mut rng = Rng::new(99);
        let r = rng.ext_vec(n);
        let t = build_eq(&r);
        let sum: F192 = t.iter().copied().fold(F192::ZERO, |a, b| a + b);
        assert_eq!(sum, F192::ONE, "Σ_x eq(r, x) should be 1");
    }

    #[test]
    fn round1_all_zero_witness_gives_zero_message() {
        let m = 7;
        let k_skip = 3;
        let mut rng = Rng::new(2);
        let r = rng.ext_vec(m - k_skip);
        let zeros = vec![false; 1 << m];
        let (p_ab, p_c) = round1_naive(&zeros, &zeros, &zeros, m, k_skip, &r);
        assert!(p_ab.iter().all(|v| v.is_zero()));
        assert!(p_c.iter().all(|v| v.is_zero()));
    }

    #[test]
    fn round1_p_c_is_xor_linear_in_c() {
        // p_c(c1 XOR c2) = p_c(c1) + p_c(c2), with a, b fixed.
        let m = 6;
        let k_skip = 3;
        let mut rng = Rng::new(4);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c1 = rng.bits(1 << m);
        let c2 = rng.bits(1 << m);
        let c_sum: Vec<bool> = c1.iter().zip(&c2).map(|(x, y)| x ^ y).collect();
        let r = rng.ext_vec(m - k_skip);

        let (ab1, pc1) = round1_naive(&a, &b, &c1, m, k_skip, &r);
        let (ab2, pc2) = round1_naive(&a, &b, &c2, m, k_skip, &r);
        let (ab_sum, pc_sum) = round1_naive(&a, &b, &c_sum, m, k_skip, &r);

        // P^AB only depends on (a, b), not c: should be unchanged.
        assert_eq!(ab1, ab_sum);
        assert_eq!(ab2, ab_sum);
        // P^C is XOR-linear in c.
        for i in 0..pc1.len() {
            assert_eq!(pc1[i] + pc2[i], pc_sum[i]);
        }
    }

    #[test]
    fn round1_at_s_zero_for_honest_witness() {
        // The strongest correctness check we can write without the optimized
        // version: for an honest witness with a · b = c on the hypercube,
        // the round-1 polynomial P^{AB}(λ) + P^C(λ) is zero at every λ ∈ S.
        // (At S the extension polynomial equals the original boolean values,
        // so P at S is just the eq-weighted sum of (a·b ⊕ c) = 0.)
        //
        // We use `round1_evals_on_s` as the test oracle since it computes P at S
        // directly without the NTT. The protocol's actual round-1 message
        // (`round1_naive`) lives at Λ; cross-checking S↔Λ via NTT
        // interpolation is left for the optimized-vs-naive comparison.
        let m = 8;
        let k_skip = 3;
        let mut rng = Rng::new(5);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        // Honest c: c = a AND b for every i.
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let r = rng.ext_vec(m - k_skip);

        let (p_ab_s, p_c_s) = round1_evals_on_s(&a, &b, &c, m, k_skip, &r);
        for s in 0..p_ab_s.len() {
            assert_eq!(
                p_ab_s[s] + p_c_s[s],
                F192::ZERO,
                "P at S should be 0 for honest witness, but failed at s={s}"
            );
        }
    }

    #[test]
    fn round1_at_s_nonzero_for_random_witness() {
        // Sanity: for an arbitrary (likely-not-honest) witness, P at S is
        // generally nonzero. This guards against round1_evals_on_s returning
        // zero trivially.
        let m = 8;
        let k_skip = 3;
        let mut rng = Rng::new(6);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c = rng.bits(1 << m);
        let r = rng.ext_vec(m - k_skip);

        let (p_ab_s, p_c_s) = round1_evals_on_s(&a, &b, &c, m, k_skip, &r);
        let combined: Vec<F192> = p_ab_s.iter().zip(&p_c_s).map(|(x, y)| *x + *y).collect();
        let nonzero = combined.iter().any(|v| !v.is_zero());
        assert!(nonzero, "P at S should be nonzero for a random witness");
    }

    fn make_inv_table(k_skip: usize) -> InvNttTableByteSingleGf8 {
        let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
        let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
        InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l)
    }

    /// The `s_hat_v_c` output is byte-identical to what ring-switch's
    /// `fold_1b_rows` would produce on the C-witness against the canonical
    /// equality tail `r_rest`. Its two banks leave `r_rest[0]` unfolded, and
    /// combining them with that coordinate recovers the ordinary packed fold.
    #[test]
    fn extract_c_with_s_hat_v_matches_fold_1b_rows() {
        use pcs::pack::pack_witness;
        use pcs::ring_switch::fold_1b_rows;
        // K_SKIP = 6 is the production setup (LOG_PACKING = 7, so 2 · 2^K_SKIP
        // = 128 matches s_hat_v's length). The kernel needs m >= K_SKIP + 1 =
        // 7 for pack_witness, plus the SplitEq's n_lo + n_hi machinery
        // wants m - k_skip >= some floor — tested at m=8..11.
        const K_SKIP: usize = 6;
        for &m in &[8usize, 9, 10, 11] {
            let mut rng = Rng::new(0xC0FFEE_u64.wrapping_add(m as u64));
            let z_bits = rng.bits(1 << m);
            let a = pack_bits(&rng.bits(1 << m));
            let b = pack_bits(&rng.bits(1 << m));
            let c = pack_bits(&z_bits);
            let r = rng.ext_vec(m - K_SKIP);
            let table = make_inv_table(K_SKIP);

            let (_, _, s_hat_v_c) = round1_extract_c_packed_with_s_hat_v(&a, &b, &c, m, K_SKIP, &r, &table);

            // Reference: fold_1b_rows on the packed C-witness against the
            // complete equality tail.
            let packed_c = pack_witness(&z_bits, m);
            let suffix_tensor = build_eq(&r);
            let want = fold_1b_rows(&packed_c, &suffix_tensor);

            let c = r[0];
            let folded: Vec<_> = (0..pcs::pack::PACKING_WIDTH)
                .map(|i| (F192::ONE + c) * s_hat_v_c[i] + c * s_hat_v_c[i + pcs::pack::PACKING_WIDTH])
                .collect();

            assert_eq!(folded.len(), want.len(), "length mismatch at m={m}");
            assert_eq!(folded, want, "s_hat_v_c mismatch at m={m}");
        }
    }

    /// The strongest correctness check: extract_c must produce **identical**
    /// output to the naive round-1 message — same eq weights, same protocol,
    /// just a faster algorithm.
    #[test]
    fn extract_c_matches_naive() {
        for &(m, k_skip) in &[(4, 3), (5, 3), (6, 3), (7, 4), (8, 3), (9, 6)] {
            let mut rng = Rng::new(100 + m as u64 * 10 + k_skip as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c = rng.bits(1 << m);
            let r = rng.ext_vec(m - k_skip);
            let table = make_inv_table(k_skip);

            let (naive_ab, naive_c) = round1_naive(&a, &b, &c, m, k_skip, &r);
            let (opt_ab, opt_c) = round1_extract_c(&a, &b, &c, m, k_skip, &r, &table);

            assert_eq!(naive_ab, opt_ab, "AB mismatch at m={m}, k_skip={k_skip}");
            assert_eq!(naive_c, opt_c, "C mismatch at m={m}, k_skip={k_skip}");
        }
    }

    #[test]
    fn split_eq_basic() {
        // Building the lo and hi tables separately should produce the same
        // values as the full eq table when indexed appropriately.
        let mut rng = Rng::new(300);
        let n = 6;
        let r = rng.ext_vec(n);
        let full = build_eq(&r);
        let eq = SplitEq::new(&r);
        assert_eq!(eq.n_lo + eq.n_hi, n);
        for x in 0..(1 << n) {
            let x_lo = x & ((1 << eq.n_lo) - 1);
            let x_hi = x >> eq.n_lo;
            assert_eq!(eq.lo[x_lo] * eq.hi[x_hi], full[x]);
        }
    }

    #[test]
    fn round1_message_nonzero_for_random_witness() {
        // Sanity: round1_naive on random inputs should give nonzero output too.
        // (Catches accidentally zeroing the accumulators.)
        let m = 8;
        let k_skip = 3;
        let mut rng = Rng::new(7);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c = rng.bits(1 << m);
        let r = rng.ext_vec(m - k_skip);

        let (p_ab, p_c) = round1_naive(&a, &b, &c, m, k_skip, &r);
        assert!(p_ab.iter().any(|v| !v.is_zero()));
        assert!(p_c.iter().any(|v| !v.is_zero()));
    }
}
