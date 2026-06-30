// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Round-1 prover message (univariate skip).
//!
//! The round-1 message is `(P^{AB}, P^C)`, each a length-`2^k_skip` vector
//! of F128 values. They are evaluations on the NTT domain `Λ` of the
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
//! Unoptimized reference: returns the AB and C polynomials separately (the
//! extract_c variant). The optimized variant in
//! [`super::univariate_skip_optimized`] drops a constant F₈ factor
//! `C_s = φ₈(0x1C)` from the eq-on-S weights; this one keeps it.

use crate::field::{F8, F128, mul_by_x, phi8};
use crate::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build the multilinear-eq evaluation table over `r`:
/// `table[x] = ∏_i ((1 + r_i) · (1 ⊕ bit_i(x)) + r_i · bit_i(x))` for `x ∈ {0,1}^n`,
/// where `n = r.len()`. Standard in-place power-of-two doubling.
pub fn build_eq(r: &[F128]) -> Vec<F128> {
    let n = r.len();
    // Uninit alloc — same invariant as `build_eq_parallel` in ring_switch:
    // every slot in t[0..2^n] is written exactly once before any read.
    let mut t = crate::alloc_uninit_f128_vec(1usize << n);
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

// ---------------------------------------------------------------------------
// Naive round-1 prover message (extract_c form)
// ---------------------------------------------------------------------------

/// Compute the round-1 prover message naively (no shift-reduce, no fused
/// inner, no deferred reduction — direct algorithmic translation of the
/// protocol formula).
///
/// Returns `(p_ab, p_c)`, each a length-`2^k_skip` F128 vector of evaluations
/// on Λ.
///
/// Preconditions:
/// - `a.len() == b.len() == c.len() == 2^m`
/// - `r.len() == m`
/// - `k_skip <= m`
///
/// Index convention: for index `i ∈ 0..2^m`, the low `k_skip` bits address
/// the *skip* variables (`y_skip ∈ S`), the high `m - k_skip` bits address
/// the *rest* variables (`y_rest`).
pub fn round1_naive(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    m: usize,
    k_skip: usize,
    r: &[F128],
) -> (Vec<F128>, Vec<F128>) {
    assert!(k_skip <= m, "k_skip must be ≤ m");
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert_eq!(c.len(), 1usize << m);
    assert_eq!(r.len(), m);

    let ell = 1usize << k_skip;
    let n_chunks_x = 1usize << (m - k_skip);

    // NTT for evaluating-on-Λ via inv-on-S then fwd-on-Λ.
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(ell as u8));

    // eq table over the rest-of-r challenges; only r[k_skip..] is used here
    // (the skip portion r[0..k_skip] is consumed by the verifier later).
    let eq_full = build_eq(&r[k_skip..]);

    let mut p_ab = vec![F128::ZERO; ell];
    let mut p_c = vec![F128::ZERO; ell];

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

// ---------------------------------------------------------------------------
// Algorithmically-structured optimized round-1 (extract_c form, scalar)
// ---------------------------------------------------------------------------
//
// Same output as `round1_naive`, but:
//   * uses `InvNttTableByteSingleGf8::apply` (one L1 lookup pass) instead of
//     two F8 NTT calls per row;
//   * splits the eq table into lo/hi halves (cache-friendly outer/inner);
//   * processes C in extract_c form — accumulates on S, NTT-extends to Λ once
//     at the end, instead of NTT-extending per row.
//
// The geometric-eq shift_reduce + convert-table tricks (which give the C++ its
// final ~5× win) are a follow-up; they change the output by the C_s factor,
// so doing them on a separately-validated scaffold is cleaner.

/// Pack a bit vector LSB-first into bytes.
pub fn pack_bits(bits: &[bool]) -> Vec<u8> {
    use rayon::prelude::*;
    let n_bytes = bits.len().div_ceil(8);
    let mut out = vec![0u8; n_bytes];
    // Each output byte depends on 8 contiguous input bits — disjoint, so
    // process bytes in parallel.
    out.par_chunks_mut(1)
        .enumerate()
        .for_each(|(byte_idx, slot)| {
            let mut byte = 0u8;
            let base = byte_idx * 8;
            for j in 0..8 {
                let bit_idx = base + j;
                if bit_idx < bits.len() && bits[bit_idx] {
                    byte |= 1u8 << j;
                }
            }
            slot[0] = byte;
        });
    out
}

/// Eq table split into a lo half (large, L2-resident) and a hi half (small,
/// kept in registers across the inner loop).
#[derive(Clone, Debug)]
pub struct SplitEqGhash {
    pub n_lo: usize,
    pub n_hi: usize,
    pub lo: Vec<F128>,
    pub hi: Vec<F128>,
}

impl SplitEqGhash {
    /// C++-default cap on the hi half size — keeps outer F128 muls cheap.
    pub const MAX_N_HI: usize = 7;

    pub fn new(r: &[F128]) -> Self {
        let n = r.len();
        let n_hi = n.min(Self::MAX_N_HI);
        Self::with_n_hi(r, n_hi)
    }

    pub fn with_n_hi(r: &[F128], n_hi: usize) -> Self {
        let n = r.len();
        let n_hi = n_hi.min(n);
        let n_lo = n - n_hi;
        Self {
            n_lo,
            n_hi,
            lo: build_eq(&r[..n_lo]),
            hi: build_eq(&r[n_lo..]),
        }
    }
}

/// Extend a length-`ell` F128 vector from the input domain S to the extension
/// domain Λ using bit-plane decomposition: for each of the 128 bit positions
/// of F128, run the bit-input NTT (`inv_NTT_S` then `fwd_NTT_Λ` via the
/// precomputed table) on that bit-plane, scale by γ^b, and accumulate.
///
/// Ports `ntt_extend_f128_vec_ghash` (scalar form). The NTT is F_2-linear and
/// φ_8 commutes with that linearity, which is what makes the bit-by-bit
/// decomposition equal to the direct F_8-valued NTT extension.
pub fn ntt_extend_f128_vec_ghash(in_s: &[F128], inv_table: &InvNttTableByteSingleGf8) -> Vec<F128> {
    let ell = inv_table.ell;
    assert_eq!(in_s.len(), ell);
    assert_eq!(ell, 1usize << inv_table.k);

    let mut out = vec![F128::ZERO; ell];
    let n_chunks = inv_table.n_chunks;

    // γ^b for b ∈ [0, 128).
    let mut gamma_pow = [F128::ZERO; 128];
    gamma_pow[0] = F128::ONE;
    for b in 1..128 {
        gamma_pow[b] = mul_by_x(gamma_pow[b - 1]);
    }

    let mut input_bits = vec![0u8; n_chunks];
    let mut out_bytes = vec![F8::ZERO; ell];

    for b in 0..128 {
        // Pack bit b of each in_s[z] into z-indexed LSB-first byte form.
        input_bits.iter_mut().for_each(|x| *x = 0);
        for z in 0..ell {
            let bit = if b < 64 {
                (in_s[z].lo >> b) & 1
            } else {
                (in_s[z].hi >> (b - 64)) & 1
            };
            if bit != 0 {
                input_bits[z / 8] |= 1u8 << (z % 8);
            }
        }

        // Bit-input NTT.
        inv_table.apply(&input_bits, &mut out_bytes);

        let g_b = gamma_pow[b];
        for lambda in 0..ell {
            out[lambda] += g_b * phi8(out_bytes[lambda]);
        }
    }

    out
}

/// Round-1 prover message (extract_c form, scalar, algorithmically optimized
/// but without the geometric-eq shift_reduce trick).
///
/// Output: `(res_AB, res_C_lifted)`, each length `2^k_skip` F128 vector.
/// Both are evaluations on Λ. Output equals `round1_naive(..)` byte-for-byte
/// (no C_s factor — see module-level comment).
pub fn round1_extract_c(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    m: usize,
    k_skip: usize,
    r: &[F128],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F128>, Vec<F128>) {
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert_eq!(c.len(), 1usize << m);
    let a_packed = pack_bits(a);
    let b_packed = pack_bits(b);
    let c_packed = pack_bits(c);
    round1_extract_c_packed(&a_packed, &b_packed, &c_packed, m, k_skip, r, inv_table)
}

/// Packed-input variant of [`round1_extract_c`]. Skips the bool→byte packing —
/// caller passes pre-packed bytes (LSB-first within each byte, as produced
/// by [`pack_bits`]). Use this when the caller already has packed witnesses
/// or wants to factor packing out of timed work.
pub fn round1_extract_c_packed(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r: &[F128],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F128>, Vec<F128>) {
    assert!(k_skip <= m);
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r.len(), m);
    assert_eq!(inv_table.k, k_skip);

    let ell = 1usize << k_skip;
    let n_chunks = ell / 8;

    let eq = SplitEqGhash::new(&r[k_skip..]);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;

    let mut res_ab = vec![F128::ZERO; ell];
    // C accumulator stays in S-domain; we NTT-extend once at the end.
    let mut res_c_s = vec![F128::ZERO; ell];

    let mut partial_ab = vec![F128::ZERO; ell];
    let mut partial_c = vec![F128::ZERO; ell];

    let mut a_col = vec![F8::ZERO; ell];
    let mut b_col = vec![F8::ZERO; ell];

    for x_hi in 0..hi_size {
        partial_ab.iter_mut().for_each(|p| *p = F128::ZERO);
        partial_c.iter_mut().for_each(|p| *p = F128::ZERO);

        for x_lo in 0..lo_size {
            let x_rest = (x_hi << eq.n_lo) | x_lo;
            let chunk_offset = x_rest * n_chunks;

            // A, B → Λ-domain via table lookup.
            inv_table.apply(&a_packed[chunk_offset..chunk_offset + n_chunks], &mut a_col);
            inv_table.apply(&b_packed[chunk_offset..chunk_offset + n_chunks], &mut b_col);

            let eq_lo = eq.lo[x_lo];

            // AB on Λ.
            for lambda in 0..ell {
                let ab = a_col[lambda] * b_col[lambda];
                partial_ab[lambda] += eq_lo * phi8(ab);
            }

            // C on S — read original bits, no NTT yet.
            for s in 0..ell {
                let c_bit = (c_packed[chunk_offset + s / 8] >> (s % 8)) & 1;
                if c_bit != 0 {
                    partial_c[s] += eq_lo;
                }
            }
        }

        let eq_hi = eq.hi[x_hi];
        for lambda in 0..ell {
            res_ab[lambda] += eq_hi * partial_ab[lambda];
            res_c_s[lambda] += eq_hi * partial_c[lambda];
        }
    }

    // Lift C from S to Λ via bit-plane NTT extension.
    let res_c_lifted = ntt_extend_f128_vec_ghash(&res_c_s, inv_table);

    (res_ab, res_c_lifted)
}

/// Same as [`round1_extract_c_packed`] but **also returns `s_hat_v_c`** — the
/// 128-entry vector ring-switch would otherwise produce via `fold_1b_rows` for
/// the c-claim's PCS opening at point `r[k_skip..]`.
///
/// # Trick
///
/// Round 1's c-side already does the witness scan needed for `s_hat_v_c`; it
/// just collapses one too many dims. The first friendly constant `r[k_skip]`
/// (= φ_8(α)) applies to bit `i_inner[k_skip]` of the witness, which is also
/// bit 0 of `x_rest` in this function's loop nest. So splitting the `partial_c`
/// accumulator into **two banks**, one per value of that bit, gives us the
/// per-`b_7`-slice partial folds that `s_hat_v_c` indexes by.
///
/// Specifically, for `b_7 ∈ {0, 1}`:
/// ```text
/// res_c_s_{b_7}[lane] = Σ_{x_rest with bit-0 = b_7}
///                        eq(r[k_skip..m], x_rest) · c_bit(lane, x_rest)
/// ```
/// The wire output `res_c_s` is recovered by `res_c_s_0 + res_c_s_1` (the eq
/// factor for `r[k_skip]` is already absorbed in each bank), then NTT-extended
/// as before to produce `res_c_lifted`.
///
/// To get the canonical `s_hat_v_c` (eq weight WITHOUT the `r[k_skip]` factor),
/// divide bank 0 by `1 + r[k_skip]` (= `eq(r[k_skip], 0)`) and bank 1 by
/// `r[k_skip]` (= `eq(r[k_skip], 1)`):
/// ```text
/// s_hat_v_c[(lane, b_7)] = res_c_s_{b_7}[lane] / eq(r[k_skip], b_7)
/// ```
/// Output layout (matches `fold_1b_rows`): `s_hat_v_c[lane | (b_7 << k_skip)]`
/// for `lane ∈ [0, 2^k_skip)`, `b_7 ∈ {0, 1}`. Length = `2 · 2^k_skip` =
/// `2^LOG_PACKING = 128` when `k_skip = 6`.
pub fn round1_extract_c_packed_with_s_hat_v(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r: &[F128],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F128>, Vec<F128>, Vec<F128>) {
    assert!(k_skip <= m);
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r.len(), m);
    assert_eq!(inv_table.k, k_skip);

    let ell = 1usize << k_skip;
    let n_chunks = ell / 8;

    let eq = SplitEqGhash::new(&r[k_skip..]);
    let lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;

    let mut res_ab = vec![F128::ZERO; ell];
    // Two C banks, one per value of bit 0 of `x_rest` = bit `k_skip` of the
    // flat witness index (= `b_7` in ring-switch's parlance).
    let mut res_c_s_0 = vec![F128::ZERO; ell];
    let mut res_c_s_1 = vec![F128::ZERO; ell];

    let mut partial_ab = vec![F128::ZERO; ell];
    let mut partial_c_0 = vec![F128::ZERO; ell];
    let mut partial_c_1 = vec![F128::ZERO; ell];

    let mut a_col = vec![F8::ZERO; ell];
    let mut b_col = vec![F8::ZERO; ell];

    for x_hi in 0..hi_size {
        partial_ab.iter_mut().for_each(|p| *p = F128::ZERO);
        partial_c_0.iter_mut().for_each(|p| *p = F128::ZERO);
        partial_c_1.iter_mut().for_each(|p| *p = F128::ZERO);

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
            // factor `eq(r[k_skip], b_7)` is implicit in eq_lo because the
            // SplitEqGhash builds the tensor for r[k_skip..]; we strip that
            // factor out at the end via division.
            let target = if b_7 == 0 {
                &mut partial_c_0
            } else {
                &mut partial_c_1
            };
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

    // Wire output: combined bank sum = original res_c_s. (The eq(r[k_skip], 0)
    // factor (= 1 + r[k_skip]) is baked into bank 0, eq(r[k_skip], 1) (= r[k_skip])
    // into bank 1. Summing reconstitutes the eq(r[k_skip..m], x_rest) sum.)
    let mut res_c_s = vec![F128::ZERO; ell];
    for s in 0..ell {
        res_c_s[s] = res_c_s_0[s] + res_c_s_1[s];
    }
    let res_c_lifted = ntt_extend_f128_vec_ghash(&res_c_s, inv_table);

    // s_hat_v_c: strip the eq(r[k_skip], ·) factor from each bank by dividing
    // by 1 + r[k_skip] (bank 0) and r[k_skip] (bank 1). No NTT extension —
    // lanes are already boolean indices, which is what ring-switch consumes.
    let inv_zero = (F128::ONE + r[k_skip]).inv();
    let inv_one = r[k_skip].inv();
    let mut s_hat_v_c = vec![F128::ZERO; 2 * ell];
    for lane in 0..ell {
        s_hat_v_c[lane] = res_c_s_0[lane] * inv_zero;
        s_hat_v_c[ell + lane] = res_c_s_1[lane] * inv_one;
    }

    (res_ab, res_c_lifted, s_hat_v_c)
}

// ---------------------------------------------------------------------------
// Test oracle: round-1 polynomial values evaluated AT S
// ---------------------------------------------------------------------------

/// **Test oracle, not part of the protocol.**
///
/// Returns `(P^{AB} at S, P^C at S)` — i.e. evaluations of the same round-1
/// polynomial on the input domain S instead of the extension domain Λ.
/// Computed directly from the boolean witness, skipping the NTT extension.
///
/// For an honest prover (`a·b = c` everywhere on the hypercube),
/// `P^{AB}(λ) + P^C(λ) = 0` for every `λ ∈ S`.
pub fn round1_evals_on_s(
    a: &[bool],
    b: &[bool],
    c: &[bool],
    m: usize,
    k_skip: usize,
    r: &[F128],
) -> (Vec<F128>, Vec<F128>) {
    assert!(k_skip <= m);
    assert_eq!(a.len(), 1usize << m);
    assert_eq!(b.len(), 1usize << m);
    assert_eq!(c.len(), 1usize << m);
    assert_eq!(r.len(), m);

    let ell = 1usize << k_skip;
    let n_chunks_x = 1usize << (m - k_skip);
    let eq_full = build_eq(&r[k_skip..]);

    let mut p_ab = vec![F128::ZERO; ell];
    let mut p_c = vec![F128::ZERO; ell];

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
