// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Round-1 prover message — fully optimized (shift_reduce + extract_c, scalar).
//!
//! Scalar Rust implementation (no NEON). Three layered optimizations on top of
//! the [`super::round1_extract_c`] scaffold:
//!
//! 1. **Geometric small-eq + shift_reduce inner** (3 inner-most rest-dims).
//!    Protocol fixes the three small challenges to
//!    `r[k_skip..k_skip+3] = φ_8([0xF7, 0x53, 0xB5])`, which makes
//!    `eq_small[K] = C_s · α^K` (geometric in α, the AES root in GHASH).
//!    The shift_reduce trick computes
//!    `Σ_K eq_small[K] · φ_8(y_K)  =  C_s · φ_8(reduce(Σ_K y_K << K))`,
//!    replacing 8 F128 mults per lane with 8 u16 XOR-shifts + one F_8
//!    reduction.
//!
//! 2. **Geometric medium-eq + convert table** (4 next rest-dims).
//!    Protocol fixes the four medium challenges to
//!    `β_i = γ^{2^{i-1}} / (1 + γ^{2^{i-1}})`, which makes
//!    `eq_med[b] = γ^b / D` for `D = ∏(1+γ^{2^{i-1}})`.
//!    Precomputed table `convert[b][v] = γ^b · φ_8(v)` (64 KB) reduces the
//!    per-lane medium-eq sum from 16 F128 mults to 16 lookups + 16 XORs.
//!
//! 3. **D⁻¹ absorbed into eq_lo.**
//!    Pre-scale `eq_lo[i] ← eq_lo[i] · D⁻¹` once before the loop; this cancels
//!    the `1/D` from the medium-eq factorization, leaving only the `C_s`
//!    factor in the relative output scaling.
//!
//! Net output relationship vs the naive / structural versions:
//!   `C_s · (res_AB[i] + res_C_lifted[i])  ==  naive_p_ab[i] + naive_p_c[i]`
//! with `C_s = φ_8(0x1C)`.
//!
//! This variant is hardcoded for `k_skip = 6` (ell=64, n_chunks=8, N_INNER=7).

use std::sync::OnceLock;

use crate::field::gf2_8::gf8_reduce;
use crate::field::{F8, F128, PHI_8_TABLE, mul_by_x, phi8};
use crate::ntt::InvNttTableByteSingleGf8;

use super::PaddingSpec;
use super::univariate_skip::{SplitEqGhash, ntt_extend_f128_vec_ghash, pack_bits};

// ---------------------------------------------------------------------------
// Protocol constants — fixed by the optimization design.
// ---------------------------------------------------------------------------

/// Number of variables folded in round 1 for the shift_reduce variant.
pub const K_SKIP: usize = 6;
const ELL: usize = 64;
const N_CHUNKS: usize = 8;
/// Total inner-most dims absorbed by the optimization: 3 small + 4 medium.
const N_INNER: usize = 7;
const N_MEDIUM: usize = 4;

/// The three small-eq challenges (as F_8 values, then embedded via φ_8).
/// Choosing these specific values is what makes `eq_small[K] = C_s · α^K`.
///
/// **Soundness dependency.** These three constants — together with the
/// four medium constants returned by [`medium_challenges_ghash`] — must be
/// **F₂-linearly independent** in F₁₂₈. Zerocheck soundness relies on this
/// (a witness aligned with the friendly subspace would otherwise let the
/// prover cancel the URM message), and so does Ligerito's L0 list-collapse
/// argument (the SZ bound `(m−7)/|F|` for MLE collisions at `r` requires
/// the seven friendly coords to span a 7-dim F₂-subspace). Asserted by
/// `tests::friendly_challenges_f2_independent`.
pub const SMALL_CHAL_F8: [u8; 3] = [0xF7, 0x53, 0xB5];

/// `C_s` as an F_8 value. Verified empirically by the C++ project.
pub const C_S_F8: u8 = 0x1C;

/// The constant `C_s = φ_8(0x1C) ∈ F_{2^128}` — the relative scaling factor
/// between this optimized output and the naive output.
pub fn c_s_f128() -> F128 {
    phi8(F8(C_S_F8))
}

/// The three F_128 small challenges (embeddings of [`SMALL_CHAL_F8`]) — caller
/// must place these at `r[k_skip..k_skip+3]` for the naive cross-check to
/// produce a result related to the optimized output by exactly `C_s`.
pub fn small_challenges_ghash() -> [F128; 3] {
    [
        phi8(F8(SMALL_CHAL_F8[0])),
        phi8(F8(SMALL_CHAL_F8[1])),
        phi8(F8(SMALL_CHAL_F8[2])),
    ]
}

/// The four F_128 medium challenges `β_i = γ^{2^{i-1}} / (1 + γ^{2^{i-1}})`.
/// Caller must place these at `r[k_skip+3..k_skip+7]` for the naive
/// cross-check.
pub fn medium_challenges_ghash() -> [F128; 4] {
    let g1 = F128 {
        lo: 1u64 << 1,
        hi: 0,
    }; // γ^1
    let g2 = F128 {
        lo: 1u64 << 2,
        hi: 0,
    }; // γ^2
    let g4 = F128 {
        lo: 1u64 << 4,
        hi: 0,
    }; // γ^4
    let g8 = F128 {
        lo: 1u64 << 8,
        hi: 0,
    }; // γ^8
    [
        g1 * (F128::ONE + g1).inv(),
        g2 * (F128::ONE + g2).inv(),
        g4 * (F128::ONE + g4).inv(),
        g8 * (F128::ONE + g8).inv(),
    ]
}

/// `C_2 = (1+r_2)(1+r_3)` where `r_2 = φ_8(0x53)` (= `α^2/(1+α^2)`),
/// `r_3 = φ_8(0xB5)` (= `α^4/(1+α^4)`). This is the residual small-eq
/// constant after the first small friendly bit (`b_3[0]`, indexed by
/// `r[k_skip] = φ_8(α)`) has been pulled out for the s_hat_v_c bank split:
///
/// ```text
/// eq([r[k_skip+1], r[k_skip+2]], (b_3[1], b_3[2])) = C_2 · α^{2 b_3[1] + 4 b_3[2]}
/// ```
///
/// Used in [`round1_shift_reduce_extract_c_packed_padded_with_s_hat_v`] to
/// post-scale the raw bank values into canonical `s_hat_v_c` (which
/// `ring_switch::fold_1b_rows` would produce against suffix `r[k_skip+1..m]`).
pub fn c_2_small_f128() -> F128 {
    let r_2 = phi8(F8(SMALL_CHAL_F8[1]));
    let r_3 = phi8(F8(SMALL_CHAL_F8[2]));
    (F128::ONE + r_2) * (F128::ONE + r_3)
}

/// `α⁻¹` in F_128, as a subfield-embedded F_8 element. Used to strip the
/// extra `α` factor from `s_hat_v_c`'s bank 1 (the K-odd lattice's raw
/// contribution is `α · α^{2 b_3[1] + 4 b_3[2]}`; canonical wants just
/// `α^{2 b_3[1] + 4 b_3[2]}`).
pub fn alpha_inv_f128() -> F128 {
    // α in F_8 = byte 0x02 (the polynomial generator). Its inverse is α^254;
    // F8::inv computes it via the standard extended Euclidean / power table.
    phi8(F8(0x02).inv())
}

/// `D = (1+γ)(1+γ^2)(1+γ^4)(1+γ^8)`; `D⁻¹` cancels the medium-eq normalization.
fn compute_d_inv() -> F128 {
    let g1 = F128 {
        lo: 1u64 << 1,
        hi: 0,
    };
    let g2 = F128 {
        lo: 1u64 << 2,
        hi: 0,
    };
    let g4 = F128 {
        lo: 1u64 << 4,
        hi: 0,
    };
    let g8 = F128 {
        lo: 1u64 << 8,
        hi: 0,
    };
    ((F128::ONE + g1) * (F128::ONE + g2) * (F128::ONE + g4) * (F128::ONE + g8)).inv()
}

static D_INV_CACHE: OnceLock<F128> = OnceLock::new();
fn d_inv() -> F128 {
    *D_INV_CACHE.get_or_init(compute_d_inv)
}

// ---------------------------------------------------------------------------
// Convert table: γ^b · φ_8(v) for b ∈ [0, 16), v ∈ [0, 256).
// 16 × 256 × 16 bytes = 64 KB. Computed once, cached via OnceLock.
// ---------------------------------------------------------------------------

const CONVERT_TABLE_SIZE: usize = 16 * 256;

static CONVERT_TABLE_CACHE: OnceLock<Vec<F128>> = OnceLock::new();

fn build_convert_table() -> Vec<F128> {
    let mut gamma_pow = [F128::ZERO; 16];
    gamma_pow[0] = F128::ONE;
    for b in 1..16 {
        gamma_pow[b] = mul_by_x(gamma_pow[b - 1]);
    }
    let mut table = vec![F128::ZERO; CONVERT_TABLE_SIZE];
    for b in 0..16 {
        let g_b = gamma_pow[b];
        for v in 0..256 {
            table[b * 256 + v] = g_b * PHI_8_TABLE[v];
        }
    }
    table
}

fn convert_table() -> &'static [F128] {
    CONVERT_TABLE_CACHE.get_or_init(build_convert_table)
}

// ---------------------------------------------------------------------------
// Bit transpose for C (scalar form of `bit_transpose_64bytes`).
//
// Input layout :  byte at offset (x_small * 8 + b_chunk) — bit t holds c at
//                 lane = 8*b_chunk + t with inner_K = x_small.
// Output layout:  byte at offset (b_chunk * 8 + t)        — bit K holds c at
//                 lane = 8*b_chunk + t with inner_K = K.
//
// So `out[lane]`'s 8 bits are the inner_K-direction polynomial of c at lane.
// ---------------------------------------------------------------------------

#[allow(dead_code)]
fn bit_transpose_64bytes_scalar(input: &[u8; 64], output: &mut [u8; 64]) {
    output.iter_mut().for_each(|x| *x = 0);
    for byte_idx in 0..64 {
        let x_small = byte_idx / 8;
        let b_chunk = byte_idx % 8;
        for t in 0..8 {
            let bit = (input[byte_idx] >> t) & 1;
            if bit != 0 {
                output[b_chunk * 8 + t] |= 1u8 << x_small;
            }
        }
    }
}

/// NEON 64-byte bit-transpose. Two-stage:
///   1. `vqtbl4q_u8` reorders the 64 input bytes so each 8-byte group within
///      the output is one byte-chunk's worth of `x_small=0..8` bytes.
///   2. Three rounds of bit-swap at distances 7, 14, 28 across `uint64x2_t`
///      lanes do the actual 8×8 bit transpose.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn bit_transpose_64bytes_neon(input: &[u8; 64], output: &mut [u8; 64]) {
    use core::arch::aarch64::*;

    unsafe {
        let in_ptr = input.as_ptr();
        let v0 = vld1q_u8(in_ptr);
        let v1 = vld1q_u8(in_ptr.add(16));
        let v2 = vld1q_u8(in_ptr.add(32));
        let v3 = vld1q_u8(in_ptr.add(48));
        let table = uint8x16x4_t(v0, v1, v2, v3);

        // vqtbl4q indexes that bring bytes belonging to byte-chunk b ∈ 0..8
        // into contiguous 8-byte runs, packed two-chunks-per-Q-reg.
        const IDX0: [u8; 16] = [0, 8, 16, 24, 32, 40, 48, 56, 1, 9, 17, 25, 33, 41, 49, 57];
        const IDX1: [u8; 16] = [2, 10, 18, 26, 34, 42, 50, 58, 3, 11, 19, 27, 35, 43, 51, 59];
        const IDX2: [u8; 16] = [4, 12, 20, 28, 36, 44, 52, 60, 5, 13, 21, 29, 37, 45, 53, 61];
        const IDX3: [u8; 16] = [6, 14, 22, 30, 38, 46, 54, 62, 7, 15, 23, 31, 39, 47, 55, 63];

        let mut y0 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX0.as_ptr())));
        let mut y1 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX1.as_ptr())));
        let mut y2 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX2.as_ptr())));
        let mut y3 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX3.as_ptr())));

        let mask1 = vdupq_n_u64(0x00AA00AA00AA00AA);
        let mask2 = vdupq_n_u64(0x0000CCCC0000CCCC);
        let mask3 = vdupq_n_u64(0x00000000F0F0F0F0);

        // Round 1: distance 7.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<7>(y0)), mask1);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<7>(y1)), mask1);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<7>(y2)), mask1);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<7>(y3)), mask1);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<7>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<7>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<7>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<7>(t3)));

        // Round 2: distance 14.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<14>(y0)), mask2);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<14>(y1)), mask2);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<14>(y2)), mask2);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<14>(y3)), mask2);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<14>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<14>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<14>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<14>(t3)));

        // Round 3: distance 28.
        let t0 = vandq_u64(veorq_u64(y0, vshrq_n_u64::<28>(y0)), mask3);
        let t1 = vandq_u64(veorq_u64(y1, vshrq_n_u64::<28>(y1)), mask3);
        let t2 = vandq_u64(veorq_u64(y2, vshrq_n_u64::<28>(y2)), mask3);
        let t3 = vandq_u64(veorq_u64(y3, vshrq_n_u64::<28>(y3)), mask3);
        y0 = veorq_u64(y0, veorq_u64(t0, vshlq_n_u64::<28>(t0)));
        y1 = veorq_u64(y1, veorq_u64(t1, vshlq_n_u64::<28>(t1)));
        y2 = veorq_u64(y2, veorq_u64(t2, vshlq_n_u64::<28>(t2)));
        y3 = veorq_u64(y3, veorq_u64(t3, vshlq_n_u64::<28>(t3)));

        let out_ptr = output.as_mut_ptr();
        vst1q_u8(out_ptr, vreinterpretq_u8_u64(y0));
        vst1q_u8(out_ptr.add(16), vreinterpretq_u8_u64(y1));
        vst1q_u8(out_ptr.add(32), vreinterpretq_u8_u64(y2));
        vst1q_u8(out_ptr.add(48), vreinterpretq_u8_u64(y3));
    }
}

#[inline]
pub fn bit_transpose_64bytes(input: &[u8; 64], output: &mut [u8; 64]) {
    #[cfg(target_arch = "aarch64")]
    // SAFETY: aarch64 statically guarantees NEON.
    unsafe {
        bit_transpose_64bytes_neon(input, output)
    }
    #[cfg(not(target_arch = "aarch64"))]
    bit_transpose_64bytes_scalar(input, output);
}

// ---------------------------------------------------------------------------
// Shift_reduce inner kernel (AB only — extract_c handles C separately).
//
// For one medium-position b_med and the 8 small-positions K ∈ 0..8:
//   1. Look up NTT-extended A,B at chunk `chunk_byte_base + (b_med*8 + K)*8`.
//   2. y_K[lane] = ntt_a[lane] · ntt_b[lane]  (in F_8).
//   3. acc[lane] ^= (y_K[lane] as u16) << K   (no reduction yet).
// At the end, reduce each acc[lane] back to a u8 in F_8.
//
// Output `out[lane]` is the F_8 representative of Σ_K x^K · y_K[lane] mod p.
// ---------------------------------------------------------------------------

// Intermediate-stage NEON kernel: scalar `inv_table.apply` writing to
// `a_col`/`b_col` Vecs, then NEON `gf8_mul_vec16` from those Vecs. Superseded
// by `shift_reduce_inner_ab_fused_neon` which keeps everything register-
// resident; kept under `#[allow(dead_code)]` as a cross-check oracle.
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)]
fn shift_reduce_inner_ab_neon(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
    a_col: &mut [F8],
    b_col: &mut [F8],
) {
    use crate::field::gf2_8::neon::{gf8_mul_vec16, gf8_reduce_vec16};
    use core::arch::aarch64::*;

    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;

    // Four (lo, hi) pairs of u16x8 accumulators = 64 u16 lanes total, matching
    // the 64 lanes of the inv-NTT output.
    unsafe {
        let mut acc0_lo = vdupq_n_u16(0);
        let mut acc0_hi = vdupq_n_u16(0);
        let mut acc1_lo = vdupq_n_u16(0);
        let mut acc1_hi = vdupq_n_u16(0);
        let mut acc2_lo = vdupq_n_u16(0);
        let mut acc2_hi = vdupq_n_u16(0);
        let mut acc3_lo = vdupq_n_u16(0);
        let mut acc3_hi = vdupq_n_u16(0);

        // Per-K step: scalar inv-NTT apply into a_col/b_col, then NEON load +
        // 4× gf8_mul_vec16 + 8× vshll_n_u8::<K> + 8× veorq_u16 into the accs.
        // K is `const` so vshll_n_u8 specializes per call site.
        macro_rules! step_k {
            ($k:literal) => {{
                let chunk_off = byte_base_b + $k * N_CHUNKS;
                inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], a_col);
                inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], b_col);
                let a_ptr = a_col.as_ptr() as *const u8;
                let b_ptr = b_col.as_ptr() as *const u8;
                let y0 = gf8_mul_vec16(vld1q_u8(a_ptr), vld1q_u8(b_ptr));
                let y1 = gf8_mul_vec16(vld1q_u8(a_ptr.add(16)), vld1q_u8(b_ptr.add(16)));
                let y2 = gf8_mul_vec16(vld1q_u8(a_ptr.add(32)), vld1q_u8(b_ptr.add(32)));
                let y3 = gf8_mul_vec16(vld1q_u8(a_ptr.add(48)), vld1q_u8(b_ptr.add(48)));
                acc0_lo = veorq_u16(acc0_lo, vshll_n_u8::<$k>(vget_low_u8(y0)));
                acc0_hi = veorq_u16(acc0_hi, vshll_n_u8::<$k>(vget_high_u8(y0)));
                acc1_lo = veorq_u16(acc1_lo, vshll_n_u8::<$k>(vget_low_u8(y1)));
                acc1_hi = veorq_u16(acc1_hi, vshll_n_u8::<$k>(vget_high_u8(y1)));
                acc2_lo = veorq_u16(acc2_lo, vshll_n_u8::<$k>(vget_low_u8(y2)));
                acc2_hi = veorq_u16(acc2_hi, vshll_n_u8::<$k>(vget_high_u8(y2)));
                acc3_lo = veorq_u16(acc3_lo, vshll_n_u8::<$k>(vget_low_u8(y3)));
                acc3_hi = veorq_u16(acc3_hi, vshll_n_u8::<$k>(vget_high_u8(y3)));
            }};
        }

        step_k!(0);
        step_k!(1);
        step_k!(2);
        step_k!(3);
        step_k!(4);
        step_k!(5);
        step_k!(6);
        step_k!(7);

        // Final F_8 reduction: each (acc_lo, acc_hi) pair → 16 reduced u8 values.
        let r0 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc0_lo), vreinterpretq_u8_u16(acc0_hi));
        let r1 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc1_lo), vreinterpretq_u8_u16(acc1_hi));
        let r2 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc2_lo), vreinterpretq_u8_u16(acc2_hi));
        let r3 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc3_lo), vreinterpretq_u8_u16(acc3_hi));

        let out_ptr = out.as_mut_ptr();
        vst1q_u8(out_ptr, r0);
        vst1q_u8(out_ptr.add(16), r1);
        vst1q_u8(out_ptr.add(32), r2);
        vst1q_u8(out_ptr.add(48), r3);
    }
}

// ---------------------------------------------------------------------------
// Fused NEON inner kernel: inv_NTT apply + F_8 mul + shift_reduce, all in
// NEON registers (no Vec<F8> round-trip).
//
// `xor_apply_byte_into_8_regs::<BH, ODD>` handles one byte position (b ≥ 1).
// `BH` (= b >> 1) selects which chunk-index XOR to apply; `ODD` (= b & 1)
// switches on the within-chunk half-swap. Both const-generic so the compiler
// dead-code-eliminates the if-branch and folds the chunk-index XORs.
//
// `fused_apply_one_k::<K>` runs one full K-row: the initial b=0 plain load,
// 7 calls to the byte helper for b=1..7 (with the specific protocol BH/ODD
// pattern), one 16-lane F_8 mul per output chunk, and finally widen-shift-XOR
// into the per-(K, lane) 16-bit accumulators.
// ---------------------------------------------------------------------------

#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn xor_apply_byte_into_8_regs<const BH: usize, const ODD: bool>(
    table_base: *const u8,
    a_byte: u8,
    b_byte: u8,
    da0: &mut core::arch::aarch64::uint8x16_t,
    da1: &mut core::arch::aarch64::uint8x16_t,
    da2: &mut core::arch::aarch64::uint8x16_t,
    da3: &mut core::arch::aarch64::uint8x16_t,
    db0: &mut core::arch::aarch64::uint8x16_t,
    db1: &mut core::arch::aarch64::uint8x16_t,
    db2: &mut core::arch::aarch64::uint8x16_t,
    db3: &mut core::arch::aarch64::uint8x16_t,
) {
    use core::arch::aarch64::*;
    unsafe {
        let ra = table_base.add(a_byte as usize * 64);
        let rb = table_base.add(b_byte as usize * 64);
        let va0 = vld1q_u8(ra.add((0 ^ BH) * 16));
        let va1 = vld1q_u8(ra.add((1 ^ BH) * 16));
        let va2 = vld1q_u8(ra.add((2 ^ BH) * 16));
        let va3 = vld1q_u8(ra.add((3 ^ BH) * 16));
        let vb0 = vld1q_u8(rb.add((0 ^ BH) * 16));
        let vb1 = vld1q_u8(rb.add((1 ^ BH) * 16));
        let vb2 = vld1q_u8(rb.add((2 ^ BH) * 16));
        let vb3 = vld1q_u8(rb.add((3 ^ BH) * 16));
        let (va0, va1, va2, va3, vb0, vb1, vb2, vb3) = if ODD {
            (
                vextq_u8::<8>(va0, va0),
                vextq_u8::<8>(va1, va1),
                vextq_u8::<8>(va2, va2),
                vextq_u8::<8>(va3, va3),
                vextq_u8::<8>(vb0, vb0),
                vextq_u8::<8>(vb1, vb1),
                vextq_u8::<8>(vb2, vb2),
                vextq_u8::<8>(vb3, vb3),
            )
        } else {
            (va0, va1, va2, va3, vb0, vb1, vb2, vb3)
        };
        *da0 = veorq_u8(*da0, va0);
        *da1 = veorq_u8(*da1, va1);
        *da2 = veorq_u8(*da2, va2);
        *da3 = veorq_u8(*da3, va3);
        *db0 = veorq_u8(*db0, vb0);
        *db1 = veorq_u8(*db1, vb1);
        *db2 = veorq_u8(*db2, vb2);
        *db3 = veorq_u8(*db3, vb3);
    }
}

/// Process one K-row: 8 byte positions of `a` and `b` via the inv_NTT table,
/// F_8 multiply, widen-shift by K, XOR into the four `(acc_lo, acc_hi)` pairs.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn fused_apply_one_k<const K: i32>(
    table_base: *const u8,
    a_row: *const u8,
    b_row: *const u8,
    acc0_lo: &mut core::arch::aarch64::uint16x8_t,
    acc0_hi: &mut core::arch::aarch64::uint16x8_t,
    acc1_lo: &mut core::arch::aarch64::uint16x8_t,
    acc1_hi: &mut core::arch::aarch64::uint16x8_t,
    acc2_lo: &mut core::arch::aarch64::uint16x8_t,
    acc2_hi: &mut core::arch::aarch64::uint16x8_t,
    acc3_lo: &mut core::arch::aarch64::uint16x8_t,
    acc3_hi: &mut core::arch::aarch64::uint16x8_t,
) {
    use crate::field::gf2_8::neon::gf8_mul_vec16;
    use core::arch::aarch64::*;
    unsafe {
        // b = 0: identity permutation — plain load of the 4 chunks.
        let ra0 = table_base.add(*a_row as usize * 64);
        let rb0 = table_base.add(*b_row as usize * 64);
        let mut da0 = vld1q_u8(ra0);
        let mut da1 = vld1q_u8(ra0.add(16));
        let mut da2 = vld1q_u8(ra0.add(32));
        let mut da3 = vld1q_u8(ra0.add(48));
        let mut db0 = vld1q_u8(rb0);
        let mut db1 = vld1q_u8(rb0.add(16));
        let mut db2 = vld1q_u8(rb0.add(32));
        let mut db3 = vld1q_u8(rb0.add(48));

        // b = 1..7: XOR with table row[bytes[b]], permuted per (BH, ODD).
        xor_apply_byte_into_8_regs::<0, true>(
            table_base,
            *a_row.add(1),
            *b_row.add(1),
            &mut da0,
            &mut da1,
            &mut da2,
            &mut da3,
            &mut db0,
            &mut db1,
            &mut db2,
            &mut db3,
        );
        xor_apply_byte_into_8_regs::<1, false>(
            table_base,
            *a_row.add(2),
            *b_row.add(2),
            &mut da0,
            &mut da1,
            &mut da2,
            &mut da3,
            &mut db0,
            &mut db1,
            &mut db2,
            &mut db3,
        );
        xor_apply_byte_into_8_regs::<1, true>(
            table_base,
            *a_row.add(3),
            *b_row.add(3),
            &mut da0,
            &mut da1,
            &mut da2,
            &mut da3,
            &mut db0,
            &mut db1,
            &mut db2,
            &mut db3,
        );
        xor_apply_byte_into_8_regs::<2, false>(
            table_base,
            *a_row.add(4),
            *b_row.add(4),
            &mut da0,
            &mut da1,
            &mut da2,
            &mut da3,
            &mut db0,
            &mut db1,
            &mut db2,
            &mut db3,
        );
        xor_apply_byte_into_8_regs::<2, true>(
            table_base,
            *a_row.add(5),
            *b_row.add(5),
            &mut da0,
            &mut da1,
            &mut da2,
            &mut da3,
            &mut db0,
            &mut db1,
            &mut db2,
            &mut db3,
        );
        xor_apply_byte_into_8_regs::<3, false>(
            table_base,
            *a_row.add(6),
            *b_row.add(6),
            &mut da0,
            &mut da1,
            &mut da2,
            &mut da3,
            &mut db0,
            &mut db1,
            &mut db2,
            &mut db3,
        );
        xor_apply_byte_into_8_regs::<3, true>(
            table_base,
            *a_row.add(7),
            *b_row.add(7),
            &mut da0,
            &mut da1,
            &mut da2,
            &mut da3,
            &mut db0,
            &mut db1,
            &mut db2,
            &mut db3,
        );

        // F_8 multiply lane-wise (4 × 16 lanes = 64 total).
        let y0 = gf8_mul_vec16(da0, db0);
        let y1 = gf8_mul_vec16(da1, db1);
        let y2 = gf8_mul_vec16(da2, db2);
        let y3 = gf8_mul_vec16(da3, db3);

        // Widen-shift by K, XOR into the 16-bit accumulators.
        *acc0_lo = veorq_u16(*acc0_lo, vshll_n_u8::<K>(vget_low_u8(y0)));
        *acc0_hi = veorq_u16(*acc0_hi, vshll_n_u8::<K>(vget_high_u8(y0)));
        *acc1_lo = veorq_u16(*acc1_lo, vshll_n_u8::<K>(vget_low_u8(y1)));
        *acc1_hi = veorq_u16(*acc1_hi, vshll_n_u8::<K>(vget_high_u8(y1)));
        *acc2_lo = veorq_u16(*acc2_lo, vshll_n_u8::<K>(vget_low_u8(y2)));
        *acc2_hi = veorq_u16(*acc2_hi, vshll_n_u8::<K>(vget_high_u8(y2)));
        *acc3_lo = veorq_u16(*acc3_lo, vshll_n_u8::<K>(vget_low_u8(y3)));
        *acc3_hi = veorq_u16(*acc3_hi, vshll_n_u8::<K>(vget_high_u8(y3)));
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn shift_reduce_inner_ab_fused_neon(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
) {
    use crate::field::gf2_8::neon::gf8_reduce_vec16;
    use core::arch::aarch64::*;

    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    let table_base = inv_table.data_ptr();

    unsafe {
        let mut acc0_lo = vdupq_n_u16(0);
        let mut acc0_hi = vdupq_n_u16(0);
        let mut acc1_lo = vdupq_n_u16(0);
        let mut acc1_hi = vdupq_n_u16(0);
        let mut acc2_lo = vdupq_n_u16(0);
        let mut acc2_hi = vdupq_n_u16(0);
        let mut acc3_lo = vdupq_n_u16(0);
        let mut acc3_hi = vdupq_n_u16(0);

        // 8 K-iterations — each consumes N_CHUNKS = 8 packed witness bytes
        // for `a` and `b`. K is a const generic so `vshll_n_u8::<K>` specializes.
        macro_rules! do_k {
            ($k:literal) => {{
                let off = byte_base_b + $k * N_CHUNKS;
                fused_apply_one_k::<$k>(
                    table_base,
                    a_packed.as_ptr().add(off),
                    b_packed.as_ptr().add(off),
                    &mut acc0_lo,
                    &mut acc0_hi,
                    &mut acc1_lo,
                    &mut acc1_hi,
                    &mut acc2_lo,
                    &mut acc2_hi,
                    &mut acc3_lo,
                    &mut acc3_hi,
                );
            }};
        }
        do_k!(0);
        do_k!(1);
        do_k!(2);
        do_k!(3);
        do_k!(4);
        do_k!(5);
        do_k!(6);
        do_k!(7);

        // Reduce 16-bit accs → 16-byte F_8 results (4 × 16 lanes).
        let r0 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc0_lo), vreinterpretq_u8_u16(acc0_hi));
        let r1 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc1_lo), vreinterpretq_u8_u16(acc1_hi));
        let r2 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc2_lo), vreinterpretq_u8_u16(acc2_hi));
        let r3 = gf8_reduce_vec16(vreinterpretq_u8_u16(acc3_lo), vreinterpretq_u8_u16(acc3_hi));

        let p = out.as_mut_ptr();
        vst1q_u8(p, r0);
        vst1q_u8(p.add(16), r1);
        vst1q_u8(p.add(32), r2);
        vst1q_u8(p.add(48), r3);
    }
}

/// Dispatch helper — picks the fused NEON kernel when available, otherwise scalar.
#[inline]
fn shift_reduce_inner_ab(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
    a_col: &mut [F8],
    b_col: &mut [F8],
) {
    #[cfg(target_arch = "aarch64")]
    {
        let _ = (a_col, b_col); // unused in the fused path
        shift_reduce_inner_ab_fused_neon(
            a_packed,
            b_packed,
            inv_table,
            chunk_byte_base,
            b_med,
            out,
        );
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        shift_reduce_inner_ab_scalar(
            a_packed,
            b_packed,
            inv_table,
            chunk_byte_base,
            b_med,
            out,
            a_col,
            b_col,
        );
    }
}

/// Kept under `#[allow(dead_code)]` because on aarch64 the dispatcher only
/// reaches `_neon` — but this scalar version remains the non-aarch64 fallback
/// AND the cross-check oracle used by `neon_inner_matches_scalar_inner`.
#[allow(dead_code)]
fn shift_reduce_inner_ab_scalar(
    a_packed: &[u8],
    b_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    chunk_byte_base: usize,
    b_med: usize,
    out: &mut [u8; 64],
    a_col: &mut [F8],
    b_col: &mut [F8],
) {
    let mut acc: [u16; 64] = [0u16; 64];
    let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
    for k in 0..8 {
        let chunk_off = byte_base_b + k * N_CHUNKS;
        inv_table.apply(&a_packed[chunk_off..chunk_off + N_CHUNKS], a_col);
        inv_table.apply(&b_packed[chunk_off..chunk_off + N_CHUNKS], b_col);
        for lane in 0..ELL {
            let y = (a_col[lane] * b_col[lane]).0 as u16;
            acc[lane] ^= y << k;
        }
    }
    for lane in 0..ELL {
        out[lane] = gf8_reduce(acc[lane]);
    }
}

// ---------------------------------------------------------------------------
// Main optimized round-1 prover message.
// ---------------------------------------------------------------------------

/// Compute the round-1 prover message via the full shift_reduce + extract_c
/// optimization, in scalar Rust.
///
/// Output relative to [`super::round1_naive`]:
///   `C_s · (res_AB[i] + res_C_lifted[i]) = naive_p_ab[i] + naive_p_c[i]`
///
/// Preconditions:
/// - `k_skip == K_SKIP` (= 6)
/// - `m >= k_skip + N_INNER` (= 13)
/// - `r.len() == m`. `r[k_skip..k_skip+7]` must hold the protocol-fixed small
///   + medium constants (see [`small_challenges_ghash`] /
///   [`medium_challenges_ghash`]) for the naive cross-check to line up. Only
///   `r[k_skip+7..m]` is used internally.
/// - `inv_table.k == k_skip`.
pub fn round1_shift_reduce_extract_c(
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
    round1_shift_reduce_extract_c_packed(&a_packed, &b_packed, &c_packed, m, k_skip, r, inv_table)
}

// Per-worker scratch + local accumulator. ~6 KB total, stack-allocated.
struct WorkerState {
    partial_ab: [F128; ELL],
    partial_c: [F128; ELL],
    chunk_ab_bytes: [[u8; 64]; 1 << N_MEDIUM],
    chunk_c_bytes: [[u8; 64]; 1 << N_MEDIUM],
    a_col: [F8; ELL],
    b_col: [F8; ELL],
    local_res_ab: [F128; ELL],
    local_res_c_s: [F128; ELL],
}

impl WorkerState {
    fn new() -> Self {
        Self {
            partial_ab: [F128::ZERO; ELL],
            partial_c: [F128::ZERO; ELL],
            chunk_ab_bytes: [[0u8; 64]; 1 << N_MEDIUM],
            chunk_c_bytes: [[0u8; 64]; 1 << N_MEDIUM],
            a_col: [F8::ZERO; ELL],
            b_col: [F8::ZERO; ELL],
            local_res_ab: [F128::ZERO; ELL],
            local_res_c_s: [F128::ZERO; ELL],
        }
    }
}

/// Process one outer x_hi value: middle-loop over x_outer_lo (reset `partial_ab/c`,
/// run shift_reduce_inner + bit_transpose + convert+apply), then outer fold by
/// `eq_hi_val` into `state.local_res_ab/c_s`.
///
/// Called per-x_hi by both the parallel public function and the serial test oracle.
///
/// `within_outer_mask` and `b_med_counts` together encode the per-block padding
/// pattern (see [`PaddingSpec`]). For each x_outer, `within_hash_outer =
/// x_outer & within_outer_mask` is the position of its 8192-bit window within
/// a block, and `b_med_counts[within_hash_outer]` tells the kernel how many
/// of the 16 b_med 512-bit sub-windows are worth processing — the rest fall
/// entirely in zero padding and are skipped. Pass `within_outer_mask = 0` and
/// `b_med_counts = &[1 << N_MEDIUM]` to disable skipping.
#[inline]
#[allow(clippy::too_many_arguments)]
fn process_one_x_hi(
    x_hi: usize,
    big_lo_size: usize,
    n_lo_and_inner: usize,
    within_outer_mask: usize,
    b_med_counts: &[u8],
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    eq_lo_scaled: &[F128],
    eq_hi_val: F128,
    convert: &[F128],
    state: &mut WorkerState,
) {
    state.partial_ab.iter_mut().for_each(|p| *p = F128::ZERO);
    state.partial_c.iter_mut().for_each(|p| *p = F128::ZERO);

    let n_lo = n_lo_and_inner - N_INNER;

    for x_outer_lo in 0..big_lo_size {
        let x_outer = x_outer_lo | (x_hi << n_lo);
        let within_hash_outer = x_outer & within_outer_mask;
        let n_b_med = b_med_counts[within_hash_outer] as usize;
        if n_b_med == 0 {
            continue;
        }

        let chunk_byte_base = ((x_outer_lo << N_INNER) | (x_hi << n_lo_and_inner)) * N_CHUNKS;

        let eq_lo_val = eq_lo_scaled[x_outer_lo];

        // Two paths: when n_b_med == 16 (the full case — true for every
        // x_outer_lo on the dense path, and for most of them on the padded
        // path too), use compile-time loop bounds so the SIMD XOR chain
        // unrolls. The slow path handles the rare boundary window where
        // n_b_med < 16.
        if n_b_med == (1 << N_MEDIUM) {
            for b_med in 0..(1 << N_MEDIUM) {
                shift_reduce_inner_ab(
                    a_packed,
                    b_packed,
                    inv_table,
                    chunk_byte_base,
                    b_med,
                    &mut state.chunk_ab_bytes[b_med],
                    &mut state.a_col,
                    &mut state.b_col,
                );
                let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
                let c_in: &[u8; 64] = (&c_packed[byte_base_b..byte_base_b + 64])
                    .try_into()
                    .expect("64 c-bytes per medium position");
                bit_transpose_64bytes(c_in, &mut state.chunk_c_bytes[b_med]);
            }

            #[cfg(target_arch = "aarch64")]
            unsafe {
                use core::arch::aarch64::*;
                let convert_ptr = convert.as_ptr() as *const u8;
                for lane in 0..ELL {
                    let mut cf_ab = vdupq_n_u8(0);
                    let mut cf_c = vdupq_n_u8(0);
                    for b_med in 0..(1 << N_MEDIUM) {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        cf_ab =
                            veorq_u8(cf_ab, vld1q_u8(convert_ptr.add((b_med * 256 + v_ab) * 16)));
                        cf_c = veorq_u8(cf_c, vld1q_u8(convert_ptr.add((b_med * 256 + v_c) * 16)));
                    }
                    let cf_ab_u64 = vreinterpretq_u64_u8(cf_ab);
                    let cf_c_u64 = vreinterpretq_u64_u8(cf_c);
                    let cf_ab_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_ab_u64),
                        hi: vgetq_lane_u64::<1>(cf_ab_u64),
                    };
                    let cf_c_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_c_u64),
                        hi: vgetq_lane_u64::<1>(cf_c_u64),
                    };
                    state.partial_ab[lane] += cf_ab_f * eq_lo_val;
                    state.partial_c[lane] += cf_c_f * eq_lo_val;
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            {
                for lane in 0..ELL {
                    let mut cf_ab = F128::ZERO;
                    let mut cf_c = F128::ZERO;
                    for b_med in 0..(1 << N_MEDIUM) {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        cf_ab += convert[b_med * 256 + v_ab];
                        cf_c += convert[b_med * 256 + v_c];
                    }
                    state.partial_ab[lane] += cf_ab * eq_lo_val;
                    state.partial_c[lane] += cf_c * eq_lo_val;
                }
            }
        } else {
            // Partial path: n_b_med ∈ (0, 1 << N_MEDIUM). At most one
            // within_hash_outer value per [`PaddingSpec`] lands here (the
            // window straddling the useful/padding boundary), so the tighter
            // loop wins despite losing the SIMD chain unroll.
            for b_med in 0..n_b_med {
                shift_reduce_inner_ab(
                    a_packed,
                    b_packed,
                    inv_table,
                    chunk_byte_base,
                    b_med,
                    &mut state.chunk_ab_bytes[b_med],
                    &mut state.a_col,
                    &mut state.b_col,
                );
                let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
                let c_in: &[u8; 64] = (&c_packed[byte_base_b..byte_base_b + 64])
                    .try_into()
                    .expect("64 c-bytes per medium position");
                bit_transpose_64bytes(c_in, &mut state.chunk_c_bytes[b_med]);
            }

            #[cfg(target_arch = "aarch64")]
            unsafe {
                use core::arch::aarch64::*;
                let convert_ptr = convert.as_ptr() as *const u8;
                for lane in 0..ELL {
                    let mut cf_ab = vdupq_n_u8(0);
                    let mut cf_c = vdupq_n_u8(0);
                    for b_med in 0..n_b_med {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        cf_ab =
                            veorq_u8(cf_ab, vld1q_u8(convert_ptr.add((b_med * 256 + v_ab) * 16)));
                        cf_c = veorq_u8(cf_c, vld1q_u8(convert_ptr.add((b_med * 256 + v_c) * 16)));
                    }
                    let cf_ab_u64 = vreinterpretq_u64_u8(cf_ab);
                    let cf_c_u64 = vreinterpretq_u64_u8(cf_c);
                    let cf_ab_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_ab_u64),
                        hi: vgetq_lane_u64::<1>(cf_ab_u64),
                    };
                    let cf_c_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_c_u64),
                        hi: vgetq_lane_u64::<1>(cf_c_u64),
                    };
                    state.partial_ab[lane] += cf_ab_f * eq_lo_val;
                    state.partial_c[lane] += cf_c_f * eq_lo_val;
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            {
                for lane in 0..ELL {
                    let mut cf_ab = F128::ZERO;
                    let mut cf_c = F128::ZERO;
                    for b_med in 0..n_b_med {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        cf_ab += convert[b_med * 256 + v_ab];
                        cf_c += convert[b_med * 256 + v_c];
                    }
                    state.partial_ab[lane] += cf_ab * eq_lo_val;
                    state.partial_c[lane] += cf_c * eq_lo_val;
                }
            }
        }
    }

    // Outer fold by eq_hi.
    for lane in 0..ELL {
        state.local_res_ab[lane] += eq_hi_val * state.partial_ab[lane];
        state.local_res_c_s[lane] += eq_hi_val * state.partial_c[lane];
    }
}

// ---------------------------------------------------------------------------
// Fusion: two-bank C accumulator that produces s_hat_v_c alongside round 1.
//
// The only structural change from `process_one_x_hi` is in the C-side inner
// loop: instead of one `cf_c` accumulator collapsing all 3 small bits, we
// keep `b_3[0]` (= bit `k_skip` of the witness, = `b_7` in ring-switch's
// packed-prefix index) as a routing dim. Two `cf_c` banks: bank 0 takes
// the K-even contributions (`v_c & 0x55`), bank 1 takes K-odd (`v_c & 0xAA`).
// By F_2-linearity of φ_8, `PHI_8(v) == PHI_8(v & 0x55) + PHI_8(v & 0xAA)`,
// so summing the two banks reconstructs the original `cf_c` → wire `res_c_s`.
//
// Per chunk-lane-b_med, this costs +1 `vld1q_u8` + +1 `veorq_u8`. Everything
// else (shift_reduce_inner_ab, bit_transpose, partial_ab/c fold, eq_hi
// outer fold) is unchanged.
// ---------------------------------------------------------------------------

/// Per-worker scratch + local accumulator for the two-bank C variant.
/// Identical to [`WorkerState`] except `partial_c` and `local_res_c_s` are
/// split into bank 0 / bank 1.
struct WorkerStateWithSHatV {
    partial_ab: [F128; ELL],
    partial_c_0: [F128; ELL],
    partial_c_1: [F128; ELL],
    chunk_ab_bytes: [[u8; 64]; 1 << N_MEDIUM],
    chunk_c_bytes: [[u8; 64]; 1 << N_MEDIUM],
    a_col: [F8; ELL],
    b_col: [F8; ELL],
    local_res_ab: [F128; ELL],
    local_res_c_s_0: [F128; ELL],
    local_res_c_s_1: [F128; ELL],
}

impl WorkerStateWithSHatV {
    fn new() -> Self {
        Self {
            partial_ab: [F128::ZERO; ELL],
            partial_c_0: [F128::ZERO; ELL],
            partial_c_1: [F128::ZERO; ELL],
            chunk_ab_bytes: [[0u8; 64]; 1 << N_MEDIUM],
            chunk_c_bytes: [[0u8; 64]; 1 << N_MEDIUM],
            a_col: [F8::ZERO; ELL],
            b_col: [F8::ZERO; ELL],
            local_res_ab: [F128::ZERO; ELL],
            local_res_c_s_0: [F128::ZERO; ELL],
            local_res_c_s_1: [F128::ZERO; ELL],
        }
    }
}

/// Two-bank C variant of [`process_one_x_hi`]. AB-side and witness traffic
/// unchanged; the only modification is the C-side inner loop now maintains
/// `cf_c_0` and `cf_c_1` via masked convert-table lookups.
#[inline]
#[allow(clippy::too_many_arguments)]
fn process_one_x_hi_with_s_hat_v(
    x_hi: usize,
    big_lo_size: usize,
    n_lo_and_inner: usize,
    within_outer_mask: usize,
    b_med_counts: &[u8],
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    inv_table: &InvNttTableByteSingleGf8,
    eq_lo_scaled: &[F128],
    eq_hi_val: F128,
    convert: &[F128],
    state: &mut WorkerStateWithSHatV,
) {
    state.partial_ab.iter_mut().for_each(|p| *p = F128::ZERO);
    state.partial_c_0.iter_mut().for_each(|p| *p = F128::ZERO);
    state.partial_c_1.iter_mut().for_each(|p| *p = F128::ZERO);

    let n_lo = n_lo_and_inner - N_INNER;

    for x_outer_lo in 0..big_lo_size {
        let x_outer = x_outer_lo | (x_hi << n_lo);
        let within_hash_outer = x_outer & within_outer_mask;
        let n_b_med = b_med_counts[within_hash_outer] as usize;
        if n_b_med == 0 {
            continue;
        }

        let chunk_byte_base = ((x_outer_lo << N_INNER) | (x_hi << n_lo_and_inner)) * N_CHUNKS;
        let eq_lo_val = eq_lo_scaled[x_outer_lo];

        if n_b_med == (1 << N_MEDIUM) {
            for b_med in 0..(1 << N_MEDIUM) {
                shift_reduce_inner_ab(
                    a_packed,
                    b_packed,
                    inv_table,
                    chunk_byte_base,
                    b_med,
                    &mut state.chunk_ab_bytes[b_med],
                    &mut state.a_col,
                    &mut state.b_col,
                );
                let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
                let c_in: &[u8; 64] = (&c_packed[byte_base_b..byte_base_b + 64])
                    .try_into()
                    .expect("64 c-bytes per medium position");
                bit_transpose_64bytes(c_in, &mut state.chunk_c_bytes[b_med]);
            }

            #[cfg(target_arch = "aarch64")]
            unsafe {
                use core::arch::aarch64::*;
                let convert_ptr = convert.as_ptr() as *const u8;
                for lane in 0..ELL {
                    let mut cf_ab = vdupq_n_u8(0);
                    let mut cf_c_0 = vdupq_n_u8(0);
                    let mut cf_c_1 = vdupq_n_u8(0);
                    for b_med in 0..(1 << N_MEDIUM) {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        let v_c_0 = v_c & 0x55;
                        let v_c_1 = v_c & 0xAA;
                        cf_ab =
                            veorq_u8(cf_ab, vld1q_u8(convert_ptr.add((b_med * 256 + v_ab) * 16)));
                        cf_c_0 = veorq_u8(
                            cf_c_0,
                            vld1q_u8(convert_ptr.add((b_med * 256 + v_c_0) * 16)),
                        );
                        cf_c_1 = veorq_u8(
                            cf_c_1,
                            vld1q_u8(convert_ptr.add((b_med * 256 + v_c_1) * 16)),
                        );
                    }
                    let cf_ab_u64 = vreinterpretq_u64_u8(cf_ab);
                    let cf_c_0_u64 = vreinterpretq_u64_u8(cf_c_0);
                    let cf_c_1_u64 = vreinterpretq_u64_u8(cf_c_1);
                    let cf_ab_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_ab_u64),
                        hi: vgetq_lane_u64::<1>(cf_ab_u64),
                    };
                    let cf_c_0_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_c_0_u64),
                        hi: vgetq_lane_u64::<1>(cf_c_0_u64),
                    };
                    let cf_c_1_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_c_1_u64),
                        hi: vgetq_lane_u64::<1>(cf_c_1_u64),
                    };
                    state.partial_ab[lane] += cf_ab_f * eq_lo_val;
                    state.partial_c_0[lane] += cf_c_0_f * eq_lo_val;
                    state.partial_c_1[lane] += cf_c_1_f * eq_lo_val;
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            {
                for lane in 0..ELL {
                    let mut cf_ab = F128::ZERO;
                    let mut cf_c_0 = F128::ZERO;
                    let mut cf_c_1 = F128::ZERO;
                    for b_med in 0..(1 << N_MEDIUM) {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        cf_ab += convert[b_med * 256 + v_ab];
                        cf_c_0 += convert[b_med * 256 + (v_c & 0x55)];
                        cf_c_1 += convert[b_med * 256 + (v_c & 0xAA)];
                    }
                    state.partial_ab[lane] += cf_ab * eq_lo_val;
                    state.partial_c_0[lane] += cf_c_0 * eq_lo_val;
                    state.partial_c_1[lane] += cf_c_1 * eq_lo_val;
                }
            }
        } else {
            for b_med in 0..n_b_med {
                shift_reduce_inner_ab(
                    a_packed,
                    b_packed,
                    inv_table,
                    chunk_byte_base,
                    b_med,
                    &mut state.chunk_ab_bytes[b_med],
                    &mut state.a_col,
                    &mut state.b_col,
                );
                let byte_base_b = chunk_byte_base + b_med * N_CHUNKS * 8;
                let c_in: &[u8; 64] = (&c_packed[byte_base_b..byte_base_b + 64])
                    .try_into()
                    .expect("64 c-bytes per medium position");
                bit_transpose_64bytes(c_in, &mut state.chunk_c_bytes[b_med]);
            }

            #[cfg(target_arch = "aarch64")]
            unsafe {
                use core::arch::aarch64::*;
                let convert_ptr = convert.as_ptr() as *const u8;
                for lane in 0..ELL {
                    let mut cf_ab = vdupq_n_u8(0);
                    let mut cf_c_0 = vdupq_n_u8(0);
                    let mut cf_c_1 = vdupq_n_u8(0);
                    for b_med in 0..n_b_med {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        let v_c_0 = v_c & 0x55;
                        let v_c_1 = v_c & 0xAA;
                        cf_ab =
                            veorq_u8(cf_ab, vld1q_u8(convert_ptr.add((b_med * 256 + v_ab) * 16)));
                        cf_c_0 = veorq_u8(
                            cf_c_0,
                            vld1q_u8(convert_ptr.add((b_med * 256 + v_c_0) * 16)),
                        );
                        cf_c_1 = veorq_u8(
                            cf_c_1,
                            vld1q_u8(convert_ptr.add((b_med * 256 + v_c_1) * 16)),
                        );
                    }
                    let cf_ab_u64 = vreinterpretq_u64_u8(cf_ab);
                    let cf_c_0_u64 = vreinterpretq_u64_u8(cf_c_0);
                    let cf_c_1_u64 = vreinterpretq_u64_u8(cf_c_1);
                    let cf_ab_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_ab_u64),
                        hi: vgetq_lane_u64::<1>(cf_ab_u64),
                    };
                    let cf_c_0_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_c_0_u64),
                        hi: vgetq_lane_u64::<1>(cf_c_0_u64),
                    };
                    let cf_c_1_f = F128 {
                        lo: vgetq_lane_u64::<0>(cf_c_1_u64),
                        hi: vgetq_lane_u64::<1>(cf_c_1_u64),
                    };
                    state.partial_ab[lane] += cf_ab_f * eq_lo_val;
                    state.partial_c_0[lane] += cf_c_0_f * eq_lo_val;
                    state.partial_c_1[lane] += cf_c_1_f * eq_lo_val;
                }
            }
            #[cfg(not(target_arch = "aarch64"))]
            {
                for lane in 0..ELL {
                    let mut cf_ab = F128::ZERO;
                    let mut cf_c_0 = F128::ZERO;
                    let mut cf_c_1 = F128::ZERO;
                    for b_med in 0..n_b_med {
                        let v_ab = state.chunk_ab_bytes[b_med][lane] as usize;
                        let v_c = state.chunk_c_bytes[b_med][lane] as usize;
                        cf_ab += convert[b_med * 256 + v_ab];
                        cf_c_0 += convert[b_med * 256 + (v_c & 0x55)];
                        cf_c_1 += convert[b_med * 256 + (v_c & 0xAA)];
                    }
                    state.partial_ab[lane] += cf_ab * eq_lo_val;
                    state.partial_c_0[lane] += cf_c_0 * eq_lo_val;
                    state.partial_c_1[lane] += cf_c_1 * eq_lo_val;
                }
            }
        }
    }

    // Outer fold by eq_hi (per bank).
    for lane in 0..ELL {
        state.local_res_ab[lane] += eq_hi_val * state.partial_ab[lane];
        state.local_res_c_s_0[lane] += eq_hi_val * state.partial_c_0[lane];
        state.local_res_c_s_1[lane] += eq_hi_val * state.partial_c_1[lane];
    }
}

/// Build the `b_med_counts` table from a [`PaddingSpec`] for use by
/// [`process_one_x_hi`].
///
/// Returns `(within_outer_mask, b_med_counts)`:
///   - `within_outer_mask` masks `x_outer` to the bits identifying the
///     within-block window.
///   - `b_med_counts[w]` is how many of the 16 b_med 512-bit sub-windows of
///     window `w` we should process. Entries past the useful prefix are 0
///     (full skip) — kernels just `continue` past those x_outer_lo iterations.
fn build_b_med_counts(padding: &PaddingSpec) -> (usize, Vec<u8>) {
    const STRIDE: usize = 1 << (K_SKIP + N_INNER); // 8192 bits per within-window
    const B_MED_WINDOW: usize = 1 << (K_SKIP + 3); // 512 bits per b_med
    const N_B_MED_MAX: usize = 1 << N_MEDIUM;

    // For k_log < K_SKIP + N_INNER (= 13) the within-window granularity is
    // coarser than the block itself — skipping at this granularity would be
    // incorrect, so we fall back to "no skip". All hash modules use
    // k_log ∈ {14, 15, 16}.
    if padding.k_log < K_SKIP + N_INNER {
        return (0, vec![N_B_MED_MAX as u8]);
    }
    let within_outer_bits = padding.k_log - K_SKIP - N_INNER;
    let within_outer_count = 1usize << within_outer_bits;
    let within_outer_mask = within_outer_count - 1;
    let useful = padding.useful_bits_per_block;
    let counts: Vec<u8> = (0..within_outer_count)
        .map(|w| {
            let block_start = w * STRIDE;
            if block_start >= useful {
                0u8
            } else {
                let bits_left = useful - block_start;
                let processed = bits_left.div_ceil(B_MED_WINDOW);
                processed.min(N_B_MED_MAX) as u8
            }
        })
        .collect();
    (within_outer_mask, counts)
}

/// Packed-input variant of [`round1_shift_reduce_extract_c`]. **Parallel by
/// default** via rayon — the outer x_hi loop is distributed across workers,
/// each with its own scratch + local accumulator. Reduction is a per-lane
/// F128 XOR across workers (commutative + associative).
///
/// To run single-threaded for debugging, set `RAYON_NUM_THREADS=1`.
pub fn round1_shift_reduce_extract_c_packed(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r: &[F128],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F128>, Vec<F128>) {
    round1_shift_reduce_extract_c_packed_padded(
        a_packed,
        b_packed,
        c_packed,
        m,
        k_skip,
        r,
        inv_table,
        &PaddingSpec::dense(m),
    )
}

/// Padding-aware variant of [`round1_shift_reduce_extract_c_packed`]. Skips
/// 512-bit b_med sub-windows that fall entirely in the zero padding of every
/// witness block per `padding`. Output is byte-identical to the dense path
/// when the padding bits are honestly zero.
pub fn round1_shift_reduce_extract_c_packed_padded(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r: &[F128],
    inv_table: &InvNttTableByteSingleGf8,
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>) {
    use rayon::prelude::*;

    assert_eq!(k_skip, K_SKIP, "optimized variant is k_skip=6 only");
    assert!(
        m >= k_skip + N_INNER,
        "m must be ≥ k_skip + N_INNER ({}) for the shift_reduce optimization",
        k_skip + N_INNER
    );
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r.len(), m);
    assert_eq!(inv_table.k, k_skip);

    let eq = SplitEqGhash::new(&r[k_skip + N_INNER..]);
    let big_lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    let n_lo_and_inner = eq.n_lo + N_INNER;

    let d_inv_val = d_inv();
    let eq_lo_scaled: Vec<F128> = eq.lo.iter().map(|v| *v * d_inv_val).collect();
    let convert = convert_table();
    let eq_hi = &eq.hi;

    let (within_outer_mask, b_med_counts) = build_b_med_counts(padding);

    // Parallel fold: each worker accumulates a subset of x_hi values into its
    // own WorkerState. Reduce step combines the per-worker `local_res_*` by
    // per-lane F128 XOR.
    let (res_ab, res_c_s) = (0..hi_size)
        .into_par_iter()
        .fold(WorkerState::new, |mut state, x_hi| {
            let eq_hi_val = eq_hi[x_hi];
            process_one_x_hi(
                x_hi,
                big_lo_size,
                n_lo_and_inner,
                within_outer_mask,
                &b_med_counts,
                a_packed,
                b_packed,
                c_packed,
                inv_table,
                &eq_lo_scaled,
                eq_hi_val,
                convert,
                &mut state,
            );
            state
        })
        .map(|s| (s.local_res_ab, s.local_res_c_s))
        .reduce(
            || ([F128::ZERO; ELL], [F128::ZERO; ELL]),
            |(mut ab1, mut c1), (ab2, c2)| {
                for i in 0..ELL {
                    ab1[i] += ab2[i];
                    c1[i] += c2[i];
                }
                (ab1, c1)
            },
        );

    let res_c_lifted = ntt_extend_f128_vec_ghash(&res_c_s, inv_table);
    (res_ab.to_vec(), res_c_lifted)
}

/// Same as [`round1_shift_reduce_extract_c_packed_padded`] but **also returns
/// `s_hat_v_c`** — the length-128 vector ring-switch would otherwise produce
/// via `fold_1b_rows` for the c-claim's PCS opening at suffix `r[k_skip+1..m]`.
///
/// The wire output `(res_ab, res_c_lifted)` is byte-identical to
/// [`round1_shift_reduce_extract_c_packed_padded`] — same eq weights, same
/// `C_s` drop convention. `s_hat_v_c` is returned in **canonical form**
/// (matches `fold_1b_rows`), with the residual `C_2` and `α⁻¹` scaling
/// applied internally so the caller can feed it straight into
/// `pcs::ring_switch::prove_batched_padded_with_precomputed`.
///
/// Cost vs the original: per chunk-lane-`b_med`, +1 `vld1q_u8` + +1 `veorq_u8`
/// (the bank-split convert lookup). bit_transpose, shift_reduce, eq folds
/// are unchanged. See module-level docs for the F_2-linearity argument that
/// makes `s_hat_v_c[(λ, 0)] + s_hat_v_c[(λ, 1)] · α == res_c_s_opt[λ]`.
pub fn round1_shift_reduce_extract_c_packed_padded_with_s_hat_v(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r: &[F128],
    inv_table: &InvNttTableByteSingleGf8,
    padding: &PaddingSpec,
) -> (Vec<F128>, Vec<F128>, Vec<F128>) {
    use rayon::prelude::*;

    assert_eq!(k_skip, K_SKIP, "optimized variant is k_skip=6 only");
    assert!(
        m >= k_skip + N_INNER,
        "m must be ≥ k_skip + N_INNER ({}) for the shift_reduce optimization",
        k_skip + N_INNER
    );
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r.len(), m);
    assert_eq!(inv_table.k, k_skip);

    let eq = SplitEqGhash::new(&r[k_skip + N_INNER..]);
    let big_lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    let n_lo_and_inner = eq.n_lo + N_INNER;

    let d_inv_val = d_inv();
    let eq_lo_scaled: Vec<F128> = eq.lo.iter().map(|v| *v * d_inv_val).collect();
    let convert = convert_table();
    let eq_hi = &eq.hi;

    let (within_outer_mask, b_med_counts) = build_b_med_counts(padding);

    let (res_ab, res_c_s_0, res_c_s_1) = (0..hi_size)
        .into_par_iter()
        .fold(WorkerStateWithSHatV::new, |mut state, x_hi| {
            let eq_hi_val = eq_hi[x_hi];
            process_one_x_hi_with_s_hat_v(
                x_hi,
                big_lo_size,
                n_lo_and_inner,
                within_outer_mask,
                &b_med_counts,
                a_packed,
                b_packed,
                c_packed,
                inv_table,
                &eq_lo_scaled,
                eq_hi_val,
                convert,
                &mut state,
            );
            state
        })
        .map(|s| (s.local_res_ab, s.local_res_c_s_0, s.local_res_c_s_1))
        .reduce(
            || ([F128::ZERO; ELL], [F128::ZERO; ELL], [F128::ZERO; ELL]),
            |(mut ab1, mut c0_1, mut c1_1), (ab2, c0_2, c1_2)| {
                for i in 0..ELL {
                    ab1[i] += ab2[i];
                    c0_1[i] += c0_2[i];
                    c1_1[i] += c1_2[i];
                }
                (ab1, c0_1, c1_1)
            },
        );

    // Wire output: bank_0 + bank_1 reconstructs the original `res_c_s` (by
    // F_2-linearity of φ_8 over the masked-byte sum).
    let mut res_c_s_combined = [F128::ZERO; ELL];
    for i in 0..ELL {
        res_c_s_combined[i] = res_c_s_0[i] + res_c_s_1[i];
    }
    let res_c_lifted = ntt_extend_f128_vec_ghash(&res_c_s_combined, inv_table);

    // s_hat_v_c canonical form: apply residual C_2 (small-eq constant for
    // r[k_skip+1..k_skip+3]) and α⁻¹ (strips bank 1's extra α factor).
    let c_2 = c_2_small_f128();
    let alpha_inv = alpha_inv_f128();
    let c_2_alpha_inv = c_2 * alpha_inv;
    let mut s_hat_v_c = vec![F128::ZERO; 2 * ELL];
    for lane in 0..ELL {
        s_hat_v_c[lane] = c_2 * res_c_s_0[lane];
        s_hat_v_c[ELL + lane] = c_2_alpha_inv * res_c_s_1[lane];
    }

    (res_ab.to_vec(), res_c_lifted, s_hat_v_c)
}

/// Serial reference — same I/O as [`round1_shift_reduce_extract_c_packed`],
/// no rayon. Kept under `#[cfg(test)]` as the cross-check oracle for the
/// parallel version: future "optimizations" to the parallel path must still
/// produce identical output to this straight-line loop.
#[cfg(test)]
fn round1_shift_reduce_extract_c_packed_serial(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    k_skip: usize,
    r: &[F128],
    inv_table: &InvNttTableByteSingleGf8,
) -> (Vec<F128>, Vec<F128>) {
    assert_eq!(k_skip, K_SKIP);
    assert!(m >= k_skip + N_INNER);
    let total_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), total_bytes);
    assert_eq!(b_packed.len(), total_bytes);
    assert_eq!(c_packed.len(), total_bytes);
    assert_eq!(r.len(), m);
    assert_eq!(inv_table.k, k_skip);

    let eq = SplitEqGhash::new(&r[k_skip + N_INNER..]);
    let big_lo_size = 1usize << eq.n_lo;
    let hi_size = 1usize << eq.n_hi;
    let n_lo_and_inner = eq.n_lo + N_INNER;

    let d_inv_val = d_inv();
    let eq_lo_scaled: Vec<F128> = eq.lo.iter().map(|v| *v * d_inv_val).collect();
    let convert = convert_table();

    let (within_outer_mask, b_med_counts) = build_b_med_counts(&PaddingSpec::dense(m));

    let mut state = WorkerState::new();
    for x_hi in 0..hi_size {
        process_one_x_hi(
            x_hi,
            big_lo_size,
            n_lo_and_inner,
            within_outer_mask,
            &b_med_counts,
            a_packed,
            b_packed,
            c_packed,
            inv_table,
            &eq_lo_scaled,
            eq.hi[x_hi],
            convert,
            &mut state,
        );
    }

    let res_c_lifted = ntt_extend_f128_vec_ghash(&state.local_res_c_s, inv_table);
    (state.local_res_ab.to_vec(), res_c_lifted)
}
