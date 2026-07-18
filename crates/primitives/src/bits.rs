// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Small bit-manipulation primitives shared across modules.

/// Hacker's Delight (Sec. 7-3) 8×8 bit-matrix transpose stored in a `u64`.
///
/// The input holds 8 bytes representing 8 rows of 8 bits each; the output holds
/// the transposed matrix (bit `r·8 + c` of input → bit `c·8 + r` of output).
///
/// Used by the PCS ring-switch `fold_1b` kernels (`pcs::ring_switch`).
#[inline(always)]
pub fn transpose_8x8_bits(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AAu64;
    x = x ^ t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCCu64;
    x = x ^ t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0u64;
    x = x ^ t ^ (t << 28);
    x
}

/// Bit-transpose 8 little-endian `u64` lanes (the 64-byte block they form) into
/// a 64-byte output stripe.
///
/// The 8 LE u64s viewed as 64 bytes are exactly the input shape of the NEON
/// [`bit_transpose_64bytes`] kernel (input byte `r·8 + c` = byte `c` of lane
/// `r`; output byte `c·8 + t` bit `r` = that byte's bit `t`), so this delegates
/// to it — ~5× fewer ops than the scalar per-column loop. Used by the
/// lincheck byte-stripe builder (`flock::binary_witness`).
#[inline(always)]
pub fn transpose_8_u64s_to_64_bytes(lanes: &[u64; 8], out: &mut [u8]) {
    debug_assert_eq!(out.len(), 64);
    // SAFETY: [u64; 8] is 64 bytes with no padding; u8 has weaker alignment.
    let input: &[u8; 64] = unsafe { &*(lanes.as_ptr() as *const [u8; 64]) };
    let out64: &mut [u8; 64] = out.try_into().expect("64-byte stripe slice");
    bit_transpose_64bytes(input, out64);
}

// 64-byte bit transpose (bit (r,c) -> byte c·8 + t, bit r).
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

/// Portable u64 64-byte bit-transpose (Hacker's Delight `transpose8`, the
/// same 3-round masked bit-swap the NEON path uses, on scalar registers).
///
/// Per byte-chunk `b`: gather the 8 strided bytes `input[x*8 + b]` into a
/// u64 (little-endian, byte x = lane x), transpose the 8×8 bit matrix via
/// swaps at distances 7/14/28, and store the result contiguously at
/// `output[b*8..]`. Bit `(x, t)` of the gathered word lands at `(t, x)` —
/// exactly `output[b*8 + t] bit x = input[x*8 + b] bit t`.
#[cfg(not(target_arch = "aarch64"))]
#[cfg_attr(all(target_arch = "x86_64", target_feature = "avx512vbmi"), allow(dead_code))]
#[inline]
fn bit_transpose_64bytes_u64(input: &[u8; 64], output: &mut [u8; 64]) {
    for b_chunk in 0..8 {
        let mut y = u64::from_le_bytes([
            input[b_chunk],
            input[8 + b_chunk],
            input[16 + b_chunk],
            input[24 + b_chunk],
            input[32 + b_chunk],
            input[40 + b_chunk],
            input[48 + b_chunk],
            input[56 + b_chunk],
        ]);
        let t = (y ^ (y >> 7)) & 0x00AA00AA00AA00AA;
        y ^= t ^ (t << 7);
        let t = (y ^ (y >> 14)) & 0x0000CCCC0000CCCC;
        y ^= t ^ (t << 14);
        let t = (y ^ (y >> 28)) & 0x00000000F0F0F0F0;
        y ^= t ^ (t << 28);
        output[b_chunk * 8..b_chunk * 8 + 8].copy_from_slice(&y.to_le_bytes());
    }
}

/// AVX-512VBMI 64-byte bit-transpose. `vpermb` first gathers the eight
/// strided byte-columns into eight `u64` lanes; three lane-wise masked-swap
/// rounds then transpose each gathered 8x8 bit matrix in parallel.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi"))]
#[target_feature(enable = "avx512vbmi", enable = "avx512f")]
unsafe fn bit_transpose_64bytes_avx512vbmi(input: &[u8; 64], output: &mut [u8; 64]) {
    use core::arch::x86_64::*;

    // Each consecutive eight indices select byte-column b from input rows
    // x=0..7, producing one gathered u64 lane per column.
    const IDX: [u8; 64] = [
        0, 8, 16, 24, 32, 40, 48, 56, 1, 9, 17, 25, 33, 41, 49, 57, 2, 10, 18, 26, 34, 42, 50, 58, 3, 11, 19, 27, 35,
        43, 51, 59, 4, 12, 20, 28, 36, 44, 52, 60, 5, 13, 21, 29, 37, 45, 53, 61, 6, 14, 22, 30, 38, 46, 54, 62, 7, 15,
        23, 31, 39, 47, 55, 63,
    ];

    unsafe {
        let bytes = _mm512_loadu_si512(input.as_ptr().cast());
        let indices = _mm512_loadu_si512(IDX.as_ptr().cast());
        let mut y = _mm512_permutexvar_epi8(indices, bytes);

        let mask1 = _mm512_set1_epi64(0x00AA00AA00AA00AA);
        let t = _mm512_and_si512(_mm512_xor_si512(y, _mm512_srli_epi64::<7>(y)), mask1);
        y = _mm512_xor_si512(y, _mm512_xor_si512(t, _mm512_slli_epi64::<7>(t)));

        let mask2 = _mm512_set1_epi64(0x0000CCCC0000CCCC);
        let t = _mm512_and_si512(_mm512_xor_si512(y, _mm512_srli_epi64::<14>(y)), mask2);
        y = _mm512_xor_si512(y, _mm512_xor_si512(t, _mm512_slli_epi64::<14>(t)));

        let mask3 = _mm512_set1_epi64(0x00000000F0F0F0F0);
        let t = _mm512_and_si512(_mm512_xor_si512(y, _mm512_srli_epi64::<28>(y)), mask3);
        y = _mm512_xor_si512(y, _mm512_xor_si512(t, _mm512_slli_epi64::<28>(t)));

        _mm512_storeu_si512(output.as_mut_ptr().cast(), y);
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
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi"))]
    // SAFETY: AVX-512VBMI is statically enabled at compile time.
    unsafe {
        bit_transpose_64bytes_avx512vbmi(input, output)
    }
    #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "avx512vbmi"))))]
    bit_transpose_64bytes_u64(input, output);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// splitmix64 test PRNG (same helper as the former_field_module/gf2_8 test modules).
    #[cfg(target_arch = "aarch64")]
    struct Rng(u64);
    #[cfg(target_arch = "aarch64")]
    impl Rng {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
    }

    /// Scalar reference for [`transpose_8_u64s_to_64_bytes`] — test oracle only.
    #[allow(clippy::erasing_op, clippy::identity_op)]
    fn transpose_8_u64s_to_64_bytes_scalar(lanes: &[u64; 8], out: &mut [u8]) {
        debug_assert_eq!(out.len(), 64);
        for c in 0..8 {
            let shift = c * 8;
            let mut packed: u64 = 0;
            packed |= ((lanes[0] >> shift) & 0xFF) << (0 * 8);
            packed |= ((lanes[1] >> shift) & 0xFF) << (1 * 8);
            packed |= ((lanes[2] >> shift) & 0xFF) << (2 * 8);
            packed |= ((lanes[3] >> shift) & 0xFF) << (3 * 8);
            packed |= ((lanes[4] >> shift) & 0xFF) << (4 * 8);
            packed |= ((lanes[5] >> shift) & 0xFF) << (5 * 8);
            packed |= ((lanes[6] >> shift) & 0xFF) << (6 * 8);
            packed |= ((lanes[7] >> shift) & 0xFF) << (7 * 8);
            let transposed = transpose_8x8_bits(packed);
            out[c * 8..c * 8 + 8].copy_from_slice(&transposed.to_le_bytes());
        }
    }

    /// The NEON-delegating transpose must match the scalar per-column oracle
    /// bit-for-bit on varied inputs.
    #[test]
    fn transpose_8_u64s_matches_scalar() {
        let mut state = 0x1234_5678_9ABC_DEF0u64;
        let mut next = || {
            state = state.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        };
        for _ in 0..100 {
            let lanes: [u64; 8] = std::array::from_fn(|_| next());
            let mut fast = [0u8; 64];
            let mut oracle = [0u8; 64];
            transpose_8_u64s_to_64_bytes(&lanes, &mut fast);
            transpose_8_u64s_to_64_bytes_scalar(&lanes, &mut oracle);
            assert_eq!(fast, oracle);
        }
        // Edge patterns.
        for lanes in [[0u64; 8], [u64::MAX; 8], std::array::from_fn(|i| 1u64 << i)] {
            let mut fast = [0u8; 64];
            let mut oracle = [0u8; 64];
            transpose_8_u64s_to_64_bytes(&lanes, &mut fast);
            transpose_8_u64s_to_64_bytes_scalar(&lanes, &mut oracle);
            assert_eq!(fast, oracle, "lanes={lanes:?}");
        }
    }

    /// Transposing twice is the identity.
    #[test]
    fn transpose_is_involution() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..256 {
            state = state.wrapping_mul(0x2545_F491_4F6C_DD1D).rotate_left(31);
            assert_eq!(transpose_8x8_bits(transpose_8x8_bits(state)), state);
        }
    }

    /// Cross-check against a naive bit-by-bit transpose of the 8×8 matrix.
    #[test]
    fn matches_naive() {
        let mut state = 0x1234_5678_9ABC_DEF0u64;
        for _ in 0..256 {
            state = state.wrapping_mul(0x2545_F491_4F6C_DD1D).rotate_left(17);
            let got = transpose_8x8_bits(state);
            let mut want = 0u64;
            for r in 0..8 {
                for c in 0..8 {
                    if (state >> (r * 8 + c)) & 1 == 1 {
                        want |= 1u64 << (c * 8 + r);
                    }
                }
            }
            assert_eq!(got, want, "input={state:016x}");
        }
    }
    #[cfg(not(target_arch = "aarch64"))]
    #[test]
    fn bit_transpose_u64_matches_scalar() {
        let mut seed = 0x12345678u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 33) as u8
        };
        for _ in 0..64 {
            let mut input = [0u8; 64];
            input.iter_mut().for_each(|b| *b = next());
            let mut out_scalar = [0u8; 64];
            let mut out_u64 = [0u8; 64];
            bit_transpose_64bytes_scalar(&input, &mut out_scalar);
            bit_transpose_64bytes_u64(&input, &mut out_u64);
            assert_eq!(out_scalar, out_u64);
        }
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "avx512vbmi"))]
    #[test]
    fn avx512vbmi_bit_transpose_matches_scalar() {
        let mut seed = 0xB17_BB17u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 33) as u8
        };
        for _ in 0..64 {
            let mut input = [0u8; 64];
            input.iter_mut().for_each(|b| *b = next());
            let mut out_scalar = [0u8; 64];
            let mut out_avx512vbmi = [0u8; 64];
            bit_transpose_64bytes_scalar(&input, &mut out_scalar);
            // SAFETY: this test is compiled only when AVX-512VBMI is enabled.
            unsafe { bit_transpose_64bytes_avx512vbmi(&input, &mut out_avx512vbmi) };
            assert_eq!(out_scalar, out_avx512vbmi, "bit_transpose disagreement");
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn neon_bit_transpose_matches_scalar() {
        let mut rng = Rng::new(0xB17_BB17);
        for _ in 0..64 {
            let mut input = [0u8; 64];
            for byte in input.iter_mut() {
                *byte = (rng.next_u64() & 0xff) as u8;
            }
            let mut out_scalar = [0u8; 64];
            let mut out_neon = [0u8; 64];
            bit_transpose_64bytes_scalar(&input, &mut out_scalar);
            // SAFETY: on aarch64.
            unsafe { bit_transpose_64bytes_neon(&input, &mut out_neon) };
            assert_eq!(out_scalar, out_neon, "bit_transpose disagreement");
        }
    }
}
