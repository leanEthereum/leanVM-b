//! GF(2^64), first-class: the data/commitment field of the 64-bit transition.
//!
//! K = F_2[x]/(x^64 + x^4 + x^3 + x + 1), the standard low-weight irreducible
//! pentanomial; fold constant `R64 = 0x1B`. `x` is primitive (order exactly
//! 2^64 − 1; pinned by a test). One multiplication = 1 product PMULL + 1
//! fold PMULL + a ≤4-bit overflow tail; the product and fold never leave
//! the NEON register file.
//!
//! This is the same base field as [`super::gf2_64x3`] (F192's tower base) and
//! [`super::tower_f128`] (F128T's tower base); the reduction helper
//! [`super::gf2_64x3::base_reduce_128`] is shared.

use core::ops::{Add, AddAssign, Mul, MulAssign};

use serde::{Deserialize, Serialize};

use super::gf2_64x3::{R64, base_reduce_128};

/// A GF(2^64) element; bit i = coefficient of x^i.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(transparent)]
pub struct F64(pub u64);

impl F64 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    /// The generator x — primitive, order 2^64 − 1.
    pub const G: Self = Self(2);

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Squaring (cross terms vanish in char 2): same cost as mul here (the
    /// PMULL already squares), kept for API symmetry with the other fields.
    #[inline]
    pub fn square(self) -> Self {
        self * self
    }

    /// Multiplicative inverse via Fermat: x^(2^64 − 2). `ZERO.inv() == ZERO`.
    pub fn inv(self) -> Self {
        let mut cur = self.square();
        let mut r = cur;
        for _ in 2..64 {
            cur = cur.square();
            r *= cur;
        }
        r
    }
}

impl Add for F64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

impl AddAssign for F64 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0;
    }
}

impl Mul for F64 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_neon(self, rhs) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            software::mul(self, rhs)
        }
    }
}

impl MulAssign for F64 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{F64, R64};
    use core::arch::aarch64::*;
    use core::mem::transmute;

    const fn clmul8(a: u64, b: u64) -> u64 {
        let mut r = 0u64;
        let mut i = 0;
        while i < 8 {
            if (a >> i) & 1 == 1 {
                r ^= b << i;
            }
            i += 1;
        }
        r
    }

    /// `FOLD_TBL[ov] = clmul(ov, 0x1B)` for the ≤4-bit second-order overflow
    /// `ov`: the exact final fold (fits in 8 bits), as a 16-entry TBL table.
    /// One TBL folds both lanes of a pair reduction at once.
    const FOLD_TBL: [u8; 16] = {
        let mut t = [0u8; 16];
        let mut n = 0;
        while n < 16 {
            t[n] = clmul8(n as u64, R64) as u8;
            n += 1;
        }
        t
    };

    /// 64x64 carry-less product as a 128-bit NEON vector.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn pmull(a: u64, b: u64) -> uint64x2_t {
        // SAFETY: u128 and uint64x2_t are both 128-bit values.
        unsafe { transmute::<u128, uint64x2_t>(vmull_p64(a, b)) }
    }

    /// Carry-less product of the two *high* lanes: PMULL2 on the register
    /// pair, no lane extraction (the lane-crossing-free way to fold a
    /// product's high half).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn pmull_hi(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        // SAFETY: bit-level reinterprets between 128-bit vector types.
        unsafe {
            transmute::<u128, uint64x2_t>(vmull_high_p64(
                transmute::<uint64x2_t, poly64x2_t>(a),
                transmute::<uint64x2_t, poly64x2_t>(b),
            ))
        }
    }

    /// Reduce two 128-bit carry-less products into GF(2^64) as a lane pair:
    /// returns `{reduce(p0), reduce(p1)}`. One PMULL-by-0x1B per product
    /// folds the high half; the two ≤4-bit second-order overflows are folded
    /// together by one vectorized shift-XOR (exact: ov·0x1B fits in 8 bits).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_pair(p0: uint64x2_t, p1: uint64x2_t) -> uint64x2_t {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let t0 = pmull_hi(p0, r);
            let t1 = pmull_hi(p1, r);
            let lo = vtrn1q_u64(veorq_u64(p0, t0), veorq_u64(p1, t1));
            let ov = vtrn2q_u64(t0, t1);
            let f = veorq_u64(
                veorq_u64(ov, vshlq_n_u64::<1>(ov)),
                veorq_u64(vshlq_n_u64::<3>(ov), vshlq_n_u64::<4>(ov)),
            );
            veorq_u64(lo, f)
        }
    }

    /// Like [`reduce_pair`] but the second-order overflows also fold by
    /// PMULL (4 PMULL total, minimal non-PMULL op count). Fastest pair
    /// reduction in memory-resident loops (the NTT butterfly shape) on
    /// M-series, where PMULL throughput is plentiful.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_pair_pmull4(p0: uint64x2_t, p1: uint64x2_t) -> uint64x2_t {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let t0 = pmull_hi(p0, r);
            let t1 = pmull_hi(p1, r);
            // clmul(t.hi, 0x1B) fits in 8 bits (high lane 0): the exact fold
            // of the ≤4-bit overflow, ready to XOR into lane 0.
            let u0 = pmull_hi(t0, r);
            let u1 = pmull_hi(t1, r);
            vtrn1q_u64(
                veorq_u64(veorq_u64(p0, t0), u0),
                veorq_u64(veorq_u64(p1, t1), u1),
            )
        }
    }

    /// Like [`reduce_pair`] but the two ≤4-bit second-order overflows fold
    /// through one 16-byte TBL lookup ([`FOLD_TBL`]): the overflow nibbles
    /// sit in bytes 0 and 8 of the transposed high words and the table maps
    /// each to its exact 8-bit fold in a single instruction. Shortest
    /// dependency chain of the three pair reductions.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_pair_tbl(p0: uint64x2_t, p1: uint64x2_t) -> uint64x2_t {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let t0 = pmull_hi(p0, r);
            let t1 = pmull_hi(p1, r);
            let lo = vtrn1q_u64(veorq_u64(p0, t0), veorq_u64(p1, t1));
            // ov = {t0.hi, t1.hi}, each ≤ 4 bits: byte 0 and byte 8 index the
            // table; all other bytes are zero and map to zero.
            let ov = vtrn2q_u64(t0, t1);
            let table: uint8x16_t = transmute(FOLD_TBL);
            let f = vreinterpretq_u64_u8(vqtbl1q_u8(table, vreinterpretq_u8_u64(ov)));
            veorq_u64(lo, f)
        }
    }

    /// 3-PMULL fully vector-resident multiply: product, PMULL-by-0x1B fold of
    /// the high half, second PMULL fold of the ≤4-bit overflow. Benchmark
    /// alternate: best serial-chain latency by a hair, but the extra PMULL
    /// costs throughput next to [`mul_shift_tail`].
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_pmull_fold(a: F64, b: F64) -> F64 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let p = pmull(a.0, b.0);
            let t = pmull_hi(p, r); // clmul(p.hi, 0x1B), ≤68 bits
            let u = pmull_hi(t, r); // clmul(t.hi, 0x1B), ≤8 bits, high lane 0
            F64(vgetq_lane_u64::<0>(veorq_u64(veorq_u64(p, t), u)))
        }
    }

    /// 2-PMULL multiply: product, PMULL-by-0x1B fold, and a shift-XOR fold of
    /// the ≤4-bit overflow (exact: ov·0x1B fits in 8 bits). LLVM lowers the
    /// tail onto the scalar ports, which run free next to the PMULL-saturated
    /// vector pipes: best throughput of the variants tried.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_shift_tail(a: F64, b: F64) -> F64 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p = pmull(a.0, b.0);
            let t = pmull_hi(p, vdupq_n_u64(R64));
            let ov = vdupq_laneq_u64::<1>(t);
            let f = veorq_u64(
                veorq_u64(ov, vshlq_n_u64::<1>(ov)),
                veorq_u64(vshlq_n_u64::<3>(ov), vshlq_n_u64::<4>(ov)),
            );
            F64(vgetq_lane_u64::<0>(veorq_u64(veorq_u64(p, t), f)))
        }
    }

    /// Default multiply kernel: [`mul_shift_tail`] (best throughput in both
    /// register-chain and array loops; within 3% of the best latency).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_neon(a: F64, b: F64) -> F64 {
        // SAFETY: function carries the aes target feature.
        unsafe { mul_shift_tail(a, b) }
    }
}

pub mod software {
    use super::{F64, base_reduce_128};
    use crate::field::gf2_128::software::clmul64;

    pub fn mul(a: F64, b: F64) -> F64 {
        let (lo, hi) = clmul64(a.0, b.0);
        F64(base_reduce_128(lo, hi))
    }
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

    /// Independent Python reference vectors: (a, b, a·b).
    const VECTORS: [(u64, u64, u64); 3] = [
        (0x01090913877ed8ed, 0x66ab35ac2768468f, 0x50c4519dc383744a),
        (0xa7715ae18f12a3b5, 0x05743059f43fa4f5, 0xeb64cd9cd9cda6df),
        (0xbd3efb4705e79ddd, 0x3aff618604de4ae0, 0xc3d7a95fa9cb59bb),
    ];

    #[test]
    fn python_vectors() {
        for (a, b, c) in VECTORS {
            assert_eq!(F64(a) * F64(b), F64(c));
            assert_eq!(software::mul(F64(a), F64(b)), F64(c));
        }
    }

    #[test]
    fn neon_matches_software_and_axioms() {
        let mut s = 1u64;
        for _ in 0..10_000 {
            let (a, b, c) = (F64(splitmix64(&mut s)), F64(splitmix64(&mut s)), F64(splitmix64(&mut s)));
            assert_eq!(a * b, software::mul(a, b));
            assert_eq!(a * b, b * a);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
        }
    }

    /// Every NEON mul variant agrees with the software reference.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn neon_variants_match_software() {
        let mut s = 5u64;
        for _ in 0..10_000 {
            let (a, b) = (F64(splitmix64(&mut s)), F64(splitmix64(&mut s)));
            let want = software::mul(a, b);
            // SAFETY: aes target feature is enabled at compile time.
            unsafe {
                assert_eq!(aarch64::mul_pmull_fold(a, b), want);
                assert_eq!(aarch64::mul_shift_tail(a, b), want);
            }
        }
    }

    #[test]
    fn inv_and_identities() {
        let mut s = 2u64;
        for _ in 0..200 {
            let a = F64(splitmix64(&mut s));
            assert_eq!(a * F64::ONE, a);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F64::ONE);
            }
        }
        assert_eq!(F64::ZERO.inv(), F64::ZERO);
    }

    /// x is primitive: x^((2^64−1)/q) ≠ 1 for every prime q | 2^64 − 1.
    #[test]
    fn x_is_primitive() {
        fn pow(mut base: F64, mut e: u128) -> F64 {
            let mut r = F64::ONE;
            while e > 0 {
                if e & 1 == 1 {
                    r *= base;
                }
                base = base.square();
                e >>= 1;
            }
            r
        }
        let n: u128 = (1 << 64) - 1;
        for q in [3u128, 5, 17, 257, 641, 65537, 6700417] {
            assert_ne!(pow(F64::G, n / q), F64::ONE, "x^((2^64-1)/{q}) == 1");
        }
    }
}
