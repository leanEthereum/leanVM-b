// CREDIT: https://github.com/binius-zk/binius64, Apache-2.0.
//! `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`,
//! `R64 = 0x1B = x^4 + x^3 + x + 1`, and `ord(x) = 2^64 - 1`.
//! One multiplication = 1 product PMULL + 1
//! fold PMULL + a ≤4-bit overflow tail; the product and fold never leave
//! the NEON register file.
//!
//! This is the base field for [`super::gf2_64x3`] (F192's tower base); the
//! reduction helper [`super::gf2_64x3::base_reduce_128`] is shared.

use core::ops::{Add, AddAssign, Mul, MulAssign};

use serde::{Deserialize, Serialize};

#[cfg(target_arch = "aarch64")]
use super::gf2_64x3::R64;
use super::gf2_64x3::base_reduce_128;

/// A GF(2^64) element; bit i = coefficient of x^i.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(transparent)]
pub struct F64(pub u64);

impl F64 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    /// `x`, with `ord(x) = 2^64 - 1`.
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

    /// Multiplicative inverse: x^(2^64 − 2). `ZERO.inv() == ZERO`.
    ///
    /// Itoh-Tsujii: x^(2^64−2) = (x^(2^63−1))², and x^(2^k−1) is built by an
    /// addition chain on `k`. Doubling `k` costs `k` squarings and one multiply,
    /// incrementing it one of each, so the chain 1,2,3,6,7,14,15,30,31,62,63
    /// spends 63 squarings and 10 multiplies where the plain Fermat ladder
    /// spends 63 and 62.
    pub fn inv(self) -> Self {
        let sq = |mut v: Self, n: u32| {
            for _ in 0..n {
                v = v.square();
            }
            v
        };
        let t1 = self; // x^(2^1−1)
        let t2 = sq(t1, 1) * t1;
        let t3 = sq(t2, 1) * t1;
        let t6 = sq(t3, 3) * t3;
        let t7 = sq(t6, 1) * t1;
        let t14 = sq(t7, 7) * t7;
        let t15 = sq(t14, 1) * t1;
        let t30 = sq(t15, 15) * t15;
        let t31 = sq(t30, 1) * t1;
        let t62 = sq(t31, 31) * t31;
        let t63 = sq(t62, 1) * t1;
        sq(t63, 1)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for F64 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
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
            unsafe { aarch64::mul_shift_tail(self, rhs) }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe { x86_64::mul(self, rhs) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
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
    /// returns `{reduce(p0), reduce(p1)}`. One PMULL-by-0x1B per product folds
    /// the high half, and a second PMULL folds that fold's ≤4-bit second-order
    /// overflow (4 PMULL total, minimal non-PMULL op count). Fastest pair
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
            vtrn1q_u64(veorq_u64(veorq_u64(p0, t0), u0), veorq_u64(veorq_u64(p1, t1), u1))
        }
    }

    /// The default `Mul` kernel on aarch64. 3-PMULL multiply: product, then two
    /// PMULL-by-0x1B folds, the second taking the first's ≤4-bit overflow
    /// exactly (`ov·0x1B` fits in 8 bits). The shift-XOR tail this replaced was
    /// chosen on the premise that the vector pipes were PMULL-saturated and the
    /// scalar ports free; PMULL retires at about the rate `eor` does here, so
    /// the extra product costs less than the lane extraction it removes.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`pmull`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_shift_tail(a: F64, b: F64) -> F64 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let r = vdupq_n_u64(R64);
            let p = pmull(a.0, b.0);
            let t = pmull_hi(p, r);
            let u = pmull_hi(t, r);
            F64(vgetq_lane_u64::<0>(veorq_u64(veorq_u64(p, t), u)))
        }
    }
}

/// x86-64 `pclmulqdq` path, the twin of [`aarch64`] for AMD/Intel. GF(2^64)
/// multiply is one CLMUL product plus a two-CLMUL fold by `R64` (= x^64 mod P),
/// the same reduction as [`base_reduce_128`].
#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub mod x86_64 {
    use super::F64;
    use crate::field::gf2_64x3::R64;
    use core::arch::x86_64::*;

    /// 64×64 carry-less product as a 128-bit vector `{lo, hi}`.
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; only call where it is
    /// statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn clmul(a: u64, b: u64) -> __m128i {
        _mm_clmulepi64_si128::<0x00>(_mm_set_epi64x(0, a as i64), _mm_set_epi64x(0, b as i64))
    }

    /// Reduce a 128-bit carry-less product `{lo, hi}` into GF(2^64): fold the
    /// high word by `R64` (= x^64 mod P), then fold the ≤5-bit second-order
    /// overflow once more. Two CLMUL; the exact residue of [`base_reduce_128`].
    ///
    /// Credit: binius64 <https://github.com/binius-zk/binius64>
    /// (`crates/arith-bench/src/monbijou/clmul.rs::reduce`), whose Monbijou
    /// field is this same GF(2^64): a `<0x01>` CLMUL fold by `0x1B` applied
    /// twice, XOR-ing the low halves.
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; see [`clmul`].
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn reduce(p: __m128i) -> u64 {
        let r = _mm_set_epi64x(0, R64 as i64);
        let t = _mm_clmulepi64_si128::<0x01>(p, r); // clmul(p.hi, R64), ≤68 bits
        let u = _mm_clmulepi64_si128::<0x01>(t, r); // clmul(t.hi, R64), ≤9 bits
        _mm_cvtsi128_si64(_mm_xor_si128(_mm_xor_si128(p, t), u)) as u64
    }

    /// One GF(2^64) multiply: product + reduction (3 CLMUL).
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; see [`clmul`].
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn mul(a: F64, b: F64) -> F64 {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe { F64(reduce(clmul(a.0, b.0))) }
    }
}

pub mod software {
    use super::{F64, base_reduce_128};
    use crate::field::gf2_64x3::clmul64;

    pub fn mul(a: F64, b: F64) -> F64 {
        let (lo, hi) = clmul64(a.0, b.0);
        F64(base_reduce_128(lo, hi))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

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
    fn optimized_mul_matches_software() {
        let mut rng = Rng::new(1);
        for _ in 0..10_000 {
            let (a, b) = (F64(rng.next_u64()), F64(rng.next_u64()));
            assert_eq!(a * b, software::mul(a, b));
        }
    }

    /// Every NEON mul variant agrees with the software reference.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn neon_variants_match_software() {
        let mut rng = Rng::new(5);
        for _ in 0..10_000 {
            let (a, b) = (F64(rng.next_u64()), F64(rng.next_u64()));
            let want = software::mul(a, b);
            // SAFETY: aes target feature is enabled at compile time.
            unsafe {
                assert_eq!(aarch64::mul_shift_tail(a, b), want);
            }
        }
    }

    #[test]
    fn inverses() {
        let mut rng = Rng::new(2);
        for _ in 0..200 {
            let a = F64(rng.next_u64());
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
