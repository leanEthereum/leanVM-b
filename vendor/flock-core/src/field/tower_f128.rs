//! GF(2^128) as a degree-2 tower over GF(2^64): the challenge field of the
//! 64-bit transition.
//!
//! E = K[y]/(y^2 + y + c) with K = GF(2^64) ([`super::gf2_64::F64`]) and
//! c = x^61. By Artin--Schreier, y^2 + y + c is irreducible over K exactly
//! when Tr_{K/F_2}(c) = 1, and x^61 is the least monomial of trace 1 (a test
//! pins this). Elements are `c0 + c1·y`: two 64-bit lanes, so a pair of
//! K-values packs into one element by a copy, and every 16-byte string is a
//! valid element (transcript sampling stays a raw reinterpretation).
//!
//! This field is isomorphic to the GHASH [`super::gf2_128::F128`] but in a
//! different representation; the two must never be byte-interchanged.
//!
//! Multiplication is a 2-term Karatsuba over K: 3 PMULL products, the y-fold
//! (y^2 = y + c, one PMULL by the sparse constant after reducing the high
//! coefficient), and per-coefficient base folds. The mixed product
//! [`F128T::mul_base`] costs 2 PMULL: the workhorse pairing committed K-data
//! with E-challenges.

use core::ops::{Add, AddAssign, Mul, MulAssign};

use serde::{Deserialize, Serialize};

use super::gf2_64::F64;
use super::gf2_64x3::{R64, base_reduce_128};

/// Artin--Schreier constant: c = x^61 (trace 1, so y^2 + y + c is irreducible).
pub const C61: u64 = 1 << 61;

/// A tower GF(2^128) element `c0 + c1·y`, coefficients in GF(2^64).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub struct F128T {
    pub c0: u64,
    pub c1: u64,
}

impl F128T {
    pub const ZERO: Self = Self { c0: 0, c1: 0 };
    pub const ONE: Self = Self { c0: 1, c1: 0 };
    /// The element y.
    pub const Y: Self = Self { c0: 0, c1: 1 };

    #[inline]
    pub const fn new(c0: u64, c1: u64) -> Self {
        Self { c0, c1 }
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.c0 == 0 && self.c1 == 0
    }

    /// Mixed product K × E: two base multiplications, the hot kernel of the
    /// 64-bit transition (committed K-data times E-challenges).
    #[inline]
    pub fn mul_base(self, k: F64) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_base_neon(self, k.0) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            Self {
                c0: (F64(self.c0) * k).0,
                c1: (F64(self.c1) * k).0,
            }
        }
    }

    /// Squaring: (c0 + c1·y)^2 = (c0^2 + c·c1^2) + c1^2·y.
    #[inline]
    pub fn square(self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::square_neon(self) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            software::square(self)
        }
    }

    /// Multiplicative inverse via Fermat: self^(2^128 − 2). `ZERO.inv() == ZERO`.
    pub fn inv(self) -> Self {
        let mut cur = self.square();
        let mut r = cur;
        for _ in 2..128 {
            cur = cur.square();
            r *= cur;
        }
        r
    }
}

impl From<F64> for F128T {
    #[inline]
    fn from(k: F64) -> Self {
        Self { c0: k.0, c1: 0 }
    }
}

impl Add for F128T {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 ^ rhs.c0,
            c1: self.c1 ^ rhs.c1,
        }
    }
}

impl AddAssign for F128T {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.c0 ^= rhs.c0;
        self.c1 ^= rhs.c1;
    }
}

impl Mul for F128T {
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

impl MulAssign for F128T {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{C61, F128T, R64};
    use core::arch::aarch64::*;
    use core::mem::transmute;

    /// 64x64 carry-less product as a 128-bit NEON vector.
    ///
    /// # Safety
    /// Requires the `aes` target feature.
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn pmull(a: u64, b: u64) -> uint64x2_t {
        // SAFETY: u128 and uint64x2_t are both 128-bit values.
        unsafe { transmute::<u128, uint64x2_t>(vmull_p64(a, b)) }
    }

    /// Vectorized base fold of a lane pair: given lo = (l0, l1) and
    /// hi = (h0, h1) of two 128-bit carry-less products, returns
    /// (reduce(l0, h0), reduce(l1, h1)) via the shift-XOR fold by 0x1B,
    /// entirely inside the NEON register file.
    ///
    /// # Safety
    /// Requires the `aes` target feature.
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn fold_pair(lo: uint64x2_t, hi: uint64x2_t) -> uint64x2_t {
        // SAFETY: pure NEON ops under the aes feature.
        unsafe {
            let f = veorq_u64(
                veorq_u64(hi, vshlq_n_u64::<1>(hi)),
                veorq_u64(vshlq_n_u64::<3>(hi), vshlq_n_u64::<4>(hi)),
            );
            let ov = veorq_u64(
                veorq_u64(vshrq_n_u64::<63>(hi), vshrq_n_u64::<61>(hi)),
                vshrq_n_u64::<60>(hi),
            );
            let f2 = veorq_u64(
                veorq_u64(ov, vshlq_n_u64::<1>(ov)),
                veorq_u64(vshlq_n_u64::<3>(ov), vshlq_n_u64::<4>(ov)),
            );
            veorq_u64(veorq_u64(lo, f), f2)
        }
    }

    /// Karatsuba-2 over K with the fold y^2 = y + x^61, NEON-resident:
    /// 5 PMULL total (3 products, the sparse-constant fold, one final base
    /// fold) plus one vectorized pair fold for the other two reductions.
    ///
    /// (a0 + a1 y)(b0 + b1 y) = (p0 + c·p1) + (pm + p0)·y, with
    /// p0 = a0b0, p1 = a1b1, pm = (a0+a1)(b0+b1).
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_neon(a: F128T, b: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(a.c0, b.c0);
            let p1 = pmull(a.c1, b.c1);
            let pm = pmull(a.c0 ^ a.c1, b.c0 ^ b.c1);
            // Reduce p1 (needed for the c-fold) and pm^p0 (= c1) as a pair.
            let q = veorq_u64(pm, p0);
            let red = fold_pair(vtrn1q_u64(p1, q), vtrn2q_u64(p1, q));
            let r1 = vgetq_lane_u64::<0>(red);
            let c1 = vgetq_lane_u64::<1>(red);
            // c0 = reduce(p0 ^ x^61 * r1).
            let e0 = veorq_u64(p0, pmull(r1, C61));
            let t = pmull(vgetq_lane_u64::<1>(e0), R64);
            let ov = vgetq_lane_u64::<1>(t); // <= 4 bits
            let c0 = vgetq_lane_u64::<0>(e0)
                ^ vgetq_lane_u64::<0>(t)
                ^ ov
                ^ (ov << 1)
                ^ (ov << 3)
                ^ (ov << 4);
            F128T { c0, c1 }
        }
    }

    /// Mixed product K x E: 2 PMULL plus one vectorized pair fold.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_base_neon(e: F128T, k: u64) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(e.c0, k);
            let p1 = pmull(e.c1, k);
            let red = fold_pair(vtrn1q_u64(p0, p1), vtrn2q_u64(p0, p1));
            F128T {
                c0: vgetq_lane_u64::<0>(red),
                c1: vgetq_lane_u64::<1>(red),
            }
        }
    }

    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn square_neon(a: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let s0 = pmull(a.c0, a.c0);
            let s1 = pmull(a.c1, a.c1);
            let red = fold_pair(vtrn1q_u64(s1, s0), vtrn2q_u64(s1, s0));
            let r1 = vgetq_lane_u64::<0>(red);
            let r0 = vgetq_lane_u64::<1>(red);
            // c0 = reduce(s0) ^ reduce(x^61 * r1); both operands of the final
            // XOR are already reduced except the c-fold product.
            let e0 = pmull(r1, C61);
            let t = pmull(vgetq_lane_u64::<1>(e0), R64);
            let ov = vgetq_lane_u64::<1>(t);
            let c0 = r0
                ^ vgetq_lane_u64::<0>(e0)
                ^ vgetq_lane_u64::<0>(t)
                ^ ov
                ^ (ov << 1)
                ^ (ov << 3)
                ^ (ov << 4);
            F128T { c0, c1: r1 }
        }
    }
}

pub mod software {
    use super::{C61, F128T, base_reduce_128};
    use crate::field::gf2_128::software::clmul64;

    fn kmul(a: u64, b: u64) -> u64 {
        let (lo, hi) = clmul64(a, b);
        base_reduce_128(lo, hi)
    }

    pub fn mul(a: F128T, b: F128T) -> F128T {
        let p0 = kmul(a.c0, b.c0);
        let p1 = kmul(a.c1, b.c1);
        let pm = kmul(a.c0 ^ a.c1, b.c0 ^ b.c1);
        F128T {
            c0: p0 ^ kmul(C61, p1),
            c1: pm ^ p0,
        }
    }

    pub fn square(a: F128T) -> F128T {
        mul(a, a)
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

    fn rand_e(s: &mut u64) -> F128T {
        F128T::new(splitmix64(s), splitmix64(s))
    }

    /// Independent Python reference vectors: (a0, a1, b0, b1, c0, c1, s0, s1)
    /// with c = a·b and s = a·a.
    const VECTORS: [(u64, u64, u64, u64, u64, u64, u64, u64); 4] = [
        (0x837cdbaf0b2b77d0, 0x17db9019a5c7a28d, 0x4a8920a023b4363b, 0xaceebe818a0b1752,
         0x1f9ec82acac5b51b, 0xbf2eab10c28048c4, 0x7f2eea026d898016, 0x5ed13da49f045d8a),
        (0x1cd777cd5ded16c4, 0x64459b0ac86aadf2, 0xb0e421e0d55ad554, 0xcaaf5ef374e4939f,
         0xe2cfede22402b8c8, 0xb33d1ccaedae4aa6, 0xc9f68d6a38bb8d2a, 0x8df1a5e999e653b3),
        (0xe90d69507da22a5f, 0x514316d0a6fa9ebd, 0x67e5123d4abe45e4, 0x6f91273f56b9bf72,
         0x91dbd4c24df9e336, 0xebbc034ead81d268, 0x58bb09d18f9de68c, 0xef0ee5335b8f2e4a),
        (0x00bc98ae289212e6, 0x2b4d03d6a1dc235d, 0x2d8d19215a96789d, 0xe7683665a42ae4e2,
         0x185d7654d90fc676, 0x7a17c0dfadc43b22, 0xd9e5de7671ce8203, 0x2eb7e63b04757b8d),
    ];

    #[test]
    fn python_vectors() {
        for (a0, a1, b0, b1, c0, c1, s0, s1) in VECTORS {
            let (a, b) = (F128T::new(a0, a1), F128T::new(b0, b1));
            assert_eq!(a * b, F128T::new(c0, c1));
            assert_eq!(a.square(), F128T::new(s0, s1));
            assert_eq!(software::mul(a, b), F128T::new(c0, c1));
        }
    }

    #[test]
    fn defining_relation_and_identities() {
        // y^2 = y + c
        assert_eq!(F128T::Y * F128T::Y, F128T::Y + F128T::new(C61, 0));
        let mut s = 1u64;
        for _ in 0..100 {
            let a = rand_e(&mut s);
            assert_eq!(a * F128T::ONE, a);
            assert_eq!(a * F128T::ZERO, F128T::ZERO);
            assert_eq!(a + a, F128T::ZERO);
        }
    }

    #[test]
    fn neon_matches_software_and_axioms() {
        let mut s = 2u64;
        for _ in 0..10_000 {
            let (a, b, c) = (rand_e(&mut s), rand_e(&mut s), rand_e(&mut s));
            assert_eq!(a * b, software::mul(a, b));
            assert_eq!(a * b, b * a);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!(a.square(), a * a);
        }
    }

    #[test]
    fn mixed_product_matches_embedded() {
        let mut s = 3u64;
        for _ in 0..1_000 {
            let e = rand_e(&mut s);
            let k = F64(splitmix64(&mut s));
            assert_eq!(e.mul_base(k), e * F128T::from(k));
        }
    }

    #[test]
    fn inv() {
        let mut s = 4u64;
        for _ in 0..50 {
            let a = rand_e(&mut s);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F128T::ONE);
            }
        }
        assert_eq!(F128T::ZERO.inv(), F128T::ZERO);
    }

    /// Artin--Schreier: y^2 + y + c is irreducible over K iff Tr(c) = 1.
    /// Compute Tr(c) = Σ_{i<64} c^(2^i) in K and pin the constant choice.
    #[test]
    fn trace_of_c_is_one() {
        let mut t = F64::ZERO;
        let mut cur = F64(C61);
        for _ in 0..64 {
            t += cur;
            cur = cur.square();
        }
        assert_eq!(t, F64::ONE, "Tr(x^61) must be 1");
        // And the two monomials below it have trace 0 (x^61 is the least).
        for k in [59u32, 60] {
            let mut t = F64::ZERO;
            let mut cur = F64(1 << k);
            for _ in 0..64 {
                t += cur;
                cur = cur.square();
            }
            assert_eq!(t, F64::ZERO);
        }
    }
}
