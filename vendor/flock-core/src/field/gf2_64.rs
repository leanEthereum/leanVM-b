//! GF(2^64), first-class: the data/commitment field of the 64-bit transition.
//!
//! K = F_2[x]/(x^64 + x^4 + x^3 + x + 1), the standard low-weight irreducible
//! pentanomial; fold constant `R64 = 0x1B`. `x` is primitive (order exactly
//! 2^64 − 1; pinned by a test). One multiplication = 1 PMULL + a fold.
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
    use core::arch::aarch64::vmull_p64;

    /// 1 PMULL product + 1 PMULL fold + a ≤4-bit scalar fixup.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_neon(a: F64, b: F64) -> F64 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p = vmull_p64(a.0, b.0);
            let (lo, hi) = (p as u64, (p >> 64) as u64);
            let t = vmull_p64(hi, R64);
            let (tlo, ov) = (t as u64, (t >> 64) as u64); // ov ≤ 4 bits
            F64(lo ^ tlo ^ ov ^ (ov << 1) ^ (ov << 3) ^ (ov << 4))
        }
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
