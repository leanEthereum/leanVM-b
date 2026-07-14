//! Investigation variant: the **binius64** degree-2 tower of GF(2^64),
//! `GF((2^64)^2) = K[y]/(y² + x·y + 1)`, for a head-to-head comparison against
//! [`super::tower_f128`]'s Artin–Schreier tower `K[y]/(y² + y + x^61)`.
//!
//! Same base field K = GF(2^64) (`x^64 + x^4 + x^3 + x + 1`, [`F64`]) — only the
//! degree-2 extension polynomial differs, so a benchmark of the two isolates the
//! *tower choice*. The reduction here is cheaper on paper: with `y² = xy + 1`,
//!
//! ```text
//!   (a0 + a1·y)(b0 + b1·y) = (a0b0 + a1b1) + (a0b1 + a1b0 + x·a1b1)·y
//!   c0 = p0 + p1                       ← pure XOR, no constant multiply
//!   c1 = (a0b1 + a1b0) + x·p1          ← the only scaling is by x (a 1-bit shift)
//! ```
//!
//! versus our tower's `c0 = p0 + x^61·p1` (a multiply by `x^61`). The products
//! are the same 3-CLMUL Karatsuba either way; only the fold differs.
//!
//! Credit: binius64 <https://github.com/binius-zk/binius64>
//! (`crates/arith-bench/src/monbijou/{mod,clmul,soft64}.rs`) for the field and
//! its CLMUL arithmetic; this is a reimplementation over our [`F64`] base for
//! apples-to-apples benchmarking, not a vendored copy.
//!
//! This module is a benchmarking/exploration aid: it carries only the ops the
//! comparison needs (eager mul, the deferred-reduction pair, square, inv), not
//! the full field surface of [`super::tower_f128`].

use core::ops::{Add, BitXor, BitXorAssign, Mul};

/// A binius-tower GF(2^128) element `c0 + c1·y`, `y² = x·y + 1`, coeffs in K.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct F128Txy {
    pub c0: u64,
    pub c1: u64,
}

impl F128Txy {
    pub const ZERO: Self = Self { c0: 0, c1: 0 };
    pub const ONE: Self = Self { c0: 1, c1: 0 };

    #[inline]
    pub const fn new(c0: u64, c1: u64) -> Self {
        Self { c0, c1 }
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.c0 == 0 && self.c1 == 0
    }

    /// The three unreduced Karatsuba sub-products (raw 128-bit carry-less
    /// values), for deferred accumulation — the same shape as
    /// [`super::F128TUnreduced`], so the sumcheck hot loop is identical.
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> F128TxyUnreduced {
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe { x86_64::mul_unreduced(self, rhs) }
        }
        #[cfg(not(all(target_arch = "x86_64", target_feature = "pclmulqdq")))]
        {
            software::mul_unreduced(self, rhs)
        }
    }

    #[inline]
    pub fn square(self) -> Self {
        self * self
    }

    /// Multiplicative inverse via Fermat: self^(2^128 − 2).
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

impl Add for F128Txy {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self { c0: self.c0 ^ rhs.c0, c1: self.c1 ^ rhs.c1 }
    }
}

impl Mul for F128Txy {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.mul_unreduced(rhs).reduce()
    }
}

impl core::ops::MulAssign for F128Txy {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// The three unreduced Karatsuba sub-products `p0 = a0·b0`, `p1 = a1·b1`,
/// `pm = (a0+a1)(b0+b1)`, each a raw 128-bit carry-less value. Reduction is
/// GF(2)-linear, so these XOR-accumulate and reduce once.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128TxyUnreduced {
    pub p0: u128,
    pub p1: u128,
    pub pm: u128,
}

impl F128TxyUnreduced {
    pub const ZERO: Self = Self { p0: 0, p1: 0, pm: 0 };

    /// One reduction of the accumulated parts under `y² = xy + 1`:
    /// `c0 = reduce(p0 ^ p1)`, `c1 = reduce((pm ^ p0 ^ p1) ^ (p1 << 1))`
    /// (the `<< 1` is the unreduced multiply-by-x). The u128 combination is
    /// arch-independent; only the final GF(2^64) fold uses CLMUL.
    #[inline]
    pub fn reduce(self) -> F128Txy {
        let cross = self.pm ^ self.p0 ^ self.p1; // a0b1 + a1b0 (Karatsuba)
        let c0 = self.p0 ^ self.p1;
        let c1 = cross ^ (self.p1 << 1); // + x·(a1b1), unreduced
        F128Txy { c0: kreduce_u128(c0), c1: kreduce_u128(c1) }
    }
}

impl BitXor for F128TxyUnreduced {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        Self { p0: self.p0 ^ rhs.p0, p1: self.p1 ^ rhs.p1, pm: self.pm ^ rhs.pm }
    }
}

impl BitXorAssign for F128TxyUnreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.p0 ^= rhs.p0;
        self.p1 ^= rhs.p1;
        self.pm ^= rhs.pm;
    }
}

/// Reduce a 128-bit carry-less value (deg ≤ 127) mod `x^64 + x^4 + x^3 + x + 1`.
#[inline]
fn kreduce_u128(v: u128) -> u64 {
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        // SAFETY: pclmulqdq target feature is enabled at compile time; u128 and
        // __m128i are both 128-bit values.
        unsafe {
            super::gf2_64::x86_64::reduce(core::mem::transmute::<u128, core::arch::x86_64::__m128i>(v))
        }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "pclmulqdq")))]
    {
        super::gf2_64x3::base_reduce_128(v as u64, (v >> 64) as u64)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub mod x86_64 {
    use super::{F128Txy, F128TxyUnreduced};
    use crate::field::gf2_64::x86_64::clmul;

    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    unsafe fn pack(v: core::arch::x86_64::__m128i) -> u128 {
        // SAFETY: __m128i and u128 are both 128-bit values.
        unsafe { core::mem::transmute::<core::arch::x86_64::__m128i, u128>(v) }
    }

    /// The three Karatsuba products via CLMUL (3 CLMUL, no reduction).
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature.
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn mul_unreduced(a: F128Txy, b: F128Txy) -> F128TxyUnreduced {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe {
            F128TxyUnreduced {
                p0: pack(clmul(a.c0, b.c0)),
                p1: pack(clmul(a.c1, b.c1)),
                pm: pack(clmul(a.c0 ^ a.c1, b.c0 ^ b.c1)),
            }
        }
    }
}

pub mod software {
    use super::{F128Txy, F128TxyUnreduced};
    use crate::field::gf2_128::software::clmul64;

    #[inline]
    fn clmul128(a: u64, b: u64) -> u128 {
        let (lo, hi) = clmul64(a, b);
        lo as u128 | ((hi as u128) << 64)
    }

    pub fn mul_unreduced(a: F128Txy, b: F128Txy) -> F128TxyUnreduced {
        F128TxyUnreduced {
            p0: clmul128(a.c0, b.c0),
            p1: clmul128(a.c1, b.c1),
            pm: clmul128(a.c0 ^ a.c1, b.c0 ^ b.c1),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::gf2_64::F64;

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_e(s: &mut u64) -> F128Txy {
        F128Txy::new(splitmix64(s), splitmix64(s))
    }

    /// `y² = x·y + 1` (the defining relation) and the field axioms hold — a
    /// consistent field (associativity + inverses) confirms `y²+xy+1` is
    /// irreducible over our K.
    #[test]
    fn defining_relation_and_axioms() {
        let y = F128Txy::Y();
        let x = F128Txy::new(F64::G.0, 0); // the base generator x, lifted
        // y² = x·y + 1
        assert_eq!(y * y, x * y + F128Txy::ONE);

        let mut s = 1u64;
        for _ in 0..10_000 {
            let (a, b, c) = (rand_e(&mut s), rand_e(&mut s), rand_e(&mut s));
            assert_eq!(a * b, b * a);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!(a.square(), a * a);
            assert_eq!(a * F128Txy::ONE, a);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F128Txy::ONE);
            }
        }
    }

    /// A single deferred product reduces to the plain product, and XOR of many
    /// unreduced products reduces to the sum of the reduced ones (linearity).
    #[test]
    fn deferred_reduction_matches() {
        let mut s = 3u64;
        for _ in 0..5_000 {
            let (a, b, c, d) = (rand_e(&mut s), rand_e(&mut s), rand_e(&mut s), rand_e(&mut s));
            assert_eq!(a.mul_unreduced(b).reduce(), a * b);
            let acc = a.mul_unreduced(b) ^ c.mul_unreduced(d);
            assert_eq!(acc.reduce(), a * b + c * d);
        }
    }

    /// The x86 CLMUL path agrees with the software reference.
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    #[test]
    fn x86_matches_software() {
        let mut s = 9u64;
        for _ in 0..10_000 {
            let (a, b) = (rand_e(&mut s), rand_e(&mut s));
            let want = software::mul_unreduced(a, b).reduce();
            // SAFETY: pclmulqdq is statically enabled.
            let got = unsafe { x86_64::mul_unreduced(a, b) }.reduce();
            assert_eq!(got, want);
        }
    }
}

impl F128Txy {
    /// The element `y` (test helper).
    #[allow(non_snake_case)]
    #[cfg(test)]
    fn Y() -> Self {
        Self { c0: 0, c1: 1 }
    }
}
