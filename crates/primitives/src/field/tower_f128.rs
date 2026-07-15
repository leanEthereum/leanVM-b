//! Investigation variant: the **binius64** degree-2 tower of GF(2^64),
//! `GF((2^64)^2) = K[y]/(y² + x·y + 1)`, for a head-to-head comparison against
//! [`super::tower_f128_artin`]'s Artin–Schreier tower `K[y]/(y² + y + x^61)`.
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
//! the full field surface of [`super::tower_f128_artin`].

use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul};

use serde::{Deserialize, Serialize};

use super::gf2_64::F64;

/// A binius-tower GF(2^128) element `c0 + c1·y`, `y² = x·y + 1`, coeffs in K.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub struct F128T {
    pub c0: u64,
    pub c1: u64,
}

impl F128T {
    pub const ZERO: Self = Self { c0: 0, c1: 0 };
    pub const ONE: Self = Self { c0: 1, c1: 0 };
    /// The degree-2 generator `y`.
    pub const Y: Self = Self { c0: 0, c1: 1 };

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
    pub fn mul_unreduced(self, rhs: Self) -> F128TUnreduced {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_unreduced_neon(self, rhs) }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe { x86_64::mul_unreduced(self, rhs) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            software::mul_unreduced(self, rhs)
        }
    }

    /// Mixed product K × E: two base multiplications (`{c0·k, c1·k}`).
    /// Multiplying by a base-field scalar never reaches `y²`, so this is
    /// identical for either degree-2 tower.
    #[inline]
    pub fn mul_base(self, k: F64) -> Self {
        Self { c0: (F64(self.c0) * k).0, c1: (F64(self.c1) * k).0 }
    }

    /// The two unreduced lane products of a mixed K × E multiply, for deferred
    /// accumulation (the bus-leaf `Σ αⁱ·cᵢ` shape). Tower-independent.
    #[inline]
    pub fn mul_base_unreduced(self, k: F64) -> F128TBaseUnreduced {
        F128TBaseUnreduced { p0: kclmul(self.c0, k.0), p1: kclmul(self.c1, k.0) }
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

impl Add for F128T {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self { c0: self.c0 ^ rhs.c0, c1: self.c1 ^ rhs.c1 }
    }
}

impl AddAssign for F128T {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.c0 ^= rhs.c0;
        self.c1 ^= rhs.c1;
    }
}

impl From<F64> for F128T {
    #[inline]
    fn from(k: F64) -> Self {
        Self { c0: k.0, c1: 0 }
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
            self.mul_unreduced(rhs).reduce()
        }
    }
}

impl core::ops::MulAssign for F128T {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// The three unreduced Karatsuba sub-products `p0 = a0·b0`, `p1 = a1·b1`,
/// `pm = (a0+a1)(b0+b1)`, each a raw 128-bit carry-less value. Reduction is
/// GF(2)-linear, so these XOR-accumulate and reduce once.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128TUnreduced {
    pub p0: u128,
    pub p1: u128,
    pub pm: u128,
}

impl F128TUnreduced {
    pub const ZERO: Self = Self { p0: 0, p1: 0, pm: 0 };

    /// One reduction of the accumulated parts under `y² = xy + 1`:
    /// `c0 = reduce(p0 ^ p1)`, `c1 = reduce((pm ^ p0 ^ p1) ^ (p1 << 1))`
    /// (the `<< 1` is the unreduced multiply-by-x). The u128 combination is
    /// arch-independent; only the final GF(2^64) fold uses CLMUL.
    #[inline]
    pub fn reduce(self) -> F128T {
        let cross = self.pm ^ self.p0 ^ self.p1; // a0b1 + a1b0 (Karatsuba)
        let c0 = self.p0 ^ self.p1;
        let c1 = cross ^ (self.p1 << 1); // + x·(a1b1), unreduced
        F128T { c0: kreduce_u128(c0), c1: kreduce_u128(c1) }
    }
}

impl BitXor for F128TUnreduced {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        Self { p0: self.p0 ^ rhs.p0, p1: self.p1 ^ rhs.p1, pm: self.pm ^ rhs.pm }
    }
}

impl BitXorAssign for F128TUnreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.p0 ^= rhs.p0;
        self.p1 ^= rhs.p1;
        self.pm ^= rhs.pm;
    }
}

/// The two unreduced lane products of a mixed K × E multiply
/// ([`F128T::mul_base_unreduced`]): `p0 = c0·k`, `p1 = c1·k`, raw 128-bit
/// carry-less values. XOR-accumulates; [`Self::reduce`] runs one K-reduction per
/// lane. Tower-independent — the binius twin of `super::F128TBaseUnreduced`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128TBaseUnreduced {
    pub p0: u128,
    pub p1: u128,
}

impl F128TBaseUnreduced {
    pub const ZERO: Self = Self { p0: 0, p1: 0 };

    /// Reduce the two accumulated lanes back to K.
    #[inline]
    pub fn reduce(self) -> F128T {
        F128T { c0: kreduce_u128(self.p0), c1: kreduce_u128(self.p1) }
    }
}

impl BitXor for F128TBaseUnreduced {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        Self { p0: self.p0 ^ rhs.p0, p1: self.p1 ^ rhs.p1 }
    }
}

impl BitXorAssign for F128TBaseUnreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.p0 ^= rhs.p0;
        self.p1 ^= rhs.p1;
    }
}

/// Carry-less product of two K-scalars as a raw 128-bit value (arch-dispatched:
/// PMULL / PCLMULQDQ / software), shared by the mixed K×E kernels above.
#[inline]
fn kclmul(a: u64, b: u64) -> u128 {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: aes is statically enabled; uint64x2_t and u128 are both 128-bit.
        unsafe {
            core::mem::transmute::<core::arch::aarch64::uint64x2_t, u128>(
                crate::field::gf2_64::aarch64::pmull(a, b),
            )
        }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        // SAFETY: pclmulqdq is statically enabled; __m128i and u128 are both 128-bit.
        unsafe {
            core::mem::transmute::<core::arch::x86_64::__m128i, u128>(
                crate::field::gf2_64::x86_64::clmul(a, b),
            )
        }
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    )))]
    {
        let (lo, hi) = crate::field::gf2_128::software::clmul64(a, b);
        lo as u128 | ((hi as u128) << 64)
    }
}

/// Reduce a 128-bit carry-less value (deg ≤ 127) mod `x^64 + x^4 + x^3 + x + 1`.
#[inline]
fn kreduce_u128(v: u128) -> u64 {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: aes target feature is enabled at compile time.
        unsafe { aarch64::kreduce_u128(v) }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        // SAFETY: pclmulqdq target feature is enabled at compile time; u128 and
        // __m128i are both 128-bit values.
        unsafe {
            super::gf2_64::x86_64::reduce(core::mem::transmute::<u128, core::arch::x86_64::__m128i>(v))
        }
    }
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "aes"),
        all(target_arch = "x86_64", target_feature = "pclmulqdq")
    )))]
    {
        super::gf2_64x3::base_reduce_128(v as u64, (v >> 64) as u64)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub mod x86_64 {
    use super::{F128T, F128TUnreduced};
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
    pub unsafe fn mul_unreduced(a: F128T, b: F128T) -> F128TUnreduced {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe {
            F128TUnreduced {
                p0: pack(clmul(a.c0, b.c0)),
                p1: pack(clmul(a.c1, b.c1)),
                pm: pack(clmul(a.c0 ^ a.c1, b.c0 ^ b.c1)),
            }
        }
    }

    /// Deferred inner product `Σ aᵢ·bᵢ` via the AVX-512 `VPCLMULQDQ` batched
    /// Karatsuba accumulator (`B` independent banks) + one binius-tower reduce.
    /// Four elements fold per CLMUL; the reduce reuses the scalar-tested
    /// [`super::F128TUnreduced::reduce`].
    ///
    /// # Safety
    /// `a.len() == b.len()`; requires vpclmulqdq + avx512f.
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2", enable = "sse2")]
    pub unsafe fn inner_unreduced_vpclmul_kara<const B: usize>(
        a: &[F128T],
        b: &[F128T],
    ) -> F128T {
        debug_assert_eq!(a.len(), b.len());
        // SAFETY: F128T is repr(C) { c0, c1 }, i.e. two contiguous u64;
        // features carried.
        unsafe {
            let (p0, p1, pm) =
                crate::field::vpclmul::x86_64::karatsuba_acc::<B>(a.as_ptr().cast(), b.as_ptr().cast(), a.len());
            F128TUnreduced { p0, p1, pm }.reduce()
        }
    }

    /// [`inner_unreduced_vpclmul_kara`]'s schoolbook twin (four CLMULs/element,
    /// no pre-XOR) — the x86 side of the schoolbook-vs-Karatsuba question.
    ///
    /// # Safety
    /// See [`inner_unreduced_vpclmul_kara`].
    #[cfg(all(target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2", enable = "sse2")]
    pub unsafe fn inner_unreduced_vpclmul_school<const B: usize>(
        a: &[F128T],
        b: &[F128T],
    ) -> F128T {
        debug_assert_eq!(a.len(), b.len());
        // SAFETY: as in `inner_unreduced_vpclmul_kara`.
        unsafe {
            let (p0, p1, pm) =
                crate::field::vpclmul::x86_64::schoolbook_acc::<B>(a.as_ptr().cast(), b.as_ptr().cast(), a.len());
            F128TUnreduced { p0, p1, pm }.reduce()
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{F128T, F128TUnreduced};
    use crate::field::gf2_64::aarch64::{pmull, pmull_hi, reduce_pair};
    use crate::field::gf2_64x3::R64;
    use core::arch::aarch64::*;

    /// Karatsuba-2 over K with the binius fold `y² = x·y + 1`, NEON-resident.
    /// The products are the same 3-PMULL Karatsuba as
    /// [`super::super::tower_f128_artin::aarch64::mul_neon`], and each output limb
    /// reduces with the identical two-PMULL tail (`v ^ v.hi·0x1B ^ …`), so this
    /// kernel isolates the *fold* on NEON exactly as the x86 path does. With
    /// `y² = x·y + 1`:
    ///
    /// ```text
    ///   c0 = reduce(p0 ^ p1)
    ///   c1 = reduce((pm ^ p0 ^ p1) ^ (p1 << 1))
    /// ```
    ///
    /// with `p0 = a0b0`, `p1 = a1b1`, `pm = (a0+a1)(b0+b1)`. The lone constant
    /// scaling is the 128-bit `p1 << 1` — the unreduced multiply-by-`x` — versus
    /// the Artin–Schreier tower's 192-bit `x^61` fold: binius folds one word
    /// fewer, so both limbs are plain 128-bit reductions (7 PMULL total vs the
    /// Artin–Schreier kernel's 8), no GPR round-trips.
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
            let r = vdupq_n_u64(R64);

            // c0 = reduce(p0 ^ p1): PMULL fold + PMULL overflow fold.
            let e0 = veorq_u64(p0, p1);
            let t0 = pmull_hi(e0, r);
            let u0 = pmull_hi(t0, r); // exact ≤8-bit fold, high lane 0
            let c0v = veorq_u64(veorq_u64(e0, t0), u0);

            // c1 = reduce((pm ^ p0 ^ p1) ^ (p1 << 1)). p1 << 1 across the
            // 128-bit lane pair: the low-word bit-63 carry lands in the high
            // word (the unreduced multiply-by-x of a1b1).
            let p1x = veorq_u64(
                vshlq_n_u64::<1>(p1),
                vextq_u64::<1>(vdupq_n_u64(0), vshrq_n_u64::<63>(p1)),
            );
            let e1 = veorq_u64(veorq_u64(veorq_u64(pm, p0), p1), p1x);
            let t1 = pmull_hi(e1, r);
            let u1 = pmull_hi(t1, r);
            let c1v = veorq_u64(veorq_u64(e1, t1), u1);

            let res = vtrn1q_u64(c0v, c1v);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// The three unreduced Karatsuba sub-products (3 PMULL, no reduction) — the
    /// deferred-accumulation term shape, mirroring
    /// [`super::super::tower_f128_artin::aarch64::mul_unreduced_neon`].
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_unreduced_neon(a: F128T, b: F128T) -> F128TUnreduced {
        // SAFETY: function carries the aes target feature; uint64x2_t and u128
        // are both 128-bit values.
        unsafe {
            F128TUnreduced {
                p0: core::mem::transmute::<uint64x2_t, u128>(pmull(a.c0, b.c0)),
                p1: core::mem::transmute::<uint64x2_t, u128>(pmull(a.c1, b.c1)),
                pm: core::mem::transmute::<uint64x2_t, u128>(pmull(a.c0 ^ a.c1, b.c0 ^ b.c1)),
            }
        }
    }

    /// Reduce a 128-bit carry-less value to GF(2^64) via NEON — one lane of a
    /// [`reduce_pair`] (the other is discarded) — for the deferred reduce.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn kreduce_u128(v: u128) -> u64 {
        // SAFETY: function carries the aes target feature; u128 and uint64x2_t
        // are both 128-bit values.
        unsafe {
            let vv = core::mem::transmute::<u128, uint64x2_t>(v);
            vgetq_lane_u64::<0>(reduce_pair(vv, vdupq_n_u64(0)))
        }
    }
}

pub mod software {
    use super::{F128T, F128TUnreduced};
    use crate::field::gf2_128::software::clmul64;

    #[inline]
    fn clmul128(a: u64, b: u64) -> u128 {
        let (lo, hi) = clmul64(a, b);
        lo as u128 | ((hi as u128) << 64)
    }

    pub fn mul_unreduced(a: F128T, b: F128T) -> F128TUnreduced {
        F128TUnreduced {
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

    #[test]
    fn frob64_lane_extraction() {
        // F128T = F64[Y]/(Y^2 = X*Y + 1) with Y = new(0,1); the 2^64-Frobenius is
        // the nontrivial F64-automorphism, so Frob64(Y) = X + Y (the conjugate
        // root). Hence for pi = a + b*Y (a,b in F64): pi + Frob64(pi) = b*X, so
        // b = (pi + Frob64(pi))*X^{-1} (the c1 lane) and a = pi + b*Y (the c0
        // lane). This is how the recursion guest recovers memory lanes from a
        // 128-bit public-input word (deterministic ⇒ sound).
        let y = F128T::new(0, 1);
        let frob = |z0: F128T| {
            let mut z = z0;
            for _ in 0..64 {
                z = z * z;
            }
            z
        };
        let x = frob(y) + y; // = X, the F64 generator embedded (c1 must be 0)
        assert_eq!(x.c1, 0, "X = Frob64(Y)+Y must lie in F64");
        let x_inv = x.inv();
        let mut s = 0x1234_5678_9abc_def0u64;
        for _ in 0..1000 {
            let a = splitmix64(&mut s);
            let b = splitmix64(&mut s);
            let pi = F128T::new(a, b); // = a + b*Y
            let fp = frob(pi);
            let b_ext = (pi + fp) * x_inv;
            let a_ext = pi + b_ext * y;
            assert_eq!(b_ext, F128T::new(b, 0), "c1 lane extraction failed");
            assert_eq!(a_ext, F128T::new(a, 0), "c0 lane extraction failed");
        }
    }

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

    /// `y² = x·y + 1` (the defining relation) and the field axioms hold — a
    /// consistent field (associativity + inverses) confirms `y²+xy+1` is
    /// irreducible over our K.
    #[test]
    fn defining_relation_and_axioms() {
        let y = F128T::Y;
        let x = F128T::new(F64::G.0, 0); // the base generator x, lifted
        // y² = x·y + 1
        assert_eq!(y * y, x * y + F128T::ONE);

        let mut s = 1u64;
        for _ in 0..10_000 {
            let (a, b, c) = (rand_e(&mut s), rand_e(&mut s), rand_e(&mut s));
            assert_eq!(a * b, b * a);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!(a.square(), a * a);
            assert_eq!(a * F128T::ONE, a);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F128T::ONE);
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

    /// The AVX-512 VPCLMULQDQ batched inner-product kernels (Karatsuba and
    /// schoolbook, several bank counts) equal the scalar deferred reference
    /// across a range of lengths — including partial vector groups and the
    /// scalar `< 4` tail.
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    #[test]
    fn vpclmul_inner_matches_scalar() {
        fn reference(a: &[F128T], b: &[F128T]) -> F128T {
            let mut acc = F128TUnreduced::ZERO;
            for i in 0..a.len() {
                acc ^= a[i].mul_unreduced(b[i]);
            }
            acc.reduce()
        }
        let mut s = 0x1234u64;
        for &n in &[0usize, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 33, 64, 100, 257, 1024] {
            let a: Vec<F128T> = (0..n).map(|_| rand_e(&mut s)).collect();
            let b: Vec<F128T> = (0..n).map(|_| rand_e(&mut s)).collect();
            let want = reference(&a, &b);
            // SAFETY: vpclmulqdq + avx512f statically enabled by the cfg gate.
            unsafe {
                assert_eq!(x86_64::inner_unreduced_vpclmul_kara::<1>(&a, &b), want, "kara B=1 n={n}");
                assert_eq!(x86_64::inner_unreduced_vpclmul_kara::<2>(&a, &b), want, "kara B=2 n={n}");
                assert_eq!(x86_64::inner_unreduced_vpclmul_kara::<4>(&a, &b), want, "kara B=4 n={n}");
                assert_eq!(x86_64::inner_unreduced_vpclmul_school::<1>(&a, &b), want, "school B=1 n={n}");
                assert_eq!(x86_64::inner_unreduced_vpclmul_school::<2>(&a, &b), want, "school B=2 n={n}");
                assert_eq!(x86_64::inner_unreduced_vpclmul_school::<4>(&a, &b), want, "school B=4 n={n}");
            }
        }
    }

    /// The NEON paths (fused `mul_neon`, and `mul_unreduced_neon` + reduce)
    /// agree with the software reference.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn aarch64_matches_software() {
        let mut s = 9u64;
        for _ in 0..10_000 {
            let (a, b) = (rand_e(&mut s), rand_e(&mut s));
            let want = software::mul_unreduced(a, b).reduce();
            // SAFETY: the aes target feature is statically enabled.
            let fused = unsafe { aarch64::mul_neon(a, b) };
            let deferred = unsafe { aarch64::mul_unreduced_neon(a, b) }.reduce();
            assert_eq!(fused, want);
            assert_eq!(deferred, want);
        }
    }

    /// `mul_base` and `mul_base_unreduced` agree with the lane-wise F64
    /// reference, and the deferred base accumulator is F2-linear.
    #[test]
    fn base_mul_matches_reference() {
        let mut s = 11u64;
        for _ in 0..10_000 {
            let e = rand_e(&mut s);
            let k = F64(splitmix64(&mut s));
            let want = F128T::new((F64(e.c0) * k).0, (F64(e.c1) * k).0);
            assert_eq!(e.mul_base(k), want);
            assert_eq!(e.mul_base_unreduced(k).reduce(), want);
            let e2 = rand_e(&mut s);
            let k2 = F64(splitmix64(&mut s));
            let acc = e.mul_base_unreduced(k) ^ e2.mul_base_unreduced(k2);
            assert_eq!(acc.reduce(), e.mul_base(k) + e2.mul_base(k2));
        }
    }
}
