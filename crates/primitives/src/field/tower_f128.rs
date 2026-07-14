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
//! Multiplication is a 2-term Karatsuba over K (3 PMULL products) with
//! PMULL-based reductions that never leave the NEON register file: the
//! y-lane folds its high half by 0x1B, and the constant lane folds
//! p0 ^ x^61·p1 as one 192-bit value with a parallel PMULL pair (word 1 by
//! x^64 mod P = 0x1B, word 2 by x^128 mod P = 0x145), 8 PMULL total. The
//! mixed product [`F128T::mul_base`] costs 2 product PMULL + a 2-PMULL pair
//! fold with a TBL tail: the workhorse pairing committed K-data with
//! E-challenges.

use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};

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

    /// Unreduced product `(self · rhs)`: the three Karatsuba sub-products as
    /// raw 128-bit carry-less values — 3 PMULL, NO reduction. Caller XORs many
    /// of these into an [`F128TUnreduced`] accumulator and calls `.reduce()`
    /// once at the end. Reduction and the `y² = y + x^61` fold are
    /// GF(2)-linear, so `Σ (aᵢ·bᵢ) mod P = reduce(Σ parts)` — this defers the
    /// 5-PMULL reduction tail (the majority of a full mul's work) from every
    /// term to once per sum. The tower analog of GHASH's
    /// [`F256Unreduced`](crate::field::F256Unreduced).
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

    /// Unreduced mixed product K × E: the two lane products `c0·k`, `c1·k` as
    /// raw 128-bit carry-less values — 2 PMULL, NO reduction. XOR many into an
    /// [`F128TBaseUnreduced`] and reduce once (the bus-leaf `Σ αⁱ·cᵢ` shape).
    #[inline]
    pub fn mul_base_unreduced(self, k: F64) -> F128TBaseUnreduced {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_base_unreduced_neon(self, k.0) }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe { x86_64::mul_base_unreduced(self, k.0) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            software::mul_base_unreduced(self, k)
        }
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
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe { x86_64::square(self) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            software::square(self)
        }
    }

    /// Two independent products at once: `[a[0]·b[0], a[1]·b[1]]`, exactly the
    /// values of two scalar muls. On NEON the pair kernel interleaves the two
    /// products so the six PMULL latency chains overlap and the three shared
    /// pair folds reduce both at once ([`aarch64::mul2_neon`]). Worth it only
    /// when the two muls sit on serial dependence chains (~40% faster there,
    /// see `bench_mul2_kernel`); in loops over independent data the OoO core
    /// already overlaps scalar muls and the pair form gains little or loses.
    #[inline]
    pub fn mul2(a: [Self; 2], b: [Self; 2]) -> [Self; 2] {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul2_neon(a, b) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            [a[0] * b[0], a[1] * b[1]]
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

// ---------------------------------------------------------------------------
// Deferred reduction: unreduced tower products that can be XOR-accumulated.
// ---------------------------------------------------------------------------

/// The three unreduced Karatsuba sub-products of one E × E multiply:
/// `p0 = a0·b0`, `p1 = a1·b1`, `pm = (a0+a1)·(b0+b1)`, each a raw 128-bit
/// carry-less value. XOR-accumulates ([`BitXor`]); [`Self::reduce`] runs the
/// full reduction tail once. 48 bytes per accumulator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128TUnreduced {
    pub p0: u128,
    pub p1: u128,
    pub pm: u128,
}

impl F128TUnreduced {
    pub const ZERO: Self = Self { p0: 0, p1: 0, pm: 0 };

    /// One full reduction of the accumulated parts: `c1 = reduce(pm ^ p0)`,
    /// `c0 = reduce(p0 ^ x^61·p1)` — exactly the tail of one multiply
    /// ([`aarch64::mul_neon`]), applied to the sums.
    #[inline]
    pub fn reduce(self) -> F128T {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::reduce_unreduced_neon(self) }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe { x86_64::reduce_unreduced(self) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            software::reduce_unreduced(self)
        }
    }
}

impl BitXor for F128TUnreduced {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        Self {
            p0: self.p0 ^ rhs.p0,
            p1: self.p1 ^ rhs.p1,
            pm: self.pm ^ rhs.pm,
        }
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
/// ([`F128T::mul_base_unreduced`]): `p0 = c0·k`, `p1 = c1·k`, each a raw
/// 128-bit carry-less value. XOR-accumulates; [`Self::reduce`] runs one pair
/// reduction. 32 bytes per accumulator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128TBaseUnreduced {
    pub p0: u128,
    pub p1: u128,
}

impl F128TBaseUnreduced {
    pub const ZERO: Self = Self { p0: 0, p1: 0 };

    /// One pair reduction of the accumulated lanes.
    #[inline]
    pub fn reduce(self) -> F128T {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::reduce_base_unreduced_neon(self) }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
        {
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe { x86_64::reduce_base_unreduced(self) }
        }
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "pclmulqdq")
        )))]
        {
            software::reduce_base_unreduced(self)
        }
    }
}

impl BitXor for F128TBaseUnreduced {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        Self {
            p0: self.p0 ^ rhs.p0,
            p1: self.p1 ^ rhs.p1,
        }
    }
}

impl BitXorAssign for F128TBaseUnreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.p0 ^= rhs.p0;
        self.p1 ^= rhs.p1;
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

impl MulAssign for F128T {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{C61, F128T, R64};
    use crate::field::gf2_64::aarch64::{
        pmull, pmull_hi, reduce_pair, reduce_pair_pmull4, reduce_pair_tbl,
    };
    use core::arch::aarch64::*;

    /// x^128 mod (x^64 + x^4 + x^3 + x + 1) = (x^4 + x^3 + x + 1)^2, the
    /// Frobenius square of `R64`: folds the third 64-bit word of a 192-bit
    /// carry-less value in one PMULL.
    const R128: u64 = 0x145;

    /// Karatsuba-2 over K with the fold y^2 = y + x^61, NEON-resident with
    /// parallel PMULL reductions (8 PMULL total, no GPR round-trips):
    ///
    /// (a0 + a1 y)(b0 + b1 y) = (p0 + c·p1) + (pm + p0)·y, with
    /// p0 = a0b0, p1 = a1b1, pm = (a0+a1)(b0+b1).
    ///
    /// The y-lane reduces as usual: c1 = reduce(pm ^ p0), one PMULL-by-0x1B
    /// fold. For the constant lane, x^61·reduce(p1) ≡ x^61·p1 (mod P), so
    /// instead of reducing p1 first and feeding a serial C61 multiply, the
    /// kernel builds the 189-bit value p0 ^ x^61·p1 directly (x^61·p1 is a
    /// 3-word shift of p1) and folds its two upper words in one parallel
    /// PMULL pair: word 1 by 0x1B (= x^64 mod P), word 2 by 0x145 (= x^128
    /// mod P). Each lane's tiny second-order overflow (≤5 bits for c0,
    /// ≤4 bits for c1) folds exactly with one more PMULL each, and the
    /// result packs as a single uint64x2 {c0, c1}.
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

            // c1 = reduce(pm ^ p0): PMULL fold + PMULL overflow fold.
            let q = veorq_u64(pm, p0);
            let tq = pmull_hi(q, r);
            let u1 = pmull_hi(tq, r); // exact ≤8-bit fold, high lane 0
            let c1v = veorq_u64(veorq_u64(q, tq), u1);

            // c0 = reduce(p0 ^ x^61·p1) as a 192-bit fold. x^61·p1 spans
            // words {p1.lo<<61, p1.lo>>3 ^ p1.hi<<61, p1.hi>>3}.
            let sl = vshlq_n_u64::<61>(p1);
            let sr = vshrq_n_u64::<3>(p1);
            // v = {v0, v1}: the low two words of p0 ^ x^61·p1.
            let v = veorq_u64(
                veorq_u64(p0, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r); // v1·0x1B, ≤68 bits
            let w2 = pmull_hi(sr, vdupq_n_u64(R128)); // v2·0x145, ≤69 bits
            let x = veorq_u64(w1, w2);
            let u0 = pmull_hi(x, r); // exact ≤9-bit fold of x.hi ≤ 5 bits
            let c0v = veorq_u64(veorq_u64(v, x), u0);

            let res = vtrn1q_u64(c0v, c1v);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// [`mul_neon`] with the two second-order overflows folded together by a
    /// shared vectorized shift-XOR instead of two PMULLs (6 PMULL total).
    /// Benchmark alternate: marginally better serial latency, ~15% worse
    /// array throughput than the PMULL tails.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_shift_tail(a: F128T, b: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(a.c0, b.c0);
            let p1 = pmull(a.c1, b.c1);
            let pm = pmull(a.c0 ^ a.c1, b.c0 ^ b.c1);
            let r = vdupq_n_u64(R64);

            let q = veorq_u64(pm, p0);
            let tq = pmull_hi(q, r);

            let sl = vshlq_n_u64::<61>(p1);
            let sr = vshrq_n_u64::<3>(p1);
            let v = veorq_u64(
                veorq_u64(p0, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r);
            let w2 = pmull_hi(sr, vdupq_n_u64(R128));
            let x = veorq_u64(w1, w2);

            // Shared tail: lane 0 finishes c0, lane 1 finishes c1. The
            // overflows (x.hi ≤ 5 bits, tq.hi ≤ 4 bits) fold exactly by
            // one shift-XOR (ov·0x1B fits in 9 bits).
            let lo = vtrn1q_u64(veorq_u64(v, x), veorq_u64(q, tq));
            let ov = vtrn2q_u64(x, tq);
            let f = veorq_u64(
                veorq_u64(ov, vshlq_n_u64::<1>(ov)),
                veorq_u64(vshlq_n_u64::<3>(ov), vshlq_n_u64::<4>(ov)),
            );
            let res = veorq_u64(lo, f);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// Serial-fold variant: reduce p1 fully (2 PMULL), multiply by C61, then
    /// reduce the constant lane (8 PMULL, longer y-fold dependency chain).
    /// Kept as a benchmark alternate; [`mul_neon`]'s parallel 192-bit fold
    /// beat it on both latency and throughput.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_serial_fold(a: F128T, b: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(a.c0, b.c0);
            let p1 = pmull(a.c1, b.c1);
            let pm = pmull(a.c0 ^ a.c1, b.c0 ^ b.c1);
            let q = veorq_u64(pm, p0);
            // {r1, c1} = {reduce(p1), reduce(q)}.
            let red = reduce_pair(p1, q);
            // c0 = reduce(p0 ^ x^61·r1): the C61 product waits on r1.
            let e0 = veorq_u64(p0, pmull(vgetq_lane_u64::<0>(red), C61));
            let r = vdupq_n_u64(R64);
            let t = pmull_hi(e0, r);
            let u = pmull_hi(t, r);
            let c0v = veorq_u64(veorq_u64(e0, t), u);
            F128T {
                c0: vgetq_lane_u64::<0>(c0v),
                c1: vgetq_lane_u64::<1>(red),
            }
        }
    }

    /// The three unreduced Karatsuba sub-products: 3 PMULL + 2 GPR XORs,
    /// nothing else — the term cost of a deferred-reduction sum
    /// ([`super::F128TUnreduced`]).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_unreduced_neon(a: F128T, b: F128T) -> super::F128TUnreduced {
        // SAFETY: function carries the aes target feature; u128 and
        // uint64x2_t are both 128-bit values.
        unsafe {
            super::F128TUnreduced {
                p0: core::mem::transmute::<uint64x2_t, u128>(pmull(a.c0, b.c0)),
                p1: core::mem::transmute::<uint64x2_t, u128>(pmull(a.c1, b.c1)),
                pm: core::mem::transmute::<uint64x2_t, u128>(pmull(a.c0 ^ a.c1, b.c0 ^ b.c1)),
            }
        }
    }

    /// The two unreduced lane products of a mixed K × E multiply: 2 PMULL,
    /// nothing else — the term cost of a deferred bus-leaf sum.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_base_unreduced_neon(e: F128T, k: u64) -> super::F128TBaseUnreduced {
        // SAFETY: function carries the aes target feature; u128 and
        // uint64x2_t are both 128-bit values.
        unsafe {
            super::F128TBaseUnreduced {
                p0: core::mem::transmute::<uint64x2_t, u128>(pmull(e.c0, k)),
                p1: core::mem::transmute::<uint64x2_t, u128>(pmull(e.c1, k)),
            }
        }
    }

    /// Reduce accumulated mixed-product lanes: one [`reduce_pair`].
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_base_unreduced_neon(u: super::F128TBaseUnreduced) -> F128T {
        // SAFETY: function carries the aes target feature; u128 and
        // uint64x2_t are both 128-bit values.
        unsafe {
            let p0 = core::mem::transmute::<u128, uint64x2_t>(u.p0);
            let p1 = core::mem::transmute::<u128, uint64x2_t>(u.p1);
            let red = reduce_pair(p0, p1);
            F128T {
                c0: vgetq_lane_u64::<0>(red),
                c1: vgetq_lane_u64::<1>(red),
            }
        }
    }

    /// Reduce accumulated unreduced parts: [`mul_neon`]'s exact reduction
    /// tail (5 PMULL, parallel folds), applied once to the sums.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn reduce_unreduced_neon(u: super::F128TUnreduced) -> F128T {
        // SAFETY: function carries the aes target feature; u128 and
        // uint64x2_t are both 128-bit values.
        unsafe {
            let p0 = core::mem::transmute::<u128, uint64x2_t>(u.p0);
            let p1 = core::mem::transmute::<u128, uint64x2_t>(u.p1);
            let pm = core::mem::transmute::<u128, uint64x2_t>(u.pm);
            let r = vdupq_n_u64(R64);

            let q = veorq_u64(pm, p0);
            let tq = pmull_hi(q, r);
            let u1 = pmull_hi(tq, r);
            let c1v = veorq_u64(veorq_u64(q, tq), u1);

            let sl = vshlq_n_u64::<61>(p1);
            let sr = vshrq_n_u64::<3>(p1);
            let v = veorq_u64(
                veorq_u64(p0, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r);
            let w2 = pmull_hi(sr, vdupq_n_u64(R128));
            let x = veorq_u64(w1, w2);
            let u0 = pmull_hi(x, r);
            let c0v = veorq_u64(veorq_u64(v, x), u0);

            let res = vtrn1q_u64(c0v, c1v);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// Deferred-reduction inner product `Σ aᵢ·bᵢ` with the three unreduced
    /// accumulators held in NEON registers across the whole loop: per term
    /// 2 vector loads, 3 PMULL, and 5 EOR/EXT — no reduction, no GPR
    /// round-trip, no per-term accumulator store. One [`mul_neon`]-tail
    /// reduction at the end. The hot-loop form of
    /// [`super::F128TUnreduced`]-style accumulation.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[target_feature(enable = "aes")]
    pub unsafe fn inner_unreduced_neon(a: &[F128T], b: &[F128T]) -> F128T {
        debug_assert_eq!(a.len(), b.len());
        // SAFETY: function carries the aes target feature; F128T is
        // repr(C) { c0: u64, c1: u64 }, so a pointer to it reads as one
        // uint64x2_t lane pair.
        unsafe {
            let mut acc0 = vdupq_n_u64(0);
            let mut acc1 = vdupq_n_u64(0);
            let mut accm = vdupq_n_u64(0);
            for i in 0..a.len() {
                let av = vld1q_u64((&raw const a[i]).cast::<u64>());
                let bv = vld1q_u64((&raw const b[i]).cast::<u64>());
                let am = veorq_u64(av, vextq_u64::<1>(av, av)); // lane 0 = a0^a1
                let bm = veorq_u64(bv, vextq_u64::<1>(bv, bv));
                acc0 = veorq_u64(acc0, pmull(vgetq_lane_u64::<0>(av), vgetq_lane_u64::<0>(bv)));
                acc1 = veorq_u64(acc1, pmull_hi(av, bv));
                accm = veorq_u64(accm, pmull(vgetq_lane_u64::<0>(am), vgetq_lane_u64::<0>(bm)));
            }
            // One reduction of the sums: mul_neon's exact tail.
            let r = vdupq_n_u64(R64);
            let q = veorq_u64(accm, acc0);
            let tq = pmull_hi(q, r);
            let u1 = pmull_hi(tq, r);
            let c1v = veorq_u64(veorq_u64(q, tq), u1);

            let sl = vshlq_n_u64::<61>(acc1);
            let sr = vshrq_n_u64::<3>(acc1);
            let v = veorq_u64(
                veorq_u64(acc0, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r);
            let w2 = pmull_hi(sr, vdupq_n_u64(R128));
            let x = veorq_u64(w1, w2);
            let u0 = pmull_hi(x, r);
            let c0v = veorq_u64(veorq_u64(v, x), u0);

            let res = vtrn1q_u64(c0v, c1v);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// Vector-resident schoolbook: each operand enters NEON once as a
    /// `{c0, c1}` lane pair and NOTHING returns to GPRs until the final
    /// extraction. The four products come straight off the lane pairs — the
    /// low lanes via PMULL, the high lanes via PMULL2, and the cross products
    /// from one EXT-swapped copy of `b` — so Karatsuba's two GPR pre-XORs and
    /// their operand transfers disappear at the cost of one extra PMULL
    /// (4 products instead of 3; 9 PMULL total with the parallel-fold
    /// reduction). Trades the scarce-ish PMULL for scarcer issue slots and
    /// GPR→NEON bandwidth, which is what the 8-chain throughput shape is
    /// actually bound by.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_schoolbook(a: F128T, b: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let av = vcombine_u64(vcreate_u64(a.c0), vcreate_u64(a.c1));
            let bv = vcombine_u64(vcreate_u64(b.c0), vcreate_u64(b.c1));
            let brev = vextq_u64::<1>(bv, bv); // {b1, b0}

            // Low-lane products compile to PMULL on the D registers (no lane
            // moves); high-lane products are PMULL2.
            let p00 = pmull(vgetq_lane_u64::<0>(av), vgetq_lane_u64::<0>(bv)); // a0·b0
            let p11 = pmull_hi(av, bv); // a1·b1
            let p01 = pmull(vgetq_lane_u64::<0>(av), vgetq_lane_u64::<0>(brev)); // a0·b1
            let p10 = pmull_hi(av, brev); // a1·b0
            let r = vdupq_n_u64(R64);

            // y-lane: c1 = reduce(p01 ^ p10 ^ p11).
            let q = veorq_u64(veorq_u64(p01, p10), p11);
            let tq = pmull_hi(q, r);
            let u1 = pmull_hi(tq, r);
            let c1v = veorq_u64(veorq_u64(q, tq), u1);

            // constant lane: c0 = reduce(p00 ^ x^61·p11), the 192-bit
            // parallel fold of [`mul_neon`].
            let sl = vshlq_n_u64::<61>(p11);
            let sr = vshrq_n_u64::<3>(p11);
            let v = veorq_u64(
                veorq_u64(p00, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r);
            let w2 = pmull_hi(sr, vdupq_n_u64(R128));
            let x = veorq_u64(w1, w2);
            let u0 = pmull_hi(x, r);
            let c0v = veorq_u64(veorq_u64(v, x), u0);

            let res = vtrn1q_u64(c0v, c1v);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// [`mul_schoolbook`] with the shared shift-XOR overflow tail of
    /// [`mul_shift_tail`] (7 PMULL total). Benchmark alternate.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_schoolbook_shift_tail(a: F128T, b: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let av = vcombine_u64(vcreate_u64(a.c0), vcreate_u64(a.c1));
            let bv = vcombine_u64(vcreate_u64(b.c0), vcreate_u64(b.c1));
            let brev = vextq_u64::<1>(bv, bv);

            let p00 = pmull(vgetq_lane_u64::<0>(av), vgetq_lane_u64::<0>(bv));
            let p11 = pmull_hi(av, bv);
            let p01 = pmull(vgetq_lane_u64::<0>(av), vgetq_lane_u64::<0>(brev));
            let p10 = pmull_hi(av, brev);
            let r = vdupq_n_u64(R64);

            let q = veorq_u64(veorq_u64(p01, p10), p11);
            let tq = pmull_hi(q, r);

            let sl = vshlq_n_u64::<61>(p11);
            let sr = vshrq_n_u64::<3>(p11);
            let v = veorq_u64(
                veorq_u64(p00, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r);
            let w2 = pmull_hi(sr, vdupq_n_u64(R128));
            let x = veorq_u64(w1, w2);

            let lo = vtrn1q_u64(veorq_u64(v, x), veorq_u64(q, tq));
            let ov = vtrn2q_u64(x, tq);
            let f = veorq_u64(
                veorq_u64(ov, vshlq_n_u64::<1>(ov)),
                veorq_u64(vshlq_n_u64::<3>(ov), vshlq_n_u64::<4>(ov)),
            );
            let res = veorq_u64(lo, f);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// Vector-resident Karatsuba: [`mul_neon`]'s 3-product decomposition, but
    /// the pre-XORs `(a0^a1, b0^b1)` computed in NEON off the packed lane
    /// pairs (EXT + EOR) instead of in GPRs — same 8 PMULL, fewer transfers.
    /// Benchmark alternate.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_karatsuba_vec(a: F128T, b: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let av = vcombine_u64(vcreate_u64(a.c0), vcreate_u64(a.c1));
            let bv = vcombine_u64(vcreate_u64(b.c0), vcreate_u64(b.c1));
            let am = veorq_u64(av, vextq_u64::<1>(av, av)); // lane 0 = a0^a1
            let bm = veorq_u64(bv, vextq_u64::<1>(bv, bv));

            let p0 = pmull(vgetq_lane_u64::<0>(av), vgetq_lane_u64::<0>(bv));
            let p1 = pmull_hi(av, bv);
            let pm = pmull(vgetq_lane_u64::<0>(am), vgetq_lane_u64::<0>(bm));
            let r = vdupq_n_u64(R64);

            let q = veorq_u64(pm, p0);
            let tq = pmull_hi(q, r);
            let u1 = pmull_hi(tq, r);
            let c1v = veorq_u64(veorq_u64(q, tq), u1);

            let sl = vshlq_n_u64::<61>(p1);
            let sr = vshrq_n_u64::<3>(p1);
            let v = veorq_u64(
                veorq_u64(p0, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r);
            let w2 = pmull_hi(sr, vdupq_n_u64(R128));
            let x = veorq_u64(w1, w2);
            let u0 = pmull_hi(x, r);
            let c0v = veorq_u64(veorq_u64(v, x), u0);

            let res = vtrn1q_u64(c0v, c1v);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }

    /// Two independent [`mul_neon`] products. With the parallel-fold kernel
    /// each mul's reduction is already fully vectorized (no shared work left
    /// to merge), so the pair form is exactly two inlined muls: its value is
    /// letting the sixteen PMULLs of two muls issue back to back on serial
    /// dependence chains that a scalar loop would run one mul at a time.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul2_neon(a: [F128T; 2], b: [F128T; 2]) -> [F128T; 2] {
        // SAFETY: function carries the aes target feature.
        unsafe { [mul_neon(a[0], b[0]), mul_neon(a[1], b[1])] }
    }

    /// Mixed product K x E: 2 product PMULL + the TBL lane-pair reduction
    /// ([`reduce_pair_tbl`]). Shortest dependency chain of the variants
    /// tried (~2.8 ns serial latency vs ~4.7 for the all-PMULL reduce) at
    /// equal chain throughput.
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
            let red = reduce_pair_tbl(p0, p1);
            F128T {
                c0: vgetq_lane_u64::<0>(red),
                c1: vgetq_lane_u64::<1>(red),
            }
        }
    }

    /// [`mul_base_neon`] with the all-PMULL pair reduction (6 PMULL, minimal
    /// non-PMULL op count): best array throughput, benchmark alternate.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_base_pmull4(e: F128T, k: u64) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(e.c0, k);
            let p1 = pmull(e.c1, k);
            let red = reduce_pair_pmull4(p0, p1);
            F128T {
                c0: vgetq_lane_u64::<0>(red),
                c1: vgetq_lane_u64::<1>(red),
            }
        }
    }

    /// [`mul_base_neon`] with the shift-XOR overflow tail. Benchmark
    /// alternate.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_base_shift_tail(e: F128T, k: u64) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(e.c0, k);
            let p1 = pmull(e.c1, k);
            let red = reduce_pair(p0, p1);
            F128T {
                c0: vgetq_lane_u64::<0>(red),
                c1: vgetq_lane_u64::<1>(red),
            }
        }
    }

    /// Squaring: (c0 + c1·y)^2 = (c0^2 + c·c1^2) + c1^2·y. Same structure as
    /// [`mul_neon`] with p0 = c0^2, p1 = c1^2 and the y-lane just reduce(s1)
    /// (7 PMULL total).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_neon`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn square_neon(a: F128T) -> F128T {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let s0 = pmull(a.c0, a.c0);
            let s1 = pmull(a.c1, a.c1);
            let r = vdupq_n_u64(R64);

            // c1 = reduce(s1).
            let tq = pmull_hi(s1, r);
            let u1 = pmull_hi(tq, r);
            let c1v = veorq_u64(veorq_u64(s1, tq), u1);

            // c0 = reduce(s0 ^ x^61·s1), 192-bit fold as in mul_neon.
            let sl = vshlq_n_u64::<61>(s1);
            let sr = vshrq_n_u64::<3>(s1);
            let v = veorq_u64(
                veorq_u64(s0, sl),
                vextq_u64::<1>(vdupq_n_u64(0), sr),
            );
            let w1 = pmull_hi(v, r);
            let w2 = pmull_hi(sr, vdupq_n_u64(R128));
            let x = veorq_u64(w1, w2);
            let u0 = pmull_hi(x, r);
            let c0v = veorq_u64(veorq_u64(v, x), u0);

            let res = vtrn1q_u64(c0v, c1v);
            F128T {
                c0: vgetq_lane_u64::<0>(res),
                c1: vgetq_lane_u64::<1>(res),
            }
        }
    }
}

/// x86-64 `pclmulqdq` path — the twin of [`aarch64`] for AMD/Intel. Mirrors the
/// software reference exactly: 3 CLMUL Karatsuba sub-products over the scalar
/// coefficients, then the tower reduction `c0 = reduce(p0) + x^61·reduce(p1)`,
/// `c1 = reduce(pm + p0)`. Each GF(2^64) reduction is [`crate::field::gf2_64`]'s
/// two-CLMUL fold.
///
/// Credit: binius64 <https://github.com/binius-zk/binius64>
/// (`crates/arith-bench/src/monbijou/clmul.rs`) for the GF(2^64) base-field
/// CLMUL and the deferred-reduction structure (the base field is identical).
/// The degree-2 extension differs — this tower is Artin–Schreier `y²+y+x^61`,
/// not binius's `y²+xy+1` — so the extension reduction here follows our own
/// field's algebra rather than theirs.
#[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
pub mod x86_64 {
    use super::{C61, F128T, F128TBaseUnreduced, F128TUnreduced};
    use crate::field::gf2_64::x86_64::{clmul, reduce as kreduce};
    use core::arch::x86_64::*;

    /// `__m128i` ↔ `u128`: both are 128-bit values; the low lane is bits 0..64.
    #[inline]
    #[target_feature(enable = "sse2")]
    unsafe fn pack(v: __m128i) -> u128 {
        // SAFETY: __m128i and u128 are both 128-bit values.
        unsafe { core::mem::transmute::<__m128i, u128>(v) }
    }
    #[inline]
    #[target_feature(enable = "sse2")]
    unsafe fn unpack(x: u128) -> __m128i {
        // SAFETY: u128 and __m128i are both 128-bit values.
        unsafe { core::mem::transmute::<u128, __m128i>(x) }
    }

    /// The reduction tail of one E×E multiply applied to three carry-less parts
    /// (each a 128-bit CLMUL product). Mirrors [`super::software::mul`]:
    /// `c1 = reduce(pm ^ p0)`, `c0 = reduce(p0) ^ x^61·reduce(p1)`.
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    unsafe fn reduce_parts(p0: __m128i, p1: __m128i, pm: __m128i) -> F128T {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe {
            let rp0 = kreduce(p0);
            let rp1 = kreduce(p1);
            let c1 = kreduce(_mm_xor_si128(pm, p0)); // reduce is F2-linear
            let c0 = rp0 ^ kreduce(clmul(C61, rp1));
            F128T { c0, c1 }
        }
    }

    /// Full E × E multiply: 3 Karatsuba products + the tower reduction.
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; only call where it is
    /// statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn mul(a: F128T, b: F128T) -> F128T {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe {
            reduce_parts(
                clmul(a.c0, b.c0),
                clmul(a.c1, b.c1),
                clmul(a.c0 ^ a.c1, b.c0 ^ b.c1),
            )
        }
    }

    /// Squaring via [`mul`].
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; see [`mul`].
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn square(a: F128T) -> F128T {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe { mul(a, a) }
    }

    /// The three unreduced Karatsuba sub-products, for deferred accumulation
    /// (3 CLMUL, no reduction). Reduction is F2-linear, so callers XOR many of
    /// these and [`reduce_unreduced`] once.
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; see [`mul`].
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

    /// Reduce accumulated unreduced parts: the [`mul`] tail applied to the sums.
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; see [`mul`].
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn reduce_unreduced(u: F128TUnreduced) -> F128T {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe { reduce_parts(unpack(u.p0), unpack(u.p1), unpack(u.pm)) }
    }

    /// The two unreduced lane products of a mixed K × E multiply (2 CLMUL).
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; see [`mul`].
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn mul_base_unreduced(e: F128T, k: u64) -> F128TBaseUnreduced {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe {
            F128TBaseUnreduced {
                p0: pack(clmul(e.c0, k)),
                p1: pack(clmul(e.c1, k)),
            }
        }
    }

    /// Reduce accumulated mixed-product lanes: one GF(2^64) reduction per lane.
    ///
    /// # Safety
    /// Requires the `pclmulqdq` target feature; see [`mul`].
    #[inline]
    #[target_feature(enable = "pclmulqdq", enable = "sse2")]
    pub unsafe fn reduce_base_unreduced(u: F128TBaseUnreduced) -> F128T {
        // SAFETY: function carries the pclmulqdq+sse2 target features.
        unsafe {
            F128T {
                c0: kreduce(unpack(u.p0)),
                c1: kreduce(unpack(u.p1)),
            }
        }
    }
}

pub mod software {
    use super::{C61, F64, F128T, F128TUnreduced, base_reduce_128};
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

    pub fn reduce_unreduced(u: F128TUnreduced) -> F128T {
        let red = |p: u128| base_reduce_128(p as u64, (p >> 64) as u64);
        let (p0, p1, pm) = (red(u.p0), red(u.p1), red(u.pm));
        F128T {
            c0: p0 ^ kmul(C61, p1),
            c1: pm ^ p0,
        }
    }

    pub fn mul_base_unreduced(e: F128T, k: F64) -> super::F128TBaseUnreduced {
        let cl = |a: u64, b: u64| {
            let (lo, hi) = clmul64(a, b);
            lo as u128 | ((hi as u128) << 64)
        };
        super::F128TBaseUnreduced {
            p0: cl(e.c0, k.0),
            p1: cl(e.c1, k.0),
        }
    }

    pub fn reduce_base_unreduced(u: super::F128TBaseUnreduced) -> F128T {
        let red = |p: u128| base_reduce_128(p as u64, (p >> 64) as u64);
        F128T {
            c0: red(u.p0),
            c1: red(u.p1),
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

    /// Every NEON kernel variant agrees with the software reference.
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn neon_variants_match_software() {
        let mut s = 11u64;
        for _ in 0..10_000 {
            let (a, b) = (rand_e(&mut s), rand_e(&mut s));
            let k = splitmix64(&mut s);
            let want = software::mul(a, b);
            let want_base = F128T {
                c0: (F64(a.c0) * F64(k)).0,
                c1: (F64(a.c1) * F64(k)).0,
            };
            // SAFETY: aes target feature is enabled at compile time.
            unsafe {
                assert_eq!(aarch64::mul_neon(a, b), want);
                assert_eq!(aarch64::mul_shift_tail(a, b), want);
                assert_eq!(aarch64::mul_serial_fold(a, b), want);
                assert_eq!(aarch64::mul_schoolbook(a, b), want);
                assert_eq!(aarch64::mul_schoolbook_shift_tail(a, b), want);
                assert_eq!(aarch64::mul_karatsuba_vec(a, b), want);
                assert_eq!(aarch64::mul_base_neon(a, k), want_base);
                assert_eq!(aarch64::mul_base_pmull4(a, k), want_base);
                assert_eq!(aarch64::mul_base_shift_tail(a, k), want_base);
                assert_eq!(aarch64::square_neon(a), software::square(a));
            }
        }
    }

    /// Every x86-64 pclmulqdq kernel agrees with the software reference,
    /// including the deferred-reduction paths (mul_unreduced/reduce_unreduced
    /// and mul_base_unreduced/reduce_base_unreduced) the sumcheck loop uses.
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    #[test]
    fn x86_variants_match_software() {
        let mut s = 17u64;
        for _ in 0..10_000 {
            let (a, b) = (rand_e(&mut s), rand_e(&mut s));
            let k = splitmix64(&mut s);
            let want = software::mul(a, b);
            let want_base = F128T {
                c0: (F64(a.c0) * F64(k)).0,
                c1: (F64(a.c1) * F64(k)).0,
            };
            // SAFETY: pclmulqdq target feature is enabled at compile time.
            unsafe {
                assert_eq!(x86_64::mul(a, b), want);
                assert_eq!(x86_64::square(a), software::square(a));
                // Deferred E×E: one unreduced product reduces to the product.
                assert_eq!(x86_64::mul_unreduced(a, b).reduce(), want);
                // Deferred K×E mixed product.
                assert_eq!(x86_64::mul_base_unreduced(a, k).reduce(), want_base);
            }
        }
    }

    /// A single deferred product reduces to the plain product, and a XOR of
    /// many unreduced products reduces to the sum of the reduced ones
    /// (reduction is GF(2)-linear) — on both the NEON and software paths.
    #[test]
    fn deferred_reduction_matches() {
        let mut s = 13u64;
        for _ in 0..10_000 {
            let (a, b) = (rand_e(&mut s), rand_e(&mut s));
            assert_eq!(a.mul_unreduced(b).reduce(), a * b);
        }
        for n in [1usize, 2, 3, 17, 256] {
            let terms: Vec<(F128T, F128T)> = (0..n).map(|_| (rand_e(&mut s), rand_e(&mut s))).collect();
            let mut acc = F128TUnreduced::ZERO;
            let mut want = F128T::ZERO;
            for &(a, b) in &terms {
                acc ^= a.mul_unreduced(b);
                want = want + a * b;
            }
            assert_eq!(acc.reduce(), want, "n={n}");
            // The software path agrees term-for-term with the NEON path.
            let mut acc_sw = F128TUnreduced::ZERO;
            for &(a, b) in &terms {
                acc_sw ^= software::mul_unreduced(a, b);
            }
            assert_eq!(acc_sw, acc, "unreduced parts diverge (n={n})");
            assert_eq!(software::reduce_unreduced(acc_sw), want, "software reduce (n={n})");
            #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
            {
                let (av, bv): (Vec<F128T>, Vec<F128T>) = terms.iter().copied().unzip();
                // SAFETY: aes target feature is enabled at compile time.
                unsafe {
                    assert_eq!(aarch64::inner_unreduced_neon(&av, &bv), want, "kernel (n={n})");
                }
            }
        }
    }

    #[test]
    fn mul2_matches_scalar() {
        let mut s = 7u64;
        for _ in 0..10_000 {
            let a = [rand_e(&mut s), rand_e(&mut s)];
            let b = [rand_e(&mut s), rand_e(&mut s)];
            assert_eq!(F128T::mul2(a, b), [a[0] * b[0], a[1] * b[1]]);
        }
        // Edge lanes: zero/one in either slot.
        let x = rand_e(&mut s);
        for e in [F128T::ZERO, F128T::ONE, F128T::Y] {
            assert_eq!(F128T::mul2([e, x], [x, e]), [e * x, x * e]);
        }
    }

    /// Kernel timing probe, scalar vs [`F128T::mul2`], throughput- and
    /// latency-bound (run with
    /// `cargo test --release --lib -- --ignored bench_mul2 --nocapture`).
    /// On Apple M-series the pair kernel wins ~5% on independent-product
    /// throughput and ~40% on serial dependence chains; loops whose muls the
    /// OoO core already overlaps see only the former.
    #[test]
    #[ignore]
    fn bench_mul2_kernel() {
        use std::hint::black_box;
        use std::time::Instant;
        let mut s = 9u64;
        let n = 1usize << 12;
        let a: Vec<F128T> = (0..n).map(|_| rand_e(&mut s)).collect();
        let b: Vec<F128T> = (0..n).map(|_| rand_e(&mut s)).collect();
        let mut out = vec![F128T::ZERO; n];
        let iters = 20_000usize;
        let total = (n * iters) as f64;

        let t0 = Instant::now();
        for _ in 0..iters {
            for i in 0..n {
                out[i] = a[i] * b[i];
            }
            black_box(&mut out);
        }
        let scalar_tp = t0.elapsed().as_secs_f64() / total * 1e9;

        let t0 = Instant::now();
        for _ in 0..iters {
            for i in 0..n / 2 {
                let m = F128T::mul2([a[2 * i], a[2 * i + 1]], [b[2 * i], b[2 * i + 1]]);
                out[2 * i] = m[0];
                out[2 * i + 1] = m[1];
            }
            black_box(&mut out);
        }
        let mul2_tp = t0.elapsed().as_secs_f64() / total * 1e9;

        // Latency-bound: one serial chain vs two chains through mul2.
        let iters_lat = 4_000usize;
        let t0 = Instant::now();
        let mut acc = F128T::ONE;
        for _ in 0..iters_lat {
            for i in 0..n {
                acc = (acc + a[i]) * b[i];
            }
        }
        black_box(acc);
        let scalar_lat = t0.elapsed().as_secs_f64() / (n * iters_lat) as f64 * 1e9;

        let t0 = Instant::now();
        let mut acc2 = [F128T::ONE, F128T::Y];
        for _ in 0..iters_lat {
            for i in 0..n / 2 {
                acc2 = F128T::mul2(
                    [acc2[0] + a[2 * i], acc2[1] + a[2 * i + 1]],
                    [b[2 * i], b[2 * i + 1]],
                );
            }
        }
        black_box(acc2);
        let mul2_lat = t0.elapsed().as_secs_f64() / (n * iters_lat) as f64 * 1e9;

        eprintln!("throughput ns/mul: scalar {scalar_tp:.3}  mul2 {mul2_tp:.3}");
        eprintln!("latency    ns/mul: scalar {scalar_lat:.3}  mul2(2 chains) {mul2_lat:.3}");
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
