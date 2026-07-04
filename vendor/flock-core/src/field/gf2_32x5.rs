//! GF((2^32)^5) — a 160-bit binary extension field ("option C" for >128-bit
//! security).
//!
//! Base field K = GF(2^32) = GF(2)[x]/(x^32 + x^7 + x^3 + x^2 + 1), the
//! standard low-weight irreducible pentanomial for degree 32 (no degree-32
//! trinomial exists). Fold constant `R32 = 0x8D` (x^7 + x^3 + x^2 + 1).
//!
//! Extension: K[y]/(y^5 + y^2 + 1). y^5 + y^2 + 1 is irreducible over GF(2)
//! and gcd(5, 32) = 1, so it stays irreducible over K (an irreducible degree-d
//! polynomial over GF(2) splits into gcd(d, k) factors over GF(2^k)); the
//! tests re-verify this computationally.
//!
//! Layout: `c[i]` = coefficient of y^i, each a GF(2^32) element.
//!
//! Hardware strategy (aarch64 + AES/PMULL):
//! - a base 32×32 product uses one `vmull_p64`; the result has degree ≤ 62 so
//!   it fits entirely in the low 64-bit lane. PMULL has no 32-bit form, so
//!   half of each multiplier is wasted — the structural handicap of this
//!   field. Packing two 32-bit coefficients per PMULL operand does NOT work:
//!   the three sub-products overlap at 32-bit offsets and the individual
//!   coefficients are information-theoretically unrecoverable from the XOR
//!   overlay (e.g. x^32·y^0 and 1·y^1 pack identically but reduce
//!   differently).
//! - product coefficients c0..c8 are combined with plain u64 XORs on the
//!   scalar side; three product schemes are provided:
//!     * `mul_montgomery` — Montgomery's 5-term formula (IEEE ToC 54(3),
//!       2005; US patent 7,765,252), 13 PMULL — the minimum known bilinear
//!       count for 5 terms. In char 2 all signs and even coefficients vanish.
//!       Default `Mul` implementation.
//!     * `mul_karatsuba` — two-level (2,3)-split Karatsuba, 15 PMULL but
//!       fewer XORs;
//!     * `mul_schoolbook` — 25 PMULL, zero input-sum overhead.
//! - y-fold (y^5 = y^2 + 1) and the per-coefficient base reduction are pure
//!   shift-XORs on the scalar side: both folds of x^32 ≡ x^7+x^3+x^2+1 run on
//!   the (otherwise idle) integer ALUs instead of adding 5 more PMULLs.

use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};

use serde::{Deserialize, Serialize};

/// Reduction constant of the base field: x^32 ≡ x^7 + x^3 + x^2 + 1.
pub const R32: u32 = 0x8D;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub struct F160 {
    /// `c[i]` = coefficient of y^i.
    pub c: [u32; 5],
}

impl F160 {
    pub const ZERO: Self = Self { c: [0; 5] };
    pub const ONE: Self = Self { c: [1, 0, 0, 0, 0] };
    /// The element `y` (root of y^5 + y^2 + 1 over the base field).
    pub const Y: Self = Self { c: [0, 1, 0, 0, 0] };

    #[inline]
    pub const fn new(c: [u32; 5]) -> Self {
        Self { c }
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        (self.c[0] | self.c[1] | self.c[2] | self.c[3] | self.c[4]) == 0
    }

    /// Unreduced product: the 9 raw ≤63-bit polynomial coefficients, before
    /// the y-fold and base reductions. XOR-accumulate many of these and
    /// `.reduce()` once — both folds are GF(2)-linear, so they commute with
    /// XOR (and ≤63-bit values stay ≤63 bits under XOR; nothing overflows).
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> F160Unreduced {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_unreduced_neon(self, rhs) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            software::mul_unreduced(self, rhs)
        }
    }

    /// Squaring. Char-2 cross terms vanish: squares land on y^0..y^8 even
    /// powers only — 5 PMULL + folds instead of 13.
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

    /// Multiplicative inverse via Fermat: self^(2^160 − 2) = ∏_{i=1..159} self^(2^i).
    /// One-time-setup speed class, not a hot path. `ZERO.inv() == ZERO`.
    pub fn inv(self) -> Self {
        let mut cur = self.square();
        let mut r = cur;
        for _ in 2..160 {
            cur = cur.square();
            r *= cur;
        }
        r
    }
}

impl Add for F160 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            c: [
                self.c[0] ^ rhs.c[0],
                self.c[1] ^ rhs.c[1],
                self.c[2] ^ rhs.c[2],
                self.c[3] ^ rhs.c[3],
                self.c[4] ^ rhs.c[4],
            ],
        }
    }
}

impl AddAssign for F160 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..5 {
            self.c[i] ^= rhs.c[i];
        }
    }
}

impl Mul for F160 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_montgomery(self, rhs) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            software::mul(self, rhs)
        }
    }
}

impl MulAssign for F160 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---------------------------------------------------------------------------
// Deferred reduction: 9 unreduced ≤63-bit coefficients, XOR-accumulable.
// ---------------------------------------------------------------------------

/// Unreduced F160 product: the degree-8 polynomial product over K before any
/// reduction. `w[k]` = the ≤63-bit carry-less coefficient of y^k.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F160Unreduced {
    pub w: [u64; 9],
}

impl F160Unreduced {
    pub const ZERO: Self = Self { w: [0; 9] };

    #[inline]
    pub fn reduce(self) -> F160 {
        let [c0, c1, c2, c3, c4, c5, c6, c7, c8] = self.w;
        // y-fold: y^5 = y^2 + 1 ⇒ y^6 = y^3+y, y^7 = y^4+y^2, y^8 = y^3+y^2+1.
        let d0 = c0 ^ c5 ^ c8;
        let d1 = c1 ^ c6;
        let d2 = c2 ^ c5 ^ c7 ^ c8;
        let d3 = c3 ^ c6 ^ c8;
        let d4 = c4 ^ c7;
        F160 {
            c: [
                base_reduce_64(d0),
                base_reduce_64(d1),
                base_reduce_64(d2),
                base_reduce_64(d3),
                base_reduce_64(d4),
            ],
        }
    }
}

impl BitXor for F160Unreduced {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        let mut w = self.w;
        for i in 0..9 {
            w[i] ^= rhs.w[i];
        }
        Self { w }
    }
}

impl BitXorAssign for F160Unreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        for i in 0..9 {
            self.w[i] ^= rhs.w[i];
        }
    }
}

// ---------------------------------------------------------------------------
// Base-field reduction mod x^32 + x^7 + x^3 + x^2 + 1. Works on any target.
// ---------------------------------------------------------------------------

/// Fold a ≤63-bit carry-less product into GF(2^32).
/// x^32 ≡ x^7+x^3+x^2+1, so U·x^32 ≡ U ^ U<<2 ^ U<<3 ^ U<<7. The first fold
/// leaves ≤6 dirty bits above position 31; their contribution `s` is computed
/// directly from `hi` (in parallel with the first fold — shallower dependency
/// chain than two sequential passes) and folded once more, exactly.
#[inline]
pub const fn base_reduce_64(t: u64) -> u32 {
    let hi = t >> 32; // ≤ 31 bits
    let s = (hi >> 30) ^ (hi >> 29) ^ (hi >> 25); // bits of hi·0x8D above 31
    let f = hi ^ (hi << 2) ^ (hi << 3) ^ (hi << 7);
    let g = s ^ (s << 2) ^ (s << 3) ^ (s << 7); // ≤ 13 bits, exact
    (t ^ f ^ g) as u32
}

/// Portable base-field helpers (reference-grade; tests and setup only).
pub mod base {
    use super::base_reduce_64;
    use crate::field::gf2_128::software::clmul64;

    /// GF(2^32) multiply: carry-less 32×32 then fold.
    pub fn mul(a: u32, b: u32) -> u32 {
        let (lo, _) = clmul64(a as u64, b as u64); // deg ≤ 62: fits in lo
        base_reduce_64(lo)
    }

    pub fn square(a: u32) -> u32 {
        mul(a, a)
    }

    /// Fermat inverse in GF(2^32): a^(2^32 − 2).
    pub fn inv(a: u32) -> u32 {
        let mut cur = square(a);
        let mut r = cur;
        for _ in 2..32 {
            cur = square(cur);
            r = mul(r, cur);
        }
        r
    }
}

// ---------------------------------------------------------------------------
// aarch64 + AES: PMULL-based multiplication variants.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
pub mod aarch64 {
    use super::{F160, F160Unreduced, base_reduce_64};
    use core::arch::aarch64::*;

    /// 32×32 carry-less product. Degree ≤ 62, so the whole product is the low
    /// 64 bits of the PMULL result; the high lane is zero and discarded.
    ///
    /// # Safety
    /// Requires the `aes` target feature (statically satisfied: every caller
    /// is itself `#[target_feature(enable = "aes")]`).
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn clmul32(a: u32, b: u32) -> u64 {
        // SAFETY: function carries the aes target feature.
        unsafe { vmull_p64(a as u64, b as u64) as u64 }
    }

    /// y-fold + per-coefficient base reduction of the 9 raw product
    /// coefficients (shared tail of all product schemes).
    #[inline]
    fn fold_and_reduce(c: [u64; 9]) -> F160 {
        F160Unreduced { w: c }.reduce()
    }

    /// Montgomery's 5-term Karatsuba-like formula (13 PMULL — minimum known
    /// bilinear count for 5-term polynomials), reduced mod 2 so all signs and
    /// even coefficients vanish. Verified against schoolbook in the tests.
    /// Default `Mul` implementation.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_montgomery(a: F160, b: F160) -> F160 {
        let [a0, a1, a2, a3, a4] = a.c;
        let [b0, b1, b2, b3, b4] = b.c;

        // Shared operand sums (11 XORs per side).
        let (ta01, tb01) = (a0 ^ a1, b0 ^ b1);
        let (ta34, tb34) = (a3 ^ a4, b3 ^ b4);
        let (ta04, tb04) = (a0 ^ a4, b0 ^ b4);
        let (ta02, tb02) = (a0 ^ a2, b0 ^ b2);
        let (ta24, tb24) = (a2 ^ a4, b2 ^ b4);
        let (sa0134, sb0134) = (ta01 ^ ta34, tb01 ^ tb34);

        // SAFETY: function carries the aes target feature.
        unsafe {
            let p = clmul32(sa0134 ^ a2, sb0134 ^ b2); // (a0+a1+a2+a3+a4)(…)
            let q = clmul32(ta02 ^ ta34, tb02 ^ tb34); // (a0+a2+a3+a4)(…)
            let r = clmul32(ta01 ^ ta24, tb01 ^ tb24); // (a0+a1+a2+a4)(…)
            let s = clmul32(sa0134, sb0134); //           (a0+a1+a3+a4)(…)
            let t = clmul32(ta02 ^ a3, tb02 ^ b3); //     (a0+a2+a3)(…)
            let u = clmul32(a1 ^ ta24, b1 ^ tb24); //     (a1+a2+a4)(…)
            let v = clmul32(ta34, tb34); //               (a3+a4)(…)
            let w = clmul32(ta01, tb01); //               (a0+a1)(…)
            let x = clmul32(ta04, tb04); //               (a0+a4)(…)
            let m0 = clmul32(a0, b0);
            let m1 = clmul32(a1, b1);
            let m3 = clmul32(a3, b3);
            let m4 = clmul32(a4, b4);

            // Char-2 reconstruction (US 7,765,252 with signs/even terms dropped).
            let x40 = x ^ m4 ^ m0;
            let psx = p ^ s ^ x;
            fold_and_reduce([
                m0,
                w ^ m1 ^ m0,
                r ^ u ^ w ^ x40,
                psx ^ q ^ v ^ m4,
                p ^ t ^ u ^ v ^ w ^ m4 ^ m3 ^ m1 ^ m0,
                psx ^ r ^ w ^ m0,
                q ^ t ^ v ^ x40,
                v ^ m3 ^ m4,
                m4,
            ])
        }
    }

    /// Two-level (2,3)-split Karatsuba: A = L + y²·H with L = a0+a1y and
    /// H = a2+a3y+a4y². M(2)=3 + two M(3)=6 blocks → 15 PMULL, fewer
    /// combination XORs than Montgomery. Benchmark variant.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_montgomery`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_karatsuba(a: F160, b: F160) -> F160 {
        let [a0, a1, a2, a3, a4] = a.c;
        let [b0, b1, b2, b3, b4] = b.c;

        // SAFETY: function carries the aes target feature.
        unsafe {
            // L·L' (2-term Karatsuba, 3 products): coeffs l0..l2.
            let p0 = clmul32(a0, b0);
            let p1 = clmul32(a1, b1);
            let p01 = clmul32(a0 ^ a1, b0 ^ b1);
            let (l0, l1, l2) = (p0, p01 ^ p0 ^ p1, p1);

            // H·H' (3-term Karatsuba, 6 products): coeffs h0..h4.
            let q0 = clmul32(a2, b2);
            let q1 = clmul32(a3, b3);
            let q2 = clmul32(a4, b4);
            let q01 = clmul32(a2 ^ a3, b2 ^ b3);
            let q02 = clmul32(a2 ^ a4, b2 ^ b4);
            let q12 = clmul32(a3 ^ a4, b3 ^ b4);
            let (h0, h1, h2, h3, h4) = (q0, q01 ^ q0 ^ q1, q02 ^ q0 ^ q1 ^ q2, q12 ^ q1 ^ q2, q2);

            // (L+H)·(L'+H') (3-term Karatsuba, 6 products): coeffs m0..m4.
            let (u0, u1, u2) = (a0 ^ a2, a1 ^ a3, a4);
            let (v0, v1, v2) = (b0 ^ b2, b1 ^ b3, b4);
            let r0 = clmul32(u0, v0);
            let r1 = clmul32(u1, v1);
            let r2 = clmul32(u2, v2);
            let r01 = clmul32(u0 ^ u1, v0 ^ v1);
            let r02 = clmul32(u0 ^ u2, v0 ^ v2);
            let r12 = clmul32(u1 ^ u2, v1 ^ v2);
            let (m0, m1, m2, m3, m4) = (r0, r01 ^ r0 ^ r1, r02 ^ r0 ^ r1 ^ r2, r12 ^ r1 ^ r2, r2);

            // A·B = L·L' + y²·(M + L·L' + H·H') + y⁴·H·H'.
            fold_and_reduce([
                l0,
                l1,
                l2 ^ m0 ^ l0 ^ h0,
                m1 ^ l1 ^ h1,
                m2 ^ l2 ^ h2 ^ h0,
                m3 ^ h3 ^ h1,
                m4 ^ h4 ^ h2,
                h3,
                h4,
            ])
        }
    }

    /// Schoolbook: 25 independent PMULL products, 16 combination XORs, zero
    /// input-sum overhead. Benchmark variant.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_montgomery`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_schoolbook(a: F160, b: F160) -> F160 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let mut c = [0u64; 9];
            for i in 0..5 {
                for j in 0..5 {
                    c[i + j] ^= clmul32(a.c[i], b.c[j]);
                }
            }
            fold_and_reduce(c)
        }
    }

    /// Karatsuba-15 products only — no reduction at all. The caller
    /// XOR-accumulates the raw coefficients (inner products, sumcheck-style).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_montgomery`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_unreduced_neon(a: F160, b: F160) -> F160Unreduced {
        let [a0, a1, a2, a3, a4] = a.c;
        let [b0, b1, b2, b3, b4] = b.c;

        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = clmul32(a0, b0);
            let p1 = clmul32(a1, b1);
            let p01 = clmul32(a0 ^ a1, b0 ^ b1);
            let (l0, l1, l2) = (p0, p01 ^ p0 ^ p1, p1);

            let q0 = clmul32(a2, b2);
            let q1 = clmul32(a3, b3);
            let q2 = clmul32(a4, b4);
            let q01 = clmul32(a2 ^ a3, b2 ^ b3);
            let q02 = clmul32(a2 ^ a4, b2 ^ b4);
            let q12 = clmul32(a3 ^ a4, b3 ^ b4);
            let (h0, h1, h2, h3, h4) = (q0, q01 ^ q0 ^ q1, q02 ^ q0 ^ q1 ^ q2, q12 ^ q1 ^ q2, q2);

            let (u0, u1, u2) = (a0 ^ a2, a1 ^ a3, a4);
            let (v0, v1, v2) = (b0 ^ b2, b1 ^ b3, b4);
            let r0 = clmul32(u0, v0);
            let r1 = clmul32(u1, v1);
            let r2 = clmul32(u2, v2);
            let r01 = clmul32(u0 ^ u1, v0 ^ v1);
            let r02 = clmul32(u0 ^ u2, v0 ^ v2);
            let r12 = clmul32(u1 ^ u2, v1 ^ v2);
            let (m0, m1, m2, m3, m4) = (r0, r01 ^ r0 ^ r1, r02 ^ r0 ^ r1 ^ r2, r12 ^ r1 ^ r2, r2);

            F160Unreduced {
                w: [
                    l0,
                    l1,
                    l2 ^ m0 ^ l0 ^ h0,
                    m1 ^ l1 ^ h1,
                    m2 ^ l2 ^ h2 ^ h0,
                    m3 ^ h3 ^ h1,
                    m4 ^ h4 ^ h2,
                    h3,
                    h4,
                ],
            }
        }
    }

    /// Squaring: cross terms vanish, squares land on y^0, y^2, y^4, y^6, y^8.
    /// 5 PMULL + folds (y^6 = y^3+y, y^8 = y^3+y^2+1).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_montgomery`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn square_neon(a: F160) -> F160 {
        let [a0, a1, a2, a3, a4] = a.c;
        // SAFETY: function carries the aes target feature.
        unsafe {
            let s0 = clmul32(a0, a0);
            let s1 = clmul32(a1, a1);
            let s2 = clmul32(a2, a2);
            let s3 = clmul32(a3, a3);
            let s4 = clmul32(a4, a4);
            F160 {
                c: [
                    base_reduce_64(s0 ^ s4),
                    base_reduce_64(s3),
                    base_reduce_64(s1 ^ s4),
                    base_reduce_64(s3 ^ s4),
                    base_reduce_64(s2),
                ],
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Software fallback: portable, also the reference the NEON path is tested
// against.
// ---------------------------------------------------------------------------

pub mod software {
    use super::{F160, F160Unreduced, base_reduce_64};
    use crate::field::gf2_128::software::clmul64;

    /// Schoolbook 25-product unreduced coefficients.
    pub fn mul_unreduced(a: F160, b: F160) -> F160Unreduced {
        let mut c = [0u64; 9];
        for i in 0..5 {
            for j in 0..5 {
                let (lo, _) = clmul64(a.c[i] as u64, b.c[j] as u64);
                c[i + j] ^= lo;
            }
        }
        F160Unreduced { w: c }
    }

    pub fn mul(a: F160, b: F160) -> F160 {
        mul_unreduced(a, b).reduce()
    }

    pub fn square(a: F160) -> F160 {
        let mut s = [0u64; 5];
        for i in 0..5 {
            let (lo, _) = clmul64(a.c[i] as u64, a.c[i] as u64);
            s[i] = lo;
        }
        F160 {
            c: [
                base_reduce_64(s[0] ^ s[4]),
                base_reduce_64(s[3]),
                base_reduce_64(s[1] ^ s[4]),
                base_reduce_64(s[3] ^ s[4]),
                base_reduce_64(s[2]),
            ],
        }
    }
}

// ---------------------------------------------------------------------------
// Tests: NEON vs software, independent Python vectors, field axioms, and
// computational irreducibility proofs for both moduli.
// ---------------------------------------------------------------------------

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

    fn rand_elem(s: &mut u64) -> F160 {
        let (a, b, c) = (splitmix64(s), splitmix64(s), splitmix64(s));
        F160::new([a as u32, (a >> 32) as u32, b as u32, (b >> 32) as u32, c as u32])
    }

    /// Vectors generated by an independent Python implementation
    /// (scratchpad/fieldref.py): (a, b, a·b, a·a).
    const VECTORS: [([u32; 5], [u32; 5], [u32; 5], [u32; 5]); 4] = [
        (
            [0x8d29b146, 0x7a2f1108, 0x6fc24b83, 0xda10faaa, 0x2fcb9940],
            [0x2de288f1, 0xef041066, 0xb98937df, 0xd355871e, 0xdd4b712e],
            [0x6dabd0ed, 0xdf39e1ac, 0xf9b8d474, 0xe36ae53d, 0xa4774f06],
            [0x725db70d, 0x6930dd1b, 0x1534b8f8, 0x35737df8, 0xdd47d743],
        ),
        (
            [0x4a2e3224, 0xc5b79031, 0xfa017ed7, 0x07fdc889, 0x1198bf15],
            [0x81eeadd7, 0x425a7de1, 0x3a46305c, 0x66e0440d, 0xaaabc8d3],
            [0x784e56bd, 0xa436a1ed, 0x4c038a52, 0xfdc62e33, 0x9c7e5918],
            [0x3c89f28d, 0x5a00425c, 0x11870d66, 0x92fbad0d, 0x1d2044dd],
        ),
        (
            [0xc51d1a5e, 0x3371364f, 0x1ac44b70, 0x4763dd19, 0x5646e6d0],
            [0x016590c5, 0x81e4b9e7, 0x0b7a6e1d, 0xf16e981a, 0xe5a2a8be],
            [0xb5194f7f, 0x61fe980e, 0x84ff775a, 0x7aca9664, 0x1e7bd6b9],
            [0x9ae12c9a, 0x8b32e390, 0xbd5ff74e, 0x88ca6c1c, 0xbc1a8dd0],
        ),
        (
            [0xa2927979, 0x1167fba4, 0x1b534b87, 0x3d01ac0f, 0x5532c867],
            [0xd27a5f0f, 0x358b24d3, 0xee26cbc0, 0xca3c6a00, 0x9bdb39b2],
            [0xee96fc6d, 0xf7767e73, 0xe5f2fb6c, 0xefc4a234, 0x5855d798],
            [0x66496011, 0xd64d01c2, 0xdddd0130, 0xd352aa8b, 0xbcb41fac],
        ),
    ];

    #[test]
    fn python_vectors() {
        for (a, b, c, s) in VECTORS {
            let (a, b) = (F160::new(a), F160::new(b));
            assert_eq!(a * b, F160::new(c));
            assert_eq!(a.square(), F160::new(s));
            assert_eq!(software::mul(a, b), F160::new(c));
        }
    }

    #[test]
    fn identities() {
        let mut s = 1u64;
        for _ in 0..100 {
            let a = rand_elem(&mut s);
            assert_eq!(a * F160::ONE, a);
            assert_eq!(a * F160::ZERO, F160::ZERO);
            assert_eq!(a + F160::ZERO, a);
            assert_eq!(a + a, F160::ZERO);
        }
        // y^5 = y^2 + 1
        let y2 = F160::Y * F160::Y;
        let y5 = y2 * y2 * F160::Y;
        assert_eq!(y5, y2 + F160::ONE);
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    #[test]
    fn neon_variants_match_software() {
        let mut s = 2u64;
        for _ in 0..10_000 {
            let a = rand_elem(&mut s);
            let b = rand_elem(&mut s);
            let want = software::mul(a, b);
            // SAFETY: cfg-gated on the aes target feature.
            unsafe {
                assert_eq!(aarch64::mul_montgomery(a, b), want);
                assert_eq!(aarch64::mul_karatsuba(a, b), want);
                assert_eq!(aarch64::mul_schoolbook(a, b), want);
                assert_eq!(aarch64::mul_unreduced_neon(a, b).reduce(), want);
                assert_eq!(aarch64::square_neon(a), software::square(a));
            }
        }
    }

    #[test]
    fn axioms() {
        let mut s = 3u64;
        for _ in 0..1_000 {
            let a = rand_elem(&mut s);
            let b = rand_elem(&mut s);
            let c = rand_elem(&mut s);
            assert_eq!(a * b, b * a);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
        }
    }

    #[test]
    fn square_and_inv() {
        let mut s = 4u64;
        for _ in 0..50 {
            let a = rand_elem(&mut s);
            assert_eq!(a.square(), a * a);
            if !a.is_zero() {
                assert_eq!(a * a.inv(), F160::ONE);
            }
        }
        assert_eq!(F160::ZERO.inv(), F160::ZERO);
    }

    #[test]
    fn unreduced_accumulation_matches_reduced_sum() {
        let mut s = 5u64;
        for _ in 0..100 {
            let pairs: Vec<(F160, F160)> = (0..16).map(|_| (rand_elem(&mut s), rand_elem(&mut s))).collect();
            let mut acc = F160Unreduced::ZERO;
            let mut want = F160::ZERO;
            for &(a, b) in &pairs {
                acc ^= a.mul_unreduced(b);
                want += a * b;
            }
            assert_eq!(acc.reduce(), want);
        }
    }

    // -- GF(2)[x] helpers on u64 for the base-polynomial irreducibility test.

    fn gf2_mod(mut a: u64, m: u64) -> u64 {
        let dm = 63 - m.leading_zeros();
        while a != 0 {
            let da = 63 - a.leading_zeros();
            if da < dm {
                break;
            }
            a ^= m << (da - dm);
        }
        a
    }

    fn gf2_gcd(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let r = gf2_mod(a, b);
            a = b;
            b = r;
        }
        a
    }

    /// Rabin: p32 (degree 32 = 2^5) is irreducible iff x^(2^32) ≡ x mod p32
    /// and gcd(x^(2^16) − x, p32) = 1.
    #[test]
    fn base_poly_irreducible() {
        const P32: u64 = (1u64 << 32) | (R32 as u64);
        let mut t = 2u32; // the element x
        for _ in 0..16 {
            t = base::square(t);
        }
        assert_eq!(gf2_gcd((t as u64) ^ 2, P32), 1, "factor of degree | 16");
        for _ in 0..16 {
            t = base::square(t);
        }
        assert_eq!(t, 2, "x^(2^32) != x mod p32");
    }

    // -- K[y] gcd for the extension-polynomial irreducibility test.

    fn pdeg(p: &[u32]) -> Option<usize> {
        p.iter().rposition(|&c| c != 0)
    }

    fn poly_mod(mut a: Vec<u32>, b: &[u32]) -> Vec<u32> {
        let db = pdeg(b).expect("mod by zero poly");
        let lead_inv = base::inv(b[db]);
        while let Some(da) = pdeg(&a) {
            if da < db {
                break;
            }
            let q = base::mul(a[da], lead_inv);
            for i in 0..=db {
                a[da - db + i] ^= base::mul(q, b[i]);
            }
        }
        a
    }

    fn poly_gcd(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
        while pdeg(&b).is_some() {
            let r = poly_mod(a, &b);
            a = b;
            b = r;
        }
        a
    }

    /// A quintic is irreducible over K iff it has no factor of degree 1 or 2:
    /// gcd(y^|K| − y, f) = 1 and gcd(y^|K|² − y, f) = 1. The Frobenius powers
    /// y^(2^32) and y^(2^64) are computed as repeated squarings of the element
    /// y in the quotient ring (which is exactly F160).
    #[test]
    fn extension_poly_irreducible_over_base() {
        let f = vec![1u32, 0, 1, 0, 0, 1]; // y^5 + y^2 + 1
        let mut t = F160::Y;
        for _ in 0..32 {
            t = t.square();
        }
        let d1 = t + F160::Y;
        assert!(!d1.is_zero());
        let g1 = poly_gcd(f.clone(), d1.c.to_vec());
        assert_eq!(pdeg(&g1), Some(0), "y^5+y^2+1 has a root in GF(2^32)");

        for _ in 0..32 {
            t = t.square();
        }
        let d2 = t + F160::Y;
        assert!(!d2.is_zero());
        let g2 = poly_gcd(f, d2.c.to_vec());
        assert_eq!(pdeg(&g2), Some(0), "y^5+y^2+1 has a quadratic factor");
    }

    #[test]
    fn serde_roundtrip() {
        let a = F160::new([0x01234567, 0x89abcdef, 0xfedcba98, 0x76543210, 0x13579bdf]);
        let ser = bincode::serialize(&a).unwrap();
        assert_eq!(bincode::deserialize::<F160>(&ser).unwrap(), a);
    }
}
