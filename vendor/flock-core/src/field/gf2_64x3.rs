//! GF((2^64)^3) — a 192-bit binary tower field ("option B" for >128-bit security).
//!
//! Base field K = GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), the standard
//! low-weight irreducible pentanomial for degree 64. Its fold constant is
//! `R64 = 0x1B` (x^4 + x^3 + x + 1), so x^64 ≡ U ^ U<<1 ^ U<<3 ^ U<<4.
//!
//! Extension: K[y]/(y^3 + y + 1). y^3 + y + 1 is irreducible over GF(2), and an
//! irreducible degree-d polynomial over GF(2) splits into gcd(d, k) factors over
//! GF(2^k) — gcd(3, 64) = 1, so it stays irreducible over K (the tests
//! re-verify this computationally via Frobenius + gcd).
//!
//! Layout: coefficients `c0 + c1·y + c2·y²`, each a GF(2^64) element (bit i of
//! `cj` = coeff of x^i).
//!
//! Hardware strategy (aarch64 + AES/PMULL):
//! - one base-field 64×64 product = one `vmull_p64`;
//! - extension mult = 3-term Karatsuba (6 PMULL, optimal for 3-term bilinear
//!   over GF(2)) producing 5 unreduced 128-bit coefficients;
//! - y-fold (y³ = y+1, y⁴ = y²+y) on the unreduced coefficients — 4 NEON XORs;
//! - base reduction per coefficient: 1 PMULL by 0x1B; the ≤4-bit overflow is
//!   folded with 3 scalar shift-XORs (0x1B·overflow fits in 8 bits, exact).
//!
//! Total: 9 PMULL per mult (vs 6 for F128's GHASH). Squaring drops the cross
//! terms (char 2): 3 PMULL + 3 reduction PMULL = 6.
//!
//! Why no packed-lane tricks: PMULL is one 64×64 product per instruction; base
//! coefficients already fill the operand exactly, so — unlike GF(2^32) — no
//! width is wasted.

use core::ops::{Add, AddAssign, BitXor, BitXorAssign, Mul, MulAssign};

use serde::{Deserialize, Serialize};

/// Reduction constant of the base field: x^64 ≡ x^4 + x^3 + x + 1.
pub const R64: u64 = 0x1B;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub struct F192 {
    pub c0: u64,
    pub c1: u64,
    pub c2: u64,
}

impl F192 {
    pub const ZERO: Self = Self { c0: 0, c1: 0, c2: 0 };
    pub const ONE: Self = Self { c0: 1, c1: 0, c2: 0 };
    /// The element `y` (root of y^3 + y + 1 over the base field).
    pub const Y: Self = Self { c0: 0, c1: 1, c2: 0 };

    #[inline]
    pub const fn new(c0: u64, c1: u64, c2: u64) -> Self {
        Self { c0, c1, c2 }
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.c0 == 0 && self.c1 == 0 && self.c2 == 0
    }

    /// Unreduced product: the 5 raw 128-bit polynomial coefficients, before the
    /// y-fold and base reductions. XOR-accumulate many of these and `.reduce()`
    /// once — both folds are GF(2)-linear, so they commute with XOR.
    #[inline]
    pub fn mul_unreduced(self, rhs: Self) -> F192Unreduced {
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

    /// Squaring. Char-2 cross terms vanish: (c0 + c1·y + c2·y²)² =
    /// c0² + c1²·y² + c2²·y⁴, so 3 PMULL + reduction instead of 6.
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

    /// Multiplicative inverse via Fermat: self^(2^192 − 2) = ∏_{i=1..191} self^(2^i).
    /// One-time-setup speed class, not a hot path. `ZERO.inv() == ZERO`.
    pub fn inv(self) -> Self {
        let mut cur = self.square();
        let mut r = cur;
        for _ in 2..192 {
            cur = cur.square();
            r *= cur;
        }
        r
    }
}

impl Add for F192 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 ^ rhs.c0,
            c1: self.c1 ^ rhs.c1,
            c2: self.c2 ^ rhs.c2,
        }
    }
}

impl AddAssign for F192 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.c0 ^= rhs.c0;
        self.c1 ^= rhs.c1;
        self.c2 ^= rhs.c2;
    }
}

impl Mul for F192 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        {
            // SAFETY: aes target feature is enabled at compile time.
            unsafe { aarch64::mul_karatsuba(self, rhs) }
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        {
            software::mul(self, rhs)
        }
    }
}

impl MulAssign for F192 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// ---------------------------------------------------------------------------
// Deferred reduction: 5 unreduced 128-bit coefficients, XOR-accumulable.
// ---------------------------------------------------------------------------

/// Unreduced F192 product: the degree-4 polynomial product over K before any
/// reduction. `w[2k], w[2k+1]` = (lo, hi) of the 128-bit coefficient of y^k.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F192Unreduced {
    pub w: [u64; 10],
}

impl F192Unreduced {
    pub const ZERO: Self = Self { w: [0; 10] };

    #[inline]
    pub fn reduce(self) -> F192 {
        let w = &self.w;
        // y-fold: y³ = y + 1, y⁴ = y² + y (on 128-bit coefficients).
        let d0 = (w[0] ^ w[6], w[1] ^ w[7]);
        let d1 = (w[2] ^ w[6] ^ w[8], w[3] ^ w[7] ^ w[9]);
        let d2 = (w[4] ^ w[8], w[5] ^ w[9]);
        F192 {
            c0: base_reduce_128(d0.0, d0.1),
            c1: base_reduce_128(d1.0, d1.1),
            c2: base_reduce_128(d2.0, d2.1),
        }
    }
}

impl BitXor for F192Unreduced {
    type Output = Self;
    #[inline]
    fn bitxor(self, rhs: Self) -> Self {
        let mut w = self.w;
        for i in 0..10 {
            w[i] ^= rhs.w[i];
        }
        Self { w }
    }
}

impl BitXorAssign for F192Unreduced {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        for i in 0..10 {
            self.w[i] ^= rhs.w[i];
        }
    }
}

// ---------------------------------------------------------------------------
// Base-field reduction mod x^64 + x^4 + x^3 + x + 1. Works on any target.
// ---------------------------------------------------------------------------

/// Fold a 128-bit carry-less product (lo, hi) into GF(2^64).
/// x^64 ≡ x^4+x^3+x+1, so U·x^64 ≡ U ^ U<<1 ^ U<<3 ^ U<<4; the ≤4 bits that
/// shift out past position 63 are folded once more (their product with 0x1B
/// fits in 8 bits — exact).
#[inline]
pub const fn base_reduce_128(lo: u64, hi: u64) -> u64 {
    let f = hi ^ (hi << 1) ^ (hi << 3) ^ (hi << 4);
    let ov = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60); // bits shifted past 63
    lo ^ f ^ ov ^ (ov << 1) ^ (ov << 3) ^ (ov << 4)
}

/// Portable base-field helpers (reference-grade; tests and setup only).
pub mod base {
    use super::base_reduce_128;
    use crate::field::gf2_128::software::clmul64;

    /// GF(2^64) multiply: carry-less 64×64 then fold.
    pub fn mul(a: u64, b: u64) -> u64 {
        let (lo, hi) = clmul64(a, b);
        base_reduce_128(lo, hi)
    }

    pub fn square(a: u64) -> u64 {
        mul(a, a)
    }

    /// Fermat inverse in GF(2^64): a^(2^64 − 2).
    pub fn inv(a: u64) -> u64 {
        let mut cur = square(a);
        let mut r = cur;
        for _ in 2..64 {
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
    use super::{F192, F192Unreduced, R64, base_reduce_128};
    use core::arch::aarch64::*;
    use core::mem::transmute;

    /// 64×64 carry-less product as a 128-bit vector.
    ///
    /// # Safety
    /// Requires the `aes` target feature (statically satisfied: every caller
    /// is itself `#[target_feature(enable = "aes")]`).
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn pmull(a: u64, b: u64) -> uint64x2_t {
        let prod = vmull_p64(a, b);
        // SAFETY: u128 and uint64x2_t are both 128-bit values; bit-level
        // reinterpret with no UB.
        unsafe { transmute::<u128, uint64x2_t>(prod) }
    }

    /// Fold one 128-bit coefficient into GF(2^64): 1 PMULL by 0x1B, then the
    /// ≤4-bit overflow (high lane of the PMULL) is folded with shift-XORs on
    /// the scalar side, off the busy PMULL ports.
    ///
    /// # Safety
    /// Requires the `aes` target feature.
    #[inline]
    #[target_feature(enable = "aes")]
    unsafe fn base_reduce(d: uint64x2_t) -> u64 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let t = pmull(vgetq_lane_u64::<1>(d), R64);
            let ov = vgetq_lane_u64::<1>(t); // ≤ 4 bits (deg(hi·0x1B) ≤ 67)
            vgetq_lane_u64::<0>(d) ^ vgetq_lane_u64::<0>(t) ^ ov ^ (ov << 1) ^ (ov << 3) ^ (ov << 4)
        }
    }

    /// Karatsuba-3: 6 PMULL products (optimal bilinear count for 3 terms),
    /// NEON XOR combination, y-fold, then 3 PMULL base reductions. 9 PMULL
    /// total. Default `Mul` implementation.
    ///
    /// # Safety
    /// Requires the `aes` target feature (compiles to PMULL); only call where
    /// `aes` is statically enabled or has been runtime-detected.
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_karatsuba(a: F192, b: F192) -> F192 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(a.c0, b.c0);
            let p1 = pmull(a.c1, b.c1);
            let p2 = pmull(a.c2, b.c2);
            let p01 = pmull(a.c0 ^ a.c1, b.c0 ^ b.c1);
            let p02 = pmull(a.c0 ^ a.c2, b.c0 ^ b.c2);
            let p12 = pmull(a.c1 ^ a.c2, b.c1 ^ b.c2);

            // c0 = p0                    c3 = p12 ^ p1 ^ p2
            // c1 = p01 ^ p0 ^ p1         c4 = p2
            // c2 = p02 ^ p0 ^ p1 ^ p2
            let t01 = veorq_u64(p0, p1);
            let t12 = veorq_u64(p1, p2);
            let c1 = veorq_u64(p01, t01);
            let c2 = veorq_u64(veorq_u64(p02, p0), t12);
            let c3 = veorq_u64(p12, t12);

            // y-fold: d0 = c0^c3, d1 = c1^c3^c4, d2 = c2^c4 (c4 = p2).
            let d0 = veorq_u64(p0, c3);
            let d1 = veorq_u64(veorq_u64(c1, c3), p2);
            let d2 = veorq_u64(c2, p2);

            F192 {
                c0: base_reduce(d0),
                c1: base_reduce(d1),
                c2: base_reduce(d2),
            }
        }
    }

    /// Schoolbook: 9 fully independent PMULL products + 3 reduction PMULL.
    /// More PMULL pressure than Karatsuba but no input-sum dependencies —
    /// kept as a benchmark variant.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_karatsuba`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_schoolbook(a: F192, b: F192) -> F192 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let q00 = pmull(a.c0, b.c0);
            let q01 = pmull(a.c0, b.c1);
            let q02 = pmull(a.c0, b.c2);
            let q10 = pmull(a.c1, b.c0);
            let q11 = pmull(a.c1, b.c1);
            let q12 = pmull(a.c1, b.c2);
            let q20 = pmull(a.c2, b.c0);
            let q21 = pmull(a.c2, b.c1);
            let q22 = pmull(a.c2, b.c2);

            let c1 = veorq_u64(q01, q10);
            let c2 = veorq_u64(veorq_u64(q02, q11), q20);
            let c3 = veorq_u64(q12, q21);

            let d0 = veorq_u64(q00, c3);
            let d1 = veorq_u64(veorq_u64(c1, c3), q22);
            let d2 = veorq_u64(c2, q22);

            F192 {
                c0: base_reduce(d0),
                c1: base_reduce(d1),
                c2: base_reduce(d2),
            }
        }
    }

    /// Karatsuba products + fully scalar shift-XOR base reduction (no
    /// reduction PMULLs — 6 PMULL total). Trades PMULL-port pressure for
    /// integer-ALU work; benchmark variant.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_karatsuba`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_karatsuba_scalar_reduce(a: F192, b: F192) -> F192 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(a.c0, b.c0);
            let p1 = pmull(a.c1, b.c1);
            let p2 = pmull(a.c2, b.c2);
            let p01 = pmull(a.c0 ^ a.c1, b.c0 ^ b.c1);
            let p02 = pmull(a.c0 ^ a.c2, b.c0 ^ b.c2);
            let p12 = pmull(a.c1 ^ a.c2, b.c1 ^ b.c2);

            let t01 = veorq_u64(p0, p1);
            let t12 = veorq_u64(p1, p2);
            let c1 = veorq_u64(p01, t01);
            let c2 = veorq_u64(veorq_u64(p02, p0), t12);
            let c3 = veorq_u64(p12, t12);

            let d0 = veorq_u64(p0, c3);
            let d1 = veorq_u64(veorq_u64(c1, c3), p2);
            let d2 = veorq_u64(c2, p2);

            F192 {
                c0: base_reduce_128(vgetq_lane_u64::<0>(d0), vgetq_lane_u64::<1>(d0)),
                c1: base_reduce_128(vgetq_lane_u64::<0>(d1), vgetq_lane_u64::<1>(d1)),
                c2: base_reduce_128(vgetq_lane_u64::<0>(d2), vgetq_lane_u64::<1>(d2)),
            }
        }
    }

    /// Karatsuba products only — 6 PMULL, no reduction at all. The caller
    /// XOR-accumulates the raw coefficients (inner products, sumcheck-style).
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_karatsuba`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn mul_unreduced_neon(a: F192, b: F192) -> F192Unreduced {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let p0 = pmull(a.c0, b.c0);
            let p1 = pmull(a.c1, b.c1);
            let p2 = pmull(a.c2, b.c2);
            let p01 = pmull(a.c0 ^ a.c1, b.c0 ^ b.c1);
            let p02 = pmull(a.c0 ^ a.c2, b.c0 ^ b.c2);
            let p12 = pmull(a.c1 ^ a.c2, b.c1 ^ b.c2);

            let t01 = veorq_u64(p0, p1);
            let t12 = veorq_u64(p1, p2);
            let c1 = veorq_u64(p01, t01);
            let c2 = veorq_u64(veorq_u64(p02, p0), t12);
            let c3 = veorq_u64(p12, t12);

            F192Unreduced {
                w: [
                    vgetq_lane_u64::<0>(p0),
                    vgetq_lane_u64::<1>(p0),
                    vgetq_lane_u64::<0>(c1),
                    vgetq_lane_u64::<1>(c1),
                    vgetq_lane_u64::<0>(c2),
                    vgetq_lane_u64::<1>(c2),
                    vgetq_lane_u64::<0>(c3),
                    vgetq_lane_u64::<1>(c3),
                    vgetq_lane_u64::<0>(p2),
                    vgetq_lane_u64::<1>(p2),
                ],
            }
        }
    }

    /// Squaring: cross terms vanish, squares land on y^0, y^2, y^4.
    /// 3 PMULL squares + y-fold + 3 PMULL reductions.
    ///
    /// # Safety
    /// Requires the `aes` target feature; see [`mul_karatsuba`].
    #[inline]
    #[target_feature(enable = "aes")]
    pub unsafe fn square_neon(a: F192) -> F192 {
        // SAFETY: function carries the aes target feature.
        unsafe {
            let s0 = pmull(a.c0, a.c0);
            let s1 = pmull(a.c1, a.c1);
            let s2 = pmull(a.c2, a.c2);
            // (c0 + c1 y + c2 y²)² = s0 + s1 y² + s2 y⁴; y⁴ = y² + y:
            // d0 = s0, d1 = s2, d2 = s1 ^ s2.
            F192 {
                c0: base_reduce(s0),
                c1: base_reduce(s2),
                c2: base_reduce(veorq_u64(s1, s2)),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Software fallback: portable, also the reference the NEON path is tested
// against.
// ---------------------------------------------------------------------------

pub mod software {
    use super::{F192, F192Unreduced, base_reduce_128};
    use crate::field::gf2_128::software::clmul64;

    /// Schoolbook 9-product unreduced coefficients.
    pub fn mul_unreduced(a: F192, b: F192) -> F192Unreduced {
        let a_ = [a.c0, a.c1, a.c2];
        let b_ = [b.c0, b.c1, b.c2];
        let mut c = [(0u64, 0u64); 5];
        for i in 0..3 {
            for j in 0..3 {
                let (lo, hi) = clmul64(a_[i], b_[j]);
                c[i + j].0 ^= lo;
                c[i + j].1 ^= hi;
            }
        }
        F192Unreduced {
            w: [
                c[0].0, c[0].1, c[1].0, c[1].1, c[2].0, c[2].1, c[3].0, c[3].1, c[4].0, c[4].1,
            ],
        }
    }

    pub fn mul(a: F192, b: F192) -> F192 {
        mul_unreduced(a, b).reduce()
    }

    pub fn square(a: F192) -> F192 {
        let (l0, h0) = clmul64(a.c0, a.c0);
        let (l1, h1) = clmul64(a.c1, a.c1);
        let (l2, h2) = clmul64(a.c2, a.c2);
        // Squares land on y^0, y^2, y^4; y^4 = y^2 + y.
        F192 {
            c0: base_reduce_128(l0, h0),
            c1: base_reduce_128(l2, h2),
            c2: base_reduce_128(l1 ^ l2, h1 ^ h2),
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

    fn rand_elem(s: &mut u64) -> F192 {
        F192::new(splitmix64(s), splitmix64(s), splitmix64(s))
    }

    /// Vectors generated by an independent Python implementation
    /// (scratchpad/fieldref.py): (a, b, a·b, a·a).
    const VECTORS: [([u64; 3], [u64; 3], [u64; 3], [u64; 3]); 4] = [
        (
            [0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923],
            [0x6dbca290a9eab706, 0x4c10a4fe30cffdda, 0xf26fff4cc4fd394d],
            [0x888a0fc35abaf5f6, 0x68a84cbc132b0649, 0x9fdeaf613003cabe],
            [0x8fba131ad5d46b8c, 0x1c170457f537a805, 0x3632cc098ca15135],
        ),
        (
            [0x6814a2bc786a6d2d, 0xa26b351e6c8042c5, 0x54760e7fbc051c6c],
            [0xd4c08880a5a4666d, 0x29610ae0eed8f1e7, 0xc34bd8e2fe5213e5],
            [0x2ad322ebf2f9043b, 0x8ac800aa67154c80, 0x6d0f76651d3c4d0c],
            [0xcf800ef2b83bb43a, 0xefe1c6cd064dd44c, 0x57dc5c7a60e2981b],
        ),
        (
            [0x6c50afb6e9fb123d, 0x6f28d015a2aa0b9d, 0x4e385994ebac94af],
            [0x194f9545adba52ce, 0xc675ce05588f882f, 0x57de8c051d4b7ef2],
            [0xea6b9f9d23d4a1ff, 0xd82aa6058c431457, 0x5fd4d8fda2f1e74a],
            [0x8f30fe43aa05b396, 0xe3593591eccd9efe, 0x7c5a1b128788c51f],
        ),
        (
            [0xd998efd82733e933, 0x6df216c33f8f3201, 0x11dc6f3fcb57d5d8],
            [0x8860a84722025e05, 0x33176469aa6ef630, 0x607507ebc5b864d7],
            [0xfa3a0d66cdfbc1b3, 0xbd47bd3343aad307, 0xdaf50186477f6a77],
            [0x69c8d8c24f416884, 0x4b597d648a162147, 0x95603a5d95c9512a],
        ),
    ];

    #[test]
    fn python_vectors() {
        for (a, b, c, s) in VECTORS {
            let (a, b) = (F192::new(a[0], a[1], a[2]), F192::new(b[0], b[1], b[2]));
            assert_eq!(a * b, F192::new(c[0], c[1], c[2]));
            assert_eq!(a.square(), F192::new(s[0], s[1], s[2]));
            assert_eq!(software::mul(a, b), F192::new(c[0], c[1], c[2]));
        }
    }

    #[test]
    fn identities() {
        let mut s = 1u64;
        for _ in 0..100 {
            let a = rand_elem(&mut s);
            assert_eq!(a * F192::ONE, a);
            assert_eq!(a * F192::ZERO, F192::ZERO);
            assert_eq!(a + F192::ZERO, a);
            assert_eq!(a + a, F192::ZERO);
        }
        // y^3 = y + 1
        assert_eq!(F192::Y * F192::Y * F192::Y, F192::Y + F192::ONE);
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
                assert_eq!(aarch64::mul_karatsuba(a, b), want);
                assert_eq!(aarch64::mul_schoolbook(a, b), want);
                assert_eq!(aarch64::mul_karatsuba_scalar_reduce(a, b), want);
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
                assert_eq!(a * a.inv(), F192::ONE);
            }
        }
        assert_eq!(F192::ZERO.inv(), F192::ZERO);
    }

    #[test]
    fn unreduced_accumulation_matches_reduced_sum() {
        let mut s = 5u64;
        for _ in 0..100 {
            let pairs: Vec<(F192, F192)> = (0..16).map(|_| (rand_elem(&mut s), rand_elem(&mut s))).collect();
            let mut acc = F192Unreduced::ZERO;
            let mut want = F192::ZERO;
            for &(a, b) in &pairs {
                acc ^= a.mul_unreduced(b);
                want += a * b;
            }
            assert_eq!(acc.reduce(), want);
        }
    }

    // -- GF(2)[x] helpers on u128 for the base-polynomial irreducibility test.

    fn gf2_mod(mut a: u128, m: u128) -> u128 {
        let dm = 127 - m.leading_zeros();
        while a != 0 {
            let da = 127 - a.leading_zeros();
            if da < dm {
                break;
            }
            a ^= m << (da - dm);
        }
        a
    }

    fn gf2_gcd(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            let r = gf2_mod(a, b);
            a = b;
            b = r;
        }
        a
    }

    /// Rabin: p64 (degree 64 = 2^6) is irreducible iff x^(2^64) ≡ x mod p64
    /// and gcd(x^(2^32) − x, p64) = 1.
    #[test]
    fn base_poly_irreducible() {
        const P64: u128 = (1u128 << 64) | (R64 as u128);
        let mut t = 2u64; // the element x
        for _ in 0..32 {
            t = base::square(t);
        }
        assert_eq!(gf2_gcd((t as u128) ^ 2, P64), 1, "factor of degree | 32");
        for _ in 0..32 {
            t = base::square(t);
        }
        assert_eq!(t, 2, "x^(2^64) != x mod p64");
    }

    // -- K[y] gcd for the extension-polynomial irreducibility test.

    fn pdeg(p: &[u64]) -> Option<usize> {
        p.iter().rposition(|&c| c != 0)
    }

    fn poly_mod(mut a: Vec<u64>, b: &[u64]) -> Vec<u64> {
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

    fn poly_gcd(mut a: Vec<u64>, mut b: Vec<u64>) -> Vec<u64> {
        while pdeg(&b).is_some() {
            let r = poly_mod(a, &b);
            a = b;
            b = r;
        }
        a
    }

    /// A cubic is irreducible over K iff it has no root in K, i.e.
    /// gcd(y^|K| − y, f) = 1. y^(2^64) is computed as 64 Frobenius squarings
    /// of the element y in the quotient ring (which is exactly F192).
    #[test]
    fn extension_poly_irreducible_over_base() {
        let mut t = F192::Y;
        for _ in 0..64 {
            t = t.square();
        }
        let d = t + F192::Y; // y^(2^64) − y as a deg ≤ 2 poly over K
        assert!(!d.is_zero());
        let f = vec![1u64, 1, 0, 1]; // y^3 + y + 1
        let g = poly_gcd(f, vec![d.c0, d.c1, d.c2]);
        assert_eq!(pdeg(&g), Some(0), "y^3+y+1 has a root in GF(2^64)");
    }

    #[test]
    fn serde_roundtrip() {
        let a = F192::new(0x0123456789abcdef, 0xfedcba9876543210, 0x1122334455667788);
        let ser = bincode::serialize(&a).unwrap();
        assert_eq!(bincode::deserialize::<F192>(&ser).unwrap(), a);
    }
}
