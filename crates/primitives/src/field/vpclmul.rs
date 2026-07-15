//! AVX-512 `VPCLMULQDQ` batched Karatsuba accumulator shared by
//! `F128T = K[y]/(y²+x·y+1)` and `F128TArtin = K[y]/(y²+y+x^61)`.
//!
//! Both element types are `#[repr(C)] { c0: u64, c1: u64 }`, so a slice of
//! either reads as interleaved `{c0, c1}` u64 pairs. The three Karatsuba
//! sub-products of an inner product `Σ aᵢ·bᵢ` —
//!
//! ```text
//!   p0 = Σ a0ᵢ·b0ᵢ,   p1 = Σ a1ᵢ·b1ᵢ,   pm = Σ (a0ᵢ+a1ᵢ)(b0ᵢ+b1ᵢ)
//! ```
//!
//! — accumulate *identically* for the two fields; only the final, F2-linear
//! reduce differs, and that stays in each tower module (reusing its already
//! tested `…Unreduced::reduce()`). This module produces the `(Σp0, Σp1, Σpm)`
//! triple and nothing else.
//!
//! One `VPCLMULQDQ` computes four independent 64×64→128 carry-less products
//! (one per 128-bit lane of a zmm), so **four field elements are folded per
//! CLMUL instruction** — 4× fewer CLMULs than the scalar `pclmulqdq` path.
//! `BANKS` independent zmm accumulators overlap the CLMUL latency chains.
//!
//! Scope: this is exploration/benchmark code. It compares the two reductions
//! and schoolbook versus Karatsuba on x86 (see the
//! `inner_bench` binary). It needs `vpclmulqdq` + `avx512f` (a Zen 4 /
//! Sapphire-Rapids-class core); `-C target-cpu=native` on such a box enables
//! both. The CLMUL stays 128-bit-per-lane — this batches four of them, it does
//! not widen the field multiply itself.

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "vpclmulqdq",
    target_feature = "avx512f"
))]
pub mod x86_64 {
    use core::arch::x86_64::*;

    /// XOR the four 128-bit lanes of a zmm down to one `__m128i`.
    #[inline]
    #[target_feature(enable = "avx512f", enable = "avx2")]
    unsafe fn fold_lanes(z: __m512i) -> __m128i {
        // Pure register moves/XOR, all covered by this fn's target features.
        let x = _mm256_xor_si256(_mm512_castsi512_si256(z), _mm512_extracti64x4_epi64::<1>(z));
        _mm_xor_si128(_mm256_castsi256_si128(x), _mm256_extracti128_si256::<1>(x))
    }

    /// The Karatsuba pre-XOR for four elements at once: each 128-bit lane's low
    /// 64 bits become `c0 ^ c1` (the high 64 the same). Shuffle `0x4E` swaps the
    /// two 64-bit halves within each 128-bit lane, so `z ^ swap(z)` lands
    /// `c0 ^ c1` in both halves.
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn premix(z: __m512i) -> __m512i {
        _mm512_xor_si512(z, _mm512_shuffle_epi32::<0x4E>(z))
    }

    #[inline]
    #[target_feature(enable = "sse2")]
    unsafe fn pack(v: __m128i) -> u128 {
        // SAFETY: __m128i and u128 are both 128-bit values.
        unsafe { core::mem::transmute::<__m128i, u128>(v) }
    }

    /// Scalar `pclmulqdq` tail: XOR element `i`'s three Karatsuba sub-products
    /// into the running 128-bit parts, for the `< 4`-element remainder. Returns
    /// the finished `(Σp0, Σp1, Σpm)`.
    ///
    /// # Safety
    /// `a`,`b` valid for `2*n` u64 reads; caller carries the CLMUL features.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2", enable = "sse2")]
    unsafe fn tail(
        a: *const u64,
        b: *const u64,
        mut i: usize,
        n: usize,
        mut p0: __m128i,
        mut p1: __m128i,
        mut pm: __m128i,
    ) -> (u128, u128, u128) {
        // SAFETY: i..n are in-bounds by the caller's contract; features carried.
        unsafe {
            while i < n {
                let a0 = *a.add(2 * i);
                let a1 = *a.add(2 * i + 1);
                let b0 = *b.add(2 * i);
                let b1 = *b.add(2 * i + 1);
                let va = _mm_set_epi64x(a1 as i64, a0 as i64);
                let vb = _mm_set_epi64x(b1 as i64, b0 as i64);
                let vam = _mm_set_epi64x(0, (a0 ^ a1) as i64);
                let vbm = _mm_set_epi64x(0, (b0 ^ b1) as i64);
                p0 = _mm_xor_si128(p0, _mm_clmulepi64_si128::<0x00>(va, vb));
                p1 = _mm_xor_si128(p1, _mm_clmulepi64_si128::<0x11>(va, vb));
                pm = _mm_xor_si128(pm, _mm_clmulepi64_si128::<0x00>(vam, vbm));
                i += 1;
            }
            (pack(p0), pack(p1), pack(pm))
        }
    }

    /// `Σ aᵢ·bᵢ` Karatsuba sub-products `(Σp0, Σp1, Σpm)`, four elements per
    /// `VPCLMULQDQ`, `BANKS` independent zmm accumulators. `a`,`b` point at `n`
    /// interleaved `{c0, c1}` u64 pairs. Three CLMULs per four elements
    /// (+ two shuffle/XOR pre-mixes for `pm`).
    ///
    /// # Safety
    /// `a`,`b` valid for `2*n` u64 reads; requires vpclmulqdq + avx512f.
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2", enable = "sse2")]
    pub unsafe fn karatsuba_acc<const BANKS: usize>(
        a: *const u64,
        b: *const u64,
        n: usize,
    ) -> (u128, u128, u128) {
        // SAFETY: caller upholds the pointer contract; features carried.
        unsafe {
            let mut acc0 = [_mm512_setzero_si512(); BANKS];
            let mut acc1 = [_mm512_setzero_si512(); BANKS];
            let mut accm = [_mm512_setzero_si512(); BANKS];
            let stride = 4 * BANKS; // elements consumed per iteration
            let mut i = 0usize;
            while i + stride <= n {
                for k in 0..BANKS {
                    let off = 2 * (i + 4 * k);
                    let za = _mm512_loadu_si512(a.add(off).cast());
                    let zb = _mm512_loadu_si512(b.add(off).cast());
                    acc0[k] = _mm512_xor_si512(acc0[k], _mm512_clmulepi64_epi128::<0x00>(za, zb));
                    acc1[k] = _mm512_xor_si512(acc1[k], _mm512_clmulepi64_epi128::<0x11>(za, zb));
                    accm[k] = _mm512_xor_si512(
                        accm[k],
                        _mm512_clmulepi64_epi128::<0x00>(premix(za), premix(zb)),
                    );
                }
                i += stride;
            }
            // Remaining full groups of four fold into bank 0.
            while i + 4 <= n {
                let off = 2 * i;
                let za = _mm512_loadu_si512(a.add(off).cast());
                let zb = _mm512_loadu_si512(b.add(off).cast());
                acc0[0] = _mm512_xor_si512(acc0[0], _mm512_clmulepi64_epi128::<0x00>(za, zb));
                acc1[0] = _mm512_xor_si512(acc1[0], _mm512_clmulepi64_epi128::<0x11>(za, zb));
                accm[0] = _mm512_xor_si512(
                    accm[0],
                    _mm512_clmulepi64_epi128::<0x00>(premix(za), premix(zb)),
                );
                i += 4;
            }
            let mut s0 = acc0[0];
            let mut s1 = acc1[0];
            let mut sm = accm[0];
            for k in 1..BANKS {
                s0 = _mm512_xor_si512(s0, acc0[k]);
                s1 = _mm512_xor_si512(s1, acc1[k]);
                sm = _mm512_xor_si512(sm, accm[k]);
            }
            tail(a, b, i, n, fold_lanes(s0), fold_lanes(s1), fold_lanes(sm))
        }
    }

    /// Like [`karatsuba_acc`] but schoolbook: four products per element
    /// (`a0b0, a1b1, a0b1, a1b0`), no Karatsuba pre-XOR — one extra
    /// `VPCLMULQDQ` per group in exchange for dropping the two shuffle+XOR
    /// pre-mixes. Returns the SAME `(Σp0, Σp1, Σpm)` triple (`pm` rebuilt as
    /// `p0 ^ p1 ^ cross`, where `cross = Σ a0b1 + a1b0`) so the field reduce is
    /// bit-identical. The Karatsuba/schoolbook trade — one CLMUL vs a couple of
    /// cheap shuffles — is exactly what flips between M-series and x86.
    ///
    /// # Safety
    /// See [`karatsuba_acc`].
    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f", enable = "avx2", enable = "sse2")]
    pub unsafe fn schoolbook_acc<const BANKS: usize>(
        a: *const u64,
        b: *const u64,
        n: usize,
    ) -> (u128, u128, u128) {
        // SAFETY: caller upholds the pointer contract; features carried.
        unsafe {
            let mut acc0 = [_mm512_setzero_si512(); BANKS]; // Σ a0·b0
            let mut acc1 = [_mm512_setzero_si512(); BANKS]; // Σ a1·b1
            let mut accc = [_mm512_setzero_si512(); BANKS]; // Σ a0·b1 ^ a1·b0
            let stride = 4 * BANKS;
            let mut i = 0usize;
            while i + stride <= n {
                for k in 0..BANKS {
                    let off = 2 * (i + 4 * k);
                    let za = _mm512_loadu_si512(a.add(off).cast());
                    let zb = _mm512_loadu_si512(b.add(off).cast());
                    acc0[k] = _mm512_xor_si512(acc0[k], _mm512_clmulepi64_epi128::<0x00>(za, zb));
                    acc1[k] = _mm512_xor_si512(acc1[k], _mm512_clmulepi64_epi128::<0x11>(za, zb));
                    accc[k] = _mm512_xor_si512(
                        accc[k],
                        _mm512_xor_si512(
                            _mm512_clmulepi64_epi128::<0x10>(za, zb), // a0·b1
                            _mm512_clmulepi64_epi128::<0x01>(za, zb), // a1·b0
                        ),
                    );
                }
                i += stride;
            }
            while i + 4 <= n {
                let off = 2 * i;
                let za = _mm512_loadu_si512(a.add(off).cast());
                let zb = _mm512_loadu_si512(b.add(off).cast());
                acc0[0] = _mm512_xor_si512(acc0[0], _mm512_clmulepi64_epi128::<0x00>(za, zb));
                acc1[0] = _mm512_xor_si512(acc1[0], _mm512_clmulepi64_epi128::<0x11>(za, zb));
                accc[0] = _mm512_xor_si512(
                    accc[0],
                    _mm512_xor_si512(
                        _mm512_clmulepi64_epi128::<0x10>(za, zb),
                        _mm512_clmulepi64_epi128::<0x01>(za, zb),
                    ),
                );
                i += 4;
            }
            let mut s0 = acc0[0];
            let mut s1 = acc1[0];
            let mut sc = accc[0];
            for k in 1..BANKS {
                s0 = _mm512_xor_si512(s0, acc0[k]);
                s1 = _mm512_xor_si512(s1, acc1[k]);
                sc = _mm512_xor_si512(sc, accc[k]);
            }
            let (p0, p1, cross) = (fold_lanes(s0), fold_lanes(s1), fold_lanes(sc));
            // pm = (a0+a1)(b0+b1) = a0b0 + a1b1 + (a0b1 + a1b0) — F2-linear over the sum.
            let pm = _mm_xor_si128(_mm_xor_si128(p0, p1), cross);
            tail(a, b, i, n, p0, p1, pm)
        }
    }
}
