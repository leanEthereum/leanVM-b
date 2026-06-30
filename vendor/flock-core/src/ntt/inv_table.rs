// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! §2.1 single-table collapse of the LDE matrix `M = fwd_NTT_Λ ∘ inv_NTT_S`.
//!
//! Background: the URM round-1 needs to map each `ell`-bit row of the boolean
//! witness (packed as `n_chunks = ell/8` bytes) to `ell` evaluations on the
//! NTT domain `Λ`. The naive way computes inv_NTT on S then fwd_NTT on Λ for
//! every row — too slow.
//!
//! The optimization (§2.1 of the paper): `M = α · M̃` with `M̃` Cauchy and `α`
//! a scalar. The columns of `M` satisfy a XOR-shift relation, so the `n_chunks`
//! per-byte sub-tables collapse to a single 256-row base table `T_0`:
//!
//!   M[i', 8b + t]  =  T_0[bit-t-mask(8b+t)][i' ⊕ 8b]
//!
//! Per-byte-chunk b contributes `π_b(T_0[byte_b])` to the output, where
//! `π_b(i') = i' ⊕ 8b`.
//!
//! Storage: 256 × ell bytes (16 KB at k=6, 32 KB at k=7) — fits in L1.
//! Lookups per row: n_chunks (= ell/8), each load is `ell` contiguous bytes.
//!
//! Scalar/correctness-first implementation; NEON `apply_triple` and the
//! unrolled `ntt_and_accum` can be added if the URM hot path needs them.

use crate::field::F8;
use crate::ntt::AdditiveNttGf8;

#[derive(Clone, Debug)]
pub struct InvNttTableByteSingleGf8 {
    pub k: usize,
    pub ell: usize,
    pub n_chunks: usize,
    /// `data[w * ell .. (w+1) * ell]` = T_0[w], the XOR-sum of columns of `M`
    /// indexed by the set bits of `w`.
    data: Vec<F8>,
}

impl InvNttTableByteSingleGf8 {
    /// Build the table given the two NTT instances: `ntt_S` over the input
    /// domain, `ntt_L` over the output (extension) domain. Both must have the
    /// same `k`.
    pub fn new(ntt_s: &AdditiveNttGf8, ntt_l: &AdditiveNttGf8) -> Self {
        assert_eq!(ntt_s.k(), ntt_l.k(), "ntt_S and ntt_L must share k");
        let k = ntt_s.k();
        let ell = 1usize << k;
        assert!(ell >= 8, "ell must be ≥ 8 so n_chunks ≥ 1");
        let n_chunks = ell / 8;
        assert!(
            n_chunks <= 16,
            "n_chunks must fit the i'/chunk XOR encoding"
        );

        let mut data = vec![F8::ZERO; 256 * ell];

        // Compute the 8 unit-column images cols[t] = fwd_NTT_Λ ∘ inv_NTT_S (e_t)
        // for t ∈ 0..8. The remaining columns of M are XOR-shifted versions.
        let mut tmp = vec![F8::ZERO; ell];
        let mut cols: Vec<Vec<F8>> = Vec::with_capacity(8);
        for t in 0..8 {
            tmp.iter_mut().for_each(|x| *x = F8::ZERO);
            tmp[t] = F8::ONE;
            ntt_s.inverse(&mut tmp);
            ntt_l.forward(&mut tmp);
            cols.push(tmp.clone());
        }

        // T_0[0] already zero. T_0[2^t] = cols[t]. Then for non-power-of-two w,
        // T_0[w] = T_0[w ^ lo_bit] ⊕ T_0[lo_bit]; this builds all 256 entries
        // with one XOR per entry.
        for t in 0..8 {
            let entry_start = (1usize << t) * ell;
            data[entry_start..entry_start + ell].copy_from_slice(&cols[t]);
        }
        for w in 3usize..256 {
            if (w & (w - 1)) == 0 {
                continue; // skip powers of 2 (already written)
            }
            let lo_bit = w & w.wrapping_neg(); // w & -w
            let parent = w ^ lo_bit;
            // Borrow-checker friendly: read parent + bit_v slices, then write entry.
            let (parent_off, bit_off, entry_off) = (parent * ell, lo_bit * ell, w * ell);
            for i in 0..ell {
                let v = data[parent_off + i] + data[bit_off + i];
                data[entry_off + i] = v;
            }
        }

        Self {
            k,
            ell,
            n_chunks,
            data,
        }
    }

    /// Raw pointer to the table data (`256 × ell` bytes, row-major). Used by
    /// the URM fused inner kernel, which can't go through the safe slice API
    /// without losing the register-fused layout.
    #[inline]
    pub fn data_ptr(&self) -> *const u8 {
        self.data.as_ptr() as *const u8
    }

    /// Apply M to a single byte-packed row, in place.
    /// `bytes` is `n_chunks` bytes (the LCH-coefficient bits of the row);
    /// `out` will be filled with the `ell` evaluations on Λ.
    ///
    /// Dispatches: NEON on aarch64 when `ell ≥ 16` (true for the protocol
    /// path k_skip=6 ⇒ ell=64), scalar otherwise.
    #[inline]
    pub fn apply(&self, bytes: &[u8], out: &mut [F8]) {
        #[cfg(target_arch = "aarch64")]
        if self.ell >= 16 {
            // SAFETY: aarch64 statically guarantees NEON; ell ≥ 16 ⇒ at least
            // one 128-bit chunk; method validates slice lengths.
            unsafe { self.apply_neon_unchecked(bytes, out) };
            return;
        }
        self.apply_scalar(bytes, out);
    }

    /// Scalar reference. Kept public so tests can use it as the cross-check
    /// oracle for the NEON variant.
    pub fn apply_scalar(&self, bytes: &[u8], out: &mut [F8]) {
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        out.iter_mut().for_each(|x| *x = F8::ZERO);
        for (b, &byte_b) in bytes.iter().enumerate() {
            let row_off = byte_b as usize * self.ell;
            let row = &self.data[row_off..row_off + self.ell];
            let shift = 8 * b;
            for i in 0..self.ell {
                out[i] += row[i ^ shift];
            }
        }
    }

    /// NEON variant of `apply` — operates in 16-byte chunks.
    ///
    /// For each output chunk `c ∈ 0..ell/16`:
    ///   * `b = 0`: straight 16-byte copy from `row0[c]`
    ///   * `b ≥ 1`: load `row_b[c ⊕ (b>>1)]`, half-swap if `b` is odd, XOR
    ///
    /// The `b>>1` chunk-XOR and the `8 · b` within-chunk shift together
    /// implement the `π_b(i') = i' ⊕ 8b` permutation that the §2.1 collapse
    /// requires.
    ///
    /// # Safety
    /// Caller must be on aarch64 (statically true at the dispatch site). The
    /// method validates slice lengths.
    #[cfg(target_arch = "aarch64")]
    pub unsafe fn apply_neon_unchecked(&self, bytes: &[u8], out: &mut [F8]) {
        use core::arch::aarch64::*;
        assert_eq!(bytes.len(), self.n_chunks);
        assert_eq!(out.len(), self.ell);
        let n128 = self.ell / 16; // 4 for ell = 64
        let base = self.data.as_ptr() as *const u8;
        let out_ptr = out.as_mut_ptr() as *mut u8;

        unsafe {
            // b = 0: identity permutation — straight copy from row 0.
            let row0 = base.add(bytes[0] as usize * self.ell);
            for c in 0..n128 {
                vst1q_u8(out_ptr.add(c * 16), vld1q_u8(row0.add(c * 16)));
            }

            // b ≥ 1: XOR with table row[bytes[b]], permuted.
            for b in 1..self.n_chunks {
                let b_high = b >> 1;
                let b_odd = (b & 1) != 0;
                let row_b = base.add(bytes[b] as usize * self.ell);
                if b_odd {
                    for c in 0..n128 {
                        let sc = c ^ b_high;
                        let v = vld1q_u8(row_b.add(sc * 16));
                        let v_swapped = vextq_u8::<8>(v, v);
                        let dst = out_ptr.add(c * 16);
                        vst1q_u8(dst, veorq_u8(vld1q_u8(dst), v_swapped));
                    }
                } else {
                    for c in 0..n128 {
                        let sc = c ^ b_high;
                        let v = vld1q_u8(row_b.add(sc * 16));
                        let dst = out_ptr.add(c * 16);
                        vst1q_u8(dst, veorq_u8(vld1q_u8(dst), v));
                    }
                }
            }
        }
    }

    /// Apply M to three byte-packed rows (a, b, c) — matches the C++ hot-path
    /// signature. Identical math to three `apply` calls; kept separate so the
    /// future NEON port can batch loads across the three rows.
    pub fn apply_triple(
        &self,
        a_bytes: &[u8],
        a_out: &mut [F8],
        b_bytes: &[u8],
        b_out: &mut [F8],
        c_bytes: &[u8],
        c_out: &mut [F8],
    ) {
        self.apply(a_bytes, a_out);
        self.apply(b_bytes, b_out);
        self.apply(c_bytes, c_out);
    }
}
