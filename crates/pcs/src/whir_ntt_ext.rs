// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright (c) 2026 Bain Capital Crypto, LP and Ron Rothblum
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Interleaved forward additive NTT over `E = GF(2^192)` with K-twiddles,
//! split out of `whir` because it shares nothing with the rest of the
//! opener beyond the two log helpers.

use crate::ntt::AdditiveNttF64;
use primitives::field::{F64, F192};
use primitives::log2_ceil_usize;
use primitives::log2_strict_usize;

// ===================================================================
// Interleaved forward additive NTT over E with K-twiddles
// ===================================================================
//
// Deeper WHIR levels RS-encode an E-valued (folded) witness on the SAME
// K-domain: the twiddles are F64, and each butterfly multiply is the mixed
// product `v.mul_base(twiddle)` (3 PMULL). Structure copied from
// `ntt::additive_ntt_f64`'s interleaved transform, with constants re-derived
// for 24-byte elements.

pub(crate) fn forward_transform_interleaved_ext_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    num_ntts: usize,
    start_layer: usize,
) {
    assert!(num_ntts.is_power_of_two() && num_ntts > 0);
    let n_total = data.len();
    assert_eq!(n_total % num_ntts, 0);
    let log_d = log2_strict_usize(n_total / num_ntts);
    assert!(log_d <= ntt.log_domain_size());
    assert!(start_layer <= log_d);

    forward_transform_interleaved_ext_parallel_from_layer(ntt, data, num_ntts, start_layer);
}

/// Scalar reference for the E-valued interleaved forward NTT (test oracle and
/// small-input path).
pub(crate) fn forward_transform_interleaved_ext_scalar_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    num_ntts: usize,
    start_layer: usize,
) {
    let n_total = data.len();
    let log_d = log2_strict_usize(n_total / num_ntts);

    for layer in start_layer..log_d {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let block_size_half = block_size >> 1;
        let block_elems = block_size * num_ntts;
        for block in 0..num_blocks {
            let twiddle = ntt.twiddle(layer, block);
            let block_start = block * block_elems;
            for row in 0..block_size_half {
                let off_top = block_start + row * num_ntts;
                let off_bot = off_top + block_size_half * num_ntts;
                for lane in 0..num_ntts {
                    let v = data[off_bot + lane];
                    let new_u = data[off_top + lane] + v.mul_base(twiddle);
                    data[off_top + lane] = new_u;
                    data[off_bot + lane] = v + new_u;
                }
            }
        }
    }
}

/// Parallel interleaved forward NTT over E, cache-blocked like the F64 twin:
/// top layers sweep the full buffer (fused two-layer passes, row-parallel),
/// deep layers run as cache-resident sub-NTTs in parallel. Constants are
/// derived from the actual F192 element size.
pub(crate) fn forward_transform_interleaved_ext_parallel_from_layer(
    ntt: &AdditiveNttF64,
    data: &mut [F192],
    num_ntts: usize,
    start_layer: usize,
) {
    let n_total = data.len();
    let log_d = log2_strict_usize(n_total / num_ntts);

    // Target sub-group ~2 MB; each position is `num_ntts` F192 elements.
    const TARGET_SUBGROUP_LOG_BYTES: usize = 21;
    let log_bytes_per_position = log2_ceil_usize(num_ntts * core::mem::size_of::<F192>());
    let target_log_positions = TARGET_SUBGROUP_LOG_BYTES.saturating_sub(log_bytes_per_position);
    let cache_n_top = log_d.saturating_sub(target_log_positions);

    const PARALLEL_FLOOR_LOG_D: usize = 12;
    const MIN_SUB_LOG: usize = 8;
    let n_top = if log_d >= PARALLEL_FLOOR_LOG_D {
        let want_subs_log = log2_strict_usize(parallel::num_threads().next_power_of_two());
        let max_n_top = log_d.saturating_sub(MIN_SUB_LOG);
        cache_n_top.max(want_subs_log.min(max_n_top))
    } else {
        cache_n_top
    };
    if n_top == 0 || log_d < 8 {
        forward_transform_interleaved_ext_scalar_from_layer(ntt, data, num_ntts, start_layer);
        return;
    }

    // Top layers: full-buffer sweeps, fusing two layers where possible.
    let mut layer = start_layer.min(n_top);
    while layer < n_top {
        let num_blocks = 1usize << layer;
        let block_size = 1usize << (log_d - layer);
        let block_elems = block_size * num_ntts;

        if layer + 1 < n_top && block_size >= 4 {
            let quarter = block_size >> 2;
            for block in 0..num_blocks {
                let t_outer = ntt.twiddle(layer, block);
                let t_inner_a = ntt.twiddle(layer + 1, 2 * block);
                let t_inner_b = ntt.twiddle(layer + 1, 2 * block + 1);
                let start = block * block_elems;
                butterfly_interleaved_ext_fused_2layer_par_rows(
                    &mut data[start..start + block_elems],
                    t_outer,
                    t_inner_a,
                    t_inner_b,
                    quarter,
                    num_ntts,
                );
            }
            layer += 2;
        } else {
            let block_size_half = block_size >> 1;
            for block in 0..num_blocks {
                let t = ntt.twiddle(layer, block);
                let start = block * block_elems;
                butterfly_interleaved_ext_block_par_rows(
                    &mut data[start..start + block_elems],
                    t,
                    block_size_half,
                    num_ntts,
                );
            }
            layer += 1;
        }
    }

    // Deep layers: parallel cache-resident sub-NTTs.
    let sub_size_positions = 1usize << (log_d - n_top);
    let sub_elems = sub_size_positions * num_ntts;
    parallel::chunks_mut(data, sub_elems, |sub_idx, sub_data| {
        for layer in n_top.max(start_layer)..log_d {
            let layer_in_sub = layer - n_top;
            let num_blocks_in_sub = 1usize << layer_in_sub;
            let block_size = 1usize << (log_d - layer);
            let block_size_half = block_size >> 1;
            let block_elems = block_size * num_ntts;
            for block_in_sub in 0..num_blocks_in_sub {
                let global_block = sub_idx * num_blocks_in_sub + block_in_sub;
                let twiddle = ntt.twiddle(layer, global_block);
                let block_start = block_in_sub * block_elems;
                let block = &mut sub_data[block_start..block_start + block_elems];
                butterfly_interleaved_ext_block(block, twiddle, block_size_half, num_ntts);
            }
        }
    });
}

fn butterfly_interleaved_ext_block_par_rows(block: &mut [F192], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    const PARALLEL_ROW_THRESHOLD: usize = 1024;
    if block_size_half < PARALLEL_ROW_THRESHOLD {
        butterfly_interleaved_ext_block(block, twiddle, block_size_half, num_ntts);
        return;
    }
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    let bot_base = parallel::SendPtr(bot.as_mut_ptr());
    parallel::chunks_mut(top, num_ntts, |r, top_row| {
        // SAFETY: distinct `r` take disjoint `num_ntts`-windows of `bot` (the
        // same windows `chunks_mut` proved disjoint in `top`), and the halves are
        // disjoint by `split_at_mut`.
        let bot_row = unsafe { bot_base.slice(r * num_ntts, top_row.len()) };
        butterfly_ext_lanes(top_row, bot_row, twiddle);
    });
}

/// Fused 2-layer butterfly, row-parallel; see the F64 twin for the shape.
fn butterfly_interleaved_ext_fused_2layer_par_rows(
    block: &mut [F192],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
    quarter: usize,
    num_ntts: usize,
) {
    const PARALLEL_ROW_THRESHOLD: usize = 512;
    let stride = quarter * num_ntts;
    debug_assert_eq!(block.len(), 4 * stride);

    let do_one = |row_a: &mut [F192], row_b: &mut [F192], row_c: &mut [F192], row_d: &mut [F192]| {
        butterfly_ext_fused_lanes(row_a, row_b, row_c, row_d, t_outer, t_inner_a, t_inner_b);
    };

    // Row group `r` owns `block[i·stride + r·num_ntts .. + num_ntts]` for
    // `i ∈ 0..4`; distinct `r` give disjoint windows within each quarter, and the
    // quarters are disjoint by construction.
    let base = parallel::SendPtr(block.as_mut_ptr());
    let group = |r: usize| {
        let off = r * num_ntts;
        // SAFETY: see above; `off + num_ntts <= stride` because `r < quarter`.
        let [a, b, c, d] = std::array::from_fn(|i| unsafe { base.slice(i * stride + off, num_ntts) });
        do_one(a, b, c, d);
    };

    if quarter < PARALLEL_ROW_THRESHOLD {
        for r in 0..quarter {
            group(r);
        }
    } else {
        parallel::for_each(quarter, group);
    }
}

#[inline]
fn butterfly_interleaved_ext_block(block: &mut [F192], twiddle: F64, block_size_half: usize, num_ntts: usize) {
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    for r in 0..block_size_half {
        let off = r * num_ntts;
        butterfly_ext_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
    }
}

/// Butterfly all extension-field lanes in a row pair. The production layout
/// has eight interleaved NTTs, which the AVX-512 path transposes from eight
/// AoS `F192`s into three coefficient vectors before multiplying.
#[inline]
fn butterfly_ext_lanes(top: &mut [F192], bot: &mut [F192], twiddle: F64) {
    debug_assert_eq!(top.len(), bot.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let vectors = top.len() / 8;
        // SAFETY: target features are enabled at compile time and every call
        // addresses exactly eight readable and writable F192 values.
        unsafe {
            for i in 0..vectors {
                butterfly_ext_lanes_avx512(top.as_mut_ptr().add(8 * i), bot.as_mut_ptr().add(8 * i), twiddle.0);
            }
        }
        for lane in 8 * vectors..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v.mul_base(twiddle);
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    {
        for lane in 0..top.len() {
            let v = bot[lane];
            let new_u = top[lane] + v.mul_base(twiddle);
            top[lane] = new_u;
            bot[lane] = v + new_u;
        }
    }
}

#[inline]
pub(crate) fn butterfly_ext_fused_lanes(
    row_a: &mut [F192],
    row_b: &mut [F192],
    row_c: &mut [F192],
    row_d: &mut [F192],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
) {
    debug_assert_eq!(row_a.len(), row_b.len());
    debug_assert_eq!(row_a.len(), row_c.len());
    debug_assert_eq!(row_a.len(), row_d.len());
    #[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
    {
        let vectors = row_a.len() / 8;
        // SAFETY: target features are enabled at compile time and every call
        // addresses exactly eight elements in each of four disjoint rows.
        unsafe {
            for i in 0..vectors {
                butterfly_ext_fused_lanes_avx512(
                    row_a.as_mut_ptr().add(8 * i),
                    row_b.as_mut_ptr().add(8 * i),
                    row_c.as_mut_ptr().add(8 * i),
                    row_d.as_mut_ptr().add(8 * i),
                    t_outer.0,
                    t_inner_a.0,
                    t_inner_b.0,
                );
            }
        }
        for lane in 8 * vectors..row_a.len() {
            let mut a = row_a[lane];
            let mut b = row_b[lane];
            let mut c = row_c[lane];
            let mut d = row_d[lane];
            let new_a = a + c.mul_base(t_outer);
            c += new_a;
            a = new_a;
            let new_b = b + d.mul_base(t_outer);
            d += new_b;
            b = new_b;
            let new_a2 = a + b.mul_base(t_inner_a);
            b += new_a2;
            a = new_a2;
            let new_c2 = c + d.mul_base(t_inner_b);
            d += new_c2;
            c = new_c2;
            row_a[lane] = a;
            row_b[lane] = b;
            row_c[lane] = c;
            row_d[lane] = d;
        }
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")))]
    {
        butterfly_ext_lanes(row_a, row_c, t_outer);
        butterfly_ext_lanes(row_b, row_d, t_outer);
        butterfly_ext_lanes(row_a, row_b, t_inner_a);
        butterfly_ext_lanes(row_c, row_d, t_inner_b);
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[derive(Clone, Copy)]
struct F192x8 {
    c0: core::arch::x86_64::__m512i,
    c1: core::arch::x86_64::__m512i,
    c2: core::arch::x86_64::__m512i,
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn load_f192x8_avx512(ptr: *const F192) -> F192x8 {
    use core::arch::x86_64::*;

    // The 24 coefficients occupy three contiguous ZMM registers. Each result
    // first selects from the first two registers, then fills its tail from the
    // third register.
    unsafe {
        let p = ptr.cast::<u64>();
        let x0 = _mm512_loadu_si512(p.cast());
        let x1 = _mm512_loadu_si512(p.add(8).cast());
        let x2 = _mm512_loadu_si512(p.add(16).cast());

        let c0_head = _mm512_permutex2var_epi64(x0, _mm512_set_epi64(0, 0, 15, 12, 9, 6, 3, 0), x1);
        let c0_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(5, 2, 0, 0, 0, 0, 0, 0), x2);
        let c1_head = _mm512_permutex2var_epi64(x0, _mm512_set_epi64(0, 0, 0, 13, 10, 7, 4, 1), x1);
        let c1_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(6, 3, 0, 0, 0, 0, 0, 0), x2);
        let c2_head = _mm512_permutex2var_epi64(x0, _mm512_set_epi64(0, 0, 0, 14, 11, 8, 5, 2), x1);
        let c2_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(7, 4, 1, 0, 0, 0, 0, 0), x2);

        F192x8 {
            c0: _mm512_mask_mov_epi64(c0_head, 0xc0, c0_tail),
            c1: _mm512_mask_mov_epi64(c1_head, 0xe0, c1_tail),
            c2: _mm512_mask_mov_epi64(c2_head, 0xe0, c2_tail),
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn store_f192x8_avx512(ptr: *mut F192, value: F192x8) {
    use core::arch::x86_64::*;

    unsafe {
        let x0_head = _mm512_permutex2var_epi64(value.c0, _mm512_set_epi64(10, 2, 0, 9, 1, 0, 8, 0), value.c1);
        let x0_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(0, 0, 1, 0, 0, 0, 0, 0), value.c2);

        let x1_head = _mm512_permutex2var_epi64(value.c0, _mm512_set_epi64(5, 0, 12, 4, 0, 11, 3, 0), value.c1);
        let x1_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(0, 4, 0, 0, 3, 0, 0, 2), value.c2);

        let x2_head = _mm512_permutex2var_epi64(value.c0, _mm512_set_epi64(0, 15, 7, 0, 14, 6, 0, 13), value.c1);
        let x2_tail = _mm512_permutexvar_epi64(_mm512_set_epi64(7, 0, 0, 6, 0, 0, 5, 0), value.c2);

        let p = ptr.cast::<u64>();
        _mm512_storeu_si512(p.cast(), _mm512_mask_mov_epi64(x0_head, 0x24, x0_tail));
        _mm512_storeu_si512(p.add(8).cast(), _mm512_mask_mov_epi64(x1_head, 0x49, x1_tail));
        _mm512_storeu_si512(p.add(16).cast(), _mm512_mask_mov_epi64(x2_head, 0x92, x2_tail));
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn mul_base_f192x8_avx512(value: F192x8, twiddle: u64) -> F192x8 {
    use core::arch::x86_64::*;

    #[inline]
    #[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
    unsafe fn mul_coeff(value: __m512i, tw: __m512i, r: __m512i) -> __m512i {
        let even = _mm512_clmulepi64_epi128::<0x00>(value, tw);
        let even_t = _mm512_clmulepi64_epi128::<0x01>(even, r);
        let even_u = _mm512_clmulepi64_epi128::<0x01>(even_t, r);
        let even = _mm512_xor_si512(_mm512_xor_si512(even, even_t), even_u);

        let odd = _mm512_clmulepi64_epi128::<0x11>(value, tw);
        let odd_t = _mm512_clmulepi64_epi128::<0x01>(odd, r);
        let odd_u = _mm512_clmulepi64_epi128::<0x01>(odd_t, r);
        let odd = _mm512_shuffle_epi32::<0x4e>(_mm512_xor_si512(_mm512_xor_si512(odd, odd_t), odd_u));
        _mm512_mask_blend_epi64(0xaa, even, odd)
    }

    unsafe {
        let tw = _mm512_set1_epi64(twiddle as i64);
        let r = _mm512_set1_epi64(0x1b);
        F192x8 {
            c0: mul_coeff(value.c0, tw, r),
            c1: mul_coeff(value.c1, tw, r),
            c2: mul_coeff(value.c2, tw, r),
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn butterfly_f192x8_avx512(top: &mut F192x8, bot: &mut F192x8, twiddle: u64) {
    use core::arch::x86_64::_mm512_xor_si512;

    unsafe {
        let product = mul_base_f192x8_avx512(*bot, twiddle);
        top.c0 = _mm512_xor_si512(top.c0, product.c0);
        top.c1 = _mm512_xor_si512(top.c1, product.c1);
        top.c2 = _mm512_xor_si512(top.c2, product.c2);
        bot.c0 = _mm512_xor_si512(bot.c0, top.c0);
        bot.c1 = _mm512_xor_si512(bot.c1, top.c1);
        bot.c2 = _mm512_xor_si512(bot.c2, top.c2);
    }
}

/// Eight F192 butterflies with a shared base-field twiddle.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX-512F; `top` and `bot` must each address eight
/// readable and writable F192 values.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn butterfly_ext_lanes_avx512(top: *mut F192, bot: *mut F192, twiddle: u64) {
    unsafe {
        let mut u = load_f192x8_avx512(top);
        let mut v = load_f192x8_avx512(bot);
        butterfly_f192x8_avx512(&mut u, &mut v, twiddle);
        store_f192x8_avx512(top, u);
        store_f192x8_avx512(bot, v);
    }
}

/// Fused two-layer butterfly over eight F192 lanes. Four rows stay in SoA ZMM
/// form across both layers, so each row pays the AoS transpose only once.
///
/// # Safety
/// Requires VPCLMULQDQ + AVX-512F; each pointer must address eight readable
/// and writable F192 values, and the four regions must be disjoint.
#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "vpclmulqdq", enable = "avx512f")]
unsafe fn butterfly_ext_fused_lanes_avx512(
    row_a: *mut F192,
    row_b: *mut F192,
    row_c: *mut F192,
    row_d: *mut F192,
    t_outer: u64,
    t_inner_a: u64,
    t_inner_b: u64,
) {
    unsafe {
        let mut a = load_f192x8_avx512(row_a);
        let mut b = load_f192x8_avx512(row_b);
        let mut c = load_f192x8_avx512(row_c);
        let mut d = load_f192x8_avx512(row_d);
        butterfly_f192x8_avx512(&mut a, &mut c, t_outer);
        butterfly_f192x8_avx512(&mut b, &mut d, t_outer);
        butterfly_f192x8_avx512(&mut a, &mut b, t_inner_a);
        butterfly_f192x8_avx512(&mut c, &mut d, t_inner_b);
        store_f192x8_avx512(row_a, a);
        store_f192x8_avx512(row_b, b);
        store_f192x8_avx512(row_c, c);
        store_f192x8_avx512(row_d, d);
    }
}
