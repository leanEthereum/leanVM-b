//! Eight-leaf BLAKE3 chunk kernel for AArch64.
//!
//! Upstream BLAKE3's NEON `hash_many` is degree 4: it hashes four 1 KiB
//! chunks through all sixteen dependent compression blocks before starting
//! the next four. Within one 4-lane state the sixteen `v[]` vectors form a
//! single dependency chain of add/xor/rotate, and a 4-lane state uses only
//! half of AArch64's 32 vector registers — so the chain, not the issue width,
//! sets the pace.
//!
//! This kernel keeps **two** independent 4-lane states in flight and
//! interleaves them instruction-for-instruction inside the G function. That
//! doubles the independent work available to the out-of-order engine at every
//! step while still fitting both states plus both message blocks in registers.
//!
//! The contract is fixed to the PCS's L0 Merkle leaf: eight contiguous
//! 1024-byte unkeyed chunks, counter zero, `CHUNK_START` on the first block
//! and `CHUNK_END | ROOT` on the last — i.e. byte-identical to
//! `blake3::hash(leaf)` for each of the eight leaves, exactly like
//! [`super::hash_many_oneshot`].
//!
//! Derived from the reference kernel in Layr-Labs/flock-challenge, which
//! ships the same algorithm as pre-generated assembly.

use core::arch::aarch64::*;

const IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

const MSG_SCHEDULE: [[u8; 16]; 7] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8],
    [3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1],
    [10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6],
    [12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
    [9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7],
    [11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13],
];

/// Leaves per group. Two 4-lane states.
const LANES: usize = 8;
/// Bytes per leaf: one full BLAKE3 chunk.
const LEAF: usize = 1024;
/// 64-byte compression blocks per chunk.
const BLOCKS: usize = LEAF / 64;

#[inline(always)]
unsafe fn rot16(x: uint32x4_t) -> uint32x4_t {
    // SAFETY: NEON is mandatory on aarch64.
    unsafe { vreinterpretq_u32_u16(vrev32q_u16(vreinterpretq_u16_u32(x))) }
}

#[inline(always)]
unsafe fn rot12(x: uint32x4_t) -> uint32x4_t {
    // SAFETY: NEON is mandatory on aarch64.
    unsafe { vsriq_n_u32::<12>(vshlq_n_u32::<20>(x), x) }
}

#[inline(always)]
unsafe fn rot8(x: uint32x4_t) -> uint32x4_t {
    const ROTATE: [u8; 16] = [1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12];
    // SAFETY: NEON is mandatory on aarch64; the table is a valid 16-byte
    // permutation for `vqtbl1q_u8`.
    unsafe {
        let table = vld1q_u8(ROTATE.as_ptr());
        vreinterpretq_u32_u8(vqtbl1q_u8(vreinterpretq_u8_u32(x), table))
    }
}

#[inline(always)]
unsafe fn rot7(x: uint32x4_t) -> uint32x4_t {
    // SAFETY: NEON is mandatory on aarch64.
    unsafe { vsriq_n_u32::<7>(vshlq_n_u32::<25>(x), x) }
}

/// 4x4 u32 transpose in place: turns four lanes' worth of one 4-word group
/// into four word-major vectors.
#[inline(always)]
unsafe fn transpose4(vecs: &mut [uint32x4_t; 4]) {
    // SAFETY: NEON is mandatory on aarch64.
    unsafe {
        let rows01 = vtrnq_u32(vecs[0], vecs[1]);
        let rows23 = vtrnq_u32(vecs[2], vecs[3]);
        vecs[0] = vcombine_u32(vget_low_u32(rows01.0), vget_low_u32(rows23.0));
        vecs[1] = vcombine_u32(vget_low_u32(rows01.1), vget_low_u32(rows23.1));
        vecs[2] = vcombine_u32(vget_high_u32(rows01.0), vget_high_u32(rows23.0));
        vecs[3] = vcombine_u32(vget_high_u32(rows01.1), vget_high_u32(rows23.1));
    }
}

/// Load and transpose one 64-byte block from four leaves into 16 word-major
/// message vectors.
///
/// # Safety
/// Each `inputs[i]` must be readable for `block_offset + 64` bytes.
#[inline(always)]
unsafe fn transpose_block4(
    inputs: [*const u8; 4],
    block_offset: usize,
    out: &mut [uint32x4_t; 16],
) {
    // SAFETY: the caller guarantees each input covers the requested block.
    unsafe {
        for quarter in 0..4 {
            let offset = block_offset + quarter * 16;
            let mut group = [
                vreinterpretq_u32_u8(vld1q_u8(inputs[0].add(offset))),
                vreinterpretq_u32_u8(vld1q_u8(inputs[1].add(offset))),
                vreinterpretq_u32_u8(vld1q_u8(inputs[2].add(offset))),
                vreinterpretq_u32_u8(vld1q_u8(inputs[3].add(offset))),
            ];
            transpose4(&mut group);
            out[quarter * 4..quarter * 4 + 4].copy_from_slice(&group);
        }
    }
}

/// The BLAKE3 G function applied to both 4-lane states, interleaved so the two
/// independent dependency chains issue side by side.
macro_rules! g2 {
    ($v0:expr, $v1:expr, $m0:expr, $m1:expr, $a:expr, $b:expr, $c:expr, $d:expr, $x:expr, $y:expr) => {{
        $v0[$a] = vaddq_u32(vaddq_u32($v0[$a], $v0[$b]), $m0[$x]);
        $v1[$a] = vaddq_u32(vaddq_u32($v1[$a], $v1[$b]), $m1[$x]);
        $v0[$d] = rot16(veorq_u32($v0[$d], $v0[$a]));
        $v1[$d] = rot16(veorq_u32($v1[$d], $v1[$a]));
        $v0[$c] = vaddq_u32($v0[$c], $v0[$d]);
        $v1[$c] = vaddq_u32($v1[$c], $v1[$d]);
        $v0[$b] = rot12(veorq_u32($v0[$b], $v0[$c]));
        $v1[$b] = rot12(veorq_u32($v1[$b], $v1[$c]));
        $v0[$a] = vaddq_u32(vaddq_u32($v0[$a], $v0[$b]), $m0[$y]);
        $v1[$a] = vaddq_u32(vaddq_u32($v1[$a], $v1[$b]), $m1[$y]);
        $v0[$d] = rot8(veorq_u32($v0[$d], $v0[$a]));
        $v1[$d] = rot8(veorq_u32($v1[$d], $v1[$a]));
        $v0[$c] = vaddq_u32($v0[$c], $v0[$d]);
        $v1[$c] = vaddq_u32($v1[$c], $v1[$d]);
        $v0[$b] = rot7(veorq_u32($v0[$b], $v0[$c]));
        $v1[$b] = rot7(veorq_u32($v1[$b], $v1[$c]));
    }};
}

/// One BLAKE3 round on both states. `$round` is a literal so the message
/// schedule indices are compile-time constants.
macro_rules! round2 {
    ($v0:expr, $v1:expr, $m0:expr, $m1:expr, $round:literal) => {{
        const S: [u8; 16] = MSG_SCHEDULE[$round];
        g2!($v0, $v1, $m0, $m1, 0, 4, 8, 12, S[0] as usize, S[1] as usize);
        g2!($v0, $v1, $m0, $m1, 1, 5, 9, 13, S[2] as usize, S[3] as usize);
        g2!($v0, $v1, $m0, $m1, 2, 6, 10, 14, S[4] as usize, S[5] as usize);
        g2!($v0, $v1, $m0, $m1, 3, 7, 11, 15, S[6] as usize, S[7] as usize);
        g2!($v0, $v1, $m0, $m1, 0, 5, 10, 15, S[8] as usize, S[9] as usize);
        g2!($v0, $v1, $m0, $m1, 1, 6, 11, 12, S[10] as usize, S[11] as usize);
        g2!($v0, $v1, $m0, $m1, 2, 7, 8, 13, S[12] as usize, S[13] as usize);
        g2!($v0, $v1, $m0, $m1, 3, 4, 9, 14, S[14] as usize, S[15] as usize);
    }};
}

/// Seed the 16-word compression state from the chaining value. Counter is
/// zero and the block length is always 64 for a full chunk.
#[inline(always)]
unsafe fn init_state(h: &[uint32x4_t; 8], flags: u32) -> [uint32x4_t; 16] {
    // SAFETY: NEON is mandatory on aarch64.
    unsafe {
        [
            h[0],
            h[1],
            h[2],
            h[3],
            h[4],
            h[5],
            h[6],
            h[7],
            vdupq_n_u32(IV[0]),
            vdupq_n_u32(IV[1]),
            vdupq_n_u32(IV[2]),
            vdupq_n_u32(IV[3]),
            vdupq_n_u32(0),
            vdupq_n_u32(0),
            vdupq_n_u32(64),
            vdupq_n_u32(flags),
        ]
    }
}

#[inline(always)]
unsafe fn finish_block(h: &mut [uint32x4_t; 8], v: &[uint32x4_t; 16]) {
    // SAFETY: NEON is mandatory on aarch64.
    unsafe {
        for i in 0..8 {
            h[i] = veorq_u32(v[i], v[i + 8]);
        }
    }
}

/// Transpose the word-major chaining values back to four 32-byte digests.
///
/// # Safety
/// `out` must be writable for 128 bytes.
#[inline(always)]
unsafe fn store_cv4(h: &mut [uint32x4_t; 8], out: *mut u8) {
    // SAFETY: the caller guarantees 128 writable bytes at `out`.
    unsafe {
        let (lo, hi) = h.split_at_mut(4);
        let lo: &mut [uint32x4_t; 4] = lo.try_into().expect("split at 4");
        let hi: &mut [uint32x4_t; 4] = hi.try_into().expect("split at 4");
        transpose4(lo);
        transpose4(hi);
        for lane in 0..4 {
            vst1q_u8(out.add(lane * 32), vreinterpretq_u8_u32(lo[lane]));
            vst1q_u8(out.add(lane * 32 + 16), vreinterpretq_u8_u32(hi[lane]));
        }
    }
}

/// Hash as many complete groups of eight 1 KiB leaves as fit in `out`,
/// returning the number of leaves written. The caller handles the remainder
/// through upstream `hash_many`, which also makes arbitrary chunk sizes safe
/// without padding or over-read.
pub(super) fn hash_complete_groups_1024(data: &[u8], out: &mut [[u8; 32]]) -> usize {
    debug_assert_eq!(data.len(), out.len() * LEAF);
    let groups = out.len() / LANES;
    if groups == 0 {
        return 0;
    }

    for group in 0..groups {
        // SAFETY: group `g` reads `data[g·8·1024 .. (g+1)·8·1024]` and writes
        // `out[g·8 .. (g+1)·8]`, both in bounds because `groups` is
        // `out.len() / 8` and `data.len() == out.len() * 1024`.
        unsafe {
            let input = data.as_ptr().add(group * LANES * LEAF);
            let mut h0 = [vdupq_n_u32(0); 8];
            let mut h1 = [vdupq_n_u32(0); 8];
            for i in 0..8 {
                h0[i] = vdupq_n_u32(IV[i]);
                h1[i] = h0[i];
            }
            let lanes_lo = [
                input,
                input.add(LEAF),
                input.add(2 * LEAF),
                input.add(3 * LEAF),
            ];
            let lanes_hi = [
                input.add(4 * LEAF),
                input.add(5 * LEAF),
                input.add(6 * LEAF),
                input.add(7 * LEAF),
            ];

            let mut m0 = [vdupq_n_u32(0); 16];
            let mut m1 = [vdupq_n_u32(0); 16];
            for block in 0..BLOCKS {
                let block_offset = block * 64;
                transpose_block4(lanes_lo, block_offset, &mut m0);
                transpose_block4(lanes_hi, block_offset, &mut m1);

                // CHUNK_START on the first block; CHUNK_END | ROOT on the
                // last — a whole 1 KiB leaf is exactly one chunk and is its
                // own root, so this reproduces `blake3::hash(leaf)`.
                let flags = u32::from(block == 0) | if block == BLOCKS - 1 { 2 | 8 } else { 0 };
                let mut v0 = init_state(&h0, flags);
                let mut v1 = init_state(&h1, flags);

                round2!(v0, v1, m0, m1, 0);
                round2!(v0, v1, m0, m1, 1);
                round2!(v0, v1, m0, m1, 2);
                round2!(v0, v1, m0, m1, 3);
                round2!(v0, v1, m0, m1, 4);
                round2!(v0, v1, m0, m1, 5);
                round2!(v0, v1, m0, m1, 6);

                finish_block(&mut h0, &v0);
                finish_block(&mut h1, &v1);
            }

            let out_ptr = out.as_mut_ptr().add(group * LANES).cast::<u8>();
            store_cv4(&mut h0, out_ptr);
            store_cv4(&mut h1, out_ptr.add(4 * 32));
        }
    }

    groups * LANES
}
