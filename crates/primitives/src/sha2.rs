//! `sha2_eth`, the repo's one hash function: SHA-256's compression under a
//! length-prefixed Merkle-Damgard.
//!
//! ## The construction
//!
//! [`compress`] is `C`, the FIPS 180-4 SHA-256 compression: a 32-byte chaining
//! value and a 64-byte block in, 32 bytes out, with the standard big-endian
//! byte-to-word reading, so it is byte-for-byte the compression a stock
//! SHA-256 runs.
//!
//! [`hash`] is `sha2_eth`. For a message of `n` bits it Merkle-Damgards
//!
//! ```text
//!   len_block(n) ‖ msg ‖ 0…0
//! ```
//!
//! from [`IV_ETH`], where `len_block(n)` is `n` as a 512-bit big-endian integer
//! and the trailing zeros round the message up to a whole number of 64-byte
//! blocks. Putting the length first rather than last makes the encoding
//! prefix-free, and prefix-free Merkle-Damgard is indifferentiable from a
//! random oracle when the compression is (Coron et al.); SHA-256's `C` is
//! Davies-Meyer, which provably is NOT an ideal fixed-input-length primitive,
//! so as always the claim rests on the usual heuristic about `C` rather than on
//! a theorem about SHA-256. The usual `10*` padding is unnecessary either way,
//! since the length block already separates messages of different lengths and
//! the zero fill is injective at a fixed length.
//!
//! Prefix-freeness is a statement about [`hash`]. [`compress`] and the VM's
//! `Sha2` opcode expose a raw chain from a caller-chosen chaining value, and
//! anything built on those (the sponge, the Merkle tree) needs its own
//! argument.
//!
//! ## Why the length goes first: free hashing at known sizes
//!
//! The first compression absorbs only the length, so
//!
//! ```text
//!   iv_for_len(n) = C(IV_ETH, len_block(8n))
//! ```
//!
//! depends on nothing but `n`. Every call site in leanVM-b knows its length at
//! compile time, so that compression is a constant: [`IV_64`] for the 64-byte
//! hash the sponge and the Merkle parent use, [`iv_for_len`] for the rest. An
//! `n`-byte hash is then exactly `ceil(n / 64)` compressions, the same count
//! BLAKE2s cost, and **the VM proves exactly those**.
//!
//! Natively, taking that constant is the caller's job and the type system will
//! not do it for you: [`iv_for_len`] is a `const fn`, but called with a runtime
//! length it is an ordinary function and runs a whole extra compression. So
//! [`hash_block`] exists for the 64-byte case, which is most of the hashing a
//! proof does, and [`hash`] at any other length pays one hardware compression
//! for the length block on top of the `ceil(n / 64)`. Measured on an M4 Max
//! (`tests/sha2_bench.rs`, `serial_throughput`): 33 ns for the 64-byte hash,
//! 106 ns at 96 bytes, 346 ns at 704 bytes.
//!
//! ## Surfaces
//!
//! - [`compress`], the compression. The VM's `Sha2` opcode computes it and
//!   `flock::sha2` proves it.
//! - [`hash`] / [`Hasher`], `sha2_eth` over bytes. The hasher takes the total
//!   length up front, because the construction needs it in the first block.
//! - [`hash_block`], `sha2_eth` of exactly 64 bytes at one compression.
//! - [`hash_many`], the batched form: `LANES` independent equal-length inputs
//!   hashed together with the state transposed across lanes, which is how the
//!   PCS Merkle tree gets SIMD out of hashes that are individually serial.

/// SHA-256's initial hash value (FIPS 180-4 §5.3.3). Only [`sha256`] uses it;
/// `sha2_eth` starts from [`IV_ETH`].
pub const IV: [u32; 8] = [
    0x6A09_E667,
    0xBB67_AE85,
    0x3C6E_F372,
    0xA54F_F53A,
    0x510E_527F,
    0x9B05_688C,
    0x1F83_D9AB,
    0x5BE0_CD19,
];

/// SHA-256's round constants (FIPS 180-4 §4.2.2).
pub const K: [u32; 64] = [
    0x428A_2F98,
    0x7137_4491,
    0xB5C0_FBCF,
    0xE9B5_DBA5,
    0x3956_C25B,
    0x59F1_11F1,
    0x923F_82A4,
    0xAB1C_5ED5,
    0xD807_AA98,
    0x1283_5B01,
    0x2431_85BE,
    0x550C_7DC3,
    0x72BE_5D74,
    0x80DE_B1FE,
    0x9BDC_06A7,
    0xC19B_F174,
    0xE49B_69C1,
    0xEFBE_4786,
    0x0FC1_9DC6,
    0x240C_A1CC,
    0x2DE9_2C6F,
    0x4A74_84AA,
    0x5CB0_A9DC,
    0x76F9_88DA,
    0x983E_5152,
    0xA831_C66D,
    0xB003_27C8,
    0xBF59_7FC7,
    0xC6E0_0BF3,
    0xD5A7_9147,
    0x06CA_6351,
    0x1429_2967,
    0x27B7_0A85,
    0x2E1B_2138,
    0x4D2C_6DFC,
    0x5338_0D13,
    0x650A_7354,
    0x766A_0ABB,
    0x81C2_C92E,
    0x9272_2C85,
    0xA2BF_E8A1,
    0xA81A_664B,
    0xC24B_8B70,
    0xC76C_51A3,
    0xD192_E819,
    0xD699_0624,
    0xF40E_3585,
    0x106A_A070,
    0x19A4_C116,
    0x1E37_6C08,
    0x2748_774C,
    0x34B0_BCB5,
    0x391C_0CB3,
    0x4ED8_AA4A,
    0x5B9C_CA4F,
    0x682E_6FF3,
    0x748F_82EE,
    0x78A5_636F,
    0x84C8_7814,
    0x8CC7_0208,
    0x90BE_FFFA,
    0xA450_6CEB,
    0xBEF9_A3F7,
    0xC671_78F2,
];

/// Digest length in bytes.
pub const OUT_LEN: usize = 32;
/// Compression block length in bytes.
pub const BLOCK_LEN: usize = 64;
/// Rounds per compression.
pub const ROUNDS: usize = 64;

/// `C`, the SHA-256 compression: absorb one 64-byte block, given as its 16
/// big-endian words, into the chaining value `h`.
///
/// This is the whole nonlinear core of every hash in leanVM-b, and the one
/// relation flock proves. Dispatches to the CPU's SHA-256 extension where the
/// target has one; [`compress_portable`] is the definition it agrees with.
#[inline]
pub fn compress(h: [u32; 8], m: [u32; 16]) -> [u32; 8] {
    #[cfg(any(
        all(target_arch = "aarch64", target_feature = "sha2"),
        all(target_arch = "x86_64", target_feature = "sha", target_feature = "sse4.1")
    ))]
    return hw::compress(h, m);
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "sha2"),
        all(target_arch = "x86_64", target_feature = "sha", target_feature = "sse4.1")
    )))]
    compress_portable(h, m)
}

/// [`compress`] in portable Rust: the definition, and the reference the
/// hardware paths are checked against.
///
/// `const`, which is what lets the per-length initial states ([`iv_for_len`],
/// [`IV_ETH`]) fold at compile time.
#[inline]
pub const fn compress_portable(h: [u32; 8], m: [u32; 16]) -> [u32; 8] {
    let mut w = [0u32; ROUNDS];
    let mut t = 0;
    while t < 16 {
        w[t] = m[t];
        t += 1;
    }
    while t < ROUNDS {
        let x = w[t - 15];
        let s0 = x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3);
        let y = w[t - 2];
        let s1 = y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10);
        w[t] = w[t - 16].wrapping_add(s0).wrapping_add(w[t - 7]).wrapping_add(s1);
        t += 1;
    }

    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
    let mut t = 0;
    while t < ROUNDS {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        // `g ^ (e & (f ^ g))` is `(e & f) ^ (!e & g)` with one AND, the form the
        // R1CS encoding also uses.
        let ch = g ^ (e & (f ^ g));
        let t1 = hh
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        // `a ^ ((a ^ b) & (a ^ c))` is the majority, again with one AND.
        let maj = a ^ ((a ^ b) & (a ^ c));
        let t2 = s0.wrapping_add(maj);
        hh = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
        t += 1;
    }

    [
        h[0].wrapping_add(a),
        h[1].wrapping_add(b),
        h[2].wrapping_add(c),
        h[3].wrapping_add(d),
        h[4].wrapping_add(e),
        h[5].wrapping_add(f),
        h[6].wrapping_add(g),
        h[7].wrapping_add(hh),
    ]
}

/// Read a 64-byte block as 16 big-endian words.
#[inline]
const fn block_words(block: &[u8; BLOCK_LEN]) -> [u32; 16] {
    let mut m = [0u32; 16];
    let mut i = 0;
    while i < 16 {
        m[i] = u32::from_be_bytes([block[4 * i], block[4 * i + 1], block[4 * i + 2], block[4 * i + 3]]);
        i += 1;
    }
    m
}

/// Serialize a chaining value as the 32-byte digest, big-endian per word.
#[inline]
const fn state_bytes(h: &[u32; 8]) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    let mut i = 0;
    while i < 8 {
        let b = h[i].to_be_bytes();
        out[4 * i] = b[0];
        out[4 * i + 1] = b[1];
        out[4 * i + 2] = b[2];
        out[4 * i + 3] = b[3];
        i += 1;
    }
    out
}

// ---------------------------------------------------------------------------
// The CPU's SHA-256 extension
//
// Both ISAs expose the same two pieces: a four-rounds-at-a-time instruction
// pair over a 128-bit state, and a four-schedule-words-at-a-time pair. So both
// backends are the same sixteen steps over a rotating window `m0..m3` holding
// `w[i-16 .. i)`, twelve of which also advance the window; only the state
// packing and the spelling differ.
//
// A block is then ~50 instructions against the portable path's ~1,800
// operations, which is why this is worth having for the serial callers (the
// Fiat-Shamir sponge, the VM's execution trace, XMSS) even where the batched
// path already gets its speed from lane transposition.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
mod hw {
    use super::{BLOCK_LEN, K, OUT_LEN};
    use core::arch::aarch64::*;

    /// The four-round step over `N` independent chains: `sha256h` produces the
    /// next `abcd` and `sha256h2` the next `efgh`, both from the *old* pair,
    /// hence the `old` copy. `N` is a literal, so the loop unrolls and the
    /// arrays stay in registers.
    macro_rules! quad {
        ($s0:ident, $s1:ident, $m:ident, $k:expr, $n:expr) => {{
            let kv = vld1q_u32(K.as_ptr().add($k));
            for j in 0..$n {
                let t = vaddq_u32($m[j], kv);
                let old = $s0[j];
                $s0[j] = vsha256hq_u32($s0[j], $s1[j], t);
                $s1[j] = vsha256h2q_u32($s1[j], old, t);
            }
        }};
    }

    /// `m0` advances from `w[i-16..i-12]` to `w[i..i+4]`, so the sixteen steps
    /// rotate the four names rather than shifting a buffer.
    macro_rules! sched {
        ($m0:ident, $m1:ident, $m2:ident, $m3:ident, $n:expr) => {
            for j in 0..$n {
                $m0[j] = vsha256su1q_u32(vsha256su0q_u32($m0[j], $m1[j]), $m2[j], $m3[j]);
            }
        };
    }

    /// All 64 rounds. Rounds 0..48 also expand the schedule; 48..64 have
    /// nothing left to expand.
    macro_rules! rounds {
        ($s0:ident, $s1:ident, $m0:ident, $m1:ident, $m2:ident, $m3:ident, $n:expr) => {{
            let mut k = 0;
            while k < 48 {
                quad!($s0, $s1, $m0, k, $n);
                sched!($m0, $m1, $m2, $m3, $n);
                quad!($s0, $s1, $m1, k + 4, $n);
                sched!($m1, $m2, $m3, $m0, $n);
                quad!($s0, $s1, $m2, k + 8, $n);
                sched!($m2, $m3, $m0, $m1, $n);
                quad!($s0, $s1, $m3, k + 12, $n);
                sched!($m3, $m0, $m1, $m2, $n);
                k += 16;
            }
            quad!($s0, $s1, $m0, 48, $n);
            quad!($s0, $s1, $m1, 52, $n);
            quad!($s0, $s1, $m2, 56, $n);
            quad!($s0, $s1, $m3, 60, $n);
        }};
    }

    /// [`super::compress`] on the crypto extension.
    #[inline]
    pub(super) fn compress(h: [u32; 8], m: [u32; 16]) -> [u32; 8] {
        // SAFETY: every intrinsic here is gated on `target_feature = "sha2"`
        // by the module's `cfg`, and all loads are of in-bounds fixed arrays.
        unsafe {
            let mut s0 = [vld1q_u32(h.as_ptr())];
            let mut s1 = [vld1q_u32(h.as_ptr().add(4))];
            let (save0, save1) = (s0[0], s1[0]);
            let mut m0 = [vld1q_u32(m.as_ptr())];
            let mut m1 = [vld1q_u32(m.as_ptr().add(4))];
            let mut m2 = [vld1q_u32(m.as_ptr().add(8))];
            let mut m3 = [vld1q_u32(m.as_ptr().add(12))];
            rounds!(s0, s1, m0, m1, m2, m3, 1);
            let mut out = [0u32; 8];
            vst1q_u32(out.as_mut_ptr(), vaddq_u32(s0[0], save0));
            vst1q_u32(out.as_mut_ptr().add(4), vaddq_u32(s1[0], save1));
            out
        }
    }

    /// Independent hashes driven through the extension four at a time.
    ///
    /// `sha256h` is a several-cycle dependency chain and one-per-cycle
    /// throughput, so a lone chain leaves most of the unit idle; four
    /// independent ones fill it. This is what makes the extension beat the
    /// four-lane NEON transposition for the Merkle tree as well as for the
    /// serial callers, so aarch64 never takes the `Lanes32` path.
    ///
    /// Four is not tuned, it is where the curve is flat: measured on an M4 Max,
    /// 2 through 6 all land in 3.2 to 3.6 GB/s at every leaf size, so the
    /// crypto unit is throughput-bound rather than latency-bound and one extra
    /// chain buys nothing. Fully unrolling `rounds!` over literal `k` was also
    /// tried and is very slightly worse. About 70% of the unit's peak is what
    /// this gets; the rest is the block loads and the big-endian decode.
    const INTERLEAVE: usize = 4;

    /// [`super::hash_many_dyn`] on the crypto extension. Same contract: `len` a
    /// nonzero multiple of 64, one 32-byte digest per input.
    pub(super) fn hash_many(data: &[u8], len: usize, out: &mut [u8]) {
        let n = out.len() / OUT_LEN;
        let iv = super::iv_at(len as u64);
        let groups = n / INTERLEAVE;
        // SAFETY: `g * INTERLEAVE + j < n`, so each input's `len` bytes and
        // each digest's 32 bytes are in bounds.
        unsafe {
            for g in 0..groups {
                compress_group(data, len, &iv, g * INTERLEAVE, out);
            }
        }
        for i in groups * INTERLEAVE..n {
            out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&super::hash(&data[i * len..(i + 1) * len]));
        }
    }

    /// Hash inputs `base .. base + INTERLEAVE` with their four chains
    /// interleaved round-group by round-group.
    ///
    /// # Safety
    /// Inputs `base .. base + INTERLEAVE` must each have `len` readable bytes
    /// in `data`, and their digest windows must be inside `out`.
    #[inline]
    unsafe fn compress_group(data: &[u8], len: usize, iv: &[u32; 8], base: usize, out: &mut [u8]) {
        // SAFETY: as the caller's contract.
        unsafe {
            let mut s0 = [vld1q_u32(iv.as_ptr()); INTERLEAVE];
            let mut s1 = [vld1q_u32(iv.as_ptr().add(4)); INTERLEAVE];
            for blk in 0..len / BLOCK_LEN {
                let mut m0 = [vdupq_n_u32(0); INTERLEAVE];
                let mut m1 = m0;
                let mut m2 = m0;
                let mut m3 = m0;
                for j in 0..INTERLEAVE {
                    let p = data.as_ptr().add((base + j) * len + blk * BLOCK_LEN);
                    // `vrev32q_u8` is the big-endian word decode.
                    let w = |o: usize| vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(o))));
                    m0[j] = w(0);
                    m1[j] = w(16);
                    m2[j] = w(32);
                    m3[j] = w(48);
                }
                let (save0, save1) = (s0, s1);
                // The interleave lives in `quad!`'s inner loop: one four-round
                // step for all four chains before moving on, so no chain waits
                // on its own latency.
                rounds!(s0, s1, m0, m1, m2, m3, INTERLEAVE);
                for j in 0..INTERLEAVE {
                    s0[j] = vaddq_u32(s0[j], save0[j]);
                    s1[j] = vaddq_u32(s1[j], save1[j]);
                }
            }
            for j in 0..INTERLEAVE {
                let p = out.as_mut_ptr().add((base + j) * OUT_LEN);
                vst1q_u8(p, vrev32q_u8(vreinterpretq_u8_u32(s0[j])));
                vst1q_u8(p.add(16), vrev32q_u8(vreinterpretq_u8_u32(s1[j])));
            }
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "sha", target_feature = "sse4.1"))]
mod hw {
    use super::K;
    use core::arch::x86_64::*;

    /// [`super::compress`] on SHA-NI.
    ///
    /// `sha256rnds2` works on the state repacked as `ABEF` / `CDGH` and takes
    /// two rounds' constants in its low two lanes, so a four-round step is two
    /// of them with a shuffle between. The schedule step is the same rotating
    /// window as the aarch64 path: `msg1` folds `sigma_0` in, the `alignr`
    /// supplies `w[i-7 .. i-3]`, and `msg2` finishes with `sigma_1`.
    #[inline]
    pub(super) fn compress(h: [u32; 8], m: [u32; 16]) -> [u32; 8] {
        // SAFETY: every intrinsic here is gated on `target_feature = "sha"` and
        // `"sse4.1"` by the module's `cfg`, and all loads are in-bounds.
        unsafe {
            // Repack: `s0` becomes ABEF and `s1` CDGH (lane 3 down to lane 0).
            let tmp = _mm_shuffle_epi32::<0xB1>(_mm_loadu_si128(h.as_ptr().cast()));
            let efgh = _mm_shuffle_epi32::<0x1B>(_mm_loadu_si128(h.as_ptr().add(4).cast()));
            let mut s0 = _mm_alignr_epi8::<8>(tmp, efgh);
            let mut s1 = _mm_blend_epi16::<0xF0>(efgh, tmp);
            let (save0, save1) = (s0, s1);

            let mut m0 = _mm_loadu_si128(m.as_ptr().cast());
            let mut m1 = _mm_loadu_si128(m.as_ptr().add(4).cast());
            let mut m2 = _mm_loadu_si128(m.as_ptr().add(8).cast());
            let mut m3 = _mm_loadu_si128(m.as_ptr().add(12).cast());

            macro_rules! quad {
                ($m:expr, $k:expr) => {{
                    let kv = _mm_add_epi32($m, _mm_loadu_si128(K.as_ptr().add($k).cast()));
                    s1 = _mm_sha256rnds2_epu32(s1, s0, kv);
                    s0 = _mm_sha256rnds2_epu32(s0, s1, _mm_shuffle_epi32::<0x0E>(kv));
                }};
            }
            macro_rules! sched {
                ($m0:ident, $m1:ident, $m2:ident, $m3:ident) => {
                    $m0 = _mm_sha256msg2_epu32(
                        _mm_add_epi32(
                            _mm_sha256msg1_epu32($m0, $m1),
                            _mm_alignr_epi8::<4>($m3, $m2),
                        ),
                        $m3,
                    )
                };
            }
            let mut k = 0;
            while k < 48 {
                quad!(m0, k);
                sched!(m0, m1, m2, m3);
                quad!(m1, k + 4);
                sched!(m1, m2, m3, m0);
                quad!(m2, k + 8);
                sched!(m2, m3, m0, m1);
                quad!(m3, k + 12);
                sched!(m3, m0, m1, m2);
                k += 16;
            }
            quad!(m0, 48);
            quad!(m1, 52);
            quad!(m2, 56);
            quad!(m3, 60);

            s0 = _mm_add_epi32(s0, save0);
            s1 = _mm_add_epi32(s1, save1);
            // Unpack ABEF / CDGH back to `a..h` in order.
            let feba = _mm_shuffle_epi32::<0x1B>(s0);
            let dchg = _mm_shuffle_epi32::<0xB1>(s1);
            let mut out = [0u32; 8];
            _mm_storeu_si128(out.as_mut_ptr().cast(), _mm_blend_epi16::<0xF0>(feba, dchg));
            _mm_storeu_si128(out.as_mut_ptr().add(4).cast(), _mm_alignr_epi8::<8>(dchg, feba));
            out
        }
    }
}

/// Stock SHA-256 (with FIPS `10*len` padding) of an input short enough to pad
/// into one block, i.e. at most 55 bytes.
///
/// Not part of `sha2_eth`, and nothing on the proving path calls it: it exists
/// so [`IV_ETH`] can be *written as its definition* rather than pasted in as an
/// opaque 32-byte constant.
pub const fn sha256(data: &[u8]) -> [u8; OUT_LEN] {
    assert!(data.len() <= BLOCK_LEN - 9, "const SHA-256 takes one padded block");
    let mut block = [0u8; BLOCK_LEN];
    let mut i = 0;
    while i < data.len() {
        block[i] = data[i];
        i += 1;
    }
    block[data.len()] = 0x80;
    let bits = (data.len() as u64) * 8;
    let be = bits.to_be_bytes();
    let mut j = 0;
    while j < 8 {
        block[BLOCK_LEN - 8 + j] = be[j];
        j += 1;
    }
    state_bytes(&compress_portable(IV, block_words(&block)))
}

/// `sha2_eth`'s initial chaining value, `sha256("Ethereum")`.
pub const IV_ETH: [u32; 8] = {
    let d = sha256(b"Ethereum");
    let mut h = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        h[i] = u32::from_be_bytes([d[4 * i], d[4 * i + 1], d[4 * i + 2], d[4 * i + 3]]);
        i += 1;
    }
    h
};

/// The length block: `bits` as a 512-bit big-endian integer, so its 16 words
/// are all zero but the last two.
#[inline]
const fn len_block(bits: u128) -> [u32; 16] {
    let mut m = [0u32; 16];
    m[12] = (bits >> 96) as u32;
    m[13] = (bits >> 64) as u32;
    m[14] = (bits >> 32) as u32;
    m[15] = bits as u32;
    m
}

/// The chaining value every `n`-byte `sha2_eth` starts its message blocks
/// from: `C(IV_ETH, len_block(8n))`.
///
/// This is the whole point of the length-first ordering. It is `const`, so a
/// call site that knows its length pays no compression for the length block:
/// the VM's `Sha2` opcode takes this as its default (or bytecode-supplied)
/// chaining value and the guest gets the same constant folded in.
#[inline]
pub const fn iv_for_len(n_bytes: u64) -> [u32; 8] {
    compress_portable(IV_ETH, len_block((n_bytes as u128) * 8))
}

/// [`iv_for_len`] at 64 bytes: the Fiat-Shamir sponge step, the Merkle parent,
/// and the `Sha2` opcode's default chaining value all hash exactly one block.
pub const IV_64: [u32; 8] = iv_for_len(64);

/// [`BLOCK_LEN`] as the type [`iv_at`] matches on.
const BLOCK_LEN_U64: u64 = BLOCK_LEN as u64;

/// [`iv_for_len`] at a length known only at run time.
///
/// A `const fn` called with a runtime argument is just a function, so
/// [`iv_for_len`] would otherwise run a full **portable** compression on every
/// hash: measured at 137 ns against 14 ns for the compression the caller
/// actually wanted, an 11x tax on the Fiat-Shamir sponge and on PoW grinding.
/// So take the constant at the one length the protocol hashes in bulk, and the
/// hardware compression otherwise.
#[inline]
fn iv_at(n_bytes: u64) -> [u32; 8] {
    match n_bytes {
        BLOCK_LEN_U64 => IV_64,
        n => compress(IV_ETH, len_block((n as u128) * 8)),
    }
}

/// `sha2_eth` of exactly 64 bytes: ONE compression from the constant [`IV_64`],
/// and nothing else.
///
/// The sponge step, the Merkle parent and the `Sha2` opcode are all this shape,
/// and between them they are most of the hashing a proof does, so they get a
/// path on which the length cannot be anything but a constant.
pub fn hash_block(block: &[u8; BLOCK_LEN]) -> [u8; OUT_LEN] {
    state_bytes(&compress(IV_64, block_words(block)))
}

/// `sha2_eth` over bytes, streaming.
///
/// The total length has to be known before the first block, so it is a
/// constructor argument rather than something [`Self::finalize`] discovers.
/// `update` calls must add up to exactly that many bytes.
#[derive(Clone)]
pub struct Hasher {
    h: [u32; 8],
    buf: [u8; BLOCK_LEN],
    /// Bytes currently in `buf`, in `0..BLOCK_LEN`.
    buf_len: usize,
    /// Bytes fed so far, across `update` calls.
    fed: usize,
    /// Bytes the caller promised.
    total: usize,
}

impl Hasher {
    /// A hasher for a message of exactly `total` bytes.
    pub fn new(total: usize) -> Self {
        Self {
            h: iv_at(total as u64),
            buf: [0u8; BLOCK_LEN],
            buf_len: 0,
            fed: 0,
            total,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        self.fed += data.len();
        debug_assert!(self.fed <= self.total, "fed more than the announced length");
        while !data.is_empty() {
            let take = (BLOCK_LEN - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == BLOCK_LEN {
                self.h = compress(self.h, block_words(&self.buf));
                self.buf_len = 0;
            }
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        assert_eq!(
            self.fed, self.total,
            "hasher fed {} bytes, announced {}",
            self.fed, self.total
        );
        let mut h = self.h;
        if self.buf_len > 0 {
            // The zero fill: `padd` rounds the message up to a whole block.
            let mut block = self.buf;
            block[self.buf_len..].fill(0);
            h = compress(h, block_words(&block));
        }
        state_bytes(&h)
    }
}

/// One-shot `sha2_eth`.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    let mut h = iv_at(data.len() as u64);
    let mut chunks = data.chunks_exact(BLOCK_LEN);
    for block in &mut chunks {
        h = compress(h, block_words(block.try_into().unwrap()));
    }
    let tail = chunks.remainder();
    if !tail.is_empty() {
        let mut block = [0u8; BLOCK_LEN];
        block[..tail.len()].copy_from_slice(tail);
        h = compress(h, block_words(&block));
    }
    state_bytes(&h)
}

// ---------------------------------------------------------------------------
// Batched (transposed) hashing
//
// `LANES` independent inputs are hashed together with the state transposed
// across lanes: state word `i` becomes one SIMD vector holding that word for
// every lane, so a round is elementwise 32-bit work with no cross-lane traffic.
// Equal-length inputs share one `iv_for_len`, so the whole batch also shares
// its starting state.
//
// The compression is written once, generically over [`Lanes32`], and
// instantiated per backend. Two details carried over from the BLAKE2s kernel
// this replaces, both measured there:
//
// - **The message schedule stays in memory.** All 64 words are expanded into a
//   stack buffer up front, so each round's `add` folds its load
//   (`vpaddd zmm, zmm, mem`). Holding the 16-word window in registers instead
//   costs half the register file and the round spills.
// - **Every index is a compile-time literal**, via the unrolled `rounds!`
//   macro, which also lets the eight-way register rotation be a renaming rather
//   than eight moves per round.
// ---------------------------------------------------------------------------

// Everything from here to `hash_many_dyn` is unreachable on a target whose CPU
// hashes SHA-256 itself: `hw` serves the batch there too, so the attributes
// below say so rather than letting seven dead-code warnings accumulate.

/// One state word across all lanes of a batch: a vector of `WIDTH` 32-bit
/// lanes. The batched compression is written once over this trait, so each
/// backend supplies only add / xor / and / the rotations and shifts.
///
/// # Safety
///
/// `load` and `store` take raw pointers to `WIDTH` contiguous `u32`, and
/// implementors may use unaligned vector accesses, so callers must keep those
/// `WIDTH` elements in bounds.
#[cfg_attr(all(target_arch = "aarch64", target_feature = "sha2"), allow(dead_code))]
trait Lanes32: Copy {
    const WIDTH: usize;

    /// Load `WIDTH` contiguous `u32`.
    ///
    /// # Safety
    /// `p` must be valid for reads of `WIDTH` `u32`.
    unsafe fn load(p: *const u32) -> Self;

    /// Store `WIDTH` contiguous `u32`.
    ///
    /// # Safety
    /// `p` must be valid for writes of `WIDTH` `u32`.
    unsafe fn store(self, p: *mut u32);

    fn splat(x: u32) -> Self;
    fn add(self, o: Self) -> Self;
    fn xor(self, o: Self) -> Self;
    fn and(self, o: Self) -> Self;
    /// Rotate every lane right by `N`.
    fn rotr<const N: u32>(self) -> Self;
    /// Shift every lane right by `N`, zero-filling.
    fn shr<const N: u32>(self) -> Self;

    /// Transpose one 64-byte block from each of `WIDTH` inputs into `buf`,
    /// decoding each 4-byte group as a big-endian word, so that
    /// `buf[w * WIDTH + l]` is lane `l`'s word `w`.
    ///
    /// The default reads word by word, which the compiler turns into strided
    /// vector gathers: 32 `vpgatherqd` per block, enough to cost more than the
    /// rounds it feeds. Backends with a shuffle network override it.
    ///
    /// # Safety
    /// Every `inputs[l]` must be valid for 64 readable bytes at `off`, and
    /// `buf` must hold at least `16 * WIDTH` words.
    #[inline(always)]
    unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
        debug_assert_eq!(inputs.len(), Self::WIDTH);
        debug_assert!(buf.len() >= 16 * Self::WIDTH);
        for (lane, &input) in inputs.iter().enumerate() {
            for w in 0..16 {
                // SAFETY: the caller guarantees 64 readable bytes at `off`.
                let word = unsafe { input.add(off + 4 * w).cast::<u32>().read_unaligned() };
                buf[w * Self::WIDTH + lane] = u32::from_be(word);
            }
        }
    }

    /// Write the finished chaining values out as `WIDTH` consecutive 32-byte
    /// big-endian digests: the reverse of [`Lanes32::transpose`], over 8 words
    /// rather than 16.
    ///
    /// # Safety
    /// `out` must be valid for writes of `WIDTH * OUT_LEN` bytes.
    #[inline(always)]
    unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
        let mut words = [0u32; 8 * 16];
        for (i, hi) in h.iter().enumerate() {
            // SAFETY: `words` holds 8 * 16 >= 8 * WIDTH elements.
            unsafe { hi.store(words.as_mut_ptr().add(i * Self::WIDTH)) };
        }
        for lane in 0..Self::WIDTH {
            for i in 0..8 {
                let bytes = words[i * Self::WIDTH + lane].to_be_bytes();
                // SAFETY: `lane * 32 + i * 4 + 4 <= WIDTH * 32`.
                unsafe {
                    out.add(lane * OUT_LEN + 4 * i)
                        .copy_from_nonoverlapping(bytes.as_ptr(), 4)
                };
            }
        }
    }
}

/// SHA-256's ten right-rotation amounts, paired with their complements, as
/// **literals**: `for_each_rotation!(f, n)` expands to a match dispatching `n`
/// to `f!(N, 32 - N)`.
///
/// Every backend's rotation is either a shift pair or an immediate-form
/// instruction, and Rust admits a const generic only as a standalone turbofish
/// argument, never inside `32 - N`, so the complement has to arrive as a
/// literal. Ten arms, all of which the compiler folds away for a literal `N`.
macro_rules! for_each_rotation {
    ($f:ident, $n:expr) => {
        match $n {
            2 => $f!(2, 30),
            6 => $f!(6, 26),
            7 => $f!(7, 25),
            11 => $f!(11, 21),
            13 => $f!(13, 19),
            17 => $f!(17, 15),
            18 => $f!(18, 14),
            19 => $f!(19, 13),
            22 => $f!(22, 10),
            25 => $f!(25, 7),
            _ => unreachable!("SHA-256 rotates right by 2, 6, 7, 11, 13, 17, 18, 19, 22 or 25"),
        }
    };
}

/// The two right-shift amounts (`sigma_0`'s and `sigma_1`'s), as literals; see
/// [`for_each_rotation`].
macro_rules! for_each_shift {
    ($f:ident, $n:expr) => {
        match $n {
            3 => $f!(3),
            10 => $f!(10),
            _ => unreachable!("SHA-256 shifts right by 3 or 10"),
        }
    };
}

/// The portable backend, and the reference the SIMD ones are checked against.
///
/// Unused by the library whenever a SIMD backend is available for the target,
/// since the dispatch is resolved at compile time, but always exercised by
/// `every_backend_matches_scalar`.
#[allow(dead_code)]
#[derive(Clone, Copy)]
struct Scalar8([u32; 8]);

impl Lanes32 for Scalar8 {
    const WIDTH: usize = 8;

    #[inline(always)]
    unsafe fn load(p: *const u32) -> Self {
        Self(std::array::from_fn(|i| unsafe { *p.add(i) }))
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u32) {
        for (i, x) in self.0.into_iter().enumerate() {
            unsafe { *p.add(i) = x };
        }
    }
    #[inline(always)]
    fn splat(x: u32) -> Self {
        Self([x; 8])
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i].wrapping_add(o.0[i])))
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] ^ o.0[i]))
    }
    #[inline(always)]
    fn and(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] & o.0[i]))
    }
    #[inline(always)]
    fn rotr<const N: u32>(self) -> Self {
        Self(std::array::from_fn(|i| self.0[i].rotate_right(N)))
    }
    #[inline(always)]
    fn shr<const N: u32>(self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] >> N))
    }
}

#[cfg(target_arch = "x86_64")]
mod x86 {
    use super::{Lanes32, OUT_LEN};
    use core::arch::x86_64::*;

    /// Byte-reverse each 32-bit lane of a 16-byte group: the big-endian decode
    /// SHA-256's block loading and digest store both need.
    #[cfg_attr(not(target_feature = "avx2"), allow(dead_code))]
    const BSWAP32: [i8; 16] = [3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12];

    /// AVX2: eight lanes. Every SHA-256 rotation is odd, so each is a shift
    /// pair here; AVX-512's `vprold` is what makes this kernel cheap.
    ///
    /// Unused by the library on an AVX-512 target (the dispatch is compile
    /// time), but always exercised by `every_backend_matches_scalar`.
    #[cfg_attr(any(target_feature = "avx512f", not(target_feature = "avx2")), allow(dead_code))]
    #[derive(Clone, Copy)]
    pub(super) struct Avx2(__m256i);

    #[cfg_attr(any(target_feature = "avx512f", not(target_feature = "avx2")), allow(dead_code))]
    impl Avx2 {
        #[inline(always)]
        fn bswap(self) -> Self {
            unsafe {
                let half = _mm_loadu_si128(BSWAP32.as_ptr().cast());
                Self(_mm256_shuffle_epi8(self.0, _mm256_set_m128i(half, half)))
            }
        }
    }

    impl Lanes32 for Avx2 {
        const WIDTH: usize = 8;

        #[inline(always)]
        unsafe fn load(p: *const u32) -> Self {
            Self(unsafe { _mm256_loadu_si256(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u32) {
            unsafe { _mm256_storeu_si256(p.cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u32) -> Self {
            Self(unsafe { _mm256_set1_epi32(x as i32) })
        }
        #[inline(always)]
        fn add(self, o: Self) -> Self {
            Self(unsafe { _mm256_add_epi32(self.0, o.0) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(self.0, o.0) })
        }
        #[inline(always)]
        fn and(self, o: Self) -> Self {
            Self(unsafe { _mm256_and_si256(self.0, o.0) })
        }
        #[inline(always)]
        fn rotr<const N: u32>(self) -> Self {
            let v = self.0;
            macro_rules! r {
                ($k:literal, $m:literal) => {
                    Self(unsafe { _mm256_or_si256(_mm256_srli_epi32::<$k>(v), _mm256_slli_epi32::<$m>(v)) })
                };
            }
            for_each_rotation!(r, N)
        }
        #[inline(always)]
        fn shr<const N: u32>(self) -> Self {
            let v = self.0;
            macro_rules! s {
                ($k:literal) => {
                    Self(unsafe { _mm256_srli_epi32::<$k>(v) })
                };
            }
            for_each_shift!(s, N)
        }

        /// Two 8x8 32-bit transposes, then the big-endian decode: each input's
        /// 64-byte block is two `ymm`, words 0..8 and 8..16, and each half
        /// transposes independently.
        #[inline(always)]
        unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
            debug_assert_eq!(inputs.len(), 8);
            debug_assert!(buf.len() >= 128);
            unsafe {
                for half in 0..2 {
                    let r: [__m256i; 8] =
                        std::array::from_fn(|l| _mm256_loadu_si256(inputs[l].add(off + 32 * half).cast()));
                    let mut t = [_mm256_setzero_si256(); 8];
                    for k in 0..4 {
                        t[2 * k] = _mm256_unpacklo_epi32(r[2 * k], r[2 * k + 1]);
                        t[2 * k + 1] = _mm256_unpackhi_epi32(r[2 * k], r[2 * k + 1]);
                    }
                    let s: [__m256i; 8] = [
                        _mm256_unpacklo_epi64(t[0], t[2]),
                        _mm256_unpackhi_epi64(t[0], t[2]),
                        _mm256_unpacklo_epi64(t[1], t[3]),
                        _mm256_unpackhi_epi64(t[1], t[3]),
                        _mm256_unpacklo_epi64(t[4], t[6]),
                        _mm256_unpackhi_epi64(t[4], t[6]),
                        _mm256_unpacklo_epi64(t[5], t[7]),
                        _mm256_unpackhi_epi64(t[5], t[7]),
                    ];
                    for k in 0..4 {
                        let w = 8 * half + k;
                        let lo = Self(_mm256_permute2x128_si256(s[k], s[k + 4], 0x20)).bswap();
                        let hi = Self(_mm256_permute2x128_si256(s[k], s[k + 4], 0x31)).bswap();
                        lo.store(buf.as_mut_ptr().add(w * 8));
                        hi.store(buf.as_mut_ptr().add((w + 4) * 8));
                    }
                }
            }
        }

        #[inline(always)]
        unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
            let be: [Self; 8] = std::array::from_fn(|i| h[i].bswap());
            let mut words = [0u32; 64];
            for (i, hi) in be.iter().enumerate() {
                // SAFETY: `words` holds 64 = 8 * WIDTH elements.
                unsafe { hi.store(words.as_mut_ptr().add(8 * i)) };
            }
            for lane in 0..8 {
                for i in 0..8 {
                    // SAFETY: `lane * 32 + i * 4 + 4 <= 8 * 32`.
                    unsafe {
                        out.add(lane * OUT_LEN + 4 * i)
                            .copy_from_nonoverlapping(words[8 * i + lane].to_ne_bytes().as_ptr(), 4)
                    };
                }
            }
        }
    }

    /// AVX-512: sixteen lanes, and `vprord` makes every rotation one
    /// instruction, which matters more here than it did for BLAKE2s since
    /// SHA-256 has ten distinct odd rotation amounts and no byte-aligned one.
    ///
    /// Gated on `avx512bw` as well as `avx512f`, because the big-endian decode
    /// is `vpshufb zmm` (`_mm512_shuffle_epi8`), which is a BW instruction.
    /// Gating on `avx512f` alone compiles, but LLVM then refuses to inline the
    /// intrinsic into a caller that does not declare BW and emits a real call
    /// per block instead; on an F-without-BW part it would be a `#UD`.
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw"))]
    #[derive(Clone, Copy)]
    pub(super) struct Avx512(__m512i);

    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw"))]
    impl Avx512 {
        #[inline(always)]
        fn bswap(self) -> Self {
            unsafe {
                let quarter = _mm_loadu_si128(BSWAP32.as_ptr().cast());
                Self(_mm512_shuffle_epi8(self.0, _mm512_broadcast_i32x4(quarter)))
            }
        }
    }

    #[cfg(all(target_feature = "avx512f", target_feature = "avx512bw"))]
    impl Lanes32 for Avx512 {
        const WIDTH: usize = 16;

        #[inline(always)]
        unsafe fn load(p: *const u32) -> Self {
            Self(unsafe { _mm512_loadu_si512(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u32) {
            unsafe { _mm512_storeu_si512(p.cast(), self.0) }
        }
        #[inline(always)]
        fn splat(x: u32) -> Self {
            Self(unsafe { _mm512_set1_epi32(x as i32) })
        }
        #[inline(always)]
        fn add(self, o: Self) -> Self {
            Self(unsafe { _mm512_add_epi32(self.0, o.0) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { _mm512_xor_si512(self.0, o.0) })
        }
        #[inline(always)]
        fn and(self, o: Self) -> Self {
            Self(unsafe { _mm512_and_si512(self.0, o.0) })
        }
        #[inline(always)]
        fn rotr<const N: u32>(self) -> Self {
            let v = self.0;
            macro_rules! r {
                ($k:literal, $_m:literal) => {
                    Self(unsafe { _mm512_ror_epi32::<$k>(v) })
                };
            }
            for_each_rotation!(r, N)
        }
        #[inline(always)]
        fn shr<const N: u32>(self) -> Self {
            let v = self.0;
            macro_rules! s {
                ($k:literal) => {
                    Self(unsafe { _mm512_srli_epi32::<$k>(v) })
                };
            }
            for_each_shift!(s, N)
        }

        /// The 8x16 -> 16x8 digest transpose. Phases 1 and 2 of the block
        /// network over eight rows leave lane `4L + c`'s first four words in
        /// `s[c]`'s 128-bit lane `L` and its last four in `s[4 + c]`'s, so each
        /// digest is two 128-bit extracts rather than eight scalar stores.
        #[inline(always)]
        unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
            unsafe {
                let mut s = [_mm512_setzero_si512(); 8];
                for a in 0..2 {
                    let r = |i: usize| h[4 * a + i].bswap().0;
                    let (r0, r1, r2, r3) = (r(0), r(1), r(2), r(3));
                    let lo01 = _mm512_unpacklo_epi32(r0, r1);
                    let hi01 = _mm512_unpackhi_epi32(r0, r1);
                    let lo23 = _mm512_unpacklo_epi32(r2, r3);
                    let hi23 = _mm512_unpackhi_epi32(r2, r3);
                    s[4 * a] = _mm512_unpacklo_epi64(lo01, lo23);
                    s[4 * a + 1] = _mm512_unpackhi_epi64(lo01, lo23);
                    s[4 * a + 2] = _mm512_unpacklo_epi64(hi01, hi23);
                    s[4 * a + 3] = _mm512_unpackhi_epi64(hi01, hi23);
                }
                macro_rules! lane {
                    ($l:expr, $c:expr) => {{
                        let p = out.add((4 * $l + $c) * OUT_LEN);
                        _mm_storeu_si128(p.cast(), _mm512_extracti32x4_epi32::<$l>(s[$c]));
                        _mm_storeu_si128(p.add(16).cast(), _mm512_extracti32x4_epi32::<$l>(s[4 + $c]));
                    }};
                }
                lane!(0, 0);
                lane!(0, 1);
                lane!(0, 2);
                lane!(0, 3);
                lane!(1, 0);
                lane!(1, 1);
                lane!(1, 2);
                lane!(1, 3);
                lane!(2, 0);
                lane!(2, 1);
                lane!(2, 2);
                lane!(2, 3);
                lane!(3, 0);
                lane!(3, 1);
                lane!(3, 2);
                lane!(3, 3);
            }
        }

        /// A 16x16 32-bit transpose, then the big-endian decode: each input's
        /// 64-byte block is exactly one `zmm`, so the block loads are sixteen
        /// full-width loads and the transpose is a shuffle network. Two
        /// `unpack` phases put four rows' worth of one column into each 128-bit
        /// lane, then two `shuffle_i32x4` phases collect the four row groups.
        #[inline(always)]
        unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
            debug_assert_eq!(inputs.len(), 16);
            debug_assert!(buf.len() >= 256);
            unsafe {
                let r: [__m512i; 16] = std::array::from_fn(|l| _mm512_loadu_si512(inputs[l].add(off).cast()));
                // Phase 1 and 2: `s[4 * a + c]`'s 128-bit lane L holds column
                // `4L + c` of rows `4a .. 4a + 4`.
                let mut s = [_mm512_setzero_si512(); 16];
                for a in 0..4 {
                    let (r0, r1, r2, r3) = (r[4 * a], r[4 * a + 1], r[4 * a + 2], r[4 * a + 3]);
                    let lo01 = _mm512_unpacklo_epi32(r0, r1);
                    let hi01 = _mm512_unpackhi_epi32(r0, r1);
                    let lo23 = _mm512_unpacklo_epi32(r2, r3);
                    let hi23 = _mm512_unpackhi_epi32(r2, r3);
                    s[4 * a] = _mm512_unpacklo_epi64(lo01, lo23);
                    s[4 * a + 1] = _mm512_unpackhi_epi64(lo01, lo23);
                    s[4 * a + 2] = _mm512_unpacklo_epi64(hi01, hi23);
                    s[4 * a + 3] = _mm512_unpackhi_epi64(hi01, hi23);
                }
                // Word `w` needs 128-bit lane `w / 4` of the four `s` entries
                // whose `c` is `w % 4`. `IMM_L` broadcasts that lane, and 0x88
                // then takes lanes 0 and 2 of each half.
                macro_rules! word {
                    ($w:expr) => {{
                        const L: i32 = ($w / 4) as i32;
                        const C: usize = ($w % 4) as usize;
                        const IMM_L: i32 = L * 0x55;
                        let p = _mm512_shuffle_i32x4::<IMM_L>(s[C], s[4 + C]);
                        let q = _mm512_shuffle_i32x4::<IMM_L>(s[8 + C], s[12 + C]);
                        Self(_mm512_shuffle_i32x4::<0x88>(p, q))
                            .bswap()
                            .store(buf.as_mut_ptr().add($w * 16));
                    }};
                }
                word!(0);
                word!(1);
                word!(2);
                word!(3);
                word!(4);
                word!(5);
                word!(6);
                word!(7);
                word!(8);
                word!(9);
                word!(10);
                word!(11);
                word!(12);
                word!(13);
                word!(14);
                word!(15);
            }
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    use super::{Lanes32, OUT_LEN};
    use core::arch::aarch64::*;

    /// NEON: four lanes. Every SHA-256 rotation is a shift pair, so this
    /// backend is issue-bound rather than latency-bound, unlike the BLAKE2s one
    /// it replaces. It is also not what the library picks on any aarch64 target
    /// with the crypto extension, where the `sha256h` path is several times
    /// faster; it stays compiled and tested as the portable fallback.
    #[cfg_attr(target_feature = "sha2", allow(dead_code))]
    #[derive(Clone, Copy)]
    pub(super) struct Neon(uint32x4_t);

    impl Lanes32 for Neon {
        const WIDTH: usize = 4;

        #[inline(always)]
        unsafe fn load(p: *const u32) -> Self {
            Self(unsafe { vld1q_u32(p) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u32) {
            unsafe { vst1q_u32(p, self.0) }
        }
        #[inline(always)]
        fn splat(x: u32) -> Self {
            Self(unsafe { vdupq_n_u32(x) })
        }
        #[inline(always)]
        fn add(self, o: Self) -> Self {
            Self(unsafe { vaddq_u32(self.0, o.0) })
        }
        #[inline(always)]
        fn xor(self, o: Self) -> Self {
            Self(unsafe { veorq_u32(self.0, o.0) })
        }
        #[inline(always)]
        fn and(self, o: Self) -> Self {
            Self(unsafe { vandq_u32(self.0, o.0) })
        }
        #[inline(always)]
        fn rotr<const N: u32>(self) -> Self {
            let v = self.0;
            macro_rules! r {
                ($k:literal, $m:literal) => {
                    Self(rot_sri::<$k, $m>(v))
                };
            }
            for_each_rotation!(r, N)
        }
        #[inline(always)]
        fn shr<const N: u32>(self) -> Self {
            let v = self.0;
            macro_rules! s {
                ($k:literal) => {
                    Self(unsafe { vshrq_n_u32::<$k>(v) })
                };
            }
            for_each_shift!(s, N)
        }

        /// Four 4x4 32-bit transposes plus the big-endian decode. Quarter `q`
        /// of every lane's block holds words `4q..4q+4`, which is 64 contiguous
        /// bytes of `buf`, so each quarter transposes independently.
        #[inline(always)]
        unsafe fn transpose(inputs: &[*const u8], off: usize, buf: &mut [u32]) {
            debug_assert_eq!(inputs.len(), 4);
            debug_assert!(buf.len() >= 64);
            unsafe {
                // `vld1q_u32` would claim 4-byte alignment, which a `&[u8]`
                // input does not have; the `u8` form is the unaligned load, and
                // the same instruction. `vrev32q_u8` is the big-endian decode.
                let r: [uint32x4_t; 16] = std::array::from_fn(|i| {
                    vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(inputs[i / 4].add(off + 16 * (i % 4)))))
                });
                for q in 0..4 {
                    let [a, b, c, d] = [r[q], r[4 + q], r[8 + q], r[12 + q]];
                    for (j, o) in transpose4(a, b, c, d).into_iter().enumerate() {
                        vst1q_u32(buf.as_mut_ptr().add(16 * q + 4 * j), o);
                    }
                }
            }
        }

        /// The same network over the eight chaining words: `h[0..4]` gives each
        /// lane's first 16 digest bytes and `h[4..8]` its second.
        #[inline(always)]
        unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
            unsafe {
                for half in 0..2 {
                    let [a, b, c, d] = [h[4 * half], h[4 * half + 1], h[4 * half + 2], h[4 * half + 3]];
                    for (lane, o) in transpose4(a.0, b.0, c.0, d.0).into_iter().enumerate() {
                        // Unaligned, as in `transpose`: `out` is bytes.
                        vst1q_u8(out.add(lane * OUT_LEN + 16 * half), vrev32q_u8(vreinterpretq_u8_u32(o)));
                    }
                }
            }
        }
    }

    /// `shl` then `sri` (shift right and insert), the one-instruction-shorter
    /// rotate.
    ///
    /// Written as `asm!` because LLVM rewrites both this and the `vsri`
    /// intrinsic into `shl` plus `usra`, which is correct (the shifted-out bits
    /// are zero, so inserting and accumulating agree) but a cycle longer, and
    /// SHA-256 puts six of these on each round's chain.
    #[inline(always)]
    #[cfg_attr(all(target_arch = "aarch64", target_feature = "sha2"), allow(dead_code))]
    fn rot_sri<const N: u32, const SHL: i32>(v: uint32x4_t) -> uint32x4_t {
        unsafe {
            let mut out = vshlq_n_u32::<SHL>(v);
            std::arch::asm!(
                "sri {out:v}.4s, {v:v}.4s, #{n}",
                out = inout(vreg) out,
                v = in(vreg) v,
                n = const N,
                options(pure, nomem, nostack)
            );
            out
        }
    }

    /// Transpose four vectors of four 32-bit words: `out[j][i]` is `in[i][j]`.
    #[inline(always)]
    #[cfg_attr(all(target_arch = "aarch64", target_feature = "sha2"), allow(dead_code))]
    fn transpose4(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t, d: uint32x4_t) -> [uint32x4_t; 4] {
        unsafe {
            let (ab0, ab1) = (vtrn1q_u32(a, b), vtrn2q_u32(a, b));
            let (cd0, cd1) = (vtrn1q_u32(c, d), vtrn2q_u32(c, d));
            let pair = |x, y| {
                (
                    vreinterpretq_u32_u64(vtrn1q_u64(vreinterpretq_u64_u32(x), vreinterpretq_u64_u32(y))),
                    vreinterpretq_u32_u64(vtrn2q_u64(vreinterpretq_u64_u32(x), vreinterpretq_u64_u32(y))),
                )
            };
            let ((o0, o2), (o1, o3)) = (pair(ab0, cd0), pair(ab1, cd1));
            [o0, o1, o2, o3]
        }
    }
}

/// One SHA-256 round over LITERAL state names and a literal round index. The
/// eight-way register shift is a *renaming* at the call site rather than eight
/// moves: this round writes the new `e` over `$d` and the new `a` over `$h`,
/// and the next invocation rotates its arguments right by one.
macro_rules! round {
    ($a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $w:ident, $t:expr) => {{
        let s1 = $e.rotr::<6>().xor($e.rotr::<11>()).xor($e.rotr::<25>());
        let ch = $g.xor($e.and($f.xor($g)));
        let t1 = $h
            .add(s1)
            .add(ch)
            .add(S::splat(K[$t]))
            .add(S::load($w.add($t * S::WIDTH)));
        let s0 = $a.rotr::<2>().xor($a.rotr::<13>()).xor($a.rotr::<22>());
        let maj = $a.xor($a.xor($b).and($a.xor($c)));
        $d = $d.add(t1);
        $h = t1.add(s0.add(maj));
    }};
}

/// Eight rounds starting at `$t`, after which the names are back in place.
macro_rules! rounds8 {
    ($a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $w:ident, $t:expr) => {{
        round!($a, $b, $c, $d, $e, $f, $g, $h, $w, $t);
        round!($h, $a, $b, $c, $d, $e, $f, $g, $w, $t + 1);
        round!($g, $h, $a, $b, $c, $d, $e, $f, $w, $t + 2);
        round!($f, $g, $h, $a, $b, $c, $d, $e, $w, $t + 3);
        round!($e, $f, $g, $h, $a, $b, $c, $d, $w, $t + 4);
        round!($d, $e, $f, $g, $h, $a, $b, $c, $w, $t + 5);
        round!($c, $d, $e, $f, $g, $h, $a, $b, $w, $t + 6);
        round!($b, $c, $d, $e, $f, $g, $h, $a, $w, $t + 7);
    }};
}

/// Expand the 16 transposed message words at `buf` into all 64, in place.
///
/// # Safety
/// `buf` must hold `64 * S::WIDTH` words, the first `16 * S::WIDTH` of them the
/// transposed block.
#[inline(always)]
#[cfg_attr(all(target_arch = "aarch64", target_feature = "sha2"), allow(dead_code))]
unsafe fn expand_schedule<S: Lanes32>(buf: *mut u32) {
    for t in 16..ROUNDS {
        // SAFETY: every index is below 64, and the caller sized `buf`.
        unsafe {
            let at = |i: usize| S::load(buf.add(i * S::WIDTH));
            let x = at(t - 15);
            let s0 = x.rotr::<7>().xor(x.rotr::<18>()).xor(x.shr::<3>());
            let y = at(t - 2);
            let s1 = y.rotr::<17>().xor(y.rotr::<19>()).xor(y.shr::<10>());
            at(t - 16).add(s0).add(at(t - 7)).add(s1).store(buf.add(t * S::WIDTH));
        }
    }
}

/// One transposed compression across `S::WIDTH` lanes. `buf` holds the block as
/// 16 groups of `S::WIDTH` words on entry and is clobbered with the expanded
/// schedule.
///
/// # Safety
/// `buf` must be valid for reads and writes of `64 * S::WIDTH` `u32`.
#[inline(always)]
#[cfg_attr(all(target_arch = "aarch64", target_feature = "sha2"), allow(dead_code))]
unsafe fn compress_lanes<S: Lanes32>(h: &mut [S; 8], buf: *mut u32) {
    // SAFETY: the caller sized `buf`; every offset below is `< 64 * WIDTH`.
    unsafe { expand_schedule::<S>(buf) };
    let (mut a, mut b, mut c, mut d) = (h[0], h[1], h[2], h[3]);
    let (mut e, mut f, mut g, mut hh) = (h[4], h[5], h[6], h[7]);
    // SAFETY: as above.
    unsafe {
        rounds8!(a, b, c, d, e, f, g, hh, buf, 0);
        rounds8!(a, b, c, d, e, f, g, hh, buf, 8);
        rounds8!(a, b, c, d, e, f, g, hh, buf, 16);
        rounds8!(a, b, c, d, e, f, g, hh, buf, 24);
        rounds8!(a, b, c, d, e, f, g, hh, buf, 32);
        rounds8!(a, b, c, d, e, f, g, hh, buf, 40);
        rounds8!(a, b, c, d, e, f, g, hh, buf, 48);
        rounds8!(a, b, c, d, e, f, g, hh, buf, 56);
    }
    for (slot, v) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
        *slot = slot.add(v);
    }
}

/// Hash `S::WIDTH` inputs of `len` bytes (a nonzero multiple of 64) into
/// `S::WIDTH` consecutive 32-byte digests at `out`.
///
/// `iv` is the caller's [`iv_at`] for `len`, passed in rather than recomputed:
/// every group of one call shares it, and recomputing it here would put a
/// portable compression on each group (see [`iv_at`]).
///
/// # Safety
/// Every `inputs[l]` must be valid for `len` bytes, `out` for
/// `S::WIDTH * OUT_LEN` bytes, `buf` must hold `64 * S::WIDTH` words, and `len`
/// must be a nonzero multiple of 64.
#[inline(always)]
#[cfg_attr(all(target_arch = "aarch64", target_feature = "sha2"), allow(dead_code))]
unsafe fn hash_group<S: Lanes32>(inputs: &[*const u8], len: usize, iv: &[u32; 8], buf: &mut [u32], out: *mut u8) {
    debug_assert!(len > 0 && len.is_multiple_of(BLOCK_LEN));
    let mut h: [S; 8] = std::array::from_fn(|i| S::splat(iv[i]));
    for b in 0..len / BLOCK_LEN {
        // SAFETY: `b * 64 + 64 <= len`, so the window is inside every input.
        unsafe {
            S::transpose(inputs, b * BLOCK_LEN, buf);
            compress_lanes::<S>(&mut h, buf.as_mut_ptr());
        }
    }
    // SAFETY: the caller guarantees `WIDTH * OUT_LEN` writable bytes at `out`.
    unsafe { S::store_digests(&h, out) };
}

/// Drive the whole batch through one backend, scalar-tailing the last partial
/// group.
///
/// # Safety
/// `data` must hold `n * len` bytes and `out` `n * OUT_LEN`, with `len` a
/// nonzero multiple of 64.
#[inline(always)]
#[cfg_attr(all(target_arch = "aarch64", target_feature = "sha2"), allow(dead_code))]
unsafe fn hash_many_with<S: Lanes32>(data: &[u8], len: usize, out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    let groups = n / S::WIDTH;
    let iv = iv_at(len as u64);
    let mut ptrs = [std::ptr::null::<u8>(); 16];
    // The widest backend's expanded schedule, 64 words by 16 lanes. One buffer
    // for the whole call keeps it on the stack, so the round's message operand
    // is a memory load, without paying to clear it per group.
    let mut buf = [0u32; 64 * 16];
    for g in 0..groups {
        let base = g * S::WIDTH;
        for (l, slot) in ptrs[..S::WIDTH].iter_mut().enumerate() {
            *slot = data[(base + l) * len..].as_ptr();
        }
        // SAFETY: each pointer has `len` readable bytes, and the output window
        // `[base, base + WIDTH)` is inside `out`.
        unsafe {
            hash_group::<S>(
                &ptrs[..S::WIDTH],
                len,
                &iv,
                &mut buf,
                out.as_mut_ptr().add(base * OUT_LEN),
            );
        }
    }
    for i in groups * S::WIDTH..n {
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&hash(&data[i * len..(i + 1) * len]));
    }
}

/// Independent inputs hashed per batch by the widest backend this build
/// targets: 16 on AVX-512, 8 on AVX2, 4 on NEON. Public so callers can size
/// their groups; the batched entry points handle any count and scalar-tail the
/// remainder.
pub const LANES: usize = if cfg!(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw"
)) {
    16
} else if cfg!(target_arch = "x86_64") {
    8
} else if cfg!(target_arch = "aarch64") {
    4
} else {
    8
};

/// Batched `sha2_eth` of `data` split into `LEN`-byte inputs, writing one
/// 32-byte digest per input to `out`.
///
/// Byte-identical to [`hash`] per input; the batching only changes how the
/// lanes are scheduled. `LEN` must be a nonzero multiple of 64.
pub fn hash_many<const LEN: usize>(data: &[u8], out: &mut [u8]) {
    const {
        assert!(LEN > 0 && LEN.is_multiple_of(BLOCK_LEN));
    }
    hash_many_dyn(data, LEN, out);
}

/// [`hash_many`] with the input length known only at runtime. Same contract:
/// `len` a nonzero multiple of 64.
pub fn hash_many_dyn(data: &[u8], len: usize, out: &mut [u8]) {
    assert!(
        len > 0 && len.is_multiple_of(BLOCK_LEN),
        "batched inputs are whole blocks"
    );
    let n = out.len() / OUT_LEN;
    assert_eq!(data.len(), n * len);
    assert_eq!(out.len(), n * OUT_LEN);
    // On aarch64 the crypto extension beats four-lane transposition even in
    // bulk, so the `Lanes32` path is the fallback there rather than the choice.
    #[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
    return hw::hash_many(data, len, out);
    // SAFETY (each arm): the asserts above pin the buffer sizes the backends
    // require, and every backend is gated on the feature its intrinsics need.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw"))]
    unsafe {
        hash_many_with::<x86::Avx512>(data, len, out)
    }
    #[cfg(all(
        target_arch = "x86_64",
        not(all(target_feature = "avx512f", target_feature = "avx512bw")),
        target_feature = "avx2"
    ))]
    unsafe {
        hash_many_with::<x86::Avx2>(data, len, out)
    }
    #[cfg(all(target_arch = "aarch64", not(target_feature = "sha2")))]
    unsafe {
        hash_many_with::<arm::Neon>(data, len, out)
    }
    // The arms are exhaustive and disjoint. The x86 fallback is written
    // against `avx2` alone rather than also naming `avx512f`, which is only
    // safe because rustc implies `avx2` from `avx512f`; `+avx512f,-avx2` would
    // expand two arms and compute the batch twice.
    #[cfg(not(any(all(target_arch = "x86_64", target_feature = "avx2"), target_arch = "aarch64")))]
    unsafe {
        hash_many_with::<Scalar8>(data, len, out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn pattern(n: usize) -> Vec<u8> {
        (0..n).map(|i| ((i * 7 + 3) & 0xff) as u8).collect()
    }

    /// `compress` is the stock SHA-256 compression, pinned through the padded
    /// one-block hash: these are `hashlib.sha256` digests.
    #[test]
    fn compress_matches_sha256_vectors() {
        assert_eq!(
            hex(&sha256(b"")),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(&sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hex(&sha256(b"Ethereum")),
            "a13bebeb57e1ea699bd4d2d9ac7e58399644e884b8a8783d96f6d146083f2430"
        );
    }

    /// The CPU's SHA-256 extension computes the same compression as the
    /// portable definition. Only one of the two hardware backends is ever
    /// compiled, and on a target with neither this is `compress` against
    /// itself, so what keeps an untaken path honest is running this on that
    /// target: a wrong repacking here would corrupt every digest silently.
    #[test]
    fn hardware_matches_portable() {
        let mut h = IV_ETH;
        for i in 0..8u32 {
            let m: [u32; 16] = std::array::from_fn(|w| (w as u32).wrapping_mul(0x9E37_79B9) ^ i.rotate_left(11));
            assert_eq!(compress(h, m), compress_portable(h, m), "block {i}");
            h = compress_portable(h, m);
        }
        assert_eq!(compress([0; 8], [0; 16]), compress_portable([0; 8], [0; 16]));
        assert_eq!(
            compress([u32::MAX; 8], [u32::MAX; 16]),
            compress_portable([u32::MAX; 8], [u32::MAX; 16])
        );
    }

    /// The chaining values the whole protocol is built on. `IV_64` in
    /// particular is the `Sha2` opcode's default and the sponge's starting
    /// state, so it is baked into bytecode and into three verifiers.
    #[test]
    fn precomputed_initial_states() {
        let hexed = |h: [u32; 8]| hex(&state_bytes(&h));
        assert_eq!(
            hexed(IV_ETH),
            "a13bebeb57e1ea699bd4d2d9ac7e58399644e884b8a8783d96f6d146083f2430"
        );
        assert_eq!(
            hexed(iv_for_len(32)),
            "293212363e032a4949431a2396cccb8af08e5d10027129d1978babffc4046ee6"
        );
        assert_eq!(
            hexed(iv_for_len(48)),
            "da0124bdee36425a446f458455fd2b42c5d387b71e45cf5a30d37c354a7f31eb"
        );
        assert_eq!(
            hexed(IV_64),
            "fe8c354bb51868efc9eca0e2f9f6e1bd1445382e75b3e290b8423842a07f5684"
        );
        assert_eq!(
            hexed(iv_for_len(96)),
            "ce343a789f5c9d963fd9f251d922fb4b2fe0a1bb7d7a291c6c7ba700afe3917a"
        );
    }

    /// `hash` is the length-prefixed Merkle-Damgard spelled out: the length
    /// block, then the zero-padded message, from `IV_ETH`. Recomputing it the
    /// long way here is what pins the fast path's block loop and its
    /// `iv_for_len` shortcut.
    #[test]
    fn hash_is_the_stated_construction() {
        for n in [0usize, 1, 31, 32, 63, 64, 65, 100, 128, 191, 512] {
            let msg = pattern(n);
            let mut full = vec![0u8; BLOCK_LEN - 16];
            full.extend_from_slice(&(8 * n as u128).to_be_bytes());
            full.extend_from_slice(&msg);
            full.resize(BLOCK_LEN + n.div_ceil(BLOCK_LEN) * BLOCK_LEN, 0);
            let mut h = IV_ETH;
            for block in full.chunks_exact(BLOCK_LEN) {
                h = compress(h, block_words(block.try_into().unwrap()));
            }
            assert_eq!(hash(&msg), state_bytes(&h), "{n} bytes");
        }
    }

    /// `hash_block` is a shortcut, not a second hash: it must agree with the
    /// general path on every 64-byte input. It exists only so the sponge and
    /// the Merkle parent reach `IV_64` as a constant instead of deriving it, so
    /// the thing to guard is that the shortcut stayed a shortcut.
    #[test]
    fn hash_block_is_hash_at_64_bytes() {
        for seed in [0usize, 1, 7, 255] {
            let block: [u8; BLOCK_LEN] = std::array::from_fn(|i| ((i * 31 + seed) & 0xff) as u8);
            assert_eq!(hash_block(&block), hash(&block), "seed {seed}");
        }
        assert_eq!(hash_block(&[0u8; BLOCK_LEN]), hash(&[0u8; BLOCK_LEN]));
        assert_eq!(hash_block(&[0xffu8; BLOCK_LEN]), hash(&[0xffu8; BLOCK_LEN]));
    }

    /// `iv_at` is the runtime spelling of `iv_for_len` and must not drift from
    /// it, including at the 64-byte length where it returns a constant instead
    /// of compressing.
    #[test]
    fn iv_at_matches_iv_for_len() {
        for n in [0u64, 1, 32, 48, 63, 64, 65, 96, 128, 704, 5824, 1 << 20] {
            assert_eq!(iv_at(n), iv_for_len(n), "length {n}");
        }
        assert_eq!(iv_at(64), IV_64);
    }

    /// Different lengths cannot collide even when one message is a prefix of
    /// the other, which is what the length-first ordering buys and what the
    /// zero fill on its own would lose.
    #[test]
    fn prefix_free() {
        assert_ne!(hash(&[]), hash(&[0u8]));
        assert_ne!(hash(&[1u8]), hash(&[1u8, 0]));
        assert_ne!(hash(&[7u8; 32]), hash(&[7u8; 33]));
        let mut extended = [0u8; 64];
        extended[..32].copy_from_slice(&[9u8; 32]);
        assert_ne!(hash(&[9u8; 32]), hash(&extended));
    }

    /// Any split of the input into `update` calls gives the same digest, and
    /// agrees with the whole-block fast path in `hash`.
    #[test]
    fn streaming_matches_one_shot() {
        for n in [0usize, 1, 63, 64, 65, 130, 192, 577] {
            let data = pattern(n);
            let want = hash(&data);
            for split in [1usize, 7, 64, 65] {
                let mut h = Hasher::new(n);
                for chunk in data.chunks(split.min(n.max(1))) {
                    h.update(chunk);
                }
                assert_eq!(h.finalize(), want, "{n} bytes in {split}-byte updates");
            }
        }
    }

    /// Every SIMD backend compiled into this build agrees with the scalar
    /// hash, not just the one the dispatch picks. Both the round arithmetic and
    /// the transpose network are per-backend, so this is what keeps an untaken
    /// path honest.
    #[test]
    fn every_backend_matches_scalar() {
        fn check<S: Lanes32>(name: &str) {
            for n in [1usize, S::WIDTH - 1, S::WIDTH, S::WIDTH + 1, 3 * S::WIDTH + 2] {
                for len in [64usize, 128, 192, 1024] {
                    let data: Vec<u8> = (0..n * len).map(|i| ((i * 37 + 11) & 0xff) as u8).collect();
                    let mut got = vec![0u8; n * OUT_LEN];
                    // SAFETY: `data` holds `n * len` bytes and `got` `n * 32`.
                    unsafe { hash_many_with::<S>(&data, len, &mut got) };
                    for i in 0..n {
                        assert_eq!(
                            &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &hash(&data[i * len..(i + 1) * len])[..],
                            "{name}: input {i} of {n}, len {len}"
                        );
                    }
                }
            }
        }
        check::<Scalar8>("scalar");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        check::<x86::Avx2>("avx2");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx512bw"))]
        check::<x86::Avx512>("avx512");
        #[cfg(target_arch = "aarch64")]
        check::<arm::Neon>("neon");
    }

    /// The dispatched batch is byte-identical to the scalar hash per input,
    /// including a group that is not a multiple of `LANES`.
    #[test]
    fn batched_matches_scalar() {
        fn check<const LEN: usize>(n: usize) {
            let data: Vec<u8> = (0..n * LEN).map(|i| ((i * 31 + 7) & 0xff) as u8).collect();
            let mut got = vec![0u8; n * OUT_LEN];
            hash_many::<LEN>(&data, &mut got);
            for i in 0..n {
                assert_eq!(
                    &got[i * OUT_LEN..(i + 1) * OUT_LEN],
                    &hash(&data[i * LEN..(i + 1) * LEN])[..],
                    "LEN={LEN}, input {i} of {n}"
                );
            }
        }
        for n in [1usize, 7, 8, 9, 16, 21] {
            check::<64>(n);
            check::<128>(n);
            check::<192>(n);
            check::<1024>(n);
        }
    }
}
