//! SHA3-256 (FIPS 202) and the `Keccak-f[1600]` permutation under it.
//!
//! The one hash function. `sha3_256(msg)` is the standard sponge: absorb `msg`
//! in `RATE = 136` byte blocks into a 1600-bit state, pad the last block with
//! `pad10*1` and the `0x06` domain byte, permute, and read the first 32 bytes
//! of the state. Byte-exact FIPS 202, so it interoperates with any other
//! SHA3-256.
//!
//! **The permutation is the unit of proving.** The VM's `Keccak` opcode and
//! flock's R1CS both encode `Keccak-f[1600]` itself, not the sponge, because the
//! sponge around it is XORs into a state and a fixed pad. That split is what
//! keeps the circuit free of padding logic: a hash of KNOWN length pads with a
//! constant bit pattern, so `0x06` and the trailing `0x80` are constant wires,
//! and an `n`-byte hash of known length is exactly `ceil((n + 1) / RATE)`
//! permutations. Only a runtime-length message would need `pad10*1` enforced
//! in-circuit, and no call site has one.
//!
//! Keccak is cheap here for a different reason than a 32-bit ARX hash. Its
//! only nonlinear step is `chi`, one AND per bit, and the multiplicative
//! complexity of the five-bit `chi` is exactly five: the five outputs have
//! quadratic parts equal to five distinct degree-two monomials, and four
//! products of affine forms span at most four dimensions. So 1,600 AND rows a
//! round is a floor, and `theta`, `rho`, `pi` and `iota` are free over GF(2).
//!
//! Natively the same shape pays off on aarch64, where FEAT_SHA3 gives `BCAX`
//! (`chi` in one instruction), `EOR3`, `RAX1` and `XAR`. Those are vector
//! instructions, so they drive the BATCHED path ([`hash_many`], two states per
//! register), which is where the volume is: the PCS Merkle tree. A lone hash
//! runs the scalar permutation.
//!
//! Surfaces: [`permute`] (the opcode's relation), [`hash_block`] for the
//! 64-byte case (the Fiat-Shamir chain, the Merkle parent), [`hash`] /
//! [`Hasher`] for anything else, and [`hash_many`] for the PCS Merkle tree.

// ---------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------

/// Lanes in the `Keccak-f[1600]` state.
pub const STATE_LANES: usize = 25;
/// Rounds of `Keccak-f[1600]`.
pub const ROUNDS: usize = 24;
/// Rate in bytes: `(1600 - 512) / 8`, the SHA3-256 block.
pub const RATE: usize = 136;
/// Capacity in bytes, `512 / 8`.
pub const CAPACITY: usize = 200 - RATE;
/// Digest length in bytes.
pub const OUT_LEN: usize = 32;
/// The absorbed block, an alias for [`RATE`] that reads better at call sites
/// that think in blocks.
pub const BLOCK_LEN: usize = RATE;
/// FIPS 202's domain-separation byte for the SHA3-* family, `0b011` padded.
pub const DOMAIN: u8 = 0x06;

/// The 24 iota round constants.
pub const RC: [u64; ROUNDS] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// `rho` offsets, flat by `x + 5y`.
pub const RHO: [u32; STATE_LANES] = [
    0, 1, 62, 28, 27, //
    36, 44, 6, 55, 20, //
    3, 10, 43, 25, 39, //
    41, 45, 15, 21, 8, //
    18, 2, 61, 56, 14,
];

/// `pi`'s lane permutation: lane `PI[i]` of the input becomes lane `i` of the
/// output, i.e. `B[y + 5·((2x + 3y) mod 5)] = rot(A[x + 5y], RHO[x + 5y])`
/// read backwards so the walk is a gather.
pub const PI: [usize; STATE_LANES] = {
    let mut pi = [0usize; STATE_LANES];
    let mut y = 0;
    while y < 5 {
        let mut x = 0;
        while x < 5 {
            pi[y + 5 * ((2 * x + 3 * y) % 5)] = x + 5 * y;
            x += 1;
        }
        y += 1;
    }
    pi
};

// ---------------------------------------------------------------------------
// The permutation
// ---------------------------------------------------------------------------

/// `Keccak-f[1600]`, the relation the VM's opcode proves. Lane `i` of the state
/// is bytes `8i..8i+8` of the sponge, little-endian.
#[inline]
pub fn permute(state: &mut [u64; STATE_LANES]) {
    *state = permute_portable(*state);
}

/// [`permute`] as a `const fn`, so a state reachable at compile time (the
/// zero-prefix chain of [`zero_prefix_state`], say) costs nothing at run time.
pub const fn permute_portable(mut a: [u64; STATE_LANES]) -> [u64; STATE_LANES] {
    let mut round = 0;
    while round < ROUNDS {
        // theta
        let mut c = [0u64; 5];
        let mut x = 0;
        while x < 5 {
            c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            x += 1;
        }
        let mut d = [0u64; 5];
        x = 0;
        while x < 5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            x += 1;
        }
        let mut i = 0;
        while i < STATE_LANES {
            a[i] ^= d[i % 5];
            i += 1;
        }

        // rho and pi, gathered so the two are one pass
        let mut b = [0u64; STATE_LANES];
        i = 0;
        while i < STATE_LANES {
            let src = PI[i];
            b[i] = a[src].rotate_left(RHO[src]);
            i += 1;
        }

        // chi
        let mut y = 0;
        while y < 5 {
            x = 0;
            while x < 5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
                x += 1;
            }
            y += 1;
        }

        // iota
        a[0] ^= RC[round];
        round += 1;
    }
    a
}

// ---------------------------------------------------------------------------
// The sponge
// ---------------------------------------------------------------------------

/// XOR `block` into the rate and permute. `block` must be at most [`RATE`].
#[inline]
fn absorb_block(state: &mut [u64; STATE_LANES], block: &[u8]) {
    debug_assert!(block.len() <= RATE);
    xor_into_rate(state, block, 0);
    permute(state);
}

/// XOR `bytes` into the rate starting at byte `offset`.
#[inline]
fn xor_into_rate(state: &mut [u64; STATE_LANES], bytes: &[u8], offset: usize) {
    debug_assert!(offset + bytes.len() <= RATE);
    for (i, &b) in bytes.iter().enumerate() {
        let pos = offset + i;
        state[pos / 8] ^= (b as u64) << (8 * (pos % 8));
    }
}

/// The final block: `tail`, then `pad10*1` around the `0x06` domain byte.
/// `tail` is what is left of the message after the whole blocks, so shorter
/// than [`RATE`].
#[inline]
fn absorb_final(state: &mut [u64; STATE_LANES], tail: &[u8]) {
    debug_assert!(tail.len() < RATE);
    xor_into_rate(state, tail, 0);
    // The two pad bits can land in the same byte when the tail is RATE-1 long,
    // which is why both are XORed rather than written.
    state[tail.len() / 8] ^= (DOMAIN as u64) << (8 * (tail.len() % 8));
    state[(RATE - 1) / 8] ^= 0x80u64 << (8 * ((RATE - 1) % 8));
    permute(state);
}

/// The first [`OUT_LEN`] bytes of the state, which is the whole squeeze for
/// SHA3-256 (`OUT_LEN < RATE`, so it never permutes again).
#[inline]
const fn squeeze(state: &[u64; STATE_LANES]) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    let mut i = 0;
    while i < OUT_LEN {
        out[i] = (state[i / 8] >> (8 * (i % 8))) as u8;
        i += 1;
    }
    out
}

/// SHA3-256 of `data`.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    let mut state = [0u64; STATE_LANES];
    let mut rest = data;
    while rest.len() >= RATE {
        absorb_block(&mut state, &rest[..RATE]);
        rest = &rest[RATE..];
    }
    absorb_final(&mut state, rest);
    squeeze(&state)
}

/// SHA3-256 of exactly 64 bytes: the Fiat-Shamir chain step and the Merkle
/// parent, and the case the VM proves. 64 is under [`RATE`], so this is one
/// permutation and the pad is a constant.
#[inline]
pub fn hash_block(block: &[u8; 64]) -> [u8; OUT_LEN] {
    let mut state = [0u64; STATE_LANES];
    absorb_final(&mut state, block);
    squeeze(&state)
}

/// Merkle-Damgard chain over [`hash_block`], for the messages the VM cannot
/// hash in one bite.
///
/// `msg` is zero-filled to a whole number of 32-byte groups, at least two,
/// because a VM cell is 128 bits and the opcode hashes 64 bytes. The caller
/// binds the length: every call site here has a fixed one, and XMSS's tweak
/// carries it explicitly. Then:
///
/// ```text
///   st = sha3_256(msg[0..64])
///   st = sha3_256(st ‖ group)   for each 32-byte group after the first two
/// ```
///
/// **This is not SHA3-256 of `msg`.** It is a chain of them, and it exists
/// because the VM's `Keccak` opcode hashes exactly 64 bytes: a guest can chain
/// that, but it cannot absorb a 136-byte rate block, whose seventeen lanes do
/// not divide into 128-bit memory cells. Every call site has a fixed length and
/// a distinct domain tag in its first group, so the encoding stays prefix-free
/// and the chain is as sound as the compression it iterates. Anything that fits
/// 64 bytes uses [`hash_block`] and IS plain SHA3-256.
pub fn hash_md(msg: &[u8]) -> [u8; OUT_LEN] {
    let padded = msg.len().next_multiple_of(32).max(64);
    if padded == msg.len() {
        return hash_md_from_state(&msg[64..], &hash_block(msg[..64].try_into().unwrap()));
    }
    let mut buf = vec![0u8; padded];
    buf[..msg.len()].copy_from_slice(msg);
    hash_md_from_state(&buf[64..], &hash_block(buf[..64].try_into().unwrap()))
}

/// Continue a [`hash_md`] chain over the 32-byte groups of `rest`.
pub fn hash_md_from_state(rest: &[u8], state: &[u8; OUT_LEN]) -> [u8; OUT_LEN] {
    debug_assert!(rest.len().is_multiple_of(32));
    let mut st = *state;
    for group in rest.chunks_exact(32) {
        let mut block = [0u8; 64];
        block[..32].copy_from_slice(&st);
        block[32..].copy_from_slice(group);
        st = hash_block(&block);
    }
    st
}

/// The [`hash_md`] state after `n_zero_groups` leading 32-byte groups of zeros,
/// which is at least two (the chain's first link is 64 bytes). A leading run of
/// zeros is the same for every leaf, so the PCS committer pays this once rather
/// than per leaf.
pub fn md_zero_prefix_state(n_zero_groups: usize) -> [u8; OUT_LEN] {
    assert!(n_zero_groups >= 2, "the chain's first link is two groups");
    let mut st = hash_block(&[0u8; 64]);
    for _ in 2..n_zero_groups {
        let mut block = [0u8; 64];
        block[..32].copy_from_slice(&st);
        st = hash_block(&block);
    }
    st
}

/// [`hash_md`] of each `len`-byte record of `data`, digests written in order.
pub fn hash_many_md(data: &[u8], len: usize, out: &mut [u8]) {
    let n = data.len().checked_div(len).unwrap_or(0);
    assert!(out.len() >= n * OUT_LEN, "digest buffer too small");
    for i in 0..n {
        let d = hash_md(&data[i * len..(i + 1) * len]);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
    }
}

/// [`hash_md`] of each `len`-byte record of `data`, resuming from a shared
/// prefix state, digests written in order. `len` counts only what follows the
/// prefix and must be a whole number of 32-byte groups. The chains are
/// independent, one per record, so a pair of them shares every permutation on
/// the batched backend.
pub fn hash_many_md_from_state(data: &[u8], len: usize, state: &[u8; OUT_LEN], out: &mut [u8]) {
    let n = data.len().checked_div(len).unwrap_or(0);
    assert!(out.len() >= n * OUT_LEN, "digest buffer too small");
    assert!(len.is_multiple_of(32), "a record is whole 32-byte groups");
    let mut i = 0;
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    while i + 2 <= n {
        let (mut s0, mut s1) = (*state, *state);
        let zero = [0u64; STATE_LANES];
        for g in 0..len / 32 {
            let link = |st: &[u8; OUT_LEN], rec: usize| -> [u8; 64] {
                let mut b = [0u8; 64];
                b[..32].copy_from_slice(st);
                b[32..].copy_from_slice(&data[(i + rec) * len + g * 32..][..32]);
                b
            };
            let (b0, b1) = (link(&s0, 0), link(&s1, 1));
            (s0, s1) = aarch64_sha3::hash_pair_from_state(&b0, &b1, &zero);
        }
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&s0);
        out[(i + 1) * OUT_LEN..(i + 2) * OUT_LEN].copy_from_slice(&s1);
        i += 2;
    }
    while i < n {
        let d = hash_md_from_state(&data[i * len..(i + 1) * len], state);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
        i += 1;
    }
}

/// Incremental SHA3-256, for the callers that build a message from pieces.
#[derive(Clone)]
pub struct Hasher {
    state: [u64; STATE_LANES],
    /// Bytes of the current block already absorbed, always `< RATE`.
    filled: usize,
}

impl Hasher {
    pub fn new() -> Self {
        Self {
            state: [0u64; STATE_LANES],
            filled: 0,
        }
    }

    /// Resume from a state reached by absorbing some whole blocks already, e.g.
    /// [`zero_prefix_state`].
    pub fn from_state(state: [u64; STATE_LANES]) -> Self {
        Self { state, filled: 0 }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        if self.filled > 0 {
            let take = data.len().min(RATE - self.filled);
            xor_into_rate(&mut self.state, &data[..take], self.filled);
            self.filled += take;
            data = &data[take..];
            if self.filled == RATE {
                permute(&mut self.state);
                self.filled = 0;
            }
        }
        while data.len() >= RATE {
            absorb_block(&mut self.state, &data[..RATE]);
            data = &data[RATE..];
        }
        if !data.is_empty() {
            xor_into_rate(&mut self.state, data, self.filled);
            self.filled += data.len();
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut state = self.state;
        // The tail is already XORed in, so only the pad is left.
        state[self.filled / 8] ^= (DOMAIN as u64) << (8 * (self.filled % 8));
        state[(RATE - 1) / 8] ^= 0x80u64 << (8 * ((RATE - 1) % 8));
        permute(&mut state);
        squeeze(&state)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// The state after absorbing `n_blocks` all-zero rate blocks from the initial
/// state. A zero block XORs nothing, so this is `f^n(0)`, a constant: the PCS
/// leaf hasher pays it once instead of per leaf.
pub fn zero_prefix_state(n_blocks: usize) -> [u64; STATE_LANES] {
    let mut state = [0u64; STATE_LANES];
    for _ in 0..n_blocks {
        permute(&mut state);
    }
    state
}

/// SHA3-256 of `data` appended to a message whose whole blocks are already
/// absorbed into `state` (see [`zero_prefix_state`]).
pub fn hash_from_state(data: &[u8], state: &[u64; STATE_LANES]) -> [u8; OUT_LEN] {
    let mut h = Hasher::from_state(*state);
    h.update(data);
    h.finalize()
}

// ---------------------------------------------------------------------------
// Batched hashing (the PCS Merkle tree)
// ---------------------------------------------------------------------------

/// States hashed in one batch. On aarch64 the FEAT_SHA3 instructions are
/// 128-bit, so two states share every register; elsewhere the portable
/// permutation runs one at a time and batching only amortizes the loop.
pub const LANES: usize = if cfg!(all(target_arch = "aarch64", target_feature = "sha3")) {
    2
} else {
    1
};

/// SHA3-256 of each `LEN`-byte record of `data`, digests written in order.
/// `LEN` is a constant because every caller knows its record size, which keeps
/// the block split out of the inner loop.
pub fn hash_many<const LEN: usize>(data: &[u8], out: &mut [u8]) {
    hash_many_dyn(data, LEN, out);
}

/// [`hash_many`] with a runtime record length.
pub fn hash_many_dyn(data: &[u8], len: usize, out: &mut [u8]) {
    let zero = [0u64; STATE_LANES];
    hash_many_dyn_from_state(data, len, &zero, out);
}

/// [`hash_many_dyn`] resuming from a shared prefix state, which is what makes
/// a leaf's leading zero blocks free (see [`zero_prefix_state`]).
pub fn hash_many_dyn_from_state(data: &[u8], len: usize, state: &[u64; STATE_LANES], out: &mut [u8]) {
    let n = data.len().checked_div(len).unwrap_or(0);
    assert!(out.len() >= n * OUT_LEN, "digest buffer too small");
    let mut i = 0;
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    while i + 2 <= n {
        let (d0, d1) = aarch64_sha3::hash_pair_from_state(
            &data[i * len..(i + 1) * len],
            &data[(i + 1) * len..(i + 2) * len],
            state,
        );
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d0);
        out[(i + 1) * OUT_LEN..(i + 2) * OUT_LEN].copy_from_slice(&d1);
        i += 2;
    }
    while i < n {
        let d = hash_from_state(&data[i * len..(i + 1) * len], state);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
        i += 1;
    }
}

/// Two independent sponges per NEON register, driven by FEAT_SHA3's `EOR3`,
/// `RAX1`, `XAR` and `BCAX`. `BCAX(a, b, c) = a ^ (b & ~c)` is exactly `chi`,
/// so the nonlinear layer is one instruction per lane pair.
#[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
mod aarch64_sha3 {
    use super::{DOMAIN, OUT_LEN, PI, RATE, RC, RHO, ROUNDS, STATE_LANES};
    use core::arch::aarch64::*;

    /// `vxarq_u64` needs its rotation as a const generic, so `rho` is unrolled
    /// through this dispatch rather than indexed.
    macro_rules! xar_dispatch {
        ($v:expr, $r:expr, $($n:literal),*) => {
            match $r {
                $($n => vxarq_u64::<$n>($v, vdupq_n_u64(0)),)*
                _ => unreachable!(),
            }
        };
    }

    #[inline]
    #[target_feature(enable = "sha3")]
    unsafe fn rotl(v: uint64x2_t, r: u32) -> uint64x2_t {
        if r == 0 {
            return v;
        }
        // XAR rotates right by its immediate, so a left rotation by `r` is a
        // right rotation by `64 - r`.
        xar_dispatch!(
            v,
            64 - r,
            1,
            2,
            3,
            4,
            5,
            6,
            7,
            8,
            9,
            10,
            11,
            12,
            13,
            14,
            15,
            16,
            17,
            18,
            19,
            20,
            21,
            22,
            23,
            24,
            25,
            26,
            27,
            28,
            29,
            30,
            31,
            32,
            33,
            34,
            35,
            36,
            37,
            38,
            39,
            40,
            41,
            42,
            43,
            44,
            45,
            46,
            47,
            48,
            49,
            50,
            51,
            52,
            53,
            54,
            55,
            56,
            57,
            58,
            59,
            60,
            61,
            62,
            63
        )
    }

    #[target_feature(enable = "sha3")]
    unsafe fn permute_x2(a: &mut [uint64x2_t; STATE_LANES]) {
        for &rc in RC.iter().take(ROUNDS) {
            let mut c = [vdupq_n_u64(0); 5];
            for (x, c) in c.iter_mut().enumerate() {
                *c = veor3q_u64(veor3q_u64(a[x], a[x + 5], a[x + 10]), a[x + 15], a[x + 20]);
            }
            let mut d = [vdupq_n_u64(0); 5];
            for (x, d) in d.iter_mut().enumerate() {
                *d = vrax1q_u64(c[(x + 4) % 5], c[(x + 1) % 5]);
            }
            for (i, a) in a.iter_mut().enumerate() {
                *a = veorq_u64(*a, d[i % 5]);
            }

            let mut b = [vdupq_n_u64(0); STATE_LANES];
            for (i, b) in b.iter_mut().enumerate() {
                let src = PI[i];
                *b = unsafe { rotl(a[src], RHO[src]) };
            }

            for y in 0..5 {
                for x in 0..5 {
                    a[x + 5 * y] = vbcaxq_u64(b[x + 5 * y], b[(x + 2) % 5 + 5 * y], b[(x + 1) % 5 + 5 * y]);
                }
            }

            a[0] = veorq_u64(a[0], vdupq_n_u64(rc));
        }
    }

    /// SHA3-256 of two equal-length messages, resuming from a shared state.
    pub fn hash_pair_from_state(m0: &[u8], m1: &[u8], state: &[u64; STATE_LANES]) -> ([u8; OUT_LEN], [u8; OUT_LEN]) {
        debug_assert_eq!(m0.len(), m1.len());
        // SAFETY: the module is compiled only when `sha3` is a target feature.
        unsafe {
            let mut a: [uint64x2_t; STATE_LANES] = std::array::from_fn(|i| vdupq_n_u64(state[i]));
            let (mut r0, mut r1) = (m0, m1);
            while r0.len() >= RATE {
                xor_pair(&mut a, &r0[..RATE], &r1[..RATE]);
                permute_x2(&mut a);
                r0 = &r0[RATE..];
                r1 = &r1[RATE..];
            }
            xor_pair(&mut a, r0, r1);
            let tail = r0.len();
            pad_pair(&mut a, tail);
            permute_x2(&mut a);
            let mut d0 = [0u8; OUT_LEN];
            let mut d1 = [0u8; OUT_LEN];
            for i in 0..OUT_LEN {
                let lane = a[i / 8];
                d0[i] = (vgetq_lane_u64::<0>(lane) >> (8 * (i % 8))) as u8;
                d1[i] = (vgetq_lane_u64::<1>(lane) >> (8 * (i % 8))) as u8;
            }
            (d0, d1)
        }
    }

    #[inline]
    unsafe fn xor_pair(a: &mut [uint64x2_t; STATE_LANES], b0: &[u8], b1: &[u8]) {
        for i in 0..b0.len() {
            let (l, sh) = (i / 8, 8 * (i % 8));
            let v = unsafe { vcombine_u64(vcreate_u64((b0[i] as u64) << sh), vcreate_u64((b1[i] as u64) << sh)) };
            a[l] = unsafe { veorq_u64(a[l], v) };
        }
    }

    #[inline]
    unsafe fn pad_pair(a: &mut [uint64x2_t; STATE_LANES], tail: usize) {
        unsafe {
            let d = vdupq_n_u64((DOMAIN as u64) << (8 * (tail % 8)));
            a[tail / 8] = veorq_u64(a[tail / 8], d);
            let e = vdupq_n_u64(0x80u64 << (8 * ((RATE - 1) % 8)));
            a[(RATE - 1) / 8] = veorq_u64(a[(RATE - 1) / 8], e);
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// FIPS 202 / NIST CAVP SHA3-256 known answers. Pins the round constants,
    /// the rho offsets, the pi permutation and the pad, all at once: one wrong
    /// entry in any of them changes every digest.
    #[test]
    fn matches_sha3_256_vectors() {
        assert_eq!(
            hex(&hash(b"")),
            "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
        );
        assert_eq!(
            hex(&hash(b"abc")),
            "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
        );
        assert_eq!(
            hex(&hash(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
            "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376"
        );
        // Exactly one rate block, so the pad takes a whole extra block, and one
        // byte short of it, where the two pad bits share a byte.
        assert_eq!(
            hex(&hash(&[0xa3u8; RATE])),
            "0adf6bfb359ae40019b67d8c49c361574b70242a6b752de6f9e0d426ca177f7a"
        );
        assert_eq!(
            hex(&hash(&[0xa3u8; RATE - 1])),
            "d51927265ca4bf0cc8b4453387700918c03f8894e395ad437d4573f3be4d2c34"
        );
    }

    #[test]
    fn hash_block_matches_hash() {
        let block: [u8; 64] = std::array::from_fn(|i| i as u8);
        assert_eq!(hash_block(&block), hash(&block));
    }

    /// The incremental path must agree with the one-shot on every split,
    /// including splits that land inside a block and exactly on its boundary.
    #[test]
    fn hasher_matches_hash_at_every_split() {
        let msg: Vec<u8> = (0..3 * RATE + 7).map(|i| (i * 31) as u8).collect();
        let want = hash(&msg);
        for split in [0, 1, 7, 63, RATE - 1, RATE, RATE + 1, 2 * RATE, msg.len()] {
            let mut h = Hasher::new();
            h.update(&msg[..split]);
            h.update(&msg[split..]);
            assert_eq!(h.finalize(), want, "split at {split}");
        }
        // Byte at a time, which exercises the partial-block path exclusively.
        let mut h = Hasher::new();
        for b in &msg {
            h.update(std::slice::from_ref(b));
        }
        assert_eq!(h.finalize(), want);
    }

    /// A zero prefix of whole blocks is a constant state, which is the whole
    /// point of `zero_prefix_state` for the PCS leaf hasher.
    #[test]
    fn zero_prefix_state_is_the_absorbed_prefix() {
        for n_blocks in [0usize, 1, 3] {
            let state = zero_prefix_state(n_blocks);
            let tail: Vec<u8> = (0..70u8).collect();
            let mut full = vec![0u8; n_blocks * RATE];
            full.extend_from_slice(&tail);
            assert_eq!(hash_from_state(&tail, &state), hash(&full), "{n_blocks} zero blocks");
        }
    }

    /// The batched path is a different permutation implementation on aarch64,
    /// so it has to agree with the scalar one on every record length that
    /// straddles a block boundary.
    #[test]
    fn hash_many_matches_hash() {
        for len in [1usize, 32, 64, RATE - 1, RATE, RATE + 1, 2 * RATE + 5] {
            let n = 5;
            let data: Vec<u8> = (0..n * len).map(|i| (i * 17 + 3) as u8).collect();
            let mut out = vec![0u8; n * OUT_LEN];
            hash_many_dyn(&data, len, &mut out);
            for i in 0..n {
                let want = hash(&data[i * len..(i + 1) * len]);
                assert_eq!(&out[i * OUT_LEN..(i + 1) * OUT_LEN], &want[..], "len {len}, record {i}");
            }
        }
    }

    /// The chain agrees with itself however the message is grouped, and its
    /// first link is plain SHA3-256 of the 64 bytes.
    #[test]
    fn hash_md_is_a_chain_of_64_byte_hashes() {
        let msg: Vec<u8> = (0..160u8).collect();
        assert_eq!(hash_md(&msg[..64]), hash_block(msg[..64].try_into().unwrap()));
        let mut st = hash_block(msg[..64].try_into().unwrap());
        for group in msg[64..].chunks_exact(32) {
            let mut block = [0u8; 64];
            block[..32].copy_from_slice(&st);
            block[32..].copy_from_slice(group);
            st = hash_block(&block);
        }
        assert_eq!(hash_md(&msg), st);
        // A chain is not the sponge over the same bytes: they must not collide.
        assert_ne!(hash_md(&msg), hash(&msg));
    }

    /// The shared zero prefix and the batched chain must both agree with the
    /// plain one, at every record length the PCS may ask for.
    #[test]
    fn md_prefix_and_batching_agree_with_the_plain_chain() {
        for zero_groups in [2usize, 3, 6] {
            for groups in [1usize, 2, 5] {
                let len = 32 * groups;
                let n = 5;
                let data: Vec<u8> = (0..n * len).map(|i| (i * 29 + 11) as u8).collect();
                let state = md_zero_prefix_state(zero_groups);
                let mut out = vec![0u8; n * OUT_LEN];
                hash_many_md_from_state(&data, len, &state, &mut out);
                for i in 0..n {
                    let mut full = vec![0u8; 32 * zero_groups];
                    full.extend_from_slice(&data[i * len..(i + 1) * len]);
                    assert_eq!(
                        &out[i * OUT_LEN..(i + 1) * OUT_LEN],
                        &hash_md(&full)[..],
                        "zero_groups {zero_groups}, groups {groups}, record {i}"
                    );
                }
            }
        }
    }

    #[test]
    fn permute_is_const_evaluable() {
        const P: [u64; STATE_LANES] = permute_portable([0u64; STATE_LANES]);
        let mut s = [0u64; STATE_LANES];
        permute(&mut s);
        assert_eq!(P, s);
    }

    /// `pi` is a permutation of the 25 lanes, which the gather form relies on.
    #[test]
    fn pi_is_a_permutation() {
        let mut seen = [false; STATE_LANES];
        for &src in &PI {
            assert!(!seen[src], "lane {src} gathered twice");
            seen[src] = true;
        }
        assert!(seen.iter().all(|s| *s));
    }
}
