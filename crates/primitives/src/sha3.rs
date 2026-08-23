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
//! (`chi` in one instruction), `EOR3`, `RAX1` and `XAR` (`theta`'s per-lane XOR
//! fused into `rho`'s rotation). Those are 128-bit instructions, so the state of
//! TWO sponges fits one set of registers and the batched paths
//! ([`hash_many_md`], [`hash_many`]) get two hashes for the price of one, which
//! is where the volume is: the PCS Merkle tree. A lone hash runs the same code
//! with its state in both halves, wasting the width but keeping the fused
//! instructions, which still beats the portable permutation.
//!
//! Surfaces: [`permute`] (the opcode's relation), [`hash_block`] for the
//! 64-byte case (the Fiat-Shamir chain, the Merkle parent), [`hash_md`] and
//! [`hash_many_md`] for the chain below, [`hash`] / [`Hasher`] for anything
//! else, and [`hash_many`] for a batch of plain sponges.

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
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    aarch64_sha3::permute(state);
    #[cfg(not(all(target_arch = "aarch64", target_feature = "sha3")))]
    {
        *state = permute_portable(*state);
    }
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

/// XOR `bytes` into the rate starting at byte `offset`, a whole lane at a time
/// once the offset is lane-aligned. A byte at a time costs more than the
/// permutation it feeds on a long message.
#[inline]
fn xor_into_rate(state: &mut [u64; STATE_LANES], bytes: &[u8], offset: usize) {
    debug_assert!(offset + bytes.len() <= RATE);
    let mut pos = offset;
    let mut rest = bytes;
    let head = (8 - pos % 8) % 8;
    let (head, tail) = rest.split_at(head.min(rest.len()));
    for (i, &b) in head.iter().enumerate() {
        state[pos / 8] ^= (b as u64) << (8 * ((pos + i) % 8));
    }
    pos += head.len();
    rest = tail;
    while let Some((lane, tail)) = rest.split_first_chunk::<8>() {
        state[pos / 8] ^= u64::from_le_bytes(*lane);
        pos += 8;
        rest = tail;
    }
    for (i, &b) in rest.iter().enumerate() {
        state[pos / 8] ^= (b as u64) << (8 * i);
    }
}

/// `pad10*1` around the `0x06` domain byte, for a message whose `tail` bytes are
/// already XORed into the rate. The two pad bits can land in the same byte when
/// the tail is `RATE - 1` long, which is why both are XORed rather than written.
#[inline]
fn pad_final(state: &mut [u64; STATE_LANES], tail: usize) {
    debug_assert!(tail < RATE);
    state[tail / 8] ^= (DOMAIN as u64) << (8 * (tail % 8));
    state[(RATE - 1) / 8] ^= 0x80u64 << (8 * ((RATE - 1) % 8));
}

/// The final block: `tail`, then the pad, then the permutation. `tail` is what
/// is left of the message after the whole blocks, so shorter than [`RATE`].
#[inline]
fn absorb_final(state: &mut [u64; STATE_LANES], tail: &[u8]) {
    xor_into_rate(state, tail, 0);
    pad_final(state, tail.len());
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
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    return aarch64_sha3::hash_block(block);
    #[cfg(not(all(target_arch = "aarch64", target_feature = "sha3")))]
    {
        let mut state = [0u64; STATE_LANES];
        absorb_final(&mut state, block);
        squeeze(&state)
    }
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
    md_zero_filled(msg, hash_md_padded)
}

/// [`hash_md`]'s zero-fill to whole 32-byte groups, at least two, then `chain`.
/// Every call site is already padded, so the copy is the cold path.
fn md_zero_filled(msg: &[u8], chain: impl Fn(&[u8]) -> [u8; OUT_LEN]) -> [u8; OUT_LEN] {
    let padded = msg.len().next_multiple_of(32).max(64);
    if padded == msg.len() {
        return chain(msg);
    }
    let mut buf = vec![0u8; padded];
    buf[..msg.len()].copy_from_slice(msg);
    chain(&buf)
}

/// [`hash_md`] of a record that already is whole 32-byte groups, at least two.
fn hash_md_padded(msg: &[u8]) -> [u8; OUT_LEN] {
    debug_assert!(msg.len() >= 64 && msg.len().is_multiple_of(32));
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    return aarch64_sha3::hash_md_one(msg, None);
    #[cfg(not(all(target_arch = "aarch64", target_feature = "sha3")))]
    hash_md_portable(msg)
}

/// One 64-byte compression through [`permute_portable`]. 64 is under [`RATE`],
/// so this is a whole SHA3-256 and one link of the [`hash_md`] chain.
fn compress64_portable(block: &[u8; 64]) -> [u8; OUT_LEN] {
    let mut state = [0u64; STATE_LANES];
    xor_into_rate(&mut state, block, 0);
    pad_final(&mut state, block.len());
    squeeze(&permute_portable(state))
}

/// [`hash_md_padded`] through [`permute_portable`], one state at a time: what a
/// host with no Keccak extension runs, whichever host this is.
fn hash_md_portable(msg: &[u8]) -> [u8; OUT_LEN] {
    debug_assert!(msg.len() >= 64 && msg.len().is_multiple_of(32));
    let mut block = [0u8; 64];
    block.copy_from_slice(&msg[..64]);
    let mut st = compress64_portable(&block);
    for group in msg[64..].chunks_exact(32) {
        block[..32].copy_from_slice(&st);
        block[32..].copy_from_slice(group);
        st = compress64_portable(&block);
    }
    st
}

/// Continue a [`hash_md`] chain over the 32-byte groups of `rest`.
pub fn hash_md_from_state(rest: &[u8], state: &[u8; OUT_LEN]) -> [u8; OUT_LEN] {
    debug_assert!(rest.len().is_multiple_of(32));
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    return aarch64_sha3::hash_md_one(rest, Some(state));
    #[cfg(not(all(target_arch = "aarch64", target_feature = "sha3")))]
    {
        let mut st = *state;
        let mut block = [0u8; 64];
        for group in rest.chunks_exact(32) {
            block[..32].copy_from_slice(&st);
            block[32..].copy_from_slice(group);
            st = compress64_portable(&block);
        }
        st
    }
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
/// The chains are independent, so a pair of them shares every permutation on
/// the batched backend; a record that needs zero-filling does not, and takes
/// the one-at-a-time path.
pub fn hash_many_md(data: &[u8], len: usize, out: &mut [u8]) {
    let n = data.len().checked_div(len).unwrap_or(0);
    assert!(out.len() >= n * OUT_LEN, "digest buffer too small");
    let mut i = 0;
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    if len >= 64 && len.is_multiple_of(32) {
        i = aarch64_sha3::hash_many_md_pairs(data, len, None, out);
    }
    while i < n {
        let d = hash_md(&data[i * len..(i + 1) * len]);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
        i += 1;
    }
}

/// [`hash_many_md`] through [`permute_portable`], which is what a host with no
/// Keccak extension runs. Production always takes the backend's permutation;
/// this exists so the benchmark can measure the gap on a host that has one.
pub fn hash_many_md_portable(data: &[u8], len: usize, out: &mut [u8]) {
    let n = data.len().checked_div(len).unwrap_or(0);
    assert!(out.len() >= n * OUT_LEN, "digest buffer too small");
    for i in 0..n {
        let d = md_zero_filled(&data[i * len..(i + 1) * len], hash_md_portable);
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
    #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
    let mut i = aarch64_sha3::hash_many_md_pairs(data, len, Some(state), out);
    #[cfg(not(all(target_arch = "aarch64", target_feature = "sha3")))]
    let mut i = 0;
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
        pad_final(&mut state, self.filled);
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
/// so the nonlinear layer is one instruction per lane pair, and
/// `XAR(a, b, n) = rotr(a ^ b, n)` fuses `theta`'s per-lane XOR into `rho`'s
/// rotation, so neither costs an instruction of its own. A round is then 10
/// `EOR3`, 5 `RAX1`, 25 `XAR`, 25 `BCAX` and the `iota` `EOR`, for two states.
///
/// Twenty-five lanes of two states is twenty-five of the thirty-two vector
/// registers, so the state stays resident across all 24 rounds. That is what
/// fixes the width at two: a wider batch spills, and the round is written out
/// rather than looped over the lanes because `XAR` takes its rotation as an
/// immediate. A lone hash runs the same code with its state in both halves,
/// which the fused instructions still pay for.
#[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
mod aarch64_sha3 {
    use super::{DOMAIN, OUT_LEN, RATE, RC, STATE_LANES};
    use core::arch::aarch64::*;

    /// A pair of 32-byte digests, interleaved: lane 0 of each word is the first
    /// state's, lane 1 the second's.
    type Pair = [uint64x2_t; 4];

    #[inline(always)]
    unsafe fn eor3(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
        unsafe { veor3q_u64(a, b, c) }
    }

    /// `a ^ rotl(b, 1)`, which is `theta`'s `d` word.
    #[inline(always)]
    unsafe fn rax1(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        unsafe { vrax1q_u64(a, b) }
    }

    /// `rotr(a ^ b, N)`.
    #[inline(always)]
    unsafe fn xar<const N: i32>(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        unsafe { vxarq_u64::<N>(a, b) }
    }

    /// `a ^ (b & !c)`, which is `chi`.
    #[inline(always)]
    unsafe fn bcax(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
        unsafe { vbcaxq_u64(a, b, c) }
    }

    #[inline]
    unsafe fn permute_x2(mut a: [uint64x2_t; STATE_LANES]) -> [uint64x2_t; STATE_LANES] {
        unsafe {
            for &rc in RC.iter() {
                let c0 = eor3(eor3(a[0], a[5], a[10]), a[15], a[20]);
                let c1 = eor3(eor3(a[1], a[6], a[11]), a[16], a[21]);
                let c2 = eor3(eor3(a[2], a[7], a[12]), a[17], a[22]);
                let c3 = eor3(eor3(a[3], a[8], a[13]), a[18], a[23]);
                let c4 = eor3(eor3(a[4], a[9], a[14]), a[19], a[24]);
                let d0 = rax1(c4, c1);
                let d1 = rax1(c0, c2);
                let d2 = rax1(c1, c3);
                let d3 = rax1(c2, c4);
                let d4 = rax1(c3, c0);

                let b00 = xar::<0>(a[0], d0);
                let b01 = xar::<20>(a[6], d1);
                let b02 = xar::<21>(a[12], d2);
                let b03 = xar::<43>(a[18], d3);
                let b04 = xar::<50>(a[24], d4);
                let b05 = xar::<36>(a[3], d3);
                let b06 = xar::<44>(a[9], d4);
                let b07 = xar::<61>(a[10], d0);
                let b08 = xar::<19>(a[16], d1);
                let b09 = xar::<3>(a[22], d2);
                let b10 = xar::<63>(a[1], d1);
                let b11 = xar::<58>(a[7], d2);
                let b12 = xar::<39>(a[13], d3);
                let b13 = xar::<56>(a[19], d4);
                let b14 = xar::<46>(a[20], d0);
                let b15 = xar::<37>(a[4], d4);
                let b16 = xar::<28>(a[5], d0);
                let b17 = xar::<54>(a[11], d1);
                let b18 = xar::<49>(a[17], d2);
                let b19 = xar::<8>(a[23], d3);
                let b20 = xar::<2>(a[2], d2);
                let b21 = xar::<9>(a[8], d3);
                let b22 = xar::<25>(a[14], d4);
                let b23 = xar::<23>(a[15], d0);
                let b24 = xar::<62>(a[21], d1);

                a[0] = bcax(b00, b02, b01);
                a[1] = bcax(b01, b03, b02);
                a[2] = bcax(b02, b04, b03);
                a[3] = bcax(b03, b00, b04);
                a[4] = bcax(b04, b01, b00);
                a[5] = bcax(b05, b07, b06);
                a[6] = bcax(b06, b08, b07);
                a[7] = bcax(b07, b09, b08);
                a[8] = bcax(b08, b05, b09);
                a[9] = bcax(b09, b06, b05);
                a[10] = bcax(b10, b12, b11);
                a[11] = bcax(b11, b13, b12);
                a[12] = bcax(b12, b14, b13);
                a[13] = bcax(b13, b10, b14);
                a[14] = bcax(b14, b11, b10);
                a[15] = bcax(b15, b17, b16);
                a[16] = bcax(b16, b18, b17);
                a[17] = bcax(b17, b19, b18);
                a[18] = bcax(b18, b15, b19);
                a[19] = bcax(b19, b16, b15);
                a[20] = bcax(b20, b22, b21);
                a[21] = bcax(b21, b23, b22);
                a[22] = bcax(b22, b24, b23);
                a[23] = bcax(b23, b20, b24);
                a[24] = bcax(b24, b21, b20);

                a[0] = veorq_u64(a[0], vdupq_n_u64(rc));
            }
            a
        }
    }

    /// Absorb eight lanes and the constant 64-byte pad, then permute: one link
    /// of the [`super::hash_md`] chain, and the whole of a 64-byte SHA3-256.
    /// The pad is constant because the length is: `0x06` at byte 64 and the
    /// final `0x80` at byte `RATE - 1`.
    #[inline]
    unsafe fn link(l: [uint64x2_t; 8]) -> Pair {
        unsafe {
            let mut a = [vdupq_n_u64(0); STATE_LANES];
            a[0] = l[0];
            a[1] = l[1];
            a[2] = l[2];
            a[3] = l[3];
            a[4] = l[4];
            a[5] = l[5];
            a[6] = l[6];
            a[7] = l[7];
            a[8] = vdupq_n_u64(DOMAIN as u64);
            a[16] = vdupq_n_u64(0x80u64 << 56);
            let a = permute_x2(a);
            [a[0], a[1], a[2], a[3]]
        }
    }

    /// The four interleaved lanes of 32 bytes read from each pointer. Pass the
    /// same pointer twice to run one chain in both halves.
    #[inline(always)]
    unsafe fn load32(p0: *const u8, p1: *const u8) -> Pair {
        unsafe {
            let x0 = vreinterpretq_u64_u8(vld1q_u8(p0));
            let x1 = vreinterpretq_u64_u8(vld1q_u8(p0.add(16)));
            let y0 = vreinterpretq_u64_u8(vld1q_u8(p1));
            let y1 = vreinterpretq_u64_u8(vld1q_u8(p1.add(16)));
            [
                vzip1q_u64(x0, y0),
                vzip2q_u64(x0, y0),
                vzip1q_u64(x1, y1),
                vzip2q_u64(x1, y1),
            ]
        }
    }

    /// De-interleave a digest pair into 32 bytes at each pointer.
    #[inline(always)]
    unsafe fn store32(v: Pair, o0: *mut u8, o1: *mut u8) {
        unsafe {
            vst1q_u8(o0, vreinterpretq_u8_u64(vzip1q_u64(v[0], v[1])));
            vst1q_u8(o0.add(16), vreinterpretq_u8_u64(vzip1q_u64(v[2], v[3])));
            vst1q_u8(o1, vreinterpretq_u8_u64(vzip2q_u64(v[0], v[1])));
            vst1q_u8(o1.add(16), vreinterpretq_u8_u64(vzip2q_u64(v[2], v[3])));
        }
    }

    /// One [`super::hash_md`] chain per pointer, walked together: 64 bytes open
    /// it, then a 32-byte group a link. `len` is a whole number of groups and at
    /// least 64, or, with `st`, a whole number of groups continuing that state.
    ///
    /// SAFETY: both pointers must be readable for `len` bytes.
    #[inline]
    unsafe fn chain(p0: *const u8, p1: *const u8, len: usize, st: Option<Pair>) -> Pair {
        unsafe {
            let (mut acc, mut off) = match st {
                Some(st) => (st, 0),
                None => {
                    let lo = load32(p0, p1);
                    let hi = load32(p0.add(32), p1.add(32));
                    (link([lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]), 64)
                }
            };
            while off < len {
                let g = load32(p0.add(off), p1.add(off));
                acc = link([acc[0], acc[1], acc[2], acc[3], g[0], g[1], g[2], g[3]]);
                off += 32;
            }
            acc
        }
    }

    /// A chain state broadcast into both halves.
    #[inline]
    fn broadcast(state: &[u8; OUT_LEN]) -> Pair {
        // SAFETY: no memory is touched; `state` is read as four words.
        unsafe { std::array::from_fn(|i| vdupq_n_u64(u64::from_le_bytes(state[8 * i..8 * i + 8].try_into().unwrap()))) }
    }

    /// [`super::hash_many_md`] and [`super::hash_many_md_from_state`] over the
    /// even prefix of the records, two chains at a time. Returns how many
    /// records were written, always even.
    pub fn hash_many_md_pairs(data: &[u8], len: usize, state: Option<&[u8; OUT_LEN]>, out: &mut [u8]) -> usize {
        let n = (data.len() / len) & !1;
        let st = state.map(broadcast);
        for p in 0..n / 2 {
            // SAFETY: record `2p+1` ends at `(2p + 2) * len <= data.len()`, and the
            // two 32-byte digests at `2p * OUT_LEN` are inside `out`, which the
            // caller checked holds `data.len() / len` of them.
            unsafe {
                let p0 = data.as_ptr().add(2 * p * len);
                let acc = chain(p0, p0.add(len), len, st);
                let o0 = out.as_mut_ptr().add(2 * p * OUT_LEN);
                store32(acc, o0, o0.add(OUT_LEN));
            }
        }
        n
    }

    /// One [`super::hash_md`] chain, in lanes: the same code with the record in
    /// both halves.
    pub fn hash_md_one(rec: &[u8], state: Option<&[u8; OUT_LEN]>) -> [u8; OUT_LEN] {
        let mut out = [0u8; 2 * OUT_LEN];
        // SAFETY: `rec` is `rec.len()` readable bytes, read twice, and `out`
        // holds the two 32-byte halves the de-interleave writes.
        unsafe {
            let p = rec.as_ptr();
            let acc = chain(p, p, rec.len(), state.map(broadcast));
            store32(acc, out.as_mut_ptr(), out.as_mut_ptr().add(OUT_LEN));
        }
        out[..OUT_LEN].try_into().unwrap()
    }

    /// SHA3-256 of exactly 64 bytes.
    pub fn hash_block(block: &[u8; 64]) -> [u8; OUT_LEN] {
        hash_md_one(block, None)
    }

    /// `Keccak-f[1600]` on one state, which is [`permute_x2`] with the state in
    /// both halves. Half the width goes unused; the fused instructions and the
    /// absence of spills still beat the portable permutation.
    pub fn permute(state: &mut [u64; STATE_LANES]) {
        // SAFETY: `state` is 8-aligned and 25 words long, and every store below
        // writes one of those words.
        unsafe {
            let a = permute_x2(std::array::from_fn(|i| vdupq_n_u64(state[i])));
            for (i, v) in a.iter().enumerate() {
                vst1_u64(state.as_mut_ptr().add(i), vget_low_u64(*v));
            }
        }
    }

    /// SHA3-256 of two equal-length messages, resuming from a shared state:
    /// the plain sponge, absorbing whole [`RATE`] blocks.
    pub fn hash_pair_from_state(m0: &[u8], m1: &[u8], state: &[u64; STATE_LANES]) -> ([u8; OUT_LEN], [u8; OUT_LEN]) {
        debug_assert_eq!(m0.len(), m1.len());
        // SAFETY: the loads below stay inside `m0` and `m1`, and the digests are
        // written to local arrays.
        unsafe {
            let mut a: [uint64x2_t; STATE_LANES] = std::array::from_fn(|i| vdupq_n_u64(state[i]));
            let (mut r0, mut r1) = (m0, m1);
            while r0.len() >= RATE {
                xor_pair(&mut a, &r0[..RATE], &r1[..RATE]);
                a = permute_x2(a);
                r0 = &r0[RATE..];
                r1 = &r1[RATE..];
            }
            xor_pair(&mut a, r0, r1);
            pad_pair(&mut a, r0.len());
            let a = permute_x2(a);
            let mut out = [0u8; 2 * OUT_LEN];
            store32(
                [a[0], a[1], a[2], a[3]],
                out.as_mut_ptr(),
                out.as_mut_ptr().add(OUT_LEN),
            );
            (out[..OUT_LEN].try_into().unwrap(), out[OUT_LEN..].try_into().unwrap())
        }
    }

    /// XOR two messages into the rate, a lane of each state at a time and the
    /// odd tail byte by byte.
    #[inline]
    unsafe fn xor_pair(a: &mut [uint64x2_t; STATE_LANES], b0: &[u8], b1: &[u8]) {
        unsafe {
            let whole = b0.len() / 8;
            for l in 0..whole {
                let w0 = u64::from_le_bytes(b0[8 * l..8 * l + 8].try_into().unwrap());
                let w1 = u64::from_le_bytes(b1[8 * l..8 * l + 8].try_into().unwrap());
                a[l] = veorq_u64(a[l], vcombine_u64(vcreate_u64(w0), vcreate_u64(w1)));
            }
            let mut t0 = 0u64;
            let mut t1 = 0u64;
            for (i, (&x, &y)) in b0[8 * whole..].iter().zip(&b1[8 * whole..]).enumerate() {
                t0 |= (x as u64) << (8 * i);
                t1 |= (y as u64) << (8 * i);
            }
            if t0 | t1 != 0 {
                a[whole] = veorq_u64(a[whole], vcombine_u64(vcreate_u64(t0), vcreate_u64(t1)));
            }
        }
    }

    /// `pad10*1` around the domain byte, for a tail shorter than [`RATE`].
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

    /// The whole [`hash_md`] chain, batched and one at a time, against a chain
    /// built only from [`permute_portable`]: the reference stays independent of
    /// whichever backend the batch runs on, and an odd record count exercises
    /// the tail the batch leaves behind.
    #[test]
    fn batched_md_matches_the_portable_chain() {
        for len in [64usize, 96, 192, 512] {
            for n in [1usize, 2, 5] {
                let data: Vec<u8> = (0..n * len).map(|i| (i * 37 + 13) as u8).collect();
                let mut out = vec![0u8; n * OUT_LEN];
                hash_many_md(&data, len, &mut out);
                for i in 0..n {
                    let rec = &data[i * len..(i + 1) * len];
                    let want = hash_md_portable(rec);
                    assert_eq!(
                        &out[i * OUT_LEN..(i + 1) * OUT_LEN],
                        &want[..],
                        "len {len}, n {n}, record {i}"
                    );
                    assert_eq!(hash_md(rec), want, "len {len}, record {i}");
                }
                // The same records resumed from a shared state, which is the
                // padding-free leaf path.
                let state = md_zero_prefix_state(2);
                let mut from = vec![0u8; n * OUT_LEN];
                hash_many_md_from_state(&data, len, &state, &mut from);
                for i in 0..n {
                    let mut full = vec![0u8; 64];
                    full.extend_from_slice(&data[i * len..(i + 1) * len]);
                    assert_eq!(&from[i * OUT_LEN..(i + 1) * OUT_LEN], &hash_md_portable(&full)[..]);
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
