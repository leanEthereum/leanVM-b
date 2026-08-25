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
//! Natively the permutation is bitwise and lanewise, so what a host gives it is
//! width: `LANES` independent sponges share one set of vector registers, one
//! per state lane, and a round is elementwise 64-bit work with no cross-lane
//! traffic. That is where the volume is, the PCS Merkle tree hashing millions
//! of independent leaves and parents, so the batched paths ([`hash_many_md`],
//! [`hash_many`]) get `LANES` hashes for the price of one.
//!
//! aarch64's FEAT_SHA3 fits two states in its 128-bit registers and spends
//! fewer instructions on each: `BCAX` is `chi` in one, and `XAR` fuses
//! `theta`'s per-lane XOR into `rho`'s rotation. x86 has no Keccak extension,
//! but `vpternlogq` recovers `chi` and `theta`'s parity as one instruction each,
//! and AVX-512's eight states per register more than pay for the rotation it
//! cannot fuse. A lone hash rides the pair on aarch64, the fused instructions
//! covering the idle lane; on x86 it stays scalar, seven idle lanes being no
//! bargain.
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
    let a = permute_lanes::<Single>(std::array::from_fn(|i| Single::splat(state[i])));
    for (lane, v) in state.iter_mut().zip(a) {
        *lane = v.lane0();
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
    md_one::<Single>(block, None)
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
    md_one::<Single>(msg, None)
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
    md_one::<Single>(rest, Some(state))
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
    if len >= 64 && len.is_multiple_of(32) {
        i = md_many::<Batch>(data, len, n, None, out);
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
    let mut i = md_many::<Batch>(data, len, n, Some(state), out);
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

/// States hashed in one batch: eight under AVX-512, four under AVX2, two under
/// aarch64's FEAT_SHA3, one with no vector permutation to run. Batched entry
/// points accept any count and run the remainder one at a time.
pub const LANES: usize = <Batch as Lanes64>::WIDTH;

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
    let mut i = n - n % LANES;
    for g in 0..i / LANES {
        let base = g * LANES;
        // SAFETY: record `base + LANES - 1` ends at `i * len <= data.len()`, and
        // its digest at `(base + LANES - 1) * OUT_LEN` is inside `out`.
        unsafe {
            sponge_group::<Batch>(
                data.as_ptr().add(base * len),
                len,
                len,
                state,
                out.as_mut_ptr().add(base * OUT_LEN),
            );
        }
    }
    while i < n {
        let d = hash_from_state(&data[i * len..(i + 1) * len], state);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// The batched core
// ---------------------------------------------------------------------------

// `WIDTH` independent sponges share one set of vector registers: state lane `i`
// of every one of them is a single vector, so a round is elementwise 64-bit work
// with no cross-lane traffic. The permutation is written once over [`Lanes64`]
// and instantiated per backend, which supply only `theta`'s parity, `theta`'s
// XOR fused with `rho`'s rotation, and `chi`.
//
// The register file fixes the width: twenty-five lanes is twenty-five of the
// thirty-two vector registers, so the state stays resident across all 24 rounds
// and a wider batch spills. That is two states on aarch64's 128-bit registers
// and eight on AVX-512's. AVX2 takes four, which does spill, and still wins for
// having four times the XOR width and nothing else to spend it on.
//
// The instruction sets are not equal here. FEAT_SHA3 gives `BCAX` (`chi` in one
// instruction), `EOR3`, `RAX1` and `XAR` (`theta`'s per-lane XOR fused into
// `rho`'s rotation), so a round is 10 `EOR3`, 5 `RAX1`, 25 `XAR`, 25 `BCAX` and
// the `iota` `EOR`. AVX-512 has no Keccak extension, but `vpternlogq` is an
// arbitrary three-input bitwise function in one instruction, so `EOR3` is
// immediate `0x96` and `BCAX` immediate `0xb4`; only `XAR` has no counterpart,
// `vprorq` costing an instruction beyond the XOR. A round is then 96
// instructions against aarch64's 66, for four times the states.

/// The widest batch any backend runs, and the length of every scratch array the
/// generic driver keeps on the stack.
const MAX_LANES: usize = 8;

/// One state lane across a whole batch: a vector of `WIDTH` 64-bit lanes.
///
/// # Safety
/// `load` and `store` take raw pointers to `WIDTH` contiguous `u64`, and
/// implementors may use unaligned vector accesses, so callers must keep those
/// `WIDTH` elements in bounds.
trait Lanes64: Copy {
    /// States hashed together. A power of two, and at most [`MAX_LANES`].
    const WIDTH: usize;

    fn splat(x: u64) -> Self;
    fn xor(self, b: Self) -> Self;
    /// `a ^ b ^ c`; `theta`'s column parity is two of these.
    fn xor3(self, b: Self, c: Self) -> Self;
    /// `a ^ rotl(b, 1)`, which is `theta`'s `d` word.
    fn rax1(self, b: Self) -> Self;
    /// `rotr(a ^ b, N)`: `theta`'s per-lane XOR and `rho`'s rotation, which one
    /// instruction does on aarch64 and two everywhere else.
    fn xor_rotr<const N: i32>(self, b: Self) -> Self;
    /// `a ^ (b & !c)`, which is `chi`.
    fn chi(self, b: Self, c: Self) -> Self;
    /// Lane 0, which is the whole answer when a lone hash rides a batched
    /// backend.
    fn lane0(self) -> u64;

    /// # Safety
    /// `p` must be valid for reads of `WIDTH` `u64`.
    unsafe fn load(p: *const u64) -> Self;

    /// # Safety
    /// `p` must be valid for writes of `WIDTH` `u64`.
    unsafe fn store(self, p: *mut u64);

    /// Lane `l` is the little-endian `u64` at `base + l * stride + off`. A
    /// `stride` of 0 puts one input in every lane, which is how a lone hash runs
    /// on a batched backend.
    ///
    /// # Safety
    /// Every `base + l * stride + off` must be valid for 8 readable bytes.
    #[inline(always)]
    unsafe fn gather(base: *const u8, stride: usize, off: usize) -> Self {
        let mut w = [0u64; MAX_LANES];
        for (l, slot) in w[..Self::WIDTH].iter_mut().enumerate() {
            // SAFETY: the caller guarantees 8 readable bytes at every lane.
            *slot = unsafe { base.add(l * stride + off).cast::<u64>().read_unaligned() };
        }
        // SAFETY: `w` holds MAX_LANES >= WIDTH words.
        unsafe { Self::load(w.as_ptr()) }
    }

    /// De-interleave the four digest words into `WIDTH` consecutive 32-byte
    /// digests.
    ///
    /// # Safety
    /// `out` must be valid for writes of `WIDTH * OUT_LEN` bytes.
    #[inline(always)]
    unsafe fn store_digests(h: &[Self; 4], out: *mut u8) {
        let mut w = [0u64; 4 * MAX_LANES];
        for (i, hi) in h.iter().enumerate() {
            // SAFETY: `w` holds 4 * MAX_LANES >= 4 * WIDTH words.
            unsafe { hi.store(w.as_mut_ptr().add(i * Self::WIDTH)) };
        }
        for lane in 0..Self::WIDTH {
            for i in 0..4 {
                let bytes = w[i * Self::WIDTH + lane].to_le_bytes();
                // SAFETY: `lane * 32 + 8 * i + 8 <= WIDTH * OUT_LEN`.
                unsafe {
                    out.add(lane * OUT_LEN + 8 * i)
                        .copy_from_nonoverlapping(bytes.as_ptr(), 8)
                };
            }
        }
    }
}

/// The portable backend, and the reference the SIMD ones are checked against.
/// Also what a lone hash runs on wherever the batched backend is wider than
/// aarch64's two, since there the idle lanes are not paid for by fused
/// instructions.
#[allow(dead_code)]
#[derive(Clone, Copy)]
struct Scalar(u64);

impl Lanes64 for Scalar {
    const WIDTH: usize = 1;

    #[inline(always)]
    fn splat(x: u64) -> Self {
        Self(x)
    }
    #[inline(always)]
    fn xor(self, b: Self) -> Self {
        Self(self.0 ^ b.0)
    }
    #[inline(always)]
    fn xor3(self, b: Self, c: Self) -> Self {
        Self(self.0 ^ b.0 ^ c.0)
    }
    #[inline(always)]
    fn rax1(self, b: Self) -> Self {
        Self(self.0 ^ b.0.rotate_left(1))
    }
    #[inline(always)]
    fn xor_rotr<const N: i32>(self, b: Self) -> Self {
        Self((self.0 ^ b.0).rotate_right(N as u32))
    }
    #[inline(always)]
    fn chi(self, b: Self, c: Self) -> Self {
        Self(self.0 ^ (b.0 & !c.0))
    }
    #[inline(always)]
    fn lane0(self) -> u64 {
        self.0
    }
    #[inline(always)]
    unsafe fn load(p: *const u64) -> Self {
        Self(unsafe { *p })
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u64) {
        unsafe { *p = self.0 };
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
mod arm {
    use super::Lanes64;
    use core::arch::aarch64::*;

    /// Two states per Q register, driven by FEAT_SHA3's `EOR3`, `RAX1`, `XAR`
    /// and `BCAX`.
    #[derive(Clone, Copy)]
    pub(super) struct Neon(uint64x2_t);

    impl Lanes64 for Neon {
        const WIDTH: usize = 2;

        #[inline(always)]
        fn splat(x: u64) -> Self {
            Self(unsafe { vdupq_n_u64(x) })
        }
        #[inline(always)]
        fn xor(self, b: Self) -> Self {
            Self(unsafe { veorq_u64(self.0, b.0) })
        }
        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            Self(unsafe { veor3q_u64(self.0, b.0, c.0) })
        }
        #[inline(always)]
        fn rax1(self, b: Self) -> Self {
            Self(unsafe { vrax1q_u64(self.0, b.0) })
        }
        #[inline(always)]
        fn xor_rotr<const N: i32>(self, b: Self) -> Self {
            Self(unsafe { vxarq_u64::<N>(self.0, b.0) })
        }
        #[inline(always)]
        fn chi(self, b: Self, c: Self) -> Self {
            Self(unsafe { vbcaxq_u64(self.0, b.0, c.0) })
        }
        #[inline(always)]
        fn lane0(self) -> u64 {
            unsafe { vgetq_lane_u64::<0>(self.0) }
        }
        #[inline(always)]
        unsafe fn load(p: *const u64) -> Self {
            Self(unsafe { vld1q_u64(p) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            unsafe { vst1q_u64(p, self.0) };
        }
        /// Two scalar loads and one `INS`, which is what the hand-written pair
        /// loader did before this was written over [`Lanes64`]. The default's
        /// stack round trip measured the same on the wider x86 backends, so
        /// this is conservatism about a host that cannot be measured here, not
        /// a known win.
        #[inline(always)]
        unsafe fn gather(base: *const u8, stride: usize, off: usize) -> Self {
            unsafe {
                let w0 = base.add(off).cast::<u64>().read_unaligned();
                let w1 = base.add(stride + off).cast::<u64>().read_unaligned();
                Self(vcombine_u64(vcreate_u64(w0), vcreate_u64(w1)))
            }
        }
        /// The digest pair de-interleaved by `ZIP1`/`ZIP2`, as above.
        #[inline(always)]
        unsafe fn store_digests(h: &[Self; 4], out: *mut u8) {
            unsafe {
                let o1 = out.add(super::OUT_LEN);
                vst1q_u8(out, vreinterpretq_u8_u64(vzip1q_u64(h[0].0, h[1].0)));
                vst1q_u8(out.add(16), vreinterpretq_u8_u64(vzip1q_u64(h[2].0, h[3].0)));
                vst1q_u8(o1, vreinterpretq_u8_u64(vzip2q_u64(h[0].0, h[1].0)));
                vst1q_u8(o1.add(16), vreinterpretq_u8_u64(vzip2q_u64(h[2].0, h[3].0)));
            }
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod x86 {
    use super::Lanes64;
    use core::arch::x86_64::*;

    /// AVX2: four states, at four registers each, so the state does not stay
    /// resident and the round pays some spill traffic. Kept anyway because it is
    /// still four XORs an instruction, and because most x86 has no AVX-512.
    ///
    /// Unused by the library on an AVX-512 target (the dispatch is compile
    /// time), but always exercised by `every_backend_matches_scalar`.
    #[cfg_attr(target_feature = "avx512f", allow(dead_code))]
    #[derive(Clone, Copy)]
    pub(super) struct Avx2(__m256i);

    /// `rotr` by a constant, as the shift pair AVX2 has to spell it. The count
    /// travels in an `xmm` because the const-generic shift wants `64 - N`, which
    /// is not an expression a stable const generic may hold; LLVM folds the
    /// splat back into the shift's immediate.
    #[inline(always)]
    unsafe fn ror(x: __m256i, n: i32) -> __m256i {
        unsafe {
            if n == 0 {
                return x;
            }
            _mm256_or_si256(
                _mm256_srl_epi64(x, _mm_cvtsi32_si128(n)),
                _mm256_sll_epi64(x, _mm_cvtsi32_si128(64 - n)),
            )
        }
    }

    impl Lanes64 for Avx2 {
        const WIDTH: usize = 4;

        #[inline(always)]
        fn splat(x: u64) -> Self {
            Self(unsafe { _mm256_set1_epi64x(x as i64) })
        }
        #[inline(always)]
        fn xor(self, b: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(self.0, b.0) })
        }
        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(_mm256_xor_si256(self.0, b.0), c.0) })
        }
        #[inline(always)]
        fn rax1(self, b: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(self.0, ror(b.0, 63)) })
        }
        #[inline(always)]
        fn xor_rotr<const N: i32>(self, b: Self) -> Self {
            Self(unsafe { ror(_mm256_xor_si256(self.0, b.0), N) })
        }
        #[inline(always)]
        fn chi(self, b: Self, c: Self) -> Self {
            Self(unsafe { _mm256_xor_si256(self.0, _mm256_andnot_si256(c.0, b.0)) })
        }
        #[inline(always)]
        fn lane0(self) -> u64 {
            unsafe { _mm_cvtsi128_si64(_mm256_castsi256_si128(self.0)) as u64 }
        }
        #[inline(always)]
        unsafe fn load(p: *const u64) -> Self {
            Self(unsafe { _mm256_loadu_si256(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            unsafe { _mm256_storeu_si256(p.cast(), self.0) };
        }
    }

    /// AVX-512: eight states, `vpternlogq` for `chi` and `theta`'s parity, and
    /// `vprorq` for `rho`.
    #[cfg(target_feature = "avx512f")]
    #[derive(Clone, Copy)]
    pub(super) struct Avx512(__m512i);

    #[cfg(target_feature = "avx512f")]
    impl Lanes64 for Avx512 {
        const WIDTH: usize = 8;

        #[inline(always)]
        fn splat(x: u64) -> Self {
            Self(unsafe { _mm512_set1_epi64(x as i64) })
        }
        #[inline(always)]
        fn xor(self, b: Self) -> Self {
            Self(unsafe { _mm512_xor_si512(self.0, b.0) })
        }
        #[inline(always)]
        fn xor3(self, b: Self, c: Self) -> Self {
            Self(unsafe { _mm512_ternarylogic_epi64::<0x96>(self.0, b.0, c.0) })
        }
        #[inline(always)]
        fn rax1(self, b: Self) -> Self {
            Self(unsafe { _mm512_xor_si512(self.0, _mm512_rol_epi64::<1>(b.0)) })
        }
        #[inline(always)]
        fn xor_rotr<const N: i32>(self, b: Self) -> Self {
            Self(unsafe { _mm512_ror_epi64::<N>(_mm512_xor_si512(self.0, b.0)) })
        }
        #[inline(always)]
        fn chi(self, b: Self, c: Self) -> Self {
            Self(unsafe { _mm512_ternarylogic_epi64::<0xb4>(self.0, b.0, c.0) })
        }
        #[inline(always)]
        fn lane0(self) -> u64 {
            unsafe { _mm_cvtsi128_si64(_mm512_castsi512_si128(self.0)) as u64 }
        }
        #[inline(always)]
        unsafe fn load(p: *const u64) -> Self {
            Self(unsafe { _mm512_loadu_si512(p.cast()) })
        }
        #[inline(always)]
        unsafe fn store(self, p: *mut u64) {
            unsafe { _mm512_storeu_si512(p.cast(), self.0) };
        }
    }
}

/// The backend a batch of independent hashes runs on.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
type Batch = x86::Avx512;
#[cfg(all(target_arch = "x86_64", not(target_feature = "avx512f"), target_feature = "avx2"))]
type Batch = x86::Avx2;
#[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
type Batch = arm::Neon;
#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "avx2"),
    all(target_arch = "aarch64", target_feature = "sha3")
)))]
type Batch = Scalar;

/// The backend a lone hash runs on, with the same input in every lane. Only
/// aarch64 wants a vector there: FEAT_SHA3's fused instructions pay for the one
/// idle lane, where a wider x86 vector would waste seven and lose to the scalar
/// permutation.
#[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
type Single = arm::Neon;
#[cfg(not(all(target_arch = "aarch64", target_feature = "sha3")))]
type Single = Scalar;

/// `Keccak-f[1600]` on `S::WIDTH` states at once.
#[inline(always)]
fn permute_lanes<S: Lanes64>(mut a: [S; STATE_LANES]) -> [S; STATE_LANES] {
    for &rc in RC.iter() {
        let c0 = a[0].xor3(a[5], a[10]).xor3(a[15], a[20]);
        let c1 = a[1].xor3(a[6], a[11]).xor3(a[16], a[21]);
        let c2 = a[2].xor3(a[7], a[12]).xor3(a[17], a[22]);
        let c3 = a[3].xor3(a[8], a[13]).xor3(a[18], a[23]);
        let c4 = a[4].xor3(a[9], a[14]).xor3(a[19], a[24]);
        let d0 = c4.rax1(c1);
        let d1 = c0.rax1(c2);
        let d2 = c1.rax1(c3);
        let d3 = c2.rax1(c4);
        let d4 = c3.rax1(c0);

        // `rho` and `pi` gathered: lane `PI[i]` of the theta'd state, rotated
        // left by `RHO[PI[i]]`, which is the `64 - N` these spell as a rotate
        // right.
        let b00 = a[0].xor_rotr::<0>(d0);
        let b01 = a[6].xor_rotr::<20>(d1);
        let b02 = a[12].xor_rotr::<21>(d2);
        let b03 = a[18].xor_rotr::<43>(d3);
        let b04 = a[24].xor_rotr::<50>(d4);
        let b05 = a[3].xor_rotr::<36>(d3);
        let b06 = a[9].xor_rotr::<44>(d4);
        let b07 = a[10].xor_rotr::<61>(d0);
        let b08 = a[16].xor_rotr::<19>(d1);
        let b09 = a[22].xor_rotr::<3>(d2);
        let b10 = a[1].xor_rotr::<63>(d1);
        let b11 = a[7].xor_rotr::<58>(d2);
        let b12 = a[13].xor_rotr::<39>(d3);
        let b13 = a[19].xor_rotr::<56>(d4);
        let b14 = a[20].xor_rotr::<46>(d0);
        let b15 = a[4].xor_rotr::<37>(d4);
        let b16 = a[5].xor_rotr::<28>(d0);
        let b17 = a[11].xor_rotr::<54>(d1);
        let b18 = a[17].xor_rotr::<49>(d2);
        let b19 = a[23].xor_rotr::<8>(d3);
        let b20 = a[2].xor_rotr::<2>(d2);
        let b21 = a[8].xor_rotr::<9>(d3);
        let b22 = a[14].xor_rotr::<25>(d4);
        let b23 = a[15].xor_rotr::<23>(d0);
        let b24 = a[21].xor_rotr::<62>(d1);

        a[0] = b00.chi(b02, b01);
        a[1] = b01.chi(b03, b02);
        a[2] = b02.chi(b04, b03);
        a[3] = b03.chi(b00, b04);
        a[4] = b04.chi(b01, b00);
        a[5] = b05.chi(b07, b06);
        a[6] = b06.chi(b08, b07);
        a[7] = b07.chi(b09, b08);
        a[8] = b08.chi(b05, b09);
        a[9] = b09.chi(b06, b05);
        a[10] = b10.chi(b12, b11);
        a[11] = b11.chi(b13, b12);
        a[12] = b12.chi(b14, b13);
        a[13] = b13.chi(b10, b14);
        a[14] = b14.chi(b11, b10);
        a[15] = b15.chi(b17, b16);
        a[16] = b16.chi(b18, b17);
        a[17] = b17.chi(b19, b18);
        a[18] = b18.chi(b15, b19);
        a[19] = b19.chi(b16, b15);
        a[20] = b20.chi(b22, b21);
        a[21] = b21.chi(b23, b22);
        a[22] = b22.chi(b24, b23);
        a[23] = b23.chi(b20, b24);
        a[24] = b24.chi(b21, b20);

        a[0] = a[0].xor(S::splat(rc));
    }
    a
}

/// One link of the [`hash_md`] chain, and the whole of a 64-byte SHA3-256:
/// absorb `acc ‖ m` and the constant 64-byte pad, permute, keep the digest.
/// The pad is constant because the length is: `0x06` at byte 64 and the final
/// `0x80` at byte `RATE - 1`.
#[inline]
fn link<S: Lanes64>(acc: [S; 4], m: [S; 4]) -> [S; 4] {
    let mut a = [S::splat(0); STATE_LANES];
    a[..4].copy_from_slice(&acc);
    a[4..8].copy_from_slice(&m);
    a[8] = S::splat(DOMAIN as u64);
    a[16] = S::splat(0x80u64 << 56);
    let a = permute_lanes(a);
    [a[0], a[1], a[2], a[3]]
}

/// `S::WIDTH` [`hash_md`] chains walked together, one per lane: 64 bytes open
/// each, then a 32-byte group a link, or, with `st`, whole groups continuing
/// that state. Lane `l` reads `base + l * stride`, so a `stride` of 0 runs one
/// record in every lane.
///
/// # Safety
/// Every `base + l * stride` must be valid for `len` readable bytes, `len` a
/// whole number of 32-byte groups and at least 64 unless `st` is given, and
/// `out` valid for `S::WIDTH * OUT_LEN` writable bytes.
unsafe fn md_group<S: Lanes64>(base: *const u8, stride: usize, len: usize, st: Option<&[u8; OUT_LEN]>, out: *mut u8) {
    // SAFETY: the caller guarantees `len` readable bytes in every lane, and
    // `group` is only ever called at offsets inside that.
    let group = |off: usize| -> [S; 4] { std::array::from_fn(|j| unsafe { S::gather(base, stride, off + 8 * j) }) };
    let (mut acc, mut off) = match st {
        Some(s) => {
            let words = |i: usize| u64::from_le_bytes(s[8 * i..8 * i + 8].try_into().unwrap());
            (std::array::from_fn(|i| S::splat(words(i))), 0)
        }
        None => (link(group(0), group(32)), 64),
    };
    while off < len {
        acc = link(acc, group(off));
        off += 32;
    }
    // SAFETY: the caller guarantees `WIDTH * OUT_LEN` writable bytes at `out`.
    unsafe { S::store_digests(&acc, out) };
}

/// One [`hash_md`] chain, with the record in every lane of `S`.
fn md_one<S: Lanes64>(rec: &[u8], st: Option<&[u8; OUT_LEN]>) -> [u8; OUT_LEN] {
    let mut out = [0u8; MAX_LANES * OUT_LEN];
    // SAFETY: a stride of 0 reads `rec` in every lane, and `out` holds
    // MAX_LANES >= WIDTH digests.
    unsafe { md_group::<S>(rec.as_ptr(), 0, rec.len(), st, out.as_mut_ptr()) };
    out[..OUT_LEN].try_into().unwrap()
}

/// [`hash_many_md`] and [`hash_many_md_from_state`] over the `S::WIDTH`-aligned
/// prefix of `n` records of `len` bytes. Returns how many were written.
fn md_many<S: Lanes64>(data: &[u8], len: usize, n: usize, st: Option<&[u8; OUT_LEN]>, out: &mut [u8]) -> usize {
    let whole = n - n % S::WIDTH;
    assert!(data.len() >= whole * len && out.len() >= whole * OUT_LEN);
    for g in 0..whole / S::WIDTH {
        let base = g * S::WIDTH;
        // SAFETY: record `base + WIDTH - 1` ends at `whole * len <= data.len()`,
        // and the `WIDTH` digests at `base * OUT_LEN` are inside `out`.
        unsafe {
            md_group::<S>(
                data.as_ptr().add(base * len),
                len,
                len,
                st,
                out.as_mut_ptr().add(base * OUT_LEN),
            );
        }
    }
    whole
}

/// XOR `n` bytes of every lane's message, starting at record offset `off`, into
/// the rate.
///
/// # Safety
/// Every `base + l * stride + off` must be valid for `n` readable bytes, with
/// `n <= RATE`.
#[inline]
unsafe fn xor_rate_lanes<S: Lanes64>(a: &mut [S; STATE_LANES], base: *const u8, stride: usize, off: usize, n: usize) {
    unsafe {
        let whole = n / 8;
        for (l, slot) in a[..whole].iter_mut().enumerate() {
            *slot = slot.xor(S::gather(base, stride, off + 8 * l));
        }
        let rem = n % 8;
        if rem != 0 {
            let mut w = [0u64; MAX_LANES];
            for (lane, slot) in w[..S::WIDTH].iter_mut().enumerate() {
                let p = base.add(lane * stride + off + 8 * whole);
                for i in 0..rem {
                    *slot |= (*p.add(i) as u64) << (8 * i);
                }
            }
            a[whole] = a[whole].xor(S::load(w.as_ptr()));
        }
    }
}

/// `S::WIDTH` plain sponges of `len` bytes each, resuming from a shared state:
/// absorb whole [`RATE`] blocks, then the tail and `pad10*1`.
///
/// # Safety
/// Every `base + l * stride` must be valid for `len` readable bytes, and `out`
/// for `S::WIDTH * OUT_LEN` writable bytes.
unsafe fn sponge_group<S: Lanes64>(
    base: *const u8,
    stride: usize,
    len: usize,
    state: &[u64; STATE_LANES],
    out: *mut u8,
) {
    unsafe {
        let mut a: [S; STATE_LANES] = std::array::from_fn(|i| S::splat(state[i]));
        let mut off = 0;
        while len - off >= RATE {
            xor_rate_lanes::<S>(&mut a, base, stride, off, RATE);
            a = permute_lanes(a);
            off += RATE;
        }
        let tail = len - off;
        xor_rate_lanes::<S>(&mut a, base, stride, off, tail);
        a[tail / 8] = a[tail / 8].xor(S::splat((DOMAIN as u64) << (8 * (tail % 8))));
        a[(RATE - 1) / 8] = a[(RATE - 1) / 8].xor(S::splat(0x80u64 << (8 * ((RATE - 1) % 8))));
        let a = permute_lanes(a);
        S::store_digests(&[a[0], a[1], a[2], a[3]], out);
    }
}

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
            for n in [1usize, 5, LANES, LANES + 1, 2 * LANES + 3] {
                let data: Vec<u8> = (0..n * len).map(|i| (i * 17 + 3) as u8).collect();
                let mut out = vec![0u8; n * OUT_LEN];
                hash_many_dyn(&data, len, &mut out);
                for i in 0..n {
                    let want = hash(&data[i * len..(i + 1) * len]);
                    assert_eq!(
                        &out[i * OUT_LEN..(i + 1) * OUT_LEN],
                        &want[..],
                        "len {len}, n {n}, record {i}"
                    );
                }
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
                let n = 2 * LANES + 3;
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
            for n in [1usize, 2, 5, LANES, LANES + 1, 2 * LANES + 3] {
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

    /// Every backend the crate can compile, taken or not, against the portable
    /// chain: the dispatch resolves at compile time, so without this the arm the
    /// host does not run is never executed anywhere.
    #[test]
    fn every_backend_matches_scalar() {
        fn check<S: Lanes64>(name: &str) {
            for n in [1usize, S::WIDTH - 1, S::WIDTH, S::WIDTH + 1, 3 * S::WIDTH + 2] {
                for len in [64usize, 96, 192, 512] {
                    let data: Vec<u8> = (0..n * len).map(|i| ((i * 37 + 11) & 0xff) as u8).collect();
                    let mut out = vec![0u8; n * OUT_LEN];
                    let done = md_many::<S>(&data, len, n, None, &mut out);
                    assert_eq!(done, n - n % S::WIDTH, "{name}: n {n}");
                    for i in 0..done {
                        let rec = &data[i * len..(i + 1) * len];
                        assert_eq!(
                            &out[i * OUT_LEN..(i + 1) * OUT_LEN],
                            &hash_md_portable(rec)[..],
                            "{name}: chain of {n} records of {len}, record {i}"
                        );
                        assert_eq!(md_one::<S>(rec, None), hash_md_portable(rec), "{name}: lone chain");
                    }
                    // The plain sponge, whose tail is not a whole lane.
                    let mut sponged = vec![0u8; S::WIDTH * OUT_LEN];
                    // SAFETY: `data` holds n * len >= WIDTH * len bytes when the
                    // batch is full, and `sponged` WIDTH digests.
                    if n >= S::WIDTH {
                        unsafe {
                            sponge_group::<S>(data.as_ptr(), len, len, &[0u64; STATE_LANES], sponged.as_mut_ptr())
                        };
                        for i in 0..S::WIDTH {
                            assert_eq!(
                                &sponged[i * OUT_LEN..(i + 1) * OUT_LEN],
                                &hash(&data[i * len..(i + 1) * len])[..],
                                "{name}: sponge of {len}, record {i}"
                            );
                        }
                    }
                }
            }
        }
        check::<Scalar>("scalar");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        check::<x86::Avx2>("avx2");
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        check::<x86::Avx512>("avx512");
        #[cfg(all(target_arch = "aarch64", target_feature = "sha3"))]
        check::<arm::Neon>("neon");
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
