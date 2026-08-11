//! BLAKE2s (RFC 7693), the repo's one hash function.
//!
//! Three surfaces, in increasing order of how much of the machine they touch:
//!
//! - [`compress`], the 10-round compression. Every other hash in leanVM-b is a
//!   chain of these, and it is the one the VM's `Blake2s` opcode computes and
//!   `flock::blake2s` proves.
//! - [`hash`] / [`keyed_hash`] / [`Hasher`], ordinary BLAKE2s-256 over bytes.
//! - [`hash_many`], the batched form: `LANES` independent equal-length inputs
//!   hashed together with the state transposed across lanes, which is how the
//!   PCS Merkle tree gets SIMD out of hashes that are individually serial.
//!
//! Why BLAKE2s and not BLAKE2s: the VM proves one compression per opcode, and
//! BLAKE2s's multi-block chunk tree (counter, flags, parent nodes) cannot be
//! reproduced by a single compression, so its streaming hasher was never
//! VM-native. BLAKE2s's compression takes the counter and the final-block flag
//! as ordinary inputs, so one opcode covers every use here.

/// BLAKE2s initial values: the SHA-256 IV.
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

/// Digest length in bytes. BLAKE2s-256 throughout.
pub const OUT_LEN: usize = 32;
/// Compression block length in bytes.
pub const BLOCK_LEN: usize = 64;
/// Rounds per compression.
pub const ROUNDS: usize = 10;

/// BLAKE2s message schedule.
pub const SIGMA: [[usize; 16]; ROUNDS] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/// Lanes touched by G index `g` within a round: `[a, b, c, d]`.
pub const G_LANES: [[usize; 4]; 8] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

/// The parameter block folded into `h[0]` for an unkeyed BLAKE2s-256:
/// digest length 32, key length 0, fanout 1, depth 1.
pub const PARAM_UNKEYED: u32 = 0x0101_0000 ^ OUT_LEN as u32;

/// The initial chaining value for a `key_len`-byte key (0 = unkeyed).
#[inline]
pub const fn init_state(key_len: usize) -> [u32; 8] {
    assert!(key_len <= 32, "BLAKE2s key is at most 32 bytes");
    let mut h = IV;
    h[0] ^= 0x0101_0000 ^ ((key_len as u32) << 8) ^ OUT_LEN as u32;
    h
}

/// The unkeyed BLAKE2s-256 initial chaining value: [`IV`] with the parameter
/// block folded into word 0. Hashing exactly 64 bytes is one [`compress`] from
/// this state at counter 64 with the final flag, which is what makes the VM's
/// one-compression opcode a complete hash.
pub const PARAM_IV: [u32; 8] = init_state(0);

/// The BLAKE2s compression: absorb one 64-byte block `m` at byte counter `t`
/// into the chaining value `h`. `last` sets the final-block flag `f0`.
///
/// This is the whole nonlinear core of every hash in leanVM-b. The `f1`
/// last-node flag is always zero: nothing here uses BLAKE2s's tree mode.
#[inline]
pub fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    if last {
        v[14] = !v[14];
    }
    for round in &SIGMA {
        for (g, &[a, b, c, d]) in G_LANES.iter().enumerate() {
            let (mx, my) = (m[round[2 * g]], m[round[2 * g + 1]]);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(mx);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(my);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
        }
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// Read a 64-byte block as 16 little-endian words.
#[inline]
fn block_words(block: &[u8; BLOCK_LEN]) -> [u32; 16] {
    std::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()))
}

/// Serialize a chaining value as the 32-byte digest.
#[inline]
fn state_bytes(h: &[u32; 8]) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    for (chunk, word) in out.chunks_exact_mut(4).zip(h) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    out
}

/// Streaming BLAKE2s-256.
///
/// The final block has to be compressed with the `last` flag, so the hasher
/// holds a full 64-byte buffer back until it knows more input follows. That is
/// the only subtlety; everything else is a straight block loop.
#[derive(Clone)]
pub struct Hasher {
    h: [u32; 8],
    buf: [u8; BLOCK_LEN],
    /// Bytes currently in `buf`, in `0..=BLOCK_LEN`.
    buf_len: usize,
    /// Bytes already compressed.
    counter: u64,
}

impl Hasher {
    pub fn new() -> Self {
        Self {
            h: init_state(0),
            buf: [0u8; BLOCK_LEN],
            buf_len: 0,
            counter: 0,
        }
    }

    /// Keyed BLAKE2s-256 (RFC 7693 §2.9): the zero-padded key is the first
    /// block. `key` must be at most 32 bytes.
    pub fn new_keyed(key: &[u8]) -> Self {
        assert!(key.len() <= 32, "BLAKE2s key is at most 32 bytes");
        let mut s = Self {
            h: init_state(key.len()),
            buf: [0u8; BLOCK_LEN],
            buf_len: 0,
            counter: 0,
        };
        if !key.is_empty() {
            // The key block counts toward the byte counter and is a full block
            // even when the key is shorter.
            s.buf[..key.len()].copy_from_slice(key);
            s.buf_len = BLOCK_LEN;
        }
        s
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.buf_len == BLOCK_LEN {
                // More input follows, so this buffered block is not the last.
                self.counter += BLOCK_LEN as u64;
                compress(&mut self.h, &block_words(&self.buf), self.counter, false);
                self.buf_len = 0;
            }
            let take = (BLOCK_LEN - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
        }
        self
    }

    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut h = self.h;
        let mut block = self.buf;
        block[self.buf_len..].fill(0);
        let t = self.counter + self.buf_len as u64;
        compress(&mut h, &block_words(&block), t, true);
        state_bytes(&h)
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

/// One-shot unkeyed BLAKE2s-256.
pub fn hash(data: &[u8]) -> [u8; OUT_LEN] {
    // Fast path for the shapes the protocol actually hashes in bulk: a whole
    // number of blocks, no buffering needed.
    if !data.is_empty() && data.len().is_multiple_of(BLOCK_LEN) {
        let mut h = init_state(0);
        let n = data.len() / BLOCK_LEN;
        for (b, block) in data.chunks_exact(BLOCK_LEN).enumerate() {
            let t = ((b + 1) * BLOCK_LEN) as u64;
            compress(&mut h, &block_words(block.try_into().unwrap()), t, b + 1 == n);
        }
        return state_bytes(&h);
    }
    let mut hasher = Hasher::new();
    hasher.update(data);
    hasher.finalize()
}

/// One-shot keyed BLAKE2s-256, the PRF form. `key` is at most 32 bytes.
pub fn keyed_hash(key: &[u8], data: &[u8]) -> [u8; OUT_LEN] {
    let mut hasher = Hasher::new_keyed(key);
    hasher.update(data);
    hasher.finalize()
}

// ---------------------------------------------------------------------------
// Batched (transposed) hashing
// ---------------------------------------------------------------------------

/// Independent inputs hashed per batch. The state is held as `[[u32; LANES];
/// 16]`, so each round's arithmetic is `LANES`-wide elementwise `u32` work that
/// the compiler turns into SIMD.
///
/// Eight measured fastest of 4/8/16 on AVX-512 (1841 vs 1690 and 1530 MB/s):
/// the working state and the message block together are 32 vectors, so 16 lanes
/// spills them. Two things that look like wins are not: fully unrolling the
/// rounds so every index is literal (1132 MB/s, same spill), and gathering each
/// lane's block contiguously before transposing (no change, so the round
/// function is the cost, not the load pattern).
///
/// For scale, BLAKE2s's hand-written multi-input kernel does 5815 MB/s on the
/// same shapes. A factor 10/7 of that gap is BLAKE2s having ten rounds per
/// 64-byte block against BLAKE2s's seven; the remaining ~2.2x is hand-written
/// intrinsics, which is the lever left if Merkle hashing becomes the bottleneck.
pub const LANES: usize = 8;

/// One state word across all lanes.
type Lanes = [u32; LANES];

#[inline(always)]
fn v_add(a: Lanes, b: Lanes) -> Lanes {
    std::array::from_fn(|i| a[i].wrapping_add(b[i]))
}

#[inline(always)]
fn v_xor(a: Lanes, b: Lanes) -> Lanes {
    std::array::from_fn(|i| a[i] ^ b[i])
}

#[inline(always)]
fn v_rotr(a: Lanes, n: u32) -> Lanes {
    std::array::from_fn(|i| a[i].rotate_right(n))
}

/// One transposed compression across `LANES` independent inputs. `t` and
/// `last` are shared, which holds because every batch here hashes equal-length
/// inputs and so steps their block counters in lockstep.
#[inline(always)]
fn compress_lanes(h: &mut [Lanes; 8], m: &[Lanes; 16], t: u64, last: bool) {
    let mut v = [[0u32; LANES]; 16];
    v[..8].copy_from_slice(h);
    for i in 0..8 {
        v[8 + i] = [IV[i]; LANES];
    }
    v[12] = v_xor(v[12], [t as u32; LANES]);
    v[13] = v_xor(v[13], [(t >> 32) as u32; LANES]);
    if last {
        v[14] = v_xor(v[14], [u32::MAX; LANES]);
    }
    for round in &SIGMA {
        for (g, &[a, b, c, d]) in G_LANES.iter().enumerate() {
            let (mx, my) = (m[round[2 * g]], m[round[2 * g + 1]]);
            v[a] = v_add(v_add(v[a], v[b]), mx);
            v[d] = v_rotr(v_xor(v[d], v[a]), 16);
            v[c] = v_add(v[c], v[d]);
            v[b] = v_rotr(v_xor(v[b], v[c]), 12);
            v[a] = v_add(v_add(v[a], v[b]), my);
            v[d] = v_rotr(v_xor(v[d], v[a]), 8);
            v[c] = v_add(v[c], v[d]);
            v[b] = v_rotr(v_xor(v[b], v[c]), 7);
        }
    }
    for i in 0..8 {
        h[i] = v_xor(h[i], v_xor(v[i], v[i + 8]));
    }
}

/// Transpose one 64-byte block from each lane into `[[u32; LANES]; 16]`.
///
/// Each lane's block is read contiguously first, then transposed in registers.
/// Gathering word-by-word across lanes instead strides by `LEN` per load, which
/// neither vectorizes nor prefetches.
#[inline(always)]
fn gather_block<const LEN: usize>(inputs: &[&[u8; LEN]; LANES], block: usize) -> [Lanes; 16] {
    let off = block * BLOCK_LEN;
    let per_lane: [[u32; 16]; LANES] = std::array::from_fn(|lane| {
        let b: &[u8; BLOCK_LEN] = inputs[lane][off..off + BLOCK_LEN].try_into().unwrap();
        block_words(b)
    });
    std::array::from_fn(|w| std::array::from_fn(|lane| per_lane[lane][w]))
}

/// Hash `LANES` inputs of `LEN` bytes each, writing `LANES` consecutive
/// 32-byte digests to `out`. `LEN` must be a nonzero multiple of 64.
#[inline]
fn hash_lane_group<const LEN: usize>(inputs: &[&[u8; LEN]; LANES], out: &mut [u8]) {
    const {
        assert!(LEN > 0 && LEN.is_multiple_of(BLOCK_LEN));
    }
    debug_assert_eq!(out.len(), LANES * OUT_LEN);
    let n_blocks = LEN / BLOCK_LEN;
    let mut h: [Lanes; 8] = std::array::from_fn(|i| [init_state(0)[i]; LANES]);
    for b in 0..n_blocks {
        let m = gather_block(inputs, b);
        compress_lanes(&mut h, &m, ((b + 1) * BLOCK_LEN) as u64, b + 1 == n_blocks);
    }
    // Un-transpose: lane `l`'s digest is word `i` of `h[i][l]`.
    for (lane, digest) in out.chunks_exact_mut(OUT_LEN).enumerate() {
        for (i, chunk) in digest.chunks_exact_mut(4).enumerate() {
            chunk.copy_from_slice(&h[i][lane].to_le_bytes());
        }
    }
}

/// Batched BLAKE2s-256 of `data` split into `LEN`-byte inputs, writing one
/// 32-byte digest per input to `out`.
///
/// Byte-identical to [`hash`] per input; the batching only changes how the
/// lanes are scheduled. `LEN` must be a nonzero multiple of 64. A trailing
/// partial group (fewer than [`LANES`] inputs) falls back to the scalar path.
pub fn hash_many<const LEN: usize>(data: &[u8], out: &mut [u8]) {
    let n = out.len() / OUT_LEN;
    debug_assert_eq!(data.len(), n * LEN);
    debug_assert_eq!(out.len(), n * OUT_LEN);
    let groups = n / LANES;
    for g in 0..groups {
        let base = g * LANES;
        let inputs: [&[u8; LEN]; LANES] =
            std::array::from_fn(|l| (&data[(base + l) * LEN..(base + l + 1) * LEN]).try_into().unwrap());
        hash_lane_group::<LEN>(&inputs, &mut out[base * OUT_LEN..(base + LANES) * OUT_LEN]);
    }
    for i in groups * LANES..n {
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&hash(&data[i * LEN..(i + 1) * LEN]));
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

    /// Known answers from `hashlib.blake2s`, spanning empty, sub-block,
    /// exactly-one-block, block+1 (the case that pins the held-back-buffer
    /// rule) and multi-block inputs.
    #[test]
    fn matches_reference_vectors() {
        for (n, expected) in [
            (
                0usize,
                "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9",
            ),
            (1, "a28ac19d6bcbe2cd1d7de183485768d598e996b07889b9b11f418cb1b4a4fb0d"),
            (63, "de27df0e375d83c49f1af9ca8270f9f2fe7b70bf800fc01672db0e9746021ebf"),
            (64, "5377e4ff957bda4d4535f4879876b71a61056c4cec31e78397c66ec47a86a130"),
            (65, "19b1b26fba093f4a670d8913e1b71cbb2916dfa701018cc6b05785c966593374"),
            (127, "6846f99493436241d0a6f289c9a911b1d0f4860db8f2b5df5295ffd37d03a3c4"),
            (128, "83470c75afa23d90cd7659906e4b47daa278131fbb225241dd37a40fd5355ac7"),
            (192, "8608895acbb0b5581cdfb5e84d11de01f722ab250285a172e8d59f2f67c46110"),
            (256, "080c6da49f3ef891dfbf1abdfe224490e30afbad3a24e4e689fd13e4a13de241"),
            (1024, "72dc5524951b8955c23b7e3e7f51fb9fff71d8650317f3b7d6e8572e78e230a6"),
        ] {
            assert_eq!(hex(&hash(&pattern(n))), expected, "unkeyed, {n} bytes");
        }
    }

    /// Keyed mode, same source. The key block is a full block and counts
    /// toward the counter, which is what these pin.
    #[test]
    fn matches_keyed_reference_vectors() {
        let key: Vec<u8> = (0..32u8).collect();
        for (n, expected) in [
            (
                0usize,
                "48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49",
            ),
            (1, "722ac21d94c3868234e075bb5692678e6460c23466b10b48acf133e6f89f9082"),
            (64, "ce3c22b930e6395797de1e490600d305294ff2e30eb187bb63120e3f5e3fc129"),
            (65, "82e02e62a066f2f3cd7a8a542581cbf441e35cf7a771fc7adb0965d8446b71cb"),
            (100, "6d76c967766118147e79a7528778f3c53125c42b357c86a97834339715a74bcd"),
        ] {
            assert_eq!(hex(&keyed_hash(&key, &pattern(n))), expected, "keyed, {n} bytes");
        }
    }

    /// Any split of the input into `update` calls gives the same digest, and
    /// agrees with the whole-block fast path in [`hash`].
    #[test]
    fn streaming_matches_one_shot() {
        for n in [0usize, 1, 63, 64, 65, 130, 192, 577] {
            let data = pattern(n);
            let want = {
                let mut h = Hasher::new();
                h.update(&data);
                h.finalize()
            };
            assert_eq!(hash(&data), want, "one-shot vs streaming, {n}");
            for split in [1usize, 7, 64, 65] {
                if split > n {
                    continue;
                }
                let mut h = Hasher::new();
                for chunk in data.chunks(split) {
                    h.update(chunk);
                }
                assert_eq!(h.finalize(), want, "{n} bytes in {split}-byte updates");
            }
        }
    }

    /// The transposed batch is byte-identical to the scalar hash per input,
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
