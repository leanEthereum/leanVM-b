//! The VM-native hash primitive: one standard SHA-256 compression with the
//! SHA-256 IV, over exactly one unpadded 64-byte message block.
//!
//! This is deliberately not `SHA256(message)`: the standard hash of a
//! 64-byte message adds a second block containing padding and the bit length.
//! The primitive here is exactly `compress256(SHA256_IV, message)` and thus
//! always costs one compression.

use sha2::digest::{generic_array::GenericArray, typenum::U64};

pub type Block = [u8; 64];
pub type Digest = [u8; 32];

/// Initial chaining value from FIPS 180-4 section 5.3.3.
pub const IV: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

#[inline]
fn state_to_digest(state: [u32; 8]) -> Digest {
    let mut out = [0u8; 32];
    for (dst, word) in out.chunks_exact_mut(4).zip(state) {
        dst.copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// `SHA256_Compress(IV, block)`, including SHA-256's feed-forward addition.
///
/// With the workspace's `target-cpu=native` configuration this dispatches to
/// RustCrypto's ARMv8 SHA2 backend (`sha256h`, `sha256h2`, `sha256su0`, and
/// `sha256su1`) on Apple silicon. The crate retains a runtime software
/// fallback for AArch64 CPUs without the SHA2 extension.
#[inline]
pub fn compress(block: &Block) -> Digest {
    let mut state = IV;
    let block: &GenericArray<u8, U64> = GenericArray::from_slice(block);
    sha2::compress256(&mut state, core::slice::from_ref(block));
    state_to_digest(state)
}

/// Hash many independent blocks. This API is intentionally centralized so
/// architecture-specific multi-buffer implementations can be selected without
/// changing PCS, XMSS, or VM semantics.
#[inline]
pub fn compress_many(blocks: &[Block], out: &mut [Digest]) {
    assert_eq!(blocks.len(), out.len());
    #[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
    {
        return aarch64::compress_many(blocks, out);
    }
    #[cfg(not(all(target_arch = "aarch64", target_feature = "sha2")))]
    {
        for (block, digest) in blocks.iter().zip(out) {
            *digest = compress(block);
        }
    }
}

/// A length-bound byte-string hash constructed exclusively from [`compress`].
///
/// The 32-byte chaining value starts with the total byte length in its first
/// eight little-endian bytes. Input is absorbed 32 bytes at a time as
/// `state <- compress(state || block)`; the final partial block is zero-padded.
/// Callers should prefix a domain string in the input when different protocols
/// share this helper.
pub struct CompressionHasher {
    state: Digest,
    block: [u8; 32],
    used: usize,
    seen: usize,
    total_len: usize,
}

impl CompressionHasher {
    pub fn new(total_len: usize) -> Self {
        let mut state = [0u8; 32];
        state[..8].copy_from_slice(&(total_len as u64).to_le_bytes());
        Self {
            state,
            block: [0u8; 32],
            used: 0,
            seen: 0,
            total_len,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) {
        assert!(self.seen + data.len() <= self.total_len, "compression hash received too many bytes");
        self.seen += data.len();
        while !data.is_empty() {
            let take = (32 - self.used).min(data.len());
            self.block[self.used..self.used + take].copy_from_slice(&data[..take]);
            self.used += take;
            data = &data[take..];
            if self.used == 32 {
                self.absorb_block();
            }
        }
    }

    fn absorb_block(&mut self) {
        let mut input = [0u8; 64];
        input[..32].copy_from_slice(&self.state);
        input[32..].copy_from_slice(&self.block);
        self.state = compress(&input);
        self.block.fill(0);
        self.used = 0;
    }

    pub fn finalize(mut self) -> Digest {
        assert_eq!(self.seen, self.total_len, "compression hash byte count mismatch");
        if self.used != 0 {
            self.absorb_block();
        }
        self.state
    }
}

/// Convenience wrapper around [`CompressionHasher`].
pub fn hash_bytes(data: &[u8]) -> Digest {
    let mut hasher = CompressionHasher::new(data.len());
    hasher.update(data);
    hasher.finalize()
}

// Four independent streams are interleaved to cover the latency of Apple's
// pipelined SHA unit. This is adapted from Flock's measured M-series kernel;
// unlike its full-hash helper, this runs exactly one unpadded block.
#[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
mod aarch64 {
    use super::{Block, Digest, IV, state_to_digest};
    use core::arch::aarch64::*;

    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
        0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
        0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
        0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    #[inline(always)]
    unsafe fn compress4(blocks: [&Block; 4]) -> [Digest; 4] {
        unsafe {
            let iv_abcd = vld1q_u32(IV.as_ptr());
            let iv_efgh = vld1q_u32(IV.as_ptr().add(4));
            let mut abcd = [iv_abcd; 4];
            let mut efgh = [iv_efgh; 4];
            let mut m0 = [vdupq_n_u32(0); 4];
            let mut m1 = [vdupq_n_u32(0); 4];
            let mut m2 = [vdupq_n_u32(0); 4];
            let mut m3 = [vdupq_n_u32(0); 4];
            for i in 0..4 {
                let p = blocks[i].as_ptr();
                m0[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p)));
                m1[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(16))));
                m2[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(32))));
                m3[i] = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(48))));
            }

            macro_rules! rounds4 {
                ($msg:expr, $ki:expr) => {{
                    let kv = vld1q_u32(K.as_ptr().add($ki));
                    for i in 0..4 {
                        let wk = vaddq_u32($msg[i], kv);
                        let old_abcd = abcd[i];
                        abcd[i] = vsha256hq_u32(abcd[i], efgh[i], wk);
                        efgh[i] = vsha256h2q_u32(efgh[i], old_abcd, wk);
                    }
                }};
            }
            macro_rules! schedule {
                ($a:expr, $b:expr, $c:expr, $d:expr) => {
                    for i in 0..4 {
                        $a[i] = vsha256su1q_u32(vsha256su0q_u32($a[i], $b[i]), $c[i], $d[i]);
                    }
                };
            }

            rounds4!(m0, 0);
            rounds4!(m1, 4);
            rounds4!(m2, 8);
            rounds4!(m3, 12);
            for r in 1..4 {
                schedule!(m0, m1, m2, m3);
                schedule!(m1, m2, m3, m0);
                schedule!(m2, m3, m0, m1);
                schedule!(m3, m0, m1, m2);
                rounds4!(m0, 16 * r);
                rounds4!(m1, 16 * r + 4);
                rounds4!(m2, 16 * r + 8);
                rounds4!(m3, 16 * r + 12);
            }

            let mut out = [[0u8; 32]; 4];
            for i in 0..4 {
                let mut state = [0u32; 8];
                vst1q_u32(state.as_mut_ptr(), vaddq_u32(abcd[i], iv_abcd));
                vst1q_u32(state.as_mut_ptr().add(4), vaddq_u32(efgh[i], iv_efgh));
                out[i] = state_to_digest(state);
            }
            out
        }
    }

    pub fn compress_many(blocks: &[Block], out: &mut [Digest]) {
        let groups = blocks.len() / 4;
        for g in 0..groups {
            let i = 4 * g;
            let digests = unsafe { compress4([&blocks[i], &blocks[i + 1], &blocks[i + 2], &blocks[i + 3]]) };
            out[i..i + 4].copy_from_slice(&digests);
        }
        for i in groups * 4..blocks.len() {
            out[i] = super::compress(&blocks[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Computed independently with Python's SHA-256 compression construction:
    // SHA256(64 zero bytes) after its first (message) block, before padding.
    const ZERO_BLOCK: Digest = [
        0xda, 0x56, 0x98, 0xbe, 0x17, 0xb9, 0xb4, 0x69, 0x62, 0x33, 0x57, 0x99, 0x77, 0x9f, 0xbe, 0xca, 0x8c, 0xe5,
        0xd4, 0x91, 0xc0, 0xd2, 0x62, 0x43, 0xba, 0xfe, 0xf9, 0xea, 0x18, 0x37, 0xa9, 0xd8,
    ];

    #[test]
    fn zero_block_vector() {
        assert_eq!(compress(&[0u8; 64]), ZERO_BLOCK);
    }

    #[test]
    fn batch_matches_single() {
        let blocks: Vec<Block> = (0..11)
            .map(|i| std::array::from_fn(|j| (i * 29 + j * 17) as u8))
            .collect();
        let mut got = vec![[0u8; 32]; blocks.len()];
        compress_many(&blocks, &mut got);
        for (block, digest) in blocks.iter().zip(got) {
            assert_eq!(digest, compress(block));
        }
    }

    #[test]
    fn compression_hasher_is_chunking_invariant_and_length_bound() {
        let data: Vec<u8> = (0..93).map(|i| (17 * i + 9) as u8).collect();
        let expected = hash_bytes(&data);
        let mut hasher = CompressionHasher::new(data.len());
        for chunk in data.chunks(7) {
            hasher.update(chunk);
        }
        assert_eq!(hasher.finalize(), expected);
        let mut extended = data;
        extended.push(0);
        assert_ne!(hash_bytes(&extended), expected);
    }
}
