// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Pack each 64 consecutive witness bits into one `F64`, least significant bit first.

use primitives::field::F64;

/// `log_2` of the packing width. F_{2^64} holds 64 bits = 2^6.
pub const LOG_PACKING: usize = 6;

/// Packing width (number of bits per F_{2^64} element).
pub const PACKING_WIDTH: usize = 1 << LOG_PACKING;

/// Pack a Boolean witness `z` of length `2^m` into `2^(m - LOG_PACKING)`
/// F_{2^64} elements.
///
/// See module docs for the layout convention.
///
/// # Panics
///
/// - if `z.len() != 1 << m`
/// - if `m < LOG_PACKING`
pub fn pack_witness(witness: &[bool], log_size: usize) -> Vec<F64> {
    assert_eq!(witness.len(), 1usize << log_size, "witness length must be 2^log_size");
    assert!(
        log_size >= LOG_PACKING,
        "witness too small to pack: log_size = {log_size} < LOG_PACKING = {LOG_PACKING}",
    );
    let packed_len = 1usize << (log_size - LOG_PACKING);

    // `bool` is guaranteed 1 byte holding 0x00/0x01, so 8 bools read as one
    // little-endian u64 pack to an LSB-first byte with one multiply:
    // byte 7 of `x * 0x0102040810204080` is the sum of b_r * 2^r (each lower
    // product byte sums distinct powers of two <= 0xFE, so nothing carries
    // into byte 7).
    // SAFETY: same length, and any &[bool] is a valid &[u8].
    let bytes: &[u8] = unsafe { core::slice::from_raw_parts(witness.as_ptr().cast(), witness.len()) };
    #[inline]
    fn pack64(bytes: &[u8]) -> u64 {
        let mut packed = 0u64;
        for (index, chunk) in bytes.as_chunks::<8>().0.iter().enumerate() {
            let word = u64::from_le_bytes(*chunk);
            packed |= (word.wrapping_mul(0x0102_0408_1020_4080) >> 56) << (8 * index);
        }
        packed
    }
    let pack_one = |index: usize| {
        let base = index << LOG_PACKING;
        F64(pack64(&bytes[base..base + PACKING_WIDTH]))
    };
    // Parallel for real witnesses; sequential below the dispatch-overhead
    // floor (tiny test instances).
    if packed_len >= (1 << 12) {
        parallel::map_collect(packed_len, pack_one)
    } else {
        (0..packed_len).map(pack_one).collect()
    }
}

/// Describes zero padding within each logical witness block.
#[derive(Clone, Copy, Debug)]
pub struct PaddingSpec {
    pub k_log: usize,
    pub useful_bits_per_block: usize,
}

impl PaddingSpec {
    /// Treat every bit as useful.
    pub fn dense(m: usize) -> Self {
        Self {
            k_log: m,
            useful_bits_per_block: 1usize << m,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_rng::Rng;

    fn rand_bits(m: usize, seed: u64) -> Vec<bool> {
        Rng::new(seed).bits(1usize << m)
    }

    #[test]
    fn bit_layout() {
        let m = 9;
        let z = rand_bits(m, 5);
        let packed = pack_witness(&z, m);
        for i_rest in 0..packed.len() {
            for i in 0..PACKING_WIDTH {
                assert_eq!(
                    (packed[i_rest].0 >> i) & 1 == 1,
                    z[(i_rest << LOG_PACKING) | i],
                    "bit ({i_rest}, {i}) disagrees with the flat layout"
                );
            }
        }
    }
}
