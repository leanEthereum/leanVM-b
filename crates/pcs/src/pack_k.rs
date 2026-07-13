// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Bit-witness packing into K = F_{2^64} for the 64-bit transition PCS.
//!
//! Mirror of [`super::pack`] at half the stride: the witness
//! `z : {0,1}^m -> {0,1}` is laid out as a flat 2^m-length bool array, and
//! packing groups the **first** `LOG_PACKING_K = 6` boolean coordinates into
//! one F_{2^64} element, leaving `2^(m-6)` packed words indexed by the
//! remaining m-6 outer coords.
//!
//! Layout convention: for packed index `i_rest` and bit position `i`,
//! ```text
//!     bit i of out[i_rest]  ==  z[i_rest * 64 + i]
//! ```
//! where "bit i of an F_{2^64} element" is the i-th coordinate of its
//! polynomial-basis decomposition (bit i of the u64, little-endian).
//!
//! This matches the packing basis of the generalized ring-switching reduction
//! ([`super::ring_switch_k`]): `s_hat_v[i]` is the MLE of the i-th bit-slice
//! of the witness, and the i-th bit-slice is exactly bit i of every word.

use primitives::field::F64;

/// `log_2` of the packing width. F_{2^64} holds 64 bits = 2^6.
pub const LOG_PACKING_K: usize = 6;

/// Packing width (number of bits per F_{2^64} element).
pub const PACKING_WIDTH_K: usize = 1 << LOG_PACKING_K;

/// Pack a Boolean witness `z` of length `2^m` into `2^(m - LOG_PACKING_K)`
/// F_{2^64} elements.
///
/// See module docs for the layout convention.
///
/// # Panics
///
/// - if `z.len() != 1 << m`
/// - if `m < LOG_PACKING_K`
pub fn pack_witness_k(z: &[bool], m: usize) -> Vec<F64> {
    use rayon::prelude::*;
    assert_eq!(z.len(), 1usize << m, "z length must be 2^m");
    assert!(
        m >= LOG_PACKING_K,
        "witness too small to pack: m = {m} < LOG_PACKING_K = {LOG_PACKING_K}",
    );
    let n_packed = 1usize << (m - LOG_PACKING_K);

    // `bool` is guaranteed 1 byte holding 0x00/0x01, so 8 bools read as one
    // little-endian u64 pack to an LSB-first byte with one multiply:
    // byte 7 of `x * 0x0102040810204080` is the sum of b_r * 2^r (each lower
    // product byte sums distinct powers of two <= 0xFE, so nothing carries
    // into byte 7). Same trick as `pack::pack_witness`.
    // SAFETY: same length, and any &[bool] is a valid &[u8].
    let bytes: &[u8] = unsafe { core::slice::from_raw_parts(z.as_ptr() as *const u8, z.len()) };
    #[inline]
    fn pack64(b: &[u8]) -> u64 {
        let mut w = 0u64;
        for (i, ch) in b.chunks_exact(8).enumerate() {
            let x = u64::from_le_bytes(ch.try_into().unwrap());
            w |= (x.wrapping_mul(0x0102_0408_1020_4080) >> 56) << (8 * i);
        }
        w
    }
    let one = |i_rest: usize| {
        let base = i_rest << LOG_PACKING_K;
        F64(pack64(&bytes[base..base + PACKING_WIDTH_K]))
    };
    // Parallel for real witnesses; sequential below the dispatch-overhead
    // floor (tiny test instances).
    if n_packed >= (1 << 12) {
        (0..n_packed).into_par_iter().map(one).collect()
    } else {
        (0..n_packed).map(one).collect()
    }
}

/// Inverse of [`pack_witness_k`]: unpack F_{2^64} elements back to a Boolean
/// witness of length `2^m`.
///
/// Round-trips with [`pack_witness_k`] by construction.
pub fn unpack_witness_k(packed: &[F64], m: usize) -> Vec<bool> {
    let n_packed = 1usize << (m - LOG_PACKING_K);
    assert_eq!(packed.len(), n_packed, "packed length must be 2^(m - LOG_PACKING_K)");
    let mut out = vec![false; 1usize << m];
    for (i_rest, elem) in packed.iter().enumerate() {
        let base = i_rest << LOG_PACKING_K;
        for r in 0..PACKING_WIDTH_K {
            out[base | r] = (elem.0 >> r) & 1 == 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_bits(m: usize, seed: u64) -> Vec<bool> {
        let mut s = seed;
        (0..1usize << m).map(|_| splitmix64(&mut s) & 1 == 1).collect()
    }

    #[test]
    fn roundtrip() {
        for (m, seed) in [(6usize, 1u64), (7, 2), (10, 3), (13, 4)] {
            let z = rand_bits(m, seed);
            let packed = pack_witness_k(&z, m);
            assert_eq!(packed.len(), 1 << (m - LOG_PACKING_K));
            assert_eq!(unpack_witness_k(&packed, m), z, "roundtrip failed at m={m}");
        }
    }

    /// Bit-level layout: bit i of word i_rest is z[i_rest * 64 + i].
    #[test]
    fn bit_layout() {
        let m = 9;
        let z = rand_bits(m, 5);
        let packed = pack_witness_k(&z, m);
        for i_rest in 0..packed.len() {
            for i in 0..PACKING_WIDTH_K {
                assert_eq!(
                    (packed[i_rest].0 >> i) & 1 == 1,
                    z[(i_rest << LOG_PACKING_K) | i],
                    "bit ({i_rest}, {i}) disagrees with the flat layout"
                );
            }
        }
    }

    /// Agreement with the F128 packing at the bit level: the K packing is the
    /// F128 packing split at the 64-bit boundary, so word 2j is the lo half
    /// and word 2j+1 the hi half of F128 word j.
    #[test]
    fn agrees_with_f128_packing() {
        let m = 10;
        let z = rand_bits(m, 6);
        let packed_k = pack_witness_k(&z, m);
        let packed_128 = crate::pack::pack_witness(&z, m);
        assert_eq!(packed_k.len(), 2 * packed_128.len());
        for (j, w) in packed_128.iter().enumerate() {
            assert_eq!(packed_k[2 * j].0, w.lo, "lo half mismatch at {j}");
            assert_eq!(packed_k[2 * j + 1].0, w.hi, "hi half mismatch at {j}");
        }
    }
}
