//! Micro-benchmark attributing the commit-phase cost difference between the
//! F128 and F64 Ligerito commits: same byte volume, but the K version runs
//! its NTT over twice the elements (1-PMULL muls) and hashes twice the
//! Merkle leaves at half the leaf size.
//!
//! Run with: cargo run --release --bin commit_parts_bench

use std::time::Instant;

use primitives::field::{F64, F128};
use pcs::merkle::merkle_tree;
use pcs::ntt::{AdditiveNttF64, AdditiveNttF128};

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    xs[xs.len() / 2]
}

fn main() {
    const SAMPLES: usize = 5;
    let lanes = 64usize; // 2^log_batch = 2^6

    // Codeword byte volume matching the 2^30-bit witness at rate 1/2:
    // 2^31 bits = 256 MB... keep one size below for speed: 2^28-bit witness
    // gives a 2^29-bit codeword = 64 MB.
    // F128: 2^22 elements; F64: 2^23 elements. Positions = elems / lanes.
    let n128 = 1usize << 22;
    let n64 = 1usize << 23;

    let mut s = 7u64;
    let base128: Vec<F128> = (0..n128)
        .map(|_| F128::new(splitmix64(&mut s), splitmix64(&mut s)))
        .collect();
    let base64: Vec<F64> = (0..n64).map(|_| F64(splitmix64(&mut s))).collect();

    let ntt128 = AdditiveNttF128::standard(26);
    let ntt64 = AdditiveNttF64::standard(26);

    let mut t128 = Vec::new();
    let mut t64 = Vec::new();
    let mut m128 = Vec::new();
    let mut m64 = Vec::new();
    for _ in 0..SAMPLES {
        let mut d = base128.clone();
        let t = Instant::now();
        ntt128.forward_transform_interleaved_from_layer(&mut d, lanes, 1);
        t128.push(t.elapsed().as_secs_f64());

        // Merkle over the F128 codeword: 2^16 leaves of 64*16 = 1024 B.
        let bytes = unsafe {
            core::slice::from_raw_parts(d.as_ptr() as *const u8, d.len() * 16)
        };
        let t = Instant::now();
        let tree = merkle_tree(bytes, n128 / lanes);
        m128.push(t.elapsed().as_secs_f64());
        std::hint::black_box(tree);

        let mut d = base64.clone();
        let t = Instant::now();
        ntt64.forward_transform_interleaved_from_layer(&mut d, lanes, 1);
        t64.push(t.elapsed().as_secs_f64());

        // Merkle over the F64 codeword: 2^17 leaves of 64*8 = 512 B.
        let bytes = unsafe {
            core::slice::from_raw_parts(d.as_ptr() as *const u8, d.len() * 8)
        };
        let t = Instant::now();
        let tree = merkle_tree(bytes, n64 / lanes);
        m64.push(t.elapsed().as_secs_f64());
        std::hint::black_box(tree);
    }

    println!("codeword volume: 64 MB, {lanes} lanes per position");
    println!("NTT    F128 (2^22 elems): {:>8.4}s", median(t128));
    println!("NTT    F64  (2^23 elems): {:>8.4}s", median(t64));
    println!("Merkle F128 (2^16 x 1KB): {:>8.4}s", median(m128));
    println!("Merkle F64  (2^17 x 512B):{:>8.4}s", median(m64));
}
