//! Native SHA3-256 throughput.
//!
//! A permutation absorbs up to `RATE = 136` bytes, so hashes per second and
//! bytes per second say different things and both are printed: the leaf-size
//! choice wants the second one.

use std::time::Instant;

/// Median of `PASSES` timed passes, with a cooldown between them: the machine
/// this runs on is not necessarily idle, so a single pass is not a measurement.
const PASSES: usize = 5;
const COOLDOWN: std::time::Duration = std::time::Duration::from_millis(300);

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

fn time(reps: usize, mut f: impl FnMut()) -> f64 {
    f();
    let mut samples = Vec::with_capacity(PASSES);
    for _ in 0..PASSES {
        let t = Instant::now();
        for _ in 0..reps {
            f();
        }
        samples.push(t.elapsed().as_secs_f64() / reps as f64);
        std::thread::sleep(COOLDOWN);
    }
    median(samples)
}

/// cargo test --release -p primitives --test sha3_bench multithreaded_throughput -- --ignored --nocapture
#[test]
#[ignore = "manual throughput measurement"]
fn multithreaded_throughput() {
    const K: usize = 1 << 10; // hashes per call, kept cache-resident
    const ITERS: usize = 1 << 5;
    const TASKS: usize = 512;

    let data: Vec<u8> = (0..TASKS * K * 64).map(|i| (i & 0xff) as u8).collect();
    let mut out = vec![0u8; TASKS * K * 32];
    let s = time(2, || {
        parallel::chunks_mut(&mut out, K * 32, |i, sub| {
            let d = &data[i * K * 64..i * K * 64 + sub.len() * 2];
            for _ in 0..ITERS {
                primitives::sha3::hash_many::<64>(d, sub);
                std::hint::black_box(&mut *sub);
            }
        });
    });
    println!(
        "64B -> 32B, {} threads, LANES={}: {:.0} Mhash/s",
        parallel::num_threads(),
        primitives::sha3::LANES,
        (TASKS * K * ITERS) as f64 / s / 1e6,
    );
}

/// Single-threaded batched throughput at each leaf size `pcs::merkle` may
/// dispatch. `RATE` is the interesting boundary: everything up to it is one
/// permutation, and one byte past it is two.
#[test]
#[ignore = "manual throughput measurement"]
fn batched_throughput() {
    use primitives::sha3::RATE;
    const N: usize = 1 << 12;
    for len in [32usize, 64, 128, RATE, RATE + 1, 2 * RATE, 512, 1024] {
        let data: Vec<u8> = (0..N * len).map(|i| (i & 0xff) as u8).collect();
        let mut out = vec![0u8; N * 32];
        let s = time(8, || {
            primitives::sha3::hash_many_dyn(&data, len, &mut out);
            std::hint::black_box(&mut out);
        });
        let perms = len / RATE + 1;
        println!(
            "{len:5} B -> 32B, {perms} perm(s): {:8.1} Mhash/s   {:7.2} GiB/s",
            N as f64 / s / 1e6,
            (N * len) as f64 / s / (1u64 << 30) as f64,
        );
    }
}

/// The lone-hash path, which is the scalar permutation even where the batched
/// path is vectorized. This is what the Fiat-Shamir chain and every one-off
/// hash actually run.
#[test]
#[ignore = "manual throughput measurement"]
fn serial_throughput() {
    let block = [0xa5u8; 64];
    let s = time(1 << 12, || {
        std::hint::black_box(primitives::sha3::hash_block(std::hint::black_box(&block)));
    });
    println!("64B -> 32B, serial: {:.1} Mhash/s", 1.0 / s / 1e6);

    let mut state = [0u64; primitives::sha3::STATE_LANES];
    let s = time(1 << 12, || {
        primitives::sha3::permute(std::hint::black_box(&mut state));
    });
    println!("Keccak-f[1600], serial: {:.1} Mperm/s", 1.0 / s / 1e6);
}
