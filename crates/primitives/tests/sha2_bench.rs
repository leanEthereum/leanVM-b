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

/// cargo test --release -p primitives --test sha2_bench multithreaded_throughput -- --ignored --nocapture
#[test]
#[ignore = "manual throughput measurement"]
fn multithreaded_throughput() {
    const K: usize = 1 << 10; // hashes per call: 96 KiB in+out per task, cache-resident
    const ITERS: usize = 1 << 5; // rehash rounds per task per dispatch
    const TASKS: usize = 512;

    let data: Vec<u8> = (0..TASKS * K * 64).map(|i| (i & 0xff) as u8).collect();
    let mut out = vec![0u8; TASKS * K * 32];
    let s = time(2, || {
        parallel::chunks_mut(&mut out, K * 32, |i, sub| {
            let d = &data[i * K * 64..i * K * 64 + sub.len() * 2];
            for _ in 0..ITERS {
                primitives::sha2::hash_many::<64>(d, sub);
                std::hint::black_box(&mut *sub);
            }
        });
    });
    println!(
        "64B -> 32B, {} threads, LANES={}: {:.0} Mhash/s",
        parallel::num_threads(),
        primitives::sha2::LANES,
        (TASKS * K * ITERS) as f64 / s / 1e6,
    );
}

/// Single-threaded batched `sha2_eth` throughput, at every leaf size
/// `pcs::merkle` dispatches.
///
/// Two shapes of backend answer this, and they run into different limits. On
/// x86-64 it is lane transposition, sixteen independent inputs per AVX-512
/// register, bound by issue width. On aarch64 it is the crypto extension, four
/// chains interleaved to cover `sha256h`'s latency. `sha2::LANES` reports the
/// group size either way.
#[test]
#[ignore = "manual throughput measurement"]
fn batched_throughput() {
    fn run<const LEN: usize>(n: usize) {
        let data: Vec<u8> = (0..n * LEN).map(|i| (i & 0xff) as u8).collect();
        let mut out = vec![0u8; n * 32];
        let s = time(20, || primitives::sha2::hash_many::<LEN>(&data, &mut out));
        println!("  LEN={LEN:<5} {:>6.0} MB/s", (n * LEN) as f64 / 1e6 / s);
    }
    println!("batched, single-threaded, LANES={}", primitives::sha2::LANES);
    run::<64>(1 << 18);
    run::<128>(1 << 17);
    run::<192>(1 << 16);
    run::<256>(1 << 16);
    run::<384>(1 << 15);
    run::<512>(1 << 15);
    run::<768>(1 << 14);
    run::<1024>(1 << 14);
}

/// Single-threaded SERIAL throughput: one compression at a time, which is what
/// the Fiat-Shamir chain, PoW grinding and every verifier Merkle path do.
///
/// This exists because its absence hid an 11x regression. `sha2_eth` derives
/// its starting chaining value from the message length, and `iv_for_len` is a
/// `const fn`, so a call with a RUNTIME length silently ran a second, portable
/// compression per hash. `hash_block` and `sha2::iv_at` are the fix, and the
/// three numbers below are what says so: `hash_block` must sit on top of
/// `compress`, and `hash` at 64 bytes must match it.
#[test]
#[ignore = "manual throughput measurement"]
fn serial_throughput() {
    const N: usize = 1 << 18;
    let block: [u8; 64] = std::array::from_fn(|i| (i * 7 + 1) as u8);

    let mut h = primitives::sha2::IV_64;
    let m: [u32; 16] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x9E37_79B9));
    let s = time(N, || h = primitives::sha2::compress(std::hint::black_box(h), m));
    println!("  compress            {:>7.1} ns/op", s * 1e9);
    std::hint::black_box(h);

    let s = time(N, || {
        std::hint::black_box(primitives::sha2::hash_block(std::hint::black_box(&block)));
    });
    println!("  hash_block (64 B)   {:>7.1} ns/op", s * 1e9);

    for len in [64usize, 96, 704] {
        let data: Vec<u8> = (0..len).map(|i| (i * 7 + 1) as u8).collect();
        let s = time(N, || {
            std::hint::black_box(primitives::sha2::hash(std::hint::black_box(&data)));
        });
        println!("  hash ({len:>3} B)        {:>7.1} ns/op", s * 1e9);
    }
}
