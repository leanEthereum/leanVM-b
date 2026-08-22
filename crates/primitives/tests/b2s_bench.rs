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

/// cargo test --release -p primitives --test b2s_bench multithreaded_throughput -- --ignored --nocapture
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
                primitives::blake2s::hash_many::<64>(d, sub);
                std::hint::black_box(&mut *sub);
            }
        });
    });
    println!(
        "64B -> 32B, {} threads, LANES={}: {:.0} Mhash/s",
        parallel::num_threads(),
        primitives::blake2s::LANES,
        (TASKS * K * ITERS) as f64 / s / 1e6,
    );
}

/// Single-threaded batched throughput, at every leaf size `pcs::merkle`
/// dispatches.
///
/// The two backends run into different limits: AVX-512 is bound by issue width,
/// so its fixes were instruction-count ones, while NEON is bound by the G
/// function's dependency chain and needed latency ones. See `blake2s::LANES`.
#[test]
#[ignore = "manual throughput measurement"]
fn batched_throughput() {
    fn run<const LEN: usize>(n: usize) {
        let data: Vec<u8> = (0..n * LEN).map(|i| (i & 0xff) as u8).collect();
        let mut out = vec![0u8; n * 32];
        let s = time(20, || primitives::blake2s::hash_many::<LEN>(&data, &mut out));
        println!("  LEN={LEN:<5} {:>6.0} MB/s", (n * LEN) as f64 / 1e6 / s);
    }
    println!("batched, single-threaded, LANES={}", primitives::blake2s::LANES);
    run::<64>(1 << 18);
    run::<128>(1 << 17);
    run::<192>(1 << 16);
    run::<256>(1 << 16);
    run::<384>(1 << 15);
    run::<512>(1 << 15);
    run::<768>(1 << 14);
    run::<1024>(1 << 14);
}
