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

/// Single-threaded batched throughput, at every leaf size `pcs::merkle`
/// dispatches.
///
/// On AVX-512, BLAKE3's hand-written multi-input kernel measured 5.6 to 8.3 GB/s
/// on the same shapes and machine. BLAKE2s does ten rounds per 64-byte block
/// against BLAKE3's seven, so 10/7 = 1.43x is the floor a same-quality
/// implementation can reach; this sits at 1.23x to 1.70x of it, median ~1.45x.
///
/// On 4-lane NEON (M4 Max) it is 1.9 to 2.2 GB/s. That backend is bound by the
/// G function's dependency chain rather than by issue width, so its two fixes
/// were latency ones; see `blake2s::LANES`.
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
