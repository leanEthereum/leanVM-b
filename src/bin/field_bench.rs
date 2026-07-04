//! Field-arithmetic benchmark: the current field vs. the >128-bit tower.
//!
//!   A. `F128` — GF(2^128), GHASH form (the current field; 128-bit security ceiling)
//!   B. `F192` — GF((2^64)^3), degree-3 tower over GF(2^64)   (192 bits)
//!
//! Run with:
//!   cargo run --release --bin field_bench
//! (`.cargo/config.toml` already applies `-C target-cpu=native`, which enables
//! the aarch64 `aes` feature the PMULL paths need.)
//!
//! What is measured (mul is the headline; everything else is context):
//! - mul latency        — serial dependency chain, one mul feeding the next.
//!   This is what a sumcheck-style fold sees on its critical path.
//! - mul throughput     — (a) 8 independent register-resident chains and
//!   (b) 1024-element array passes; both expose instruction-level parallelism,
//!   the array adds realistic loads/stores.
//! - inner product      — sum of a_i * b_i two ways: fully reduced per term vs
//!   deferred reduction (XOR-accumulate unreduced products, reduce once) —
//!   the shape of the PCS/sumcheck hot loop.
//! - per-implementation variants of mul (schoolbook / Karatsuba / Barrett /
//!   vec2 batch) at both latency and throughput.
//! - add, square, inv   — supporting ops.
//!
//! Methodology: fixed-seed splitmix64 data, 2 warmup runs, median of 7 timed
//! samples per metric, `black_box` fencing on every input/output. Throughput
//! loops use per-index chains (`out[i] *= a[i]`) so no pass can be hoisted.

use std::hint::black_box;
use std::ops::{Add, Mul};
use std::time::Instant;

use flare::field::{F128, F192, F192Unreduced, F256Unreduced};

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

const SAMPLES: usize = 7;
const CHAINS: usize = 8; // independent chains for ILP throughput
const ARR_N: usize = 1024;

/// `--quick` shrinks every loop 64x: a functional smoke test, not a benchmark.
fn quick() -> bool {
    static QUICK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *QUICK.get_or_init(|| std::env::args().any(|a| a == "--quick"))
}

fn scaled(n: u64) -> u64 {
    if quick() { (n >> 6).max(1) } else { n }
}

fn lat_iters() -> u64 {
    scaled(1 << 21) // serial-chain length
}
fn chain_iters() -> u64 {
    scaled(1 << 18)
}
fn arr_passes() -> u64 {
    scaled(1 << 11)
}
fn inner_passes() -> u64 {
    scaled(1 << 11)
}
fn inv_iters() -> u64 {
    scaled(2_048)
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Runs `run` (which performs `ops` field operations) `SAMPLES` times after a
/// warmup and returns the median ns/op.
fn measure(ops: u64, mut run: impl FnMut()) -> f64 {
    run();
    run();
    let mut times: Vec<f64> = (0..SAMPLES)
        .map(|_| {
            let t = Instant::now();
            run();
            t.elapsed().as_secs_f64() * 1e9 / ops as f64
        })
        .collect();
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    times[SAMPLES / 2]
}

// ---------------------------------------------------------------------------
// Field abstraction (only what the benches need)
// ---------------------------------------------------------------------------

trait BenchField: Copy + Add<Output = Self> + Mul<Output = Self> {
    fn rand(s: &mut u64) -> Self;
    fn zero() -> Self;
    fn inv(self) -> Self;
}

impl BenchField for F128 {
    fn rand(s: &mut u64) -> Self {
        F128::new(splitmix64(s), splitmix64(s))
    }
    fn zero() -> Self {
        F128::ZERO
    }
    fn inv(self) -> Self {
        F128::inv(self)
    }
}

impl BenchField for F192 {
    fn rand(s: &mut u64) -> Self {
        F192::new(splitmix64(s), splitmix64(s), splitmix64(s))
    }
    fn zero() -> Self {
        F192::ZERO
    }
    fn inv(self) -> Self {
        F192::inv(self)
    }
}

// ---------------------------------------------------------------------------
// Generic benches
// ---------------------------------------------------------------------------

/// Serial dependency chain of an arbitrary binary op: true latency.
fn lat_chain<T: Copy>(seed: T, op: impl Fn(T) -> T) -> f64 {
    let mut acc = black_box(seed);
    let iters = lat_iters();
    measure(iters, move || {
        let mut a = acc;
        for _ in 0..iters {
            a = op(a);
        }
        acc = black_box(a);
    })
}

/// 8 independent register-resident chains: ILP-limited throughput.
fn tp_chains<T: BenchField>(op: impl Fn(T, T) -> T) -> f64 {
    let mut s = 0xA5A5_0001u64;
    let mut accs = [(); CHAINS].map(|_| T::rand(&mut s));
    let ms = [(); CHAINS].map(|_| T::rand(&mut s));
    let iters = chain_iters();
    measure(iters * CHAINS as u64, move || {
        let mut a = black_box(accs);
        for _ in 0..iters {
            for j in 0..CHAINS {
                a[j] = op(a[j], ms[j]);
            }
        }
        accs = black_box(a);
    })
}

/// Array throughput: 1024 independent per-index chains through memory.
fn tp_array<T: BenchField>(op: impl Fn(T, T) -> T) -> f64 {
    let mut s = 0xA5A5_0002u64;
    let a: Vec<T> = (0..ARR_N).map(|_| T::rand(&mut s)).collect();
    let mut out: Vec<T> = (0..ARR_N).map(|_| T::rand(&mut s)).collect();
    let passes = arr_passes();
    measure(passes * ARR_N as u64, move || {
        for _ in 0..passes {
            for i in 0..ARR_N {
                out[i] = op(out[i], a[i]);
            }
            black_box(&mut out);
        }
    })
}

/// Inner product with per-term full reduction: acc += a[i] * b[i].
fn inner_reduced<T: BenchField>() -> f64 {
    let mut s = 0xA5A5_0003u64;
    let a: Vec<T> = (0..ARR_N).map(|_| T::rand(&mut s)).collect();
    let b: Vec<T> = (0..ARR_N).map(|_| T::rand(&mut s)).collect();
    let passes = inner_passes();
    measure(passes * ARR_N as u64, move || {
        for _ in 0..passes {
            let mut acc = T::zero();
            for i in 0..ARR_N {
                acc = acc + black_box(a[i]) * b[i];
            }
            black_box(acc);
        }
    })
}

/// Inner product with deferred reduction (XOR-accumulate raw products,
/// reduce once). One macro expansion per field: the accumulator types differ.
macro_rules! inner_deferred {
    ($T:ty, $U:ty, $seed:expr) => {{
        let mut s: u64 = $seed;
        let a: Vec<$T> = (0..ARR_N).map(|_| <$T as BenchField>::rand(&mut s)).collect();
        let b: Vec<$T> = (0..ARR_N).map(|_| <$T as BenchField>::rand(&mut s)).collect();
        let passes = inner_passes();
        measure(passes * ARR_N as u64, move || {
            for _ in 0..passes {
                let mut acc = <$U>::ZERO;
                for i in 0..ARR_N {
                    acc ^= black_box(a[i]).mul_unreduced(b[i]);
                }
                black_box(acc.reduce());
            }
        })
    }};
}

fn inv_bench<T: BenchField>() -> f64 {
    let mut s = 0xA5A5_0004u64;
    let m = T::rand(&mut s);
    let mut acc = T::rand(&mut s);
    let iters = inv_iters();
    measure(iters, move || {
        let mut a = black_box(acc);
        for _ in 0..iters {
            a = a.inv() + m;
        }
        acc = black_box(a);
    })
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

struct Row {
    metric: &'static str,
    v: [f64; 2], // [F128, F192], ns/op
}

fn print_headline(rows: &[Row]) {
    println!(
        "\n  {:<26} {:>10} {:>10} {:>11}",
        "metric (ns/op)", "F128", "F192", "F192/F128"
    );
    println!("  {}", "-".repeat(60));
    for r in rows {
        println!(
            "  {:<26} {:>10.2} {:>10.2} {:>10.2}x",
            r.metric,
            r.v[0],
            r.v[1],
            r.v[1] / r.v[0]
        );
    }
}

// ---------------------------------------------------------------------------
// Correctness pre-flight: refuse to print numbers from a broken build.
// ---------------------------------------------------------------------------

fn preflight() {
    let mut s = 0xDEAD_BEEFu64;
    for _ in 0..200 {
        let (a, b) = (F192::rand(&mut s), F192::rand(&mut s));
        assert_eq!(a * b, flare::field::gf2_64x3::software::mul(a, b));
        assert_eq!(a.square(), a * a);
        let (a, b) = (F128::rand(&mut s), F128::rand(&mut s));
        assert_eq!(a * b, flare::field::gf2_128::software::ghash_mul(a, b));
        assert_eq!(a.square(), a * a);
    }
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

fn main() {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    println!("PMULL (aarch64 + aes): ENABLED");
    #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
    println!("PMULL (aarch64 + aes): DISABLED — software fallback; numbers not meaningful!");

    preflight();
    println!("correctness pre-flight: ok");

    println!("\nfields:");
    println!("  A. F128 = GF(2^128)     GHASH poly, 16 B/elem — mul: 4 PMULL + 2 reduce-PMULL");
    println!("  B. F192 = GF((2^64)^3)  y^3+y+1 over x^64+x^4+x^3+x+1, 24 B/elem — mul: 6 PMULL + 3 reduce-PMULL");

    // -- headline: one row per metric, both fields.
    let mut s = 1u64;
    let rows = vec![
        Row {
            metric: "mul latency (chain)",
            v: [
                lat_chain(F128::rand(&mut s), {
                    let m = F128::rand(&mut s);
                    move |a| a * m
                }),
                lat_chain(F192::rand(&mut s), {
                    let m = F192::rand(&mut s);
                    move |a| a * m
                }),
            ],
        },
        Row {
            metric: "mul tput (8 chains)",
            v: [
                tp_chains::<F128>(|a, m| a * m),
                tp_chains::<F192>(|a, m| a * m),
            ],
        },
        Row {
            metric: "mul tput (array 1024)",
            v: [
                tp_array::<F128>(|a, m| a * m),
                tp_array::<F192>(|a, m| a * m),
            ],
        },
        Row {
            metric: "inner prod, reduced",
            v: [
                inner_reduced::<F128>(),
                inner_reduced::<F192>(),
            ],
        },
        Row {
            metric: "inner prod, deferred",
            v: [
                inner_deferred!(F128, F256Unreduced, 0xA5A5_1001),
                inner_deferred!(F192, F192Unreduced, 0xA5A5_1003),
            ],
        },
        Row {
            metric: "square latency (chain)",
            v: [
                lat_chain(F128::rand(&mut s), |a| a.square()),
                lat_chain(F192::rand(&mut s), |a| a.square()),
            ],
        },
        Row {
            metric: "add tput (array 1024)",
            v: [
                tp_array::<F128>(|a, m| a + m),
                tp_array::<F192>(|a, m| a + m),
            ],
        },
        Row {
            metric: "inverse",
            v: [inv_bench::<F128>(), inv_bench::<F192>()],
        },
    ];
    print_headline(&rows);

    // -- per-field mul variants (latency + ILP throughput).
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    variants();

    println!("\nnotes:");
    println!("  - latency = serial dependency chain; tput = independent ops (ILP).");
    println!("  - 'inner prod, deferred' XOR-accumulates unreduced products and reduces once");
    println!("    (accumulator: F128 32 B, F192 80 B) — the sumcheck hot-loop shape.");
    println!("  - inverse is Fermat (square-and-multiply); setup-only, shown for completeness.");
}

// ---------------------------------------------------------------------------
// Variant benches (NEON only)
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn variants() {
    use flare::field::gf2_64x3::aarch64 as t192;
    use flare::field::gf2_128::aarch64 as g128;

    fn report<T: BenchField>(name: &str, op: impl Fn(T, T) -> T + Copy) {
        let mut s = 7u64;
        let m = T::rand(&mut s);
        let lat = lat_chain(T::rand(&mut s), move |a| op(a, m));
        let tput = tp_chains::<T>(op);
        println!("  {:<34} {:>10.2} {:>12.2}", name, lat, tput);
    }

    println!(
        "\n  {:<34} {:>10} {:>12}",
        "mul variant (ns/op)", "latency", "tput(8ch)"
    );
    println!("  {}", "-".repeat(59));

    // SAFETY (all closures below): variants() is only compiled when the aes
    // target feature is statically enabled, satisfying each intrinsic wrapper's
    // only precondition.
    report::<F128>("F128 binius 2-stage (default)", |a, b| unsafe {
        g128::ghash_mul_binius(a, b)
    });
    report::<F128>("F128 schoolbook", |a, b| unsafe { g128::ghash_mul_schoolbook(a, b) });
    report::<F128>("F128 karatsuba", |a, b| unsafe { g128::ghash_mul_karatsuba(a, b) });
    report::<F128>("F128 karatsuba+barrett", |a, b| unsafe {
        g128::ghash_mul_karatsuba_barrett(a, b)
    });
    // vec2 batches two muls per call; harness sees one op = one lane-pair.
    {
        let mut s = 7u64;
        let m0 = F128::rand(&mut s);
        let m1 = F128::rand(&mut s);
        let lat = {
            let seed = [F128::rand(&mut s), F128::rand(&mut s)];
            // 2 muls per chain step.
            let ns2 = lat_chain(seed, move |a| unsafe { g128::ghash_mul_vec2_neon(a, [m0, m1]) });
            ns2 / 2.0
        };
        let tput = {
            let mut s = 8u64;
            let mut accs: Vec<[F128; 2]> = (0..CHAINS / 2)
                .map(|_| [F128::rand(&mut s), F128::rand(&mut s)])
                .collect();
            let ms: Vec<[F128; 2]> = (0..CHAINS / 2)
                .map(|_| [F128::rand(&mut s), F128::rand(&mut s)])
                .collect();
            let iters = chain_iters();
            measure(iters * CHAINS as u64, move || {
                let mut a = black_box(accs.clone());
                for _ in 0..iters {
                    for j in 0..CHAINS / 2 {
                        a[j] = unsafe { g128::ghash_mul_vec2_neon(a[j], ms[j]) };
                    }
                }
                accs = black_box(a);
            })
        };
        println!("  {:<34} {:>10.2} {:>12.2}", "F128 vec2 batch (per mul)", lat, tput);
    }

    report::<F192>("F192 karatsuba-6 (default)", |a, b| unsafe {
        t192::mul_karatsuba(a, b)
    });
    report::<F192>("F192 schoolbook-9", |a, b| unsafe { t192::mul_schoolbook(a, b) });
    report::<F192>("F192 karatsuba, scalar reduce", |a, b| unsafe {
        t192::mul_karatsuba_scalar_reduce(a, b)
    });
}
