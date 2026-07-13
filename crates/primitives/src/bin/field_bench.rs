//! Field-arithmetic benchmark: GF(2^128) in its two representations.
//!
//!   A. `F128`  — GF(2^128), GHASH polynomial basis (main's field)
//!   B. `F128T` — GF((2^64)^2), degree-2 tower over GF(2^64) (the 64-bit
//!      design's challenge field E)
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
//! - inner product      — acc += a_i * b_i, reduced per term — the shape of
//!   the PCS/sumcheck hot loop.
//! - add, square, inv   — supporting ops.
//!
//! Methodology: fixed-seed splitmix64 data, 2 warmup runs, median of 7 timed
//! samples per metric, `black_box` fencing on every input/output. Throughput
//! loops use per-index chains (`out[i] *= a[i]`) so no pass can be hoisted.

use std::hint::black_box;
use std::ops::{Add, Mul};
use std::time::Instant;

use primitives::field::{F128, F128T, F128TUnreduced, F256Unreduced, ghash_to_tower};

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

impl BenchField for F128T {
    fn rand(s: &mut u64) -> Self {
        F128T::new(splitmix64(s), splitmix64(s))
    }
    fn zero() -> Self {
        F128T::ZERO
    }
    fn inv(self) -> Self {
        F128T::inv(self)
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

/// Inner product with deferred reduction: XOR-accumulate unreduced products,
/// reduce once per pass. One macro expansion per field (the accumulator types
/// differ: F256Unreduced for GHASH, F128TUnreduced for the tower).
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
// Correctness pre-flight: refuse to print numbers from a broken build.
// ---------------------------------------------------------------------------

fn preflight() {
    let mut s = 0xDEAD_BEEFu64;
    for _ in 0..200 {
        let (a, b) = (F128::rand(&mut s), F128::rand(&mut s));
        assert_eq!(a * b, primitives::field::gf2_128::software::ghash_mul(a, b));
        assert_eq!(a.square(), a * a);
        // The two representations are the SAME field: the explicit isomorphism
        // must carry GHASH products to tower products.
        let (ta, tb) = (ghash_to_tower(a), ghash_to_tower(b));
        assert_eq!(ghash_to_tower(a * b), ta * tb);
        assert_eq!(ta.square(), ta * ta);
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

    println!("\nfields (two representations of GF(2^128)):");
    println!("  A. F128  = GF(2^128)     GHASH poly, one 256-bit product + one sparse fold");
    println!("  B. F128T = GF((2^64)^2)  y^2+y+x^61 over x^64+x^4+x^3+x+1, per-limb folds");

    let mut s = 1u64;
    let rows: Vec<(&str, [f64; 2])> = vec![
        (
            "mul latency (chain)",
            [
                lat_chain(F128::rand(&mut s), {
                    let m = F128::rand(&mut s);
                    move |a| a * m
                }),
                lat_chain(F128T::rand(&mut s), {
                    let m = F128T::rand(&mut s);
                    move |a| a * m
                }),
            ],
        ),
        (
            "mul tput (8 chains)",
            [tp_chains::<F128>(|a, m| a * m), tp_chains::<F128T>(|a, m| a * m)],
        ),
        (
            "mul tput (array 1024)",
            [tp_array::<F128>(|a, m| a * m), tp_array::<F128T>(|a, m| a * m)],
        ),
        (
            "inner prod, reduced",
            [inner_reduced::<F128>(), inner_reduced::<F128T>()],
        ),
        (
            "inner prod, deferred",
            [
                inner_deferred!(F128, F256Unreduced, 0xA5A5_1001),
                inner_deferred!(F128T, F128TUnreduced, 0xA5A5_1002),
            ],
        ),
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        (
            "inner prod, NEON kernel",
            [
                f64::NAN, // no GHASH equivalent wired here; tower-only kernel
                {
                    let mut s = 0xA5A5_1004u64;
                    let a: Vec<F128T> = (0..ARR_N).map(|_| F128T::rand(&mut s)).collect();
                    let b: Vec<F128T> = (0..ARR_N).map(|_| F128T::rand(&mut s)).collect();
                    let passes = inner_passes();
                    measure(passes * ARR_N as u64, move || {
                        for _ in 0..passes {
                            // SAFETY: aes is statically enabled (cfg above).
                            black_box(unsafe {
                                primitives::field::tower_f128::aarch64::inner_unreduced_neon(
                                    black_box(&a),
                                    black_box(&b),
                                )
                            });
                        }
                    })
                },
            ],
        ),
        (
            "square latency (chain)",
            [
                lat_chain(F128::rand(&mut s), |a| a.square()),
                lat_chain(F128T::rand(&mut s), |a| a.square()),
            ],
        ),
        (
            "add tput (array 1024)",
            [tp_array::<F128>(|a, m| a + m), tp_array::<F128T>(|a, m| a + m)],
        ),
        ("inverse", [inv_bench::<F128>(), inv_bench::<F128T>()]),
    ];

    println!(
        "\n  {:<26} {:>10} {:>10} {:>12}",
        "metric (ns/op)", "F128", "F128T", "F128T/F128"
    );
    println!("  {}", "-".repeat(62));
    for (metric, v) in &rows {
        let cell = |x: f64| if x.is_nan() { "-".to_string() } else { format!("{x:.2}") };
        let ratio = if v[0].is_nan() || v[1].is_nan() {
            "-".to_string()
        } else {
            format!("{:.2}x", v[1] / v[0])
        };
        println!("  {:<26} {:>10} {:>10} {:>12}", metric, cell(v[0]), cell(v[1]), ratio);
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    if std::env::args().any(|a| a == "--variants") {
        variants();
    }

    println!("\nnotes:");
    println!("  - latency = serial dependency chain; tput = independent ops (ILP).");
    println!("  - 'inner prod, deferred' XOR-accumulates unreduced products and reduces once");
    println!("    (accumulator: F128 32 B, F128T 48 B) — the sumcheck hot-loop shape.");
    println!("  - inverse is Fermat (square-and-multiply); setup-only, shown for completeness.");
    println!("  - pass --variants for the per-kernel F128T mul comparison.");
}

/// Per-kernel F128T mul variants (NEON only), with the GHASH default as the
/// reference row. `--variants` only.
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn variants() {
    use primitives::field::gf2_128::aarch64 as g128;
    use primitives::field::tower_f128::aarch64 as t128;

    fn report<T: BenchField>(name: &str, op: impl Fn(T, T) -> T + Copy) {
        let mut s = 7u64;
        let m = T::rand(&mut s);
        let lat = lat_chain(T::rand(&mut s), move |a| op(a, m));
        let tput = tp_chains::<T>(op);
        let arr = tp_array::<T>(op);
        println!("  {:<38} {:>8.2} {:>10.2} {:>10.2}", name, lat, tput, arr);
    }

    println!(
        "\n  {:<38} {:>8} {:>10} {:>10}",
        "F128T mul variant (ns/op)", "latency", "tput(8ch)", "tput(arr)"
    );
    println!("  {}", "-".repeat(70));
    // SAFETY (all closures below): variants() is only compiled when the aes
    // target feature is statically enabled, satisfying each intrinsic
    // wrapper's only precondition.
    report::<F128>("F128 ghash binius (reference)", |a, b| unsafe {
        g128::ghash_mul_binius(a, b)
    });
    report::<F128T>("karatsuba parallel-fold (default)", |a, b| unsafe {
        t128::mul_neon(a, b)
    });
    report::<F128T>("karatsuba shift-tail", |a, b| unsafe { t128::mul_shift_tail(a, b) });
    report::<F128T>("karatsuba serial-fold", |a, b| unsafe { t128::mul_serial_fold(a, b) });
    report::<F128T>("karatsuba vector-resident", |a, b| unsafe {
        t128::mul_karatsuba_vec(a, b)
    });
    report::<F128T>("schoolbook vector-resident", |a, b| unsafe {
        t128::mul_schoolbook(a, b)
    });
    report::<F128T>("schoolbook vec shift-tail", |a, b| unsafe {
        t128::mul_schoolbook_shift_tail(a, b)
    });
}
