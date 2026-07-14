//! Noise-robust comparator for the batched inner-product kernels.
//!
//! Picking the fastest kernel from a single timed pass is unreliable: a
//! background task or a scheduler tick inflates whichever method happened to be
//! running. This harness is built so the ranking survives that noise:
//!
//!   * **Interleave.** Every round runs *all* methods once, back to back, so a
//!     transient slowdown lands on whatever method is executing at that instant,
//!     not on a fixed one. The method order rotates each round so none keeps a
//!     first/last position advantage.
//!   * **Rank by the minimum.** Noise can only *add* time, never subtract it, so
//!     the smallest time a method ever posts is its cleanest estimate of true
//!     speed. The winner is the lowest min; the median and the per-round
//!     win-count are shown as corroboration.
//!   * **Right-sized samples.** Each timed sample repeats the inner product
//!     `INNER` times (~tens of µs) — long enough that the ~40 ns timer floor is
//!     negligible, short enough to usually fit between scheduler ticks.
//!
//! Two backends:
//!   * **aarch64 (PMULL):** the schoolbook-vs-Karatsuba bank-count sweep the
//!     M-series ranking was derived from.
//!   * **x86_64 (AVX-512 VPCLMULQDQ):** scalar-deferred (the `field_bench`
//!     baseline) vs the 4-wide batched Karatsuba/schoolbook kernels, for BOTH
//!     towers — so the x86 head-to-head (does binius still lose the deferred
//!     inner product? does schoolbook still beat Karatsuba?) is answerable.
//!
//! Run: `cargo run --release -p primitives --bin inner_bench`
//! (`--quick` shrinks the round count for a smoke check.)

use std::hint::black_box;
use std::time::Instant;

const N: usize = 1024; // inner-product length
const INNER: u64 = 64; // inner products per timed sample
const ROUNDS: usize = 400; // interleaved rounds

#[allow(dead_code)]
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Interleaved, min-ranked comparison of inner-product kernels over one field.
/// All methods must return the reference value (method 0) before any is timed.
/// Prints the ranked table and returns the winner's `(name, min ns/term)`.
#[allow(dead_code)]
fn compare<F: Copy + PartialEq + core::fmt::Debug>(
    title: &str,
    a: &[F],
    b: &[F],
    methods: &[(&str, unsafe fn(&[F], &[F]) -> F)],
    rounds: usize,
) -> (String, f64) {
    let m = methods.len();

    // Correctness: every method must equal the reference before it is timed.
    let reference = unsafe { methods[0].1(a, b) };
    for (name, f) in methods {
        assert_eq!(unsafe { f(a, b) }, reference, "{title}: {name} disagrees with reference");
    }

    // Warm up each method (page-in, branch predictor, frequency ramp).
    for (_, f) in methods {
        for _ in 0..64 {
            black_box(unsafe { f(black_box(a), black_box(b)) });
        }
    }

    let ops = INNER * a.len() as u64;
    let sample = |f: unsafe fn(&[F], &[F]) -> F| -> f64 {
        let t0 = Instant::now();
        for _ in 0..INNER {
            black_box(unsafe { f(black_box(a), black_box(b)) });
        }
        t0.elapsed().as_secs_f64() * 1e9 / ops as f64
    };

    let mut samples: Vec<Vec<f64>> = vec![Vec::with_capacity(rounds); m];
    let mut wins = vec![0usize; m];
    for r in 0..rounds {
        // Rotate the visiting order so no method keeps a fixed slot.
        let mut round: Vec<f64> = vec![0.0; m];
        for off in 0..m {
            let idx = (r + off) % m;
            round[idx] = sample(methods[idx].1);
        }
        for i in 0..m {
            samples[i].push(round[i]);
        }
        let win = (0..m).min_by(|&x, &y| round[x].partial_cmp(&round[y]).unwrap()).unwrap();
        wins[win] += 1;
    }

    struct Stat {
        name: String,
        min: f64,
        median: f64,
        wins: usize,
    }
    let mut stats: Vec<Stat> = (0..m)
        .map(|i| {
            let mut v = samples[i].clone();
            v.sort_by(|x, y| x.partial_cmp(y).unwrap());
            Stat {
                name: methods[i].0.to_string(),
                min: v[0],
                median: v[v.len() / 2],
                wins: wins[i],
            }
        })
        .collect();
    stats.sort_by(|x, y| x.min.partial_cmp(&y.min).unwrap());

    let best = stats[0].min;
    let best_name = stats[0].name.clone();
    println!("\n{title} — {rounds} rounds, ranked by MIN ns/term (noise only adds time):\n");
    println!("  {:<32} {:>9} {:>9} {:>9} {:>8}", "method", "min", "median", "speedup", "wins");
    println!("  {}", "-".repeat(72));
    for (rank, st) in stats.iter().enumerate() {
        let marker = if rank == 0 { " <== fastest" } else { "" };
        println!(
            "  {:<32} {:>9.3} {:>9.3} {:>8.2}x {:>8}{}",
            st.name,
            st.min,
            st.median,
            best / st.min,
            st.wins,
            marker,
        );
    }
    (best_name, best)
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn main() {
    use primitives::field::F128T;
    use primitives::field::tower_f128::aarch64 as t;

    let quick = std::env::args().any(|a| a == "--quick");
    let rounds = if quick { 40 } else { ROUNDS };

    let mut s = 1u64;
    let a: Vec<F128T> = (0..N).map(|_| F128T::new(splitmix64(&mut s), splitmix64(&mut s))).collect();
    let b: Vec<F128T> = (0..N).map(|_| F128T::new(splitmix64(&mut s), splitmix64(&mut s))).collect();

    type Kernel = unsafe fn(&[F128T], &[F128T]) -> F128T;
    let methods: Vec<(&str, Kernel)> = vec![
        ("karatsuba x1", t::inner_unreduced_kara::<1>),
        ("karatsuba x2", t::inner_unreduced_kara::<2>),
        ("karatsuba x4", t::inner_unreduced_kara::<4>),
        ("schoolbook x1", t::inner_unreduced_school::<1>),
        ("schoolbook x2  (== inner_neon)", t::inner_unreduced_school::<2>),
        ("schoolbook x4", t::inner_unreduced_school::<4>),
    ];
    compare("F128T inner-product kernels (aarch64 PMULL)", &a, &b, &methods, rounds);
    println!("\n(speedup = fastest.min / this.min; wins = rounds this method was quickest)");
}

#[cfg(all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f"))]
fn main() {
    use primitives::field::tower_f128::x86_64 as t;
    use primitives::field::tower_f128_xy::x86_64 as txy;
    use primitives::field::{F128T, F128TUnreduced, F128Txy, F128TxyUnreduced};

    // The `field_bench` "inner prod, deferred" baseline: per-term scalar
    // pclmulqdq products XOR-accumulated, one reduce at the end.
    unsafe fn scalar_t(a: &[F128T], b: &[F128T]) -> F128T {
        let mut acc = F128TUnreduced::ZERO;
        for i in 0..a.len() {
            acc ^= a[i].mul_unreduced(b[i]);
        }
        acc.reduce()
    }
    unsafe fn scalar_txy(a: &[F128Txy], b: &[F128Txy]) -> F128Txy {
        let mut acc = F128TxyUnreduced::ZERO;
        for i in 0..a.len() {
            acc ^= a[i].mul_unreduced(b[i]);
        }
        acc.reduce()
    }

    let quick = std::env::args().any(|a| a == "--quick");
    let rounds = if quick { 40 } else { ROUNDS };

    let mut s = 1u64;
    let at: Vec<F128T> = (0..N).map(|_| F128T::new(splitmix64(&mut s), splitmix64(&mut s))).collect();
    let bt: Vec<F128T> = (0..N).map(|_| F128T::new(splitmix64(&mut s), splitmix64(&mut s))).collect();
    // Same coefficients reinterpreted as binius-tower elements: identical input
    // work, so the two fields' timings are directly comparable.
    let axy: Vec<F128Txy> = at.iter().map(|e| F128Txy::new(e.c0, e.c1)).collect();
    let bxy: Vec<F128Txy> = bt.iter().map(|e| F128Txy::new(e.c0, e.c1)).collect();

    println!("VPCLMULQDQ batched inner product  Σ aᵢ·bᵢ  (N={N} terms, {INNER} products/sample)");
    println!("scalar deferred = field_bench's 'inner prod, deferred' baseline (128-bit pclmulqdq).");

    type KT = unsafe fn(&[F128T], &[F128T]) -> F128T;
    let methods_t: Vec<(&str, KT)> = vec![
        ("scalar deferred (pclmulqdq)", scalar_t as KT),
        ("vpclmul karatsuba x1", t::inner_unreduced_vpclmul_kara::<1>),
        ("vpclmul karatsuba x2", t::inner_unreduced_vpclmul_kara::<2>),
        ("vpclmul karatsuba x4", t::inner_unreduced_vpclmul_kara::<4>),
        ("vpclmul schoolbook x1", t::inner_unreduced_vpclmul_school::<1>),
        ("vpclmul schoolbook x2", t::inner_unreduced_vpclmul_school::<2>),
        ("vpclmul schoolbook x4", t::inner_unreduced_vpclmul_school::<4>),
    ];
    let (bt_name, bt_min) = compare("B: F128T  (Artin-Schreier, y²+y+x⁶¹)", &at, &bt, &methods_t, rounds);

    type KX = unsafe fn(&[F128Txy], &[F128Txy]) -> F128Txy;
    let methods_x: Vec<(&str, KX)> = vec![
        ("scalar deferred (pclmulqdq)", scalar_txy as KX),
        ("vpclmul karatsuba x1", txy::inner_unreduced_vpclmul_kara::<1>),
        ("vpclmul karatsuba x2", txy::inner_unreduced_vpclmul_kara::<2>),
        ("vpclmul karatsuba x4", txy::inner_unreduced_vpclmul_kara::<4>),
        ("vpclmul schoolbook x1", txy::inner_unreduced_vpclmul_school::<1>),
        ("vpclmul schoolbook x2", txy::inner_unreduced_vpclmul_school::<2>),
        ("vpclmul schoolbook x4", txy::inner_unreduced_vpclmul_school::<4>),
    ];
    let (bx_name, bx_min) = compare("C: F128Txy (binius64, y²+x·y+1)", &axy, &bxy, &methods_x, rounds);

    println!("\nhead-to-head — best kernel of each tower (MIN ns/term):");
    println!("  B: F128T    {bt_min:>7.3}   ({bt_name})");
    println!("  C: F128Txy  {bx_min:>7.3}   ({bx_name})");
    println!(
        "  C/B = {:.2}x   (<1 → binius wins the batched deferred inner product on x86)",
        bx_min / bt_min
    );
    println!("\n(speedup = fastest.min / this.min; wins = rounds this method was quickest)");
}

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "aes"),
    all(target_arch = "x86_64", target_feature = "vpclmulqdq", target_feature = "avx512f")
)))]
fn main() {
    println!(
        "inner_bench: needs aarch64+aes (PMULL) or x86_64+vpclmulqdq+avx512f (VPCLMULQDQ).\n\
         Build with -C target-cpu=native on a Zen4 / Sapphire-Rapids-class core."
    );
}
