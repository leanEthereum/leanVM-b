//! Noise-robust comparator for the batched inner-product NEON kernels.
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
//! Run: `cargo run --release -p primitives --bin inner_bench`
//! (`--quick` shrinks the round count for a smoke check.)

use std::hint::black_box;
use std::time::Instant;

use primitives::field::F128T;

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

const N: usize = 1024; // inner-product length
const INNER: u64 = 64; // inner products per timed sample
const ROUNDS: usize = 400; // interleaved rounds

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
fn main() {
    use primitives::field::tower_f128::aarch64 as t;

    let quick = std::env::args().any(|a| a == "--quick");
    let rounds = if quick { 40 } else { ROUNDS };

    let mut s = 1u64;
    let a: Vec<F128T> = (0..N)
        .map(|_| F128T::new(splitmix64(&mut s), splitmix64(&mut s)))
        .collect();
    let b: Vec<F128T> = (0..N)
        .map(|_| F128T::new(splitmix64(&mut s), splitmix64(&mut s)))
        .collect();

    type Kernel = unsafe fn(&[F128T], &[F128T]) -> F128T;
    let methods: Vec<(&str, Kernel)> = vec![
        ("karatsuba x1", t::inner_unreduced_kara::<1>),
        ("karatsuba x2", t::inner_unreduced_kara::<2>),
        ("karatsuba x4", t::inner_unreduced_kara::<4>),
        ("schoolbook x1", t::inner_unreduced_school::<1>),
        ("schoolbook x2  (== inner_unreduced_neon)", t::inner_unreduced_school::<2>),
        ("schoolbook x4", t::inner_unreduced_school::<4>),
    ];
    let m = methods.len();

    // Correctness: every method must equal the reference before it is timed.
    let reference = unsafe { methods[0].1(&a, &b) };
    for (name, f) in &methods {
        assert_eq!(unsafe { f(&a, &b) }, reference, "{name} disagrees with reference");
    }
    println!("correctness: ok  ({m} methods agree)\n");

    // Warm up each method (page-in, branch predictor, frequency ramp).
    for (_, f) in &methods {
        for _ in 0..64 {
            black_box(unsafe { f(black_box(&a), black_box(&b)) });
        }
    }

    let ops = INNER * N as u64;
    let sample = |f: Kernel| -> f64 {
        let t0 = Instant::now();
        for _ in 0..INNER {
            black_box(unsafe { f(black_box(&a), black_box(&b)) });
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
        // This round's winner (lowest time) gets a win.
        let win = (0..m).min_by(|&x, &y| round[x].partial_cmp(&round[y]).unwrap()).unwrap();
        wins[win] += 1;
    }

    // Robust statistics per method.
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
    println!(
        "{} rounds, interleaved, ranked by MIN ns/term (noise only adds time):\n",
        rounds
    );
    println!(
        "  {:<32} {:>9} {:>9} {:>9} {:>8}",
        "method", "min", "median", "speedup", "wins"
    );
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
    println!("\n(speedup = fastest.min / this.min; wins = rounds this method was quickest)");
}

#[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
fn main() {
    println!("inner_bench: needs aarch64 + aes (build with -C target-cpu=native)");
}
