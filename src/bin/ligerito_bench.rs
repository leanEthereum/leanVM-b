//! Ligerito throughput benchmark: bits committed + opened per second.
//!
//! Compares the current PCS (commit over GHASH F128, open over F128) against
//! the 64-bit transition's PCS (commit over F64, open over the tower F128T),
//! at matched witness BIT sizes: the K version commits twice as many
//! elements of half the width.
//!
//! Pipeline measured per version: `commit` (RS encode + Merkle) and one
//! `open` of a random eq-point evaluation claim through the recursive
//! Ligerito prover (Secure profile shapes, log_inv_rate = 1,
//! log_batch_size = initial_k = 6). Verification runs once per size as a
//! correctness gate but is excluded from the timing (the metric is prover
//! throughput).
//!
//! Run with: cargo run --release --bin ligerito_bench

use std::hint::black_box;
use std::time::Instant;

use flare::challenger::FsChallenger;
use flare::field::{F64, F128, F128T};
use flare::pcs::ligerito::{
    LigeritoProfile, LigeritoSecurityConfig, ProverConfig, VerifierConfig,
};
use flare::pcs::{PcsParams, commit};

const LOG_INV_RATE: usize = 1;
const LOG_BATCH: usize = 6; // must equal the profile's initial_k
const SAMPLES: usize = 3;

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

fn configs_for(log_n: usize) -> (ProverConfig, VerifierConfig) {
    LigeritoSecurityConfig::derive_profile(log_n + 7, LigeritoProfile::Secure)
        .expect("derive Secure profile")
        .to_prover_verifier_configs()
        .expect("prover/verifier configs")
}

/// eq(point, y) table, LSB-first indexing (mirrors lincheck::build_eq_table).
fn eq_table_f128(point: &[F128]) -> Vec<F128> {
    flare::lincheck::build_eq_table(point)
}

struct Timing {
    commit_s: f64,
    open_s: f64,
}

/// Current PCS: F128 witness of 2^log_n elements (= 2^(log_n+7) bits).
fn run_f128(log_n: usize, verify_once: bool) -> Timing {
    let mut s = 0xF128_0000u64 ^ log_n as u64;
    let n = 1usize << log_n;
    let witness: Vec<F128> = (0..n).map(|_| F128::new(splitmix64(&mut s), splitmix64(&mut s))).collect();
    let params = PcsParams {
        m: log_n + 7,
        log_inv_rate: LOG_INV_RATE,
        log_batch_size: LOG_BATCH,
        profile: LigeritoProfile::Secure,
    };
    let (pc, vc) = configs_for(log_n);

    let point: Vec<F128> = (0..log_n).map(|_| F128::new(splitmix64(&mut s), splitmix64(&mut s))).collect();
    let b = eq_table_f128(&point);
    let target = witness.iter().zip(&b).fold(F128::ZERO, |acc, (w, bv)| acc + *w * *bv);

    let mut commit_times = Vec::new();
    let mut open_times = Vec::new();
    let mut checked = false;
    for _ in 0..SAMPLES {
        let t = Instant::now();
        let (c, pd) = commit(&witness, &params);
        commit_times.push(t.elapsed().as_secs_f64());

        let mut ch = FsChallenger::new(b"ligerito-bench");
        let t = Instant::now();
        let proof = flare::pcs::ligerito::recursive_prover_with_basis(
            &pc,
            witness.clone(),
            b.clone(),
            target,
            &pd.codeword,
            &pd.merkle_tree,
            &mut ch,
        );
        open_times.push(t.elapsed().as_secs_f64());

        if verify_once && !checked {
            checked = true;
            let root = c.root;
            let mut vch = FsChallenger::new(b"ligerito-bench");
            let point_v = point.clone();
            let ok = flare::pcs::ligerito::recursive_verifier_with_basis_succinct(
                &vc,
                &proof,
                log_n,
                target,
                &root,
                |ris: &[F128], yr_log_n: usize| {
                    // b = eq(point, .) with LSB-first table indexing; the
                    // prover folds LSB variables first, so ris bind
                    // point[0..len(ris)] and y enumerates the top variables.
                    let split = ris.len();
                    debug_assert_eq!(split + yr_log_n, point_v.len());
                    let mut prefix = F128::ONE;
                    for (p, r) in point_v[..split].iter().zip(ris) {
                        prefix *= *p * *r + (*p + F128::ONE) * (*r + F128::ONE);
                    }
                    let tail = eq_table_f128(&point_v[split..]);
                    tail.into_iter().map(|t| prefix * t).collect()
                },
                &mut vch,
            );
            assert!(ok, "F128 verification failed at log_n={log_n}");
        }
        black_box(proof);
    }
    Timing {
        commit_s: median(commit_times),
        open_s: median(open_times),
    }
}

fn main() {
    println!("Ligerito throughput: bits committed+opened per second");
    println!("profile Secure, rate 1/2, log_batch = {LOG_BATCH}, median of {SAMPLES}\n");
    println!(
        "{:>10} | {:>21} | {:>21} | {:>8}",
        "witness", "F128 (current)", "F64/F128T (new)", "speedup"
    );
    println!(
        "{:>10} | {:>9} {:>11} | {:>9} {:>11} |",
        "bits", "sec", "Gbit/s", "sec", "Gbit/s"
    );
    println!("{}", "-".repeat(72));

    for log_bits in [24usize, 26, 28, 30] {
        let bits = (1u64 << log_bits) as f64;

        // Current: 2^(log_bits-7) F128 elements.
        let t128 = run_f128(log_bits - 7, log_bits == 24);
        let total128 = t128.commit_s + t128.open_s;

        // New: 2^(log_bits-6) F64 elements.
        let tk = run_k(log_bits - 6, log_bits == 24);
        let totalk = tk.commit_s + tk.open_s;

        println!(
            "{:>10} | {:>9.3} {:>11.3} | {:>9.3} {:>11.3} | {:>7.2}x",
            format!("2^{log_bits}"),
            total128,
            bits / total128 / 1e9,
            totalk,
            bits / totalk / 1e9,
            total128 / totalk,
        );
        println!(
            "{:>10} |   commit {:>6.3}s open {:>6.3}s | commit {:>6.3}s open {:>6.3}s",
            "",
            t128.commit_s,
            t128.open_s,
            tk.commit_s,
            tk.open_s
        );
    }

    println!();
    println!("same WORD count (the VM-side view: a machine word is one element,");
    println!("so the new PCS commits half the bits for the same data):");
    println!(
        "{:>10} | {:>15} | {:>15} | {:>8}",
        "words", "F128 (current)", "F64/F128T (new)", "speedup"
    );
    println!("{}", "-".repeat(60));
    for log_words in [19usize, 21, 23] {
        let t128 = run_f128(log_words, false);
        let tk = run_k(log_words, false);
        let total128 = t128.commit_s + t128.open_s;
        let totalk = tk.commit_s + tk.open_s;
        println!(
            "{:>10} | {:>13.3}s | {:>13.3}s | {:>7.2}x",
            format!("2^{log_words}"),
            total128,
            totalk,
            total128 / totalk,
        );
    }
}

/// New PCS: F64 witness of 2^log_n elements (= 2^(log_n+6) bits), commit over
/// K, open over the tower F128T.
fn run_k(log_n: usize, verify_once: bool) -> Timing {
    use flare::pcs::ligerito_k as lk;
    let mut s = 0x0064_0000u64 ^ log_n as u64;
    let n = 1usize << log_n;
    let witness: Vec<F64> = (0..n).map(|_| F64(splitmix64(&mut s))).collect();
    let (pc, vc) = lk::k_configs_for(log_n).expect("derive K Secure profile");

    let point: Vec<F128T> = (0..log_n)
        .map(|_| F128T::new(splitmix64(&mut s), splitmix64(&mut s)))
        .collect();
    let b = lk::build_eq_table_ext(&point);
    let target = lk::inner_product_base_ext(&witness, &b);

    let mut commit_times = Vec::new();
    let mut open_times = Vec::new();
    let mut checked = false;
    for _ in 0..SAMPLES {
        let t = Instant::now();
        let (c, pd) = lk::commit_k(&witness, LOG_BATCH, LOG_INV_RATE);
        commit_times.push(t.elapsed().as_secs_f64());

        let mut ch = FsChallenger::new(b"ligerito-bench-k");
        let t = Instant::now();
        let proof = lk::recursive_prover_with_basis_k(
            &pc,
            witness.clone(),
            b.clone(),
            target,
            &pd.codeword,
            &pd.merkle_tree,
            &mut ch,
        );
        open_times.push(t.elapsed().as_secs_f64());

        if verify_once && !checked {
            checked = true;
            let mut vch = FsChallenger::new(b"ligerito-bench-k");
            let point_v = point.clone();
            let ok = lk::recursive_verifier_with_basis_succinct_k(
                &vc,
                &proof,
                log_n,
                target,
                &c.root,
                |ris: &[F128T], yr_log_n: usize| {
                    // b = eq(point, .), LSB-first: ris bind point[..split].
                    let split = ris.len();
                    debug_assert_eq!(split + yr_log_n, point_v.len());
                    let mut prefix = F128T::ONE;
                    for (p, r) in point_v[..split].iter().zip(ris) {
                        prefix *= *p * *r + (F128T::ONE + *p) * (F128T::ONE + *r);
                    }
                    lk::build_eq_table_ext(&point_v[split..])
                        .into_iter()
                        .map(|t| prefix * t)
                        .collect()
                },
                &mut vch,
            );
            assert!(ok, "K succinct verification failed at log_n={log_n}");
        }
        black_box(proof);
    }
    Timing {
        commit_s: median(commit_times),
        open_s: median(open_times),
    }
}
