//! Dedicated PCS throughput benchmark (manual; `#[ignore]`d so it never runs
//! in a normal `cargo test`).
//!
//! Commits and opens a random witness of `2^PCS_LOG_N` GF(2^64) elements at
//! inverse-rate `1/2^PCS_LOG_INV_RATE`, times each phase, and reports GiB/s
//! over the committed data. Env knobs (all optional):
//!
//!   PCS_LOG_N          number of variables = log2(witness length)   [default 22]
//!   PCS_LOG_INV_RATE   log2 of the inverse RS rate (rate = 1/2^r)    [default: profile]
//!   PCS_SAMPLES        timed repetitions; the median is reported     [default 5]
//!
//! Run:
//!   PCS_LOG_N=24 PCS_LOG_INV_RATE=1 cargo test --release -p pcs --test pcs_throughput -- --ignored --nocapture
//!
//! Hierarchical tracing is enabled automatically (`RUST_LOG` adjusts its
//! verbosity). Set `LIGERITO_TRACE=1` as well for the legacy textual per-phase
//! breakdown. Large `PCS_LOG_N` needs substantial memory (the RS codeword is
//! `2^log_inv_rate`× the witness, and the open clones the basis table each
//! sample).

use std::hint::black_box;
use std::time::Instant;

use fiat_shamir::Sponge;
use pcs::ligerito::{
    build_eq_table_ext, commit, configs_for, configs_for_rate, inner_product_base_ext, recursive_prover_with_basis,
};
use primitives::{
    field::{F64, F192},
    pretty_integer,
};

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn env_usize(key: &str) -> Option<usize> {
    std::env::var(key).ok().map(|s| {
        s.parse()
            .unwrap_or_else(|_| panic!("{key} must be a non-negative integer"))
    })
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    xs[xs.len() / 2]
}

#[test]
#[ignore = "manual release benchmark; drive with PCS_LOG_N / PCS_LOG_INV_RATE"]
fn pcs_throughput() {
    primitives::init_tracing();

    let log_n = env_usize("PCS_LOG_N").unwrap_or(22);
    let samples = env_usize("PCS_SAMPLES").unwrap_or(5).max(1);

    // Honour PCS_LOG_INV_RATE if set, else the production profile's L0 rate.
    let (pc, _vc) = match env_usize("PCS_LOG_INV_RATE") {
        Some(r) => configs_for_rate(log_n, r),
        None => configs_for(log_n),
    }
    .expect("Ligerito config feasible (try a larger PCS_LOG_N, e.g. >= 16)");
    let log_inv_rate = pc.log_inv_rates[0];
    let trace_span = tracing::info_span!("PCS throughput", log_n, log_inv_rate, samples).entered();

    // Random F64 witness (the committed polynomial) and a random E evaluation point.
    let mut s = 0x0192_0000u64 ^ log_n as u64;
    let n = 1usize << log_n;
    let witness: Vec<F64> = (0..n).map(|_| F64(splitmix64(&mut s))).collect();
    let point: Vec<F192> = (0..log_n)
        .map(|_| F192::new(splitmix64(&mut s), splitmix64(&mut s), splitmix64(&mut s)))
        .collect();
    let b_initial = build_eq_table_ext(&point);
    let target = inner_product_base_ext(&witness, &b_initial);

    let mut commit_times = Vec::with_capacity(samples);
    let mut open_times = Vec::with_capacity(samples);
    for sample in 0..samples {
        tracing::info_span!("Sample", sample).in_scope(|| {
            let ((cm, pd), elapsed) = tracing::info_span!("Commit").in_scope(|| {
                let t = Instant::now();
                let committed = commit(&witness, pc.initial_k, log_inv_rate);
                (committed, t.elapsed().as_secs_f64())
            });
            commit_times.push(elapsed);

            let mut ch = Sponge::new(b"pcs-throughput", &[]);
            let (proof, elapsed) = tracing::info_span!("PCS open").in_scope(|| {
                let t = Instant::now();
                let proof = recursive_prover_with_basis(
                    &pc,
                    &witness,
                    b_initial.clone(),
                    target,
                    &pd.codeword,
                    &pd.merkle_tree,
                    &mut ch,
                );
                (proof, t.elapsed().as_secs_f64())
            });
            open_times.push(elapsed);
            black_box((cm, proof));
        });
    }

    let commit_s = median(commit_times);
    let open_s = median(open_times);

    // Throughput is over the committed data: 2^log_n F64 = 2^log_n * 8 bytes.
    let data_bytes = (n as f64) * 8.0;
    let mib = |bytes: f64| bytes / (1u64 << 20) as f64;
    let gibps = |secs: f64| (data_bytes / (1u64 << 30) as f64) / secs;
    let codeword_bytes = data_bytes * (1u64 << log_inv_rate) as f64;

    // tracing-forest renders the tree when its root span closes. Close it
    // before printing the throughput report so the complete trace appears first.
    drop(trace_span);

    println!(
        "\nPCS throughput — 2^{log_n} variables, rate 1/2^{log_inv_rate}, median of {}",
        pretty_integer(samples)
    );
    println!(
        "  committed data                  : {:>8.1} MiB  ({:>13} F64)",
        mib(data_bytes),
        pretty_integer(n)
    );
    println!("  RS codeword (encoded)           : {:>8.1} MiB", mib(codeword_bytes));
    println!("  ------------------------------------------------------------");
    println!(
        "  commit                          : {:>8.1} ms   ({:>6.2} GiB/s)",
        commit_s * 1e3,
        gibps(commit_s)
    );
    println!(
        "  open                            : {:>8.1} ms   ({:>6.2} GiB/s)",
        open_s * 1e3,
        gibps(open_s)
    );
    println!("  ------------------------------------------------------------");
    println!(
        "  commit + open                   : {:>8.1} ms   ({:>6.2} GiB/s)",
        (commit_s + open_s) * 1e3,
        gibps(commit_s + open_s),
    );
}
