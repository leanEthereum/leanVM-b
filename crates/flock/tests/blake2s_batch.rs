//! Standalone batch BLAKE2s proving, isolated from the VM.
//!
//! This exercises only Flock's BLAKE2s path over `N` compressions: witness
//! generation, F64 commitment, zerocheck + lincheck reduction, the stacked
//! ring-switch/WHIR opening, and verification. Circuit construction is
//! outside the timed region, matching the VM's warmed-setup convention.
//!
//! Run with the XMSS-sized workload:
//! ```text
//! LEANVM_NUM_THREADS=11 FLOCK_N_LOG=17 cargo test --release -p flock --test blake2s_batch -- --ignored --nocapture
//! ```
//!
//! `BENCH_REPEAT=n` averages `n` measured passes after the warmup pass, and
//! `BENCH_COOLDOWN` (seconds, default 2) spaces them so a thermally limited laptop
//! does not report its power budget as proving cost. One warmup always runs: a cold
//! pass pays thread-pool spawn, first-touch page faults, and setup-table
//! construction that steady-state proving does not (see [`primitives::bench`]).

use std::time::Instant;

use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use flock::blake2s::{
    Blake2sSetup, Compression, K_LOG, generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
    pinned_compression, ring_switch_open, ring_switch_verify,
};
use pcs::pack::LOG_PACKING;
use pcs::stack_open::{open_batch_mixed_whir_stacked, verify_opening_batch_mixed_whir_stacked};
use pcs::whir::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0};
use pcs::whir::{commit, configs_for};
use primitives::bench::{Plan, Timing};
use primitives::{field::F64, pretty_integer, test_rng::Rng};

#[test]
#[ignore = "manual release benchmark; needs a large-stack worker and substantial memory"]
fn blake2s_batch_prove_verify() {
    // The XMSS n=820 workload executes about 2^17 BLAKE2s compressions.
    let requested_n_log: usize = std::env::var("FLOCK_N_LOG")
        .ok()
        .map(|s| s.parse().expect("FLOCK_N_LOG must be an integer"))
        .unwrap_or(13);
    let n = 1usize
        .checked_shl(requested_n_log as u32)
        .expect("FLOCK_N_LOG exceeds the platform usize width");
    let n_log = min_n_blocks_log(n);
    let mu = K_LOG + n_log - LOG_PACKING;
    assert!(
        mu >= 15,
        "FLOCK_N_LOG too small: need a committed witness with mu >= 15"
    );

    let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| pinned_compression(std::array::from_fn(|_| rng.next_u32())))
        .collect();

    let t = Instant::now();
    let setup = Blake2sSetup::new(n);
    let setup_ms = t.elapsed().as_secs_f64() * 1e3;

    let (prover_config, verifier_config) = configs_for(mu).expect("WHIR configuration");

    // One full prove pass: witness generation, commitment, and the reduction +
    // stacked opening. Deterministic in `blocks`, so every pass is the same work
    // on the same shape and their timings are directly comparable.
    //
    // Each pass is one arena phase, matching how the VM prover runs. Only the
    // transcript and the opening escape, and both are plain `Vec` proof data, so
    // nothing here outlives its phase. `setup` is built above, outside any phase,
    // because it is cached across passes.
    zk_alloc::enable_arena();
    let prove_pass = || {
        let _phase = zk_alloc::enter_phase();
        let t = Instant::now();
        let (z_packed, a_packed, b_packed, z_lincheck) = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
        let q_flock: Vec<F64> = z_packed.iter().map(|&w| F64(w)).collect();
        let witness_s = t.elapsed().as_secs_f64();
        assert_eq!(q_flock.len(), 1 << mu);

        let mut ps = ProverState::new(b"flock-blake2s-batch", &[]);
        let t_prove = Instant::now();

        let t = Instant::now();
        let (commitment, prover_data) = commit(&q_flock, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
        ps.add_root(&commitment.root);
        let commit_s = t.elapsed().as_secs_f64();

        let t = Instant::now();
        let reduced = setup.prove_reduction_precomputed(&z_packed, &a_packed, &b_packed, &z_lincheck, &mut ps);
        drop((z_packed, a_packed, b_packed, z_lincheck));
        let ring = ring_switch_open(n, 0, &reduced);
        open_batch_mixed_whir_stacked(&mut ps, &q_flock, &prover_data, &prover_config, &[], &ring);
        let open_s = t.elapsed().as_secs_f64();
        let prove_s = t_prove.elapsed().as_secs_f64();

        (ps.into_proof(), [witness_s, commit_s, open_s, prove_s])
    };

    // The per-stage timings ride alongside the pass result, so one `Plan` drives
    // the warmup, the cooldown, and the repetition for all four of them.
    let plan = Plan::from_env();
    let mut stages: [Timing; 4] = std::array::from_fn(|_| Timing::default());
    let (transcript, _) = plan.warm_then_measure(|_final_pass| {
        let (out, secs) = prove_pass();
        for (timing, s) in stages.iter_mut().zip(secs) {
            timing.push(s);
        }
        out
    });
    // The warmup pass also pushed a sample; drop the leading one per stage.
    let [witness, commit_stage, open, prove] = stages.map(|t| {
        let mut kept = Timing::default();
        for &s in &t.samples()[1..] {
            kept.push(s);
        }
        kept
    });

    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|_final_pass| {
        let mut vs = VerifierState::new(b"flock-blake2s-batch", &transcript, &[]);
        let root = vs.next_root().expect("commitment root");
        let replay = setup.verify_reduction(&mut vs).expect("Flock reduction verifies");
        let ring = ring_switch_verify(n, 0, &replay.ab, &replay.c);
        assert!(
            verify_opening_batch_mixed_whir_stacked(&mut vs, &verifier_config, mu, &root, &[], &ring),
            "stacked PCS opening verifies"
        );
        vs.finish().expect("transcript fully consumed");
    });

    let ms = |t: &Timing| format!("{:>8.1} ms{}", t.mean() * 1e3, t.spread());
    println!(
        "\nFlock BLAKE2s batch proving, {} compressions (2^{n_log} slots)",
        pretty_integer(n)
    );
    println!("  setup (preprocessing, excluded) : {setup_ms:>8.1} ms");
    println!("  witness-gen                     : {}", ms(&witness));
    println!("  commit                          : {}", ms(&commit_stage));
    println!("  reduction + open                : {}", ms(&open));
    println!("  ------------------------------------------");
    println!("  prove TOTAL (witness excluded)  : {}", ms(&prove));
    println!(
        "  verify                          : {:>8.1} ms",
        verify_time.mean() * 1e3
    );
    let prove_s = prove.mean();
    let compressions_per_second = (n as f64 / prove_s).round() as u64;
    println!(
        "  throughput                      : {:>14} compressions/s{}",
        pretty_integer(compressions_per_second),
        prove.spread()
    );
    println!(
        "  (~{:.1} XMSS/s equivalent at 146 compressions/signature)",
        n as f64 / prove_s / 146.0
    );
    println!("  {} measured pass(es) after 1 warmup", plan.repeat);
}
