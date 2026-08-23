//! The two benchmarks: one leaf of the aggregation tree (`xmss`), and an n→1
//! recursion step over leaves of that size (`recursion`). Both drive the same
//! [`crate::aggregation::aggregate`] entry point the real API uses.

use primitives::bench::Plan;
use primitives::{pretty_f64, pretty_integer};
use xmss::{XmssPublicKey, XmssSignature};

use crate::aggregation::{AggregateSignature, aggregate, aggregate_with_stats};
use crate::signers_cache;

/// Cached signers `[from, to)`, as the aggregation API takes them.
fn signers(from: usize, to: usize) -> Vec<(XmssPublicKey, XmssSignature)> {
    signers_cache::get_signers(to)[from..to].to_vec()
}

/// Report the shape and cost of one aggregation node.
fn report(label: &str, stats: &lean_vm::cpu::Stats, sig: &AggregateSignature, prove_time: &primitives::bench::Timing) {
    let base_cycles: usize = stats.base_counts.iter().sum();
    println!("{label}");
    // The program's own work, then what gets proven: the fill blocks bring each table
    // to a power of two so that none needs padding rows, so the proven total is the sum
    // of those powers.
    println!(
        "  cycles (VM steps)           : {} = {}",
        pretty_integer(base_cycles),
        crate::report::pow(base_cycles)
    );
    println!(
        "    proven rows               : {} = {}  (filled to powers of two)",
        pretty_integer(stats.cycles),
        crate::report::pow(stats.cycles)
    );
    println!("    details                   : {}", stats.details());
    println!(
        "  signers                     : {}",
        pretty_integer(sig.public_keys.len())
    );
    crate::report::print_proof_size(sig.proof());
    // The whole `aggregate` call, not just `cpu::prove`: for a node that also
    // covers verifying each child and batching the deferred claims, which are
    // real per-node costs. `--tracing` breaks it down.
    println!(
        "  aggregating                 : {} s{}      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        crate::report::peak_gib()
    );
}

/// Aggregate `n` XMSS signatures in one leaf and verify it.
///
/// Proving runs one discarded warmup pass followed by `plan.repeat` measured
/// passes; see [`primitives::bench`] for why the first pass is not
/// representative and why the cooldown matters.
pub fn run_xmss_aggregation(n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("XMSS aggregation", n, log_inv_rate).entered();
    // Spawn the worker pool before any timed work, so no kernel pays the spawn
    // cost. Opting into the arena is the calling *process's* decision (one region,
    // one proof at a time), so it stays in `main`, not here.
    lean_vm::init_prover_pool();
    let raw = signers(0, n);
    let (message, epoch) = (signers_cache::message(), signers_cache::EPOCH);

    // Only the final measured pass of each stage is traced: the tree describes the
    // proof the reported timings are about, instead of repeating itself per pass.
    let ((sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        aggregate_with_stats(&[], raw.clone(), message, epoch, log_inv_rate).expect("leaf aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        sig.verify().expect("the leaf aggregate verifies");
    });
    drop(trace_span);

    report(
        &format!("\nXMSS aggregation, {} signatures", pretty_integer(n)),
        &stats,
        &sig,
        &prove_time,
    );
    println!(
        "  per signature               : {} XMSS/s",
        pretty_f64(n as f64 / prove_time.mean())
    );
    println!("  verifying                   : {} s", pretty_f64(verify_time.mean()));
}

/// Prove `n` leaves of `per_leaf` signatures each, then aggregate them in one
/// recursion step and verify the result. The leaves are built once; only the
/// recursion step is measured.
pub fn run_recursion(n: usize, per_leaf: usize, log_inv_rate: usize, enable_tracing: bool, plan: Plan) {
    assert!(n >= 1, "a recursion step needs at least one child");
    lean_vm::init_prover_pool();
    let (message, epoch) = (signers_cache::message(), signers_cache::EPOCH);
    let all = signers(0, n * per_leaf);
    let started = std::time::Instant::now();
    let guest_instructions: usize = crate::aggregation::unified_guest()
        .fn_ranges
        .iter()
        .map(|(_, _, len)| *len as usize)
        .sum();
    let compile_time = started.elapsed();

    let children: Vec<AggregateSignature> = (0..n)
        .map(|k| {
            aggregate(
                &[],
                all[k * per_leaf..(k + 1) * per_leaf].to_vec(),
                message,
                epoch,
                log_inv_rate,
            )
            .expect("leaf aggregates")
        })
        .collect();

    if enable_tracing {
        primitives::init_tracing();
    }
    let ((sig, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        aggregate_with_stats(&children, vec![], message, epoch, log_inv_rate).expect("node aggregates")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        sig.verify().expect("the recursive aggregate verifies");
    });

    println!(
        "aggregation bytecode: {} instructions (2^{} padded), compiled in {} s",
        pretty_integer(guest_instructions),
        crate::aggregation::unified_guest().prog.len().trailing_zeros(),
        pretty_f64(compile_time.as_secs_f64())
    );
    report(
        &format!(
            "\nrecursion {n}\u{2192}1, over leaves of {} signatures",
            pretty_integer(per_leaf)
        ),
        &stats,
        &sig,
        &prove_time,
    );
    println!("  verifying                   : {} s", pretty_f64(verify_time.mean()));
}
