//! Benchmark CLI for the two flagship workloads (plus the Fibonacci demo): one
//! leaf of an aggregation tree, and an n→1 recursion step over such leaves.
//!
//! ```text
//! cargo run --release -- xmss --n-signatures 820
//! cargo run --release -- xmss --n-signatures 820 --log-inv-rate 2
//! cargo run --release -- xmss --n-signatures 820 --repeat 5
//! cargo run --release -- recursion --n 2 --xmss-per-leaf 900
//! cargo run --release -- fibonacci --n 2000000
//! cargo run --release -- --tracing fibonacci --n 2000000
//! ```
//!
//! Every workload discards one warmup pass before measuring, so a reported
//! duration is steady-state proving rather than a cold first run. `--repeat n`
//! averages `n` measured passes and reports a 95% confidence half-width alongside
//! the mean. `--cooldown` (seconds, default 2) idles before each pass so a
//! thermally limited laptop does not report its power budget as proving cost.

use clap::{Parser, Subcommand};

#[derive(Parser)]
struct Cli {
    /// WHIR inverse-rate logarithm: 1, 2, 3, or 4 selects rate 1/2,
    /// 1/4, 1/8, or 1/16 respectively.
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..=4)
    )]
    log_inv_rate: usize,

    /// Enable hierarchical timing traces. Use RUST_LOG to adjust verbosity.
    #[arg(long, global = true)]
    tracing: bool,

    /// Measured proving passes to average, after the warmup pass. Reported with
    /// a 95% confidence half-width once above 1.
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..)
    )]
    repeat: usize,

    /// Idle seconds before each measured pass. On a thermally limited host (any
    /// Apple laptop) back-to-back proving throttles the SoC and measures the power
    /// budget instead of the prover. The default recovers most of that; use 6 when
    /// comparing two builds, and 0 on a server-class host, which needs none.
    #[arg(long, global = true, default_value_t = 2)]
    cooldown: u64,

    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Aggregate XMSS signatures inside the VM and verify the proof.
    Xmss {
        /// Number of signatures to aggregate.
        #[arg(long, default_value = "820")]
        n_signatures: usize,
    },
    /// Aggregate n previously aggregated signatures into one proof.
    Recursion {
        /// Number of child aggregates.
        #[arg(long, default_value = "2")]
        n: usize,
        /// Signatures in each child. Sets the child proof's committed size,
        /// which is what the recursion cost should be quoted against.
        #[arg(long, default_value = "900")]
        xmss_per_leaf: usize,
    },
    /// Prove and verify Fibonacci in the exponent (demo).
    Fibonacci {
        /// Number of recurrence steps.
        #[arg(long, default_value = "2000000")]
        n: usize,
    },
}

fn main() {
    let cli = Cli::parse();
    // Pinned worker pool plus the proving arena, for every workload below. Both
    // are process-wide policy, which is why they are set here and not inside the
    // library entry points.
    lean_vm::init_prover();
    let plan = primitives::bench::Plan::new(cli.repeat, cli.cooldown);
    match &cli.command {
        Command::Xmss { n_signatures } => {
            if cli.tracing {
                primitives::init_tracing();
            }
            rec_aggregation::run_xmss_aggregation(*n_signatures, cli.log_inv_rate, plan);
        }
        // `run_recursion` initializes tracing itself, after the guest compile it
        // does not want traced.
        Command::Recursion { n, xmss_per_leaf } => {
            rec_aggregation::run_recursion(*n, *xmss_per_leaf, cli.log_inv_rate, cli.tracing, plan);
        }
        Command::Fibonacci { n } => {
            if cli.tracing {
                primitives::init_tracing();
            }
            rec_aggregation::run_fibonacci(*n, cli.log_inv_rate, plan);
        }
    }
    // What the proving arena absorbed, for sizing its slabs and checking that the
    // buffers meant to be arena-backed are.
    if std::env::var_os("ZK_ALLOC_STATS").is_some() {
        eprintln!("{}", zk_alloc::stats());
    }
}
