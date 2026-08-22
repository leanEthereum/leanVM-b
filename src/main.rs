//! Benchmark CLI for XMSS aggregation, recursion, and the Fibonacci demo.

use clap::{Parser, Subcommand};

#[derive(Parser)]
struct Cli {
    /// WHIR inverse-rate logarithm (1 through 4).
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

    /// Measured proving passes after warmup.
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..)
    )]
    repeat: usize,

    /// Idle seconds before each measured pass.
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
    lean_vm::init_prover();
    let plan = primitives::bench::Plan::new(cli.repeat, cli.cooldown);
    if cli.tracing && !matches!(&cli.command, Command::Recursion { .. }) {
        primitives::init_tracing();
    }
    match cli.command {
        Command::Xmss { n_signatures } => {
            rec_aggregation::run_xmss_aggregation(n_signatures, cli.log_inv_rate, plan);
        }
        Command::Recursion { n, xmss_per_leaf } => {
            rec_aggregation::run_recursion(n, xmss_per_leaf, cli.log_inv_rate, cli.tracing, plan);
        }
        Command::Fibonacci { n } => {
            rec_aggregation::run_fibonacci(n, cli.log_inv_rate, plan);
        }
    }
    if std::env::var_os("ZK_ALLOC_STATS").is_some() {
        eprintln!("{}", zk_alloc::stats());
    }
}
