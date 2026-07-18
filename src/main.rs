//! Benchmark CLI for the two flagship workloads (plus the Fibonacci demo).
//!
//! ```text
//! cargo run --release -- xmss --n-signatures 820
//! cargo run --release -- xmss --n-signatures 820 --log-inv-rate 2
//! cargo run --release -- recursion --n 2
//! cargo run --release -- fibonacci --n 2000000
//! ```

use clap::{Parser, Subcommand};

#[derive(Parser)]
struct Cli {
    /// Ligerito inverse-rate logarithm: 1, 2, 3, or 4 selects rate 1/2,
    /// 1/4, 1/8, or 1/16 respectively.
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = parse_log_inv_rate
    )]
    log_inv_rate: usize,

    /// Enable hierarchical timing traces. Use RUST_LOG to adjust verbosity.
    #[arg(long, global = true)]
    tracing: bool,

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
    /// Run an n→1 recursive proof aggregation.
    Recursion {
        /// Number of inner proofs to aggregate.
        #[arg(long, default_value = "2")]
        n: usize,
        /// Single-block SHA-256 compressions per inner proof (inner program shape).
        #[arg(long, default_value = "8")]
        hashes: usize,
        /// MUL iterations per inner proof (inner program shape).
        #[arg(long, default_value = "32768")]
        iters: usize,
    },
    /// Prove and verify Fibonacci in the exponent (demo).
    Fibonacci {
        /// Number of recurrence steps.
        #[arg(long, default_value = "2000000")]
        n: usize,
    },
}

fn parse_log_inv_rate(value: &str) -> Result<usize, String> {
    let rate = value
        .parse::<usize>()
        .map_err(|_| "log_inv_rate must be one of 1, 2, 3, or 4".to_string())?;
    if (1..=4).contains(&rate) {
        Ok(rate)
    } else {
        Err("log_inv_rate must be one of 1, 2, 3, or 4".to_string())
    }
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Command::Xmss { n_signatures } => {
            if cli.tracing {
                primitives::init_tracing();
            }
            rec_aggregation::run_xmss_aggregation(n_signatures, cli.log_inv_rate);
        }
        Command::Recursion { n, hashes, iters } => {
            let inner: Vec<(usize, usize)> = (0..n).map(|_| (hashes, iters)).collect();
            rec_aggregation::run_recursion(&inner, cli.log_inv_rate, cli.tracing);
        }
        Command::Fibonacci { n } => {
            if cli.tracing {
                primitives::init_tracing();
            }
            rec_aggregation::run_fibonacci(n, cli.log_inv_rate);
        }
    }
}
