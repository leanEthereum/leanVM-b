//! Benchmark CLI for the two flagship workloads (plus the Fibonacci demo).
//!
//! ```text
//! cargo run --release -- xmss --n-signatures 820
//! cargo run --release -- xmss --n-signatures 820 --log-inv-rate 2
//! cargo run --release -- xmss --n-signatures 820 --repeat 5
//! cargo run --release -- recursion --n 2
//! cargo run --release -- fibonacci --n 2000000
//! cargo run --release -- --tracing fibonacci --n 2000000
//! ```
//!
//! Every workload discards one warmup pass before measuring, so a reported
//! duration is steady-state proving rather than a cold first run. `--repeat n`
//! averages `n` measured passes and reports a 95% confidence half-width
//! alongside the mean.

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

    /// Measured proving passes to average, after the warmup pass. Reported with
    /// a 95% confidence half-width once above 1.
    #[arg(long, global = true, default_value_t = 1, value_parser = parse_repeat)]
    repeat: usize,

    /// Idle milliseconds before each measured pass. On a thermally limited host
    /// (any Apple laptop) back-to-back proving throttles the SoC and measures
    /// the power budget instead of the prover: ~6000 restores steady-state
    /// clocks on an M4 Max MacBook Pro, and a server-class host needs none.
    #[arg(long, global = true, default_value_t = 0)]
    cooldown_ms: u64,

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
        /// BLAKE3 compressions per inner proof (inner program shape).
        #[arg(long, default_value = "8")]
        hashes: usize,
        /// MUL iterations per inner proof (inner program shape). Chosen so the
        /// inner committed witness fills most of a 2^26 PCS, which is the size
        /// the recursion cost should be quoted at. The inner program's DEREF
        /// range check gives out just above 66000, so this is near the ceiling.
        #[arg(long, default_value = "64000")]
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

fn parse_repeat(value: &str) -> Result<usize, String> {
    match value.parse::<usize>() {
        Ok(n) if n >= 1 => Ok(n),
        _ => Err("repeat must be a positive integer".to_string()),
    }
}

fn main() {
    let cli = Cli::parse();
    let plan = primitives::bench::Plan::new(cli.repeat, cli.cooldown_ms);
    match cli.command {
        Command::Xmss { n_signatures } => {
            if cli.tracing {
                primitives::init_tracing();
            }
            rec_aggregation::run_xmss_aggregation(n_signatures, cli.log_inv_rate, plan);
        }
        Command::Recursion { n, hashes, iters } => {
            let inner: Vec<(usize, usize)> = (0..n).map(|_| (hashes, iters)).collect();
            rec_aggregation::run_recursion(&inner, cli.log_inv_rate, cli.tracing, plan);
        }
        Command::Fibonacci { n } => {
            if cli.tracing {
                primitives::init_tracing();
            }
            rec_aggregation::run_fibonacci(n, cli.log_inv_rate, plan);
        }
    }
}
