//! Benchmark CLI for the two flagship workloads (plus the Fibonacci demo).
//!
//! ```text
//! cargo run --release -- xmss --n-signatures 820
//! cargo run --release -- recursion --n 2
//! cargo run --release -- fibonacci --n 2000000
//! ```

use clap::Parser;

#[derive(Parser)]
enum Cli {
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

fn main() {
    match Cli::parse() {
        Cli::Xmss { n_signatures } => rec_aggregation::run_xmss_aggregation(n_signatures),
        Cli::Recursion { n, hashes, iters } => {
            let inner: Vec<(usize, usize)> = (0..n).map(|_| (hashes, iters)).collect();
            rec_aggregation::run_recursion(&inner);
        }
        Cli::Fibonacci { n } => rec_aggregation::run_fibonacci(n),
    }
}
