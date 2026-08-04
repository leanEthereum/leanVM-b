//! Benchmark harnesses for the three workloads: Fibonacci in the exponent,
//! in-VM XMSS aggregation, and N→1 recursive proof aggregation. Each compiles a
//! zkDSL guest (`guests/*.py`), proves it, verifies the proof, and prints a
//! report; the `#[cfg(test)]` suites in each module drive the same entry points.

pub mod fibonacci;
pub mod recursion;
pub mod signers_cache;
pub mod xmss_aggregation;

pub use fibonacci::run_fibonacci;
pub use recursion::{RecursiveProof, RecursiveVerifyError, run_recursion};
pub use xmss_aggregation::run_xmss_aggregation;

/// The pieces every workload's benchmark report ends with.
///
/// Each caller drops its root tracing span before printing: tracing-forest
/// renders its tree only when that span closes, so the complete trace has to be
/// flushed above the report.
mod report {
    use primitives::pretty_f64;

    /// A count as a power of two, or a dash when the opcode never ran.
    pub fn pow(x: usize) -> String {
        if x == 0 {
            "     -".into()
        } else {
            format!("2^{}", pretty_f64((x as f64).log2()))
        }
    }

    /// Peak resident set size, in GiB.
    pub fn peak_gib() -> String {
        pretty_f64(primitives::bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    }

    pub fn print_proof_size<T: serde::Serialize>(proof: &T) {
        let bytes = bincode::serialized_size(proof).expect("proof is serializable");
        println!("  proof size                  : {:.1} KiB", bytes as f64 / 1024.0);
    }
}
