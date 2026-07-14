//! Benchmark harnesses for the two flagship workloads: in-VM XMSS aggregation
//! and N→1 recursive proof aggregation. Both compile a zkDSL guest
//! (`guests/*.py`), prove it, verify the proof, and print a report; the
//! `#[cfg(test)]` suites in each module drive the same entry points.

pub mod fibonacci;
pub mod recursion;
pub mod signers_cache;
pub mod xmss_aggregation;

pub use fibonacci::run_fibonacci;
pub use recursion::{RecursiveProof, RecursiveVerifyError, run_recursion};
pub use xmss_aggregation::run_xmss_aggregation;
