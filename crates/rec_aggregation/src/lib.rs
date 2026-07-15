//! Benchmark harnesses for the two flagship workloads: in-VM XMSS aggregation
//! and N→1 recursive proof aggregation. Both compile a zkDSL guest
//! (`guests/*.py`), prove it, verify the proof, and print a report; the
//! `#[cfg(test)]` suites in each module drive the same entry points.

pub mod fibonacci;
// The n→1 recursion harness dissects the proof stream word-for-word to build the
// guest's hint streams. It is fully ported to the K-committed machine (each
// extension scalar is one 128-bit memory word / two committed K lanes, the
// sponge state is four `F64` lanes, and the opening is stacked Ligerito-K), and
// the guest (`guests/recursion.py`)
// replays the single-field tower verifier. Verified end-to-end by
// `recursion_2to1` (honest proofs accept) and `recursion_soundness_binds`
// (tampered hints reject).
pub mod recursion;
pub mod signers_cache;
pub mod xmss_aggregation;

pub use fibonacci::run_fibonacci;
pub use recursion::{RecursiveProof, RecursiveVerifyError, run_recursion};
pub use xmss_aggregation::run_xmss_aggregation;
