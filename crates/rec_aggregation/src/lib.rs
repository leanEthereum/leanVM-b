//! Benchmark harnesses for the two flagship workloads: in-VM XMSS aggregation
//! and N→1 recursive proof aggregation. Both compile a zkDSL guest
//! (`guests/*.py`), prove it, verify the proof, and print a report; the
//! `#[cfg(test)]` suites in each module drive the same entry points.

pub mod fibonacci;
// The n→1 recursion harness builds the guest's hint streams by dissecting the
// proof stream word-for-word, so it is bound to the 128-bit-word protocol it
// was written against. Under the 64-bit machine (every `E`-scalar spans TWO
// memory words, the sponge state is four `F64` words, the opening is the
// stacked Ligerito-K) both the harness and `guests/recursion.py` need the
// field port before they can run — gated off rather than half-retyped, since
// a mechanically retyped harness would compile and silently emit wrong hints.
#[cfg(feature = "recursion")]
pub mod recursion;
pub mod signers_cache;
pub mod xmss_aggregation;

pub use fibonacci::run_fibonacci;
#[cfg(feature = "recursion")]
pub use recursion::run_recursion;
pub use xmss_aggregation::run_xmss_aggregation;

/// Placeholder for the gated [`recursion`] harness (see the module note): the
/// CLI keeps its `recursion` subcommand, failing loudly instead of silently
/// aggregating with stale 128-bit-word hints.
#[cfg(not(feature = "recursion"))]
pub fn run_recursion(_inner: &[(usize, usize)]) {
    unimplemented!(
        "the n→1 recursion harness awaits the 64-bit guest port \
         (crates/rec_aggregation/src/recursion.rs, feature `recursion`)"
    );
}
