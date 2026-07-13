//! The shared Fiat–Shamir transcript, concretized with the VM's stacked
//! Ligerito-K opening type (see [`fiat_shamir`] for the sponge and the wrapper
//! states): flock's protocol functions take these same `ps`/`vs` states, so
//! the whole stack shares ONE transcript.
pub use fiat_shamir::sponge::{Sponge, TraceOp, trace_start, trace_take};
pub use fiat_shamir::transcript::Error;

/// The one hash-bearing artifact on the `openings` channel: the batched
/// stacked opening (its ring-switch messages + ONE Ligerito-K proof).
pub type Opening = ::pcs::stack_open_k::BatchOpeningProofK;

pub type Proof = fiat_shamir::transcript::Proof<Opening>;
pub type ProverState = fiat_shamir::transcript::ProverState<Opening>;
pub type VerifierState<'a> = fiat_shamir::transcript::VerifierState<'a, Opening>;
