//! The shared Fiat-Shamir transcript (see [`fiat_shamir`] for the sponge and
//! the wrapper states): flock's protocol functions take these same `ps`/`vs`
//! states, so the whole stack shares ONE transcript. Scalars ride its stream;
//! the stacked opening's Merkle data rides its opening phases.
pub use fiat_shamir::sponge::{Sponge, TraceOp, trace_start, trace_take};
pub use fiat_shamir::transcript::{Challenger, Error, Receiver, Transmitter};

pub type Proof = fiat_shamir::transcript::Proof;
pub type ProverState = fiat_shamir::transcript::ProverState;
pub type VerifierState<'a> = fiat_shamir::transcript::VerifierState<'a>;
