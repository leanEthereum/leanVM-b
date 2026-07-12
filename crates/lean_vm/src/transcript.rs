//! The shared Fiat–Shamir transcript, concretized with the Ligerito opening
//! type (see [`fiat_shamir`] for the sponge and the wrapper states): flock's
//! protocol functions take these same `ps`/`vs` states, so the whole stack
//! shares ONE transcript.
pub use ::pcs::{Proof, ProverState, VerifierState};
pub use fiat_shamir::sponge::{Sponge, TraceOp, trace_start, trace_take};
pub use fiat_shamir::transcript::Error;
