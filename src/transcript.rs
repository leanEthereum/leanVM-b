//! Fiat–Shamir transcript: re-exported from [`flare::transcript`], where the
//! wrapper states live alongside the [`flare::sponge`] they drive — flock's
//! protocol functions take these same `ps`/`vs` states, so the whole stack
//! (leanVM protocol, flock reduction, Ligerito PCS) shares ONE transcript.
pub use flare::sponge::{Sponge, TraceOp, trace_start, trace_take};
pub use flare::transcript::{Error, Proof, ProverState, VerifierState};
