//! The shared Fiat–Shamir layer: the VM-native [`sponge::Sponge`] and the
//! [`transcript`] wrapper states (`ProverState`/`VerifierState`) that pair it
//! with the proof transport channels. Every protocol in this workspace — the
//! VM's own reductions, flock's zerocheck/lincheck, and the Ligerito PCS —
//! draws its challenges from this one transcript.

pub mod sponge;
pub mod transcript;

pub use sponge::{Sponge, TraceOp, compress, trace, trace_start, trace_take};
pub use transcript::{Error, Proof, ProverState, VerifierState};
