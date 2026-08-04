//! The shared Fiat–Shamir layer: the VM-native [`sponge::Sponge`] and the
//! [`transcript`] wrapper states (`ProverState`/`VerifierState`) that pair it
//! with the proof transport channels.

pub mod sponge;
pub mod transcript;
