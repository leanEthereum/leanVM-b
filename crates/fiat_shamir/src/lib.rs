//! The shared Fiat–Shamir layer: the VM-native [`sponge::Sponge`], the
//! [`transcript`] wrapper states (`ProverState`/`VerifierState`) that pair it
//! with the proof transport channels, and the [`merkle`] data those channels
//! carry.

pub mod merkle;
pub mod sponge;
pub mod transcript;
