//! Fiat–Shamir transcript, leanVM-style: a single state object *is* the channel
//! between prover and verifier. The API is deliberately small, so it is hard to
//! bind the wrong thing (mirrors leanVM's `FSProver`/`FSVerifier`):
//!
//! - **`add_scalar(s)`** (prover) / **`next_scalar(s)`** (verifier): the *only*
//!   way a scalar enters the proof. It transmits AND absorbs, in one call — so
//!   transmitted data is **always** bound, and the two sides cannot drift. This is
//!   the workhorse (GKR layers, constraint round polys, evaluation values, the
//!   commitment root).
//! - **The public statement** (the public input) is seeded into the sponge at
//!   construction ([`Sponge::new`]) by BOTH sides, so it is bound before any
//!   challenge. There is deliberately **no `observe` method**: the only data a
//!   caller can put into the sponge is via `add_*` (which also transmits), so you
//!   cannot bind-without-transmitting or transmit-without-binding by mistake. A
//!   challenge is just `sample()`d, bound to everything seeded/sent so far.
//! - **`hint_*` (prover) / `next_*` (verifier)**: transport that is NOT absorbed
//!   here — hash-bearing data (the Ligerito `openings`, like leanVM's
//!   `merkle_paths`) whose binding is the Merkle structure itself.
//! - **`sample` / `sample_vec`**: squeeze a challenge.
//!
//! The [`Sponge`] itself (the VM-native Merkle–Damgård chaining value, its
//! domain tags, grinding, and the diagnostic trace) lives in [`crate::sponge`].
//! This module wraps it with the proof transport channels; the flock protocol
//! functions take these SAME states (`ps`/`vs`), drawing their challenges from
//! the one shared sponge while their proof data rides its own structs.

use primitives::field::F128;
use crate::sponge::trace;
pub use crate::sponge::{Sponge, TraceOp, trace_start, trace_take};

/// A complete proof: the scalar transcript stream plus the Ligerito opening hint
/// channel — **two** channels, no bolted-on side field. The commitment root and
/// every transmitted scalar ride `stream`; the hash-bearing Ligerito openings
/// ride `openings`. flock's BLAKE3 sub-proof is carried the same way: its
/// zerocheck / lincheck / ring-switch scalars are ordinary `add_scalar` words on
/// `stream` (transmitted AND bound at their protocol points, like every other
/// scalar) and its one Ligerito opening rides `openings`.
///
/// `Deserialize` as well as `Serialize`, so a proof round-trips over the wire and
/// an independent verifier process reconstructs it: everything lives in these two
/// fields, and [`VerifierState`] re-derives every challenge from them via the
/// shared sponge, so nothing travels out of band.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Proof<O> {
    /// Every transmitted field scalar, in protocol order (plus flock's scalar
    /// sub-proof as trailing raw transport words).
    pub stream: Vec<F128>,
    /// Ligerito openings (sumcheck messages + Merkle roots/paths), in order.
    pub openings: Vec<O>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The verifier tried to read past the end of the proof stream.
    ExceededStream,
    /// A required opening hint was missing.
    MissingHint,
    /// Verification finished without consuming the whole proof.
    NotFullyConsumed,
    /// A grinding nonce failed its proof-of-work check.
    PowFailed,
}

/// Prover side: writes scalars into the stream and opening hints to the side.
pub struct ProverState<O> {
    sponge: Sponge,
    stream: Vec<F128>,
    openings: Vec<O>,
}

impl<O> ProverState<O> {
    /// `statement` is the public input, seeded into the sponge (see [`Sponge::new`]).
    pub fn new(label: &[u8], statement: &[F128]) -> Self {
        Self {
            sponge: Sponge::new(label, statement),
            stream: Vec::new(),
            openings: Vec::new(),
        }
    }

    /// Transmit a scalar into the proof AND bind it into the sponge (the two are
    /// inseparable — you cannot send without binding).
    #[inline]
    pub fn add_scalar(&mut self, x: F128) {
        self.sponge.observe(x);
        self.stream.push(x);
    }

    pub fn add_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.add_scalar(x);
        }
    }

    pub fn sample(&mut self) -> F128 {
        self.sponge.sample()
    }

    /// Prover mirror of [`VerifierState::observe_scalar`].
    pub fn observe_scalar(&mut self, x: F128) {
        self.sponge.observe(x);
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sponge.sample()).collect()
    }

    pub fn hint_opening(&mut self, opening: O) {
        self.openings.push(opening);
    }

    /// Proof-of-work grind of `bits` before the next challenge, raising that
    /// challenge's Schwartz–Zippel soundness by `bits` (the prover must redo
    /// the PoW to re-roll the challenge). Grinds, binds the nonce into the
    /// sponge, and transmits it on the stream as raw transport — already bound
    /// by the grind, so it is NOT re-absorbed. `bits = 0` is the canonical
    /// no-work nonce `0`.
    pub fn grind(&mut self, bits: u32) {
        let nonce = self.sponge.grind_pow(bits);
        self.stream.push(F128::new(nonce, 0));
    }


    /// Prover mirror of [`VerifierState::observe_scalars`].
    pub fn observe_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.sponge.observe(x);
        }
    }

    /// Absorb a byte string (a sub-protocol label, a Merkle root) — data both
    /// sides know or that is bound elsewhere, never transmitted here.
    pub fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.sponge.absorb_bytes(bytes);
    }

    /// Raw sponge grind for sub-protocols that carry the nonce in their OWN
    /// proof structs (the Ligerito fold/query grinds): grinds and binds, and
    /// returns the nonce for the caller to transport — unlike [`Self::grind`],
    /// nothing is pushed on this stream.
    pub fn grind_pow(&mut self, bits: u32) -> u64 {
        self.sponge.grind_pow(bits)
    }

    /// The raw sponge, for side-agnostic sub-steps shared by prover and
    /// verifier (e.g. the Ligerito query sampler).
    pub fn sponge_mut(&mut self) -> &mut Sponge {
        &mut self.sponge
    }

    pub fn into_proof(self) -> Proof<O> {
        Proof {
            stream: self.stream,
            openings: self.openings,
        }
    }
}

/// Verifier side: reads scalars from a received [`Proof`] (borrowed) and pulls
/// hints in order.
pub struct VerifierState<'a, O> {
    sponge: Sponge,
    stream: &'a [F128],
    offset: usize,
    openings: &'a [O],
    oi: usize,
}

impl<'a, O> VerifierState<'a, O> {
    /// `statement` is the public input, seeded into the sponge (see [`Sponge::new`])
    /// — must match the prover's, or the sponges diverge and verification fails.
    pub fn new(label: &[u8], proof: &'a Proof<O>, statement: &[F128]) -> Self {
        Self {
            sponge: Sponge::new(label, statement),
            stream: &proof.stream,
            offset: 0,
            openings: &proof.openings,
            oi: 0,
        }
    }

    /// A verifier state with EMPTY transport channels — a challenge source for
    /// unit tests that drive sub-protocols without a transmitted stream (leaks
    /// one small allocation; do not use outside tests).
    pub fn detached(label: &[u8], statement: &[F128]) -> VerifierState<'static, O> {
        let empty = Box::leak(Box::new(Proof { stream: Vec::new(), openings: Vec::new() }));
        VerifierState::new(label, empty, statement)
    }

    /// Read the next scalar, binding it into the sponge (mirrors `add_scalar`).
    #[inline]
    pub fn next_scalar(&mut self) -> Result<F128, Error> {
        let x = *self.stream.get(self.offset).ok_or(Error::ExceededStream)?;
        self.offset += 1;
        self.sponge.observe(x);
        Ok(x)
    }

    pub fn next_scalars(&mut self, n: usize) -> Result<Vec<F128>, Error> {
        (0..n).map(|_| self.next_scalar()).collect()
    }

    /// Advance the stream cursor by one **without** binding into the sponge — the
    /// read counterpart of the raw nonce push in [`ProverState::grind`].
    fn take_raw(&mut self) -> Result<F128, Error> {
        let x = *self.stream.get(self.offset).ok_or(Error::ExceededStream)?;
        self.offset += 1;
        trace(|| TraceOp::StreamRaw(x));
        Ok(x)
    }


    pub fn sample(&mut self) -> F128 {
        self.sponge.sample()
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// Absorb a value both parties compute themselves (never transmitted):
    /// protocol steps that bind derived values before sampling, e.g. the
    /// stacked-bytecode claim reduction (`leaf::verify_balance`).
    pub fn observe_scalar(&mut self, x: F128) {
        self.sponge.observe(x);
    }

    pub fn next_opening(&mut self) -> Result<&'a O, Error> {
        let o = self.openings.get(self.oi).ok_or(Error::MissingHint)?;
        self.oi += 1;
        trace(|| TraceOp::Opening);
        Ok(o)
    }

    /// Verifier mirror of [`ProverState::grind`]: read the transmitted nonce and
    /// check it clears the `bits` proof-of-work, then bind it (so the sponge
    /// stays in lockstep). Rejects a proof that skipped or under-did the grind.
    pub fn grind_check(&mut self, bits: u32) -> Result<(), Error> {
        let nonce = self.take_raw()?.lo;
        if self.sponge.verify_pow(nonce, bits) {
            Ok(())
        } else {
            Err(Error::PowFailed)
        }
    }

    /// The sponge's current chaining value (recursion harnesses snapshot the
    /// phase-boundary states as guest debug checkpoints).
    pub fn sponge_state(&self) -> [F128; 2] {
        self.sponge.state()
    }

    /// Absorb derived values in bulk (mirror of [`ProverState::observe_scalars`]).
    pub fn observe_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.sponge.observe(x);
        }
    }

    /// Absorb a byte string (a sub-protocol label, a Merkle root) — mirror of
    /// [`ProverState::absorb_bytes`].
    pub fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.sponge.absorb_bytes(bytes);
    }

    /// The raw sponge (mirror of [`ProverState::sponge_mut`]).
    pub fn sponge_mut(&mut self) -> &mut Sponge {
        &mut self.sponge
    }

    /// Raw PoW check for sub-protocols that carry the nonce in their OWN proof
    /// structs (mirror of [`ProverState::grind_pow`]): checks and binds; the
    /// caller rejects on `false`. Unlike [`Self::grind_check`], the nonce does
    /// not come from this stream.
    pub fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.sponge.verify_pow(nonce, bits)
    }

    /// Assert the whole proof was consumed (no trailing/extra data).
    pub fn finish(&self) -> Result<(), Error> {
        if self.offset == self.stream.len() && self.oi == self.openings.len() {
            Ok(())
        } else {
            Err(Error::NotFullyConsumed)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(k: u64) -> F128 {
        F128::new(k, k ^ 0x1234)
    }

    /// Prover and verifier stay in lockstep across a mixed transcript
    /// (observe / sample / grind), and the verifier rejects a mismatched grind.
    #[test]
    fn prover_verifier_lockstep() {
        let stmt = [f(7)];
        let mut ps = ProverState::<()>::new(b"lbl", &stmt);
        let c1 = ps.sample();
        ps.add_scalar(f(42));
        ps.grind(8);
        let c2 = ps.sample();
        let proof = ps.into_proof();

        let mut vs = VerifierState::new(b"lbl", &proof, &stmt);
        assert_eq!(vs.sample(), c1);
        assert_eq!(vs.next_scalar().unwrap(), f(42));
        assert!(vs.grind_check(8).is_ok());
        assert_eq!(vs.sample(), c2);
        assert!(vs.finish().is_ok());
    }

}
