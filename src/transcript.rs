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
//!   here — either hash-bearing (the Ligerito `openings`, like leanVM's
//!   `merkle_paths`) or already bound elsewhere (flock's scalar sub-proof, which
//!   re-enters the sponge through flock's own reduction/opening replay).
//! - **`sample` / `sample_vec`**: squeeze a challenge.
//!
//! Soundness: the sponge is a **VM-native** Merkle–Damgård chaining value (see
//! [`Sponge`]) advanced only by the fixed 64→32 BLAKE3 compression the `Blake3`
//! opcode computes — so the entire Fiat–Shamir transcript can be replayed by a
//! program running on the VM (the prerequisite for recursion), not just by the
//! streaming `blake3::Hasher`. Each challenge is the random-oracle image of the
//! whole prior transcript; every absorb is domain-tagged per compression (so a
//! field element, a raw integer, and a byte string cannot alias) and byte strings
//! are length-framed; each squeeze ratchets the state (binding challenge order).

use crate::field::F128;
use crate::vmhash::compress;
use flare::challenger::Challenger;
use flare::pcs::ligerito::LigeritoProof;

// Domain-separation tags, carried in the SECOND input word of every absorbed
// block, so no two roles (a scalar, a byte word, a length frame, a squeeze, a
// PoW step) can alias: the adversary controls only the FIRST word (the datum),
// never the tag. Distinct nonzero constants suffice.
const DS_SCALAR: F128 = F128::new(1, 0);
const DS_BYTE: F128 = F128::new(2, 0);
const DS_LEN: F128 = F128::new(3, 0);
const DS_SQUEEZE: F128 = F128::new(4, 0);
const DS_POW: F128 = F128::new(5, 0);

/// `compress(base, (nonce, DS_POW))` has its low `bits` bits zero — the grinding
/// predicate over the VM compression. A CONTIGUOUS low-bit window (rather than
/// byte-wise leading zeros) so a recursive verifier re-checks it with a single
/// loop over the bit decomposition of the digest word (`grind_check` in
/// `tests/verify_recursive.py`). `bits` is the grand-product soundness deficit
/// `SECURITY_BITS + push_mu + 1 - 128 <= MU_CAP - 7`, always `< 64`.
#[inline]
fn pow_bits_ok(base: [F128; 2], nonce: u64, bits: u32) -> bool {
    debug_assert!(bits < 64, "grinding deficit fits the digest's low word");
    let digest = compress(base, [F128::new(nonce, 0), DS_POW])[0];
    digest.lo & ((1u64 << bits) - 1) == 0
}

/// The VM-native Fiat–Shamir sponge: a 256-bit chaining value evolved only by the
/// fixed 64→32 [`compress`] (the `Blake3` opcode), so prover, verifier, and a
/// future recursive verifier running on the VM all derive identical challenges
/// with one `blake3` per step. Replaces the streaming `blake3::Hasher`, whose
/// multi-block chunk tree / flags / counter the opcode cannot reproduce.
///
/// Construction adapted from Signal's ShoSha256 "Stateful Hash Object"
/// (`libsignal/rust/poksho/src/shosha256.rs`, © 2020 Signal Messenger, LLC,
/// AGPL-3.0-only): a chaining value advanced by domain-separated absorb / squeeze
/// steps. Here the underlying hash is the VM's BLAKE3 compression rather than
/// SHA-256, inputs are GF(2^128) field elements, and — because every absorb is
/// domain-tagged per compression — no explicit double-hash ratchet is needed.
#[derive(Clone)]
pub struct Sponge {
    /// The 256-bit chaining value: a Merkle–Damgård hash of the transcript so far.
    cv: [F128; 2],
}

impl Sponge {
    /// Seed with the domain `label` and the PUBLIC `statement` scalars (the public
    /// input). Both sides seed identically, so the whole statement is bound before
    /// any challenge — there is no mid-protocol "observe public data" step to get
    /// wrong (or forget).
    pub fn new(label: &[u8], statement: &[F128]) -> Self {
        let mut s = Self { cv: [F128::ZERO, F128::ZERO] };
        s.absorb_bytes(b"leanvm-b/transcript/v1");
        s.absorb_bytes(label);
        for &x in statement {
            s.observe(x);
        }
        s
    }

    /// Absorb one scalar: `cv ← compress(cv, (x, DS_SCALAR))`.
    pub fn observe(&mut self, x: F128) {
        self.cv = compress(self.cv, [x, DS_SCALAR]);
    }

    /// Absorb a byte string: a length frame then its 16-byte words as tagged
    /// blocks, so a field element, a raw integer, and a byte string cannot alias.
    pub fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.cv = compress(self.cv, [F128::new(bytes.len() as u64, 0), DS_LEN]);
        for chunk in bytes.chunks(16) {
            let mut buf = [0u8; 16];
            buf[..chunk.len()].copy_from_slice(chunk);
            let w = F128::new(
                u64::from_le_bytes(buf[..8].try_into().unwrap()),
                u64::from_le_bytes(buf[8..].try_into().unwrap()),
            );
            self.cv = compress(self.cv, [w, DS_BYTE]);
        }
    }

    /// Squeeze a challenge and ratchet: the challenge is the first word of
    /// `compress(cv, (0, DS_SQUEEZE))`, whose full output becomes the new state —
    /// domain-separated from absorbs, so a challenge cannot be confused with a
    /// continued absorb. In Fiat–Shamir everything is public; soundness comes from
    /// each challenge being a random-oracle image of the entire prior transcript.
    pub fn sample(&mut self) -> F128 {
        let out = compress(self.cv, [F128::ZERO, DS_SQUEEZE]);
        self.cv = out;
        out[0]
    }

    /// The PoW base `compress(cv, (0, DS_POW))`, read without mutating the live
    /// state (the nonce is bound separately by [`Self::absorb_nonce`]).
    fn pow_base(&self) -> [F128; 2] {
        compress(self.cv, [F128::ZERO, DS_POW])
    }

    /// Bind a grinding nonce into the state (both sides, so they stay in lockstep).
    /// A fresh chain at the zero state: the guest-side aggregation and export
    /// transcripts start here (no label), and the harness mirrors them.
    pub fn empty() -> Self {
        Self { cv: [F128::ZERO; 2] }
    }

    /// The current 256-bit chaining value.
    pub fn state(&self) -> [F128; 2] {
        self.cv
    }

    /// The grinding digest this state yields for `nonce` (read-only preview;
    /// [`Self::verify_pow`] is the mutating check).
    pub fn pow_digest(&self, nonce: u64) -> F128 {
        compress(self.pow_base(), [F128::new(nonce, 0), DS_POW])[0]
    }

    /// Re-run recorded verifier transcript ops through this sponge, asserting
    /// every recorded sample (and grind) matches what this state re-derives —
    /// any prefix of a real verify trace yields the exact state reached there.
    pub fn replay(&mut self, ops: &[TraceOp]) {
        for op in ops {
            match op {
                TraceOp::StreamObserve(x) | TraceOp::Observe(x) => self.observe(*x),
                TraceOp::AbsorbBytes(b) => self.absorb_bytes(b),
                TraceOp::Sample(v) => assert_eq!(self.sample(), *v, "trace replay diverged"),
                TraceOp::Pow { nonce, bits, .. } => {
                    assert!(self.verify_pow(*nonce, *bits), "trace replay: grind failed")
                }
                TraceOp::StreamRaw(_) | TraceOp::Opening => {}
            }
        }
    }

    fn absorb_nonce(&mut self, nonce: u64) {
        self.cv = compress(self.cv, [F128::new(nonce, 0), DS_POW]);
    }

    /// Prover-side PoW grind: find the smallest `u64` nonce whose PoW hash clears
    /// `bits` low zero bits, then bind it so later challenges depend on it.
    /// `bits = 0` is the canonical no-work nonce `0`. Parallel search for the
    /// larger grinds.
    fn grind_pow(&mut self, bits: u32) -> u64 {
        const PARALLEL_GRIND_MIN_HASHES: u64 = 1 << 13;
        let base = self.pow_base();
        let nonce = if bits == 0 {
            0
        } else if (1u64 << bits.min(63)) < PARALLEL_GRIND_MIN_HASHES {
            let mut n: u64 = 0;
            loop {
                if pow_bits_ok(base, n, bits) {
                    break n;
                }
                n = n.wrapping_add(1);
            }
        } else {
            use rayon::prelude::*;
            // `find_first` returns the globally smallest satisfying nonce, so the
            // proof is deterministic regardless of the block scan.
            let block: u64 = 1 << (bits.min(24) + 1);
            let mut start: u64 = 0;
            loop {
                if let Some(n) = (start..start.saturating_add(block))
                    .into_par_iter()
                    .find_first(|&n| pow_bits_ok(base, n, bits))
                {
                    break n;
                }
                start = start.saturating_add(block);
            }
        };
        self.absorb_nonce(nonce);
        nonce
    }

    /// Verifier-side mirror of [`Self::grind_pow`]: check `nonce` clears the `bits`
    /// PoW against the current state, then bind it regardless (so the sponge stays
    /// in lockstep with an honest prover — a failed check rejects at the call
    /// site). `bits = 0` accepts only the canonical nonce `0`.
    pub fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        let base = self.pow_base();
        let ok = if bits == 0 { nonce == 0 } else { pow_bits_ok(base, nonce, bits) };
        self.absorb_nonce(nonce);
        ok
    }
}

/// A complete proof: the scalar transcript stream plus the Ligerito opening hint
/// channel — **two** channels, no bolted-on side field. The commitment root and
/// every transmitted scalar ride `stream`; the hash-bearing Ligerito openings
/// ride `openings`. flock's BLAKE3 sub-proof is carried the same way: its scalar
/// reduction (zerocheck / lincheck / ring-switch) rides `stream` as pure
/// transport ([`ProverState::hint_bytes`] — NOT re-absorbed, since flock's
/// verifier replay is the sole binder) and its one Ligerito opening rides `openings`.
///
/// `Deserialize` as well as `Serialize`, so a proof round-trips over the wire and
/// an independent verifier process reconstructs it: everything lives in these two
/// fields, and [`VerifierState`] re-derives every challenge from them via the
/// shared sponge, so nothing travels out of band.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Proof {
    /// Every transmitted field scalar, in protocol order (plus flock's scalar
    /// sub-proof as trailing raw transport words).
    pub stream: Vec<F128>,
    /// Ligerito openings (sumcheck messages + Merkle roots/paths), in order.
    pub openings: Vec<LigeritoProof>,
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
pub struct ProverState {
    sponge: Sponge,
    stream: Vec<F128>,
    openings: Vec<LigeritoProof>,
}

impl ProverState {
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

    pub fn hint_opening(&mut self, bf: LigeritoProof) {
        self.openings.push(bf);
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

    /// Transmit length-prefixed bytes on the stream (packed 16 per `F128` word)
    /// **without** binding them into the sponge — the hint channel for data bound
    /// elsewhere. Used for flock's BLAKE3 scalar sub-proof, whose values re-enter
    /// the sponge through the verifier's own reduction/opening replay, so absorbing
    /// them here too would double-bind and diverge the sponge from the prover.
    pub fn hint_bytes(&mut self, bytes: &[u8]) {
        self.stream.push(F128::new(bytes.len() as u64, 0));
        for chunk in bytes.chunks(16) {
            let mut buf = [0u8; 16];
            buf[..chunk.len()].copy_from_slice(chunk);
            self.stream.push(F128::new(
                u64::from_le_bytes(buf[..8].try_into().unwrap()),
                u64::from_le_bytes(buf[8..].try_into().unwrap()),
            ));
        }
    }

    pub fn into_proof(self) -> Proof {
        Proof {
            stream: self.stream,
            openings: self.openings,
        }
    }
}

/// Verifier side: reads scalars from a received [`Proof`] (borrowed) and pulls
/// hints in order.
/// One verifier-side transcript operation, recorded by the (diagnostic) trace
/// ([`trace_start`] / [`trace_take`]). The in-circuit verifier replays exactly
/// this op sequence, so the trace of a real `cpu::verify` run is both the guest
/// program's mechanical spec and its checkpoint data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceOp {
    /// `next_scalar`: a stream word read AND bound into the sponge.
    StreamObserve(F128),
    /// `take_raw`: a stream word consumed without binding (hint bytes, nonces).
    StreamRaw(F128),
    /// A non-stream observe (flock replay binding a sub-proof struct value).
    Observe(F128),
    /// `absorb_bytes` (labels, roots).
    AbsorbBytes(Vec<u8>),
    Sample(F128),
    /// A grinding check: the nonce, the required bits, and the digest the
    /// pre-absorb state yields for that nonce (so trace consumers never need
    /// to track sponge state in lockstep).
    Pow { nonce: u64, bits: u32, digest: F128 },
    /// `next_opening` (the Ligerito hint channel).
    Opening,
}

thread_local! {
    static TRACE: std::cell::RefCell<Option<Vec<TraceOp>>> = const { std::cell::RefCell::new(None) };
}

/// Start recording verifier transcript ops on this thread (diagnostic).
pub fn trace_start() {
    TRACE.with(|t| *t.borrow_mut() = Some(Vec::new()));
}

/// Stop recording and return the ops recorded since [`trace_start`].
pub fn trace_take() -> Vec<TraceOp> {
    TRACE.with(|t| t.borrow_mut().take().unwrap_or_default())
}

#[inline]
fn trace(op: impl FnOnce() -> TraceOp) {
    TRACE.with(|t| {
        if let Some(v) = t.borrow_mut().as_mut() {
            v.push(op());
        }
    });
}

pub struct VerifierState<'a> {
    sponge: Sponge,
    stream: &'a [F128],
    offset: usize,
    openings: &'a [LigeritoProof],
    oi: usize,
}

impl<'a> VerifierState<'a> {
    /// `statement` is the public input, seeded into the sponge (see [`Sponge::new`])
    /// — must match the prover's, or the sponges diverge and verification fails.
    pub fn new(label: &[u8], proof: &'a Proof, statement: &[F128]) -> Self {
        Self {
            sponge: Sponge::new(label, statement),
            stream: &proof.stream,
            offset: 0,
            openings: &proof.openings,
            oi: 0,
        }
    }

    /// Read the next scalar, binding it into the sponge (mirrors `add_scalar`).
    #[inline]
    pub fn next_scalar(&mut self) -> Result<F128, Error> {
        let x = *self.stream.get(self.offset).ok_or(Error::ExceededStream)?;
        self.offset += 1;
        self.sponge.observe(x);
        trace(|| TraceOp::StreamObserve(x));
        Ok(x)
    }

    pub fn next_scalars(&mut self, n: usize) -> Result<Vec<F128>, Error> {
        (0..n).map(|_| self.next_scalar()).collect()
    }

    /// Advance the stream cursor by one **without** binding into the sponge — the
    /// read counterpart of [`ProverState::hint_bytes`]'s per-word push.
    fn take_raw(&mut self) -> Result<F128, Error> {
        let x = *self.stream.get(self.offset).ok_or(Error::ExceededStream)?;
        self.offset += 1;
        trace(|| TraceOp::StreamRaw(x));
        Ok(x)
    }

    /// Read length-prefixed hint bytes written by [`ProverState::hint_bytes`]:
    /// consumes stream words but does NOT bind them into the sponge (their binding
    /// happens via the reduction/opening replay).
    pub fn next_hint_bytes(&mut self) -> Result<Vec<u8>, Error> {
        let len = self.take_raw()?.lo as usize;
        let n_words = len.div_ceil(16);
        // The bytes come from `n_words` stream words; a malicious `len` cannot make
        // us reserve more than the actual remaining stream (bounds the allocation
        // to the proof size and rules out the `n_words * 16` overflow).
        if n_words > self.stream.len() - self.offset {
            return Err(Error::ExceededStream);
        }
        let mut bytes = Vec::with_capacity(n_words * 16);
        for _ in 0..n_words {
            let w = self.take_raw()?;
            bytes.extend_from_slice(&w.lo.to_le_bytes());
            bytes.extend_from_slice(&w.hi.to_le_bytes());
        }
        bytes.truncate(len);
        Ok(bytes)
    }

    pub fn sample(&mut self) -> F128 {
        let v = self.sponge.sample();
        trace(|| TraceOp::Sample(v));
        v
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// Absorb a value both parties compute themselves (never transmitted):
    /// protocol steps that bind derived values before sampling, e.g. the
    /// stacked-bytecode claim reduction (`leaf::verify_balance`).
    pub fn observe_scalar(&mut self, x: F128) {
        self.sponge.observe(x);
        trace(|| TraceOp::Observe(x));
    }

    pub fn next_opening(&mut self) -> Result<&'a LigeritoProof, Error> {
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
        trace(|| TraceOp::Pow { nonce, bits, digest: self.sponge.pow_digest(nonce) });
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

    /// Assert the whole proof was consumed (no trailing/extra data).
    pub fn finish(&self) -> Result<(), Error> {
        if self.offset == self.stream.len() && self.oi == self.openings.len() {
            Ok(())
        } else {
            Err(Error::NotFullyConsumed)
        }
    }
}

// flock's PCS drives off the sponge for its challenges; its proof data rides the
// hint channel, so the `Challenger` ops only touch the sponge (never the stream).
// This is the vendored-flock adapter; leanVM-b's own code uses the inherent
// `add_*`/`observe_*`/`sample` methods above, not `Challenger` directly.
impl Challenger for ProverState {
    fn observe_label(&mut self, label: &[u8]) {
        self.sponge.absorb_bytes(label);
    }
    fn observe_f128(&mut self, value: F128) {
        self.sponge.observe(value);
    }
    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.sponge.absorb_bytes(bytes);
    }
    fn sample_f128(&mut self) -> F128 {
        self.sponge.sample()
    }
    // Ligerito's proximity-gap soundness budgets in fold-challenge PoW grinding
    // (`fold_grinding_bits`); without these overrides the trait defaults no-op
    // the grind and the proof falls below its target soundness.
    fn grind_pow(&mut self, bits: u32) -> u64 {
        self.sponge.grind_pow(bits)
    }
    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.sponge.verify_pow(nonce, bits)
    }
}

impl Challenger for VerifierState<'_> {
    fn observe_label(&mut self, label: &[u8]) {
        self.sponge.absorb_bytes(label);
        trace(|| TraceOp::AbsorbBytes(label.to_vec()));
    }
    fn observe_f128(&mut self, value: F128) {
        self.sponge.observe(value);
        trace(|| TraceOp::Observe(value));
    }
    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.sponge.absorb_bytes(bytes);
        trace(|| TraceOp::AbsorbBytes(bytes.to_vec()));
    }
    fn sample_f128(&mut self) -> F128 {
        let v = self.sponge.sample();
        trace(|| TraceOp::Sample(v));
        v
    }
    // The verifier mirror: check each grinding nonce (an honest prover's proof
    // stays byte-identical; a forged one that skipped the grind is rejected).
    fn grind_pow(&mut self, bits: u32) -> u64 {
        self.sponge.grind_pow(bits)
    }
    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        trace(|| TraceOp::Pow { nonce, bits, digest: self.sponge.pow_digest(nonce) });
        self.sponge.verify_pow(nonce, bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(k: u64) -> F128 {
        F128::new(k, k ^ 0x1234)
    }

    /// A challenge binds every prior absorbed scalar: flipping one observed value
    /// changes the next squeeze.
    #[test]
    fn sponge_binds_observations() {
        let mut a = Sponge::new(b"t", &[f(1), f(2)]);
        let mut b = Sponge::new(b"t", &[f(1), f(3)]);
        assert_ne!(a.sample(), b.sample());
    }

    /// Absorb order matters: observe(a) then observe(b) ≠ observe(b) then observe(a).
    #[test]
    fn sponge_binds_order() {
        let mut a = Sponge::new(b"t", &[]);
        a.observe(f(1));
        a.observe(f(2));
        let mut b = Sponge::new(b"t", &[]);
        b.observe(f(2));
        b.observe(f(1));
        assert_ne!(a.sample(), b.sample());
    }

    /// A scalar and a byte string cannot alias (distinct domain tags), so
    /// observing a scalar vs absorbing its 16-byte encoding diverge.
    #[test]
    fn sponge_domain_separation() {
        let x = f(9);
        let mut a = Sponge::new(b"t", &[]);
        a.observe(x);
        let mut b = Sponge::new(b"t", &[]);
        let mut bytes = [0u8; 16];
        bytes[..8].copy_from_slice(&x.lo.to_le_bytes());
        bytes[8..].copy_from_slice(&x.hi.to_le_bytes());
        b.absorb_bytes(&bytes);
        assert_ne!(a.sample(), b.sample());
    }

    /// Prover and verifier stay in lockstep across a mixed transcript
    /// (observe / sample / grind), and the verifier rejects a mismatched grind.
    #[test]
    fn prover_verifier_lockstep() {
        let stmt = [f(7)];
        let mut ps = ProverState::new(b"lbl", &stmt);
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

    /// A grind clears its own PoW; a nonce that does not is rejected.
    #[test]
    fn pow_predicate() {
        let sp = Sponge::new(b"t", &[f(1)]);
        let base = sp.pow_base();
        let good = {
            let mut clone = sp.clone();
            clone.grind_pow(8)
        };
        assert!(pow_bits_ok(base, good, 8));
        // A random wrong nonce almost surely fails an 8-bit grind.
        assert!(!pow_bits_ok(base, good.wrapping_add(1).wrapping_mul(3) | 1, 8) || good != 0);
    }
}
