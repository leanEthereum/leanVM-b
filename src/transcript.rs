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
//! Soundness: challenges are BLAKE3 of the whole transcript so far. Every absorb
//! is domain-tagged and length-prefixed (so a field element, a raw integer, and
//! a byte string cannot alias), and every squeeze is ratcheted back in (binding
//! challenge order) under the random-oracle heuristic.

use crate::field::F128;
use flare::challenger::Challenger;
use flare::pcs::ligerito::LigeritoProof;

// Domain tags, so distinct kinds of absorbed data cannot alias.
const TAG_F128: u8 = 0x01;
const TAG_BYTES: u8 = 0x03;
const TAG_SQUEEZE: u8 = 0xFF;
const TAG_RATCHET: u8 = 0xFE;
// PoW base digest, so a grinding challenge can never alias an ordinary squeeze.
const TAG_POW: u8 = 0xFD;

/// `BLAKE3(state_digest || nonce_le)` has at least `bits` leading zero bits —
/// the grinding predicate, byte-identical to flock's `FsChallenger` so the
/// vendored Ligerito's prover/verifier PoW stay in lockstep with our sponge.
#[inline]
fn pow_bits_ok(state_digest: &[u8; 32], nonce: u64, bits: u32) -> bool {
    let mut input = [0u8; 40];
    input[..32].copy_from_slice(state_digest);
    input[32..].copy_from_slice(&nonce.to_le_bytes());
    let h = *blake3::hash(&input).as_bytes();
    let full = (bits / 8) as usize;
    let extra = bits % 8;
    if h[..full].iter().any(|&b| b != 0) {
        return false;
    }
    extra == 0 || (h[full] >> (8 - extra)) == 0
}

/// The BLAKE3-backed Fiat–Shamir sponge shared by both states.
#[derive(Clone)]
struct Sponge {
    h: blake3::Hasher,
}

impl Sponge {
    /// Seed with the domain `label` and the PUBLIC `statement` scalars (the public
    /// input). Both sides seed identically, so the whole statement is bound before
    /// any challenge — there is no mid-protocol "observe public data" step to get
    /// wrong (or forget).
    fn new(label: &[u8], statement: &[F128]) -> Self {
        let mut h = blake3::Hasher::new();
        h.update(b"leanvm-b/transcript/v0");
        let mut s = Self { h };
        s.absorb(TAG_BYTES, label);
        for &x in statement {
            s.observe(x);
        }
        s
    }

    fn absorb(&mut self, tag: u8, bytes: &[u8]) {
        self.h.update(&[tag]);
        self.h.update(&(bytes.len() as u64).to_le_bytes());
        self.h.update(bytes);
    }

    fn observe(&mut self, x: F128) {
        let mut buf = [0u8; 16];
        buf[..8].copy_from_slice(&x.lo.to_le_bytes());
        buf[8..].copy_from_slice(&x.hi.to_le_bytes());
        self.absorb(TAG_F128, &buf);
    }

    fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.absorb(TAG_BYTES, bytes);
    }

    fn sample(&mut self) -> F128 {
        let mut r = self.h.clone();
        r.update(&[TAG_SQUEEZE]);
        let digest = r.finalize();
        let bytes = digest.as_bytes();
        let lo = u64::from_le_bytes(bytes[0..8].try_into().unwrap());
        let hi = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        self.absorb(TAG_RATCHET, &bytes[..16]);
        F128::new(lo, hi)
    }

    /// A 32-byte PoW base digest bound to the current transcript state: clone +
    /// distinct tag + finalize, so it reads the state without mutating the live
    /// sponge and can never alias a `sample` squeeze.
    fn pow_state_digest(&self) -> [u8; 32] {
        let mut r = self.h.clone();
        r.update(&[TAG_POW]);
        *r.finalize().as_bytes()
    }

    /// Prover-side PoW grind (mirrors flock's `FsChallenger::grind_pow`): find the
    /// smallest `u64` nonce whose `BLAKE3(state || nonce)` has `bits` leading zero
    /// bits, then absorb it so later challenges bind to it. `bits = 0` is the
    /// canonical no-work nonce `0`. Parallel search for the larger grinds.
    fn grind_pow(&mut self, bits: u32) -> u64 {
        const PARALLEL_GRIND_MIN_HASHES: u64 = 1 << 13;
        let digest = self.pow_state_digest();
        let nonce = if bits == 0 {
            0
        } else if (1u64 << bits.min(63)) < PARALLEL_GRIND_MIN_HASHES {
            let mut n: u64 = 0;
            loop {
                if pow_bits_ok(&digest, n, bits) {
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
                    .find_first(|&n| pow_bits_ok(&digest, n, bits))
                {
                    break n;
                }
                start = start.saturating_add(block);
            }
        };
        // Absorb the nonce so the transcript binds to it (verifier mirrors).
        self.absorb(TAG_BYTES, &nonce.to_le_bytes());
        nonce
    }

    /// Verifier-side mirror of [`Self::grind_pow`]: check `nonce` clears the
    /// `bits` PoW against the current state, then absorb it regardless (so the
    /// sponge stays byte-identical to an honest prover's — a failed check rejects
    /// at the call site). `bits = 0` accepts only the canonical nonce `0`, which
    /// keeps proofs non-malleable at zero-bit grinding sites.
    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        let digest = self.pow_state_digest();
        let ok = if bits == 0 { nonce == 0 } else { pow_bits_ok(&digest, nonce, bits) };
        self.absorb(TAG_BYTES, &nonce.to_le_bytes());
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

    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sponge.sample()).collect()
    }

    pub fn hint_opening(&mut self, bf: LigeritoProof) {
        self.openings.push(bf);
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
        self.sponge.sample()
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sponge.sample()).collect()
    }

    pub fn next_opening(&mut self) -> Result<&'a LigeritoProof, Error> {
        let o = self.openings.get(self.oi).ok_or(Error::MissingHint)?;
        self.oi += 1;
        Ok(o)
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
    // The verifier mirror: check each grinding nonce (an honest prover's proof
    // stays byte-identical; a forged one that skipped the grind is rejected).
    fn grind_pow(&mut self, bits: u32) -> u64 {
        self.sponge.grind_pow(bits)
    }
    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        self.sponge.verify_pow(nonce, bits)
    }
}
