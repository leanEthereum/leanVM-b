//! Fiat–Shamir transcript, leanVM-style: a single state object *is* the channel
//! between prover and verifier.
//!
//! The prover **writes** scalars — `write_scalars` both binds them into the
//! sponge and records them into the proof stream — and the verifier **reads**
//! them back — `next_scalars` binds and advances a cursor. Because both observe
//! the identical sequence, they squeeze identical challenges; nothing crosses
//! between them except the [`Proof`]. Public, non-transmitted data (table shapes,
//! domain labels) is bound with `observe_*`.
//!
//! Field scalars are the whole story for our own sub-protocols (GKR layers,
//! constraint round polynomials, evaluation values). The PCS commitment root and
//! BaseFold opening carry Merkle **hashes**, which are not field scalars, so they
//! ride a side "hint" channel on the [`Proof`] — exactly as leanVM keeps
//! `merkle_paths` outside its scalar transcript. flock's BaseFold drives off the
//! same sponge (challenges only), so the whole proof shares one FS state.
//!
//! Soundness: challenges are BLAKE3 of the whole transcript so far. Every absorb
//! is domain-tagged and length-prefixed (so a field element, a raw integer, and
//! a byte string cannot alias), and every squeeze is ratcheted back in (binding
//! challenge order) under the random-oracle heuristic.

use crate::field::F128;
use flare::challenger::Challenger;
use flare::pcs::basefold::BaseFoldProof;

// Domain tags, so distinct kinds of absorbed data cannot alias.
const TAG_F128: u8 = 0x01;
const TAG_U64: u8 = 0x02;
const TAG_BYTES: u8 = 0x03;
const TAG_SQUEEZE: u8 = 0xFF;
const TAG_RATCHET: u8 = 0xFE;

/// The BLAKE3-backed Fiat–Shamir sponge shared by both states.
#[derive(Clone)]
struct Sponge {
    h: blake3::Hasher,
}

impl Sponge {
    fn new(label: &[u8]) -> Self {
        let mut h = blake3::Hasher::new();
        h.update(b"leanvm-b/transcript/v0");
        let mut s = Self { h };
        s.absorb(TAG_BYTES, label);
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

    fn observe_u64(&mut self, x: u64) {
        self.absorb(TAG_U64, &x.to_le_bytes());
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
}

/// A complete proof: the scalar transcript stream plus the BaseFold opening hint
/// channel. (The commitment root rides the stream as field scalars, like
/// leanVM; only the hash-bearing BaseFold openings are hinted.)
///
/// `Deserialize` as well as `Serialize`, so a proof round-trips over the wire and
/// an independent verifier process can reconstruct it: the whole proof (stream +
/// opening hints + BLAKE3 attachment) lives in these fields, and
/// [`VerifierState`] re-derives every challenge from them via the shared sponge,
/// so nothing extra needs to travel out of band.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Proof {
    /// Every transmitted field scalar, in protocol order.
    pub stream: Vec<F128>,
    /// BaseFold openings (sumcheck/FRI messages + Merkle paths), in order.
    pub openings: Vec<BaseFoldProof>,
    /// flock's BLAKE3 sub-proof (validity + `q_pkd` slot openings), present iff
    /// the program executed ≥1 `BLAKE3`. Its challenges share this transcript's
    /// sponge; its proof data is carried here rather than on `stream`.
    pub blake3: Option<crate::blake3_flock::Blake3Attachment>,
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
    openings: Vec<BaseFoldProof>,
}

impl ProverState {
    pub fn new(label: &[u8]) -> Self {
        Self {
            sponge: Sponge::new(label),
            stream: Vec::new(),
            openings: Vec::new(),
        }
    }

    /// Record a scalar into the proof and bind it into the sponge.
    #[inline]
    pub fn write_scalar(&mut self, x: F128) {
        self.sponge.observe(x);
        self.stream.push(x);
    }

    pub fn write_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.write_scalar(x);
        }
    }

    /// Bind public data without transmitting it.
    pub fn observe_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.sponge.observe(x);
        }
    }

    pub fn observe_u64(&mut self, x: u64) {
        self.sponge.observe_u64(x);
    }

    pub fn sample(&mut self) -> F128 {
        self.sponge.sample()
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sponge.sample()).collect()
    }

    pub fn hint_opening(&mut self, bf: BaseFoldProof) {
        self.openings.push(bf);
    }

    pub fn into_proof(self) -> Proof {
        Proof {
            stream: self.stream,
            openings: self.openings,
            blake3: None,
        }
    }
}

/// Verifier side: reads scalars from a received [`Proof`] (borrowed) and pulls
/// hints in order.
pub struct VerifierState<'a> {
    sponge: Sponge,
    stream: &'a [F128],
    offset: usize,
    openings: &'a [BaseFoldProof],
    oi: usize,
}

impl<'a> VerifierState<'a> {
    pub fn new(label: &[u8], proof: &'a Proof) -> Self {
        Self {
            sponge: Sponge::new(label),
            stream: &proof.stream,
            offset: 0,
            openings: &proof.openings,
            oi: 0,
        }
    }

    /// Read the next scalar, binding it into the sponge (mirrors `write_scalar`).
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

    pub fn observe_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.sponge.observe(x);
        }
    }

    pub fn observe_u64(&mut self, x: u64) {
        self.sponge.observe_u64(x);
    }

    pub fn sample(&mut self) -> F128 {
        self.sponge.sample()
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sponge.sample()).collect()
    }

    pub fn next_opening(&mut self) -> Result<&'a BaseFoldProof, Error> {
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

/// The Fiat–Shamir surface shared by both transcripts: absorb public data and
/// draw a challenge. Lets prover and verifier share binding code as ordinary
/// generic functions rather than duck-typed macros.
pub trait Absorb {
    fn observe_u64(&mut self, x: u64);
    fn observe_scalars(&mut self, xs: &[F128]);
    fn sample(&mut self) -> F128;
}

impl Absorb for ProverState {
    fn observe_u64(&mut self, x: u64) {
        self.sponge.observe_u64(x);
    }
    fn observe_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.sponge.observe(x);
        }
    }
    fn sample(&mut self) -> F128 {
        self.sponge.sample()
    }
}

impl Absorb for VerifierState<'_> {
    fn observe_u64(&mut self, x: u64) {
        self.sponge.observe_u64(x);
    }
    fn observe_scalars(&mut self, xs: &[F128]) {
        for &x in xs {
            self.sponge.observe(x);
        }
    }
    fn sample(&mut self) -> F128 {
        self.sponge.sample()
    }
}

// flock's PCS drives off the sponge for its challenges; its proof data rides the
// hint channel, so the `Challenger` ops only touch the sponge (never the stream).
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
}
