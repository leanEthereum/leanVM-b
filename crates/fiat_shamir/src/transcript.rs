//! Fiat–Shamir transcript, leanVM-style: a single state object *is* the channel
//! between prover and verifier. The API is deliberately small, so it is hard to
//! bind the wrong thing (mirrors leanVM's `FSProver`/`FSVerifier`):
//!
//! - **`add_scalar(s)`** (prover) / **`next_scalar(s)`** (verifier): the *only*
//!   way a scalar enters the proof. It transmits AND absorbs, in one call, so
//!   transmitted data is **always** bound, and the two sides cannot drift. This is
//!   the workhorse (GKR layers, constraint round polys, evaluation values, the
//!   commitment root).
//! - **The public statement** (the public input) is seeded into the sponge at
//!   construction ([`Sponge::new`]) by BOTH sides, so it is bound before any
//!   challenge. `add_*` transmits AND binds; `observe_scalar` binds WITHOUT
//!   transmitting, and is only for values both sides derive independently. Never
//!   re-observe data that already rode the stream: it is bound once already, and
//!   binding it twice silently desynchronizes the two sides. A challenge is just
//!   `sample()`d, bound to everything seeded/sent so far.
//! - **`hint_merkle` (prover) / `next_merkle` (verifier)**: transport that is NOT
//!   absorbed here, one opening phase of hash-bearing data whose binding is the
//!   Merkle structure itself.
//! - **`sample` / `sample_vec`**: squeeze a challenge.
//!
//! The [`Sponge`] itself (the VM-native Merkle–Damgård chaining value, its
//! domain tags, grinding, and the diagnostic trace) lives in [`crate::sponge`].

use crate::merkle::{Hash, MerkleOpening, MerklePaths, hash_to_scalars, scalars_to_hash};
use crate::sponge::Sponge;
use primitives::field::{F64, F192};

/// A complete proof: the scalar transcript stream plus the Merkle phases:
/// **two** channels, no bolted-on side field. The commitment root and every
/// transmitted scalar ride `stream`; the hash-bearing openings ride
/// `merkle_paths`. flock's BLAKE3 sub-proof is carried the same way: its
/// zerocheck / lincheck / ring-switch scalars are ordinary `add_scalar` words on
/// `stream` (transmitted AND bound at their protocol points, like every other
/// scalar) and its opening phases append to `merkle_paths`.
///
/// `Deserialize` as well as `Serialize`, so a proof round-trips over the wire and
/// an independent verifier process reconstructs it: everything lives in these two
/// fields, and [`VerifierState`] re-derives every challenge from them via the
/// shared sponge, so nothing travels out of band.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Proof {
    /// Every transmitted field scalar, in protocol order (plus flock's scalar
    /// sub-proof as trailing raw transport words).
    pub stream: Vec<F192>,
    /// One entry per opening phase, in the order the phases run. Nothing here
    /// names WHIR: a phase pushes its rows and siblings, the next pulls them.
    pub merkle_paths: Vec<MerklePaths>,
}

/// The proof the recursion guest and the Python verifier consume: nothing
/// shared, nothing pruned.
///
/// Same protocol, redundant encoding. Each query carries its own full Merkle
/// path instead of an octopus over the batch, so a consumer walks one path per
/// query with no dedup bookkeeping, which is the difference between a page of
/// index arithmetic and a loop in the zkDSL. [`Proof`] is what goes over the
/// wire; a verifier run produces this as a by-product
/// ([`VerifierState::into_raw_proof`]), so the expansion is written once.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RawProof {
    /// Identical to [`Proof::stream`]: no scalar is omitted from the wire form
    /// today. Carried here anyway so a consumer needs this struct alone.
    pub stream: Vec<F192>,
    /// One opening per query, phases concatenated in the order they ran.
    pub merkle_openings: Vec<MerkleOpening>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The verifier tried to read past the end of the proof stream.
    ExceededStream,
    /// A required opening hint was missing.
    MissingHint,
    /// An opening phase did not authenticate against its root, or was malformed.
    InvalidMerkleOpening,
    /// Verification finished without consuming the whole proof.
    NotFullyConsumed,
    /// A grinding nonce failed its proof-of-work check.
    PowFailed,
    /// A transmitted field element used as a narrower encoding had nonzero
    /// limbs outside that encoding.
    NonCanonicalEncoding,
}

/// What a protocol step needs from the transcript when it only draws challenges:
/// one implementation then serves both sides. WHIR's query sampler and every
/// shared sub-step take `&mut impl Challenger`, so no caller outside this crate
/// ever holds the sponge itself: it is reachable only through these three
/// traits and the two states that implement them.
pub trait Challenger {
    fn sample(&mut self) -> F192;
    fn sample_vec(&mut self, n: usize) -> Vec<F192>;
    /// Bind a value both sides derive themselves (never transmitted), so it is
    /// side-agnostic and lives here rather than on the two halves below.
    fn observe_scalar(&mut self, x: F192);

    /// Bind a root both sides already hold (a commitment that is part of the
    /// statement) as its two scalars, not as a byte string, so the recursion
    /// guest replays one shape for every digest.
    fn observe_root(&mut self, root: &Hash) {
        for s in hash_to_scalars(root) {
            self.observe_scalar(s);
        }
    }
}

/// The prover half of a transmitting sub-protocol (WHIR and its sumchecks):
/// push an opening phase, send a scalar, or grind.
pub trait Transmitter: Challenger {
    fn hint_merkle(&mut self, paths: MerklePaths);
    fn add_scalar(&mut self, x: F192);
    fn add_scalars(&mut self, xs: &[F192]);
    fn grind(&mut self, bits: u32);

    /// Transmit a root as its two scalars ([`Challenger::observe_root`] is for
    /// the one root the verifier already holds).
    fn add_root(&mut self, root: &Hash) {
        self.add_scalars(&hash_to_scalars(root));
    }
}

/// The verifier half, mirroring [`Transmitter`] call for call.
pub trait Receiver: Challenger {
    /// Pull the next opening phase and authenticate it: see
    /// [`VerifierState::next_merkle_batch`].
    fn next_merkle_batch(
        &mut self,
        root: &Hash,
        num_leaves: usize,
        queries: &[usize],
        leaf_words: usize,
    ) -> Result<Vec<Vec<F64>>, Error>;
    fn next_scalar(&mut self) -> Result<F192, Error>;
    fn next_scalars(&mut self, n: usize) -> Result<Vec<F192>, Error> {
        (0..n).map(|_| self.next_scalar()).collect()
    }

    /// Mirror of [`Transmitter::add_root`]. Both halves are prover-chosen, so a
    /// non-canonical one is rejected here rather than reaching a decoder.
    fn next_root(&mut self) -> Result<Hash, Error> {
        scalars_to_hash(&[self.next_scalar()?, self.next_scalar()?])
    }
    fn grind_check(&mut self, bits: u32) -> Result<(), Error>;
}

/// Prover side: writes scalars into the stream and opening phases to the side.
pub struct ProverState {
    sponge: Sponge,
    stream: Vec<F192>,
    merkle_paths: Vec<MerklePaths>,
}

impl ProverState {
    /// `statement` is the public input, seeded into the sponge (see [`Sponge::new`]).
    pub fn new(label: &[u8], statement: &[F192]) -> Self {
        Self {
            sponge: Sponge::new(label, statement),
            stream: Vec::new(),
            merkle_paths: Vec::new(),
        }
    }

    pub fn into_proof(self) -> Proof {
        Proof {
            stream: self.stream,
            merkle_paths: self.merkle_paths,
        }
    }
}

/// Verifier side: reads scalars from a received [`Proof`] (borrowed) and pulls
/// opening phases in order.
pub struct VerifierState<'a> {
    sponge: Sponge,
    stream: &'a [F192],
    offset: usize,
    merkle_paths: &'a [MerklePaths],
    phase: usize,
    raw_openings: Vec<MerkleOpening>,
}

impl<'a> VerifierState<'a> {
    /// `statement` is the public input, seeded into the sponge (see [`Sponge::new`]).
    /// It must match the prover's, or the sponges diverge and verification fails.
    pub fn new(label: &[u8], proof: &'a Proof, statement: &[F192]) -> Self {
        Self {
            sponge: Sponge::new(label, statement),
            stream: &proof.stream,
            offset: 0,
            merkle_paths: &proof.merkle_paths,
            phase: 0,
            raw_openings: Vec::new(),
        }
    }

    /// Advance the stream cursor by one **without** binding into the sponge: the
    /// read counterpart of the raw nonce push in [`ProverState::grind`].
    fn take_raw(&mut self) -> Result<F192, Error> {
        let x = *self.stream.get(self.offset).ok_or(Error::ExceededStream)?;
        self.offset += 1;
        Ok(x)
    }

    /// The redundant form of the proof just verified: every scalar it read, plus
    /// one unpruned opening per query in phase order. Meaningful only after a
    /// verification that accepted, since a rejected one stops part way.
    pub fn into_raw_proof(self) -> RawProof {
        RawProof {
            stream: self.stream.to_vec(),
            merkle_openings: self.raw_openings,
        }
    }

    /// How many stream words have been read so far: the cursor a caller needs
    /// to locate a sub-protocol's scalars without counting back from the tail.
    pub fn stream_offset(&self) -> usize {
        self.offset
    }

    /// Assert the whole proof was consumed (no trailing/extra data).
    pub fn finish(&self) -> Result<(), Error> {
        if self.offset == self.stream.len() && self.phase == self.merkle_paths.len() {
            Ok(())
        } else {
            Err(Error::NotFullyConsumed)
        }
    }
}

impl Transmitter for ProverState {
    /// Hand the next opening phase's Merkle data to the verifier. Not absorbed:
    /// its binding is the Merkle structure itself.
    fn hint_merkle(&mut self, paths: MerklePaths) {
        self.merkle_paths.push(paths);
    }

    /// Transmit a scalar into the proof AND bind it into the sponge (the two are
    /// inseparable: you cannot send without binding).
    #[inline]
    fn add_scalar(&mut self, x: F192) {
        self.sponge.observe(x);
        self.stream.push(x);
    }

    fn add_scalars(&mut self, xs: &[F192]) {
        for &x in xs {
            self.add_scalar(x);
        }
    }

    /// Proof-of-work grind of `bits` before the next challenge, raising that
    /// challenge's Schwartz–Zippel soundness by `bits` (the prover must redo
    /// the PoW to re-roll the challenge). Grinds, binds the nonce into the
    /// sponge, and transmits it on the stream as raw transport (already bound
    /// by the grind, so it is NOT re-absorbed). `bits = 0` is the canonical
    /// no-work nonce `0`.
    fn grind(&mut self, bits: u32) {
        let nonce = self.sponge.grind_pow(bits);
        self.stream.push(F192::new(nonce, 0, 0));
    }
}

impl<'a> Receiver for VerifierState<'a> {
    /// Verifier mirror of [`Transmitter::hint_merkle`]: pull the next opening
    /// phase, authenticate every queried row against `root`, and return the rows
    /// in `queries` order.
    ///
    /// The only way to reach a phase's rows, so none can be used unauthenticated.
    /// The check also yields each query's full sibling path, which is recorded
    /// for [`VerifierState::into_raw_proof`].
    fn next_merkle_batch(
        &mut self,
        root: &Hash,
        num_leaves: usize,
        queries: &[usize],
        leaf_words: usize,
    ) -> Result<Vec<Vec<F64>>, Error> {
        let paths: &'a MerklePaths = self.merkle_paths.get(self.phase).ok_or(Error::MissingHint)?;
        self.phase += 1;
        let openings = paths
            .open(root, num_leaves, queries, leaf_words)
            .ok_or(Error::InvalidMerkleOpening)?;
        let rows = openings.iter().map(|o| o.leaf_data.clone()).collect();
        self.raw_openings.extend(openings);
        Ok(rows)
    }

    /// Read the next scalar, binding it into the sponge (mirrors `add_scalar`).
    #[inline]
    fn next_scalar(&mut self) -> Result<F192, Error> {
        let x = *self.stream.get(self.offset).ok_or(Error::ExceededStream)?;
        self.offset += 1;
        self.sponge.observe(x);
        Ok(x)
    }

    /// Verifier mirror of [`Transmitter::grind`]: read the transmitted nonce and
    /// check it clears the `bits` proof-of-work, then bind it (so the sponge
    /// stays in lockstep). Rejects a proof that skipped or under-did the grind.
    fn grind_check(&mut self, bits: u32) -> Result<(), Error> {
        let nonce = self.take_raw()?;
        if self.sponge.verify_pow_field(nonce, bits) {
            Ok(())
        } else {
            Err(Error::PowFailed)
        }
    }
}

impl Challenger for ProverState {
    fn sample(&mut self) -> F192 {
        self.sponge.sample()
    }
    fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        self.sponge.sample_vec(n)
    }
    fn observe_scalar(&mut self, x: F192) {
        self.sponge.observe(x);
    }
}

impl Challenger for VerifierState<'_> {
    fn sample(&mut self) -> F192 {
        self.sponge.sample()
    }
    fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        self.sponge.sample_vec(n)
    }
    /// Absorb a value both parties compute themselves (never transmitted):
    /// protocol steps that bind derived values before sampling, e.g. the
    /// stacked-bytecode claim reduction (`leaf::verify_balance`).
    fn observe_scalar(&mut self, x: F192) {
        self.sponge.observe(x);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(k: u64) -> F192 {
        F192::new(k, k ^ 0x1234, k.rotate_left(17))
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
}
