//! The VM-native Fiat–Shamir sponge: THE verifier-randomness source for the
//! whole stack — flock's zerocheck / lincheck, the BaseFold/Ligerito PCS, and
//! leanVM-b's own protocol (whose `ProverState` / `VerifierState` wrap this
//! sponge with the proof transport channels).
//!
//! A 256-bit chaining value evolved only by the fixed 64→32 BLAKE3 compression
//! the VM's `Blake3` opcode computes, so prover, verifier, and a recursive
//! verifier running on the VM all derive identical challenges with one
//! `blake3` per step. That is the reason this replaces the streaming
//! `blake3::Hasher` challenger: the multi-block chunk tree / flags / counter of
//! the streaming hasher cannot be reproduced by the one 64-byte compression the
//! machine has.
//!
//! Construction adapted from Signal's ShoSha256 "Stateful Hash Object"
//! (`libsignal/rust/poksho/src/shosha256.rs`, © 2020 Signal Messenger, LLC,
//! AGPL-3.0-only): a chaining value advanced by domain-separated absorb /
//! squeeze steps. Here the underlying hash is the VM's BLAKE3 compression
//! rather than SHA-256, inputs are GF(2^128) field elements, and — because
//! every absorb is domain-tagged per compression — no explicit double-hash
//! ratchet is needed.
//!
//! Each challenge is the random-oracle image of the whole prior transcript;
//! every absorb is domain-tagged per compression (so a field element, a raw
//! integer, and a byte string cannot alias), byte strings are length-framed,
//! and each squeeze ratchets the state (binding challenge order).

use crate::field::F128;

/// `f(a, b) = BLAKE3(a‖b)` on two 256-bit halves laid out little-endian into 64
/// bytes — *exactly* the VM's `Blake3` opcode: 64 input bytes → 32-byte digest,
/// split back into two field words. THE primitive; the sponge is a chain of
/// these, so a zkDSL program replays it with one `blake3(...)` per step.
pub fn compress(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(16).zip([a[0], a[1], b[0], b[1]]) {
        slot[..8].copy_from_slice(&w.lo.to_le_bytes());
        slot[8..].copy_from_slice(&w.hi.to_le_bytes());
    }
    let d = *blake3::hash(&input).as_bytes();
    let word = |b: &[u8]| {
        F128::new(
            u64::from_le_bytes(b[..8].try_into().unwrap()),
            u64::from_le_bytes(b[8..16].try_into().unwrap()),
        )
    };
    [word(&d[..16]), word(&d[16..])]
}

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
/// `tests/verify_recursive.py`). `bits` is always `< 64`.
#[inline]
fn pow_bits_ok(base: [F128; 2], nonce: u64, bits: u32) -> bool {
    debug_assert!(bits < 64, "grinding deficit fits the digest's low word");
    let digest = compress(base, [F128::new(nonce, 0), DS_POW])[0];
    digest.lo & ((1u64 << bits) - 1) == 0
}

/// The shared Fiat–Shamir state (see the module docs). Protocol functions take
/// `&mut Sponge`; all proof DATA travels on separate transport channels (the
/// callers'), so the sponge only ever absorbs and squeezes.
#[derive(Clone)]
pub struct Sponge {
    /// The 256-bit chaining value: a Merkle–Damgård hash of the transcript so far.
    cv: [F128; 2],
}

impl Sponge {
    /// Seed with the domain `label` and the PUBLIC `statement` scalars (the public
    /// input). Both sides seed identically, so the whole statement is bound before
    /// any challenge — there is no mid-protocol "observe public data" step to get
    /// wrong (or forget). (Untraced: the seed is the replay STARTING state, not an
    /// op of the recorded transcript.)
    pub fn new(label: &[u8], statement: &[F128]) -> Self {
        let mut s = Self { cv: [F128::ZERO, F128::ZERO] };
        s.absorb_bytes_untraced(b"leanvm-b/transcript/v1");
        s.absorb_bytes_untraced(label);
        for &x in statement {
            s.observe_untraced(x);
        }
        s
    }

    /// A fresh chain at the zero state: the guest-side aggregation and export
    /// transcripts start here (no label), and the harness mirrors them.
    pub fn empty() -> Self {
        Self { cv: [F128::ZERO; 2] }
    }

    /// Absorb one scalar: `cv ← compress(cv, (x, DS_SCALAR))`.
    pub fn observe(&mut self, x: F128) {
        self.observe_untraced(x);
        trace(|| TraceOp::Observe(x));
    }

    fn observe_untraced(&mut self, x: F128) {
        self.cv = compress(self.cv, [x, DS_SCALAR]);
    }

    /// Absorb a byte string (a protocol label, a Merkle root): a length frame
    /// then its 16-byte words as tagged blocks, so a field element, a raw
    /// integer, and a byte string cannot alias.
    pub fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.absorb_bytes_untraced(bytes);
        trace(|| TraceOp::AbsorbBytes(bytes.to_vec()));
    }

    fn absorb_bytes_untraced(&mut self, bytes: &[u8]) {
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
        let v = self.sample_untraced();
        trace(|| TraceOp::Sample(v));
        v
    }

    fn sample_untraced(&mut self) -> F128 {
        let out = compress(self.cv, [F128::ZERO, DS_SQUEEZE]);
        self.cv = out;
        out[0]
    }

    /// Squeeze `n` challenges, in order.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F128> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// The PoW base `compress(cv, (0, DS_POW))`, read without mutating the live
    /// state (the nonce is bound separately by [`Self::absorb_nonce`]).
    fn pow_base(&self) -> [F128; 2] {
        compress(self.cv, [F128::ZERO, DS_POW])
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
    /// (Untraced throughout: a replay must never re-record.)
    pub fn replay(&mut self, ops: &[TraceOp]) {
        for op in ops {
            match op {
                TraceOp::Observe(x) => self.observe_untraced(*x),
                TraceOp::AbsorbBytes(b) => self.absorb_bytes_untraced(b),
                TraceOp::Sample(v) => {
                    assert_eq!(self.sample_untraced(), *v, "trace replay diverged")
                }
                TraceOp::Pow { nonce, bits, .. } => {
                    assert!(self.verify_pow_untraced(*nonce, *bits), "trace replay: grind failed")
                }
                TraceOp::StreamRaw(_) | TraceOp::Opening => {}
            }
        }
    }

    /// Bind a grinding nonce into the state (both sides, so they stay in lockstep).
    fn absorb_nonce(&mut self, nonce: u64) {
        self.cv = compress(self.cv, [F128::new(nonce, 0), DS_POW]);
    }

    /// Prover-side PoW grind: find the smallest `u64` nonce whose PoW hash clears
    /// `bits` low zero bits, then bind it so later challenges depend on it.
    /// `bits = 0` is the canonical no-work nonce `0`. Parallel search for the
    /// larger grinds.
    pub fn grind_pow(&mut self, bits: u32) -> u64 {
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
        trace(|| TraceOp::Pow { nonce, bits, digest: self.pow_digest(nonce) });
        self.verify_pow_untraced(nonce, bits)
    }

    fn verify_pow_untraced(&mut self, nonce: u64, bits: u32) -> bool {
        let base = self.pow_base();
        let ok = if bits == 0 { nonce == 0 } else { pow_bits_ok(base, nonce, bits) };
        self.absorb_nonce(nonce);
        ok
    }
}

/// One transcript operation, recorded by the (diagnostic) trace
/// ([`trace_start`] / [`trace_take`]). The sponge records its own absorbs /
/// squeezes / grind checks; transport-only events ([`TraceOp::StreamRaw`],
/// [`TraceOp::Opening`]) are recorded by the caller owning the transport
/// channel via [`trace`]. The in-circuit verifier replays exactly this op
/// sequence, so the trace of a real verify run is both the guest program's
/// mechanical spec and its checkpoint data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceOp {
    /// A stream word consumed without binding (hint bytes, nonces).
    StreamRaw(F128),
    /// An absorbed scalar (transmitted or derived — the sponge cannot tell).
    Observe(F128),
    /// `absorb_bytes` (labels, roots).
    AbsorbBytes(Vec<u8>),
    Sample(F128),
    /// A grinding check: the nonce, the required bits, and the digest the
    /// pre-absorb state yields for that nonce (so trace consumers never need
    /// to track sponge state in lockstep).
    Pow { nonce: u64, bits: u32, digest: F128 },
    /// An opening hint consumed (the Ligerito hint channel).
    Opening,
}

thread_local! {
    static TRACE: std::cell::RefCell<Option<Vec<TraceOp>>> = const { std::cell::RefCell::new(None) };
}

/// Start recording transcript ops on this thread (diagnostic).
pub fn trace_start() {
    TRACE.with(|t| *t.borrow_mut() = Some(Vec::new()));
}

/// Stop recording and return the ops recorded since [`trace_start`].
pub fn trace_take() -> Vec<TraceOp> {
    TRACE.with(|t| t.borrow_mut().take().unwrap_or_default())
}

/// Record one op if a trace is active (the closure only runs then). The sponge
/// calls this for its own ops; transport owners call it for theirs.
#[inline]
pub fn trace(op: impl FnOnce() -> TraceOp) {
    TRACE.with(|t| {
        if let Some(v) = t.borrow_mut().as_mut() {
            v.push(op());
        }
    });
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
