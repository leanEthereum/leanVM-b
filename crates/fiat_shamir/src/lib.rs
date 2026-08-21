// CREDIT: https://github.com/signalapp/libsignal/blob/main/rust/poksho/src/shosha256.rs, AGPL-3.0-only.
//! The shared Fiat–Shamir layer: the VM-native [`FiatShamirState`] state, the
//! [`transcript`] wrapper states (`ProverState`/`VerifierState`) that pair it
//! with the proof transport channels, and the [`merkle`] data those channels
//! carry.
//!
//! [`FiatShamirState`] is a 256-bit chaining value evolved only by the fixed 64→32
//! BLAKE2s hash the VM's `Blake2s` opcode computes, so prover, verifier, and a
//! recursive verifier running on the VM all derive identical challenges with one
//! hash per step. Hashing exactly 64 bytes IS one BLAKE2s compression (counter
//! 64, final-block flag set), which is why a single opcode covers the whole
//! chain.
//!
//! Every block has ONE shape: up to three lanes of data, and the domain tag in
//! the fourth. A scalar is `E = F192` (the tower challenge field), so its three
//! little-endian `K = F64` limbs fill the data lanes exactly.
//!
//! Construction adapted from Signal's ShoSha256 "Stateful Hash Object"
//! (`libsignal/rust/poksho/src/shosha256.rs`, © 2020 Signal Messenger, LLC,
//! AGPL-3.0-only): a chaining value advanced by domain-separated absorb /
//! squeeze steps. Here the underlying hash is the VM's BLAKE2s compression
//! rather than SHA-256, inputs are `K = GF(2^64)` field words, and, because
//! every absorb is domain-tagged per compression, no explicit double-hash
//! ratchet is needed. It is a Merkle–Damgård chain, NOT a sponge: there is no
//! rate/capacity split and no permutation, so it is named for the transform it
//! serves rather than for a construction it is not.
//!
//! Each challenge is the random-oracle image of the whole prior transcript;
//! every absorb is domain-tagged per compression (so a field element, a raw
//! integer, and a byte string cannot alias), byte strings are length-framed,
//! and each squeeze ratchets the state (binding challenge order).

pub mod merkle;
pub mod transcript;

use primitives::field::{F64, F192};

/// `f(a, b) = BLAKE2s(a‖b)` on two 256-bit halves laid out little-endian into
/// 64 bytes, *exactly* the VM's `Blake2s` opcode: 64 input bytes → 32-byte
/// digest, split back into four field words. THE primitive; the chain is a
/// chain of these, so a zkDSL program replays it with one `blake2s(...)` per
/// step.
///
/// A 64-byte input is one compression, so this is `compress(init_state(0), m,
/// t = 64, last = true)` and nothing about the byte-level padding rules can
/// leak into the in-circuit version.
pub fn compress(a: [F64; 4], b: [F64; 4]) -> [F64; 4] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(8).zip(a.into_iter().chain(b)) {
        slot.copy_from_slice(&w.0.to_le_bytes());
    }
    let d = primitives::blake2s::hash(&input);
    std::array::from_fn(|k| F64(u64::from_le_bytes(d[8 * k..8 * k + 8].try_into().unwrap())))
}

// Domain-separation tags. EVERY block puts its tag in lane 3 and its data in
// lanes 0..=2, so one role is one constant in one place. The tag lane is never
// adversary-controlled, so distinct constants are all it takes to make two roles
// unable to alias.
const DS_SCALAR: F64 = F64(1);
const DS_BYTE: F64 = F64(2);
const DS_LEN: F64 = F64(3);
const DS_SQUEEZE: F64 = F64(4);
const DS_POW_BASE: F64 = F64(5);
const DS_POW_NONCE: F64 = F64(6);

/// `compress(base, (nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE))` has its low `bits`
/// bits zero: the grinding predicate over the VM compression. A CONTIGUOUS
/// low-bit window (rather than byte-wise leading zeros) so a recursive verifier
/// re-checks it with a single loop over the bit decomposition of the digest word
/// (`grind_check` in `guests/aggregate.py`). `bits` is always `< 64`.
#[inline]
fn pow_bits_ok(base: [F64; 4], nonce: F192, bits: u32) -> bool {
    debug_assert!(bits < 64, "grinding deficit fits the digest's low word");
    let digest = compress(base, [F64(nonce.c0), F64(nonce.c1), F64(nonce.c2), DS_POW_NONCE])[0];
    digest.0 & ((1u64 << bits) - 1) == 0
}

/// The shared Fiat–Shamir state (see the module docs). Protocol functions take
/// `&mut FiatShamirState`; all proof DATA travels on separate transport channels (the
/// callers'), so the state only ever absorbs and squeezes.
#[derive(Clone)]
pub struct FiatShamirState {
    /// The 256-bit chaining value: a Merkle–Damgård hash of the transcript so far.
    cv: [F64; 4],
}

impl FiatShamirState {
    /// Seed with the domain `label` and the PUBLIC `statement` scalars (the public
    /// input). Both sides seed identically, so the whole statement is bound before
    /// any challenge; there is no mid-protocol "observe public data" step to get
    /// wrong (or forget).
    pub fn new(label: &[u8], statement: &[F192]) -> Self {
        let mut s = Self { cv: [F64::ZERO; 4] };
        s.absorb_bytes(b"leanvm-b/transcript/v4-blake2s");
        s.absorb_bytes(label);
        for &x in statement {
            s.observe(x);
        }
        s
    }

    /// Absorb one 24-byte scalar (three little-endian `K` limbs):
    /// `cv ← compress(cv, (c0, c1, c2, DS_SCALAR))`.
    pub fn observe(&mut self, x: F192) {
        self.cv = compress(self.cv, [F64(x.c0), F64(x.c1), F64(x.c2), DS_SCALAR]);
    }

    /// Absorb a byte string (a protocol label, a Merkle root): a length frame,
    /// then its 24-byte (three-word) chunks as `DS_BYTE` blocks, so a field
    /// element, a raw integer, and a byte string cannot alias.
    fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.cv = compress(self.cv, [F64(bytes.len() as u64), F64::ZERO, F64::ZERO, DS_LEN]);
        for chunk in bytes.chunks(24) {
            let mut buf = [0u8; 24];
            buf[..chunk.len()].copy_from_slice(chunk);
            let w = |o: usize| F64(u64::from_le_bytes(buf[o..o + 8].try_into().unwrap()));
            self.cv = compress(self.cv, [w(0), w(8), w(16), DS_BYTE]);
        }
    }

    /// Squeeze a challenge and ratchet: the challenge's three limbs are the
    /// first three words of `compress(cv, (0, 0, 0, DS_SQUEEZE))`, whose full output
    /// becomes the new state, domain-separated from absorbs, so a challenge
    /// cannot be confused with a continued absorb. In Fiat–Shamir everything is
    /// public; soundness comes from each challenge being a random-oracle image
    /// of the entire prior transcript.
    pub fn sample(&mut self) -> F192 {
        let out = compress(self.cv, [F64::ZERO, F64::ZERO, F64::ZERO, DS_SQUEEZE]);
        self.cv = out;
        F192::new(out[0].0, out[1].0, out[2].0)
    }

    /// Squeeze `n` challenges, in order.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// The PoW base `compress(cv, (0, 0, 0, DS_POW_BASE))`, read without mutating
    /// the live state (the nonce is bound separately by [`Self::absorb_nonce`]).
    fn pow_base(&self) -> [F64; 4] {
        compress(self.cv, [F64::ZERO, F64::ZERO, F64::ZERO, DS_POW_BASE])
    }

    /// The current 256-bit chaining value.
    pub fn state(&self) -> [F64; 4] {
        self.cv
    }

    /// Bind a grinding nonce into the state (both sides, so they stay in lockstep).
    fn absorb_nonce(&mut self, nonce: F192) {
        self.cv = compress(self.cv, [F64(nonce.c0), F64(nonce.c1), F64(nonce.c2), DS_POW_NONCE]);
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
                if pow_bits_ok(base, F192::new(n, 0, 0), bits) {
                    break n;
                }
                n = n.wrapping_add(1);
            }
        } else {
            // `find_first` returns the globally smallest satisfying nonce, so the
            // proof is deterministic regardless of how the scan is claimed.
            let block: u64 = 1 << (bits.min(24) + 1);
            let mut start: u64 = 0;
            loop {
                if let Some(n) = parallel::find_first(block as usize, |i| {
                    pow_bits_ok(base, F192::new(start + i as u64, 0, 0), bits)
                }) {
                    break start + n as u64;
                }
                start = start.saturating_add(block);
            }
        };
        self.absorb_nonce(F192::new(nonce, 0, 0));
        nonce
    }

    /// Verifier-side mirror of [`Self::grind_pow`]: check `nonce` clears the `bits`
    /// PoW against the current state, then bind it regardless (so the state stays
    /// in lockstep with an honest prover; a failed check rejects at the call
    /// site). `bits = 0` accepts only the canonical nonce `0`, which keeps proofs
    /// non-malleable at zero-bit grinding sites. Allowing the complete field
    /// domain does not weaken grinding: each candidate still requires one hash
    /// and succeeds with probability 2^-bits. Honest provers remain canonical
    /// and search the deterministic u64 subset in [`Self::grind_pow`].
    pub fn verify_pow_field(&mut self, nonce: F192, bits: u32) -> bool {
        let base = self.pow_base();
        let ok = if bits == 0 {
            nonce == F192::ZERO
        } else {
            pow_bits_ok(base, nonce, bits)
        };
        self.absorb_nonce(nonce);
        ok
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(k: u64) -> F192 {
        F192::new(k, k ^ 0x1234, k.rotate_left(17))
    }

    /// A challenge binds every prior absorbed scalar: flipping one observed value
    /// changes the next squeeze.
    #[test]
    fn fs_binds_observations() {
        let mut a = FiatShamirState::new(b"t", &[f(1), f(2)]);
        let mut b = FiatShamirState::new(b"t", &[f(1), f(3)]);
        assert_ne!(a.sample(), b.sample());
    }

    /// Absorb order matters: observe(a) then observe(b) ≠ observe(b) then observe(a).
    #[test]
    fn fs_binds_order() {
        let mut a = FiatShamirState::new(b"t", &[]);
        a.observe(f(1));
        a.observe(f(2));
        let mut b = FiatShamirState::new(b"t", &[]);
        b.observe(f(2));
        b.observe(f(1));
        assert_ne!(a.sample(), b.sample());
    }

    /// A scalar and a byte string cannot alias (distinct domain tags), so
    /// observing a scalar vs absorbing its 24-byte encoding diverge.
    #[test]
    fn fs_domain_separation() {
        let x = f(9);
        let mut a = FiatShamirState::new(b"t", &[]);
        a.observe(x);
        let mut b = FiatShamirState::new(b"t", &[]);
        let mut bytes = [0u8; 24];
        bytes[..8].copy_from_slice(&x.c0.to_le_bytes());
        bytes[8..16].copy_from_slice(&x.c1.to_le_bytes());
        bytes[16..].copy_from_slice(&x.c2.to_le_bytes());
        b.absorb_bytes(&bytes);
        assert_ne!(a.sample(), b.sample());
    }

    /// A grind clears its own PoW, and returns the SMALLEST nonce that does.
    #[test]
    fn pow_predicate() {
        let sp = FiatShamirState::new(b"t", &[f(1)]);
        let base = sp.pow_base();
        let good = {
            let mut clone = sp.clone();
            clone.grind_pow(8)
        };
        assert!(pow_bits_ok(base, F192::new(good, 0, 0), 8));
        for n in 0..good {
            assert!(
                !pow_bits_ok(base, F192::new(n, 0, 0), 8),
                "nonce {n} < {good} also clears"
            );
        }
    }

    /// Recursive proofs transport the nonce as one field word. Its high limb is
    /// therefore part of both the PoW predicate and the subsequent transcript.
    #[test]
    fn pow_accepts_and_binds_full_field_nonce() {
        let mut verifier = FiatShamirState::new(b"t", &[f(1)]);
        let base = verifier.pow_base();
        let nonce = (0..u64::MAX)
            .map(|lo| F192::new(lo, 1, 2))
            .find(|&nonce| pow_bits_ok(base, nonce, 8))
            .expect("an 8-bit grind has a solution");

        let mut expected = verifier.clone();
        expected.absorb_nonce(nonce);
        assert!(verifier.verify_pow_field(nonce, 8));
        assert_eq!(verifier.state(), expected.state());

        let mut zero_bits = FiatShamirState::new(b"t", &[f(1)]);
        assert!(!zero_bits.verify_pow_field(F192::new(0, 1, 0), 0));
    }
}
