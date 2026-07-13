//! VM-native hashing: the fixed 64→32 BLAKE3 compression the `Blake3` opcode
//! computes, and the Merkle–Damgård slice hash built from it.
//!
//! Everything here is expressible by a program running on the VM — one `blake3`
//! opcode per [`compress`] call — so the Fiat–Shamir transcript
//! ([`crate::transcript`]) and any slice / leaf hash can be *replayed in-circuit*.
//! That is the prerequisite for recursion: a proof of `verify()` can only be run
//! on the VM if every hash the verifier computes decomposes into the one 64-byte
//! compression the machine has. The streaming `blake3::Hasher` (multi-block chunk
//! tree, flags, counter) does not; these constructions do.

use primitives::field::{F64, g_pow};

/// `f(a, b) = BLAKE3(a‖b)` on two 256-bit halves laid out little-endian into 64
/// bytes — *exactly* the `Blake3` opcode (§7.6, `cpu::execute`): 64 input bytes →
/// 32-byte digest, split back into four field words. THE primitive; every other
/// hash here is a chain of these, so a zkDSL program reproduces them with one
/// `blake3(...)` per call.
/// Lives in [`fiat_shamir::sponge`] (the shared Fiat–Shamir sponge is built on it).
pub use fiat_shamir::sponge::compress;

/// Merkle–Damgård hash of a field-element slice with the **byte length in the
/// IV** — mirroring the XMSS WOTS-public-key hash (`xmss_aggregate.py`): the
/// chaining value starts at `(g^{num_bytes}, 0, 0, 0)` and each 32-byte
/// (four-word) block is absorbed by one [`compress`]. Committing the length up
/// front makes the hash non-length-extendable with no separate finalization
/// block, and lets odd tails be zero-padded unambiguously (the length in the IV
/// distinguishes a real trailing zero word from padding).
///
/// In the VM the IV is a compile-time constant `SET` (the length is known), so a
/// program hashes an `n`-word slice with exactly `⌈n/4⌉` `blake3` opcodes.
pub fn hash_slice(data: &[F64]) -> [F64; 4] {
    let num_bytes = data.len() * core::mem::size_of::<u64>(); // 8 bytes / word
    let mut cv = [g_pow(num_bytes), F64::ZERO, F64::ZERO, F64::ZERO];
    for block in data.chunks(4) {
        let mut b = [F64::ZERO; 4];
        b[..block.len()].copy_from_slice(block);
        cv = compress(cv, b);
    }
    cv
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(k: u64) -> F64 {
        F64(k.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x51)
    }

    /// `hash_slice` is exactly the length-in-IV Merkle–Damgård chain the VM's
    /// `blake3` opcode would run: IV = (g^{8·n}, 0, 0, 0), then one `compress`
    /// per 4-word block.
    #[test]
    fn hash_slice_matches_md_chain() {
        let data: Vec<F64> = (1..=8).map(e).collect();
        let mut cv = [g_pow(8 * 8), F64::ZERO, F64::ZERO, F64::ZERO];
        cv = compress(cv, data[..4].try_into().unwrap());
        cv = compress(cv, data[4..].try_into().unwrap());
        assert_eq!(hash_slice(&data), cv);
    }

    /// The empty slice hashes to the bare IV of length 0 = (g^0, 0, 0, 0) = (1, 0, 0, 0).
    #[test]
    fn hash_slice_empty_is_iv() {
        assert_eq!(hash_slice(&[]), [g_pow(0), F64::ZERO, F64::ZERO, F64::ZERO]);
    }

    /// The length lives in the IV, so a slice and the same slice with an extra
    /// trailing zero (a padding-style ambiguity) hash differently — no length
    /// extension.
    #[test]
    fn hash_slice_binds_length() {
        assert_ne!(hash_slice(&[e(7)]), hash_slice(&[e(7), F64::ZERO]));
        let four: Vec<F64> = (1..=4).map(e).collect();
        let mut padded = four.clone();
        padded.extend([F64::ZERO; 4]);
        assert_ne!(hash_slice(&four), hash_slice(&padded));
    }

    /// An odd tail is zero-padded into the last block; the length in the IV keeps
    /// it distinct from an explicitly-zero-terminated even slice of a DIFFERENT
    /// length (covered above), while a 1-word slice still hashes in one block.
    #[test]
    fn hash_slice_odd_tail() {
        let one = hash_slice(&[e(5)]);
        let manual = compress(
            [g_pow(8), F64::ZERO, F64::ZERO, F64::ZERO],
            [e(5), F64::ZERO, F64::ZERO, F64::ZERO],
        );
        assert_eq!(one, manual);
    }

    /// The PCS Merkle leaf hash (`::pcs::merkle::hash_leaf`) must equal
    /// `hash_slice` on the same field words — the invariant that lets a recursive
    /// verifier reuse ONE routine for the transcript/leaf hashing and the PCS
    /// tree. Covers single-word, odd, and full-width leaves.
    #[test]
    fn hash_slice_matches_flock_leaf() {
        for n in [1usize, 2, 3, 5, 64] {
            let words: Vec<F64> = (0..n).map(|i| e(i as u64 + 1)).collect();
            let mut bytes = Vec::with_capacity(n * 8);
            for w in &words {
                bytes.extend_from_slice(&w.0.to_le_bytes());
            }
            let mine = hash_slice(&words);
            let mut expect = [0u8; 32];
            for (k, w) in mine.iter().enumerate() {
                expect[8 * k..8 * k + 8].copy_from_slice(&w.0.to_le_bytes());
            }
            assert_eq!(::pcs::merkle::hash_leaf(&bytes), expect, "n={n}");
        }
    }
}
