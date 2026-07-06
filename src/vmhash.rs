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

use crate::field::{F128, g_pow};

/// `f(a, b) = BLAKE3(a‖b)` on two 256-bit halves laid out little-endian into 64
/// bytes — *exactly* the `Blake3` opcode (§7.6, `cpu::execute`): 64 input bytes →
/// 32-byte digest, split back into two field words. THE primitive; every other
/// hash here is a chain of these, so a zkDSL program reproduces them with one
/// `blake3(...)` per call.
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

/// Merkle–Damgård hash of a field-element slice with the **byte length in the
/// IV** — mirroring the XMSS WOTS-public-key hash (`xmss_aggregate.py`): the
/// chaining value starts at `(g^{num_bytes}, 0)` and each 32-byte (two-word)
/// block is absorbed by one [`compress`]. Committing the length up front makes
/// the hash non-length-extendable with no separate finalization block, and lets
/// odd tails be zero-padded unambiguously (the length in the IV distinguishes a
/// real trailing zero word from padding).
///
/// In the VM the IV is a compile-time constant `SET` (the length is known), so a
/// program hashes an `n`-word slice with exactly `⌈n/2⌉` `blake3` opcodes.
pub fn hash_slice(data: &[F128]) -> [F128; 2] {
    let num_bytes = data.len() * core::mem::size_of::<u64>() * 2; // 16 bytes / word
    let mut cv = [g_pow(num_bytes), F128::ZERO];
    let mut i = 0;
    while i < data.len() {
        let b1 = data.get(i + 1).copied().unwrap_or(F128::ZERO);
        cv = compress(cv, [data[i], b1]);
        i += 2;
    }
    cv
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(k: u64) -> F128 {
        F128::new(k, k.wrapping_mul(0x9e37_79b9) ^ 0x51)
    }

    /// `hash_slice` is exactly the length-in-IV Merkle–Damgård chain the VM's
    /// `blake3` opcode would run: IV = (g^{16·n}, 0), then one `compress` per
    /// 2-word block.
    #[test]
    fn hash_slice_matches_md_chain() {
        let data = [e(1), e(2), e(3), e(4)];
        let mut cv = [g_pow(4 * 16), F128::ZERO];
        cv = compress(cv, [data[0], data[1]]);
        cv = compress(cv, [data[2], data[3]]);
        assert_eq!(hash_slice(&data), cv);
    }

    /// The empty slice hashes to the bare IV of length 0 = (g^0, 0) = (1, 0).
    #[test]
    fn hash_slice_empty_is_iv() {
        assert_eq!(hash_slice(&[]), [g_pow(0), F128::ZERO]);
    }

    /// The length lives in the IV, so a slice and the same slice with an extra
    /// trailing zero (a padding-style ambiguity) hash differently — no length
    /// extension.
    #[test]
    fn hash_slice_binds_length() {
        assert_ne!(hash_slice(&[e(7)]), hash_slice(&[e(7), F128::ZERO]));
        assert_ne!(hash_slice(&[e(7), e(8)]), hash_slice(&[e(7), e(8), F128::ZERO, F128::ZERO]));
    }

    /// An odd tail is zero-padded into the last block; the length in the IV keeps
    /// it distinct from an explicitly-zero-terminated even slice of a DIFFERENT
    /// length (covered above), while a 1-word slice still hashes in one block.
    #[test]
    fn hash_slice_odd_tail() {
        let one = hash_slice(&[e(5)]);
        let manual = compress([g_pow(16), F128::ZERO], [e(5), F128::ZERO]);
        assert_eq!(one, manual);
    }

    /// The vendored PCS Merkle leaf hash (`flare::merkle::hash_leaf`) must equal
    /// `hash_slice` on the same field words — the invariant that lets a recursive
    /// verifier reuse ONE routine for the transcript/leaf hashing and the PCS
    /// tree. Covers single-word, odd, and full-width (2^6) leaves.
    #[test]
    fn hash_slice_matches_flock_leaf() {
        for n in [1usize, 2, 3, 5, 64] {
            let words: Vec<F128> = (0..n).map(|i| e(i as u64 + 1)).collect();
            let mut bytes = Vec::with_capacity(n * 16);
            for w in &words {
                bytes.extend_from_slice(&w.lo.to_le_bytes());
                bytes.extend_from_slice(&w.hi.to_le_bytes());
            }
            let mine = hash_slice(&words);
            let mut expect = [0u8; 32];
            expect[..8].copy_from_slice(&mine[0].lo.to_le_bytes());
            expect[8..16].copy_from_slice(&mine[0].hi.to_le_bytes());
            expect[16..24].copy_from_slice(&mine[1].lo.to_le_bytes());
            expect[24..32].copy_from_slice(&mine[1].hi.to_le_bytes());
            assert_eq!(flare::merkle::hash_leaf(&bytes), expect, "n={n}");
        }
    }
}
