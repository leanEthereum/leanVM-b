//! `StackArray` — a run of consecutive frame (stack) cells in the zkDSL. Indexed
//! reads/writes go straight to `base+k` (no heap deref), and a size-2 `StackArray`
//! is a `blake3` operand: its two cells hold the 256-bit value's two words, so
//! `blake3(a, b)` reads them in place with no copies (a self-hash `blake3(h, h)`
//! aliases one pair into both operands).

use leanvm_b::blake3_flock::warm_setup;
use leanvm_b::compiler::{compile, parse};
use leanvm_b::cpu::{prove, verify};
use leanvm_b::field::F128;

/// `BLAKE3(a, b)` reference (matches `cpu::blake3_compress`): the four words laid
/// little-endian into 64 bytes, hashed, digest split into two `F128` words.
fn compress(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(16).zip([a[0], a[1], b[0], b[1]]) {
        slot[..8].copy_from_slice(&w.lo.to_le_bytes());
        slot[8..].copy_from_slice(&w.hi.to_le_bytes());
    }
    let d = blake3::hash(&input);
    let d = d.as_bytes();
    let word = |b: &[u8]| {
        F128::new(
            u64::from_le_bytes(b[..8].try_into().unwrap()),
            u64::from_le_bytes(b[8..16].try_into().unwrap()),
        )
    };
    [word(&d[..16]), word(&d[16..])]
}

/// A size-2 `StackArray` fed to `blake3` as a self-hash `blake3(h, h)`, then the
/// digest published to `m[0], m[1]`. Proves and verifies, and a wrong published
/// digest is rejected — so the whole path (StackArray load → aliased blake3 →
/// stack read → publish) is exercised end-to-end.
#[test]
fn stack_array_blake3_self_hash() {
    let src = "\
def main():
    a = StackArray(2)
    a[0] = 5
    a[1] = 7
    c = blake3(a, a)
    p = 1
    p[1] = c[0]
    p[GEN] = c[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    warm_setup(1);

    let five = F128::new(5, 0);
    let seven = F128::new(7, 0);
    let want = compress([five, seven], [five, seven]);

    let (proof, stats) = prove(&program, want);
    assert_eq!(stats.counts[5], 1, "one BLAKE3 instruction");
    verify(&program, &want, &proof).expect("StackArray self-hash verifies");

    let mut bad = want;
    bad[0] += F128::ONE;
    assert!(verify(&program, &bad, &proof).is_err(), "wrong digest must be rejected");
}

/// A general (non-blake3) `StackArray(3)`: indexed writes, an indexed read feeding
/// an arithmetic write into another slot, then two slots published. Confirms the
/// stack cells are plain consecutive frame cells addressable by index.
#[test]
fn stack_array_indexing() {
    let src = "\
def main():
    sa = StackArray(3)
    sa[0] = 3
    sa[1] = 4
    sa[2] = sa[0] + sa[1]
    p = 1
    p[1] = sa[2]
    p[GEN] = sa[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    // `+` is XOR: 3 ^ 4 = 7. Published: (sa[2], sa[1]) = (7, 4).
    let want = [F128::new(7, 0), F128::new(4, 0)];
    let (proof, stats) = prove(&program, want);
    assert_eq!(stats.counts[5], 0, "no BLAKE3 here");
    verify(&program, &want, &proof).expect("StackArray indexing verifies");
}
