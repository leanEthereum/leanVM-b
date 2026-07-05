//! `StackBuf` — a run of consecutive frame (stack) cells in the zkDSL. Indexed
//! reads/writes go straight to `base+k` (no heap deref), and a size-4 `StackBuf`
//! is a `blake3` operand: its four cells hold the 256-bit value's four 64-bit
//! words, so `blake3(a, b, out)` reads them in place with no copies (a self-hash
//! `blake3(h, h, out)` aliases one quad into both input operands) and writes
//! the digest into the pre-allocated quad `out`.

use leanvm_b::blake3_flock::warm_setup;
use leanvm_b::compiler::{compile, parse};
use leanvm_b::cpu::{prove, verify};
use leanvm_b::field::F64;

/// `BLAKE3(a, b)` reference (matches `cpu::blake3_compress`): the eight words
/// laid little-endian into 64 bytes, hashed, digest split into four `F64` words.
fn compress(a: [F64; 4], b: [F64; 4]) -> [F64; 4] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(8).zip(a.into_iter().chain(b)) {
        slot.copy_from_slice(&w.0.to_le_bytes());
    }
    let d = blake3::hash(&input);
    let d = d.as_bytes();
    std::array::from_fn(|k| F64(u64::from_le_bytes(d[8 * k..8 * k + 8].try_into().unwrap())))
}

/// A size-4 `StackBuf` fed to `blake3` as a self-hash `blake3(h, h)`, then the
/// digest's first two words published to `m[0], m[1]`. Proves and verifies, and a
/// wrong published digest is rejected — so the whole path (StackBuf load →
/// aliased blake3 → stack read → publish) is exercised end-to-end.
#[test]
fn stack_buf_blake3_self_hash() {
    let src = "\
def main():
    a = StackBuf(4)
    a[0] = 5
    a[1] = 7
    a[2] = 11
    a[3] = 13
    c = StackBuf(4)
    blake3(a, a, c)
    p = 1
    p[1] = c[0]
    p[GEN] = c[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    warm_setup(1);

    let h = [F64(5), F64(7), F64(11), F64(13)];
    let d = compress(h, h);
    let want = [d[0], d[1]];

    let (proof, stats) = prove(&program, want);
    assert_eq!(stats.counts[5], 1, "one BLAKE3 instruction");
    verify(&program, &want, &proof).expect("StackBuf self-hash verifies");

    let mut bad = want;
    bad[0] += F64::ONE;
    assert!(verify(&program, &bad, &proof).is_err(), "wrong digest must be rejected");
}

/// A general (non-blake3) `StackBuf(3)`: indexed writes, an indexed read feeding
/// an arithmetic write into another slot, then two slots published. Confirms the
/// stack cells are plain consecutive frame cells addressable by index.
#[test]
fn stack_buf_indexing() {
    let src = "\
def main():
    sa = StackBuf(3)
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
    let want = [F64(7), F64(4)];
    let (proof, stats) = prove(&program, want);
    assert_eq!(stats.counts[5], 0, "no BLAKE3 here");
    verify(&program, &want, &proof).expect("StackBuf indexing verifies");
}

/// A StackBuf index literal that does not fit `u32` is rejected at compile time,
/// not silently truncated modulo 2^32 (which would resolve `sa[2^32]` to `sa[0]`).
#[test]
#[should_panic(expected = "does not fit in u32")]
fn stack_buf_index_overflow_rejected() {
    let src = "def main():\n    sa = StackBuf(2)\n    x = sa[4294967296]\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// Rebinding a StackBuf name to a scalar clears the stack binding, so the name
/// is a plain scalar afterward (the old bug left a stale `stacks` entry that made
/// `x` still look like a StackBuf, panicking on scalar use).
#[test]
fn stack_buf_rebind_to_scalar() {
    let src = "def main():\n    x = StackBuf(2)\n    x = 5\n    p = 1\n    p[1] = x\n    p[GEN] = x\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let want = [F64(5), F64(5)];
    let (proof, _) = prove(&program, want);
    verify(&program, &want, &proof).expect("rebound-scalar program verifies");
}

/// A StackBuf from the enclosing scope referenced inside a `for` loop cannot be
/// captured; the compiler rejects it with a clear message (not a misleading
/// "unbound variable" from the capture being silently dropped).
#[test]
#[should_panic(expected = "cannot be captured into a `for` loop")]
fn stack_buf_loop_capture_rejected() {
    let src = "def main():\n    h = StackBuf(2)\n    h[0] = 1\n    h[1] = 2\n    for i in mul_range(1, GEN ** 4):\n        x = h[0]\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}
