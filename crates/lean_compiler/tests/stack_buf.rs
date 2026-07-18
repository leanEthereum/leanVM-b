//! `StackBuf` — a run of consecutive frame (stack) cells in the zkDSL. Indexed
//! reads/writes go straight to `base+k` (no heap deref), and a size-2 `StackBuf`
//! is a `sha256` operand: its two canonical 128-bit cells hold the 256-bit value, so
//! `sha256(a, b, out)` reads them in place with no copies (a self-hash
//! `sha256(h, h, out)` aliases one pair into both input operands) and writes
//! the digest into the pre-allocated pair `out`.
//!
//! Since these DSL scalars are K-embedded F192 cells, a `StackBuf(2)` written
//! cell-by-cell holds the flock words `[v0, 0, v1, 0]`
//! — the reference `compress` below is fed that lane layout.

use lean_compiler::{compile, parse};
use lean_vm::sha256_flock::warm_setup;
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192};

/// `SHA256(a, b)` reference (matches `cpu::sha256_compress`): the eight words
/// laid little-endian into 64 bytes, hashed, digest split into four `F64` words.
fn compress(a: [F64; 4], b: [F64; 4]) -> [F64; 4] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(8).zip(a.into_iter().chain(b)) {
        slot.copy_from_slice(&w.0.to_le_bytes());
    }
    let d = primitives::sha256::compress(&input);
    std::array::from_fn(|k| F64(u64::from_le_bytes(d[8 * k..8 * k + 8].try_into().unwrap())))
}

/// The two 128-bit digest cells of `compress(a, b)` as `F192`s (lo = word 0/2,
/// hi = word 1/3) — what a `sha256(...)` output `StackBuf(2)` holds cell-by-cell.
fn digest_cells(a: [F64; 4], b: [F64; 4]) -> [F192; 2] {
    let d = compress(a, b);
    [F192::new(d[0].0, d[1].0, 0), F192::new(d[2].0, d[3].0, 0)]
}

/// A size-2 `StackBuf` fed to `sha256` as a self-hash `sha256(h, h)`, then the
/// digest's two 128-bit cells published to `m[0], m[1]`. Proves and verifies, and
/// a wrong published digest is rejected — so the whole path (StackBuf load →
/// aliased sha256 → stack read → publish) is exercised end-to-end.
#[test]
fn stack_buf_sha256_self_hash() {
    let src = "\
def main():
    a = StackBuf(2)
    a[0] = 5
    a[1] = 7
    c = StackBuf(2)
    sha256(a, a, c)
    p = 1
    p[1] = c[0]
    p[GEN] = c[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    warm_setup(1);

    // Each cell holds one scalar in its low lane, so the hashed words are [5,0,7,0].
    let h = [F64(5), F64(0), F64(7), F64(0)];
    let want = digest_cells(h, h);

    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[5], 1, "one SHA256 instruction");
    verify(&program, &want, &proof).expect("StackBuf self-hash verifies");

    let mut bad = want;
    bad[0] += F192::ONE;
    assert!(verify(&program, &bad, &proof).is_err(), "wrong digest must be rejected");
}

/// A general (non-sha256) `StackBuf(3)`: indexed writes, an indexed read feeding
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
    let want = [F192::from(F64(7)), F192::from(F64(4))];
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[5], 0, "no SHA256 here");
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
    let want = [F192::from(F64(5)), F192::from(F64(5))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
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

/// An `@inline` may return a `StackBuf` *and* a scalar together (a tuple bind):
/// the `StackBuf` slot aliases its cell run into the caller (zero copies, usable
/// as a StackBuf downstream — here fed straight back into a second call, the
/// MD-chain idiom), while the scalar slot binds a value cell. This is the fused
/// `state, x = read_obs(state, cursor)` shape the recursion guest relies on.
#[test]
fn inline_returns_stackbuf_and_scalar() {
    warm_setup(1);
    let src = "\
def main():
    s = StackBuf(2)
    s[0] = 5
    s[1] = 7
    s, x = step(s, 9)
    s, y = step(s, x)
    p = 1
    p[1] = s[0]
    p[GEN] = s[1]
    return

@inline
def step(state, v):
    tg = StackBuf(2)
    tg[0] = v
    tg[1] = 3
    nb = StackBuf(2)
    sha256(state, tg, nb)
    return nb, v
";
    let program = compile(&parse(src).expect("parse"));

    // Each cell = one scalar in its low lane, so a StackBuf(2) hashes words
    // [c0, 0, c1, 0]. x == v == 9 (the scalar return), so both steps use tag 9.
    let tag = [F64(9), F64(0), F64(3), F64(0)];
    let s1 = compress([F64(5), F64(0), F64(7), F64(0)], tag);
    let s2 = compress(s1, tag); // the returned StackBuf (holding s1's words) fed back in
    let want = [F192::new(s2[0].0, s2[1].0, 0), F192::new(s2[2].0, s2[3].0, 0)];

    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[5], 2, "two SHA-256 instructions (one per inlined step)");
    verify(&program, &want, &proof).expect("inline StackBuf+scalar tuple return verifies");

    let mut bad = want;
    bad[1] += F192::ONE;
    assert!(
        verify(&program, &bad, &proof).is_err(),
        "wrong published state must be rejected"
    );
}

/// An `@inline` may also alias-return a folded **g-address** among its values:
/// `fs, x, cur = step(fs, cur)` hands back the sponge state (StackBuf), the
/// consumed word (scalar), and the ADVANCED cursor (`cursor * GEN`) as a
/// zero-cost folded pointer, so the caller keeps reading through it with no
/// manual `cur *= GEN`. This is the shape `fs_next` uses to walk the stream.
#[test]
fn inline_returns_advanced_cursor() {
    warm_setup(1);
    let src = "\
def main():
    hb = HeapBuf(4)
    hb[1] = 10
    hb[GEN] = 20
    hb[GEN ** 2] = 30
    fs = StackBuf(2)
    fs[0] = 1
    fs[1] = 2
    cur = hb
    fs, a, cur = step(fs, cur)
    fs, b, cur = step(fs, cur)
    v = cur[GEN ** 0]
    p = 1
    p[1] = a + b
    p[GEN] = v
    return

@inline
def step(state, cursor):
    x = cursor[GEN ** 0]
    tg = StackBuf(2)
    tg[0] = x
    tg[1] = 3
    nb = StackBuf(2)
    sha256(state, tg, nb)
    return nb, x, cursor * GEN
";
    let program = compile(&parse(src).expect("parse"));
    // a = hb[0] = 10, b = hb[1] = 20, v = hb[2] = 30 read through the cursor
    // returned twice-advanced. a + b is XOR: 10 ^ 20 = 30.
    let want = [F192::from(F64(30)), F192::from(F64(30))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("inline advanced-cursor return verifies");
}

/// `x = [a, b, c, d]` — the list-literal StackBuf initializer: allocates the run
/// and writes the elements in place, sugar for alloc-then-store. The test mixes a
/// runtime value, a constant, and an expression; feeds the result to sha256; and
/// swaps a buffer through itself (`s = [s[1], s[0], …]` reads the OLD binding,
/// per the let-rebind rule).
#[test]
fn stack_buf_list_literal() {
    warm_setup(1);
    let src = "\
def main():
    s = [5, 7]
    s = [s[1], s[0]]
    t = [s[0] + s[1], 3]
    out = StackBuf(2)
    sha256(s, t, out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    // s = [7, 5] after the swap → words [7,0,5,0]; t = [7 ^ 5, 3] = [2, 3] → [2,0,3,0].
    let want = digest_cells([F64(7), F64(0), F64(5), F64(0)], [F64(2), F64(0), F64(3), F64(0)]);
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[5], 1, "one SHA256 instruction");
    verify(&program, &want, &proof).expect("list-literal StackBuf verifies");
}

/// A list literal anywhere but the RHS of an assignment is rejected with a
/// clear message, not lowered as a phantom scalar.
#[test]
#[should_panic(expected = "a list literal must be bound to a name")]
fn stack_buf_list_literal_as_value_rejected() {
    let src = "def main():\n    x = 1 + [2, 3]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A compile-time heap index past the buffer's declared size is a compile
/// error, not a runtime wild deref.
#[test]
#[should_panic(expected = "heap index 8 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    x = hb[GEN ** 8]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// The bound follows shifted aliases back to the original buffer: a pointer
/// alias `row = hb * GEN ** k` checks `row[GEN ** j]` against size − k.
#[test]
#[should_panic(expected = "heap index 9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_alias_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    row = hb * GEN ** 6\n    x = row[GEN ** 3]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A hint slice whose end exceeds the buffer is rejected at compile time.
#[test]
#[should_panic(expected = "heap slice 0:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_hint_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hint_witness(hb[0:9], \"w\")\n    x = hb[GEN ** 0]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A sha256 heap slice straddling the buffer end is rejected. The 256-bit
/// operand `hb[7:9]` is two 128-bit cells, so the bound check trips at
/// `7 + 2 = 9 > 8`.
#[test]
#[should_panic(expected = "heap slice 7:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_sha256_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    out = StackBuf(2)\n    sha256(hb[7:9], hb[7:9], out)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// The last in-bounds index still compiles and runs.
#[test]
fn heap_index_boundary_ok() {
    warm_setup(1);
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    row = hb * GEN ** 4\n    y = row[GEN ** 3]\n    assert y == 5\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let pi = [F192::from(F64(3)), F192::from(F64(4))];
    let (proof, _) = prove(&program, pi, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &pi, &proof).expect("boundary access verifies");
}
