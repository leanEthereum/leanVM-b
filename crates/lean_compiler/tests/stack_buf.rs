//! `StackBuf` — a run of consecutive frame (stack) cells in the zkDSL. Indexed
//! reads/writes go straight to `base+k` (no heap deref), and a size-4 `StackBuf`
//! is a `blake3` operand: its four F64 cells hold the 256-bit value, so
//! `blake3(a, b, out)` reads them in place with no copies (a self-hash
//! `blake3(h, h, out)` aliases one run into both input operands) and writes
//! the digest into the pre-allocated four-word run `out`.

use lean_compiler::{compile, parse};
use lean_vm::blake3_flock::warm_setup;
use lean_vm::cpu::{Op, prove, verify};
use primitives::field::F64;

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

fn pi2(a: F64, b: F64) -> [F64; 4] {
    [a, b, F64::ZERO, F64::ZERO]
}

/// A size-4 `StackBuf` fed to `blake3` as a self-hash `blake3(h, h)`, then its
/// four digest words are published. Proves and verifies, and
/// a wrong published digest is rejected — so the whole path (StackBuf load →
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
    p[GEN ** 2] = c[2]
    p[GEN ** 3] = c[3]
    return
";
    let program = compile(&parse(src).expect("parse"));
    warm_setup(1);

    // Each cell holds one F64 word.
    let h = [F64(5), F64(7), F64(11), F64(13)];
    let want = compress(h, h);

    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[7], 1, "one BLAKE3 instruction");
    verify(&program, &want, &proof).expect("StackBuf self-hash verifies");

    let mut bad = want;
    bad[0] += F64::ONE;
    assert!(verify(&program, &bad, &proof).is_err(), "wrong digest must be rejected");
}

/// Copy aliases assembling a hash input are forwarded in 128-bit pairs. The
/// second hash reads the first hash's output chunks directly instead of copying
/// all four words into `t`.
#[test]
fn blake3_forwards_two_word_chunks() {
    let src = "\
def main():
    a = [5, 7, 11, 13]
    h = StackBuf(4)
    blake3(a, a, h)
    t = [h[0], h[1], h[2], h[3]]
    out = StackBuf(4)
    blake3(t, t, out)
    return
";
    let program = compile(&parse(src).expect("parse"));
    let hashes: Vec<Op> = program
        .prog
        .iter()
        .copied()
        .filter(|op| matches!(op, Op::Blake3 { .. }))
        .collect();
    assert_eq!(hashes.len(), 2);
    let first_out = match hashes[0] {
        Op::Blake3 { c, .. } => c,
        _ => unreachable!(),
    };
    match hashes[1] {
        Op::Blake3 { a0, a1, b0, b1, .. } => {
            assert_eq!((a0, a1), (first_out, first_out + 2));
            assert_eq!((b0, b1), (first_out, first_out + 2));
        }
        _ => unreachable!(),
    }
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
    let want = pi2(F64(7), F64(4));
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[7], 0, "no BLAKE3 here");
    verify(&program, &want, &proof).expect("StackBuf indexing verifies");
}

/// A normal (non-`@inline`) function may return a StackBuf. Its cells cross the
/// call boundary through consecutive return slots and bind as a StackBuf in the
/// caller, including through another normal wrapper function.
#[test]
fn normal_function_returns_stackbuf() {
    let src = "\
def main():
    out = forward(5)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = out[2]
    return

def forward(v):
    out = make(v)
    return out

def make(v):
    out = StackBuf(3)
    out[0] = v
    out[1] = v + 3
    out[2] = 11
    return out
";
    let program = compile(&parse(src).expect("parse"));
    // Field addition is XOR: 5 ^ (5 ^ 3) == 3.
    program.execute(pi2(F64(3), F64(11)));
}

/// Tuple returns retain their source-level arity even though a StackBuf member
/// occupies several physical return cells.
#[test]
fn normal_function_returns_stackbuf_and_scalar() {
    let src = "\
def main():
    out, x = make(9)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = x
    return

def make(v):
    out = [v, 6]
    return out, v + 1
";
    let program = compile(&parse(src).expect("parse"));
    program.execute(pi2(F64(15), F64(8)));
}

/// HeapBuf already crosses a normal call as its one-cell pointer. Allocation
/// happened in the callee, so the caller needs no size metadata to dereference
/// and use the returned buffer.
#[test]
fn normal_function_returns_heapbuf_pointer() {
    let src = "\
def main():
    out = make()
    p = 1
    p[1] = out[1]
    p[GEN] = out[GEN]
    return

def make():
    out = HeapBuf(2)
    out[1] = 17
    out[GEN] = 23
    return out
";
    let program = compile(&parse(src).expect("parse"));
    program.execute(pi2(F64(17), F64(23)));
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
    let want = pi2(F64(5), F64(5));
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
    s = StackBuf(4)
    s[0] = 5
    s[1] = 7
    s[2] = 11
    s[3] = 13
    s, x = step(s, 9)
    s, y = step(s, x)
    p = 1
    p[1] = s[0]
    p[GEN] = s[1]
    p[GEN ** 2] = s[2]
    p[GEN ** 3] = s[3]
    return

@inline
def step(state, v):
    tg = StackBuf(4)
    tg[0] = v
    tg[1] = 3
    tg[2] = 4
    tg[3] = 5
    nb = StackBuf(4)
    blake3(state, tg, nb)
    return nb, v
";
    let program = compile(&parse(src).expect("parse"));

    // x == v == 9 (the scalar return), so both steps use tag 9.
    let tag = [F64(9), F64(3), F64(4), F64(5)];
    let s1 = compress([F64(5), F64(7), F64(11), F64(13)], tag);
    let s2 = compress(s1, tag); // the returned StackBuf (holding s1's words) fed back in
    let want = s2;

    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[7], 2, "two BLAKE3 instructions (one per inlined step)");
    verify(&program, &want, &proof).expect("inline StackBuf+scalar tuple return verifies");

    let mut bad = want;
    bad[1] += F64::ONE;
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
    fs = StackBuf(4)
    fs[0] = 1
    fs[1] = 2
    fs[2] = 3
    fs[3] = 4
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
    tg = StackBuf(4)
    tg[0] = x
    tg[1] = 3
    tg[2] = 4
    tg[3] = 5
    nb = StackBuf(4)
    blake3(state, tg, nb)
    return nb, x, cursor * GEN
";
    let program = compile(&parse(src).expect("parse"));
    // a = hb[0] = 10, b = hb[1] = 20, v = hb[2] = 30 read through the cursor
    // returned twice-advanced. a + b is XOR: 10 ^ 20 = 30.
    let want = pi2(F64(30), F64(30));
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("inline advanced-cursor return verifies");
}

/// `x = [a, b, c, d]` — the list-literal StackBuf initializer: allocates the run
/// and writes the elements in place, sugar for alloc-then-store. The test mixes a
/// runtime value, a constant, and an expression; feeds the result to blake3; and
/// swaps a buffer through itself (`s = [s[1], s[0], …]` reads the OLD binding,
/// per the let-rebind rule).
#[test]
fn stack_buf_list_literal() {
    warm_setup(1);
    let src = "\
def main():
    s = [5, 7, 11, 13]
    s = [s[1], s[0], s[3], s[2]]
    t = [s[0] + s[1], 3, s[2] + s[3], 17]
    out = StackBuf(4)
    blake3(s, t, out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    p[GEN ** 2] = out[2]
    p[GEN ** 3] = out[3]
    return
";
    let program = compile(&parse(src).expect("parse"));
    // s = [7, 5] after the swap → words [7,0,5,0]; t = [7 ^ 5, 3] = [2, 3] → [2,0,3,0].
    let want = compress([F64(7), F64(5), F64(13), F64(11)], [F64(2), F64(3), F64(6), F64(17)]);
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[7], 1, "one BLAKE3 instruction");
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

/// A four-word BLAKE3 heap slice straddling the buffer end is rejected.
#[test]
#[should_panic(expected = "heap slice 5:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_blake3_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    out = StackBuf(4)\n    blake3(hb[5:9], hb[5:9], out)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// The last in-bounds index still compiles and runs.
#[test]
fn heap_index_boundary_ok() {
    warm_setup(1);
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    row = hb * GEN ** 4\n    y = row[GEN ** 3]\n    assert y == 5\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let pi = pi2(F64(3), F64(4));
    let (proof, _) = prove(&program, pi, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &pi, &proof).expect("boundary access verifies");
}
