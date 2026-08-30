//! The value-numbering pass (`cse.rs`) folds away pure instructions the lowerer
//! emitted twice. These programs pin the cases where a "duplicate" is NOT dead.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

/// A returned value that repeats a constant computed earlier in the same
/// function. The return slot lives in the callee frame and is read by the
/// CALLER, so eliminating that write leaves the caller reading an unwritten
/// (prover-chosen) cell: `walk` in the XMSS guest returned a flag exactly this
/// way, and folding it produced a proof whose caller-side assert failed.
#[test]
fn duplicate_constant_in_a_return_slot_survives() {
    let src = "\
def tag(x):
    # `marker` is the same constant the flag below returns, and it is computed
    # first, so the flag's `SET` is a textual duplicate of it.
    marker = 7
    return x * marker, 7

def main():
    v, flag = tag(GEN ** 3)
    p = 1
    p[1] = v
    p[GEN] = flag
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(3)) * F192::from(F64(7)), F192::from(F64(7))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("returned duplicate constant is preserved");
}

/// An argument slot written with a value that already exists in the caller: the
/// callee reads its arguments out of its own frame, so the store must stay.
#[test]
fn duplicate_argument_value_survives() {
    let src = "\
def add_both(a, b):
    return a + b

def main():
    k = GEN ** 5
    # Both arguments are the same expression, and the sum is computed here too,
    # so every operand the call needs has a duplicate in this frame.
    local = k + k
    s = add_both(k, k)
    p = 1
    p[1] = s + local
    return
";
    let program = compile(&parse(src).expect("parse"));
    // (k + k) + (k + k) == 0 in characteristic two.
    let want = [F192::ZERO, F192::ZERO];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("duplicated call arguments are preserved");
}

/// A duplicate on one side of a branch must not be folded into the other side's
/// computation: the value map is cleared at block boundaries, so each arm
/// recomputes what it needs. If it were folded, the untaken arm's cell would be
/// unwritten at the join.
#[test]
fn duplicates_are_not_folded_across_a_branch() {
    let src = "\
def main():
    x = GEN ** 3
    r = HeapBuf(2)
    # The same constant in both arms: folding the second into the first would
    # make the taken path store from a cell the untaken path was to write.
    if x == GEN ** 3:
        r[1] = GEN ** 4
    else:
        r[1] = GEN ** 4
    p = 1
    p[1] = r[1]
    p[GEN] = x
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(4)), F192::from(g_pow(3))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("both branches keep their own constant");
}

/// The assert idiom is `XOR fp[t] = a ^ b` then `SET fp[t] = 0`, which panics as
/// a write-once conflict when `a != b`. Both instructions write `fp[t]`, so
/// neither may be folded away: otherwise a failing assert would silently pass.
/// Here the compared difference is also computed as an ordinary value, giving the
/// assert's `XOR` a duplicate to be folded into.
#[test]
fn assert_survives_a_duplicated_comparison() {
    let src = "\
def main():
    a = GEN ** 9
    b = GEN ** 9
    # The same XOR the assert needs, as a live value.
    diff = a + b
    assert a == b
    p = 1
    p[1] = diff
    p[GEN] = a
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::ZERO, F192::from(g_pow(9))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("passing assert still verifies");
}

/// The same shape, but with the assert failing: it must still panic (the `SET`
/// that collides with the `XOR` was not eliminated).
#[test]
#[should_panic(expected = "write-once conflict")]
fn failing_assert_still_conflicts() {
    let src = "\
def main():
    a = GEN ** 9
    b = GEN ** 10
    diff = a + b
    assert a == b
    p = 1
    p[1] = diff
    p[GEN] = a
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::ZERO, F192::from(g_pow(9))];
    let _ = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
}

/// A hint at the end of a runtime branch is attached to a no-op anchor by the
/// lowerer. Even when that anchor repeats an earlier pure instruction, CSE must
/// retain it: moving the hint to the next textual instruction would move it to
/// the join and execute it when the branch is not taken.
#[test]
fn trailing_branch_hint_stays_in_its_branch() {
    let src = "\
def main():
    flag = StackBuf(1)
    hint_witness(flag, \"flag\")
    data = StackBuf(1)
    if flag[0] == 1:
        print(\"anchor\", flag[0])
        hint_witness(data, \"data\")
    p = 1
    p[1] = flag[0]
    p[GEN] = 0
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("flag", vec![vec![F192::ZERO]]);
    let want = [F192::ZERO, F192::ZERO];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("untaken branch must not consume its witness");
}

/// A BLAKE2s chaining value names a CONSECUTIVE PAIR, so neither half may be
/// folded into a canonical elsewhere and the base may not be rewritten: a
/// substitution speaks for one cell, and redirecting the base silently redirects
/// the second word too. `rewrite_reads` used to map `cv` like any single-cell
/// read, so when the first of the two assembling copies duplicated an earlier
/// copy of the same source, the compression absorbed the OTHER pair's second
/// word. Silent, and a soundness break in a transcript.
///
/// The two compressions here differ in nothing but their chaining value, and
/// their two `cv` pairs share a first word, which is what made the first copy a
/// duplicate. If either pair is rewritten or dropped, the digests coincide and
/// the inequality fails at witness generation.
#[test]
fn a_chaining_value_pair_is_neither_rewritten_nor_dropped() {
    let src = "\
def main():
    hb = HeapBuf(4)
    hb[1] = GEN ** 11
    hb[GEN] = GEN ** 22
    hb[GEN ** 2] = GEN ** 33
    hb[GEN ** 3] = GEN ** 44
    x = hb[1]
    y = hb[GEN]
    z = hb[GEN ** 2]
    w = hb[GEN ** 3]
    msg = StackBuf(4)
    msg[0] = y
    msg[1] = y
    msg[2] = y
    msg[3] = y
    t = StackBuf(2)
    t[0] = x
    t[1] = z
    o1 = StackBuf(2)
    blake2s(msg[0:2], msg[2:4], o1, cv=t, counter=64, final=1)
    s = StackBuf(2)
    s[0] = x
    s[1] = w
    o2 = StackBuf(2)
    blake2s(msg[0:2], msg[2:4], o2, cv=s, counter=64, final=1)
    assert o1[0] != o2[0]
    p = 1
    p[1] = x
    p[GEN] = y
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(11)), F192::from(g_pow(22))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("each compression absorbs its own chaining value");
}
