//! Statement forms that used to be accepted and mean something else. Each of
//! these compiled clean before, so the pin is that they are now REJECTED: a
//! diagnostic is the whole fix.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F192, g_pow};

/// A name is a plain identifier. Two different mistakes arrive here, and both
/// used to compile: a mis-split statement (`x /= 2` became a binding named
/// `x /`) and a top-level constant reused as a parameter or local. Constants
/// are substituted textually before parsing, so `V = 8` followed by
/// `def scale(V)` gave a parameter literally named `8` and a body reading the
/// constant: `scale(3)` returned 16.
#[test]
fn a_constant_may_not_be_reused_as_a_parameter() {
    let src = "\
V = 8

def scale(V):
    return V * 2

def main():
    p = GEN ** 0
    p[1] = scale(3)
    p[GEN] = scale(3)
    return
";
    let err = parse(src).expect_err("a parameter may not reuse a constant's name");
    assert!(err.contains("not a valid parameter name"), "{err}");
}

/// `/=` and `**=` are not compound assignments here. `split_aug` declined them
/// and `split_assign` then split the bare `=`, leaving a dead binding and the
/// old value in place. `/` being a real runtime field operation is what made
/// `x /= y` look legal.
#[test]
fn an_unsupported_compound_assignment_is_rejected() {
    let body = |stmt: &str| {
        format!(
            "\
def main():
    x = 4
    {stmt}
    p = GEN ** 0
    p[1] = x
    p[GEN] = x
    return
"
        )
    };
    for (stmt, want) in [
        ("x /= 2", "`/=` is not supported"),
        ("x **= 2", "`**=` is not supported"),
    ] {
        let err = parse(&body(stmt)).expect_err(stmt);
        assert!(err.contains(want), "{stmt}: {err}");
    }
    // The five that ARE supported still desugar.
    let ok = body("x += 1\n    x *= 2\n    x //= 2\n    x %= 3\n    x -= 1");
    compile(&parse(&ok).expect("the supported compound assignments parse"));
}

/// A bare comparison is not a statement. `split_assign` used to split `x != y`
/// on its `=` into a binding named `x !`, so an `assert` that lost its keyword
/// to an edit compiled to nothing at all: in a verifier, a deleted check with
/// no diagnostic and no cycle to notice.
#[test]
fn a_bare_comparison_is_rejected() {
    let body = |stmt: &str| {
        format!(
            "\
def main():
    x = 4
    y = 5
    {stmt}
    p = GEN ** 0
    p[1] = x
    p[GEN] = x
    return
"
        )
    };
    for stmt in ["x != y", "x == y", "x <= y", "x >= y", "x < y", "x > y"] {
        let err = parse(&body(stmt)).expect_err(stmt);
        assert!(err.contains("is a comparison, not a statement"), "{stmt}: {err}");
    }
    // The equality forms name the fix; the order forms say they are not predicates.
    assert!(parse(&body("x != y")).unwrap_err().contains("write `assert x != y`"));
    assert!(parse(&body("x < y")).unwrap_err().contains("order facts come from"));
}

/// A stack store whose value IS its own destination recorded `alias[dst] = dst`,
/// and `word_src` chased that forever: a compiler that never returns, with no
/// output at all. Two stores could close the same loop in two steps. Both are
/// now no-ops (write-once makes a second write of the same value one), and the
/// documented swap must keep working.
#[test]
fn a_self_referential_stack_store_terminates() {
    let cases = [
        // one statement
        "    s[0] = s[0]\n",
        // two, closing the cycle
        "    s[0] = s[1]\n    s[1] = s[0]\n",
    ];
    for tail in cases {
        let src = format!(
            "\
def main():
    s = StackBuf(2)
{tail}    p = 1
    p[1] = s[0]
    p[GEN] = s[0]
    return
"
        );
        compile(&parse(&src).expect("parse")).execute([F192::ZERO; 2]);
    }
    // `s = [s[1], s[0]]` rebinds to a fresh run and must still swap.
    let swap = "\
def main():
    s = StackBuf(2)
    s[0] = 5
    s[1] = 7
    s = [s[1], s[0]]
    p = 1
    p[1] = s[0]
    p[GEN] = s[1]
    return
";
    let want = [
        F192::from(primitives::field::F64(7)),
        F192::from(primitives::field::F64(5)),
    ];
    compile(&parse(swap).expect("parse")).execute(want);
}

/// A `mul_range` stop bound that is a compile-time value but not a power of GEN
/// can never be REACHED: the counter walks by multiplication and exits on
/// equality, so the loop ran forever at witness generation with no diagnostic.
/// The `lo` side was always checked, which made `mul_range(0, GEN ** 3)` a clean
/// parse error while `mul_range(1, 10)` was a hang.
#[test]
fn a_loop_bound_must_be_reachable() {
    let src = "\
def main():
    hb = HeapBuf(8)
    hb[1] = 1
    for i in mul_range(1, 10):
        hb[i * GEN] = hb[i]
    return
";
    let err = parse(src).expect_err("an unreachable stop bound must be rejected");
    assert!(err.contains("is not a power of GEN"), "{err}");

    // A power-of-two literal IS a power of GEN and the walk does reach it, so it
    // must be accepted, and as a compile-time bound rather than a runtime one.
    let ok = src.replace("mul_range(1, 10)", "mul_range(1, 16)");
    compile(&parse(&ok).expect("`16` is `g^4`"));
}

/// A binding made inside one arm of an `if` is local to that arm, so the other
/// arm reads the OUTER binding and the loop must capture it. `free_vars_stmt`
/// threaded one flat set through both arms, so a name rebound anywhere in the
/// body counted as loop-local everywhere and the outer binding was never
/// captured: this legal program failed with `unbound variable`.
#[test]
fn a_branch_local_rebinding_does_not_hide_the_outer_binding() {
    let src = "\
def main():
    hb = HeapBuf(8)
    w = GEN ** 3
    for i in mul_range(1, GEN ** 4):
        if i == GEN:
            w = GEN
            hb[i * GEN] = w
        else:
            hb[i * GEN] = w
    p = GEN ** 0
    p[1] = hb[GEN ** 2]
    p[GEN] = hb[GEN ** 3]
    return
";
    // Cell 2 is written on the taken arm (the branch-local `w = GEN`); cell 3 on
    // the other, from the outer `w`.
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(1)), F192::from(g_pow(3))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("the else arm reads the outer binding");
}

/// `g` is `x`, so a literal `2^k` is `g^k` ONLY while `k < 64`: at and above
/// that the modulus folds the monomial back into the low limb while the
/// literal's bit `k` lands in the next one, the tower coefficient of `y`. The
/// guest's own `Y_TOWER` is exactly `2^64`, machine-generated by `dsl_u128`, so
/// a g-power recognizer without that guard gives one literal two values
/// depending on whether it went through a binding.
#[test]
fn a_power_of_two_literal_is_a_g_power_only_below_two_to_the_64() {
    let src = "\
Y_TOWER = 18446744073709551616

def main():
    yt = Y_TOWER
    a = yt * GEN
    b = Y_TOWER * GEN
    assert a == b
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
";
    let program = compile(&parse(src).expect("parse"));
    // y·x, i.e. the tower coefficient shifted, NOT g^65.
    let want = [F192::new(0, 2, 0); 2];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("2^64 is the tower element y, not g^64");
}

/// A loop body that merely SHADOWS an enclosing `StackBuf` never touches it, so
/// rejecting the program names a capture that is not happening. Scoping the
/// arms took the arm-local binding out of the set the rejection consults, which
/// needs the flat "does the body bind this at all" answer instead.
#[test]
fn a_shadowed_stack_buf_is_not_a_capture() {
    let src = "\
def main():
    sa = StackBuf(2)
    sa[0] = GEN
    sa[1] = GEN ** 2
    hb = HeapBuf(8)
    for i in mul_range(1, GEN ** 3):
        if i == GEN:
            sa = StackBuf(2)
            sa[0] = GEN ** 5
            assert sa[0] == GEN ** 5
        else:
            hb[i] = GEN ** 7
    assert sa[0] == GEN
    return
";
    let exec = compile(&parse(src).expect("parse")).execute([F192::ZERO; 2]);
    assert!(exec.unconstrained_reads.is_empty(), "no prover-chosen read");
}

/// `lower_if` FOLDS a compile-time condition and runs the taken branch without a
/// scope, so its bindings persist exactly like an `unroll` body's. Modelling it
/// as scoped over-captured, and the loop's own self-call then evaluated a name
/// the folded arm had rebound to a `StackBuf`.
#[test]
fn a_folded_branch_keeps_its_bindings() {
    let src = "\
def main():
    hb = HeapBuf(64)
    w = HeapBuf(16)
    for i in mul_range(1, GEN ** 3):
        if 1 == 1:
            w = StackBuf(2)
            w[0] = i
            w[1] = i * GEN
        hb[i] = w[1]
    assert hb[1] == GEN
    return
";
    let exec = compile(&parse(src).expect("parse")).execute([F192::ZERO; 2]);
    assert!(exec.unconstrained_reads.is_empty(), "no prover-chosen read");
}
