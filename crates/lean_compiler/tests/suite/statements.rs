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

/// Every diagnostic names its source line. The line vector used to carry the
/// INDENT, not the source index, and the collection loop skips blanks, comments
/// and imports without counting, so nothing could name one: against a
/// 3,274-line guest an error read `inconsistent indentation` and no more.
#[test]
fn a_parse_error_names_its_source_line() {
    // Counting from 1: blank, comment, constant, blank, blank, def, let, error.
    let src = "\n# a comment\nV = 8\n\n\ndef main():\n    x = 4\n    x != y\n    return\n";
    let err = parse(src).unwrap_err();
    assert!(err.starts_with("line 8:"), "{err}");

    // A constant declaration, above the `def`s and parsed by a different loop.
    let konst = "\nN = 1\n\nM = 1 +\n\ndef main():\n    return\n";
    assert!(parse(konst).unwrap_err().starts_with("line 4:"), "{konst}");

    // Inside a block, past a blank line.
    let block =
        "\n\ndef main():\n    a = StackBuf(2)\n\n    for i in mul_range(1, 10):\n        a[0] = 1\n    return\n";
    assert!(parse(block).unwrap_err().starts_with("line 6:"));
}

/// The four diagnostics raised where no `func`/`stmt` frame is open: those two
/// stamp the line they were ENTERED on, so an enclosing header would be named
/// instead of the line that is wrong. `inconsistent indentation` is the one the
/// whole change exists for, and stamping it from the enclosing frame put it
/// 1,074 lines away from the fault in the real guest.
#[test]
fn an_error_raised_between_frames_still_names_its_line() {
    // 1 blank, 2 def, 3 let, 4 if, 5 body, 6 stray deeper indent.
    let indent = "\ndef main():\n    x = 4\n    if x == 4:\n        x = 5\n          x = 6\n    return\n";
    assert!(parse(indent).unwrap_err().starts_with("line 6:"), "{:?}", parse(indent));

    // 1 blank, 2 @inline, 3 the broken def.
    let deco = "\n@inline\nde f(x):\n    return x\n";
    assert!(parse(deco).unwrap_err().starts_with("line 3:"), "{:?}", parse(deco));

    // 1 blank, 2 def, 3 let, 4 if, 5 body, 6 the broken elif.
    let elif = "\ndef main():\n    x = 4\n    if x == 4:\n        x = 5\n    elif x ~~ 5:\n        x = 6\n    return\n";
    assert!(parse(elif).unwrap_err().starts_with("line 6:"), "{:?}", parse(elif));

    // 1 blank, 2 def, 3 let, 4 match, 5 case 0, 6 body, 7 the non-consecutive case.
    let case = "\ndef main():\n    x = GEN ** 0\n    match log(x):\n        case 0:\n            x = 5\n        case 2:\n            x = 6\n    return\n";
    assert!(parse(case).unwrap_err().starts_with("line 7:"), "{:?}", parse(case));
}

/// A replacement carrying a newline shifts every later line, so the numbers
/// above would be wrong and the injected text would land at whatever
/// indentation it fell on. A `#` is the same shape of hazard: it truncates the
/// rest of the line and changes the compiled program with no diagnostic. All
/// 134 of the guest's placeholders are clean; this keeps it that way.
#[test]
fn a_multi_line_placeholder_is_rejected() {
    let mut reps = std::collections::BTreeMap::new();
    let src = "FOO = 1\n\ndef main():\n    return\n";
    for bad in ["1\nz = 9", "1 #"] {
        reps.insert("FOO".to_string(), bad.to_string());
        let err = lean_compiler::parse_with_replacements(src, &reps).unwrap_err();
        assert!(err.contains("would reshape the line"), "{bad}: {err}");
    }
}

/// A lowering error names its line too, not just a parse error. `lower.rs` works
/// in frame cells and program counters, so the statement's line is the last
/// place that knows where the program said it: 30 diagnostics used to print a
/// Rust `Debug` dump of an AST node and nothing else.
#[test]
fn a_lowering_error_names_its_source_line() {
    // 1 blank, 2 def, 3 let, 4 store, 5 blank, 6 let, 7 the unbound read.
    let src = "\ndef main():\n    hb = HeapBuf(4)\n    hb[GEN] = 7\n\n    p = GEN ** 0\n    p[1] = nope\n    return\n";
    let err = std::panic::catch_unwind(|| {
        compile(&parse(src).expect("parse"));
    })
    .expect_err("an unbound variable must abort");
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()).unwrap_or_default());
    assert!(msg.starts_with("line 7:"), "{msg}");
}

/// And a check that fails at witness generation names it, which is the one that
/// matters day to day: a failed guest `assert` surfaces as a write-once
/// conflict, and `AGENTS.md` used to say to disassemble around the reported pc.
#[test]
fn a_failed_assert_names_its_source_line() {
    // 1 blank, 2 def, 3 let, 4 blank, 5 the assert that cannot hold.
    let src = "\ndef main():\n    x = GEN ** 3\n\n    assert x == GEN ** 4\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let err = std::panic::catch_unwind(|| {
        program.execute([F192::ZERO; 2]);
    })
    .expect_err("the assert cannot hold");
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()).unwrap_or_default());
    assert!(msg.contains("line 5"), "{msg}");
}

/// An `@inline` body lowers through the CALLER's `FnLower`, so its statements
/// move `cur_line`. Without restoring it, every instruction the caller emitted
/// after the call was blamed on whatever line the callee ended on: a line that
/// cannot fail, reported with confidence.
#[test]
fn an_inline_call_does_not_steal_the_call_site_line() {
    // 1 blank, 2 @inline, 3 def, 4 let, 5 return, 6-7 blank, 8 def main, ... 12 the assert.
    let src = "\n@inline\ndef idf(x):\n    y = x * x\n    return y\n\n\ndef main():\n    hb = HeapBuf(4)\n    hb[GEN] = GEN ** 3\n    a = hb[GEN]\n    assert idf(a) == GEN\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let err = std::panic::catch_unwind(|| {
        program.execute([F192::ZERO; 2]);
    })
    .expect_err("the assert cannot hold");
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .unwrap_or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()).unwrap_or_default());
    assert!(msg.contains("line 12"), "the call site, not the callee's line 5: {msg}");
}

/// The fill blocks are not source code, so they carry the unknown line rather
/// than whatever `main` happened to end on. They are most of a small program's
/// instructions, so blaming them on a real line makes the table mostly wrong.
#[test]
fn fill_blocks_carry_no_source_line() {
    let src = "\ndef main():\n    hb = HeapBuf(4)\n    hb[GEN] = 7\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let start = program.filler.first().map(|b| b.pc).expect("main carries fill blocks") as usize;
    assert!(
        program.src_lines[start..].iter().all(|&l| l == 0),
        "a fill block must not be attributed to a source line"
    );
    assert!(
        program.src_lines[..start].iter().any(|&l| l != 0),
        "real code keeps its lines"
    );
}

/// A dispatched `match_range` join reads one cell per bound name, but a callee
/// returning a `StackBuf` flattens it into several ABI cells, so the name would
/// silently bind the run's FIRST cell and the rest would be written where
/// nothing reads them. The guard against that is `all(is scalar)`; negating it
/// as `all(is not scalar)` rather than `any(is not scalar)` left it firing only
/// when EVERY return is a buffer, so a `(scalar, StackBuf)` pair walked through
/// and no existing test noticed.
#[test]
#[should_panic(expected = "StackBuf return cannot cross a dispatched join")]
fn a_mixed_stack_buf_return_cannot_cross_a_dispatched_join() {
    let src = "\
@inline
def f(k: Const):
    s = StackBuf(2)
    s[0] = GEN ** 7
    s[1] = GEN ** 9
    return GEN ** k, s

def main():
    x = GEN
    a, b = match_range(log(x), range(0, 2), lambda i: f(i))
    assert a == a
    assert b == GEN ** 7
    return
";
    compile(&parse(src).expect("parse"));
}
