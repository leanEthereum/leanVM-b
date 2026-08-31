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

/// An operator missing a side says which operator and which side.
///
/// Every one of these used to report `cannot parse expression \`\``: the empty
/// operand was handed to the expression parser, which had nothing to name. A
/// leading `-` is the common one, since the language has no unary minus.
#[test]
fn an_operator_missing_an_operand_says_so() {
    for (src, want) in [
        ("-3 + 5", "`-` has no left operand"),
        ("1 +", "`+` has no right operand"),
        ("* 2", "`*` has no left operand"),
        ("4 // ", "`//` has no right operand"),
    ] {
        let err = lean_compiler::parse_const(src).expect_err(src);
        assert!(err.contains(want), "{src}: got `{err}`, wanted `{want}`");
    }
}

/// A `for` body that assigns to an enclosing name says why that cannot work.
///
/// The capture set drops every name the body binds, so a body that ASSIGNS to
/// an enclosing name also loses the read that precedes the assignment, and the
/// read arrived at lowering as a bare "unbound variable". That is the loop-carry
/// limitation, not a typo: the tail-recursive helper threads its captures in and
/// never out, so an accumulator cannot come back. The `StackBuf` form of the
/// same limitation already said so; the scalar form did not.
#[test]
fn a_loop_that_cannot_carry_a_value_says_so() {
    let accumulator = "\
def main():
    s = GEN ** 0
    for i in mul_range(1, 8):
        s = s * GEN
    p = GEN ** 0
    p[1] = s
    p[GEN] = GEN ** 0
    return
";
    let ast = parse(accumulator).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
        panic!("a loop-carried accumulator was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(msg.contains("the loop cannot carry it"), "got `{msg}`");

    // A real typo, outside any loop, still gets the plain message.
    let typo = "def main():\n    p = GEN ** 0\n    p[1] = nosuch\n    p[GEN] = GEN ** 0\n    return\n";
    let ast = parse(typo).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
        panic!("a typo was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(msg.contains("unbound variable `nosuch`") && !msg.contains("loop"), "got `{msg}`");
}

/// A compile-time branch is decided by a regime the author names.
///
/// The fold decides on the integer reading while the runtime test of the same
/// condition compares field values, so the two contradict each other whenever a
/// side's readings do. `3 + 1` is the integer 4 and the field element
/// `3 XOR 1` = 2, and `if 3 + 1 == 4` used to fold into an arm whose own
/// condition is false as a value; `if K == 4: assert K == 4` compiled clean and
/// died at witness generation.
///
/// Neither reading can win: deciding in the field breaks `if 1 + 1 == 2` and
/// every `if i + 1 == n` in an `unroll`, and cannot read `-`, `//` or `%` at
/// all. So an ambiguous condition is rejected, and `const(...)` is how the
/// author says the integer regime was meant.
#[test]
fn an_ambiguous_compile_time_branch_must_be_declared() {
    let prog = |cond: &str| {
        format!(
            "def main():
    hb = HeapBuf(4)
    if {cond}:
        hb[GEN ** 0] = 5
    else:
        hb[GEN ** 0] = 7
    p = GEN ** 0
    p[1] = hb[GEN ** 0]
    p[GEN] = GEN ** 0
    return
"
        )
    };
    let fold = |cond: &str| {
        let program = compile(&parse(&prog(cond)).unwrap_or_else(|e| panic!("{cond}: {e}")));
        let want = [F192::new(5, 0, 0), g_pow(0).into()];
        let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
        verify(&program, &want, &proof).unwrap_or_else(|e| panic!("`{cond}` did not take the then arm: {e:?}"));
    };
    // Declared, so it folds with integer arithmetic and the arm runs.
    fold("const(3 + 1 == 4)");
    fold("const(1 + 1 == 2)");
    fold("const(1 + 1 == 3 - 1)");
    // Only the field can read these, and `const(...)` decides them too. A plain
    // `if` must not: folding one would rescope its arm.
    fold("const(GEN ** 3 == GEN ** 3)");
    fold("const(2 ** 40 == 2 ** 40)");
    // Undeclared but unambiguous (6 either way), so it folds as it always did.
    fold("2 * 3 == 6");

    // Undeclared and ambiguous: rejected rather than silently decided. The
    // last three are the same condition as the first with the OTHER side
    // written using an operator the field cannot read, which is how the first
    // version of this check let them through: it compared the two sides'
    // verdicts, and `try_field_const` has no arm for `-`, `//` or `%`, so one
    // missing reading disabled the whole guard. The check is per side now.
    for cond in [
        "3 + 1 == 4",
        "1 + 1 == 2",
        "1 + 1 == 3 - 1",
        "1 + 1 == 8 // 4",
        "1 + 1 == 9 % 7",
    ] {
        let src = prog(cond);
        let ast = parse(&src).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("`{cond}` was accepted");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(msg.contains("where a value is wanted"), "{cond}: got `{msg}`");
    }
    // Declared, but not actually decidable while compiling.
    let src = prog("const(hb == 4)");
    let ast = parse(&src).expect("parses");
    let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
        panic!("a runtime `if const(...)` was accepted");
    };
    let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
    assert!(msg.contains("asks for a compile-time decision"), "got `{msg}`");
}

/// A string literal is one opaque token.
///
/// Two passes used to read structure out of the middle of one. Comments were
/// stripped with `raw.split('#')`, so a `#` in a stream name truncated the line,
/// and the shortened line often still parsed. Bracket depth was counted without
/// any notion of a string, so every top-level splitter (arguments, `+`/`-`,
/// `*`//`/`%`, `**`, augmented assignment, comparisons) read a `,` or a `]`
/// spelled inside the name as structure: this call split into three arguments.
#[test]
fn a_string_literal_is_not_scanned_for_syntax() {
    let src = "\
def main():
    rb = StackBuf(1)
    hint_witness(rb[0:1], \"x,y#z]w\")
    p = GEN ** 0
    p[1] = rb[0]
    p[GEN] = GEN ** 0
    return
";
    let mut program = compile(&parse(src).expect("a `,`, `#` or `]` inside a string is part of the name"));
    program.set_witness("x,y#z]w", vec![vec![F192::new(7, 0, 0)]]);
    let want = [F192::new(7, 0, 0), g_pow(0).into()];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("the stream name survived parsing intact");
}

/// Naming a constant may not change what it means.
///
/// `K = 3 + 1` folds two ways at once. In the field, where a value expression's
/// constants live, it is `3 XOR 1` = 2 = `g^1`. As a compile-time integer, which
/// is what an index position wants, it is 4. A second g-power recognizer used to
/// match `Expr::Var` against the integer binding and read those bits as an
/// exponent, so `K` was `g^1` as a value and `g^2` as an index: one name, two
/// meanings, in one function. Spelling the constant inline was unaffected, since
/// the integer view only ever reached a *name*.
///
/// The buffer holds a distinct value per cell, so the proof pins which cell the
/// index named rather than merely that it compiled.
#[test]
fn naming_a_constant_does_not_change_which_heap_cell_it_names() {
    let src = "\
def main():
    rb = StackBuf(1)
    hint_witness(rb[0:1], \"r\")
    r = rb[0]
    hb = HeapBuf(16)
    hint_witness(hb[0:4], \"vals\")
    K = 3 + 1
    x = hb[(r * r) * K]
    p = GEN ** 0
    p[1] = x
    p[GEN] = GEN ** 0
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("r", vec![vec![g_pow(0).into()]]);
    program.set_witness(
        "vals",
        vec![(10u64..14).map(|v| F192::new(v, 0, 0)).collect()],
    );
    // `r` is 1, so the index is `K` itself: cell 1, holding 11. Reading the
    // integer view instead would name cell 2, holding 12.
    let want = [F192::new(11, 0, 0), g_pow(0).into()];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("the index means what the value means");
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
