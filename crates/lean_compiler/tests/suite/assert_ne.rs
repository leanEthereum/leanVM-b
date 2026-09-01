//! `assert a != b`: a proof-enforced inequality. It lowers to `XOR x = a + b`,
//! a hinted `inv = x⁻¹`, `MUL p = x·inv` and `SET p = 1`, the write-once
//! conflict on `p` being the assertion. Sound whatever the hint: `x = 0` forces
//! `p = 0`, which cannot then be set to `1`. Three rows and no `JUMP`.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{Op, prove, verify};
use primitives::field::{F64, F192, g_pow};

/// Honest inequality over runtime values: prove + verify pass, and corrupting
/// the public output is still caught (the assert does not disturb the trace).
#[test]
fn assert_ne_end_to_end() {
    let src = "\
def main():
    x = GEN ** 5
    y = GEN ** 7
    z = x * y
    assert z != x
    assert z != y
    p = 1
    p[1] = z
    p[GEN] = x
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(12)), F192::from(g_pow(5))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("inequality program verifies");

    let bad = [F192::from(g_pow(11)), F192::from(g_pow(5))];
    assert!(
        verify(&program, &bad, &proof).is_err(),
        "wrong public input must be rejected"
    );
}

/// The adversarial case: two hinted cells the prover sets *equal*, asserted
/// unequal. Honest witness (distinct) verifies; the equal witness leaves
/// `p = 0·inv = 0`, so `SET p = 1` conflicts and no valid proof continues. No
/// inverse hint can rescue it, which is the whole soundness argument.
#[test]
fn assert_ne_runtime_equal_rejected() {
    let src = "\
def main():
    v = StackBuf(2)
    hint_witness(v[0:2], \"vals\")
    assert v[0] != v[1]
    p = 1
    p[1] = v[0]
    p[GEN] = v[1]
    return
";
    let run = |a: F64, b: F64| -> bool {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("vals", vec![vec![F192::from(a), F192::from(b)]]);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let pi = [F192::from(a), F192::from(b)];
            let (proof, _) = prove(&program, pi, lean_vm::pcs::TEST_LOG_INV_RATE);
            verify(&program, &pi, &proof).is_ok()
        }))
        .unwrap_or(false)
    };
    assert!(run(g_pow(3), g_pow(5)), "distinct hints must verify");
    assert!(!run(g_pow(3), g_pow(3)), "equal hints must be rejected by `assert !=`");
}

/// `assert a != b` inside a `mul_range` body: the check is emitted once per
/// compiled body and runs on every iteration, each of which differs from the
/// fixed value, so the honest loop verifies.
#[test]
fn assert_ne_in_loop() {
    let src = "\
def main():
    c = GEN ** 9
    for i in mul_range(1, GEN ** 6):
        assert i != c
    p = 1
    p[1] = 5
    p[GEN] = 7
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(F64(5)), F192::from(F64(7))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("loop inequality verifies");
}

/// A compile-time-equal literal pair (e.g. after `Const`-arg substitution) is a
/// hard compile error: the assertion could never hold, so it is caught early.
#[test]
#[should_panic(expected = "compile-time-equal")]
fn assert_ne_compile_time_equal_rejected() {
    let src = "def main():\n    assert 5 != 5\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// Opcode counts of a body with and without one `assert !=`.
fn opcode_delta(with: &str, without: &str) -> (i64, i64, i64) {
    let count = |src: &str| {
        let p = compile(&parse(src).expect("parse"));
        let (mut xor, mut mul, mut jump) = (0i64, 0i64, 0i64);
        for op in &p.prog {
            match op {
                Op::Xor { .. } => xor += 1,
                Op::Mul { .. } => mul += 1,
                Op::Jump { .. } => jump += 1,
                _ => {}
            }
        }
        (xor, mul, jump)
    };
    let (a, b) = (count(with), count(without));
    (a.0 - b.0, a.1 - b.1, a.2 - b.2)
}

/// The check costs one `XOR`, one `MUL` and, above all, no `JUMP`: a
/// branch-based lowering would put an `E`-valued condition back on the one table
/// that carries constraints. The `SET` that closes the check is not counted,
/// constant materialisation elsewhere moving with the frame layout.
#[test]
fn assert_ne_emits_no_jump() {
    let body = |extra: &str| {
        format!(
            "\
def main():
    x = GEN ** 5
    y = GEN ** 7
{extra}    p = 1
    p[1] = x
    p[GEN] = y
    return
"
        )
    };
    let delta = opcode_delta(&body("    assert x != y\n"), &body(""));
    assert_eq!(delta, (1, 1, 0), "one XOR, one MUL, no JUMP");
}

/// The check survives cell sharing. `SET p = 1` writes a constant another cell
/// may already hold, and `MUL p = x·inv` a product that could otherwise be
/// shared; both are kept because `p` is written twice, which is what makes the
/// write-once conflict the assertion. Dropping either would delete the check
/// silently, so this pins it: the same product exists elsewhere in the frame,
/// and a `1` is already live.
#[test]
fn assert_ne_survives_cell_sharing() {
    let src = "\
def main():
    one = 1
    v = StackBuf(2)
    hint_witness(v[0:2], \"vals\")
    d = v[0] + v[1]
    spare = d * one
    assert v[0] != v[1]
    p = 1
    p[1] = spare
    p[GEN] = one
    return
";
    let run = |a: F64, b: F64| -> bool {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("vals", vec![vec![F192::from(a), F192::from(b)]]);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let pi = [F192::from(a) + F192::from(b), F192::ONE];
            let (proof, _) = prove(&program, pi, lean_vm::pcs::TEST_LOG_INV_RATE);
            verify(&program, &pi, &proof).is_ok()
        }))
        .unwrap_or(false)
    };
    assert!(run(g_pow(3), g_pow(5)), "distinct hints must verify");
    assert!(
        !run(g_pow(4), g_pow(4)),
        "equal hints must be rejected even with a live `1` and a shareable product"
    );
}

/// The inverse is prover advice, so the guest-level idiom must reject a wrong
/// one. Written out by hand here, the way a guest would if it hinted its own
/// inverse: only `inv = (a+b)⁻¹` makes the product `1`.
#[test]
fn assert_ne_wrong_inverse_hint_rejected() {
    let src = "\
def main():
    v = StackBuf(3)
    hint_witness(v[0:3], \"vals\")
    d = v[0] + v[1]
    prod = d * v[2]
    assert prod == 1
    p = 1
    p[1] = v[0]
    p[GEN] = v[1]
    return
";
    let run = |a: F192, b: F192, inv: F192| -> bool {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("vals", vec![vec![a, b, inv]]);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (proof, _) = prove(&program, [a, b], lean_vm::pcs::TEST_LOG_INV_RATE);
            verify(&program, &[a, b], &proof).is_ok()
        }))
        .unwrap_or(false)
    };
    let (a, b) = (F192::from(g_pow(3)), F192::from(g_pow(5)));
    let d = a + b;
    assert!(run(a, b, d.inv()), "the true inverse verifies");
    assert!(!run(a, b, d.inv() + F192::ONE), "a wrong inverse must be rejected");
    assert!(!run(a, a, F192::ONE), "equal sides admit no inverse at all");
}
