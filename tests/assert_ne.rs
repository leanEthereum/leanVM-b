//! `assert a != b` — a proof-enforced inequality. It lowers to one `XOR` and a
//! conditional `JUMP` on `a + b`: when the sides differ the jump is taken and
//! execution continues; when they are equal it falls through to a jump to the
//! poison pc `g^-1`, which lies outside the committed bytecode cube, so the
//! bytecode bus cannot balance a read there and no valid proof continues. No
//! prover hint (unlike the `(a-b)·inv == 1` idiom it replaces).

use leanvm_b::compiler::{compile, parse};
use leanvm_b::cpu::{prove, verify};
use leanvm_b::field::{F128, g_pow};

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
    let want = [g_pow(12), g_pow(5)];
    let (proof, _) = prove(&program, want);
    verify(&program, &want, &proof).expect("inequality program verifies");

    let bad = [g_pow(11), g_pow(5)];
    assert!(verify(&program, &bad, &proof).is_err(), "wrong public input must be rejected");
}

/// The adversarial case: two hinted cells the prover sets *equal*, asserted
/// unequal. Honest witness (distinct) verifies; the equal witness drives the
/// trace into the poison pc, which no valid proof can carry past.
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
    let run = |a: F128, b: F128| -> bool {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("vals", vec![vec![a, b]]);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (proof, _) = prove(&program, [a, b]);
            verify(&program, &[a, b], &proof).is_ok()
        }))
        .unwrap_or(false)
    };
    assert!(run(g_pow(3), g_pow(5)), "distinct hints must verify");
    assert!(!run(g_pow(3), g_pow(3)), "equal hints must be rejected by `assert !=`");
}

/// `assert a != b` inside a `mul_range` body: the poison path is emitted once
/// per compiled body and shared across iterations; every iteration's counter
/// differs from the fixed value, so the honest loop verifies.
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
    let want = [F128::new(5, 0), F128::new(7, 0)];
    let (proof, _) = prove(&program, want);
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
