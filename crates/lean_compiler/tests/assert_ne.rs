//! `assert a != b` — a proof-enforced inequality. It lowers to one `XOR` and a
//! conditional `JUMP` on `a + b`: when the sides differ the jump is taken and
//! execution continues; when they are equal it falls through to a jump to the
//! poison pc `g^-1`, which lies outside the committed bytecode cube, so the
//! bytecode bus cannot balance a read there and no valid proof continues. No
//! prover hint (unlike the `(a-b)·inv == 1` idiom it replaces).

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
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
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("inequality program verifies");

    let bad = [F192::from(g_pow(11)), F192::from(g_pow(5))];
    assert!(
        verify(&program, &bad, &proof).is_err(),
        "wrong public input must be rejected"
    );
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
    let run = |a: F64, b: F64| -> bool {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("vals", vec![vec![F192::from(a), F192::from(b)]]);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let pi = [F192::from(a), F192::from(b)];
            let (proof, _) = prove(&program, pi, lean_vm::pcs::LOG_INV_RATE);
            verify(&program, &pi, &proof).is_ok()
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
    let want = [F192::from(F64(5)), F192::from(F64(7))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
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
