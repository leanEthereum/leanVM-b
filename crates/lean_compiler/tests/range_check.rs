//! Range checks *in the exponent* — `assert log x < log GEN ** k` (or
//! `assert log x < k`) proves `log_g(x) < k`, i.e. `x ∈ {g^0, g^1, …, g^{k-1}}`,
//! in 3 cycles: `DEREF x` bounds `log(x)` by the memory size, a `MUL` into the
//! write-once constant cell `g^{k-1}` back-solves and binds the complement
//! `y = g^{k-1-log(x)}`, and `DEREF y` bounds the complement. leanVM's DEREF
//! range-check trick, transported to g-powers; the only nondeterminism is the
//! end-of-run resolution of the two touched cells.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

/// Both bound forms (`log GEN ** k` and a plain integer exponent) with the
/// boundary elements (`g^{k-1}`, `1 = g^0`), end-to-end: prove + verify, and a
/// wrong public input is rejected. Also pins the gadget's cost: 2 DEREFs per
/// check.
#[test]
fn range_check_end_to_end() {
    let src = "\
def main():
    x = GEN ** 5
    assert log x < log GEN ** 8
    y = GEN ** 7
    assert log y < 8
    assert log 1 < log GEN ** 8
    z = x * y
    assert log z < 13
    p = 1
    p[1] = z
    p[GEN] = x
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(12)), F192::from(g_pow(5))];
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    // 2 DEREFs per range check (4 checks) + 2 publishing stores.
    assert_eq!(stats.counts[3], 10, "DEREF count");
    verify(&program, &want, &proof).expect("range-checked program verifies");

    let bad = [F192::from(g_pow(12)), F192::from(g_pow(6))];
    assert!(
        verify(&program, &bad, &proof).is_err(),
        "wrong public input must be rejected"
    );
}

/// A check whose two touched cells (`m[300]` and the complement's `m[99]`) are
/// never written by the program: the deferred end-of-run fill fixes them (and
/// the DEREF rows) to ZERO, and the bus still balances.
#[test]
fn range_check_unwritten_cells() {
    let src = "\
def main():
    x = GEN ** 300
    assert log x < 400
    p = 1
    p[1] = x
    p[GEN] = x
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(g_pow(300)), F192::from(g_pow(300))];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("deferred-fill program verifies");
}

/// Range checks inside a `mul_range` body: the check runs once per iteration in
/// a fresh helper frame (its own `g^{k-1}` constant cell each time), and the
/// touched low cells mix already-written ones (`m[0]`, `m[1]`: the public
/// input) with deferred ones.
#[test]
fn range_check_in_loop() {
    let src = "\
def main():
    for i in mul_range(1, GEN ** 6):
        assert log i < log GEN ** 6
    p = 1
    p[1] = 5
    p[GEN] = 7
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::from(F64(5)), F192::from(F64(7))];
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    // 6 iterations × 2 range-check DEREFs, plus call/publish plumbing.
    assert!(stats.counts[3] >= 12, "at least the 12 range-check DEREFs");
    verify(&program, &want, &proof).expect("loop range checks verify");
}

/// `log(g^8) < 8` is false: the complement back-solves to a huge-exponent
/// element, and its DEREF fails witness generation — the honest-execution
/// surface of a failing range check.
#[test]
#[should_panic(expected = "failed range check")]
fn range_check_at_bound_rejected() {
    let src = "def main():\n    x = GEN ** 8\n    assert log x < 8\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    program.execute([F192::ZERO, F192::ZERO]);
}

/// A value that is no small g-power at all (5 = x^2 + 1) fails at the first
/// DEREF, the same way.
#[test]
#[should_panic(expected = "failed range check")]
fn range_check_non_g_power_rejected() {
    let src = "def main():\n    x = 5\n    assert log x < 8\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    program.execute([F192::ZERO, F192::ZERO]);
}

/// Bound 0 names the empty set — rejected at compile time.
#[test]
#[should_panic(expected = "names the empty set")]
fn range_check_empty_bound_rejected() {
    let src = "def main():\n    x = 1\n    assert log x < 0\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// Bounds beyond `2^16` (the minimum memory size) would not be sound for every
/// prover memory choice — rejected at compile time.
#[test]
#[should_panic(expected = "exceeds 2^16")]
fn range_check_bound_too_big_rejected() {
    let src = "def main():\n    x = 1\n    assert log x < 65537\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A `<` assert without `log` is rejected: field elements have no order, only
/// their logs do.
#[test]
#[should_panic(expected = "compares logs")]
fn range_check_without_log_rejected() {
    let src = "def main():\n    x = 1\n    assert x < 8\n    return\n";
    let _ = parse(src).map_err(|e| panic!("{e}"));
}
