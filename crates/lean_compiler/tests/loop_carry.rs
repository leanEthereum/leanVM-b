//! `carry (a, b, ...)` — loop-carried bindings on runtime loops: body
//! rebinding of a carried name becomes the next iteration's value; after the
//! loop the names hold the finals. The compiler threads them as loop-helper
//! arguments (no hand-rolled write-once chains).

use lean_compiler::{compile, parse};
use lean_vm::blake3_flock::warm_setup;
use lean_vm::cpu::{prove, verify};
use primitives::field::F128;
use primitives::field::g_pow;

#[test]
fn loop_carry_threads_state() {
    let src = "\
def main():
    n = GEN ** 6
    acc = 1
    last = 7
    for xk in mul_range(1, n):
        acc = acc * (xk + last)
        last = last + acc
    p = 1
    p[1] = acc
    p[GEN] = last
    return
";
    let program = compile(&parse(src).expect("parse"));
    warm_setup(1);
    // reference computation
    let (mut acc, mut last) = (F128::ONE, F128::new(7, 0));
    for k in 0..6 {
        acc *= g_pow(k) + last;
        last += acc;
    }
    let want = [acc, last];
    let (proof, _) = prove(&program, want);
    verify(&program, &want, &proof).expect("carried loop computes the reference");

    let mut bad = want;
    bad[1] += F128::ONE;
    assert!(verify(&program, &bad, &proof).is_err());
}
