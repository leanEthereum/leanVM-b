//! Layer 1: perturbation. Each case is one program with one valid trial and a
//! table of single-cell pokes that must break it.
//!
//! Coverage is by *lowering*, not by feature list: every case exercises a
//! construct whose lowering could plausibly drop the check it stands for, and
//! every poke names one constraint. A poke that is accepted says which one is
//! missing.
//!
//! The pokes lean on witness streams rather than the public input, because two
//! public words is all there is and because the streams are where a real guest's
//! untrusted data actually enters.

use super::{Case, Trial, check_case, g, k, pi, wit};
use primitives::field::F192;

/// `XOR`/`MUL` relations, both assert forms, and the division back-solve. The
/// quotient cell is written by nothing but the back-solve, so this case also
/// pins the one legitimate way a cell may be read before any instruction writes
/// it.
#[test]
fn arithmetic_and_asserts() {
    check_case(&Case {
        name: "arithmetic_and_asserts",
        src: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    assert v[0] * v[1] == v[2]
    assert v[0] != v[1]
    q = v[2] / v[0]
    assert q == v[1]
    p = GEN ** 0
    p[1] = v[2]
    p[GEN] = v[0] + v[1]
    return
",
        valid: Trial::new([g(8), g(3) + g(5)]).stream("w", vec![vec![g(3), g(5), g(8)]]),
        pokes: vec![
            // Each of the three hinted cells breaks the product relation.
            wit("w", 0, g(4)),
            wit("w", 1, g(6)),
            wit("w", 2, g(9)),
            // Equal operands: the product relation would still need v[2] = g^10,
            // but this is the poke that `assert !=` exists for.
            wit("w", 0, g(5)),
            // Both published words.
            pi(0, g(9)),
            pi(1, g(3) + g(6)),
        ],
    });
}

/// The exponent range check and `match_range` dispatch. The dispatch is only
/// sound because the matched value was range-checked first (doc §Match
/// statements), so a poke past the bound must be caught by the check rather than
/// land at an attacker-chosen arm.
#[test]
fn range_check_and_dispatch() {
    check_case(&Case {
        name: "range_check_and_dispatch",
        src: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert log(v[0]) < 8
    r = match_range(log(v[0]), range(0, 8), lambda i: sq(i))
    assert r == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = r
    return


def sq(x):
    return x * x
",
        // Arm 3 runs: sq(3) = 3·3 in K = (x+1)^2 = x^2+1 = 5.
        valid: Trial::new([g(3), k(5)]).stream("w", vec![vec![g(3), k(5)]]),
        pokes: vec![
            // Past the bound: the range check's complement DEREF must catch it.
            wit("w", 0, g(8)),
            wit("w", 0, g(63)),
            // A different arm runs, so the claimed square is wrong.
            wit("w", 0, g(4)),
            // The claimed square itself.
            wit("w", 1, k(6)),
            pi(0, g(4)),
            pi(1, k(6)),
        ],
    });
}

/// `if`/`else` communicating through a write-once heap cell: only one arm runs,
/// so both may write it and the join reads it back. A lowering that lets the
/// join read anything other than the taken arm's value shows up as a poke that
/// selects the other arm and is still accepted.
#[test]
fn branch_join() {
    check_case(&Case {
        name: "branch_join",
        src: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert log(v[0]) < 4
    r = HeapBuf(1)
    if v[0] == GEN ** 2:
        r[1] = v[1] * GEN
    else:
        r[1] = v[1] * GEN ** 3
    p = GEN ** 0
    p[1] = r[1]
    p[GEN] = v[0]
    return
",
        valid: Trial::new([g(6), g(2)]).stream("w", vec![vec![g(2), g(5)]]),
        pokes: vec![
            // Takes the else arm, which multiplies by g^3 instead of g.
            wit("w", 0, g(1)),
            wit("w", 0, g(3)),
            // Past the bound.
            wit("w", 0, g(4)),
            // The value the taken arm shifts.
            wit("w", 1, g(4)),
            pi(0, g(7)),
            pi(1, g(3)),
        ],
    });
}

/// A `mul_range` loop with a runtime bound and heap-carried state. The bound is
/// hinted, so the loop terminates only because its log was checked first; the
/// pokes cover both a bound that changes the trip count and one past the check.
#[test]
fn loop_with_runtime_bound() {
    check_case(&Case {
        name: "loop_with_runtime_bound",
        src: "\
def main():
    v = StackBuf(1)
    hint_witness(v, \"n\")
    assert log(v[0]) < 8
    acc = HeapBuf(16)
    acc[1] = GEN ** 0
    for i in mul_range(1, v[0]):
        acc[i * GEN] = acc[i] * GEN ** 2
    p = GEN ** 0
    p[1] = acc[v[0]]
    p[GEN] = v[0]
    return
",
        // n = g^5: five iterations, acc[j] = g^{2j}, so acc[5] = g^10.
        valid: Trial::new([g(10), g(5)]).stream("n", vec![vec![g(5)]]),
        pokes: vec![
            // Fewer and more iterations: acc[n] is then g^8 and g^12.
            wit("n", 0, g(4)),
            wit("n", 0, g(6)),
            // Past the bound.
            wit("n", 0, g(8)),
            pi(0, g(11)),
            pi(1, g(4)),
        ],
    });
}

/// `pack64x2`'s range assertion: both sources must lie in K. Its untaken JUMP
/// puts them in the destination and frame slots, whose memory reads have
/// literal-zero upper limbs.
#[test]
fn pack64x2_range_assertion() {
    check_case(&Case {
        name: "pack64x2_range_assertion",
        src: "\
@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + f192(0, 1, 0) * b

def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    c = pack64x2(v[0], v[1])
    p = GEN ** 0
    p[1] = c
    p[GEN] = v[0]
    return
",
        valid: Trial::new([F192::new(5, 7, 0), k(5)]).stream("w", vec![vec![k(5), k(7)]]),
        pokes: vec![
            // Either source outside K.
            wit("w", 0, F192::new(5, 1, 0)),
            wit("w", 0, F192::new(5, 0, 1)),
            wit("w", 1, F192::new(7, 1, 0)),
            // In K, but not the packing that was published.
            wit("w", 0, k(6)),
            wit("w", 1, k(8)),
            pi(0, F192::new(5, 8, 0)),
            pi(1, k(6)),
        ],
    });
}

/// The digest-as-verification idiom: a hinted preimage, hashed, and the result
/// pinned against a hinted digest through a heap store. This is the shape a
/// signature verifier has, so it is the one that most needs a regression test.
///
/// The digest constant comes from [`print_blake2s_digest`], not from a hand
/// computation: what the case tests is that a *wrong* digest is rejected, and
/// for that the honest value only has to be honest.
#[test]
fn digest_pins_its_preimage() {
    check_case(&Case {
        name: "digest_pins_its_preimage",
        src: BLAKE2S_PIN_SRC,
        valid: Trial::new([k(5), k(7)])
            .stream("msg", vec![vec![k(5), k(7), F192::ZERO, F192::ZERO]])
            .stream("dig", vec![vec![DIGEST_5_7[0], DIGEST_5_7[1]]]),
        pokes: vec![
            // A different preimage hashes to something else.
            wit("msg", 0, k(6)),
            wit("msg", 1, k(8)),
            wit("msg", 2, k(1)),
            wit("msg", 3, k(1)),
            // A wrong digest is what the write-once store has to catch.
            wit("dig", 0, F192::ZERO),
            wit("dig", 1, F192::ZERO),
            wit("dig", 0, DIGEST_5_7[0] + F192::ONE),
            wit("dig", 1, DIGEST_5_7[1] + F192::ONE),
            // The published preimage words.
            pi(0, k(6)),
            pi(1, k(8)),
        ],
    });
}

const BLAKE2S_PIN_SRC: &str = "\
def main():
    m = StackBuf(4)
    hint_witness(m, \"msg\")
    d = StackBuf(2)
    blake2s(m[0:2], m[2:4], d)
    e = HeapBuf(2)
    hint_witness(e[0:2], \"dig\")
    e[1] = d[0]
    e[GEN] = d[1]
    p = GEN ** 0
    p[1] = m[0]
    p[GEN] = m[1]
    return
";

/// BLAKE2s of the 64-byte block whose four canonical cells are `(5, 7, 0, 0)`.
pub const DIGEST_5_7: [F192; 2] = [
    F192::new(0xbbc8_c175_8cb7_7642, 0xf299_5d40_1fad_f4ff, 0),
    F192::new(0x83ea_6ade_289a_53c8, 0x57e6_e523_12ec_734b, 0),
];

/// Regenerate [`DIGEST_5_7`]: `cargo test --release -p lean_compiler
/// print_blake2s_digest -- --ignored --nocapture`. Kept so the constant above is
/// reproducible rather than folklore.
#[test]
#[ignore = "prints a constant; not a check"]
fn print_blake2s_digest() {
    let src = "\
def main():
    m = StackBuf(4)
    hint_witness(m, \"msg\")
    d = StackBuf(2)
    blake2s(m[0:2], m[2:4], d)
    print(d[0])
    print(d[1])
    return
";
    let mut p = super::build(src);
    p.set_witness("msg", vec![vec![k(5), k(7), F192::ZERO, F192::ZERO]]);
    p.execute([F192::ZERO, F192::ZERO]);
}

/// The fused `match_range` path must reject a call that binds more names than
/// the callee returns, exactly as the non-fused path does. Before this check the
/// surplus name `DEREF`ed a callee-frame offset nothing on the taken path wrote,
/// and since the shared frame is sized to the largest callee that offset exists,
/// so the name bound a prover-chosen word.
///
/// Fusion needs every arm to be a call to the same function with identical
/// runtime arguments, so the two programs below are the fused shape: one over
/// mixed-arity callees, one over a single over-bound callee.
#[test]
#[should_panic(expected = "dispatched call binds")]
fn dispatched_call_rejects_a_mixed_arity_arm() {
    super::build(
        "\
def main():
    x = GEN ** 2
    a, b, c = match_range(log(x), range(0, 2), lambda i: three(x, i), range(2, 4), lambda i: one(x, i))
    p = GEN ** 0
    p[1] = b
    p[GEN] = c
    return


def three(v, k: Const):
    q = v * GEN ** k
    return q, q * q, q * q * q


def one(v, k: Const):
    return v * GEN ** k
",
    );
}

#[test]
#[should_panic(expected = "dispatched call binds")]
fn dispatched_call_rejects_an_over_bound_callee() {
    super::build(
        "\
def main():
    x = GEN ** 1
    a, b = match_range(log(x), range(0, 4), lambda i: one(x, i))
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return


def one(v, k: Const):
    return v * GEN ** k
",
    );
}

/// A local whose name collides with a top-level constant array must be rejected.
/// `zkDSL.md` §Global constants reserves the name; a scalar constant enforces that
/// by construction (the parser substitutes its value, so the shadowing binding
/// becomes a literal and fails loudly), but a constant array was carried to
/// lowering, where `const_array_elem` resolved `NAME[i]` against it without
/// consulting the scope and `expr` folded it before the local could be seen.
///
/// The consequence was the catastrophic direction for a hint: the range check
/// below ran against the baked constant `g^3` and passed, while the actual witness
/// `g^40` was never bounded and never read.
#[test]
#[should_panic(expected = "reserved")]
fn a_local_may_not_shadow_a_constant_array() {
    super::build(
        "\
Q = [8, 32]


def main():
    Q = StackBuf(2)
    hint_witness(Q, \"w\")
    assert log(Q[0]) < 8
    p = GEN ** 0
    p[1] = Q[0]
    p[GEN] = Q[1]
    return
",
    );
}

/// Same rule for a parameter, which is the other half of what the doc reserves.
#[test]
#[should_panic(expected = "reserved")]
fn a_parameter_may_not_shadow_a_constant_array() {
    super::build(
        "\
Q = [8, 32]


def main():
    r = pick(GEN ** 2)
    p = GEN ** 0
    p[1] = r
    p[GEN] = r
    return


def pick(Q):
    return Q * GEN
",
    );
}
