//! Layer 2: equivalence. Two spellings the language documents as interchangeable
//! must accept exactly the same trials.
//!
//! This is the layer that finds dropped constraints without anyone having to
//! guess where they went. A dropped store is invisible on its own: the program
//! still runs, and its one honest witness still passes. It becomes visible the
//! moment you have a second spelling of the same intent that *kept* the store,
//! because then one side rejects a witness the other accepts, and the more
//! permissive side is the buggy one.
//!
//! Every pair here is a promise `zkDSL.md` makes. When one fails, quote the
//! promise in the bug report; the `why` field is there to be quoted.

use super::{Pair, Trial, check_pair, g, k};
use primitives::field::F192;

/// One hinted pair of cells, published so the trial's public input pins them.
fn two(a: F192, b: F192) -> Trial {
    Trial::new([a, b]).stream("w", vec![vec![a, b]])
}

/// `@inline` is documented as a pure call-site expansion: "the body is inlined at
/// each call site" with the same semantics as the call. So a function's
/// observable behaviour cannot depend on whether it carries the decorator.
#[test]
fn inline_and_plain_calls_agree() {
    let body = "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert shift(v[0]) == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return


@INLINE
def shift(x):
    return x * GEN
";
    check_pair(&Pair {
        name: "inline_and_plain_calls_agree",
        why: "zkDSL.md §`@inline`: inlining is a call-site expansion, not a change of meaning.",
        a: &body.replace("@INLINE\n", "@inline\n"),
        b: &body.replace("@INLINE\n", ""),
        trials: vec![
            two(g(3), g(4)), // shift(g^3) = g^4
            two(g(3), g(5)), // rejected by both
            two(g(0), g(1)),
            two(g(7), g(7)),
        ],
    });
}

/// Write-once memory is the assertion mechanism, so `assert a == b` and two
/// stores of `a` and `b` into one heap cell are the same statement. `zkDSL.md`
/// §Memory: "a second write of the same value is a no-op, of a different value a
/// proof failure. This turns stores into equality assertions".
#[test]
fn assert_eq_and_double_heap_store_agree() {
    check_pair(&Pair {
        name: "assert_eq_and_double_heap_store_agree",
        why: "zkDSL.md §Memory: a store into an already-written cell IS an equality assertion.",
        a: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert v[0] == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        b: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    h = HeapBuf(1)
    h[1] = v[0]
    h[1] = v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[1]
    return
",
        trials: vec![
            two(g(3), g(3)),
            two(g(3), g(4)),
            two(F192::ZERO, F192::ZERO),
            two(F192::ZERO, k(1)),
        ],
    });
}

/// `zkDSL.md` §field: "`/` is runtime field division … the compiler leaves the
/// quotient cell unset and emits the checked relation `quotient · b == a`". So
/// dividing and then comparing must equal comparing the product, wherever the
/// divisor is nonzero (division by zero is documented undefined, so no trial
/// takes it there).
#[test]
fn division_and_checked_product_agree() {
    check_pair(&Pair {
        name: "division_and_checked_product_agree",
        why: "zkDSL.md §field: `a / b` emits exactly the relation `quotient · b == a`.",
        a: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    q = v[1] / v[0]
    assert q == v[2]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[2]
    return
",
        b: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    assert v[2] * v[0] == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = v[2]
    return
",
        trials: vec![
            three(g(3), g(8), g(5)), // g^8 / g^3 = g^5
            three(g(3), g(8), g(6)), // rejected by both
            three(k(1), g(9), g(9)),
            three(g(2), g(2), g(0)),
        ],
    });
}

fn three(a: F192, b: F192, c: F192) -> Trial {
    Trial::new([a, c]).stream("w", vec![vec![a, b, c]])
}

/// `unroll` is documented as compile-time unrolling, so a loop and its expansion
/// are the same program. A structural pair: it pins the loop machinery itself
/// rather than any one assertion, which is what catches a lowering that
/// mis-addresses one iteration.
#[test]
fn unroll_and_expansion_agree() {
    check_pair(&Pair {
        name: "unroll_and_expansion_agree",
        why: "zkDSL.md §unroll: the loop is expanded at compile time, so it IS the expansion.",
        a: "\
def main():
    v = StackBuf(1)
    hint_witness(v, \"w\")
    a = HeapBuf(4)
    a[1] = v[0]
    for i in unroll(0, 3):
        a[GEN ** (i + 1)] = a[GEN ** i] * GEN
    p = GEN ** 0
    p[1] = a[GEN ** 3]
    p[GEN] = v[0]
    return
",
        b: "\
def main():
    v = StackBuf(1)
    hint_witness(v, \"w\")
    a = HeapBuf(4)
    a[1] = v[0]
    a[GEN] = a[1] * GEN
    a[GEN ** 2] = a[GEN] * GEN
    a[GEN ** 3] = a[GEN ** 2] * GEN
    p = GEN ** 0
    p[1] = a[GEN ** 3]
    p[GEN] = v[0]
    return
",
        trials: vec![
            one(g(3), g(0)), // a[3] = g^0·g^3
            one(g(4), g(0)), // rejected by both
            one(g(8), g(5)),
            one(g(5), g(5)),
        ],
    });
}

/// A published pair whose first word is the claim and whose second is the hint.
fn one(published: F192, hint: F192) -> Trial {
    Trial::new([published, hint]).stream("w", vec![vec![hint]])
}
