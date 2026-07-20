use lean_compiler::{compile, parse};
use lean_vm::cpu::{Op, prove, verify};
use primitives::field::{F64, F192};

fn words(v: F192) -> [F64; 3] {
    [F64(v.c0), F64(v.c1), F64(v.c2)]
}

#[test]
fn extension_arithmetic_proves_and_verifies() {
    let src = r#"
def main():
    a = [5, 7, 11]
    b = [13, 17, 19]
    s = StackBuf(3)
    p = StackBuf(3)
    q = StackBuf(3)
    add_ext(a, b, s)
    mul_ext(a, b, p)
    div_ext(p, b, q)
    assert q[0] == a[0]
    assert q[1] == a[1]
    assert q[2] == a[2]
    out = GEN ** 0
    out[1] = s[0]
    out[GEN] = s[1]
    out[GEN ** 2] = s[2]
    out[GEN ** 3] = p[0]
    return
"#;
    let program = compile(&parse(src).expect("parse"));
    let a = F192::new(5, 7, 11);
    let b = F192::new(13, 17, 19);
    let s = words(a + b);
    let p = words(a * b);
    let want = [s[0], s[1], s[2], p[0]];
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[2], 1);
    assert_eq!(stats.counts[3], 2);
    verify(&program, &want, &proof).expect("extension arithmetic verifies");
}

#[test]
#[should_panic(expected = "must be StackBuf(3)")]
fn extension_operand_width_is_checked() {
    let src = "def main():\n    a = StackBuf(2)\n    b = StackBuf(3)\n    c = StackBuf(3)\n    add_ext(a, b, c)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

#[test]
fn inline_stackbuf_alias_crosses_ext_call_abi() {
    let src = r#"
def main():
    value = make_ext(5)
    check_ext(value)
    return

@inline
def make_ext(x):
    value = [x, x + 3, x + 6]
    return value

def check_ext(value: Ext):
    assert value[0] == 5
    assert value[1] == 6
    assert value[2] == 3
    return
"#;
    let program = compile(&parse(src).expect("parse"));
    program.execute([F64::ZERO; 4]);
}

#[test]
fn real_call_bundles_contiguous_extension_argument() {
    let src = r#"
def main():
    a = [5, 7, 11]
    b = [13, 17, 19]
    value = StackBuf(3)
    add_ext(a, b, value)
    check_ext(value)
    return

def check_ext(value: Ext):
    assert value[0] == 8
    assert value[1] == 22
    assert value[2] == 24
    return
"#;
    let program = compile(&parse(src).expect("parse"));
    program.execute([F64::ZERO; 4]);
    assert_eq!(
        program
            .prog
            .iter()
            .filter(|op| matches!(op, Op::DerefExt { .. }))
            .count(),
        1,
        "the contiguous three-word argument crosses the real-call boundary in one row"
    );
}

#[test]
fn real_call_bundles_contiguous_argument_and_return_triples() {
    let src = r#"
def main():
    public = GEN ** 0
    state = StackBuf(4)
    state[0] = public[1]
    state[1] = public[GEN]
    state[2] = public[GEN ** 2]
    state[3] = public[GEN ** 3]
    a, b, c, d = roundtrip(state[0], state[1], state[2], state[3])
    assert a == 5
    assert b == 7
    assert c == 11
    assert d == 13
    return

def roundtrip(a, b, c, d):
    return a, b, c, d
"#;
    let program = compile(&parse(src).expect("parse"));
    program.execute([F64(5), F64(7), F64(11), F64(13)]);
    assert_eq!(
        program
            .prog
            .iter()
            .filter(|op| matches!(op, Op::DerefExt { .. }))
            .count(),
        2,
        "one bundled argument prefix and one bundled return prefix"
    );
}

#[test]
fn callee_bundles_multiple_contiguous_return_runs() {
    let src = r#"
def main():
    a, b = make()
    assert a[0] == 8
    assert a[1] == 22
    assert a[2] == 24
    assert b[0] == 13
    assert b[1] == 17
    assert b[2] == 19
    return

def make():
    x = [5, 7, 11]
    y = [13, 17, 19]
    a = StackBuf(3)
    add_ext(x, y, a)
    b = StackBuf(3)
    add_ext(x, a, b)
    return a, b
"#;
    let program = compile(&parse(src).expect("parse"));
    program.execute([F64::ZERO; 4]);
    assert_eq!(
        program
            .prog
            .iter()
            .filter(|op| matches!(op, Op::DerefExt { .. }))
            .count(),
        4,
        "two packed writes into the callee return area and two packed caller loads"
    );
}

#[test]
fn contiguous_extension_alias_is_forwarded_without_copies() {
    let src = r#"
def main():
    a = [5, 7, 11]
    b = [13, 17, 19]
    first = StackBuf(3)
    add_ext(a, b, first)
    alias = [first[0], first[1], first[2]]
    second = StackBuf(3)
    add_ext(alias, first, second)
    return
"#;
    let program = compile(&parse(src).expect("parse"));
    program.execute([F64::ZERO; 4]);

    // Both literal inputs are pooled constant extension runs, and the alias of
    // `first` already names a contiguous run. None needs a MUL-by-one copy.
    assert_eq!(program.prog.iter().filter(|op| matches!(op, Op::Mul { .. })).count(), 0);
    assert_eq!(
        program.prog.iter().filter(|op| matches!(op, Op::AddExt { .. })).count(),
        2
    );
}

#[test]
fn extension_deref_stores_loads_and_proves() {
    let src = r#"
def main():
    ptr = HeapBuf(3)
    value = [5, 7, 11]
    deref_ext(ptr, value)
    loaded = StackBuf(3)
    deref_ext(ptr, loaded)
    assert loaded[0] == 5
    assert loaded[1] == 7
    assert loaded[2] == 11
    return
"#;
    let program = compile(&parse(src).expect("parse"));
    let (proof, stats) = prove(&program, [F64::ZERO; 4], lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[6], 2);
    verify(&program, &[F64::ZERO; 4], &proof).expect("extension dereference verifies");
}

#[test]
fn deferred_extension_dereferences_propagate_through_a_chain() {
    let src = r#"
def main():
    first = HeapBuf(3)
    second = HeapBuf(3)
    linked = StackBuf(3)
    deref_ext(first, linked)
    deref_ext(second, linked)
    value = [5, 7, 11]
    deref_ext(second, value)
    return
"#;
    let program = compile(&parse(src).expect("parse"));
    let (proof, stats) = prove(&program, [F64::ZERO; 4], lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(stats.counts[6], 3);
    verify(&program, &[F64::ZERO; 4], &proof).expect("deferred extension chain verifies");
}
