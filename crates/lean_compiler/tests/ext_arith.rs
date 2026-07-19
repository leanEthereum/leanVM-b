use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
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
