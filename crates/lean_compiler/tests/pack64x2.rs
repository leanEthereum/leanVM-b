use lean_compiler::{compile, parse};
use lean_vm::blake3_flock::warm_setup;
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F128T};

#[test]
fn pack64x2_proves_and_verifies() {
    let src = "\
def main():
    a = 5
    b = 7
    packed = StackBuf(1)
    pack64x2_into(a, b, packed[0])
    p = 1
    p[1] = packed[0]
    p[GEN] = packed[0]
    return
";
    let program = compile(&parse(src).expect("parse"));
    warm_setup(1);
    let want = [F128T::new(5, 7), F128T::new(5, 7)];
    let (proof, stats) = prove(&program, want);
    assert_eq!(stats.counts[6], 1, "one PACK64X2 instruction");
    verify(&program, &want, &proof).expect("PACK64X2 program verifies");
}

#[test]
#[should_panic(expected = "PACK64X2 first input must be K-valued")]
fn pack64x2_rejects_extension_field_source() {
    let src = "\
def main():
    a = StackBuf(1)
    hint_witness(a[0:1], \"a\")
    packed = StackBuf(1)
    pack64x2_into(a[0], 7, packed[0])
    p = 1
    p[1] = packed[0]
    p[GEN] = packed[0]
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("a", vec![vec![F128T::new(5, 1)]]);
    let _ = program.execute([F128T::from(F64::ONE), F128T::from(F64::ONE)]);
}
