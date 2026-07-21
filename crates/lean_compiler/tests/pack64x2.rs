use lean_compiler::{compile, parse};
use lean_vm::blake3_flock::warm_setup;
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192};

#[test]
fn pack64x2_proves_and_verifies() {
    let src = "\
def main():
    a = 5
    b = 7
    packed = pack64x2(a, b)
    p = 1
    p[1] = packed
    p[GEN] = packed
    return
";
    let program = compile(&parse(src).expect("parse"));
    warm_setup(1);
    let want = [F192::new(5, 7, 0), F192::new(5, 7, 0)];
    let (proof, stats) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(
        stats.counts[lean_vm::tables::PACK64X2_TABLE],
        1,
        "one PACK64X2 instruction"
    );
    verify(&program, &want, &proof).expect("PACK64X2 program verifies");
}

#[test]
#[should_panic(expected = "PACK64X2 first input must be K-valued")]
fn pack64x2_rejects_extension_field_source() {
    let src = "\
def main():
    a = StackBuf(1)
    hint_witness(a[0:1], \"a\")
    packed = pack64x2(a[0], 7)
    p = 1
    p[1] = packed
    p[GEN] = packed
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("a", vec![vec![F192::new(5, 1, 0)]]);
    let _ = program.execute([F192::from(F64::ONE), F192::from(F64::ONE)]);
}
