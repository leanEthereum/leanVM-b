use lean_compiler::{compile, compile_without_filler, parse};
use lean_vm::blake3_flock::warm_setup;
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192};

/// The program's own instruction mix: a build without the fill blocks, executed but not
/// proven. Proving needs them, since a table's height has to be a power of two with no
/// padding rows, but their dummy rows would drown out exactly what these counts are
/// measuring.
fn mix(src: &str, pi: [F192; 2]) -> [usize; lean_vm::cpu::Stats::TABLES.len()] {
    compile_without_filler(&parse(src).expect("parse"))
        .execute(pi)
        .base_counts
}

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
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    assert_eq!(mix(src, want)[6], 1, "one PACK64X2 instruction");
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
