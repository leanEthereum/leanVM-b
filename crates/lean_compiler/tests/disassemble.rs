use lean_compiler::{compile, disassemble, parse};

#[test]
fn disassemble_simple_program() {
    let src = "\
def main():
    buff = HeapBuf(6)
    buff[1] = 1
    buff[GEN] = GEN
    for i in mul_range(1, GEN ** 4):
        buff[i * GEN ** 2] = buff[i] * buff[i * GEN]
    p = 1
    p[1] = buff[GEN ** 4]
    return
";

    let program = compile(&parse(src).expect("parse"));

    println!("\n=== zkDSL source ===\n{src}");
    println!(
        "=== compiled ISA ({} instructions, pc0 = {}, fp0 = {}) ===",
        program.prog.len(),
        program.pc0,
        program.fp0,
    );
    print!("{}", disassemble(&program.prog));

    assert!(!program.prog.is_empty(), "compilation produced bytecode");
}
