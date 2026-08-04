//! `disassemble` must render every one of the seven opcodes without panicking,
//! so it stays usable for the `DBG_DISASM` workflow (a failed guest `assert`
//! surfaces as a write-once conflict, and the pc is all you get).

use lean_compiler::{compile, disassemble, parse};
use primitives::pretty_integer;

#[test]
fn disassemble_covers_every_opcode() {
    let src = "\
def main():
    buff = HeapBuf(6)
    buff[1] = 1
    buff[GEN] = GEN
    for i in mul_range(1, GEN ** 4):
        buff[i * GEN ** 2] = buff[i] * buff[i * GEN]
    h = StackBuf(2)
    h[0] = 5
    h[1] = 7
    d = StackBuf(2)
    blake3(h, h, d)
    packed = pack64x2(5, 7)
    p = 1
    p[1] = buff[GEN ** 4] + packed
    p[GEN] = d[0]
    return
";

    let program = compile(&parse(src).expect("parse"));

    println!("\n=== zkDSL source ===\n{src}");
    println!(
        "=== compiled ISA ({} instructions, pc0 = {}, fp0 = {}) ===",
        pretty_integer(program.prog.len()),
        pretty_integer(program.pc0),
        pretty_integer(program.fp0),
    );
    let text = disassemble(&program.prog);
    print!("{text}");

    for mnemonic in ["SET", "XOR", "MUL", "DEREF", "JUMP", "BLAKE3", "PACK64X2"] {
        assert!(text.contains(mnemonic), "disassembly is missing {mnemonic}");
    }
}
