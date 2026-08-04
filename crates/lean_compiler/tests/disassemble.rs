//! `disassemble` must render every one of the nine opcodes without panicking,
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
    h = StackBuf(4)
    h[0] = 5
    h[1] = 7
    h[2] = 11
    h[3] = 13
    d = StackBuf(4)
    blake3(h, h, d)
    x = StackBuf(3)
    x[0] = 5
    x[1] = 7
    x[2] = 11
    y = StackBuf(3)
    y[0] = 2
    y[1] = 3
    y[2] = 6
    s = StackBuf(3)
    xor_192(x, y, s)
    q = StackBuf(3)
    mul_192(x, y, q)
    r = StackBuf(3)
    mul_192_base(h[0], y, r)
    ext = HeapBuf(3)
    deref_192(ext, q)
    p = 1
    p[1] = buff[GEN ** 4] + s[0]
    p[GEN] = d[0] + q[0] + r[0]
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

    for mnemonic in [
        "SET",
        "XOR",
        "MUL",
        "XOR_192",
        "MUL_192",
        "MUL_192_BASE",
        "DEREF",
        "DEREF_192",
        "JUMP",
        "BLAKE3",
    ] {
        assert!(text.contains(mnemonic), "disassembly is missing {mnemonic}");
    }
}
