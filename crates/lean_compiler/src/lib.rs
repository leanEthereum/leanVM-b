//! A compiler from a Python-like zkDSL (see `zkDSL.md`) to the ISA (`cpu::Op`).
//! Produces a [`cpu::Program`] — bytecode plus the prover's allocation hints.
//!
//! ## Calling convention
//!
//! A frame is fp-relative; operand `gᵏ` names cell `m[fp·gᵏ]`. Layout:
//!
//! | offset | contents |
//! |--------|----------|
//! | 0      | `retpc` — return program counter |
//! | 1      | `retfp` — caller frame pointer |
//! | 2 .. 2+nargs            | arguments |
//! | 2+nargs .. 2+nargs+nret | return values |
//! | rest                    | locals / temporaries / frame-pointer hints |
//!
//! A **call** is `DEREF`-then-`JUMP`: the callee frame pointer is a fresh
//! prover-hinted cell; the args and `retfp` are stored with `DEREF`(`Cell`/`Fp`),
//! then `DEREF`(`Pc`) stores the return address `g²·pc` (the resume point after the
//! call `JUMP`). The callee returns with one `JUMP[one, 0, 1]`. A **`mul_range`
//! loop** lowers to a recursive helper that tests `i == g^hi` and, while not done,
//! runs the body and recurses on `i·g`.

use std::collections::HashMap;

use lean_vm::cpu::hints::RHint;
use lean_vm::cpu::{Blake3Packing, DerefMode, Op, Program};
use primitives::{
    field::{F64, F192, g_pow},
    pretty_integer,
};

mod ast;
mod ir;
mod lower;
mod parser;
pub use ast::*;
pub(crate) use ir::*;
use lower::lower_func;
pub(crate) use parser::subst_stmts;
pub use parser::{parse, parse_const, parse_file_with_replacements, parse_with_replacements};

// ----------------------------------------------------------------------------
// Layout, resolution, witness generation
// ----------------------------------------------------------------------------

/// Compile an [`Ast`] to a provable [`Program`]. Panics on a malformed program
/// (unbound variable, missing `main`, address overflow).
pub fn compile(ast: &Ast) -> Program {
    // Lower main first (entry pc 0), then the rest, expanding loop helpers.
    let mut queue: Vec<Func> = Vec::new();
    let main = ast
        .funcs
        .iter()
        .find(|f| f.name == "main")
        .expect("program needs a `main`");
    assert!(!main.const_params.contains(&true), "main cannot take Const parameters");
    assert!(!main.inline, "main cannot be `@inline`");
    queue.push(main.clone());
    for f in &ast.funcs {
        if f.name != "main" {
            queue.push(f.clone());
        }
    }
    // Definitions by name, for Const-parameter specialization at call sites.
    let defs: HashMap<String, Func> = ast.funcs.iter().map(|f| (f.name.clone(), f.clone())).collect();
    // Constant arrays by name, resolved at lowering (`NAME[i]`, `len(NAME)`).
    let const_arrays: HashMap<String, Vec<F192>> = ast.const_arrays.iter().cloned().collect();
    let dbg_lower = std::env::var("DBG_LOWER").is_ok();

    let mut loop_ctr = 0usize;
    let mut lowered: Vec<Lowered> = Vec::new();
    let mut i = 0;
    while i < queue.len() {
        let f = queue[i].clone();
        i += 1;
        // A function with Const parameters is a template (only its call-site
        // specializations are lowered); an `@inline` function is expanded at
        // each call site ([`FnLower::try_inline`]), never lowered standalone.
        if f.const_params.contains(&true) || f.inline {
            continue;
        }
        let low = lower_func(&f, &mut queue, &mut loop_ctr, &defs, &const_arrays);
        if dbg_lower {
            eprintln!("== fn {} (frame {}) ==", low.name, pretty_integer(low.frame_size));
            for (i, ins) in low.code.iter().enumerate() {
                let index = pretty_integer(i);
                eprintln!("  {index:>5}: {:?}", ins.op);
            }
        }
        lowered.push(low);
    }

    // Assign entry program counters and frame sizes.
    let mut entry = HashMap::new();
    let mut frame_size = HashMap::new();
    let mut pc = 0u32;
    for l in &lowered {
        entry.insert(l.name.clone(), pc);
        frame_size.insert(l.name.clone(), l.frame_size);
        pc += l.code.len() as u32;
    }
    // The padded bytecode size `B` is fixed by the lowered length, so the halt
    // sentinel pc `g^{B-1}` (last slot) is known before resolving: `main`'s
    // `EndSentinel` jump dest resolves to it, and the program halts there.
    let total: usize = lowered.iter().map(|l| l.code.len()).sum();
    // The sentinel needs a slot of its own PAST all real code: pad from
    // total + 1, so a program of exactly 2^k instructions doesn't collide
    // its last instruction with the halt pc.
    let bytecode_size = (total + 1).next_power_of_two();
    let sentinel = (bytecode_size - 1) as u32;

    // Resolve to bytecode + a hint map keyed by global pc.
    let mut prog: Vec<Op> = Vec::new();
    let mut hints: HashMap<u32, Vec<RHint>> = HashMap::new();
    for l in &lowered {
        let base = entry[&l.name];
        for ins in &l.code {
            let here = prog.len() as u32;
            if !ins.hints.is_empty() {
                let rhs = ins
                    .hints
                    .iter()
                    .map(|h| match h {
                        Hint::AllocFrame { ptr, callee } => RHint::Alloc {
                            ptr: *ptr,
                            size: frame_size[callee],
                        },
                        Hint::AllocFrameMax { ptr, callees } => RHint::Alloc {
                            ptr: *ptr,
                            size: callees.iter().map(|c| frame_size[c]).max().unwrap(),
                        },
                        Hint::AllocBuffer { ptr, size } => RHint::Alloc { ptr: *ptr, size: *size },
                        Hint::AllocBufferDyn { ptr, size } => RHint::AllocDyn { ptr: *ptr, size: *size },
                        Hint::WitnessStack { name, base, len } => RHint::WitnessStack {
                            name: name.clone(),
                            base: *base,
                            len: *len,
                        },
                        Hint::WitnessHeap { name, ptr, lo, len } => RHint::WitnessHeap {
                            name: name.clone(),
                            ptr: *ptr,
                            lo: *lo,
                            len: *len,
                        },
                        Hint::Print { label, cell } => RHint::Print {
                            label: label.clone(),
                            cell: *cell,
                        },
                        Hint::Log2Ceil {
                            bits_ptr,
                            dst,
                            nbits,
                            floor,
                        } => RHint::Log2Ceil {
                            bits_ptr: *bits_ptr,
                            dst: *dst,
                            nbits: *nbits,
                            floor: *floor,
                        },
                        Hint::BitDecompose { value, bits_ptr, nbits } => RHint::BitDecompose {
                            value: *value,
                            bits_ptr: *bits_ptr,
                            nbits: *nbits,
                        },
                        Hint::BitDecomposeExp { value, bits_ptr, nbits } => RHint::BitDecomposeExp {
                            value: *value,
                            bits_ptr: *bits_ptr,
                            nbits: *nbits,
                        },
                    })
                    .collect();
                hints.insert(here, rhs);
            }
            prog.push(resolve(&ins.op, &entry, sentinel, base));
        }
    }

    // Pad the bytecode to `B` (the sentinel slot g^{B-1} must exist for execution).
    prog.resize(bytecode_size, Op::Set { o: 0, k: F192::ZERO });
    let mut program = Program::assemble(prog, 0, 0, hints, frame_size["main"]);
    program.fn_ranges = lowered
        .iter()
        .map(|l| (l.name.clone(), entry[&l.name], l.code.len() as u32))
        .collect();
    program
}

/// Render compiled bytecode as a human-readable disassembly. `fp[k]` is the cell
/// `m[fp·gᵏ]` (frame offset `k`); `*(p·gᵝ)` is the dereferenced cell. `SET`
/// constants that are small g-powers (code addresses, indices) show as `gʲ`.
pub fn disassemble(prog: &[Op]) -> String {
    // Reverse index for small g-powers, to pretty-print code addresses/indices.
    let mut gmap: HashMap<F64, usize> = HashMap::new();
    let mut acc = F64::ONE;
    for j in 0..(prog.len() + 512) {
        gmap.entry(acc).or_insert(j);
        acc *= primitives::field::G;
    }
    // A machine word is 192-bit; K-valued immediates (both high limbs zero) may be small
    // g-powers (code addresses, indices), shown as `gʲ`.
    let kfmt = |k: F192| match (k.c1 == 0 && k.c2 == 0).then(|| gmap.get(&F64(k.c0))).flatten() {
        Some(j) => format!("g^{j}"),
        None if k.c1 == 0 && k.c2 == 0 => format!("0x{:016x}", k.c0),
        None => format!("0x{:016x}{:016x}{:016x}", k.c2, k.c1, k.c0),
    };

    let mut out = String::new();
    for (pc, op) in prog.iter().enumerate() {
        let line = match op {
            Op::Set { o, k } => format!("SET    fp[{o}] = {}", kfmt(*k)),
            Op::Xor { a, b, c } => format!("XOR    fp[{c}] = fp[{a}] ^ fp[{b}]"),
            Op::Mul { a, b, c } => format!("MUL    fp[{c}] = fp[{a}] * fp[{b}]"),
            Op::Deref {
                alpha,
                beta,
                gamma,
                mode,
            } => {
                let src = match mode {
                    DerefMode::Cell => format!("fp[{gamma}]"),
                    DerefMode::Pc => "g²·pc".to_string(),
                    DerefMode::Fp => "fp".to_string(),
                };
                format!("DEREF  *(fp[{alpha}]·g^{beta}) = {src}  [{mode:?}]")
            }
            Op::Jump { oc, od, of } => {
                format!("JUMP   if fp[{oc}]≠0: pc=fp[{od}], fp=fp[{of}]")
            }
            Op::Pack64x2 { a, b, c } => {
                format!("PACK64X2 fp[{c}] = pack64(fp[{a}], fp[{b}])")
            }
            Op::Blake3 { ins, out, packing } => {
                format!(
                    "BLAKE3/{packing:?} fp[{out}..]= H(fp[{}], fp[{}] | fp[{}], fp[{}])",
                    ins[0], ins[1], ins[2], ins[3]
                )
            }
        };
        out.push_str(&format!("{:>6}  {line}\n", pretty_integer(pc)));
    }
    out
}

/// Embed a `u128` source literal into the low 128 bits of a 192-bit machine word.
pub(crate) fn lit_field(n: u128) -> F192 {
    F192::new(n as u64, (n >> 64) as u64, 0)
}

/// `g^e` for a `u128` exponent (square-and-multiply). `field::g_pow` only takes
/// a `usize`; an index carried in the exponent (a Fibonacci number, say) can
/// exceed 64 bits (`ord(g) = 2^64 − 1`, so the exponent wraps mod that).
fn g_pow_u128(mut e: u128) -> F64 {
    let mut result = F64::ONE;
    let mut base = primitives::field::G;
    while e > 0 {
        if e & 1 == 1 {
            result *= base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

fn resolve(op: &LOp, entry: &HashMap<String, u32>, sentinel: u32, base: u32) -> Op {
    let resolve_kval = |kv: &KVal| -> F192 {
        match kv {
            KVal::Const(c) => *c,
            // Address / entry / sentinel constants are K-valued g-powers; embed
            // into the 128-bit word (hi lane 0).
            KVal::Entry(name) => g_pow(entry[name] as usize).into(),
            KVal::EndSentinel => g_pow(sentinel as usize).into(),
            KVal::Local(i) => g_pow((base + i) as usize).into(),
            KVal::Poison => primitives::field::G.inv().into(), // g^-1: outside the bytecode cube
        }
    };
    match op {
        LOp::Set { o, k: kv } => Op::Set {
            o: *o,
            k: resolve_kval(kv),
        },
        LOp::Xor { a, b, c } => Op::Xor { a: *a, b: *b, c: *c },
        LOp::Mul { a, b, c } => Op::Mul { a: *a, b: *b, c: *c },
        LOp::Deref {
            alpha,
            beta,
            gamma,
            mode,
        } => Op::Deref {
            alpha: *alpha,
            beta: *beta,
            gamma: *gamma,
            mode: *mode,
        },
        LOp::Jump { oc, od, of } => Op::Jump {
            oc: *oc,
            od: *od,
            of: *of,
        },
        LOp::Pack64x2 { a, b, c } => Op::Pack64x2 { a: *a, b: *b, c: *c },
        LOp::Blake3 { ins, c, packing } => Op::Blake3 {
            ins: *ins,
            out: *c,
            packing: *packing,
        },
    }
}
