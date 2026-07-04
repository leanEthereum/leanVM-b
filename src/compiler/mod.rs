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

use crate::cpu::{DerefMode, Op, Program};
use crate::field::{F128, g_pow};

mod ast;
mod ir;
mod lower;
mod parser;
pub use ast::*;
pub(crate) use ir::*;
use lower::lower_func;
pub(crate) use parser::subst_stmts;
pub use parser::{parse, parse_const, parse_file};

// ----------------------------------------------------------------------------
// Layout, resolution, witness generation
// ----------------------------------------------------------------------------

/// A hint resolved to concrete offsets/sizes, keyed by global program counter.
#[derive(Clone, Debug)]
pub(crate) enum RHint {
    /// Allocate a fresh region of `size` cells and write `g^{base}` to the cell.
    Alloc { ptr: Off, size: u32 },
    /// `Alloc` with the cell count read at runtime as the g-power exponent of
    /// `m[fp+size]`.
    AllocDyn { ptr: Off, size: Off },
    /// Pop stream `name`'s next entry (`len` values) into frame cells `fp+base+k`.
    WitnessStack { name: String, base: Off, len: u32 },
    /// Pop stream `name`'s next entry (`len` values) into heap cells `m[fp+ptr]·g^{lo+k}`.
    WitnessHeap { name: String, ptr: Off, lo: u32, len: u32 },
}

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
    queue.push(main.clone());
    for f in &ast.funcs {
        if f.name != "main" {
            queue.push(f.clone());
        }
    }
    // Definitions by name, for Const-parameter specialization at call sites.
    let defs: HashMap<String, Func> = ast.funcs.iter().map(|f| (f.name.clone(), f.clone())).collect();

    let mut loop_ctr = 0usize;
    let mut lowered: Vec<Lowered> = Vec::new();
    let mut i = 0;
    while i < queue.len() {
        let f = queue[i].clone();
        i += 1;
        // A function with Const parameters is a template: only its call-site
        // specializations (queued with the constants substituted) are lowered.
        if f.const_params.contains(&true) {
            continue;
        }
        let low = lower_func(&f, &mut queue, &mut loop_ctr, &defs);
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
    let bytecode_size = total.max(1).next_power_of_two();
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
                    })
                    .collect();
                hints.insert(here, rhs);
            }
            prog.push(resolve(&ins.op, &entry, sentinel, base));
        }
    }

    // Pad the bytecode to `B` (the sentinel slot g^{B-1} must exist for execution).
    prog.resize(bytecode_size, Op::Set { o: 0, k: F128::ZERO });
    Program::assemble(prog, 0, 0, hints, frame_size["main"])
}

/// Render compiled bytecode as a human-readable disassembly. `fp[k]` is the cell
/// `m[fp·gᵏ]` (frame offset `k`); `*(p·gᵝ)` is the dereferenced cell. `SET`
/// constants that are small g-powers (code addresses, indices) show as `gʲ`.
pub fn disassemble(prog: &[Op]) -> String {
    // Reverse index for small g-powers, to pretty-print code addresses/indices.
    let mut gmap: HashMap<F128, usize> = HashMap::new();
    let mut acc = F128::ONE;
    for j in 0..(prog.len() + 512) {
        gmap.entry(acc).or_insert(j);
        acc *= crate::field::G;
    }
    let kfmt = |k: F128| match gmap.get(&k) {
        Some(j) => format!("g^{j}"),
        None => format!("0x{:016x}{:016x}", k.hi, k.lo),
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
            Op::Blake3 { a, b, c } => {
                format!("BLAKE3 fp[{c}..]= H(fp[{a}..], fp[{b}..])")
            }
        };
        out.push_str(&format!("{pc:>4}  {line}\n"));
    }
    out
}

/// `g^e` for a `u128` exponent (square-and-multiply). `field::g_pow` only takes
/// a `usize`; an index carried in the exponent (a Fibonacci number, say) can
/// exceed 64 bits.
fn g_pow_u128(mut e: u128) -> F128 {
    let mut result = F128::ONE;
    let mut base = crate::field::G;
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
    let resolve_kval = |kv: &KVal| match kv {
        KVal::Const(c) => *c,
        KVal::Entry(name) => g_pow(entry[name] as usize),
        KVal::EndSentinel => g_pow(sentinel as usize),
        KVal::Local(i) => g_pow((base + i) as usize),
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
        LOp::Blake3 { a, b, c } => Op::Blake3 { a: *a, b: *b, c: *c },
    }
}

/// Extend the `g^j` table and its reverse index `g^j ↦ j` to cover index `upto`.
pub(crate) fn grow_gpow(gpow: &mut Vec<F128>, gmap: &mut HashMap<F128, u32>, upto: usize) {
    assert!(upto < (1 << 28), "address space overflow (program too large)");
    while gpow.len() <= upto {
        let next = *gpow.last().unwrap() * crate::field::G;
        gmap.insert(next, gpow.len() as u32);
        gpow.push(next);
    }
}
