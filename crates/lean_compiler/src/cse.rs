//! Block-local common subexpression elimination for pure operations on write-once frame cells.
//!
//! Candidates must be local, have one write including hints, and carry no hints themselves. The value map is cleared at control-flow boundaries. Effectful instructions are retained, although reads from them may be rewritten.

use super::ir::{Hint, KVal, LInstr, LOp, Off};
use lean_vm::cpu::hints::RHint;
use std::collections::{HashMap, HashSet};

/// A pure operation's identity: the opcode plus its operand cells (commutative
/// operands sorted, so `a*b` and `b*a` share an entry), or a constant's bits.
#[derive(PartialEq, Eq, Hash)]
enum Key {
    Xor(Off, Off),
    Mul(Off, Off),
    Const([u64; 3]),
}

/// Rewrite `code` in place, leaving caller-visible cells and fill blocks untouched.
pub(crate) fn cse(code: &mut Vec<LInstr>, abi_end: Off, frozen_from: usize) -> usize {
    let writes = write_counts(code);
    let labels = label_targets(code);

    let mut subst: HashMap<Off, Off> = HashMap::new();
    let mut seen: HashMap<Key, Off> = HashMap::new();
    let mut drop = vec![false; code.len()];
    let mut ends_block = false;

    for (i, ins) in code.iter_mut().enumerate() {
        if i >= frozen_from {
            break;
        }
        if ends_block || labels.contains(&(i as u32)) {
            seen.clear();
        }
        ends_block = matches!(ins.op, LOp::Jump { .. });

        rewrite_reads(ins, &subst);

        let (key, dst) = match &ins.op {
            LOp::Xor { a, b, c } => (Key::Xor(*a.min(b), *a.max(b)), *c),
            LOp::Mul { a, b, c } => (Key::Mul(*a.min(b), *a.max(b)), *c),
            LOp::Set { o, k: KVal::Const(k) } => (Key::Const([k.c0, k.c1, k.c2]), *o),
            _ => continue,
        };
        if dst < abi_end || writes.get(&dst).copied().unwrap_or(0) != 1 {
            continue;
        }
        if !ins.hints.is_empty() {
            seen.entry(key).or_insert(dst);
            continue;
        }
        match seen.get(&key) {
            Some(&canon) => {
                subst.insert(dst, canon);
                drop[i] = true;
            }
            None => {
                seen.insert(key, dst);
            }
        }
    }

    let dropped = drop.iter().filter(|d| **d).count();
    if dropped > 0 {
        compact(code, &drop);
    }
    dropped
}

/// How many times each frame cell is written, instructions and hints together.
/// Over-counting is safe (it only forgoes an optimization), so ambiguous cases
/// count as writes.
fn write_counts(code: &[LInstr]) -> HashMap<Off, u32> {
    let mut writes: HashMap<Off, u32> = HashMap::new();
    let mut bump = |offset: Off| *writes.entry(offset).or_default() += 1;
    for ins in code {
        match &ins.op {
            LOp::Set { o, .. } => bump(*o),
            LOp::Xor { c, .. } | LOp::Mul { c, .. } => bump(*c),
            // A `Cell` deref unifies `m[p·g^beta]` with `fp[gamma]`, which writes
            // `fp[gamma]` when it acts as a load. The `Pc`/`Fp` modes take their
            // source from the machine state and leave `gamma` unused.
            LOp::Deref { gamma, mode, .. } => {
                if matches!(mode, super::DerefMode::Cell) {
                    bump(*gamma);
                }
            }
            // The 32-byte digest lands in two consecutive cells.
            LOp::Blake2s { c, .. } => {
                bump(*c);
                bump(*c + 1);
            }
            LOp::Jump { .. } => {}
        }
        for h in &ins.hints {
            match h {
                Hint::AllocFrame { ptr, .. }
                | Hint::AllocFrameMax { ptr, .. }
                | Hint::AllocBuffer { ptr, .. }
                | Hint::AllocBufferDyn { ptr, .. } => bump(*ptr),
                Hint::Resolved(r) => match r {
                    RHint::Alloc { ptr, .. } | RHint::AllocDyn { ptr, .. } => bump(*ptr),
                    RHint::WitnessStack { base, len, .. } | RHint::FieldLimbs { base, len, .. } => {
                        for k in 0..*len {
                            bump(*base + k);
                        }
                    }
                    RHint::Log2Ceil { dst, .. } | RHint::Inverse { dst, .. } => bump(*dst),
                    // These write HEAP cells through a pointer, not frame cells.
                    RHint::WitnessHeap { .. }
                    | RHint::BitDecompose { .. }
                    | RHint::BitDecomposeExp { .. }
                    | RHint::Print { .. } => {}
                },
            }
        }
    }
    writes
}

fn label_targets(code: &[LInstr]) -> HashSet<u32> {
    code.iter()
        .filter_map(|ins| match &ins.op {
            LOp::Set { k: KVal::Local(i), .. } => Some(*i),
            _ => None,
        })
        .collect()
}

fn rewrite_reads(ins: &mut LInstr, subst: &HashMap<Off, Off>) {
    if subst.is_empty() {
        return;
    }
    let map = |o: &mut Off| {
        if let Some(&c) = subst.get(o) {
            *o = c;
        }
    };
    match &mut ins.op {
        LOp::Set { .. } => {}
        LOp::Xor { a, b, .. } | LOp::Mul { a, b, .. } => {
            map(a);
            map(b);
        }
        LOp::Deref { alpha, gamma, mode, .. } => {
            map(alpha);
            if matches!(mode, super::DerefMode::Cell) {
                map(gamma);
            }
        }
        LOp::Jump { oc, od, of } => {
            map(oc);
            map(od);
            map(of);
        }
        LOp::Blake2s { ins: chunks, cv, .. } => {
            for chunk in chunks.iter_mut() {
                map(chunk);
            }
            map(cv);
        }
    }
    for h in &mut ins.hints {
        match h {
            Hint::AllocBufferDyn { size, .. } => map(size),
            Hint::AllocFrame { .. } | Hint::AllocFrameMax { .. } | Hint::AllocBuffer { .. } => {}
            Hint::Resolved(r) => match r {
                RHint::AllocDyn { size, .. } => map(size),
                RHint::WitnessHeap { ptr, .. } => map(ptr),
                RHint::Log2Ceil { bits_ptr, .. } => map(bits_ptr),
                RHint::BitDecompose { value, bits_ptr, .. } | RHint::BitDecomposeExp { value, bits_ptr, .. } => {
                    map(value);
                    map(bits_ptr);
                }
                RHint::FieldLimbs { value, .. } | RHint::Inverse { value, .. } => map(value),
                RHint::Print { cell, .. } => map(cell),
                RHint::Alloc { .. } | RHint::WitnessStack { .. } => {}
            },
        }
    }
}

fn compact(code: &mut Vec<LInstr>, drop: &[bool]) {
    let mut new_index = Vec::with_capacity(code.len() + 1);
    let mut next = 0u32;
    for d in drop {
        new_index.push(next);
        if !*d {
            next += 1;
        }
    }
    new_index.push(next);
    let mut kept: Vec<LInstr> = code
        .drain(..)
        .zip(drop)
        .filter_map(|(ins, d)| (!*d).then_some(ins))
        .collect();
    for ins in &mut kept {
        if let LOp::Set { k: KVal::Local(i), .. } = &mut ins.op {
            *i = new_index[*i as usize];
        }
    }
    *code = kept;
}
