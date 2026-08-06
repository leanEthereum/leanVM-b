//! Value numbering over one function's lowered code.
//!
//! leanVM's frame cells are **write-once**: a cell holds one value for the whole
//! run, so "which value does `fp[k]` hold" needs no dataflow analysis: the
//! defining instruction is the only one there will ever be. That makes common
//! subexpression elimination on the pure operations (`SET` of a constant, `XOR`,
//! `MUL`) a local rewrite: if an identical `(op, operands)` was already computed
//! in this basic block, later reads can use the earlier cell and the duplicate
//! instruction goes away.
//!
//! Why the lowerer leaves duplicates behind: it emits each expression
//! independently (an address `ptr·index` recomputed per access, a loop counter
//! advanced once for the body and once for the recursive call, the constant `1`
//! materialized per use inside a fresh frame). Roughly 5% of the recursion
//! guest's instructions were exact repeats.
//!
//! The four rules that keep this sound:
//! 1. **Only pure ops are eliminated.** `DEREF` unifies two memory cells (and
//!    bumps the bus read counts), `BLAKE3` carries bus effects, `JUMP`
//!    is control flow, so all are left alone. They still get their operands
//!    rewritten.
//! 2. **Only single-write targets.** An instruction is a candidate only if its
//!    destination cell is written exactly once in the function, counting hint
//!    writes. That protects the assert idiom (`XOR fp[t] = a^b` followed by
//!    `SET fp[t] = 0`, which panics as a write-once conflict when `a != b`):
//!    both instructions write `fp[t]`, so neither is touched and neither is
//!    offered as a replacement. It also means every cell in the substitution map
//!    is written by exactly one (dropped) instruction, so every *other*
//!    occurrence of it is a read, which is why operand rewriting can be blanket.
//! 3. **Locals only.** A candidate's destination must be a local temporary, not
//!    an argument or return slot: the caller writes the arguments and reads the
//!    returns straight out of this frame, so a write there is live even though no
//!    instruction in this function reads it.
//! 4. **Block-local.** The value map is cleared at every jump target and after
//!    every `JUMP`, so a duplicate is only ever folded into an earlier
//!    computation from the same straight-line run. Folding across a branch could
//!    redirect a read to a cell that the taken path never wrote, and an unwritten
//!    cell is a prover-chosen free variable, a soundness hole and not just a bug.

use super::ir::{Hint, KVal, LInstr, LOp, Off};
use lean_vm::cpu::hints::RHint;
use std::collections::HashMap;

/// A pure operation's identity: the opcode plus its operand cells (commutative
/// operands sorted, so `a*b` and `b*a` share an entry), or a constant's bits.
#[derive(PartialEq, Eq, Hash)]
enum Key {
    Xor(Off, Off),
    Mul(Off, Off),
    Const(u64),
}

/// Rewrite `code` in place, dropping redundant pure instructions. `abi_end` is
/// the first purely-local frame cell (see [`super::ir::Lowered::abi_end`]);
/// writes below it are visible to the caller and are never eliminated. Returns
/// the number of instructions dropped (for the `DBG_CSE` report).
pub(crate) fn cse(code: &mut Vec<LInstr>, abi_end: Off) -> usize {
    let writes = write_counts(code);
    let labels = label_targets(code);
    let run_operands = implicit_run_operands(code);

    let mut subst: HashMap<Off, Off> = HashMap::new();
    let mut seen: HashMap<Key, Off> = HashMap::new();
    let mut drop = vec![false; code.len()];
    let mut ends_block = false;

    for (i, ins) in code.iter_mut().enumerate() {
        // A jump target starts a new block; so does the instruction after a jump.
        if ends_block || labels.contains(&(i as u32)) {
            seen.clear();
        }
        ends_block = matches!(ins.op, LOp::Jump { .. });

        rewrite_reads(ins, &subst);

        // Candidates: a pure op whose destination is a local written exactly once.
        let (key, dst) = match &ins.op {
            LOp::Xor { a, b, c } => (Key::Xor(*a.min(b), *a.max(b)), *c),
            LOp::Mul { a, b, c } => (Key::Mul(*a.min(b), *a.max(b)), *c),
            LOp::Set { o, k: KVal::Const(k) } => (Key::Const(k.0), *o),
            _ => continue,
        };
        // A write to an argument or return slot is read by the CALLER, which
        // this pass cannot see: `walk` returning a flag as `SET fp[6] = 0` looks
        // dead here but is the function's result.
        if dst < abi_end || run_operands.contains(&dst) || writes.get(&dst).copied().unwrap_or(0) != 1 {
            continue;
        }
        // Hints execute immediately before their instruction. Keeping the
        // instruction is the only generally safe way to preserve that control-
        // flow position: moving a branch-local hint to the next textual
        // instruction could move it past the branch join.
        if !ins.hints.is_empty() {
            seen.entry(key).or_insert(dst);
            continue;
        }
        match seen.get(&key) {
            // The value is already in `canon`: point later reads there and drop
            // this instruction.
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

/// Copy coalescing: drop `MUL dst = src · 1` by having whatever defines `src`
/// write `dst` in the first place.
///
/// The lowerer emits that copy whenever a value has to sit at a *particular*
/// cell rather than wherever it was computed, which the 64-bit dialect asks for
/// constantly: a `BLAKE3` message chunk is two adjacent words, an extension
/// operand three, so handing one an existing value means moving it. Renaming
/// `src` to `dst` throughout the function does the move for free.
///
/// The rules are [`cse`]'s, for the same reasons, plus two of its own:
/// 5. **Single-cell definitions only.** A multiword destination (`MUL_192`'s
///    three-word run, a digest's four) is one address; renaming one of its lanes
///    would move that lane out from under the run.
/// 6. **The definition is in the copy's own block**, so the two always execute
///    together and the rename relocates the single write rather than losing it.
///    Every read of `src` is after that write, so every read is still served.
pub(crate) fn coalesce_copies(code: &mut Vec<LInstr>, abi_end: Off) -> usize {
    let writes = write_counts(code);
    let labels = label_targets(code);
    let runs = implicit_run_operands(code);
    // `FnLower::one` pools the constant, but a branch-local cache can leave more
    // than one cell holding it.
    let ones: std::collections::HashSet<Off> = code
        .iter()
        .filter_map(|ins| match &ins.op {
            LOp::Set { o, k: KVal::Const(k) } if *k == primitives::field::F64::ONE => Some(*o),
            _ => None,
        })
        .collect();

    let mut def: HashMap<Off, ()> = HashMap::new();
    let mut subst: HashMap<Off, Off> = HashMap::new();
    let mut drop = vec![false; code.len()];
    let mut ends_block = false;
    for i in 0..code.len() {
        if ends_block || labels.contains(&(i as u32)) {
            def.clear();
        }
        ends_block = matches!(code[i].op, LOp::Jump { .. });

        // `MUL dst = src · 1`, with `src` defined earlier in this same block by an
        // instruction free to write `dst` instead.
        let copy = match &code[i].op {
            LOp::Mul { a, b, c } if code[i].hints.is_empty() => match (ones.contains(a), ones.contains(b)) {
                (false, true) => Some((*a, *c)),
                (true, false) => Some((*b, *c)),
                _ => None,
            },
            _ => None,
        };
        if let Some((src, dst)) = copy
            && def.contains_key(&src)
            && src >= abi_end
            && !runs.contains(&src)
            && !subst.contains_key(&dst)
            && writes.get(&src) == Some(&1)
            && writes.get(&dst) == Some(&1)
        {
            subst.insert(src, dst);
            // `src` no longer exists, so a second copy of it cannot coalesce too.
            def.remove(&src);
            drop[i] = true;
            continue;
        }
        // Offer only single-cell definitions, and only ones this pass may move:
        // a `Cell` deref's `gamma` is the load's landing cell, so it retargets
        // like an arithmetic destination.
        let dest = match &code[i].op {
            LOp::Set { o, .. } => Some(*o),
            LOp::Xor { c, .. } | LOp::Mul { c, .. } => Some(*c),
            LOp::Deref {
                gamma,
                mode: super::DerefMode::Cell,
                ..
            } => Some(*gamma),
            _ => None,
        };
        if let Some(d) = dest {
            def.insert(d, ());
        }
    }

    let dropped = drop.iter().filter(|d| **d).count();
    if dropped > 0 {
        for ins in code.iter_mut() {
            rewrite_reads(ins, &subst);
            rewrite_dest(ins, &subst);
        }
        compact(code, &drop);
    }
    dropped
}

/// Point a single-cell destination at its renamed cell. Only the three ops
/// [`coalesce_copies`] admits as definitions can appear in its substitution, and
/// a `Cell` deref's `gamma` is already covered by [`rewrite_reads`].
fn rewrite_dest(ins: &mut LInstr, subst: &HashMap<Off, Off>) {
    if subst.is_empty() {
        return;
    }
    let dest = match &mut ins.op {
        LOp::Set { o, .. } => o,
        LOp::Xor { c, .. } | LOp::Mul { c, .. } => c,
        _ => return,
    };
    if let Some(&renamed) = subst.get(dest) {
        *dest = renamed;
    }
}

/// Cells consumed through the implicit width of a multiword operand. A BLAKE3
/// chunk, chaining value, or extension operand names only its first address;
/// rewriting (or deleting) an individual defining cell cannot retarget that
/// lane independently. Keep all such definitions in place. Whole-run
/// forwarding belongs in the lowerer, where contiguity is known explicitly.
fn implicit_run_operands(code: &[LInstr]) -> std::collections::HashSet<Off> {
    let mut out = std::collections::HashSet::new();
    let mut add = |base: Off, len: Off| {
        out.extend((0..len).map(|k| base + k));
    };
    for ins in code {
        match &ins.op {
            LOp::AddExt { a, b, .. } | LOp::MulExt { a, b, .. } => {
                add(*a, 3);
                add(*b, 3);
            }
            LOp::MulExtBase { a, b, .. } => {
                add(*a, 3);
                add(*b, 3);
            }
            LOp::Deref128 { gamma, .. } => add(*gamma, 2),
            LOp::DerefExt { gamma, .. } => add(*gamma, 3),
            LOp::Blake3 { ins, cv, .. } => {
                for &chunk in ins {
                    add(chunk, 2);
                }
                add(*cv, 4);
            }
            _ => {}
        }
    }
    out
}

/// How many times each frame cell is written, instructions and hints together.
/// Over-counting is safe (it only forgoes an optimization), so ambiguous cases
/// count as writes.
fn write_counts(code: &[LInstr]) -> HashMap<Off, u32> {
    let mut w: HashMap<Off, u32> = HashMap::new();
    let mut bump = |o: Off| *w.entry(o).or_default() += 1;
    for ins in code {
        match &ins.op {
            LOp::Set { o, .. } => bump(*o),
            LOp::Xor { c, .. } | LOp::Mul { c, .. } => bump(*c),
            LOp::AddExt { c, .. } | LOp::MulExt { c, .. } | LOp::MulExtBase { c, .. } => {
                for k in 0..3 {
                    bump(*c + k);
                }
            }
            // A `Cell` deref unifies `m[p·g^beta]` with `fp[gamma]`, which writes
            // `fp[gamma]` when it acts as a load. The `Pc`/`Fp` modes take their
            // source from the machine state and leave `gamma` unused.
            LOp::Deref { gamma, mode, .. } => {
                if matches!(mode, super::DerefMode::Cell) {
                    bump(*gamma);
                }
            }
            LOp::Deref128 { gamma, .. } => {
                for k in 0..2 {
                    bump(*gamma + k);
                }
            }
            LOp::DerefExt { gamma, .. } => {
                for k in 0..3 {
                    bump(*gamma + k);
                }
            }
            // The 32-byte digest lands in four consecutive cells.
            LOp::Blake3 { out, .. } => {
                for k in 0..4 {
                    bump(*out + k);
                }
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
                    RHint::WitnessStack { base, len, .. } => {
                        for k in 0..*len {
                            bump(*base + k);
                        }
                    }
                    RHint::Log2Ceil { dst, .. } => bump(*dst),
                    // These write HEAP cells through a pointer, not frame cells.
                    RHint::WitnessHeap { .. }
                    | RHint::BitDecompose { .. }
                    | RHint::BitDecomposeExp { .. }
                    | RHint::Print { .. } => {}
                },
            }
        }
    }
    w
}

/// Instruction indices that are jump targets ([`KVal::Local`] destinations).
fn label_targets(code: &[LInstr]) -> std::collections::HashSet<u32> {
    code.iter()
        .filter_map(|ins| match &ins.op {
            LOp::Set { k: KVal::Local(i), .. } => Some(*i),
            _ => None,
        })
        .collect()
}

/// Point every operand read at its canonical cell. Blanket-rewriting every
/// `Off` field is safe: a cell in `subst` is written exactly once, by the
/// instruction that was dropped, so no remaining field that names it is a write
/// (see rule 2 in the module docs).
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
        LOp::Xor { a, b, .. }
        | LOp::Mul { a, b, .. }
        | LOp::AddExt { a, b, .. }
        | LOp::MulExt { a, b, .. }
        | LOp::MulExtBase { a, b, .. } => {
            map(a);
            map(b);
        }
        LOp::Deref { alpha, gamma, mode, .. } => {
            map(alpha);
            if matches!(mode, super::DerefMode::Cell) {
                map(gamma);
            }
        }
        LOp::Deref128 { alpha, gamma, .. } | LOp::DerefExt { alpha, gamma, .. } => {
            map(alpha);
            map(gamma);
        }
        LOp::Jump { oc, od, of } => {
            map(oc);
            map(od);
            map(of);
        }
        LOp::Blake3 { ins: chunks, cv, .. } => {
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
                RHint::Print { cell, .. } => map(cell),
                RHint::Alloc { .. } | RHint::WitnessStack { .. } => {}
            },
        }
    }
}

/// Remove the dropped instructions and renumber the intra-function jump targets
/// ([`KVal::Local`]) to the new indices. A label is a block start and a block's
/// first instruction is never dropped (the value map is empty there), so every
/// target survives; the `saturating` fallback keeps the mapping total anyway.
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
