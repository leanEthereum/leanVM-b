//! The write-once execution interpreter: run the compiled program to produce
//! the final memory image and the per-opcode [`Trace`] (§7).

use std::collections::HashMap;

use super::*;
use crate::field::mul_by_x;

pub struct Execution {
    pub mem: Vec<F128>,      // data memory after the run, write-once (size cells, power of two)
    pub cycles: usize,       // number of instructions the run executed (trace length)
    pub mem_used: usize,     // cells actually touched, before the power-of-two pad of `mem`
    pub(crate) trace: Trace, // rows + final access-count columns, emitted in the same walk
}

impl Program {
    /// Run the program in write-once *fill* mode to produce its [`Execution`]:
    /// the final memory image and the step count. The public input seeds the
    /// first two memory cells `m[0], m[1]` (§e2e-pi). Compilation yields the
    /// `Program`; executing it (here) and proving it are separate later phases.
    pub fn execute(&self, public_input: [F128; 2]) -> Execution {
        use crate::compiler::{RHint, grow_gpow};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, grown lazily (deep recursion is
        // unbounded). Seed enough for the program counters / return targets.
        let mut gpow: Vec<F128> = vec![F128::ONE];
        let mut gmap = crate::compiler::GPowMap::default();
        gmap.insert(F128::ONE, 0u32);
        grow_gpow(&mut gpow, &mut gmap, self.prog.len() + 2);

        // Dense write-once data memory (read path stays a vector for speed), the
        // per-cell access count (g^{count}, default g^0 = 1), and a written mask.
        let mut mem: Vec<F128> = vec![F128::ZERO; self.main_frame.max(2) as usize];
        let mut written: Vec<bool> = vec![false; mem.len()];
        let mut mem_count: Vec<F128> = vec![F128::ONE; mem.len()];
        // Seed the public input into m[0], m[1] (addresses g^0, g^1, §e2e-pi).
        mem[0] = public_input[0];
        mem[1] = public_input[1];
        written[0] = true;
        written[1] = true;

        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F128> = vec![F128::ONE; self.prog.len()];

        let mut next_free = self.main_frame;
        let (mut pc, mut fp) = (self.pc0, self.fp0);
        let mut steps = 0usize;
        thread_local! {
            /// Debug: the pc of the currently executing instruction, so the
            /// write-once panic can report where the conflict happened.
            static DBG_PC: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
        }
        // `DBG_PROF=1`: per-pc step counts, printed as a per-function cycle
        // profile after the run (needs `fn_ranges`, i.e. a compiled program).
        let mut prof: Option<Vec<u64>> = std::env::var("DBG_PROF").is_ok().then(|| vec![0u64; self.prog.len()]);

        // Per-stream cursor into the named witness data (`hint_witness` pops
        // sequentially).
        let mut wit_pos: HashMap<String, usize> = HashMap::new();

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let (mut xor, mut mul, mut set, mut deref, mut jump, mut blake3): (
            Vec<Xrow>,
            Vec<Xrow>,
            Vec<Srow>,
            Vec<Drow>,
            Vec<Jrow>,
            Vec<Brow>,
        ) = (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());

        // `DEREF Cell` touches whose two sides are both still unwritten (the
        // range-check gadget's unconstrained target cells): `(deref row index,
        // a2, a3)`, back-filled after the run — write-once memory is
        // order-independent, so the value can be decided at the end (leanVM's
        // end-of-execution deref-hint resolution).
        let mut deferred: Vec<(usize, usize, u32)> = Vec::new();

        // Grow the dense vectors so `idx` is in range (keeps mem/written/mem_count in
        // sync). All accessed cells satisfy cell < next_free after their frame's
        // allocation, so this only ever extends.
        fn ensure(mem: &mut Vec<F128>, written: &mut Vec<bool>, mem_count: &mut Vec<F128>, idx: usize) {
            if idx >= mem.len() {
                let n = idx + 1;
                mem.resize(n, F128::ZERO);
                written.resize(n, false);
                mem_count.resize(n, F128::ONE);
            }
        }
        // Read a cell; an unwritten cell reads as ZERO.
        fn get(mem: &[F128], written: &[bool], cell: u32) -> F128 {
            let c = cell as usize;
            if c < written.len() && written[c] {
                mem[c]
            } else {
                F128::ZERO
            }
        }
        // Write-once store: writing a different value to an already-set cell panics.
        fn put(mem: &mut Vec<F128>, written: &mut Vec<bool>, mem_count: &mut Vec<F128>, cell: u32, v: F128) {
            ensure(mem, written, mem_count, cell as usize);
            let c = cell as usize;
            if written[c] {
                assert!(
                    mem[c] == v,
                    "write-once conflict at cell {cell} (pc {}): had {:x}:{:x}, new {:x}:{:x}",
                    DBG_PC.with(|p| p.get()),
                    mem[c].hi,
                    mem[c].lo,
                    v.hi,
                    v.lo
                );
            } else {
                mem[c] = v;
                written[c] = true;
            }
        }
        // Read the running access count and advance it by ×g (the free increment).
        // ×g is ×x, i.e. `mul_by_x` — a shift+fold, not a PMULL; this runs on every
        // memory access (several million per run), so the cheap form matters.
        fn bump_access_count(mem: &mut Vec<F128>, written: &mut Vec<bool>, mem_count: &mut Vec<F128>, cell: u32) -> F128 {
            ensure(mem, written, mem_count, cell as usize);
            let cell_idx = cell as usize;
            let count = mem_count[cell_idx];
            mem_count[cell_idx] = mul_by_x(count);
            count
        }

        while pc != ending_pc {
            assert!(steps < 100_000_000, "step limit exceeded (runaway recursion?)");
            DBG_PC.with(|p| p.set(pc));
            if let Some(p) = prof.as_mut() {
                p[pc as usize] += 1;
            }

            // Apply the hints scheduled before this instruction.
            if let Some(hs) = self.hints.get(&pc) {
                // Pop the next entry of witness stream `name`; it must hold
                // exactly `len` values (the destination run's length).
                let pop_witness = |wit_pos: &mut HashMap<String, usize>, name: &str, len: u32| {
                    let entries = self
                        .witness
                        .get(name)
                        .unwrap_or_else(|| panic!("no witness stream `{name}` (Program::set_witness)"));
                    let pos = wit_pos.entry(name.to_string()).or_insert(0);
                    let entry = entries.get(*pos).unwrap_or_else(|| {
                        panic!(
                            "witness stream `{name}` exhausted (needs entry {}, has {})",
                            *pos + 1,
                            entries.len()
                        )
                    });
                    assert_eq!(
                        entry.len(),
                        len as usize,
                        "witness `{name}` entry {} holds {} values, the destination {len}",
                        *pos,
                        entry.len()
                    );
                    *pos += 1;
                    entry.clone()
                };
                for h in hs {
                    match h {
                        // A fresh region: write its base `g^{next_free}` into the
                        // pointer cell (once) and reserve `size` cells. `AllocDyn`
                        // reads the size from a cell at runtime.
                        RHint::Alloc { .. } | RHint::AllocDyn { .. } => {
                            let (ptr, size) = match *h {
                                RHint::Alloc { ptr, size } => (ptr, size),
                                // A runtime size is carried in the exponent:
                                // the cell holds g^k, allocate k cells (reverse
                                // g-power lookup, growing the index if needed).
                                RHint::AllocDyn { ptr, size } => {
                                    let sz = get(&mem, &written, fp + size);
                                    let cells = gmap.get(&sz).copied().unwrap_or_else(|| {
                                        grow_gpow(&mut gpow, &mut gmap, 1 << 20);
                                        *gmap
                                            .get(&sz)
                                            .unwrap_or_else(|| panic!("HeapBuf size is not a g-power below 2^20 cells"))
                                    });
                                    (ptr, cells)
                                }
                                _ => unreachable!(),
                            };
                            let cell = fp + ptr;
                            ensure(&mut mem, &mut written, &mut mem_count, cell as usize);
                            if !written[cell as usize] {
                                let base = next_free;
                                next_free += size;
                                grow_gpow(&mut gpow, &mut gmap, (base + size) as usize);
                                ensure(&mut mem, &mut written, &mut mem_count, next_free as usize);
                                mem[cell as usize] = gpow[base as usize];
                                written[cell as usize] = true;
                            }
                        }
                        RHint::WitnessStack { name, base, len } => {
                            let vals = pop_witness(&mut wit_pos, name, *len);
                            for (k, v) in vals.into_iter().enumerate() {
                                put(&mut mem, &mut written, &mut mem_count, fp + base + k as u32, v);
                            }
                        }
                        RHint::WitnessHeap { name, ptr, lo, len } => {
                            let p = get(&mem, &written, fp + ptr);
                            let b = *gmap
                                .get(&p)
                                .unwrap_or_else(|| panic!("hint_witness heap pointer is not a g-power"));
                            let vals = pop_witness(&mut wit_pos, name, *len);
                            for (k, v) in vals.into_iter().enumerate() {
                                put(&mut mem, &mut written, &mut mem_count, b + lo + k as u32, v);
                            }
                        }
                        RHint::CeilLog2 { bits_ptr, dst, nbits, floor } => {
                            let p = get(&mem, &written, fp + bits_ptr);
                            let b = *gmap
                                .get(&p)
                                .unwrap_or_else(|| panic!("ceil_log2 bits pointer is not a g-power"));
                            let mut word: u128 = 0;
                            for j in 0..*nbits {
                                if !get(&mem, &written, b + j).is_zero() {
                                    word |= 1u128 << j;
                                }
                            }
                            let cl = if word <= 1 { 0 } else { u128::BITS - (word - 1).leading_zeros() };
                            let mu = cl.max(*floor);
                            put(&mut mem, &mut written, &mut mem_count, fp + dst, crate::field::g_pow(mu as usize));
                        }
                    }
                }
            }
            // Cover the g-powers this step may index (g²·pc return target, g^fp).
            grow_gpow(&mut gpow, &mut gmap, (pc as usize + 2).max(fp as usize));

            let bytecode_read = {
                let v = bytecode_count[pc as usize];
                bytecode_count[pc as usize] = mul_by_x(v);
                v
            };

            match self.prog[pc as usize] {
                Op::Xor { a, b, c } | Op::Mul { a, b, c } => {
                    let is_xor = matches!(self.prog[pc as usize], Op::Xor { .. });
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    // The row is the equality `m[c] = m[a] op m[b]` over write-once
                    // memory. Normally the operands are known and the result is
                    // computed forward; with the result already written and exactly
                    // one operand unwritten, the runner back-solves the operand
                    // (leanVM's ADD deduction, multiplicatively: this is what
                    // produces the range-check complement `y = g^{k-1}·x^{-1}` from
                    // `MUL x·y = g^{k-1}`, with no dedicated hint).
                    let is_set = |w: &[bool], cell: u32| (cell as usize) < w.len() && w[cell as usize];
                    if is_set(&written, ac) {
                        let (ha, hb) = (is_set(&written, aa), is_set(&written, ab));
                        if ha ^ hb {
                            let vc = get(&mem, &written, ac);
                            let vk = get(&mem, &written, if ha { aa } else { ab });
                            let v = if is_xor {
                                vc + vk
                            } else {
                                assert!(!vk.is_zero(), "cannot back-solve MUL through a zero operand");
                                vc * vk.inv()
                            };
                            put(&mut mem, &mut written, &mut mem_count, if ha { ab } else { aa }, v);
                        }
                    }
                    let va = get(&mem, &written, aa);
                    let vb = get(&mem, &written, ab);
                    let vc = if is_xor { va + vb } else { va * vb };
                    put(&mut mem, &mut written, &mut mem_count, ac, vc);
                    let ra = bump_access_count(&mut mem, &mut written, &mut mem_count, aa);
                    let rb = bump_access_count(&mut mem, &mut written, &mut mem_count, ab);
                    let rc = bump_access_count(&mut mem, &mut written, &mut mem_count, ac);
                    let row = Xrow {
                        pc,
                        fp,
                        aa,
                        ab,
                        ac,
                        ra,
                        rb,
                        rc,
                        bytecode_read,
                    };
                    if is_xor {
                        xor.push(row);
                    } else {
                        mul.push(row);
                    }
                    pc += 1;
                }
                Op::Set { o, k } => {
                    let a = fp + o;
                    put(&mut mem, &mut written, &mut mem_count, a, k);
                    let r = bump_access_count(&mut mem, &mut written, &mut mem_count, a);
                    set.push(Srow {
                        pc,
                        fp,
                        o,
                        a,
                        k,
                        r,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Deref {
                    alpha,
                    beta,
                    gamma,
                    mode,
                } => {
                    let a1 = fp + alpha;
                    let p = get(&mem, &written, a1);
                    let base = match gmap.get(&p) {
                        Some(&b) => b,
                        None => {
                            // Not indexed yet: grow the g-power index to the minimum
                            // memory size — range-check touches point anywhere below
                            // their bound (≤ 2^MIN_LOG_MEM), not just at allocated
                            // frames/buffers. A value still absent is no valid
                            // pointer: a wild deref, or a failed range check
                            // (`assert log _ < _`) surfacing honestly.
                            grow_gpow(&mut gpow, &mut gmap, 1 << MIN_LOG_MEM);
                            *gmap.get(&p).unwrap_or_else(|| {
                                panic!(
                                    "DEREF pointer is not a small g-power at pc {pc}: a wild \
                                     pointer, or a failed range check \
                                     (value 0x{:016x}{:016x})",
                                    p.hi, p.lo
                                )
                            })
                        }
                    };
                    let a2 = (base + beta) as usize;
                    let a3 = fp + gamma;
                    match mode {
                        DerefMode::Cell => {
                            // Equality m[a2] == m[a3]: fill the unset side.
                            ensure(&mut mem, &mut written, &mut mem_count, a2);
                            let has2 = written[a2];
                            let has3 = (a3 as usize) < written.len() && written[a3 as usize];
                            match (has2, has3) {
                                (true, true) => {
                                    assert!(mem[a2] == get(&mem, &written, a3), "DEREF mismatch")
                                }
                                (true, false) => {
                                    let v = mem[a2];
                                    put(&mut mem, &mut written, &mut mem_count, a3, v);
                                }
                                (false, true) => {
                                    let v = get(&mem, &written, a3);
                                    put(&mut mem, &mut written, &mut mem_count, a2 as u32, v);
                                }
                                (false, false) => {
                                    // Both sides still unwritten: a range-check
                                    // touch (only the address validity of `a2`
                                    // matters, not its value). Defer: the row is
                                    // pushed with ZERO values and patched after
                                    // the run, once `m[a2]`'s final value (a later
                                    // program write, or ZERO) is known.
                                    deferred.push((deref.len(), a2, a3));
                                }
                            }
                        }
                        DerefMode::Pc => {
                            let v = gpow[pc as usize + 2];
                            put(&mut mem, &mut written, &mut mem_count, a2 as u32, v);
                        }
                        DerefMode::Fp => {
                            let v = gpow[fp as usize];
                            put(&mut mem, &mut written, &mut mem_count, a2 as u32, v);
                        }
                    }
                    let v2 = get(&mem, &written, a2 as u32);
                    let v3 = get(&mem, &written, a3);
                    let r1 = bump_access_count(&mut mem, &mut written, &mut mem_count, a1);
                    let r2 = bump_access_count(&mut mem, &mut written, &mut mem_count, a2 as u32);
                    let r3 = bump_access_count(&mut mem, &mut written, &mut mem_count, a3);
                    deref.push(Drow {
                        pc,
                        fp,
                        alpha,
                        beta,
                        gamma,
                        mode,
                        a1,
                        p,
                        a2,
                        a3,
                        v2,
                        v3,
                        r1,
                        r2,
                        r3,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Jump { oc, od, of } => {
                    let (ac, ad, af) = (fp + oc, fp + od, fp + of);
                    let c = get(&mem, &written, ac);
                    let d = get(&mem, &written, ad);
                    let f = get(&mem, &written, af);
                    // `b = [c ≠ 0]` is needed now; `w = c⁻¹` is only recorded into
                    // the trace (never used for control flow), so it is deferred to
                    // ONE batched Montgomery inversion after the run — computing it
                    // per-jump here runs a 254-mul Fermat inverse on every taken
                    // branch (~2^17 of them), which dominated `execute`. Placeholder
                    // 0 now; batch-filled below (bit-identical to `c.inv()`).
                    let b = if c.is_zero() { F128::ZERO } else { F128::ONE };
                    let w = F128::ZERO;
                    let rc = bump_access_count(&mut mem, &mut written, &mut mem_count, ac);
                    let rd = bump_access_count(&mut mem, &mut written, &mut mem_count, ad);
                    let rf = bump_access_count(&mut mem, &mut written, &mut mem_count, af);
                    let taken = !c.is_zero();
                    let (npc, nfp) = if taken {
                        (d, f)
                    } else {
                        (mul_by_x(gpow[pc as usize]), gpow[fp as usize])
                    };
                    jump.push(Jrow {
                        pc,
                        fp,
                        npc,
                        nfp,
                        oc,
                        od,
                        of,
                        ac,
                        ad,
                        af,
                        c,
                        d,
                        f,
                        w,
                        b,
                        rc,
                        rd,
                        rf,
                        bytecode_read,
                    });
                    if taken {
                        pc = *gmap.get(&d).expect("JUMP target not a g-power");
                        fp = *gmap.get(&f).expect("JUMP fp not a g-power");
                    } else {
                        pc += 1;
                    }
                }
                Op::Blake3 { ins, out } => {
                    // Four independently-addressed input words; the output spans two
                    // consecutive words (ac, ac+1).
                    let (aa0, aa1, ab0, ab1) = (fp + ins[0], fp + ins[1], fp + ins[2], fp + ins[3]);
                    let ac = fp + out;
                    let va0 = get(&mem, &written, aa0);
                    let va1 = get(&mem, &written, aa1);
                    let vb0 = get(&mem, &written, ab0);
                    let vb1 = get(&mem, &written, ab1);
                    // Compress the 64 input bytes to the 32-byte digest, then write
                    // it to c's two words. The relation is unproven (no constraint),
                    // but the prover still computes a definite digest so the output
                    // cells are consistent for any later read.
                    let (vc0, vc1) = blake3_compress(va0, va1, vb0, vb1);
                    put(&mut mem, &mut written, &mut mem_count, ac, vc0);
                    put(&mut mem, &mut written, &mut mem_count, ac + 1, vc1);
                    let ra0 = bump_access_count(&mut mem, &mut written, &mut mem_count, aa0);
                    let ra1 = bump_access_count(&mut mem, &mut written, &mut mem_count, aa1);
                    let rb0 = bump_access_count(&mut mem, &mut written, &mut mem_count, ab0);
                    let rb1 = bump_access_count(&mut mem, &mut written, &mut mem_count, ab1);
                    let rc0 = bump_access_count(&mut mem, &mut written, &mut mem_count, ac);
                    let rc1 = bump_access_count(&mut mem, &mut written, &mut mem_count, ac + 1);
                    blake3.push(Brow {
                        pc,
                        fp,
                        aa0,
                        aa1,
                        ab0,
                        ab1,
                        ac,
                        va0,
                        va1,
                        vb0,
                        vb1,
                        vc0,
                        vc1,
                        ra0,
                        ra1,
                        rb0,
                        rb1,
                        rc0,
                        rc1,
                        bytecode_read,
                    });
                    pc += 1;
                }
            }
            steps += 1;
        }

        assert_eq!((pc, fp), (ending_pc, 0), "main must halt at the sentinel pc g^{{B-1}}");

        if let Some(p) = &prof {
            let mut rows: Vec<(String, u64)> = self
                .fn_ranges
                .iter()
                .map(|(name, entry, len)| {
                    let total: u64 = p[*entry as usize..(*entry + *len) as usize].iter().sum();
                    (name.clone(), total)
                })
                .collect();
            rows.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
            eprintln!("== DBG_PROF: cycles by function ({steps} total) ==");
            for (name, c) in rows.iter().filter(|(_, c)| *c > 0) {
                eprintln!("  {c:>9}  {:>5.1}%  {name}", 100.0 * *c as f64 / steps as f64);
            }
        }

        // Resolve the deferred DEREF touches: a fixpoint, so a touch whose cell is
        // filled by another deferred entry picks up that value; cells nobody ever
        // writes are fixed to ZERO. The rows' values are patched in place (their
        // access counts were already bumped during the walk — the memory bus is
        // order-independent, it only needs every access to agree on the value).
        while {
            let before = deferred.len();
            deferred.retain(|&(i, a2, a3)| {
                if written[a2] {
                    let v = mem[a2];
                    put(&mut mem, &mut written, &mut mem_count, a3, v);
                    deref[i].v2 = v;
                    deref[i].v3 = v;
                    false
                } else {
                    true
                }
            });
            deferred.len() < before
        } {}
        for (_, a2, a3) in deferred {
            // Never written: the cells are genuinely unconstrained; fix them (and
            // the rows, already ZERO) to ZERO.
            put(&mut mem, &mut written, &mut mem_count, a2 as u32, F128::ZERO);
            put(&mut mem, &mut written, &mut mem_count, a3, F128::ZERO);
        }

        // Fill the deferred JUMP inverse hints `w = c⁻¹` (the is-nonzero witness)
        // in ONE batched Montgomery inversion: a single field inverse plus ~2·#jumps
        // multiplies, instead of a 254-mul Fermat inverse per taken branch. `w` is
        // only recorded into the trace, so this reproduces exactly the per-jump
        // `c.inv()` (0 for the c = 0 rows). `prefix[i]` is the running product of the
        // nonzero conditions before row `i`; `acc` ends as the product of all
        // nonzero conditions (nonzero, so invertible).
        {
            let mut acc = F128::ONE;
            let mut prefix: Vec<F128> = Vec::with_capacity(jump.len());
            for r in &jump {
                prefix.push(acc);
                if !r.c.is_zero() {
                    acc *= r.c;
                }
            }
            let mut inv = acc.inv();
            for (i, r) in jump.iter_mut().enumerate().rev() {
                if !r.c.is_zero() {
                    r.w = inv * prefix[i];
                    inv *= r.c;
                }
            }
        }

        // Pad memory to a power of two (the boundary tables read a dense image),
        // at least 2^MIN_LOG_MEM cells (doc §Memory).
        let mem_used = mem.len();
        let cells = mem.len().next_power_of_two().max(1 << MIN_LOG_MEM);
        assert!(cells <= 1 << MAX_LOG_MEM, "data memory exceeds 2^{MAX_LOG_MEM} cells");
        mem.resize(cells, F128::ZERO);
        mem_count.resize(cells, F128::ONE);
        let trace = Trace {
            xor,
            mul,
            set,
            deref,
            jump,
            blake3,
            mem_count,
            bytecode_count,
        };
        Execution {
            mem,
            cycles: steps,
            mem_used,
            trace,
        }
    }
}
