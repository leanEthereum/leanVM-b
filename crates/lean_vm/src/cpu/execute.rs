//! The write-once execution interpreter: run the compiled program to produce
//! the final memory image and the per-opcode [`Trace`] (§7).

use std::collections::HashMap;

use super::*;
use primitives::field::{F64, F192, mul_by_g};

pub struct Execution {
    pub mem: Vec<F192>,      // data memory after the run, write-once (size cells, power of two)
    pub cycles: usize,       // number of instructions the run executed (trace length)
    pub mem_used: usize,     // cells actually touched, before the power-of-two pad of `mem`
    pub(crate) trace: Trace, // rows + final access-count columns, emitted in the same walk
}

/// A memory word interpreted as a K-valued address: valid only when both
/// extension limbs are zero (every g-power is a K-element).
fn as_addr(v: F192) -> Option<F64> {
    (v.c1 == 0 && v.c2 == 0).then_some(F64(v.c0))
}

impl Program {
    /// Run the program in write-once *fill* mode to produce its [`Execution`]:
    /// the final memory image and the step count. The public input seeds the
    /// first two memory cells `m[0], m[1]` (§e2e-pi). Compilation yields the
    /// `Program`; executing it (here) and proving it are separate later phases.
    pub fn execute(&self, public_input: [F192; 2]) -> Execution {
        use super::hints::{RHint, grow_gpow};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, grown lazily (deep recursion is
        // unbounded). Seed enough for the program counters / return targets.
        let mut gpow: Vec<F64> = vec![F64::ONE];
        let mut gmap = super::hints::GPowMap::default();
        gmap.insert(F64::ONE, 0u32);
        grow_gpow(&mut gpow, &mut gmap, self.prog.len() + 2);

        // Dense write-once data memory (read path stays a vector for speed), the
        // per-cell access count (g^{count}, default g^0 = 1), and a written mask.
        let mut mem: Vec<F192> = vec![F192::ZERO; self.main_frame.max(2) as usize];
        let mut written: Vec<bool> = vec![false; mem.len()];
        let mut mem_count: Vec<F64> = vec![F64::ONE; mem.len()];
        // Seed the public input into m[0], m[1] (addresses g^0, g^1, §e2e-pi).
        mem[0] = public_input[0];
        mem[1] = public_input[1];
        written[0] = true;
        written[1] = true;

        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; self.prog.len()];

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
        // Baby-step table for `hint_decompose_bits_exponent`, built on first use.
        let mut dlog_cache: Option<(super::hints::GPowMap, F64)> = None;

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let mut xor: Vec<Xrow> = Vec::new();
        let mut mul: Vec<Xrow> = Vec::new();
        let mut set: Vec<Srow> = Vec::new();
        let mut deref: Vec<Drow> = Vec::new();
        let mut jump: Vec<Jrow> = Vec::new();
        let mut sha256: Vec<Brow> = Vec::new();

        // `DEREF Cell` touches whose two sides are both still unwritten (the
        // range-check gadget's unconstrained target cells): `(deref row index,
        // a2, a3)`, back-filled after the run — write-once memory is
        // order-independent, so the value can be decided at the end (leanVM's
        // end-of-execution deref-hint resolution).
        let mut deferred: Vec<(usize, usize, u32)> = Vec::new();

        // Attribution aid: LEANVM_PC_HISTO=1 dumps per-pc execution counts
        // alongside the disassembly after the run, tying cycles to source.

        // Grow the dense vectors so `idx` is in range (keeps mem/written/mem_count in
        // sync). All accessed cells satisfy cell < next_free after their frame's
        // allocation, so this only ever extends.
        fn ensure(mem: &mut Vec<F192>, written: &mut Vec<bool>, mem_count: &mut Vec<F64>, idx: usize) {
            if idx >= mem.len() {
                let n = idx + 1;
                mem.resize(n, F192::ZERO);
                written.resize(n, false);
                mem_count.resize(n, F64::ONE);
            }
        }
        // Read a cell; an unwritten cell reads as ZERO.
        fn get(mem: &[F192], written: &[bool], cell: u32) -> F192 {
            let c = cell as usize;
            if c < written.len() && written[c] {
                mem[c]
            } else {
                F192::ZERO
            }
        }
        // Write-once store: writing a different value to an already-set cell panics.
        fn put(mem: &mut Vec<F192>, written: &mut Vec<bool>, mem_count: &mut Vec<F64>, cell: u32, v: F192) {
            ensure(mem, written, mem_count, cell as usize);
            let c = cell as usize;
            if written[c] {
                assert!(
                    mem[c] == v,
                    "write-once conflict at cell {cell} (pc {}): had {:x}:{:x}:{:x}, new {:x}:{:x}:{:x}",
                    DBG_PC.with(|p| p.get()),
                    mem[c].c2,
                    mem[c].c1,
                    mem[c].c0,
                    v.c2,
                    v.c1,
                    v.c0
                );
            } else {
                mem[c] = v;
                written[c] = true;
            }
        }
        // Bounded discrete log for `hint_decompose_bits_exponent`: find n < 2^nbits
        // with g^n = x, by baby-step giant-step (baby table g^j for j < 2^17,
        // built once per run; giant step ×g^(-2^17)). Prover-side only — the
        // guest re-verifies the hinted bits in-circuit.
        fn bounded_dlog(cache: &mut Option<(super::hints::GPowMap, F64)>, x: F64, nbits: u32) -> u128 {
            const LOG_BABY: u32 = 17;
            let (baby, giant) = cache.get_or_insert_with(|| {
                let mut table = super::hints::GPowMap::default();
                let mut p = F64::ONE;
                for j in 0..(1u32 << LOG_BABY) {
                    table.insert(p, j);
                    p = mul_by_g(p);
                }
                (table, p.inv()) // p = g^(2^17); its inverse is the giant step
            });
            let mut y = x;
            let max_giant = if nbits > LOG_BABY {
                1u64 << (nbits - LOG_BABY)
            } else {
                1
            };
            for a in 0..max_giant {
                if let Some(&j) = baby.get(&y) {
                    return (a as u128) << LOG_BABY | j as u128;
                }
                y *= *giant;
            }
            panic!("hint_decompose_bits_exponent: value is not g^n for n < 2^{nbits}")
        }

        // Read the running access count and advance it by ×g (the free increment).
        // ×g is ×x, i.e. `mul_by_g` — a shift+fold, not a PMULL; this runs on every
        // memory access (several million per run), so the cheap form matters.
        fn bump_access_count(mem: &mut Vec<F192>, written: &mut Vec<bool>, mem_count: &mut Vec<F64>, cell: u32) -> F64 {
            ensure(mem, written, mem_count, cell as usize);
            let cell_idx = cell as usize;
            let count = mem_count[cell_idx];
            mem_count[cell_idx] = mul_by_g(count);
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
                                    let sz = as_addr(get(&mem, &written, fp + size))
                                        .expect("HeapBuf size is not a K-valued g-power");
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
                                mem[cell as usize] = F192::from(gpow[base as usize]);
                                written[cell as usize] = true;
                            }
                        }
                        RHint::Print { label, cell } => {
                            let c = fp + cell;
                            ensure(&mut mem, &mut written, &mut mem_count, c as usize);
                            if written[c as usize] {
                                let v = mem[c as usize];
                                // Small integers and small g-powers overlap (8 = x^3
                                // = g^3): show every reading that applies. Only a
                                // K-valued word (hi lane 0) can be a g-power.
                                let k = as_addr(v).and_then(|lo| gmap.get(&lo).copied());
                                let small = v.c2 == 0 && v.c1 == 0 && v.c0 < 1 << 32;
                                match (k, small) {
                                    (Some(k), true) => eprintln!("[print] {label} = {} (g^{k})", v.c0),
                                    (Some(k), false) => eprintln!("[print] {label} = g^{k}"),
                                    (None, true) => eprintln!("[print] {label} = {}", v.c0),
                                    (None, false) => {
                                        eprintln!("[print] {label} = {:#x}:{:#x}:{:#x}", v.c2, v.c1, v.c0)
                                    }
                                }
                            } else {
                                eprintln!("[print] {label} = <unwritten>");
                            }
                        }
                        RHint::WitnessStack { name, base, len } => {
                            let vals = pop_witness(&mut wit_pos, name, *len);
                            for (k, v) in vals.into_iter().enumerate() {
                                put(&mut mem, &mut written, &mut mem_count, fp + base + k as u32, v);
                            }
                        }
                        RHint::WitnessHeap { name, ptr, lo, len } => {
                            let p = as_addr(get(&mem, &written, fp + ptr))
                                .expect("hint_witness heap pointer is not a K-valued g-power");
                            let b = *gmap
                                .get(&p)
                                .unwrap_or_else(|| panic!("hint_witness heap pointer is not a g-power"));
                            let vals = pop_witness(&mut wit_pos, name, *len);
                            for (k, v) in vals.into_iter().enumerate() {
                                put(&mut mem, &mut written, &mut mem_count, b + lo + k as u32, v);
                            }
                        }
                        RHint::Log2Ceil {
                            bits_ptr,
                            dst,
                            nbits,
                            floor,
                        } => {
                            let p = as_addr(get(&mem, &written, fp + bits_ptr))
                                .expect("log2_ceil bits pointer is not a K-valued g-power");
                            let b = *gmap
                                .get(&p)
                                .unwrap_or_else(|| panic!("log2_ceil bits pointer is not a g-power"));
                            let mut word: u128 = 0;
                            for j in 0..*nbits {
                                if !get(&mem, &written, b + j).is_zero() {
                                    word |= 1u128 << j;
                                }
                            }
                            let cl = if word <= 1 {
                                0
                            } else {
                                u128::BITS - (word - 1).leading_zeros()
                            };
                            let mu = cl.max(*floor);
                            put(
                                &mut mem,
                                &mut written,
                                &mut mem_count,
                                fp + dst,
                                F192::from(primitives::field::g_pow(mu as usize)),
                            );
                        }
                        RHint::BitDecompose { value, bits_ptr, nbits } => {
                            assert!(*nbits <= 192, "a machine word has 192 bits");
                            let v = get(&mem, &written, fp + value);
                            let limbs = [v.c0, v.c1, v.c2];
                            let bp = as_addr(get(&mem, &written, fp + bits_ptr))
                                .expect("decompose bits pointer is not a K-valued g-power");
                            let bb = *gmap
                                .get(&bp)
                                .unwrap_or_else(|| panic!("decompose bits pointer is not a g-power"));
                            for j in 0..*nbits {
                                let bit = (limbs[j as usize / 64] >> (j % 64)) & 1;
                                put(&mut mem, &mut written, &mut mem_count, bb + j, F192::new(bit, 0, 0));
                            }
                        }
                        RHint::BitDecomposeExp { value, bits_ptr, nbits } => {
                            let x = as_addr(get(&mem, &written, fp + value))
                                .expect("hint_decompose_bits_exponent value is not a K-valued g-power");
                            let n = bounded_dlog(&mut dlog_cache, x, *nbits);
                            let bp = as_addr(get(&mem, &written, fp + bits_ptr))
                                .expect("hint_decompose_bits_exponent bits pointer is not a K-valued g-power");
                            let bb = *gmap.get(&bp).unwrap_or_else(|| {
                                panic!("hint_decompose_bits_exponent bits pointer is not a g-power")
                            });
                            for j in 0..*nbits {
                                let bit = ((n >> j) & 1) as u64;
                                put(&mut mem, &mut written, &mut mem_count, bb + j, F192::new(bit, 0, 0));
                            }
                        }
                    }
                }
            }
            // Cover the g-powers this step may index (g²·pc return target, g^fp).
            grow_gpow(&mut gpow, &mut gmap, (pc as usize + 2).max(fp as usize));

            let bytecode_read = {
                let v = bytecode_count[pc as usize];
                bytecode_count[pc as usize] = mul_by_g(v);
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
                    let p_addr = as_addr(p).unwrap_or_else(|| {
                        panic!(
                            "DEREF pointer is not a K-valued g-power at pc {pc}: {:x}:{:x}",
                            p.c1, p.c0
                        )
                    });
                    let base = match gmap.get(&p_addr) {
                        Some(&b) => b,
                        None => {
                            // Not indexed yet: grow the g-power index to the minimum
                            // memory size — range-check touches point anywhere below
                            // their bound (≤ 2^MIN_LOG_MEM), not just at allocated
                            // frames/buffers. A value still absent is no valid
                            // pointer: a wild deref, or a failed range check
                            // (`assert log _ < _`) surfacing honestly.
                            grow_gpow(&mut gpow, &mut gmap, 1 << MIN_LOG_MEM);
                            *gmap.get(&p_addr).unwrap_or_else(|| {
                                panic!(
                                    "DEREF pointer is not a small g-power at pc {pc}: a wild \
                                     pointer, or a failed range check \
                                     (value 0x{:016x})",
                                    p_addr.0
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
                            let v = F192::from(gpow[pc as usize + 2]);
                            put(&mut mem, &mut written, &mut mem_count, a2 as u32, v);
                        }
                        DerefMode::Fp => {
                            let v = F192::from(gpow[fp as usize]);
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
                    // per-jump here runs a Fermat inverse on every taken branch
                    // (~2^17 of them), which dominated `execute`. Placeholder 0 now;
                    // batch-filled below (bit-identical to `c.inv()`).
                    let b = if c.is_zero() { F64::ZERO } else { F64::ONE };
                    let w = F192::ZERO;
                    let rc = bump_access_count(&mut mem, &mut written, &mut mem_count, ac);
                    let rd = bump_access_count(&mut mem, &mut written, &mut mem_count, ad);
                    let rf = bump_access_count(&mut mem, &mut written, &mut mem_count, af);
                    let taken = !c.is_zero();
                    let (npc, nfp) = if taken {
                        let dpc = as_addr(d).expect("JUMP target is not a K-valued g-power");
                        let ffp = as_addr(f).expect("JUMP fp is not a K-valued g-power");
                        (dpc, ffp)
                    } else {
                        (mul_by_g(gpow[pc as usize]), gpow[fp as usize])
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
                        pc = *gmap.get(&npc).expect("JUMP target not a g-power");
                        fp = *gmap.get(&nfp).expect("JUMP fp not a g-power");
                    } else {
                        pc += 1;
                    }
                }
                Op::Sha256 { ins, out, packing } => {
                    // Four independently-addressed 128-bit input chunks, each a
                    // single cell; the output spans two consecutive cells (ac, ac+1).
                    let (aa0, aa1, ab0, ab1) = (fp + ins[0], fp + ins[1], fp + ins[2], fp + ins[3]);
                    let ac = fp + out;
                    let words = [aa0, aa1, ab0, ab1].map(|a| get(&mem, &written, a));
                    let (va, vb) = match packing {
                        Sha256Packing::Bytes128 => {
                            assert!(
                                words.iter().all(|w| w.c2 == 0),
                                "SHA256 input cell must be a 128-bit embedding"
                            );
                            (
                                [F64(words[0].c0), F64(words[0].c1), F64(words[1].c0), F64(words[1].c1)],
                                [F64(words[2].c0), F64(words[2].c1), F64(words[3].c0), F64(words[3].c1)],
                            )
                        }
                        Sha256Packing::Transcript192 => {
                            assert_eq!(
                                (words[1].c1, words[1].c2),
                                (0, 0),
                                "transcript state tail must be K-valued"
                            );
                            assert_eq!((words[3].c1, words[3].c2), (0, 0), "transcript tag must be K-valued");
                            (
                                [F64(words[0].c0), F64(words[0].c1), F64(words[0].c2), F64(words[1].c0)],
                                [F64(words[2].c0), F64(words[2].c1), F64(words[2].c2), F64(words[3].c0)],
                            )
                        }
                    };
                    // Compress the 64 input bytes to the 32-byte digest, then write
                    // it to c's two cells. No table constraint covers the digest
                    // (the relation is proven by flock, §sha256_flock); the
                    // interpreter still computes the definite digest so the output
                    // cells are consistent for any later read.
                    let vc = sha256_compress(va, vb);
                    let outputs = match packing {
                        Sha256Packing::Bytes128 => [F192::new(vc[0].0, vc[1].0, 0), F192::new(vc[2].0, vc[3].0, 0)],
                        Sha256Packing::Transcript192 => {
                            [F192::new(vc[0].0, vc[1].0, vc[2].0), F192::new(vc[3].0, 0, 0)]
                        }
                    };
                    put(&mut mem, &mut written, &mut mem_count, ac, outputs[0]);
                    put(&mut mem, &mut written, &mut mem_count, ac + 1, outputs[1]);
                    let ra = [
                        bump_access_count(&mut mem, &mut written, &mut mem_count, aa0),
                        bump_access_count(&mut mem, &mut written, &mut mem_count, aa1),
                    ];
                    let rb = [
                        bump_access_count(&mut mem, &mut written, &mut mem_count, ab0),
                        bump_access_count(&mut mem, &mut written, &mut mem_count, ab1),
                    ];
                    let rc = [
                        bump_access_count(&mut mem, &mut written, &mut mem_count, ac),
                        bump_access_count(&mut mem, &mut written, &mut mem_count, ac + 1),
                    ];
                    sha256.push(Brow {
                        pc,
                        fp,
                        aa0,
                        aa1,
                        ab0,
                        ab1,
                        ac,
                        va,
                        vb,
                        vc,
                        words: [words[0], words[1], words[2], words[3], outputs[0], outputs[1]],
                        packing,
                        ra,
                        rb,
                        rc,
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
            put(&mut mem, &mut written, &mut mem_count, a2 as u32, F192::ZERO);
            put(&mut mem, &mut written, &mut mem_count, a3, F192::ZERO);
        }

        // Fill the deferred JUMP inverse hints `w = c⁻¹` (the is-nonzero witness)
        // in ONE batched Montgomery inversion: a single field inverse plus ~2·#jumps
        // multiplies, instead of a full inverse per taken branch. `w` is only
        // recorded into the trace, so this reproduces exactly the per-jump `c.inv()`
        // (0 for the c = 0 rows). `prefix[i]` is the running product of the nonzero
        // conditions before row `i`; `acc` ends as the product of all nonzero
        // conditions (nonzero, so invertible).
        {
            let mut acc = F192::ONE;
            let mut prefix: Vec<F192> = Vec::with_capacity(jump.len());
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
        mem.resize(cells, F192::ZERO);
        mem_count.resize(cells, F64::ONE);
        let trace = Trace {
            xor,
            mul,
            set,
            deref,
            jump,
            sha256,
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
