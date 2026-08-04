//! The write-once execution interpreter: run the compiled program to produce
//! the final memory image and the per-opcode [`Trace`].

use std::collections::HashMap;

use super::*;
use primitives::{
    field::{F64, F192, mul_by_g},
    pretty_f64, pretty_integer,
};

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
        use super::hints::{GPow, RHint};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, seeded for the program counters and
        // return targets and grown on demand past that.
        let mut g = GPow::new(self.prog.len() + 2);

        // Dense write-once data memory (read path stays a vector for speed), the
        // per-cell access count (g^{count}, default g^0 = 1), and a written mask.
        let n0 = self.main_frame.max(2) as usize;
        let mut m = Mem {
            cells: vec![F192::ZERO; n0],
            written: vec![false; n0],
            count: vec![F64::ONE; n0],
            dbg_pc: 0,
            dbg_hint: None,
        };
        // Seed the public input into m[0], m[1] (addresses g^0, g^1, §e2e-pi).
        m.cells[0] = public_input[0];
        m.cells[1] = public_input[1];
        m.written[0] = true;
        m.written[1] = true;

        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; self.prog.len()];

        let mut next_free = self.main_frame;
        let (mut pc, mut fp) = (self.pc0, self.fp0);
        let mut steps = 0usize;
        // Per-pc hint index. `self.hints` is keyed by pc, so probing it each step
        // costs a hash of the counter for what is almost always a miss; the
        // program has one bytecode slot per pc, so flatten the map into a dense
        // table: 0 = no hints, otherwise the 1-based index into `hint_lists`.
        let mut hint_at = vec![0u32; self.prog.len()];
        let mut hint_lists: Vec<&[RHint]> = Vec::with_capacity(self.hints.len());
        for (&hpc, hs) in &self.hints {
            hint_lists.push(hs.as_slice());
            hint_at[hpc as usize] = hint_lists.len() as u32;
        }
        // `DBG_PROF=1`: per-pc step counts, printed as a per-function cycle
        // profile after the run (needs `fn_ranges`, i.e. a compiled program).
        let mut prof: Option<Vec<u64>> = std::env::var("DBG_PROF").is_ok().then(|| vec![0u64; self.prog.len()]);

        // Per-stream cursor into the named witness data (`hint_witness` pops
        // sequentially).
        let mut wit_pos: HashMap<String, usize> = HashMap::new();
        // Baby-step table for `hint_decompose_bits_exponent`, built on first use.
        let mut dlog_cache: Option<(GPow, F64)> = None;

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let mut xor: Vec<Xrow> = Vec::new();
        let mut mul: Vec<Xrow> = Vec::new();
        let mut set: Vec<Srow> = Vec::new();
        let mut deref: Vec<Drow> = Vec::new();
        let mut jump: Vec<Jrow> = Vec::new();
        let mut blake3: Vec<Brow> = Vec::new();
        let mut pack64x2: Vec<Xrow> = Vec::new();

        // `DEREF Cell` touches whose two sides are both still unwritten (the
        // range-check gadget's unconstrained target cells), as `(a2, a3)`,
        // resolved after the run: write-once memory is order-independent, so the
        // value can be decided at the end (leanVM's end-of-execution deref-hint
        // resolution).
        let mut deferred: Vec<(usize, u32)> = Vec::new();

        // The three dense per-cell vectors, kept in lockstep. Every method is
        // `#[inline(always)]`: they sit in the interpreter's hot opcode loop.
        struct Mem {
            cells: Vec<F192>,
            written: Vec<bool>,
            count: Vec<F64>,
            /// The pc of the currently executing instruction, and the name of the
            /// computed-advice hint if the write comes from one, so the
            /// write-once panic can report where the conflict happened. Plain
            /// fields rather than thread-locals: this is written on every step,
            /// and a thread-local costs a lazy-init check each time.
            dbg_pc: u32,
            dbg_hint: Option<&'static str>,
        }
        impl Mem {
            // Grow the dense vectors so `idx` is in range. All accessed cells
            // satisfy cell < next_free after their frame's allocation, so this
            // only ever extends.
            #[inline(always)]
            fn ensure(&mut self, idx: usize) {
                if idx >= self.cells.len() {
                    let n = idx + 1;
                    self.cells.resize(n, F192::ZERO);
                    self.written.resize(n, false);
                    self.count.resize(n, F64::ONE);
                }
            }
            // Read a cell; an unwritten cell reads as ZERO.
            #[inline(always)]
            fn get(&self, cell: u32) -> F192 {
                let c = cell as usize;
                if c < self.written.len() && self.written[c] {
                    self.cells[c]
                } else {
                    F192::ZERO
                }
            }
            // Write-once store: writing a different value to an already-set cell panics.
            #[inline(always)]
            fn put(&mut self, cell: u32, v: F192) {
                self.ensure(cell as usize);
                let c = cell as usize;
                if self.written[c] {
                    assert!(
                        self.cells[c] == v,
                        "write-once conflict at cell {cell} (pc {}, hint {:?}): had {:x}:{:x}:{:x}, new {:x}:{:x}:{:x}",
                        self.dbg_pc,
                        self.dbg_hint,
                        self.cells[c].c2,
                        self.cells[c].c1,
                        self.cells[c].c0,
                        v.c2,
                        v.c1,
                        v.c0
                    );
                } else {
                    self.cells[c] = v;
                    self.written[c] = true;
                }
            }
            // Read the running access count and advance it by ×g (the free increment).
            // ×g is ×x, i.e. `mul_by_g`, a shift+fold rather than a PMULL; this runs on every
            // memory access (several million per run), so the cheap form matters.
            #[inline(always)]
            fn bump_access_count(&mut self, cell: u32) -> F64 {
                self.ensure(cell as usize);
                let cell_idx = cell as usize;
                let count = self.count[cell_idx];
                self.count[cell_idx] = mul_by_g(count);
                count
            }
        }
        // Bounded discrete log for `hint_decompose_bits_exponent`: find n < 2^nbits
        // with g^n = x, by baby-step giant-step (baby table g^j for j < 2^17,
        // built once per run; giant step ×g^(-2^17)). Prover-side only: the
        // guest re-verifies the hinted bits in-circuit.
        fn bounded_dlog(cache: &mut Option<(GPow, F64)>, x: F64, nbits: u32) -> u128 {
            const LOG_BABY: u32 = 17;
            let (baby, giant) = cache.get_or_insert_with(|| {
                let baby = GPow::new((1usize << LOG_BABY) - 1);
                // g^(2^17), one past the table; its inverse is the giant step.
                let giant = mul_by_g(baby.pow((1usize << LOG_BABY) - 1)).inv();
                (baby, giant)
            });
            let mut y = x;
            let max_giant = if nbits > LOG_BABY {
                1u64 << (nbits - LOG_BABY)
            } else {
                1
            };
            for a in 0..max_giant {
                if let Some(j) = baby.log(y) {
                    return (a as u128) << LOG_BABY | j as u128;
                }
                y *= *giant;
            }
            panic!("hint_decompose_bits_exponent: value is not g^n for n < 2^{nbits}")
        }

        while pc != ending_pc {
            assert!(steps < 100_000_000, "step limit exceeded (runaway recursion?)");
            m.dbg_pc = pc;
            if let Some(p) = prof.as_mut() {
                p[pc as usize] += 1;
            }

            // Apply the hints scheduled before this instruction.
            if hint_at[pc as usize] != 0 {
                let hs = hint_lists[hint_at[pc as usize] as usize - 1];
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
                    m.dbg_hint = Some(match h {
                        RHint::Alloc { .. } => "Alloc",
                        RHint::AllocDyn { .. } => "AllocDyn",
                        RHint::WitnessStack { .. } => "WitnessStack",
                        RHint::WitnessHeap { .. } => "WitnessHeap",
                        RHint::Log2Ceil { .. } => "Log2Ceil",
                        RHint::BitDecompose { .. } => "BitDecompose",
                        RHint::BitDecomposeExp { .. } => "BitDecomposeExp",
                        RHint::FieldLimbs { .. } => "FieldLimbs",
                        RHint::Print { .. } => "Print",
                    });
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
                                    let sz = as_addr(m.get(fp + size)).expect("HeapBuf size is not a K-valued g-power");
                                    let cells = g.log(sz).unwrap_or_else(|| {
                                        g.grow_to(1 << 20);
                                        g.log(sz)
                                            .unwrap_or_else(|| panic!("HeapBuf size is not a g-power below 2^20 cells"))
                                    });
                                    (ptr, cells)
                                }
                                _ => unreachable!(),
                            };
                            let cell = fp + ptr;
                            m.ensure(cell as usize);
                            if !m.written[cell as usize] {
                                let base = next_free;
                                next_free += size;
                                g.grow_to((base + size) as usize);
                                // The base is about to become a pointer in memory.
                                g.note(base as usize);
                                m.ensure(next_free as usize);
                                m.cells[cell as usize] = F192::from(g.pow(base as usize));
                                m.written[cell as usize] = true;
                            }
                        }
                        RHint::Print { label, cell } => {
                            let c = fp + cell;
                            m.ensure(c as usize);
                            if m.written[c as usize] {
                                let v = m.cells[c as usize];
                                // Small integers and small g-powers overlap (8 = x^3
                                // = g^3): show every reading that applies. Only a
                                // K-valued word (extension limbs 0) can be a g-power.
                                let k = as_addr(v).and_then(|lo| g.log(lo));
                                let small = v.c2 == 0 && v.c1 == 0 && v.c0 < 1 << 32;
                                match (k, small) {
                                    (Some(k), true) => eprintln!(
                                        "[print] {label} = {} (g^{})",
                                        pretty_integer(v.c0),
                                        pretty_integer(k)
                                    ),
                                    (Some(k), false) => {
                                        eprintln!("[print] {label} = g^{}", pretty_integer(k))
                                    }
                                    (None, true) => {
                                        eprintln!("[print] {label} = {}", pretty_integer(v.c0))
                                    }
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
                                m.put(fp + base + k as u32, v);
                            }
                        }
                        RHint::WitnessHeap { name, ptr, lo, len } => {
                            let p =
                                as_addr(m.get(fp + ptr)).expect("hint_witness heap pointer is not a K-valued g-power");
                            let b = g
                                .log(p)
                                .unwrap_or_else(|| panic!("hint_witness heap pointer is not a g-power"));
                            let vals = pop_witness(&mut wit_pos, name, *len);
                            for (k, v) in vals.into_iter().enumerate() {
                                m.put(b + lo + k as u32, v);
                            }
                        }
                        RHint::Log2Ceil {
                            bits_ptr,
                            dst,
                            nbits,
                            floor,
                        } => {
                            let p = as_addr(m.get(fp + bits_ptr))
                                .expect("log2_ceil bits pointer is not a K-valued g-power");
                            let b = g
                                .log(p)
                                .unwrap_or_else(|| panic!("log2_ceil bits pointer is not a g-power"));
                            let mut word: u128 = 0;
                            for j in 0..*nbits {
                                if !m.get(b + j).is_zero() {
                                    word |= 1u128 << j;
                                }
                            }
                            let cl = if word <= 1 {
                                0
                            } else {
                                u128::BITS - (word - 1).leading_zeros()
                            };
                            let mu = cl.max(*floor);
                            m.put(fp + dst, F192::from(primitives::field::g_pow(mu as usize)));
                        }
                        RHint::BitDecompose { value, bits_ptr, nbits } => {
                            assert!(*nbits <= 192, "a machine word has 192 bits");
                            let v = m.get(fp + value);
                            let limbs = [v.c0, v.c1, v.c2];
                            let bp = as_addr(m.get(fp + bits_ptr))
                                .expect("decompose bits pointer is not a K-valued g-power");
                            let bb = g
                                .log(bp)
                                .unwrap_or_else(|| panic!("decompose bits pointer is not a g-power"));
                            for j in 0..*nbits {
                                let bit = (limbs[j as usize / 64] >> (j % 64)) & 1;
                                m.put(bb + j, F192::new(bit, 0, 0));
                            }
                        }
                        RHint::BitDecomposeExp { value, bits_ptr, nbits } => {
                            let x = as_addr(m.get(fp + value))
                                .expect("hint_decompose_bits_exponent value is not a K-valued g-power");
                            let n = bounded_dlog(&mut dlog_cache, x, *nbits);
                            let bp = as_addr(m.get(fp + bits_ptr))
                                .expect("hint_decompose_bits_exponent bits pointer is not a K-valued g-power");
                            let bb = g.log(bp).unwrap_or_else(|| {
                                panic!("hint_decompose_bits_exponent bits pointer is not a g-power")
                            });
                            for j in 0..*nbits {
                                let bit = ((n >> j) & 1) as u64;
                                m.put(bb + j, F192::new(bit, 0, 0));
                            }
                        }
                        RHint::FieldLimbs { value, base, len } => {
                            assert!((1..=3).contains(len), "an F192 value has three K limbs");
                            let v = m.get(fp + value);
                            let limbs = [v.c0, v.c1, v.c2];
                            for j in 0..*len {
                                m.put(fp + base + j, F192::new(limbs[j as usize], 0, 0));
                            }
                        }
                    }
                    m.dbg_hint = None;
                }
            }
            // Cover the g-powers this step may index (g²·pc return target, g^fp).
            // Guarded so the steady state is a length compare, not a call.
            let need = (pc as usize + 2).max(fp as usize);
            if g.covered() <= need {
                g.grow_to(need);
            }

            let bytecode_read = {
                let v = bytecode_count[pc as usize];
                bytecode_count[pc as usize] = mul_by_g(v);
                v
            };

            // Loaded once: the shared Xor/Mul arm needs the discriminant again,
            // and `Op` is wide enough that re-reading it costs a second load.
            let op = self.prog[pc as usize];
            match op {
                Op::Xor { a, b, c } | Op::Mul { a, b, c } => {
                    let is_xor = matches!(op, Op::Xor { .. });
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    // The row is the equality `m[c] = m[a] op m[b]` over write-once
                    // memory. Normally the operands are known and the result is
                    // computed forward; with the result already m.written and exactly
                    // one operand unwritten, the runner back-solves the operand
                    // (leanVM's ADD deduction, multiplicatively: this is what
                    // produces the range-check complement `y = g^{k-1}·x^{-1}` from
                    // `MUL x·y = g^{k-1}`, with no dedicated hint).
                    let is_set = |w: &[bool], cell: u32| (cell as usize) < w.len() && w[cell as usize];
                    if is_set(&m.written, ac) {
                        let (ha, hb) = (is_set(&m.written, aa), is_set(&m.written, ab));
                        if ha ^ hb {
                            let vc = m.get(ac);
                            let vk = m.get(if ha { aa } else { ab });
                            let v = if is_xor {
                                vc + vk
                            } else {
                                assert!(!vk.is_zero(), "cannot back-solve MUL through a zero operand");
                                vc * vk.inv()
                            };
                            m.put(if ha { ab } else { aa }, v);
                        }
                    }
                    let va = m.get(aa);
                    let vb = m.get(ab);
                    let vc = if is_xor { va + vb } else { va * vb };
                    m.put(ac, vc);
                    let ra = m.bump_access_count(aa);
                    let rb = m.bump_access_count(ab);
                    let rc = m.bump_access_count(ac);
                    let row = Xrow {
                        pc,
                        fp,
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
                    m.put(a, k);
                    let r = m.bump_access_count(a);
                    set.push(Srow {
                        pc,
                        fp,
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
                    let p = m.get(a1);
                    let p_addr = as_addr(p).unwrap_or_else(|| {
                        panic!(
                            "DEREF pointer is not a K-valued g-power at pc {pc}: {:x}:{:x}",
                            p.c1, p.c0
                        )
                    });
                    let base = match g.log(p_addr) {
                        Some(b) => b,
                        None => {
                            // Not indexed yet: grow the g-power index to the minimum
                            // memory size, since range-check touches point anywhere below
                            // their bound (≤ 2^MIN_LOG_MEM), not just at allocated
                            // frames/buffers. A value still absent is no valid
                            // pointer: a wild deref, or a failed range check
                            // (`assert log _ < _`) surfacing honestly.
                            g.grow_to(1 << MIN_LOG_MEM);
                            g.log(p_addr).unwrap_or_else(|| {
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
                            m.ensure(a2);
                            let has2 = m.written[a2];
                            let has3 = (a3 as usize) < m.written.len() && m.written[a3 as usize];
                            match (has2, has3) {
                                (true, true) => {
                                    assert!(m.cells[a2] == m.get(a3), "DEREF mismatch")
                                }
                                (true, false) => {
                                    let v = m.cells[a2];
                                    m.put(a3, v);
                                }
                                (false, true) => {
                                    let v = m.get(a3);
                                    m.put(a2 as u32, v);
                                }
                                (false, false) => {
                                    // Both sides still unwritten: a range-check
                                    // touch (only the address validity of `a2`
                                    // matters, not its value). Defer the equality
                                    // to after the run, once `m[a2]`'s final value
                                    // (a later program write, or ZERO) is known;
                                    // the row itself needs no patch, since the
                                    // fill reads both values out of that image.
                                    deferred.push((a2, a3));
                                }
                            }
                        }
                        DerefMode::Pc => {
                            // The return target and the frame base are stored as
                            // addresses, and JUMP reads them back.
                            g.note(pc as usize + 2);
                            let v = F192::from(g.pow(pc as usize + 2));
                            m.put(a2 as u32, v);
                        }
                        DerefMode::Fp => {
                            g.note(fp as usize);
                            let v = F192::from(g.pow(fp as usize));
                            m.put(a2 as u32, v);
                        }
                    }
                    let r1 = m.bump_access_count(a1);
                    let r2 = m.bump_access_count(a2 as u32);
                    let r3 = m.bump_access_count(a3);
                    deref.push(Drow {
                        pc,
                        fp,
                        a2: a2 as u32,
                        r1,
                        r2,
                        r3,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Jump { oc, od, of } => {
                    let (ac, ad, af) = (fp + oc, fp + od, fp + of);
                    let c = m.get(ac);
                    let d = m.get(ad);
                    let f = m.get(af);
                    // The is-nonzero witness `w = c⁻¹` is never used for control
                    // flow, only recorded as a witness column, so it is not
                    // computed here at all: `JumpTable::fill` batch-inverts every
                    // row's condition at once (§the trace rows in `cpu::trace`).
                    let rc = m.bump_access_count(ac);
                    let rd = m.bump_access_count(ad);
                    let rf = m.bump_access_count(af);
                    let taken = !c.is_zero();
                    jump.push(Jrow {
                        pc,
                        fp,
                        rc,
                        rd,
                        rf,
                        bytecode_read,
                    });
                    if taken {
                        let dpc = as_addr(d).expect("JUMP target is not a K-valued g-power");
                        let ffp = as_addr(f).expect("JUMP fp is not a K-valued g-power");
                        pc = g.log(dpc).expect("JUMP target not a g-power");
                        fp = g.log(ffp).expect("JUMP fp not a g-power");
                    } else {
                        pc += 1;
                    }
                }
                Op::Pack64x2 { a, b, c } => {
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    let va = m.get(aa);
                    let vb = m.get(ab);
                    assert_eq!((va.c1, va.c2), (0, 0), "PACK64X2 first input must be K-valued");
                    assert_eq!((vb.c1, vb.c2), (0, 0), "PACK64X2 second input must be K-valued");
                    m.put(ac, F192::new(va.c0, vb.c0, 0));
                    let ra = m.bump_access_count(aa);
                    let rb = m.bump_access_count(ab);
                    let rc = m.bump_access_count(ac);
                    pack64x2.push(Xrow {
                        pc,
                        fp,
                        ra,
                        rb,
                        rc,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Blake3 { ins, cv, out, metadata } => {
                    // Four independently-addressed 128-bit message chunks, each a
                    // single cell; the chaining value and the output each span two
                    // consecutive cells.
                    let (aa0, aa1, ab0, ab1) = (fp + ins[0], fp + ins[1], fp + ins[2], fp + ins[3]);
                    let acv = fp + cv;
                    let ac = fp + out;
                    let words = [aa0, aa1, ab0, ab1, acv, acv + 1].map(|a| m.get(a));
                    assert!(
                        words.iter().all(|w| w.c2 == 0),
                        "BLAKE3 input cell must be a canonical 128-bit embedding"
                    );
                    let va = [F64(words[0].c0), F64(words[0].c1), F64(words[1].c0), F64(words[1].c1)];
                    let vb = [F64(words[2].c0), F64(words[2].c1), F64(words[3].c0), F64(words[3].c1)];
                    let vcv = [F64(words[4].c0), F64(words[4].c1), F64(words[5].c0), F64(words[5].c1)];
                    // Compress the 64 message bytes to the 32-byte result, then
                    // write it to c's two cells. No table constraint covers the
                    // digest (the relation is proven by flock, §blake3_flock); the
                    // interpreter still computes the definite digest so the output
                    // cells are consistent for any later read.
                    let vc = blake3_compress(va, vb, vcv, metadata);
                    let outputs = [F192::new(vc[0].0, vc[1].0, 0), F192::new(vc[2].0, vc[3].0, 0)];
                    m.put(ac, outputs[0]);
                    m.put(ac + 1, outputs[1]);
                    let ra = [m.bump_access_count(aa0), m.bump_access_count(aa1)];
                    let rb = [m.bump_access_count(ab0), m.bump_access_count(ab1)];
                    let rcv = [m.bump_access_count(acv), m.bump_access_count(acv + 1)];
                    let rc = [m.bump_access_count(ac), m.bump_access_count(ac + 1)];
                    blake3.push(Brow {
                        pc,
                        fp,
                        ra,
                        rb,
                        rcv,
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
            // `DBG_PROF_DUMP=path`: also write the raw per-pc counts plus the
            // function table, so an offline pass can attribute the straight-line
            // cycles of one big function to its source regions (the call sites of
            // the lowered `for` helpers are the landmarks).
            if let Ok(path) = std::env::var("DBG_PROF_DUMP") {
                let mut out = format!("# steps {steps}\n");
                for (name, entry, len) in &self.fn_ranges {
                    out += &format!("F {name} {entry} {len}\n");
                }
                for (pc, c) in p.iter().enumerate() {
                    if *c > 0 {
                        out += &format!("{pc} {c}\n");
                    }
                }
                let path = if std::path::Path::new(&path).exists() {
                    format!("{path}.{}", std::process::id())
                } else {
                    path
                };
                std::fs::write(&path, out).expect("write DBG_PROF_DUMP");
                eprintln!("== DBG_PROF: per-pc counts m.written to {path}");
            }
            eprintln!("== DBG_PROF: cycles by function ({} total) ==", pretty_integer(steps));
            for (name, c) in rows.iter().filter(|(_, c)| *c > 0) {
                eprintln!(
                    "  {:>13}  {:>7}%  {name}",
                    pretty_integer(c),
                    pretty_f64(100.0 * *c as f64 / steps as f64)
                );
            }
        }

        // Resolve the deferred DEREF touches: a fixpoint, so a touch whose cell is
        // filled by another deferred entry picks up that value; cells nobody ever
        // writes are fixed to ZERO. The rows need no patch: the fill reads both
        // sides out of the finished image, and their access counts were already
        // bumped during the walk (the memory bus is order-independent, it only
        // needs every access to agree on the value).
        while {
            let before = deferred.len();
            deferred.retain(|&(a2, a3)| {
                if m.written[a2] {
                    let v = m.cells[a2];
                    m.put(a3, v);
                    false
                } else {
                    true
                }
            });
            deferred.len() < before
        } {}
        for (a2, a3) in deferred {
            // Never written: the cells are genuinely unconstrained; fix them to ZERO.
            m.put(a2 as u32, F192::ZERO);
            m.put(a3, F192::ZERO);
        }

        // Pad memory to a power of two (the boundary tables read a dense image),
        // at least 2^MIN_LOG_MEM cells (doc §Memory).
        let mem_used = m.cells.len();
        let cells = m.cells.len().next_power_of_two().max(1 << MIN_LOG_MEM);
        assert!(cells <= 1 << MAX_LOG_MEM, "data memory exceeds 2^{MAX_LOG_MEM} cells");
        m.cells.resize(cells, F192::ZERO);
        m.count.resize(cells, F64::ONE);
        let trace = Trace {
            xor,
            mul,
            set,
            deref,
            jump,
            blake3,
            pack64x2,
            mem_count: m.count,
            bytecode_count,
        };
        Execution {
            mem: m.cells,
            cycles: steps,
            mem_used,
            trace,
        }
    }
}
