//! The write-once execution interpreter: run the compiled program to produce
//! the final memory image and the per-opcode [`Trace`].

use std::collections::HashMap;

use super::*;
use primitives::{
    field::{F64, F192, mul_by_g},
    pretty_f64, pretty_integer,
};

pub struct Execution {
    pub mem: Vec<F64>,   // data memory after the run, write-once (size cells, power of two)
    pub cycles: usize,   // number of instructions the run executed (trace length)
    pub mem_used: usize, // cells actually touched, before the power-of-two pad of `mem`
    /// Rows per table before the fill blocks ran: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    pub(crate) trace: Trace, // rows + final access-count columns, emitted in the same walk
}

/// A memory word interpreted as a K-valued address: valid only when both
/// extension limbs are zero (every g-power is a K-element).
fn as_addr(v: F64) -> Option<F64> {
    Some(v)
}

impl Program {
    /// Run the program in write-once *fill* mode to produce its [`Execution`]:
    /// the final memory image and the step count. The public input seeds the
    /// first four memory cells `m[0]..m[3]` (§sec:e2e-pi). Compilation yields the
    /// `Program`; executing it (here) and proving it are separate later phases.
    pub fn execute(&self, public_input: [F64; 4]) -> Execution {
        // One interpretation of the program, then the fill. The blocks that bring every
        // table to a power of two are cycles no program code enters (`cpu::filler`), so
        // they run after the chain has halted, by which point the program's own row
        // counts are final; a traversal costs exactly its block's size plus its closing
        // jump, so the solve is exact and no second run is needed to correct it.
        use super::hints::{GPow, RHint};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, seeded for the program counters and
        // return targets and grown on demand past that.
        let mut g = GPow::new(self.prog.len() + 2);

        // Dense write-once data memory (read path stays a vector for speed), the
        // per-cell access count (g^{count}, default g^0 = 1), and a written mask.
        let n0 = self.main_frame.max(4) as usize;
        let mut m = Mem {
            cells: vec![F64::ZERO; n0],
            written: vec![false; n0],
            count: vec![F64::ONE; n0],
            dbg_pc: 0,
            dbg_hint: None,
        };
        // Seed the four public words into m[0]..m[3] (§sec:e2e-pi).
        m.cells[..4].copy_from_slice(&public_input);
        m.written[..4].fill(true);

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

        // Rows per table before the fill runs, captured when the chain halts.
        let mut base_counts: Option<[usize; crate::tables::N_TABLES]> = None;

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let mut xor: Vec<Xrow> = Vec::new();
        let mut mul: Vec<Xrow> = Vec::new();
        let mut add_ext: Vec<Erow> = Vec::new();
        let mut mul_ext: Vec<Erow> = Vec::new();
        let mut set: Vec<Srow> = Vec::new();
        let mut deref: Vec<Drow> = Vec::new();
        let mut deref_ext: Vec<EDrow> = Vec::new();
        let mut jump: Vec<Jrow> = Vec::new();
        let mut blake3: Vec<Brow> = Vec::new();

        // `DEREF Cell` touches whose two sides are both still unwritten (the
        // range-check gadget's unconstrained target cells), as `(a2, a3)`,
        // resolved after the run: write-once memory is order-independent, so the
        // value can be decided at the end (leanVM's end-of-execution deref-hint
        // resolution). The wide form carries the run's width too.
        let mut deferred: Vec<(usize, u32)> = Vec::new();
        let mut deferred_wide: Vec<(usize, u32, usize)> = Vec::new();

        // The three dense per-cell vectors, kept in lockstep. Every method is
        // `#[inline(always)]`: they sit in the interpreter's hot opcode loop.
        struct Mem {
            cells: Vec<F64>,
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
                    self.cells.resize(n, F64::ZERO);
                    self.written.resize(n, false);
                    self.count.resize(n, F64::ONE);
                }
            }
            // Read a cell; an unwritten cell reads as ZERO.
            #[inline(always)]
            fn get(&self, cell: u32) -> F64 {
                let c = cell as usize;
                if c < self.written.len() && self.written[c] {
                    self.cells[c]
                } else {
                    F64::ZERO
                }
            }
            // Write-once store: writing a different value to an already-set cell panics.
            #[inline(always)]
            fn put(&mut self, cell: u32, v: F64) {
                self.ensure(cell as usize);
                let c = cell as usize;
                if self.written[c] {
                    assert!(
                        self.cells[c] == v,
                        "write-once conflict at cell {cell} (pc {}, hint {:?}): had {:x}, new {:x}",
                        self.dbg_pc,
                        self.dbg_hint,
                        self.cells[c].0,
                        v.0
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
            /// The access counts of a run of `N` consecutive cells, each advanced.
            #[inline(always)]
            fn bump_run<const N: usize>(&mut self, base: u32) -> [F64; N] {
                std::array::from_fn(|k| self.bump_access_count(base + k as u32))
            }
            /// The extension value held by the three consecutive cells at `cell`.
            #[inline(always)]
            fn get_ext(&self, cell: u32) -> F192 {
                F192::new(self.get(cell).0, self.get(cell + 1).0, self.get(cell + 2).0)
            }
            /// Store an extension value across three consecutive cells.
            #[inline(always)]
            fn put_ext(&mut self, cell: u32, v: F192) {
                for (k, limb) in [v.c0, v.c1, v.c2].into_iter().enumerate() {
                    self.put(cell + k as u32, F64(limb));
                }
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

        // The program's own chain runs to the halt sentinel; the fill blocks then run, one
        // cycle at a time. A cycle is entered at its block's first instruction, in a frame
        // of its own, and traversed for the rows `filler::solve` asks of it, always a whole
        // number of traversals, so the state tuples it pushes are exactly the ones it pulls
        // (doc §Filling the tables). `left` is the rows still to run in the current cycle,
        // and `None` while the chain runs.
        let mut cycles: std::vec::IntoIter<(u32, u32, usize)> = Vec::new().into_iter();
        let mut left: Option<usize> = None;
        loop {
            // The chain reached the sentinel, or a cycle has run its rows.
            let switch = match left {
                None => pc == ending_pc,
                Some(n) => n == 0,
            };
            if switch {
                if left.is_none() {
                    assert_eq!((pc, fp), (ending_pc, 0), "main must halt at the sentinel pc g^{{B-1}}");
                    let counts = [
                        xor.len(),
                        mul.len(),
                        add_ext.len(),
                        mul_ext.len(),
                        set.len(),
                        deref.len(),
                        deref_ext.len(),
                        jump.len(),
                        blake3.len(),
                    ];
                    base_counts = Some(counts);
                    // A frame per cycle, from the same bump allocator that serves `Alloc`
                    // but never below the memory floor: a range check's `DEREF` writes the
                    // absolute cell its bound names, which can be any cell under
                    // `2^MIN_LOG_MEM` and so is nobody's to reserve (`lower_assert_lt`).
                    use super::filler::frame as fr;
                    let mut runs: Vec<(u32, u32, usize)> = Vec::new();
                    // A hand-assembled program carries no blocks and has to land on
                    // powers of two by itself, which `Layout` checks.
                    if !self.filler.is_empty() {
                        let mut frame = (1u32 << crate::cpu::MIN_LOG_MEM).max(next_free);
                        for (block_pc, size, n) in super::filler::cycles(&self.filler, counts) {
                            g.grow_to(frame as usize);
                            g.note(frame as usize);
                            // What the closing jump reads: back to the block's own first
                            // instruction, in this same frame. Then the pointer the `DEREF`
                            // dummy follows, memory cell `0`.
                            m.put(frame + fr::DEST, g.pow(block_pc as usize));
                            m.put(frame + fr::NEXT_FP, g.pow(frame as usize));
                            m.put(frame + fr::PTR, F64::ONE);
                            runs.push((block_pc, frame, n * (size as usize + 1)));
                            frame += fr::CELLS;
                        }
                        next_free = frame;
                    }
                    cycles = runs.into_iter();
                }
                match cycles.next() {
                    Some((p, f, rows)) => {
                        pc = p;
                        fp = f;
                        left = Some(rows);
                    }
                    None => break,
                }
            }
            if let Some(n) = &mut left {
                *n -= 1;
            }
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
                                m.cells[cell as usize] = g.pow(base as usize);
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
                                let k = g.log(v);
                                let small = v.0 < 1 << 32;
                                match (k, small) {
                                    (Some(k), true) => {
                                        eprintln!("[print] {label} = {} (g^{})", pretty_integer(v.0), pretty_integer(k))
                                    }
                                    (Some(k), false) => {
                                        eprintln!("[print] {label} = g^{}", pretty_integer(k))
                                    }
                                    (None, true) => {
                                        eprintln!("[print] {label} = {}", pretty_integer(v.0))
                                    }
                                    (None, false) => {
                                        eprintln!("[print] {label} = {:#x}", v.0)
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
                            m.put(fp + dst, primitives::field::g_pow(mu as usize));
                        }
                        RHint::BitDecompose { value, bits_ptr, nbits } => {
                            assert!(*nbits <= 64, "a machine word has 64 bits");
                            let v = m.get(fp + value);
                            let bp = as_addr(m.get(fp + bits_ptr))
                                .expect("decompose bits pointer is not a K-valued g-power");
                            let bb = g
                                .log(bp)
                                .unwrap_or_else(|| panic!("decompose bits pointer is not a g-power"));
                            for j in 0..*nbits {
                                let bit = (v.0 >> j) & 1;
                                m.put(bb + j, F64(bit));
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
                                m.put(bb + j, F64(bit));
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
                Op::AddExt { a, b, c } | Op::MulExt { a, b, c } | Op::MulExtBase { a, b, c } => {
                    let is_add = matches!(op, Op::AddExt { .. });
                    let base_a = matches!(op, Op::MulExtBase { .. });
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    let is_set = |w: &[bool], cell: u32| {
                        (0..3).all(|k| ((cell + k) as usize) < w.len() && w[(cell + k) as usize])
                    };
                    if !base_a && is_set(&m.written, ac) {
                        let (ha, hb) = (is_set(&m.written, aa), is_set(&m.written, ab));
                        if ha ^ hb {
                            let vc = m.get_ext(ac);
                            let vk = m.get_ext(if ha { aa } else { ab });
                            let v = if is_add {
                                vc + vk
                            } else {
                                assert!(!vk.is_zero(), "cannot back-solve MUL_EXT through zero");
                                vc * vk.inv()
                            };
                            m.put_ext(if ha { ab } else { aa }, v);
                        }
                    }
                    m.ensure(aa as usize + 2);
                    let va = if base_a { F192::from(m.get(aa)) } else { m.get_ext(aa) };
                    let vb = m.get_ext(ab);
                    m.put_ext(ac, if is_add { va + vb } else { va * vb });
                    let ra = m.bump_run(aa);
                    let rb = m.bump_run(ab);
                    let rc = m.bump_run(ac);
                    let row = Erow {
                        pc,
                        fp,
                        ra,
                        rb,
                        rc,
                        bytecode_read,
                    };
                    if is_add {
                        add_ext.push(row);
                    } else {
                        mul_ext.push(row);
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
                    let p_addr = as_addr(p).expect("DEREF pointer is not a base-field word");
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
                                    let v3 = m.get(a3);
                                    assert!(
                                        m.cells[a2] == v3,
                                        "DEREF mismatch at pc {pc}: mem[{a2}]={:016x}, fp[{gamma}] (cell {a3})={:016x}",
                                        m.cells[a2].0,
                                        v3.0
                                    )
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
                            let v = g.pow(pc as usize + 2);
                            m.put(a2 as u32, v);
                        }
                        DerefMode::Fp => {
                            g.note(fp as usize);
                            let v = g.pow(fp as usize);
                            m.put(a2 as u32, v);
                        }
                    }
                    let r1 = m.bump_access_count(a1);
                    let r2 = m.bump_access_count(a2 as u32);
                    let r3 = m.bump_access_count(a3);
                    deref.push(Drow {
                        pc,
                        fp,
                        r1,
                        r2,
                        r3,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Deref128 { alpha, beta, gamma } | Op::DerefExt { alpha, beta, gamma } => {
                    let width = if matches!(op, Op::DerefExt { .. }) { 3 } else { 2 };
                    let kind = if width == 3 { "DEREF_EXT" } else { "DEREF_128" };
                    let a1 = fp + alpha;
                    let p = m.get(a1);
                    let p_addr = as_addr(p).unwrap_or_else(|| panic!("{kind} pointer is not a base-field word"));
                    let base = match g.log(p_addr) {
                        Some(b) => b,
                        None => {
                            g.grow_to(1 << MIN_LOG_MEM);
                            g.log(p_addr).unwrap_or_else(|| {
                                panic!("{kind} pointer is not a small g-power at pc {pc}: 0x{:016x}", p_addr.0)
                            })
                        }
                    };
                    let a2 = (base + beta) as usize;
                    let a3 = fp + gamma;
                    m.ensure(a2 + 2);
                    m.ensure(a3 as usize + 2);
                    let mut unresolved = false;
                    for k in 0..width {
                        match (m.written[a2 + k], m.written[a3 as usize + k]) {
                            (true, true) => assert_eq!(
                                m.cells[a2 + k],
                                m.cells[a3 as usize + k],
                                "{kind} mismatch at pc {pc}, limb {k}"
                            ),
                            (true, false) => {
                                let v = m.cells[a2 + k];
                                m.put(a3 + k as u32, v);
                            }
                            (false, true) => {
                                let v = m.cells[a3 as usize + k];
                                m.put(a2 as u32 + k as u32, v);
                            }
                            (false, false) => unresolved = true,
                        }
                    }
                    if unresolved {
                        deferred_wide.push((a2, a3, width));
                    }
                    let r1 = m.bump_access_count(a1);
                    let r2 = m.bump_run(a2 as u32);
                    let r3 = m.bump_run(a3);
                    deref_ext.push(EDrow {
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
                Op::Blake3 { ins, cv, out, metadata } => {
                    let (aa0, aa1, ab0, ab1) = (fp + ins[0], fp + ins[1], fp + ins[2], fp + ins[3]);
                    let acv = fp + cv;
                    let ac = fp + out;
                    let va = [m.get(aa0), m.get(aa0 + 1), m.get(aa1), m.get(aa1 + 1)];
                    let vb = [m.get(ab0), m.get(ab0 + 1), m.get(ab1), m.get(ab1 + 1)];
                    let vcv = std::array::from_fn(|k| m.get(acv + k as u32));
                    // Compress the 64 message bytes to the 32-byte result, then
                    // write it to c's four cells. No table constraint covers the
                    // digest (the relation is proven by flock, §blake3_flock); the
                    // interpreter still computes the definite digest so the output
                    // cells are consistent for any later read.
                    let vc = blake3_compress(va, vb, vcv, metadata);
                    for (k, v) in vc.into_iter().enumerate() {
                        m.put(ac + k as u32, v);
                    }
                    let ra0 = m.bump_run::<2>(aa0);
                    let ra1 = m.bump_run::<2>(aa1);
                    let rb0 = m.bump_run::<2>(ab0);
                    let rb1 = m.bump_run::<2>(ab1);
                    let rcv = m.bump_run::<4>(acv);
                    let rc = m.bump_run::<4>(ac);
                    let ra = [ra0[0], ra0[1], ra1[0], ra1[1]];
                    let rb = [rb0[0], rb0[1], rb1[0], rb1[1]];
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
        loop {
            let mut progress = false;
            deferred.retain(|&(a2, a3)| match (m.written[a2], m.written[a3 as usize]) {
                (true, true) => {
                    assert_eq!(m.cells[a2], m.cells[a3 as usize], "deferred DEREF mismatch");
                    false
                }
                (true, false) => {
                    let v = m.cells[a2];
                    m.put(a3, v);
                    progress = true;
                    false
                }
                (false, true) => {
                    let v = m.cells[a3 as usize];
                    m.put(a2 as u32, v);
                    progress = true;
                    false
                }
                (false, false) => true,
            });
            deferred_wide.retain(|&(a2, a3, width)| {
                let mut unresolved = false;
                for k in 0..width {
                    match (m.written[a2 + k], m.written[a3 as usize + k]) {
                        (true, true) => assert_eq!(
                            m.cells[a2 + k],
                            m.cells[a3 as usize + k],
                            "deferred wide DEREF mismatch, limb {k}"
                        ),
                        (true, false) => {
                            let v = m.cells[a2 + k];
                            m.put(a3 + k as u32, v);
                            progress = true;
                        }
                        (false, true) => {
                            let v = m.cells[a3 as usize + k];
                            m.put(a2 as u32 + k as u32, v);
                            progress = true;
                        }
                        (false, false) => unresolved = true,
                    }
                }
                unresolved
            });
            if !progress {
                // An all-unwritten equality component is unconstrained. Seed
                // one cell with zero, then let the same fixpoint propagate it
                // through scalar and extension dereferences before choosing a
                // seed for the next component.
                if let Some(&(a2, _)) = deferred.first() {
                    m.put(a2 as u32, F64::ZERO);
                    continue;
                }
                let seed = deferred_wide.iter().find_map(|&(a2, a3, width)| {
                    (0..width)
                        .find(|&k| !m.written[a2 + k] && !m.written[a3 as usize + k])
                        .map(|k| a2 + k)
                });
                if let Some(cell) = seed {
                    m.put(cell as u32, F64::ZERO);
                    continue;
                }
                break;
            }
        }

        // Pad memory to a power of two (the boundary tables read a dense image),
        // at least 2^MIN_LOG_MEM cells (doc §Memory).
        let mem_used = m.cells.len();
        let cells = m.cells.len().next_power_of_two().max(1 << MIN_LOG_MEM);
        assert!(cells <= 1 << MAX_LOG_MEM, "data memory exceeds 2^{MAX_LOG_MEM} cells");
        m.cells.resize(cells, F64::ZERO);
        m.count.resize(cells, F64::ONE);
        let trace = Trace {
            xor,
            mul,
            add_ext,
            mul_ext,
            set,
            deref,
            deref_ext,
            jump,
            blake3,
            mem_count: m.count,
            bytecode_count,
        };
        Execution {
            mem: m.cells,
            cycles: steps,
            mem_used,
            // Taken when the chain halted, which every run does before it can leave the
            // loop at all.
            base_counts: base_counts.expect("the run halted, so its own counts were taken"),
            trace,
        }
    }
}
