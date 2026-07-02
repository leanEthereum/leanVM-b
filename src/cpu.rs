//! Whole-program assembly over GF(2^128) (§7, §8): all six instruction
//! tables sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free.
//!
//! Each opcode keeps its own table; the tables interlock only through the three
//! shared interactions. Addresses, the program counter, and read counts are
//! g-powers, so every increment is a free ×g; arithmetic is the field's own
//! (XOR = degree-1, MUL_NATIVE = degree-2); there is no addition gadget and no
//! materialization. `BLAKE3` (§7.6) adds memory/state/bytecode plumbing for a
//! 64→32-byte compression whose relation is left unproven. A program with all
//! six opcodes plus control flow proves and verifies end-to-end.

use std::collections::HashMap;

use rayon::prelude::*;

use crate::constraints;
use crate::field::{F128, g, g_pow};
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_BLAKE3, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM,
    SEP_STATE,
};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::{self, Column};

/// `BLAKE3` compression (doc §7.6, unproven): the four input words are the two
/// 256-bit operands `a = (va0, va1)` and `b = (vb0, vb1)`, laid out little-endian
/// into 64 bytes; the 32-byte digest is split back into the two output words
/// `c = (vc0, vc1)`. The exact compression is a future detail — we use the
/// standard BLAKE3 hash of the 64-byte input, which is a deterministic
/// 64-byte→32-byte map; nothing constrains it in the proof.
fn blake3_compress(va0: F128, va1: F128, vb0: F128, vb1: F128) -> (F128, F128) {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(16).zip([va0, va1, vb0, vb1]) {
        slot[..8].copy_from_slice(&w.lo.to_le_bytes());
        slot[8..].copy_from_slice(&w.hi.to_le_bytes());
    }
    let digest = blake3::hash(&input);
    let d = digest.as_bytes();
    let word = |b: &[u8]| F128::new(
        u64::from_le_bytes(b[..8].try_into().unwrap()),
        u64::from_le_bytes(b[8..16].try_into().unwrap()),
    );
    (word(&d[..16]), word(&d[16..]))
}

/// Data-memory size bounds (doc §Memory): memory is `2^h` cells with
/// `MIN_LOG_MEM ≤ h ≤ MAX_LOG_MEM`. The prover pads up to the minimum; the
/// verifier rejects any announced `h` outside the range.
const MIN_LOG_MEM: usize = 16;
const MAX_LOG_MEM: usize = 32;

/// Each per-opcode table holds at most `2^MAX_LOG_ROWS` rows (executed
/// instructions of that opcode).
const MAX_LOG_ROWS: usize = 32;

/// Announce the public statement — per-table log-sizes (`log_mem` + the six
/// `row_counts`) and the public input into the Fiat–Shamir transcript. The prover
/// writes the seven sizes onto the scalar stream (so the verifier can reconstruct
/// the layout — which binds them into the sponge) and observes the public input.
/// The boundary states and per-table log-sizes (`taus`) are derived (constants
/// from the program, and `padlen(row_counts)`), so they need no separate binding.
/// Called right after the witness commitment, so every challenge depends on it.
fn announce_public(ps: &mut ProverState, pi: &[F128; 2], log_mem: usize, row_counts: [usize; 6]) {
    ps.write_scalar(F128::new(log_mem as u64, 0));
    for r in row_counts {
        ps.write_scalar(F128::new(r as u64, 0));
    }
    ps.observe_scalars(pi);
}

/// Verifier side of [`announce_public`]: read the seven announced sizes from the
/// stream, reconstruct the public [`Layout`] from the program + sizes + public
/// input, then observe the public input (matching the prover's binding order).
fn read_public(vs: &mut VerifierState, prog: &Program, public_input: &[F128; 2]) -> Result<Layout, Error> {
    let log_mem = vs.next_scalar().map_err(Error::Transcript)?.lo as usize;
    let mut row_counts = [0usize; 6];
    for r in &mut row_counts {
        *r = vs.next_scalar().map_err(Error::Transcript)?.lo as usize;
    }
    // Sanity-bound the announced sizes (a table's row count is the number of times
    // its opcode runs — unbounded by the bytecode size, since a small loop body
    // runs many times — so cap it generously, not by `bytecode_size`). The bus balance and
    // GKR pin the actual sizes; this only guards against absurd/overflowing values.
    let bytecode_size = prog.prog.len();
    if !bytecode_size.is_power_of_two()
        || !(MIN_LOG_MEM..=MAX_LOG_MEM).contains(&log_mem)
        || row_counts.iter().any(|&r| r > (1usize << MAX_LOG_ROWS))
    {
        return Err(Error::PublicInput);
    }
    let l = layout(&prog.prog, log_mem, row_counts, *public_input);
    vs.observe_scalars(&l.pi);
    Ok(l)
}

#[derive(Clone, Copy, Debug)]
pub enum Op {
    Xor {
        a: u32,
        b: u32,
        c: u32,
    },
    Mul {
        a: u32,
        b: u32,
        c: u32,
    },
    Set {
        o: u32,
        k: F128,
    },
    Deref {
        alpha: u32,
        beta: u32,
        gamma: u32,
        mode: DerefMode,
    },
    Jump {
        oc: u32,
        od: u32,
        of: u32,
    },
    /// `BLAKE3` (doc §7.6): each operand names a 256-bit value held in two
    /// consecutive memory words (at `fp+o` and its successor `fp+o+1`). Reads the
    /// two inputs `a, b` (64 bytes) and writes the 32-byte digest to `c`. The
    /// compression itself is *unproven* — this table carries only the memory /
    /// state / bytecode bus interactions, with no constraint relating output to
    /// input.
    Blake3 {
        a: u32,
        b: u32,
        c: u32,
    },
}

/// The source `DEREF` stores at `mem[loc_α·β]` (doc §1): a local cell, the return
/// address `pc+γ`, or the frame pointer. Encoded in the proof as two boolean
/// flags `(f_pc, f_fp)` — `Cell=(0,0)`, `Pc=(1,0)`, `Fp=(0,1)` — which keep the
/// store-selection constraint degree 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerefMode {
    Cell,
    Pc,
    Fp,
}

impl DerefMode {
    pub(crate) fn f_pc(self) -> F128 {
        if self == DerefMode::Pc { F128::ONE } else { F128::ZERO }
    }
    pub(crate) fn f_fp(self) -> F128 {
        if self == DerefMode::Fp { F128::ONE } else { F128::ZERO }
    }
}

pub struct Program {
    pub prog: Vec<Op>, // bytecode (size B, power of two)
    pub pc0: u32,
    pub fp0: u32,
    /// Prover-side frame/buffer allocation hints (keyed by global pc) and the
    /// size of `main`'s frame — the nondeterminism [`Program::execute`] needs to
    /// run the program. Public verification (\S `verify`) ignores them.
    pub(crate) hints: HashMap<u32, Vec<crate::compiler::RHint>>,
    pub(crate) main_frame: u32,
}

impl Program {
    /// Assemble a program directly from a fixed bytecode vector, starting at
    /// `(pc, fp) = (0, 0)` with no allocation hints. Suitable for straight-line
    /// programs that never change the frame pointer and touch only the first
    /// `main_frame` memory cells (so the prover needs no nondeterministic frame
    /// allocation). `prog.len()` must be a power of two with a never-executed
    /// sentinel in its last slot — the run halts on reaching `g^{len-1}` (§state).
    pub fn from_bytecode(prog: Vec<Op>, main_frame: u32) -> Self {
        Self {
            prog,
            pc0: 0,
            fp0: 0,
            hints: HashMap::new(),
            main_frame,
        }
    }
}

/// Render the bytecode as a disassembly listing (also gives `Program::to_string`).
impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&crate::compiler::disassemble(&self.prog))
    }
}

pub struct Execution {
    pub mem: Vec<F128>,      // data memory after the run, write-once (size cells, power of two)
    pub cycles: usize,       // number of instructions the run executed (trace length)
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
        let g_step = g();

        // g^j and its reverse index g^j ↦ j, grown lazily (deep recursion is
        // unbounded). Seed enough for the program counters / return targets.
        let mut gpow: Vec<F128> = vec![F128::ONE];
        let mut gmap: HashMap<F128, u32> = HashMap::from([(F128::ONE, 0u32)]);
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

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let (mut xor, mut mul, mut set, mut deref, mut jump, mut blake3) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());

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
                assert!(mem[c] == v, "write-once conflict at cell {cell}");
            } else {
                mem[c] = v;
                written[c] = true;
            }
        }
        // Read the running access count and advance it by ×g (the free increment).
        fn bump_access_count(
            mem: &mut Vec<F128>,
            written: &mut Vec<bool>,
            mem_count: &mut Vec<F128>,
            g_step: F128,
            cell: u32,
        ) -> F128 {
            ensure(mem, written, mem_count, cell as usize);
            let cell_idx = cell as usize;
            let count = mem_count[cell_idx];
            mem_count[cell_idx] = count * g_step;
            count
        }

        while pc != ending_pc {
            assert!(steps < 100_000_000, "step limit exceeded (runaway recursion?)");

            // Apply the hints scheduled before this instruction.
            if let Some(hs) = self.hints.get(&pc) {
                for h in hs {
                    match *h {
                        RHint::Alloc { ptr, size } => {
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
                    }
                }
            }
            // Cover the g-powers this step may index (g²·pc return target, g^fp).
            grow_gpow(&mut gpow, &mut gmap, (pc as usize + 2).max(fp as usize));

            let bytecode_read = {
                let v = bytecode_count[pc as usize];
                bytecode_count[pc as usize] = v * g_step;
                v
            };

            match self.prog[pc as usize] {
                Op::Xor { a, b, c } | Op::Mul { a, b, c } => {
                    let is_xor = matches!(self.prog[pc as usize], Op::Xor { .. });
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    let va = get(&mem, &written, aa);
                    let vb = get(&mem, &written, ab);
                    let vc = if is_xor { va + vb } else { va * vb };
                    put(&mut mem, &mut written, &mut mem_count, ac, vc);
                    let ra = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, aa);
                    let rb = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ab);
                    let rc = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ac);
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
                    let r = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, a);
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
                    let base = *gmap.get(&p).expect("DEREF pointer is not a g-power");
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
                                (false, false) => panic!("DEREF Cell: both sides unset"),
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
                    let r1 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, a1);
                    let r2 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, a2 as u32);
                    let r3 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, a3);
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
                    let (w, b) = if c.is_zero() {
                        (F128::ZERO, F128::ZERO)
                    } else {
                        (c.inv(), F128::ONE)
                    };
                    let rc = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ac);
                    let rd = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ad);
                    let rf = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, af);
                    let taken = !c.is_zero();
                    let (npc, nfp) = if taken {
                        (d, f)
                    } else {
                        (g_step * gpow[pc as usize], gpow[fp as usize])
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
                Op::Blake3 { a, b, c } => {
                    // Each operand spans two consecutive words: base = fp+o, second = base+1.
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    let (va0, va1) = (get(&mem, &written, aa), get(&mem, &written, aa + 1));
                    let (vb0, vb1) = (get(&mem, &written, ab), get(&mem, &written, ab + 1));
                    // Compress the 64 input bytes to the 32-byte digest, then write
                    // it to c's two words. The relation is unproven (no constraint),
                    // but the prover still computes a definite digest so the output
                    // cells are consistent for any later read.
                    let (vc0, vc1) = blake3_compress(va0, va1, vb0, vb1);
                    put(&mut mem, &mut written, &mut mem_count, ac, vc0);
                    put(&mut mem, &mut written, &mut mem_count, ac + 1, vc1);
                    let ra0 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, aa);
                    let ra1 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, aa + 1);
                    let rb0 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ab);
                    let rb1 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ab + 1);
                    let rc0 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ac);
                    let rc1 = bump_access_count(&mut mem, &mut written, &mut mem_count, g_step, ac + 1);
                    blake3.push(Brow {
                        pc,
                        fp,
                        aa,
                        ab,
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

        // Pad memory to a power of two (the boundary tables read a dense image),
        // at least 2^MIN_LOG_MEM cells (doc §Memory).
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
            trace,
        }
    }
}

// ---- column schema -----------------------------------------------------------

// Shared committed columns (indices `0..N_SHARED`). The program (opcode +
// operands) is PUBLIC, not committed: it rides the bytecode seed/finalize blocks
// as `Coord::Public`; only the witness-dependent finalize counts are committed.
const MEM: usize = 0; // the data-memory image
const MFCNT: usize = 1; // per-cell memory access count, g^{A[i]}
const BFCNT: usize = 2; // per-pc bytecode execution count, g^{A[pc]}
// flock's packed BLAKE3 witness `q_pkd`, committed in the SAME stack as every
// other column (single PCS). Size `2^(K_LOG+n_log-7)` when the program runs ≥1
// BLAKE3, else a size-1 dummy (kept in the static schema). The BLAKE3 value
// columns bind to it by point-eval equality, and flock's R1CS validity is
// discharged by a basefold over this stacked commitment (§blake3_flock).
const QPKD: usize = 3;
const N_SHARED: usize = 4;

/// Global column indexing: the shared columns occupy `0..N_SHARED`, then each
/// table `t` (in [`tables::tables`] order) owns the contiguous block `[base[t],
/// base[t] + n_committed_columns_t)`. Both prover and verifier derive this identically
/// from the table set, so every column claim lines up.
struct Schema {
    base: [usize; 6],
    n: usize,
}

/// The schema is a pure function of the fixed table set, so compute it once.
fn schema() -> &'static Schema {
    static SCHEMA: std::sync::OnceLock<Schema> = std::sync::OnceLock::new();
    SCHEMA.get_or_init(|| {
        let mut base = [0usize; 6];
        let mut next = N_SHARED;
        for (t, table) in tables::tables().iter().enumerate() {
            base[t] = next;
            next += table.n_committed_columns();
        }
        Schema { base, n: next }
    })
}

/// Offset a table's local flush coordinates to global column indices.
fn offset_coords(base: usize, coords: Vec<Coord>) -> Vec<Coord> {
    coords
        .into_iter()
        .map(|c| match c {
            Coord::Col(i) => Coord::Col(base + i),
            Coord::GCol(i) => Coord::GCol(base + i),
            other => other,
        })
        .collect()
}

// ---- simulation --------------------------------------------------------------

pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    pub(crate) aa: u32,
    pub(crate) ab: u32,
    pub(crate) ac: u32,
    pub(crate) ra: F128,
    pub(crate) rb: F128,
    pub(crate) rc: F128,
    pub(crate) bytecode_read: F128,
}
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) o: u32,
    pub(crate) a: u32,
    pub(crate) k: F128,
    pub(crate) r: F128,
    pub(crate) bytecode_read: F128,
}
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) alpha: u32,
    pub(crate) beta: u32,
    pub(crate) gamma: u32,
    pub(crate) mode: DerefMode,
    pub(crate) a1: u32,
    pub(crate) p: F128,
    pub(crate) a2: usize,
    pub(crate) a3: u32,
    pub(crate) v2: F128, // mem[a2], the store target
    pub(crate) v3: F128, // mem[a3], the local cell
    pub(crate) r1: F128,
    pub(crate) r2: F128,
    pub(crate) r3: F128,
    pub(crate) bytecode_read: F128,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) npc: F128,
    pub(crate) nfp: F128,
    pub(crate) oc: u32,
    pub(crate) od: u32,
    pub(crate) of: u32,
    pub(crate) ac: u32,
    pub(crate) ad: u32,
    pub(crate) af: u32,
    pub(crate) c: F128,
    pub(crate) d: F128,
    pub(crate) f: F128,
    pub(crate) w: F128, // inverse hint (is-nonzero witness): c⁻¹ when c ≠ 0, else 0
    pub(crate) b: F128, // taken indicator b = [c ≠ 0]
    pub(crate) rc: F128,
    pub(crate) rd: F128,
    pub(crate) rf: F128,
    pub(crate) bytecode_read: F128,
}

/// `BLAKE3` row: the base addresses `aa, ab, ac` (each spanning two words), the
/// six word values (two inputs `a`, two inputs `b`, two outputs `c`), and the six
/// per-word memory read counts.
pub(crate) struct Brow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) aa: u32,
    pub(crate) ab: u32,
    pub(crate) ac: u32,
    pub(crate) va0: F128,
    pub(crate) va1: F128,
    pub(crate) vb0: F128,
    pub(crate) vb1: F128,
    pub(crate) vc0: F128,
    pub(crate) vc1: F128,
    pub(crate) ra0: F128,
    pub(crate) ra1: F128,
    pub(crate) rb0: F128,
    pub(crate) rb1: F128,
    pub(crate) rc0: F128,
    pub(crate) rc1: F128,
    pub(crate) bytecode_read: F128,
}

pub(crate) struct Trace {
    pub(crate) xor: Vec<Xrow>,
    pub(crate) mul: Vec<Xrow>,
    pub(crate) set: Vec<Srow>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Jrow>,
    pub(crate) blake3: Vec<Brow>,
    pub(crate) mem_count: Vec<F128>, // per-cell running access count g^{count}; final = g^{A[i]}
    pub(crate) bytecode_count: Vec<F128>, // per-pc running execution count g^{count}; final = g^{A[pc]}
}

/// The public proof structure: everything the verifier reconstructs from the
/// program, the announced sizes, and the public input — no witness values. The
/// flush blocks reference columns by INDEX (see [`crate::leaf::Coord`]), so they
/// are pure public structure.
pub struct Layout {
    pub push: Vec<Block>,
    pub pull: Vec<Block>,
    /// Count channel: read-count columns whose product must be nonzero (§sec:memchan).
    pub count: Vec<Block>,
    /// Per-column padding value (count columns pad with 1, else 0), so the verifier
    /// can form the default-padding surplus it divides out of the bus (§sec:gp).
    pub pad: Vec<F128>,
    /// Per-column placement (offset + n_vars) in the stacked witness; from the
    /// columns' log-sizes alone, so reconstructable by the verifier.
    pub placements: Vec<witness::Placement>,
    /// `log2` of the stacked witness length.
    pub m: usize,
    pub pc0: u32,
    pub fp0: u32,
    pub final_pc: u32,
    pub final_fp: u32,
    /// Public input: the first two memory cells `m[0], m[1]` (256 bits), bound to
    /// the committed memory at verification (§8).
    pub pi: [F128; 2],
    pub taus: [usize; 6], // (xor, mul, set, deref, jump, blake3) log row counts
    /// Real (non-padded) per-table row counts, as announced. `row_counts[5]` is
    /// the executed `BLAKE3` count, which gates the flock sub-proof.
    pub row_counts: [usize; 6],
}

/// The prover's witness bundle: the committed column values + their stacked
/// multilinear `q` + the public [`Layout`] (plus the sizes needed to announce it).
struct Witness {
    cols: Vec<Column>,
    q: Vec<F128>,
    layout: Layout,
    log_mem: usize,
    row_counts: [usize; 6],
}

/// Column → log-size (`kappa`) map: the shared MEM/MFCNT columns are `2^log_mem`,
/// the bytecode finalize count is `2^log_bytecode`, and every column of table `t`
/// is `2^taus[t]` (its padded log-row-count). Depends only on the public sizes,
/// so the verifier can reconstruct the placements.
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; 6], n_blake3: usize) -> Vec<usize> {
    let sch = schema();
    let mut k = vec![0usize; sch.n];
    k[MEM] = log_mem;
    k[MFCNT] = log_mem;
    k[BFCNT] = log_bytecode;
    // q_pkd: `2^(K_LOG+n_log-7)` F128 coords when BLAKE3 ran, else a size-1 dummy.
    k[QPKD] = crate::blake3_flock::qpkd_kappa(n_blake3);
    for (t, table) in tables::tables().iter().enumerate() {
        for c in sch.base[t]..sch.base[t] + table.n_committed_columns() {
            k[c] = taus[t];
        }
    }
    k
}

/// Build the public [`Layout`] from the program, the memory log-size `log_mem`, the
/// six tables' real row counts `row_counts`, and the public input `pi`. The flush
/// blocks reference columns only by INDEX and the program only through its
/// public columns, so this needs no committed witness — both prover and verifier
/// reconstruct exactly the same structure (§7, §8).
fn layout(prog: &[Op], log_mem: usize, row_counts: [usize; 6], pi: [F128; 2]) -> Layout {
    let bytecode_size = prog.len();
    let log_bytecode = crate::log2_strict_usize(bytecode_size);
    let cells = 1usize << log_mem;

    // Per-table padded log-row-counts (the boundary block is fixed). The real
    // (non-padded) `row_counts[t]` tell each flush how many of its 2^kappa rows
    // are padding (default rows divided out of the bus, §sec:gp).
    let mut taus = [0usize; 6];
    for (i, &r) in row_counts.iter().enumerate() {
        taus[i] = crate::log2_ceil_usize(r.max(1));
    }
    // The BLAKE3 table is sized to flock's `2^n_log` instance count (lincheck
    // floor ≥ 8) so its per-instance value columns share `q_pkd`'s instance cube
    // — the binding (§blake3_flock) opens both at one random point of that cube.
    if row_counts[tables::BLAKE3_TABLE] > 0 {
        taus[tables::BLAKE3_TABLE] = crate::blake3_flock::n_blocks_log(row_counts[tables::BLAKE3_TABLE]);
    }

    // Derived boundary: the run starts at (pc,fp) = (0,0) and, by convention, the
    // final pc is the bytecode's last cell g^{B-1} (the compiler emits a halt jump
    // there), with fp returned to 0. All public, no trace needed.
    let pc0 = 0u32;
    let fp0 = 0u32;
    let final_pc = (bytecode_size - 1) as u32;
    let final_fp = 0u32;

    let one = F128::ONE;
    // The public program columns map operand *offsets* (small, ≤ frame size) to
    // g-powers — not memory addresses — so precompute only up to the largest
    // operand, an O(1) lookup each, rather than over the whole 2^log_mem memory.
    let max_op = prog
        .iter()
        .map(|op| match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => a.max(b).max(c),
            Op::Set { o, .. } => o,
            Op::Deref { alpha, beta, gamma, .. } => alpha.max(beta).max(gamma),
            Op::Jump { oc, od, of } => oc.max(od).max(of),
            Op::Blake3 { a, b, c } => a.max(b).max(c),
        })
        .max()
        .unwrap_or(0) as usize;
    let gpow = crate::field::g_powers((max_op + 1).max(2));
    let g_at = |i: u32| gpow[i as usize]; // operand g-power

    let opcode = |op: &Op| match op {
        Op::Xor { .. } => OP_XOR,
        Op::Mul { .. } => OP_MUL,
        Op::Set { .. } => OP_SET,
        Op::Deref { .. } => OP_DEREF,
        Op::Jump { .. } => OP_JUMP,
        Op::Blake3 { .. } => OP_BLAKE3,
    };
    let operands = |op: &Op| -> (F128, F128, F128) {
        match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (g_at(a), g_at(b), g_at(c)),
            Op::Set { o, k } => (g_at(o), k, F128::ZERO),
            Op::Deref { alpha, beta, gamma, .. } => (g_at(alpha), g_at(beta), g_at(gamma)),
            Op::Jump { oc, od, of } => (g_at(oc), g_at(od), g_at(of)),
            Op::Blake3 { a, b, c } => (g_at(a), g_at(b), g_at(c)),
        }
    };
    // The two DEREF store-mode flags, public program fields (0 elsewhere).
    let fpc = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_pc(),
        _ => F128::ZERO,
    };
    let ffp = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_fp(),
        _ => F128::ZERO,
    };
    // The program is PUBLIC (not committed): six public columns over the
    // program cube, embedded in the bytecode seed/finalize blocks below.
    let prog_op: Vec<F128> = prog.par_iter().map(opcode).collect();
    let prog_o1: Vec<F128> = prog.par_iter().map(|o| operands(o).0).collect();
    let prog_o2: Vec<F128> = prog.par_iter().map(|o| operands(o).1).collect();
    let prog_o3: Vec<F128> = prog.par_iter().map(|o| operands(o).2).collect();
    let prog_fpc: Vec<F128> = prog.par_iter().map(fpc).collect();
    let prog_ffp: Vec<F128> = prog.par_iter().map(ffp).collect();

    // ---- bus blocks ----
    use Coord::{Col, Const, Index, Public};
    // `real` is the block's non-padded row count (= 2^kappa for the full
    // boundary/seed/finalize blocks; the table's real row count for a flush).
    let blk = |kappa: usize, real: usize, coords: Vec<Coord>| Block { kappa, coords, real };

    let mut push: Vec<Block> = Vec::new();
    let mut pull: Vec<Block> = Vec::new();

    // Shared blocks (cross-instruction infra, not owned by any single table).
    // boundary state.
    push.push(blk(
        0,
        1,
        vec![Const(SEP_STATE), Const(g_pow(pc0 as usize)), Const(g_pow(fp0 as usize))],
    ));
    pull.push(blk(
        0,
        1,
        vec![
            Const(SEP_STATE),
            Const(g_pow(final_pc as usize)),
            Const(g_pow(final_fp as usize)),
        ],
    ));
    // memory seed + finalize (every address real, no padding).
    push.push(blk(log_mem, cells, vec![Const(SEP_MEM), Index, Const(one), Col(MEM)]));
    pull.push(blk(log_mem, cells, vec![Const(SEP_MEM), Index, Col(MFCNT), Col(MEM)]));
    // bytecode seed + finalize (program columns are public; padding entries
    // self-cancel at count 1, so the whole 2^log_bytecode is "real").
    push.push(blk(
        log_bytecode,
        bytecode_size,
        vec![
            Const(SEP_BYTECODE),
            Index,
            Const(one),
            Public(prog_op.clone()),
            Public(prog_o1.clone()),
            Public(prog_o2.clone()),
            Public(prog_o3.clone()),
            Public(prog_fpc.clone()),
            Public(prog_ffp.clone()),
        ],
    ));
    pull.push(blk(
        log_bytecode,
        bytecode_size,
        vec![
            Const(SEP_BYTECODE),
            Index,
            Col(BFCNT),
            Public(prog_op),
            Public(prog_o1),
            Public(prog_o2),
            Public(prog_o3),
            Public(prog_fpc),
            Public(prog_ffp),
        ],
    ));

    // Per-table blocks: each table declares its flushes and read-count columns in
    // local indices; offset them to the table's global columns. The count columns
    // also fix the per-column padding to `1` (so they never zero the bus product).
    let sch = schema();
    let mut count_blocks: Vec<Block> = Vec::new();
    let mut pad = vec![F128::ZERO; sch.n];
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        let (kappa, real) = (taus[t], row_counts[t]);
        let mut fb = FlushBuilder::new();
        table.flushes(&mut fb);
        for coords in fb.push {
            push.push(blk(kappa, real, offset_coords(base, coords)));
        }
        for coords in fb.pull {
            pull.push(blk(kappa, real, offset_coords(base, coords)));
        }
        for &c in table.count_columns() {
            count_blocks.push(blk(kappa, real, vec![Col(base + c)]));
            pad[base + c] = F128::ONE;
        }
    }
    // BLAKE3 padding rows must match flock's padding instance (the all-zero-input
    // compression): zero inputs but a NONZERO output `out_lo`. So the two output
    // value columns pad with that digest, not 0 — otherwise the value-column MLE
    // would disagree with `q_pkd` on the padding instances and the binding
    // (§blake3_flock) would fail. Inputs/counts keep their 0/1 defaults.
    if row_counts[tables::BLAKE3_TABLE] > 0 {
        let b3 = sch.base[tables::BLAKE3_TABLE];
        let pc = crate::blake3_flock::padding_digest();
        pad[b3 + tables::BLAKE3_VALUE_COLS[4]] = pc[0]; // c0
        pad[b3 + tables::BLAKE3_VALUE_COLS[5]] = pc[1]; // c1
    }

    let (placements, m) = witness::placements_of(&col_kappas(
        log_mem,
        log_bytecode,
        taus,
        row_counts[tables::BLAKE3_TABLE],
    ));
    Layout {
        push,
        pull,
        count: count_blocks,
        pad,
        placements,
        m,
        pc0,
        fp0,
        final_pc,
        final_fp,
        pi,
        taus,
        row_counts,
    }
}

impl Program {
    fn build(&self, exec: &Execution) -> Witness {
        assert!(self.prog.len().is_power_of_two());
        assert!(exec.mem.len().is_power_of_two());
        let prof = std::env::var("LEANVM_PROFILE").is_ok();
        // The trace was emitted in the same walk as the memory image (no re-walk).
        let tr = &exec.trace;
        let t_fill = std::time::Instant::now();
        let cells = exec.mem.len();
        let bytecode_size = self.prog.len();
        let log_mem = crate::log2_strict_usize(cells);

        // Each table is padded up to a power-of-two row count (§4.4, §e2e-pad):
        // the appended rows are all-zero, so on every domain their push and pull
        // are the identical tuple and self-cancel on the bus, and the all-zero
        // assignment satisfies every degree-≤2 constraint. (Padding is applied to
        // the filled columns below, after the real rows, to `2^taus[t]`.)

        let sch = schema();
        let mut cols = vec![Column::new(); sch.n];
        // Precompute g^0..g^{span-1} once so every address/pc/operand fill is an
        // O(1) lookup instead of an O(log) power.
        let span = cells.max(bytecode_size);
        let gpow = crate::field::g_powers(span);

        // Each table fills its own columns from the trace (local indices, offset
        // into its global block).
        let ctx = FillCtx {
            trace: tr,
            mem: &exec.mem,
            gpow: &gpow,
        };
        for (t, table) in tables::tables().iter().enumerate() {
            let (base, n) = (sch.base[t], table.n_committed_columns());
            table.fill(&ctx, &mut cols[base..base + n]);
        }
        // Shared columns.
        cols[MEM] = exec.mem.clone();
        cols[MFCNT] = tr.mem_count.clone(); // running counts ended at g^{A[i]}
        cols[BFCNT] = tr.bytecode_count.clone(); // running counts ended at g^{A[pc]}
        // flock's packed BLAKE3 witness q_pkd, committed in this same stack (or a
        // size-1 dummy when no BLAKE3 ran). Built from the executed BLAKE3 rows in
        // order, so row j = flock instance j.
        cols[QPKD] = if tr.blake3.is_empty() {
            vec![F128::ZERO]
        } else {
            let blocks: Vec<_> = tr
                .blake3
                .iter()
                .map(|r| crate::blake3_flock::compression([r.va0, r.va1], [r.vb0, r.vb1]))
                .collect();
            crate::blake3_flock::build_qpkd(&blocks)
        };

        if prof {
            eprintln!("[build] fill cols   : {:>7.2} ms", t_fill.elapsed().as_secs_f64() * 1e3);
        }

        // The public layout (flush/count blocks, per-column padding, placements,
        // boundary, taus) is a pure function of the program + announced sizes +
        // public input, with no committed witness; reconstruct it here so the
        // prover and verifier share exactly the same structure (§7, §8).
        let row_counts = [
            tr.xor.len(),
            tr.mul.len(),
            tr.set.len(),
            tr.deref.len(),
            tr.jump.len(),
            tr.blake3.len(),
        ];
        assert!(
            row_counts.iter().all(|&r| r <= 1 << MAX_LOG_ROWS),
            "a table exceeds 2^{MAX_LOG_ROWS} rows"
        );
        let pi = [exec.mem[0], exec.mem[1]];
        let l = layout(&self.prog, log_mem, row_counts, pi);

        // Pad each per-opcode table to its power-of-two row count: count columns
        // with g^0 = 1, every other column with 0 (§e2e-pad). A default padding
        // row (counts 1, else 0) flushes tuples that do not self-cancel; the
        // verifier divides them out of the bus product (§sec:gp). The shared
        // columns (MEM, MFCNT, BFCNT) keep their natural 2^h / 2^log_bytecode lengths.
        // Pad to `2^taus[t]` (= `next_pow2(row_counts[t])` for every table except
        // BLAKE3, which `layout` rounds up to flock's `2^n_log`).
        for (t, table) in tables::tables().iter().enumerate() {
            let n = 1usize << l.taus[t];
            for c in sch.base[t]..sch.base[t] + table.n_committed_columns() {
                cols[c].resize(n, l.pad[c]);
            }
        }
        // (`execute` already asserts the run halts at the sentinel (pc, fp) =
        // (g^{B-1}, 0), exactly the boundary the public layout derives.)
        let q = witness::stack_q(&cols, &l.placements, l.m);
        Witness {
            cols,
            q,
            layout: l,
            log_mem,
            row_counts,
        }
    }
}

/// The whole proof is the transcript: a scalar stream plus the PCS hint
/// channels (see [`crate::transcript::Proof`]).
pub use crate::transcript::Proof;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Bus(leaf::Error),
    Constraint(usize, constraints::Error),
    Open(pcs::Error),
    PublicInput,
    Transcript(crate::transcript::Error),
    /// flock's BLAKE3 R1CS validity sub-proof failed to verify.
    Blake3(flock_prover::verifier::VerifyError),
    /// The BLAKE3 attachment is missing or inconsistent with the announced
    /// BLAKE3 row count. (Constant pinning + value binding are checked as PCS
    /// claims and surface as [`Error::Open`].)
    Blake3Missing,
}

/// Lift each table's constraint evals (at its zerocheck point `rho`) to global
/// column claims, offsetting the table's local constraint columns by its base.
fn constraint_claims(table_claims: &[constraints::Claims]) -> Vec<ColumnClaim> {
    let sch = schema();
    let mut v = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        for (k, &c) in table.constraint_columns().iter().enumerate() {
            v.push(ColumnClaim {
                col: sch.base[t] + c,
                point: table_claims[t].rho.clone(),
                value: table_claims[t].evals[k],
            });
        }
    }
    v
}

/// BLAKE3↔`q_pkd` binding claims, all point-evals of the single committed stack
/// (§blake3_flock), at the random instance point `rho`:
///
/// - per value word `w`: `value_col_w(rho) = v_words[w]` AND `q_pkd(slot_w‖rho)
///   = v_words[w]` — same value ⟹ the bus-tied value column equals the proven
///   `q_pkd` slice;
/// - per pin slot: `q_pkd(pin_slot‖rho) = pin_col(rho)` against the PUBLIC
///   constant column (`cv = IV`, counter/blen/flags = 0/64/11), pinning the
///   compression to a real BLAKE3-of-64-bytes.
///
/// `v_words` are transmitted (prover computes, verifier reads); the pin values
/// are public, so both sides compute them. Symmetric across prove/verify.
fn blake3_binding_claims(rho: &[F128], v_words: &[F128; 6], n_blocks: usize) -> Vec<ColumnClaim> {
    use crate::blake3_flock::{PIN_SLOTS, SLOTS, pin_constants, slot_point};
    let base = schema().base[tables::BLAKE3_TABLE];
    let mut v = Vec::with_capacity(2 * 6 + PIN_SLOTS.len());
    for (i, &local) in tables::BLAKE3_VALUE_COLS.iter().enumerate() {
        v.push(ColumnClaim {
            col: base + local,
            point: rho.to_vec(),
            value: v_words[i],
        });
        v.push(ColumnClaim {
            col: QPKD,
            point: slot_point(SLOTS[i], rho),
            value: v_words[i],
        });
    }
    let pin = pin_constants();
    let n_slots = 1usize << rho.len();
    for (k, &pslot) in PIN_SLOTS.iter().enumerate() {
        let mut col = vec![F128::ZERO; n_slots];
        for slot in col.iter_mut().take(n_blocks) {
            *slot = pin[k];
        }
        v.push(ColumnClaim {
            col: QPKD,
            point: slot_point(pslot, rho),
            value: crate::multilinear::mle_eval(&col, rho),
        });
    }
    v
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode counts `[XOR, MUL, SET, DEREF, JUMP, BLAKE3]`, and the
/// committed witness size — the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize,
    pub counts: [usize; 6],
    pub committed: usize,
}

/// Prove the program on the given public input: run it (witness generation),
/// then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof and the
/// run [`Stats`].
pub fn prove(program: &Program, public_input: [F128; 2]) -> (Proof, Stats) {
    let prof = std::env::var("LEANVM_PROFILE").is_ok();
    let ms = |t: std::time::Instant| t.elapsed().as_secs_f64() * 1e3;
    let exec = program.execute(public_input);
    let cycles = exec.cycles;
    let w = program.build(&exec);
    let counts = w.row_counts;
    let committed_size: usize = w.cols.iter().map(|c| c.len()).sum(); // real data, before zero-pad to 2^m
    let mut ps = ProverState::new(b"leanvm-b");

    // Bind the public statement, then the witness commitment, before sampling
    // any challenge.
    announce_public(&mut ps, &w.layout.pi, w.log_mem, w.row_counts);
    let t = std::time::Instant::now();
    let committed = pcs::commit(&mut ps, &w.q);
    if prof {
        eprintln!("[prove] commit      : {:>7.2} ms", ms(t));
    }

    // BLAKE3 ↔ flock (§blake3_flock), single PCS: q_pkd is a column in `w.q`. The
    // binding point `rho` is sampled right after the commitment; flock's R1CS
    // validity and EVERY leanVM point claim are discharged together by ONE
    // BaseFold over this commitment (below). Mirrored in `verify`.
    let blake3_rho = if !exec.trace.blake3.is_empty() {
        Some(ps.sample_vec(crate::blake3_flock::n_blocks_log(exec.trace.blake3.len())))
    } else {
        None
    };

    let t = std::time::Instant::now();
    let l = &w.layout;
    let bus_claims = leaf::prove_balance(&l.push, &l.pull, &l.count, &w.cols, &mut ps);
    if prof {
        eprintln!("[prove] bus(grand-p): {:>7.2} ms", ms(t));
    }
    let t = std::time::Instant::now();
    let sch = schema();
    let mut table_claims = Vec::new();
    for (ti, table) in tables::tables().iter().enumerate() {
        let involved = table.constraint_columns();
        let position = tables::column_positions(involved);
        let cols: Vec<Column> = involved.iter().map(|&c| w.cols[sch.base[ti] + c].clone()).collect();
        table_claims.push(constraints::prove(
            &cols,
            |eta, vals| table.eval_constraint(eta, &tables::Cols::new(vals, &position)),
            &mut ps,
        ));
    }
    if prof {
        eprintln!("[prove] constraints : {:>7.2} ms", ms(t));
    }

    let mut claims = bus_claims;
    claims.extend(constraint_claims(&table_claims));
    claims.push(bind_pi_prove(&w, &mut ps));
    if let Some(rho) = &blake3_rho {
        // Transmit the six value-column evals v_w = value_col_w(rho); each pairs a
        // value-column claim and a q_pkd-slot claim (same value) — the binding.
        let base = sch.base[tables::BLAKE3_TABLE];
        let mut v_words = [F128::ZERO; 6];
        for (i, &local) in tables::BLAKE3_VALUE_COLS.iter().enumerate() {
            v_words[i] = crate::multilinear::mle_eval(&w.cols[base + local], rho);
            ps.write_scalar(v_words[i]);
        }
        claims.extend(blake3_binding_claims(rho, &v_words, exec.trace.blake3.len()));
    }
    let slots = slot_claims(&w.layout, &claims);

    // ONE opening of the single commitment. With BLAKE3: flock's validity (the
    // ring-switched ab/c) AND every point claim (as full-stack `stack_pd`) fold
    // into one BaseFold. Without BLAKE3: the plain point-batch open.
    let t = std::time::Instant::now();
    let blake3_attach = if blake3_rho.is_some() {
        let blocks: Vec<flock_prover::r1cs_hashes::blake3::Compression> = exec
            .trace
            .blake3
            .iter()
            .map(|r| crate::blake3_flock::compression([r.va0, r.va1], [r.vb0, r.vb1]))
            .collect();
        let offset = w.layout.placements[QPKD].offset;
        let stack_pd: Vec<(Vec<F128>, F128)> =
            slots.iter().map(|s| (stack_point_of(s, w.layout.m), s.value)).collect();
        let b3proof = crate::blake3_flock::prove_validity_stacked(
            &blocks,
            &w.q,
            offset,
            &committed.prover_data,
            &committed.commitment,
            &stack_pd,
            &mut ps,
        );
        Some(crate::blake3_flock::Blake3Attachment {
            n_blocks: blocks.len(),
            proof: b3proof,
        })
    } else {
        pcs::open(&mut ps, &committed, &w.q, &slots);
        None
    };
    if prof {
        eprintln!("[prove] open        : {:>7.2} ms", ms(t));
    }
    let mut proof = ps.into_proof();
    proof.blake3 = blake3_attach;
    (
        proof,
        Stats {
            cycles,
            counts,
            committed: committed_size,
        },
    )
}

/// Bind the public input `m[0], m[1]` (256 bits) to the committed memory (§8):
/// open the MEM column at `(r, 0,…,0)` and (verifier-side) check it equals the
/// MLE of the public pair at `r`. Here we emit the prover's claim.
fn bind_pi_prove(w: &Witness, ps: &mut ProverState) -> ColumnClaim {
    ps.observe_scalars(&w.layout.pi);
    let r = ps.sample();
    let h = w.layout.placements[MEM].n_vars;
    let mut point = vec![F128::ZERO; h];
    point[0] = r;
    let value = crate::multilinear::mle_eval(&w.cols[MEM], &point);
    ps.write_scalar(value);
    ColumnClaim { col: MEM, point, value }
}

/// Verifier side of [`bind_pi_prove`]: read the claimed `M(r,0,…,0)` and check it
/// equals the public input's MLE `interp(m[0], m[1], r)`.
fn bind_pi_verify(l: &Layout, vs: &mut VerifierState) -> Result<ColumnClaim, Error> {
    vs.observe_scalars(&l.pi);
    let r = vs.sample();
    let h = l.placements[MEM].n_vars;
    let mut point = vec![F128::ZERO; h];
    point[0] = r;
    let value = vs.next_scalar().map_err(Error::Transcript)?;
    if value != crate::multilinear::interp(l.pi[0], l.pi[1], r) {
        return Err(Error::PublicInput);
    }
    Ok(ColumnClaim { col: MEM, point, value })
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs — never the prover's witness.
pub fn verify(program: &Program, public_input: &[F128; 2], proof: &Proof) -> Result<(), Error> {
    let mut vs = VerifierState::new(b"leanvm-b", proof);
    let l = read_public(&mut vs, program, public_input)?;
    let root = pcs::read_commitment(&mut vs).map_err(Error::Transcript)?;

    // BLAKE3 ↔ flock (single PCS): sample the binding point `rho` right after the
    // commitment (mirroring `prove`); flock's R1CS validity and every leanVM
    // point claim are verified together by ONE BaseFold opening at the end.
    let n_b3 = l.row_counts[tables::BLAKE3_TABLE];
    let blake3_rho = if n_b3 > 0 {
        let att = proof.blake3.as_ref().ok_or(Error::Blake3Missing)?;
        if att.n_blocks != n_b3 {
            return Err(Error::Blake3Missing);
        }
        Some(vs.sample_vec(crate::blake3_flock::n_blocks_log(n_b3)))
    } else {
        if proof.blake3.is_some() {
            return Err(Error::Blake3Missing); // attachment without any BLAKE3 rows
        }
        None
    };

    let bus_claims = leaf::verify_balance(&l.push, &l.pull, &l.count, &l.pad, &mut vs).map_err(Error::Bus)?;

    let mut table_claims = Vec::new();
    for (ti, table) in tables::tables().iter().enumerate() {
        let involved = table.constraint_columns();
        let position = tables::column_positions(involved);
        let cl = constraints::verify(
            l.taus[ti],
            involved.len(),
            |eta, vals| table.eval_constraint(eta, &tables::Cols::new(vals, &position)),
            &mut vs,
        )
        .map_err(|e| Error::Constraint(ti, e))?;
        table_claims.push(cl);
    }

    let mut claims = bus_claims;
    claims.extend(constraint_claims(&table_claims));
    claims.push(bind_pi_verify(&l, &mut vs)?);
    if let Some(rho) = &blake3_rho {
        let mut v_words = [F128::ZERO; 6];
        for v in &mut v_words {
            *v = vs.next_scalar().map_err(Error::Transcript)?;
        }
        claims.extend(blake3_binding_claims(rho, &v_words, n_b3));
    }
    let slots = slot_claims(&l, &claims);

    // ONE opening of the single commitment, mirroring `prove`.
    if blake3_rho.is_some() {
        let att = proof.blake3.as_ref().ok_or(Error::Blake3Missing)?;
        let offset = l.placements[QPKD].offset;
        let commitment = pcs::commitment_from_root(root, l.m);
        let stack_pd: Vec<(Vec<F128>, F128)> = slots.iter().map(|s| (stack_point_of(s, l.m), s.value)).collect();
        crate::blake3_flock::verify_validity_stacked(n_b3, &commitment, offset, &stack_pd, &att.proof, &mut vs)
            .map_err(Error::Blake3)?;
    } else {
        pcs::verify(&mut vs, &slots, l.m, &root).map_err(Error::Open)?;
    }
    vs.finish().map_err(Error::Transcript)
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
fn slot_claims(l: &Layout, claims: &[ColumnClaim]) -> Vec<pcs::SlotClaim> {
    claims
        .iter()
        .map(|c| pcs::SlotClaim {
            offset: l.placements[c.col].offset,
            low_point: c.point.clone(),
            value: c.value,
        })
        .collect()
}

/// The full `m`-variable point of a located slot claim in the stacked witness:
/// the within-column `low_point` (low coords) followed by the column's boolean
/// selector (high coords). Used to express leanVM's point claims as full-stack
/// `packed_direct` evaluations in the single fused BLAKE3 opening (§blake3_flock).
fn stack_point_of(slot: &pcs::SlotClaim, m: usize) -> Vec<F128> {
    let mut p = slot.low_point.clone();
    let sel = slot.offset >> slot.low_point.len();
    for k in 0..(m - slot.low_point.len()) {
        p.push(F128::new(((sel >> k) & 1) as u64, 0));
    }
    p
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A hand-built straight-line program exercising the `BLAKE3` table: set up
    /// the two 256-bit inputs (`a` at cells 2,3 and `b` at cells 4,5), hash them
    /// into the output `c` (cells 6,7), and halt at the sentinel. The compression
    /// is unproven, but the memory / state / bytecode bus interactions must still
    /// balance, so this proves and verifies end-to-end.
    #[test]
    fn blake3_proves_and_verifies() {
        let x0 = F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
        let x1 = F128::new(0x1111_2222_3333_4444, 0x5555_6666_7777_8888);
        let y0 = F128::new(0xdead_beef_cafe_babe, 0x0badf00d_0badf00d);
        let y1 = F128::new(0x9999_aaaa_bbbb_cccc, 0xdddd_eeee_ffff_0000);

        // 8 slots (power of two). Slots 4 and 6 are filler SETs whose only job is to
        // step the pc so the last executed instruction lands at slot 6 (→ pc 7,
        // halt). Slot 7 is the never-executed sentinel.
        let prog = vec![
            Op::Set { o: 2, k: x0 },
            Op::Set { o: 3, k: x1 },
            Op::Set { o: 4, k: y0 },
            Op::Set { o: 5, k: y1 },
            Op::Set { o: 8, k: F128::ONE },
            Op::Blake3 { a: 2, b: 4, c: 6 },
            Op::Set { o: 9, k: F128::ONE },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel (never executed)
        ];
        let program = Program {
            prog,
            pc0: 0,
            fp0: 0,
            hints: HashMap::new(),
            main_frame: 10,
        };

        let pi = [F128::new(7, 0), F128::new(11, 0)];
        let exec = program.execute(pi);

        // The output cells hold the digest of the two inputs (the prover computes
        // a definite value even though nothing constrains it).
        let (d0, d1) = blake3_compress(x0, x1, y0, y1);
        assert_eq!(exec.mem[6], d0);
        assert_eq!(exec.mem[7], d1);
        assert_eq!(exec.trace.blake3.len(), 1);

        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        // The proof carries flock's BLAKE3 sub-proof (validity + slot openings).
        assert!(proof.blake3.is_some(), "BLAKE3 program must attach a flock proof");
        verify(&program, &pi, &proof).expect("BLAKE3 program verifies");
    }

    /// Tampering flock's validity sub-proof (its BaseFold `final_b`, opened over
    /// the same stacked commitment) must make verification fail.
    #[test]
    fn blake3_rejects_tampered_validity() {
        let prog = vec![
            Op::Set { o: 2, k: F128::new(0xABCD, 0x1234) },
            Op::Set { o: 3, k: F128::new(0x5678, 0x9999) },
            Op::Set { o: 4, k: F128::new(0x1111, 0x2222) },
            Op::Set { o: 5, k: F128::new(0x3333, 0x4444) },
            Op::Set { o: 8, k: F128::ONE },
            Op::Blake3 { a: 2, b: 4, c: 6 },
            Op::Set { o: 9, k: F128::ONE },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 10);
        let pi = [F128::new(7, 0), F128::new(11, 0)];
        let (mut proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        let att = proof.blake3.as_mut().expect("flock attachment");
        att.proof.open.basefold.final_b += F128::ONE;
        assert!(
            verify(&program, &pi, &proof).is_err(),
            "tampered BLAKE3 validity proof must be rejected"
        );
    }

    /// A program with no BLAKE3 instructions proves and verifies with no flock
    /// attachment (the `N = 0` path).
    #[test]
    fn non_blake3_program_verifies_without_attachment() {
        let prog = vec![
            Op::Set { o: 2, k: F128::new(5, 0) },
            Op::Set { o: 3, k: F128::new(6, 0) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [F128::new(1, 0), F128::new(2, 0)];
        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 0, "no BLAKE3 rows");
        assert!(proof.blake3.is_none(), "no BLAKE3 ⇒ no flock attachment");
        verify(&program, &pi, &proof).expect("non-BLAKE3 program verifies");
    }
}
