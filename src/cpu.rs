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
use crate::field::{F128, G, g_pow};
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
/// verifier rejects any announced `h` outside the range. `MIN_LOG_MEM` is also
/// the static cap on range-check bounds (`compiler::Stmt::AssertLt`): a bound
/// `≤ 2^MIN_LOG_MEM` keeps the complement argument sound for every memory size
/// the prover may announce.
pub(crate) const MIN_LOG_MEM: usize = 16;
const MAX_LOG_MEM: usize = 32;

/// Each per-opcode table holds at most `2^MAX_LOG_ROWS` rows (executed
/// instructions of that opcode).
const MAX_LOG_ROWS: usize = 32;

/// A binding digest of the program bytecode (BLAKE3 of every instruction's
/// canonical encoding — opcode, operands, and the DEREF store-mode), as two field
/// elements. Seeded into the transcript alongside the public input, so EVERY
/// challenge depends on the exact program.
///
/// Without this the program's instruction content would enter verification only
/// through the bytecode bus's `Public`-coordinate MLE evaluation at the GKR point
/// `ζ` — a single point an attacker recovers from a finished proof. It could then
/// craft a different program `P'` agreeing with `P`'s bytecode columns at that one
/// `ζ` and re-present the same proof for `P'` (adaptive-statement forgery). Seeding
/// `H(program)` before any challenge makes the whole statement — (program, public
/// input) — bound up front, so a different program yields a different sponge from
/// the very first squeeze. Both sides hold the program, so both compute this
/// identically; the announced sizes ride the stream (`announce_public`).
fn program_digest(prog: &[Op]) -> [F128; 2] {
    let mut h = blake3::Hasher::new();
    h.update(b"leanvm-b/program/v0");
    h.update(&(prog.len() as u64).to_le_bytes());
    for op in prog {
        let (tag, a, b, c, k) = match *op {
            Op::Xor { a, b, c } => (0u8, a, b, c, F128::ZERO),
            Op::Mul { a, b, c } => (1, a, b, c, F128::ZERO),
            Op::Set { o, k } => (2, o, 0, 0, k),
            Op::Deref { alpha, beta, gamma, mode } => {
                (3 + mode as u8, alpha, beta, gamma, F128::ZERO) // mode ∈ {Cell,Pc,Fp} ⇒ tag 3/4/5
            }
            Op::Jump { oc, od, of } => (6, oc, od, of, F128::ZERO),
            Op::Blake3 { a, b, c } => (7, a, b, c, F128::ZERO),
        };
        h.update(&[tag]);
        h.update(&a.to_le_bytes());
        h.update(&b.to_le_bytes());
        h.update(&c.to_le_bytes());
        h.update(&k.lo.to_le_bytes());
        h.update(&k.hi.to_le_bytes());
    }
    let d = *h.finalize().as_bytes();
    let w = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F128::new(w(0), w(8)), F128::new(w(16), w(24))]
}

/// The transcript seed: the public statement bound before any challenge — the
/// public input `pi` followed by the program's stored [`digest`](Program::digest)
/// (computed once at assembly, not re-hashed here). Both sides build it identically.
fn transcript_seed(program: &Program, pi: &[F128; 2]) -> [F128; 4] {
    [pi[0], pi[1], program.digest[0], program.digest[1]]
}

/// Announce the prover's per-table log-sizes (`log_mem` + the six `row_counts`) by
/// writing them onto the scalar stream (which binds them into the sponge and lets
/// the verifier reconstruct the layout). The public statement (program + input) is
/// not announced here — it seeds the transcript at construction (see
/// [`transcript_seed`]). The boundary states and per-table log-sizes (`taus`) are
/// derived (constants from the program, and `padlen(row_counts)`), so they need no
/// separate binding.
fn announce_public(ps: &mut ProverState, log_mem: usize, row_counts: [usize; 6]) {
    ps.add_scalar(F128::new(log_mem as u64, 0));
    for r in row_counts {
        ps.add_scalar(F128::new(r as u64, 0));
    }
}

/// Verifier side of [`announce_public`]: read the seven announced sizes from the
/// stream and reconstruct the public [`Layout`] from the program + sizes + public
/// input. (The public input was already bound by seeding the transcript.)
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
        || row_counts.iter().any(|&r| r >= (1usize << MAX_LOG_ROWS))
    {
        return Err(Error::PublicInput);
    }
    let l = layout(&prog.prog, log_mem, row_counts, *public_input);
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
    /// A binding digest of `prog` ([`program_digest`]), computed once at assembly
    /// and seeded into the transcript so every challenge depends on the exact
    /// program. Trusted to match `prog` — always set by [`Program::assemble`] from
    /// the bytecode, so a `Program` value cannot carry a digest inconsistent with
    /// its own `prog`.
    pub(crate) digest: [F128; 2],
    /// Prover-side frame/buffer allocation hints (keyed by global pc) and the
    /// size of `main`'s frame — the nondeterminism [`Program::execute`] needs to
    /// run the program. Public verification (\S `verify`) ignores them.
    pub(crate) hints: HashMap<u32, Vec<crate::compiler::RHint>>,
    pub(crate) main_frame: u32,
}

impl Program {
    /// Assemble a [`Program`], computing its bytecode [`digest`](Program::digest)
    /// from `prog`. The single funnel for construction, so the digest is always
    /// consistent with the bytecode.
    pub(crate) fn assemble(
        prog: Vec<Op>,
        pc0: u32,
        fp0: u32,
        hints: HashMap<u32, Vec<crate::compiler::RHint>>,
        main_frame: u32,
    ) -> Self {
        let digest = program_digest(&prog);
        Self { prog, pc0, fp0, digest, hints, main_frame }
    }
}

impl Program {
    /// Assemble a program directly from a fixed bytecode vector, starting at
    /// `(pc, fp) = (0, 0)` with no allocation hints. Suitable for straight-line
    /// programs that never change the frame pointer and touch only the first
    /// `main_frame` memory cells (so the prover needs no nondeterministic frame
    /// allocation). `prog.len()` must be a power of two with a never-executed
    /// sentinel in its last slot — the run halts on reaching `g^{len-1}` (§state).
    pub fn from_bytecode(prog: Vec<Op>, main_frame: u32) -> Self {
        Self::assemble(prog, 0, 0, HashMap::new(), main_frame)
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
        let g_step = G;

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
// BLAKE3, else a size-1 dummy (kept in the static schema). It is the SOLE copy of
// the input/output words: the VM's BLAKE3 value columns are virtual and their
// memory-bus claims route to `q_pkd` slots (§blake3_flock), so nothing duplicates
// them. flock's R1CS validity is discharged by a basefold over this commitment.
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
/// is `2^taus[t]` (its padded log-row-count). `None` marks a **virtual**
/// (uncommitted) column. Depends only on the public sizes, so the verifier can
/// reconstruct the placements.
///
/// The BLAKE3 value columns (`va0..vc1`) are virtual when BLAKE3 ran: `q_pkd`
/// already holds those words at fixed packed slots, so committing them again is
/// redundant. Their memory-bus claims route directly to `q_pkd` slot evaluations
/// (see [`slot_claims`] / [`blake3_flock::slot_point`]), which both binds them to
/// the proven witness AND eliminates the separate value-binding sub-protocol.
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; 6], n_blake3: usize) -> Vec<Option<usize>> {
    let sch = schema();
    let mut k = vec![Some(0usize); sch.n];
    k[MEM] = Some(log_mem);
    k[MFCNT] = Some(log_mem);
    k[BFCNT] = Some(log_bytecode);
    // q_pkd: `2^(K_LOG+n_log-7)` F128 coords, always ≥ 1 instance (`qpkd_kappa`
    // floors `n_blake3` at 1 — padding instance for a no-BLAKE3 program).
    k[QPKD] = Some(crate::blake3_flock::qpkd_kappa(n_blake3));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some(taus[t]));
    }
    // BLAKE3 value columns are ALWAYS virtual (read from q_pkd, never committed).
    let b3 = sch.base[tables::BLAKE3_TABLE];
    for &c in &tables::BLAKE3_VALUE_COLS {
        k[b3 + c] = None;
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
    // The BLAKE3 table is ALWAYS sized to flock's `2^n_log` instance count
    // (`max(count,1)`, lincheck floor ≥ 8) so its per-instance (virtual) value
    // columns share `q_pkd`'s instance cube — a value-column bus claim at instance
    // point `r` maps to the `q_pkd` slot at `slot_point(slot, r)` (`slot_claims`).
    taus[tables::BLAKE3_TABLE] = crate::blake3_flock::n_blocks_log(row_counts[tables::BLAKE3_TABLE].max(1));

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
    // value columns pad with that digest, not 0 — the memory bus flushes these
    // (virtual) columns, and their padding rows must equal `q_pkd`'s padding slots
    // so the default-padding surplus divides out and the routed claims agree.
    // Inputs/counts keep their 0/1 defaults. Always applied (the BLAKE3 table is
    // always present, all-padding for a no-BLAKE3 program).
    {
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
        // flock's packed BLAKE3 witness q_pkd, ALWAYS committed in this same stack:
        // built from the executed BLAKE3 rows in order (row j = flock instance j),
        // padded to `2^n_blocks_log(max(count,1))` all-padding instances — so a
        // program with no BLAKE3 still carries a single padding instance.
        cols[QPKD] = {
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
            let base = sch.base[t];
            for (i, col) in cols[base..base + table.n_committed_columns()].iter_mut().enumerate() {
                col.resize(n, l.pad[base + i]);
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
    /// flock's BLAKE3 R1CS validity sub-proof failed to verify. (A missing or
    /// malformed sub-proof surfaces as [`Error::Transcript`] when the shared
    /// `stream`/`openings` fail to reconstruct or fully consume.)
    Blake3(flock_prover::verifier::VerifyError),
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

/// If `col` is a BLAKE3 **value** column (global index), its `q_pkd` packed slot.
/// These columns are virtual (uncommitted): their memory-bus evaluation claims
/// are re-routed to `q_pkd` slot evaluations, which is the whole binding — the
/// bus-tied value IS the proven `q_pkd` word, no separate check needed.
fn blake3_value_slot(col: usize) -> Option<usize> {
    let base = schema().base[tables::BLAKE3_TABLE];
    tables::BLAKE3_VALUE_COLS
        .iter()
        .position(|&c| base + c == col)
        .map(|i| crate::blake3_flock::SLOTS[i])
}

/// The instance-cube point the BLAKE3 constant pins are checked at: any BLAKE3
/// value-column bus claim's point (the memory bus's push-side GKR output, an
/// FS-random, post-commit, `n_log`-dim point). Reusing it avoids a dedicated
/// binding challenge. `claims` must already hold the bus claims, and BLAKE3 must
/// have run (so a value-column claim exists). Deterministic and identical across
/// prove/verify (both build the bus claims in the same order).
fn blake3_pin_point(claims: &[ColumnClaim]) -> Vec<F128> {
    claims
        .iter()
        .find(|c| blake3_value_slot(c.col).is_some())
        .expect("BLAKE3 ran ⇒ a value-column bus claim exists")
        .point
        .clone()
}

/// MLE of `[1;n, 0;…]` at `point` (LSB-first), i.e. `Σ_{j<n} eq(j, point)`, in
/// `O(point.len()²)` — one term per set bit of `n` (an aligned `2^t` block sums to
/// `eq` of its high bits), never materializing the `2^point.len()` vector.
fn mle_of_ones_then_zeros(n: usize, point: &[F128]) -> F128 {
    let l = point.len();
    debug_assert!(n <= 1usize << l);
    let mut sum = F128::ZERO;
    let mut base = 0usize; // low indices already covered
    // Include t = l so the full cube (n = 2^l, bit l set) is one block whose free
    // coords all sum to 1; `point[l..]` is then empty ⇒ eq = 1.
    for t in (0..=l).rev() {
        if (n >> t) & 1 == 1 {
            // Block [base, base + 2^t): its high bits (coords t..l) are `base >> t`.
            let a = base >> t;
            let mut e = F128::ONE;
            for (i, &x) in point[t..].iter().enumerate() {
                e *= if (a >> i) & 1 == 1 { x } else { F128::ONE + x };
            }
            sum += e;
            base += 1 << t;
        }
    }
    sum
}

/// BLAKE3 `q_pkd` **pin** claims at the instance point `point` (a memory-bus
/// point, see [`blake3_pin_point`]): per pin slot, `q_pkd(pin_slot‖point) =
/// pin_col(point)` against the PUBLIC constant column (`cv = IV`,
/// counter/blen/flags = 0/64/11), pinning the compression to a real
/// BLAKE3-of-64-bytes. The pin column is `pin[k]` on the first `n_blocks`
/// instances and `0` on padding, so its MLE is `pin[k] · Σ_{j<n_blocks} eq(j,
/// point)` — computed in `O(n_log²)` by [`mle_of_ones_then_zeros`], never materialized. The
/// input/output words are NOT pinned here — they bind via the memory bus routing
/// to `q_pkd` (see [`blake3_value_slot`]). Values are public; symmetric across
/// prove/verify.
fn blake3_pin_claims(point: &[F128], n_blocks: usize) -> Vec<ColumnClaim> {
    use crate::blake3_flock::{PIN_SLOTS, pin_constants, slot_point};
    let pin = pin_constants();
    let prefix = mle_of_ones_then_zeros(n_blocks, point);
    let mut v = Vec::with_capacity(PIN_SLOTS.len());
    for (k, &pslot) in PIN_SLOTS.iter().enumerate() {
        v.push(ColumnClaim {
            col: QPKD,
            point: slot_point(pslot, point),
            value: pin[k] * prefix,
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
    // Real committed data, before zero-pad to 2^m. Virtual columns (the BLAKE3
    // value columns) carry data for the bus but are NOT committed, so exclude them.
    let committed_size: usize = w
        .cols
        .iter()
        .zip(&w.layout.placements)
        .filter(|(_, p)| !p.is_virtual())
        .map(|(c, _)| c.len())
        .sum();
    // The public statement (program digest + input) seeds the transcript, so
    // every challenge depends on the exact program and public input.
    let mut ps = ProverState::new(b"leanvm-b", &transcript_seed(program, &public_input));

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.log_mem, w.row_counts);
    let t = std::time::Instant::now();
    let committed = pcs::commit(&mut ps, &w.q);
    if prof {
        eprintln!("[prove] commit      : {:>7.2} ms", ms(t));
    }

    // BLAKE3 ↔ flock (§blake3_flock), single PCS: q_pkd is ALWAYS a column in
    // `w.q` (≥1 instance — a program with no BLAKE3 carries one padding instance,
    // so the proof shape is uniform and there is no has/hasn't-BLAKE3 fork). flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE
    // Ligerito over this commitment (below). The input/output words bind via the
    // memory bus (virtual value columns route to q_pkd); the constant pins reuse a
    // bus point, so no dedicated binding challenge is drawn. Mirrored in `verify`.
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
    claims.push(bind_pi_claim(ps.sample(), &w.layout.placements, &w.layout.pi));
    // The input/output words bind via the memory bus (value columns are virtual and
    // route to q_pkd, see `slot_claims`); only q_pkd's constant slots need pinning,
    // at a memory-bus point. The pin prefix uses the REAL BLAKE3 count (0 pins
    // nothing — padding instances hold 0).
    let pin_point = blake3_pin_point(&claims);
    claims.extend(blake3_pin_claims(&pin_point, exec.trace.blake3.len()));
    let slots = slot_claims(&w.layout, &claims);

    // Run flock's reduction (zerocheck + lincheck) over the executed compressions
    // (or a single padding instance when none ran); it returns the `(ab, c)`
    // validity claims on the committed `q_pkd`, discharged by the PCS below in the
    // SAME Ligerito as every leanVM point claim (the point claims become the
    // opener's `stack_pd`).
    let t = std::time::Instant::now();
    use flock_prover::r1cs_hashes::blake3::Compression;
    let blocks: Vec<Compression> = if exec.trace.blake3.is_empty() {
        vec![crate::blake3_flock::padding_compression()]
    } else {
        exec.trace
            .blake3
            .iter()
            .map(|r| crate::blake3_flock::compression([r.va0, r.va1], [r.vb0, r.vb1]))
            .collect()
    };
    let (_z_packed, zc, lc, reduced) = crate::blake3_flock::prove_reduction(&blocks, &committed.commitment, &mut ps);
    let offset = w.layout.placements[QPKD].offset;
    let ring = crate::blake3_flock::ring_switch_open(blocks.len(), offset, &reduced);
    let mixed_open = pcs::open(&mut ps, &committed, &w.q, &slots, &ring);
    // Carry flock's sub-proof on the shared channels: its scalar reduction on the
    // `stream` (raw transport), its Ligerito on the `openings` hint channel.
    crate::blake3_flock::write_stack_proof(&mut ps, zc, lc, mixed_open);
    if prof {
        eprintln!("[prove] open        : {:>7.2} ms", ms(t));
    }
    (
        ps.into_proof(),
        Stats {
            cycles,
            counts,
            committed: committed_size,
        },
    )
}

/// The public-input binding claim (§8): `MEM(r, 0,…,0) = interp(m[0], m[1], r)`.
/// The value is a deterministic function of the (seeded) public input `pi` and the
/// challenge `r`, so it is NOT transmitted — both sides compute it, and the single
/// opening proves the committed `MEM` really evaluates to it (a memory whose first
/// two cells disagree with `pi` then fails the opening). `pi` is already bound (the
/// seed), so `r` is sampled directly. `placements`/`pi` come from the prover's or
/// verifier's layout; both build the byte-identical claim.
fn bind_pi_claim(r: F128, placements: &[witness::Placement], pi: &[F128; 2]) -> ColumnClaim {
    let mut point = vec![F128::ZERO; placements[MEM].n_vars];
    point[0] = r;
    ColumnClaim { col: MEM, point, value: crate::multilinear::interp(pi[0], pi[1], r) }
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs — never the prover's witness.
pub fn verify(program: &Program, public_input: &[F128; 2], proof: &Proof) -> Result<(), Error> {
    let mut vs = VerifierState::new(b"leanvm-b", proof, &transcript_seed(program, public_input));
    let l = read_public(&mut vs, program, public_input)?;
    let root = pcs::read_commitment(&mut vs).map_err(Error::Transcript)?;

    // BLAKE3 ↔ flock (single PCS): flock's R1CS validity and every leanVM point
    // claim are verified together by ONE Ligerito opening at the end. The executed-
    // BLAKE3 count is public (announced); its flock sub-proof rides the shared
    // `stream`/`openings`, and presence is enforced by consumption below plus
    // `vs.finish()` (a proof with `n_b3 = 0` but trailing flock data, or vice versa,
    // fails to fully consume). No dedicated binding challenge: the input/output
    // words bind via the memory bus, the pins reuse a bus point.
    let n_b3 = l.row_counts[tables::BLAKE3_TABLE];

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
    claims.push(bind_pi_claim(vs.sample(), &l.placements, &l.pi));
    // Value columns are virtual (routed to q_pkd via `slot_claims`); only the
    // constant pins are added here, at a memory-bus point, mirroring `prove`. The
    // pin prefix uses the REAL count `n_b3` (0 pins nothing).
    let pin_point = blake3_pin_point(&claims);
    claims.extend(blake3_pin_claims(&pin_point, n_b3));
    // Read flock's BLAKE3 sub-proof off the shared channels (mirrors prove's
    // `write_stack_proof`): the scalar reduction from the `stream` as raw transport
    // (right after the last bound scalar), its Ligerito from `openings`.
    let (zerocheck, lincheck, open) = crate::blake3_flock::read_stack_proof(&mut vs).map_err(Error::Transcript)?;
    let slots = slot_claims(&l, &claims);

    // Replay flock's reduction to recover its `(ab, c)` validity claims on q_pkd,
    // then verify them alongside every point claim in the ONE Ligerito opening
    // (mirroring `prove`). `n_blocks = max(n_b3, 1)` — always ≥ 1 instance.
    let n_blocks = n_b3.max(1);
    let offset = l.placements[QPKD].offset;
    let (ab, c) = crate::blake3_flock::verify_reduction(n_blocks, &root, l.m, &zerocheck, &lincheck, &mut vs)
        .map_err(Error::Blake3)?;
    let ring = crate::blake3_flock::ring_switch_verify(n_blocks, offset, ab, c, &open);
    pcs::verify(&mut vs, &slots, &ring, l.m, &root).map_err(Error::Open)?;
    vs.finish().map_err(Error::Transcript)
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// BLAKE3 value columns are virtual — they have no committed placement. A bus
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_pkd` slot evaluation: an ordinary claim on the committed
/// `QPKD` column at `slot_point(slot, r)` (the packed point freezing the low 7
/// coords to the slot's bits). No downstream special-casing — it folds into the
/// one opening like every other point claim.
fn slot_claims(l: &Layout, claims: &[ColumnClaim]) -> Vec<pcs::SlotClaim> {
    claims
        .iter()
        .map(|c| {
            // A virtual BLAKE3 value column (always virtual): its bus claim at
            // instance point `c.point` is the q_pkd slot value — a boolean-selector
            // (strided) claim on QPKD, folded sparsely (2^n_log, not the 2^(7+n_log)
            // dense QPKD block).
            if let Some(slot) = blake3_value_slot(c.col) {
                return pcs::SlotClaim::Strided {
                    offset: l.placements[QPKD].offset,
                    slot,
                    stride_log: crate::blake3_flock::SLOT_STRIDE_LOG,
                    point: c.point.clone(),
                    value: c.value,
                };
            }
            pcs::SlotClaim::Slot {
                offset: l.placements[c.col].offset,
                low_point: c.point.clone(),
                value: c.value,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The O(n_log²) `mle_of_ones_then_zeros` must equal the naive MLE of the prefix
    /// indicator `[1;n, 0;…]` — the pin value depends on it, so any mismatch is a
    /// soundness bug, not just a perf regression.
    #[test]
    fn mle_of_ones_then_zeros_matches_dense() {
        for l in 0..=6usize {
            let point: Vec<F128> = (0..l).map(|i| F128::new(0x9e37 * (i as u64 + 1) + 3, 0x51 * i as u64 + 7)).collect();
            for n in 0..=(1usize << l) {
                let mut col = vec![F128::ZERO; 1usize << l];
                for c in col.iter_mut().take(n) {
                    *c = F128::ONE;
                }
                let dense = if l == 0 {
                    if n >= 1 { F128::ONE } else { F128::ZERO }
                } else {
                    crate::multilinear::mle_eval(&col, &point)
                };
                assert_eq!(mle_of_ones_then_zeros(n, &point), dense, "l={l} n={n}");
            }
        }
    }

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
        let program = Program::assemble(prog, 0, 0, HashMap::new(), 10);

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
        // flock's sub-proof rides the shared channels: its Ligerito is the proof's
        // one opening, its scalar reduction trails the `stream`.
        assert!(!proof.openings.is_empty(), "BLAKE3 program carries a Ligerito opening");
        verify(&program, &pi, &proof).expect("BLAKE3 program verifies");
    }

    /// A self-hash `BLAKE3(h, h)` (the hash-chain step) passes the *same* operand
    /// base as both `a` and `b` (`a == b`), so one 256-bit pair feeds both inputs
    /// with no copy. The row reads those two cells twice; the running access counts
    /// thread through and the bus still balances. This is the aliasing the
    /// consecutive-pair DSL lowering relies on.
    #[test]
    fn blake3_self_hash_aliased_operands() {
        let h0 = F128::new(0xfeed_face_dead_beef, 0x0123_4567_89ab_cdef);
        let h1 = F128::new(0xcafe_d00d_1337_c0de, 0x8877_6655_4433_2211);
        // 8 slots (power of two). Slots 2,3,6 are filler SETs stepping the pc so the
        // last executed instruction (slot 6) lands at pc 7 (the sentinel, halt).
        let prog = vec![
            Op::Set { o: 2, k: h0 },         // operand pair h = (cell 2, cell 3)
            Op::Set { o: 3, k: h1 },
            Op::Set { o: 8, k: F128::ONE },  // filler
            Op::Set { o: 9, k: F128::ONE },  // filler
            Op::Set { o: 10, k: F128::ONE }, // filler
            Op::Blake3 { a: 2, b: 2, c: 6 }, // a == b: hash h ‖ h into cells 6,7
            Op::Set { o: 11, k: F128::ONE }, // filler
            Op::Xor { a: 0, b: 0, c: 0 },    // sentinel
        ];
        let program = Program::from_bytecode(prog, 16);
        let pi = [F128::new(3, 0), F128::new(5, 0)];

        let exec = program.execute(pi);
        let (d0, d1) = blake3_compress(h0, h1, h0, h1);
        assert_eq!(exec.mem[6], d0);
        assert_eq!(exec.mem[7], d1);

        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        verify(&program, &pi, &proof).expect("self-hash BLAKE3 verifies");
    }

    /// Tampering flock's validity sub-proof (its Ligerito `final_b`, opened over
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

        // flock's Ligerito opening is the proof's one hint; tamper a sumcheck
        // round message (the inner-product transcript) — must be rejected.
        let lig = proof.openings.last_mut().expect("flock Ligerito opening");
        lig.sumcheck_transcript[0].u_0 += F128::ONE;
        assert!(
            verify(&program, &pi, &proof).is_err(),
            "tampered BLAKE3 validity proof must be rejected"
        );
    }

    /// flock's REDUCTION sub-proof (zerocheck / lincheck / ring-switch) rides the
    /// `stream` as raw transport, but its VALUES still re-enter the sponge through
    /// the verifier's reduction/opening replay — so tampering a transport word
    /// diverges the recovered `(ab, c)` claims (or breaks decoding) and
    /// verification must reject. (Complements `blake3_rejects_tampered_validity`,
    /// which tampers the Ligerito opening.)
    #[test]
    fn blake3_rejects_tampered_reduction() {
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
        let (proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // The reduction is serialized onto the stream tail (after the last bound
        // scalar). Flip a full transport word there — the second-to-last word is
        // always meaningful bytes (only the final word may be zero-padded).
        let mut tampered = proof.clone();
        let n = tampered.stream.len();
        tampered.stream[n - 2] += F128::ONE;
        assert!(
            verify(&program, &pi, &tampered).is_err(),
            "tampered reduction transport must be rejected"
        );
    }

    /// A program with no BLAKE3 instructions still proves and verifies through the
    /// unified path: `q_pkd` carries a single padding instance and the flock
    /// sub-proof (over that padding) rides the shared channels like any BLAKE3
    /// program — there is no separate no-BLAKE3 code path.
    #[test]
    fn non_blake3_program_verifies() {
        let prog = vec![
            Op::Set { o: 2, k: F128::new(5, 0) },
            Op::Set { o: 3, k: F128::new(6, 0) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [F128::new(1, 0), F128::new(2, 0)];
        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 0, "no real BLAKE3 rows");
        // The proof still carries exactly one Ligerito opening (over the padding).
        assert_eq!(proof.openings.len(), 1, "unified path: one opening always");
        verify(&program, &pi, &proof).expect("non-BLAKE3 program verifies");
    }

    /// A proof is bound to its exact program: presenting it against a *different*
    /// program (same sizes/layout, one instruction constant changed) must be
    /// rejected — the program digest seeds the transcript, so a modified program
    /// diverges the sponge from the first squeeze. Guards the adaptive-statement
    /// forgery the bytecode-bus single-point MLE check does not, on its own, prevent.
    #[test]
    fn proof_bound_to_program() {
        let prog = vec![
            Op::Set { o: 2, k: F128::new(5, 0) },
            Op::Set { o: 3, k: F128::new(6, 0) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog.clone(), 5);
        let pi = [F128::new(1, 0), F128::new(2, 0)];
        let (proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // Same shape (4 ops, same opcodes/operands, so identical layout + announced
        // sizes) but one SET constant changed. Must be rejected.
        let mut prog2 = prog;
        prog2[0] = Op::Set { o: 2, k: F128::new(99, 0) };
        let program2 = Program::from_bytecode(prog2, 5);
        assert!(
            verify(&program2, &pi, &proof).is_err(),
            "a proof must not verify against a different program"
        );
    }

    /// Out-of-process verification: a BLAKE3 proof (whose flock sub-proof now rides
    /// the shared `stream` + `openings`, no side field) serializes to bytes,
    /// deserializes on the other side, and verifies — everything travels in the two
    /// channels, nothing out of band. A flipped encoded byte must not verify.
    #[test]
    fn proof_roundtrips_through_bytes_and_verifies() {
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
        let (proof, _) = prove(&program, pi);

        let bytes = bincode::serialize(&proof).expect("proof serializes");
        let decoded: Proof = bincode::deserialize(&bytes).expect("proof deserializes");
        verify(&program, &pi, &decoded).expect("deserialized BLAKE3 proof verifies");

        let mut tampered = bytes.clone();
        let i = tampered.len() / 2;
        tampered[i] ^= 0x01;
        if let Ok(bad) = bincode::deserialize::<Proof>(&tampered) {
            assert!(verify(&program, &pi, &bad).is_err(), "a corrupted encoded proof must not verify");
        }
    }
}
