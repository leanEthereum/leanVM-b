//! Per-instruction tables (§7). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns. Columns are `K`-valued
//! (`F64`); a constraint is evaluated at an `E`-point, so `eval_constraint`
//! receives `E`-values (with the `K`-constants `G`, opcodes mixed in via `mul_base`).

use rayon::prelude::*;

use crate::cpu::Trace;
use primitives::field::{F64, F128T, G, mul_by_g};
use crate::leaf::Coord::{self, Col, Const, GCol};
use crate::witness::Column;

// ---- shared bus vocabulary ---------------------------------------------------

/// `g^k` at compile time (`g = x`, so repeated `mul_by_g` from `g^0 = 1`).
const fn g_pow(k: usize) -> F64 {
    let mut acc = F64::ONE;
    let mut i = 0;
    while i < k {
        acc = mul_by_g(acc);
        i += 1;
    }
    acc
}

// Domain separators (coordinate 0 of every bus tuple): the g-powers g^0, g^1, g^2.
pub(crate) const SEP_STATE: F64 = g_pow(0);
pub(crate) const SEP_MEM: F64 = g_pow(1);
pub(crate) const SEP_BYTECODE: F64 = g_pow(2);

// Opcodes (coordinate 3 of a bytecode tuple): the g-powers g^0..g^5.
pub(crate) const OP_XOR: F64 = g_pow(0);
pub(crate) const OP_MUL: F64 = g_pow(1);
pub(crate) const OP_SET: F64 = g_pow(2);
pub(crate) const OP_DEREF: F64 = g_pow(3);
pub(crate) const OP_JUMP: F64 = g_pow(4);
pub(crate) const OP_BLAKE3: F64 = g_pow(5);

// ---- flush builder -----------------------------------------------------------

/// Collects a table's push/pull bus interactions in *local* column indices. The
/// push/pull of a memory-checked entry differ only by one coordinate carrying the
/// post-increment `g·count` (`GCol`) instead of the pre-increment (`Col`); these
/// helpers encode that pairing so each table reads declaratively.
pub struct FlushBuilder {
    pub(crate) push: Vec<Vec<Coord>>,
    pub(crate) pull: Vec<Vec<Coord>>,
}

impl FlushBuilder {
    pub(crate) fn new() -> Self {
        Self {
            push: Vec::new(),
            pull: Vec::new(),
        }
    }

    fn pair(&mut self, push: Vec<Coord>, pull: Vec<Coord>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    /// Fall-through state step: the next pc is `g·pc`, fp unchanged.
    pub(crate) fn state_step(&mut self, pc: usize, fp: usize) {
        self.pair(
            vec![Const(SEP_STATE), GCol(pc, 1), Col(fp)],
            vec![Const(SEP_STATE), Col(pc), Col(fp)],
        );
    }

    /// Explicit state transition (JUMP): push the next `(npc, nfp)`, pull `(pc, fp)`.
    pub(crate) fn state_jump(&mut self, pc: usize, fp: usize, npc: usize, nfp: usize) {
        self.pair(
            vec![Const(SEP_STATE), Col(npc), Col(nfp)],
            vec![Const(SEP_STATE), Col(pc), Col(fp)],
        );
    }

    /// Bytecode read at `pc`: the program tuple (opcode + five operand slots),
    /// with the per-pc execution count advanced by ×g on the push side.
    pub(crate) fn bytecode(&mut self, pc: usize, count: usize, opcode: F64, operands: &[Coord]) {
        let mut push = vec![Const(SEP_BYTECODE), Col(pc), GCol(count, 1), Const(opcode)];
        let mut pull = vec![Const(SEP_BYTECODE), Col(pc), Col(count), Const(opcode)];
        push.extend_from_slice(operands);
        pull.extend_from_slice(operands);
        self.pair(push, pull);
    }

    /// Memory access: read `val` at `addr`, advancing the cell's access count by ×g.
    pub(crate) fn memory(&mut self, addr: usize, count: usize, val: usize) {
        self.pair(
            vec![Const(SEP_MEM), Col(addr), GCol(count, 1), Col(val)],
            vec![Const(SEP_MEM), Col(addr), Col(count), Col(val)],
        );
    }

    /// Memory access at the free successor address `g^k · col[addr]` — the `k`-th
    /// of four consecutive words (doc §7.6, `BLAKE3`). The address coordinate is
    /// the virtual ×g^k of the committed base address, so no extra committed column.
    pub(crate) fn memory_succ(&mut self, addr: usize, k: u32, count: usize, val: usize) {
        self.pair(
            vec![Const(SEP_MEM), GCol(addr, k), GCol(count, 1), Col(val)],
            vec![Const(SEP_MEM), GCol(addr, k), Col(count), Col(val)],
        );
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows, the final memory
/// image (for read values), and `g^0..` for O(1) address/operand lookups.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a [F64],
    pub(crate) gpow: &'a [F64],
}

impl FillCtx<'_> {
    fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }
}

// ---- constraint column accessor ----------------------------------------------

/// The values of a constraint's columns at its zerocheck point, indexed by
/// *local* column index — so a constraint reads `cols[arith::AA]` directly rather
/// than a positional `v[5]`. It holds the [`Table::constraint_columns`] values
/// plus a reverse map (local index → position), so the order those columns are
/// listed in is irrelevant to `eval_constraint`.
pub struct Cols<'a> {
    values: &'a [F128T],
    position: &'a [usize],
}

impl<'a> Cols<'a> {
    pub(crate) fn new(values: &'a [F128T], position: &'a [usize]) -> Self {
        Self { values, position }
    }
}

impl std::ops::Index<usize> for Cols<'_> {
    type Output = F128T;
    fn index(&self, local: usize) -> &F128T {
        &self.values[self.position[local]]
    }
}

/// Reverse map `local column index → position in `columns`` (the index `Cols`
/// uses). Built once per constraint so the indexing stays O(1).
pub(crate) fn column_positions(columns: &[usize]) -> Vec<usize> {
    let len = columns.iter().copied().max().map_or(0, |m| m + 1);
    let mut position = vec![0usize; len];
    for (pos, &c) in columns.iter().enumerate() {
        position[c] = pos;
    }
    position
}

// ---- the trait ---------------------------------------------------------------

/// One instruction table. Indices in [`flushes`](Table::flushes),
/// [`count_columns`](Table::count_columns), and
/// [`constraint_columns`](Table::constraint_columns) are local to this table.
pub trait Table: Sync {
    /// Distinct opcode tag (coordinate 3 of the bytecode tuple).
    fn opcode_tag(&self) -> F64;
    /// Number of committed columns (local indices `0..n_committed_columns`).
    fn n_committed_columns(&self) -> usize;
    /// Local indices of this table's read-count columns — the `g^{count}` values
    /// recording how many times each accessed cell (and the pc) was read. The
    /// framework treats them specially: each gets its own single-column "count"
    /// bus block, and padding rows fill them with `1` (= g^0) instead of `0`.
    fn count_columns(&self) -> &'static [usize];
    /// The committed columns this constraint reads, opened at its zerocheck point.
    /// Order is irrelevant — `eval_constraint` indexes them by name through [`Cols`].
    fn constraint_columns(&self) -> &'static [usize];
    /// Evaluate the table's degree-2 constraint at one row, reading column values
    /// by local index from `cols` (e.g. `cols[arith::AA]`). The table's individual
    /// identities (fp-relative addresses, the opcode's arithmetic, JUMP selection)
    /// are folded into one value by powers of the batching challenge `eta`. Returns
    /// `0` on every valid row (§4.1).
    fn eval_constraint(&self, eta: F128T, cols: &Cols) -> F128T;
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns (`out[i]` is local column `i`) from the trace.
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]);
}

/// The six tables in fixed order `[XOR, MUL, SET, DEREF, JUMP, BLAKE3]` — the
/// order of `row_counts` / `taus` throughout `cpu`.
pub fn tables() -> [&'static dyn Table; 6] {
    [
        &Arith { is_xor: true },
        &Arith { is_xor: false },
        &SetTable,
        &DerefTable,
        &JumpTable,
        &Blake3Table,
    ]
}

/// Index of the BLAKE3 table in [`tables`].
pub(crate) const BLAKE3_TABLE: usize = 5;

/// BLAKE3 value-column LOCAL indices in canonical slot order
/// `[a0..a3, b0..b3, c0..c3]` (matches `blake3_flock::SLOTS`). These columns are
/// VIRTUAL (never committed): `q_pkd` already holds those words at fixed packed
/// slots, so `cpu` routes their memory-bus evaluation claims straight to `q_pkd`
/// (`slot_claims`) — the value the bus flushes IS the flock-proven word.
pub const BLAKE3_VALUE_COLS: [usize; 12] = [
    blake3t::VA0,
    blake3t::VA0 + 1,
    blake3t::VA0 + 2,
    blake3t::VA0 + 3,
    blake3t::VB0,
    blake3t::VB0 + 1,
    blake3t::VB0 + 2,
    blake3t::VB0 + 3,
    blake3t::VC0,
    blake3t::VC0 + 1,
    blake3t::VC0 + 2,
    blake3t::VC0 + 3,
];

// ---- XOR / MUL ---------------------------------------------------------------

/// `XOR` and `MUL_NATIVE` share their column layout, flushes, and fill; they
/// differ only in the opcode tag and the third-operand identity (`vc = va + vb`
/// for `XOR`, `vc = va·vb` for `MUL` — the `K`-product, degree 2 as before).
struct Arith {
    is_xor: bool,
}

mod arith {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    pub const AA: usize = 5;
    pub const AB: usize = 6;
    pub const AC: usize = 7;
    pub const VA: usize = 8;
    pub const VB: usize = 9;
    pub const VC: usize = 10;
    pub const RA: usize = 11;
    pub const RB: usize = 12;
    pub const RC: usize = 13;
    pub const RBC: usize = 14;
    pub const N: usize = 15;
}

impl Table for Arith {
    fn opcode_tag(&self) -> F64 {
        if self.is_xor { OP_XOR } else { OP_MUL }
    }
    fn n_committed_columns(&self) -> usize {
        arith::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use arith::*;
        &[RA, RB, RC, RBC]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use arith::*;
        &[FP, OA, OB, OC, AA, AB, AC, VA, VB, VC]
    }
    fn eval_constraint(&self, eta: F128T, cols: &Cols) -> F128T {
        use arith::*;
        let third = if self.is_xor {
            cols[VA] + cols[VB]
        } else {
            cols[VA] * cols[VB]
        };
        (cols[AA] + cols[FP] * cols[OA])
            + eta * (cols[AB] + cols[FP] * cols[OB])
            + eta * eta * (cols[AC] + cols[FP] * cols[OC])
            + eta * eta * eta * (cols[VC] + third)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use arith::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            self.opcode_tag(),
            &[Col(OA), Col(OB), Col(OC), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(AA, RA, VA);
        f.memory(AB, RB, VB);
        f.memory(AC, RC, VC);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use arith::*;
        let rows = if self.is_xor { &ctx.trace.xor } else { &ctx.trace.mul };
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[OA] = rows.par_iter().map(|r| ctx.g_at(r.aa - r.fp)).collect();
        out[OB] = rows.par_iter().map(|r| ctx.g_at(r.ab - r.fp)).collect();
        out[OC] = rows.par_iter().map(|r| ctx.g_at(r.ac - r.fp)).collect();
        out[AA] = rows.par_iter().map(|r| ctx.g_at(r.aa)).collect();
        out[AB] = rows.par_iter().map(|r| ctx.g_at(r.ab)).collect();
        out[AC] = rows.par_iter().map(|r| ctx.g_at(r.ac)).collect();
        out[VA] = rows.par_iter().map(|r| ctx.mem[r.aa as usize]).collect();
        out[VB] = rows.par_iter().map(|r| ctx.mem[r.ab as usize]).collect();
        out[VC] = rows.par_iter().map(|r| ctx.mem[r.ac as usize]).collect();
        out[RA] = rows.par_iter().map(|r| r.ra).collect();
        out[RB] = rows.par_iter().map(|r| r.rb).collect();
        out[RC] = rows.par_iter().map(|r| r.rc).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}

// ---- SET ---------------------------------------------------------------------

struct SetTable;

mod set {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O: usize = 2;
    pub const K: usize = 3;
    pub const A: usize = 4;
    pub const R: usize = 5;
    pub const RBC: usize = 6;
    pub const N: usize = 7;
}

impl Table for SetTable {
    fn opcode_tag(&self) -> F64 {
        OP_SET
    }
    fn n_committed_columns(&self) -> usize {
        set::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use set::*;
        &[R, RBC]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use set::*;
        &[FP, O, A]
    }
    fn eval_constraint(&self, _eta: F128T, cols: &Cols) -> F128T {
        use set::*;
        // The address a = fp·o.
        cols[A] + cols[FP] * cols[O]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use set::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            OP_SET,
            &[Col(O), Col(K), Const(F64::ZERO), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(A, R, K); // the stored constant K is the cell's value
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use set::*;
        let rows = &ctx.trace.set;
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[O] = rows.par_iter().map(|r| ctx.g_at(r.o)).collect();
        out[K] = rows.par_iter().map(|r| r.k).collect();
        out[A] = rows.par_iter().map(|r| ctx.g_at(r.a)).collect();
        out[R] = rows.par_iter().map(|r| r.r).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}

// ---- DEREF -------------------------------------------------------------------

struct DerefTable;

mod deref {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OAL: usize = 2;
    pub const OBE: usize = 3;
    pub const OGA: usize = 4;
    pub const FPC: usize = 5;
    pub const FFP: usize = 6;
    pub const A1: usize = 7;
    pub const A2: usize = 8;
    pub const A3: usize = 9;
    pub const P: usize = 10;
    pub const V2: usize = 11;
    pub const V3: usize = 12;
    pub const R1: usize = 13;
    pub const R2: usize = 14;
    pub const R3: usize = 15;
    pub const RBC: usize = 16;
    pub const N: usize = 17;
}

impl Table for DerefTable {
    fn opcode_tag(&self) -> F64 {
        OP_DEREF
    }
    fn n_committed_columns(&self) -> usize {
        deref::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use deref::*;
        &[R1, R2, R3, RBC]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use deref::*;
        &[FP, OAL, OBE, OGA, A1, A2, A3, P, FPC, FFP, V2, V3, PC]
    }
    fn eval_constraint(&self, eta: F128T, cols: &Cols) -> F128T {
        use deref::*;
        // Three addresses (a2 = p·obe is pointer-relative) plus the flag-selected
        // store `v2 = src`, where `src = (1+f_pc+f_fp)·v3 + f_pc·(g²·pc) + f_fp·fp`
        // over the two boolean store-mode flags. The `pc` source is the virtual
        // return target g²·pc (a free ×g² of the committed pc), so no column.
        let src = (F128T::ONE + cols[FPC] + cols[FFP]) * cols[V3]
            + cols[FPC] * cols[PC].mul_base(G * G)
            + cols[FFP] * cols[FP];
        (cols[A1] + cols[FP] * cols[OAL])
            + eta * (cols[A2] + cols[P] * cols[OBE])
            + eta * eta * (cols[A3] + cols[FP] * cols[OGA])
            + eta * eta * eta * (cols[V2] + src)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_DEREF, &[Col(OAL), Col(OBE), Col(OGA), Col(FPC), Col(FFP)]);
        f.memory(A1, R1, P);
        f.memory(A2, R2, V2);
        f.memory(A3, R3, V3);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use deref::*;
        let rows = &ctx.trace.deref;
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[OAL] = rows.par_iter().map(|r| ctx.g_at(r.alpha)).collect();
        out[OBE] = rows.par_iter().map(|r| ctx.g_at(r.beta)).collect();
        out[OGA] = rows.par_iter().map(|r| ctx.g_at(r.gamma)).collect();
        out[FPC] = rows.par_iter().map(|r| r.mode.f_pc()).collect();
        out[FFP] = rows.par_iter().map(|r| r.mode.f_fp()).collect();
        out[A1] = rows.par_iter().map(|r| ctx.g_at(r.a1)).collect();
        out[A2] = rows.par_iter().map(|r| ctx.gpow[r.a2]).collect(); // a2 is a full memory index
        out[A3] = rows.par_iter().map(|r| ctx.g_at(r.a3)).collect();
        out[P] = rows.par_iter().map(|r| r.p).collect();
        out[V2] = rows.par_iter().map(|r| r.v2).collect();
        out[V3] = rows.par_iter().map(|r| r.v3).collect();
        out[R1] = rows.par_iter().map(|r| r.r1).collect();
        out[R2] = rows.par_iter().map(|r| r.r2).collect();
        out[R3] = rows.par_iter().map(|r| r.r3).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const NPC: usize = 2;
    pub const NFP: usize = 3;
    pub const OC: usize = 4;
    pub const OD: usize = 5;
    pub const OF: usize = 6;
    pub const AC: usize = 7;
    pub const AD: usize = 8;
    pub const AF: usize = 9;
    pub const C: usize = 10;
    pub const D: usize = 11;
    pub const F: usize = 12;
    pub const RC: usize = 13;
    pub const RD: usize = 14;
    pub const RF: usize = 15;
    pub const RBC: usize = 16;
    // Local witness columns (committed, never flushed): the inverse hint `w` and
    // the taken indicator `b = [c ≠ 0]` it certifies (doc §7.5).
    pub const W: usize = 17;
    pub const B: usize = 18;
    pub const N: usize = 19;
}

impl Table for JumpTable {
    fn opcode_tag(&self) -> F64 {
        OP_JUMP
    }
    fn n_committed_columns(&self) -> usize {
        jump::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use jump::*;
        &[RC, RD, RF, RBC]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use jump::*;
        &[PC, FP, NPC, NFP, OC, OD, OF, AC, AD, AF, C, D, F, W, B]
    }
    fn eval_constraint(&self, eta: F128T, cols: &Cols) -> F128T {
        use jump::*;
        let one = F128T::ONE;
        let fall_through = cols[PC].mul_base(G); // next pc when the branch is not taken
        let addrs = (cols[AC] + cols[FP] * cols[OC])
            + eta * (cols[AD] + cols[FP] * cols[OD])
            + eta * eta * (cols[AF] + cols[FP] * cols[OF]);
        let eta3 = eta * eta * eta;
        // `b = cond·w` and `cond·(b+1) = 0` together force `b = [cond ≠ 0]` (doc §7.5):
        // when `cond ≠ 0` the second gives `b = 1` (and the first `w = cond⁻¹`);
        // when `cond = 0` the first gives `b = 0`.
        let ind_def = eta3 * (cols[B] + cols[C] * cols[W]);
        let ind_nz = eta3 * eta * (cols[C] * (cols[B] + one));
        let sel_pc = eta3 * eta * eta * (cols[NPC] + cols[B] * cols[D] + (cols[B] + one) * fall_through);
        let sel_fp = eta3 * eta * eta * eta * (cols[NFP] + cols[B] * cols[F] + (cols[B] + one) * cols[FP]);
        addrs + ind_def + ind_nz + sel_pc + sel_fp
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use jump::*;
        f.state_jump(PC, FP, NPC, NFP);
        f.bytecode(
            PC,
            RBC,
            OP_JUMP,
            &[Col(OC), Col(OD), Col(OF), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(AC, RC, C);
        f.memory(AD, RD, D);
        f.memory(AF, RF, F);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[NPC] = rows.par_iter().map(|r| r.npc).collect();
        out[NFP] = rows.par_iter().map(|r| r.nfp).collect();
        out[OC] = rows.par_iter().map(|r| ctx.g_at(r.oc)).collect();
        out[OD] = rows.par_iter().map(|r| ctx.g_at(r.od)).collect();
        out[OF] = rows.par_iter().map(|r| ctx.g_at(r.of)).collect();
        out[AC] = rows.par_iter().map(|r| ctx.g_at(r.ac)).collect();
        out[AD] = rows.par_iter().map(|r| ctx.g_at(r.ad)).collect();
        out[AF] = rows.par_iter().map(|r| ctx.g_at(r.af)).collect();
        out[C] = rows.par_iter().map(|r| r.c).collect();
        out[D] = rows.par_iter().map(|r| r.d).collect();
        out[F] = rows.par_iter().map(|r| r.f).collect();
        out[W] = rows.par_iter().map(|r| r.w).collect();
        out[B] = rows.par_iter().map(|r| r.b).collect();
        out[RC] = rows.par_iter().map(|r| r.rc).collect();
        out[RD] = rows.par_iter().map(|r| r.rd).collect();
        out[RF] = rows.par_iter().map(|r| r.rf).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}

// ---- BLAKE3 ------------------------------------------------------------------

/// `BLAKE3` (doc §7.6): the four 128-bit input chunks are addressed
/// *independently* at `aa0, aa1, ab0, ab1` (`= fp·g^{ins[i]}`), each spanning
/// TWO consecutive 64-bit memory words (`base`, `g·base`) — no forced contiguity
/// between chunks, so a caller hashing e.g. `(tweak, pp)` need not copy them
/// into adjacent cells. The 32-byte output occupies the four consecutive words
/// `g^k·ac`, `k ∈ {0..3}`, so the row reads twelve cells in all. Five address
/// bindings `a_X = fp·o_X` are constrained; the compression relating output
/// words to input words carries no table constraint here: it is proven by
/// flock's R1CS validity via `q_pkd` (§blake3_flock).
///
/// The twelve value columns are listed in `n_committed_columns` (they need a
/// local index for the flushes and are filled from the trace for the bus), but
/// `cpu` treats them as VIRTUAL — not committed — and routes their bus claims to
/// `q_pkd`, which already holds those words (see [`BLAKE3_VALUE_COLS`]).
struct Blake3Table;

mod blake3t {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA0: usize = 2; // operand g-powers (offsets) of the four input chunk bases …
    pub const OA1: usize = 3;
    pub const OB0: usize = 4;
    pub const OB1: usize = 5;
    pub const OC: usize = 6; // … and the output base
    pub const AA0: usize = 7; // the four independent input chunk base addresses …
    pub const AA1: usize = 8;
    pub const AB0: usize = 9;
    pub const AB1: usize = 10;
    pub const AC: usize = 11; // … and the output base (word k is g^k·AC)
    pub const VA0: usize = 12; // a's four words VA0..VA0+3, at (AA0, g·AA0, AA1, g·AA1)
    pub const VB0: usize = 16; // b's four words, at (AB0, g·AB0, AB1, g·AB1)
    pub const VC0: usize = 20; // c's four words, at g^k·AC
    pub const RA0: usize = 24; // per-word read counts, same 4-word runs
    pub const RB0: usize = 28;
    pub const RC0: usize = 32;
    pub const RBC: usize = 36;
    pub const N: usize = 37;
}

impl Table for Blake3Table {
    fn opcode_tag(&self) -> F64 {
        OP_BLAKE3
    }
    fn n_committed_columns(&self) -> usize {
        blake3t::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use blake3t::*;
        &[
            RA0,
            RA0 + 1,
            RA0 + 2,
            RA0 + 3,
            RB0,
            RB0 + 1,
            RB0 + 2,
            RB0 + 3,
            RC0,
            RC0 + 1,
            RC0 + 2,
            RC0 + 3,
            RBC,
        ]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use blake3t::*;
        &[FP, OA0, OA1, OB0, OB1, OC, AA0, AA1, AB0, AB1, AC]
    }
    fn eval_constraint(&self, eta: F128T, cols: &Cols) -> F128T {
        use blake3t::*;
        // The five address bindings a_X = fp·o_X (degree 2). The compression
        // carries no table constraint here: flock's R1CS validity proves it
        // via q_pkd (§blake3_flock).
        let bind = |a: usize, o: usize| cols[a] + cols[FP] * cols[o];
        bind(AA0, OA0)
            + eta * bind(AA1, OA1)
            + eta * eta * bind(AB0, OB0)
            + eta * eta * eta * bind(AB1, OB1)
            + eta * eta * eta * eta * bind(AC, OC)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use blake3t::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_BLAKE3, &[Col(OA0), Col(OA1), Col(OB0), Col(OB1), Col(OC)]);
        // Twelve reads: each input chunk base covers two consecutive words (base,
        // g·base); the output occupies four consecutive words (g^k·AC).
        for (base, r0, v0) in [
            (AA0, RA0, VA0),
            (AA1, RA0 + 2, VA0 + 2),
            (AB0, RB0, VB0),
            (AB1, RB0 + 2, VB0 + 2),
        ] {
            f.memory(base, r0, v0);
            f.memory_succ(base, 1, r0 + 1, v0 + 1);
        }
        f.memory(AC, RC0, VC0);
        for k in 1..4u32 {
            f.memory_succ(AC, k, RC0 + k as usize, VC0 + k as usize);
        }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use blake3t::*;
        let rows = &ctx.trace.blake3;
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[OA0] = rows.par_iter().map(|r| ctx.g_at(r.aa0 - r.fp)).collect();
        out[OA1] = rows.par_iter().map(|r| ctx.g_at(r.aa1 - r.fp)).collect();
        out[OB0] = rows.par_iter().map(|r| ctx.g_at(r.ab0 - r.fp)).collect();
        out[OB1] = rows.par_iter().map(|r| ctx.g_at(r.ab1 - r.fp)).collect();
        out[OC] = rows.par_iter().map(|r| ctx.g_at(r.ac - r.fp)).collect();
        out[AA0] = rows.par_iter().map(|r| ctx.g_at(r.aa0)).collect();
        out[AA1] = rows.par_iter().map(|r| ctx.g_at(r.aa1)).collect();
        out[AB0] = rows.par_iter().map(|r| ctx.g_at(r.ab0)).collect();
        out[AB1] = rows.par_iter().map(|r| ctx.g_at(r.ab1)).collect();
        out[AC] = rows.par_iter().map(|r| ctx.g_at(r.ac)).collect();
        for k in 0..4 {
            out[VA0 + k] = rows.par_iter().map(|r| r.va[k]).collect();
            out[VB0 + k] = rows.par_iter().map(|r| r.vb[k]).collect();
            out[VC0 + k] = rows.par_iter().map(|r| r.vc[k]).collect();
            out[RA0 + k] = rows.par_iter().map(|r| r.ra[k]).collect();
            out[RB0 + k] = rows.par_iter().map(|r| r.rb[k]).collect();
            out[RC0 + k] = rows.par_iter().map(|r| r.rc[k]).collect();
        }
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}
