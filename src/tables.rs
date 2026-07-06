//! Per-instruction tables (§7). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.

use rayon::prelude::*;

use crate::cpu::Trace;
use crate::field::{F128, G, mul_by_x};
use crate::leaf::Coord::{self, Col, Const, GCol};
use crate::witness::Column;

// ---- shared bus vocabulary ---------------------------------------------------

/// `g^k` at compile time (`g = x`, so repeated `mul_by_x` from `g^0 = 1`).
const fn g_pow(k: usize) -> F128 {
    let mut acc = F128::ONE;
    let mut i = 0;
    while i < k {
        acc = mul_by_x(acc);
        i += 1;
    }
    acc
}

// Domain separators (coordinate 0 of every bus tuple): the g-powers g^0, g^1, g^2.
pub(crate) const SEP_STATE: F128 = g_pow(0);
pub(crate) const SEP_MEM: F128 = g_pow(1);
pub(crate) const SEP_BYTECODE: F128 = g_pow(2);

// Opcodes (coordinate 3 of a bytecode tuple): the g-powers g^0..g^5.
pub(crate) const OP_XOR: F128 = g_pow(0);
pub(crate) const OP_MUL: F128 = g_pow(1);
pub(crate) const OP_SET: F128 = g_pow(2);
pub(crate) const OP_DEREF: F128 = g_pow(3);
pub(crate) const OP_JUMP: F128 = g_pow(4);
pub(crate) const OP_BLAKE3: F128 = g_pow(5);

// ---- flush builder -----------------------------------------------------------

/// Collects a table's push/pull bus interactions in *local* column indices. The
/// push/pull of a memory-checked entry differ only by one coordinate carrying the
/// post-increment `g·count` (`GCol`) instead of the pre-increment (`Col`); these
/// helpers encode that pairing so each table reads declaratively.
pub(crate) struct FlushBuilder {
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
            vec![Const(SEP_STATE), GCol(pc), Col(fp)],
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
    /// with the per-pc execution count advanced by ×g on the push side. The opcode
    /// is a public constant (the table serves a single opcode).
    pub(crate) fn bytecode(&mut self, pc: usize, count: usize, opcode: F128, operands: &[Coord]) {
        self.bytecode_coord(pc, count, Const(opcode), operands);
    }

    /// Like [`bytecode`](Self::bytecode) but the opcode coordinate is a committed
    /// COLUMN, not a public constant — for a table serving several opcodes that
    /// carries the actual opcode per row (the merged arithmetic table). The
    /// bytecode bus then pins that column to the program's opcode at `pc`.
    pub(crate) fn bytecode_col(&mut self, pc: usize, count: usize, op: usize, operands: &[Coord]) {
        self.bytecode_coord(pc, count, Col(op), operands);
    }

    fn bytecode_coord(&mut self, pc: usize, count: usize, opcode: Coord, operands: &[Coord]) {
        let mut push = vec![Const(SEP_BYTECODE), Col(pc), GCol(count), opcode.clone()];
        let mut pull = vec![Const(SEP_BYTECODE), Col(pc), Col(count), opcode];
        push.extend_from_slice(operands);
        pull.extend_from_slice(operands);
        self.pair(push, pull);
    }

    /// Memory access: read `val` at `addr`, advancing the cell's access count by ×g.
    pub(crate) fn memory(&mut self, addr: usize, count: usize, val: usize) {
        self.pair(
            vec![Const(SEP_MEM), Col(addr), GCol(count), Col(val)],
            vec![Const(SEP_MEM), Col(addr), Col(count), Col(val)],
        );
    }

    /// Memory access at the free successor address `g·col[addr]` — the second of
    /// two consecutive words (doc §7.6, `BLAKE3`). The address coordinate is the
    /// virtual ×g of the committed base address, so no extra committed column.
    pub(crate) fn memory_succ(&mut self, addr: usize, count: usize, val: usize) {
        self.pair(
            vec![Const(SEP_MEM), GCol(addr), GCol(count), Col(val)],
            vec![Const(SEP_MEM), GCol(addr), Col(count), Col(val)],
        );
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows, the final memory
/// image (for read values), and `g^0..` for O(1) address/operand lookups.
pub(crate) struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a [F128],
    pub(crate) gpow: &'a [F128],
}

impl FillCtx<'_> {
    fn g_at(&self, i: u32) -> F128 {
        self.gpow[i as usize]
    }
}

// ---- constraint column accessor ----------------------------------------------

/// The values of a constraint's columns at its zerocheck point, indexed by
/// *local* column index — so a constraint reads `cols[arith::AA]` directly rather
/// than a positional `v[5]`. It holds the [`Table::constraint_columns`] values
/// plus a reverse map (local index → position), so the order those columns are
/// listed in is irrelevant to `eval_constraint`.
pub(crate) struct Cols<'a> {
    values: &'a [F128],
    position: &'a [usize],
}

impl<'a> Cols<'a> {
    pub(crate) fn new(values: &'a [F128], position: &'a [usize]) -> Self {
        Self { values, position }
    }
}

impl std::ops::Index<usize> for Cols<'_> {
    type Output = F128;
    fn index(&self, local: usize) -> &F128 {
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
pub(crate) trait Table: Sync {
    /// Number of committed columns (local indices `0..n_committed_columns`).
    fn n_committed_columns(&self) -> usize;
    /// Local indices of this table's read-count columns — the `g^{count}` values
    /// recording how many times each accessed cell (and the pc) was read. The
    /// framework treats them specially: each gets its own single-column "count"
    /// bus block, and padding rows fill them with `1` (= g^0) instead of `0`.
    fn count_columns(&self) -> &'static [usize];
    /// Local indices of committed columns whose PADDING value is `g^0 = 1` rather
    /// than `0` — but which, unlike [`count_columns`](Table::count_columns), raise
    /// no count block. The merged arithmetic table pads its committed `OP` column
    /// with `OP_XOR = g^0 = 1`, so a padding row is an inert no-op XOR and every
    /// degree-2 identity (notably the opcode-validity `(op+1)(op+g)`) still
    /// vanishes on it. Empty for single-opcode tables (all-zero padding suffices).
    fn unit_padded_columns(&self) -> &'static [usize] {
        &[]
    }
    /// The committed columns this constraint reads, opened at its zerocheck point.
    /// Order is irrelevant — `eval_constraint` indexes them by name through [`Cols`].
    fn constraint_columns(&self) -> &'static [usize];
    /// Evaluate the table's degree-2 constraint at one row, reading column values
    /// by local index from `cols` (e.g. `cols[arith::AA]`). The table's individual
    /// identities (fp-relative addresses, the opcode's arithmetic, JUMP selection)
    /// are folded into one value by powers of the batching challenge `eta`. Returns
    /// `0` on every valid row (§4.1).
    fn eval_constraint(&self, eta: F128, cols: &Cols) -> F128;
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns (`out[i]` is local column `i`) from the trace.
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]);
}

/// The number of instruction tables (the length of [`tables`]). XOR and MUL share
/// one merged [`Arith`] table, so this is 5, not one-per-opcode. It sizes the
/// per-table `row_counts` / `taus` / `base` arrays throughout `cpu`; the
/// per-*opcode* run statistics ([`crate::cpu::Stats::counts`]) stay 6-wide.
pub(crate) const N_TABLES: usize = 5;

/// The five tables in fixed order `[ARITH (XOR|MUL), SET, DEREF, JUMP, BLAKE3]` —
/// the order of `row_counts` / `taus` throughout `cpu`.
pub(crate) fn tables() -> [&'static dyn Table; N_TABLES] {
    [&Arith, &SetTable, &DerefTable, &JumpTable, &Blake3Table]
}

/// Index of the BLAKE3 table in [`tables`] (last).
pub(crate) const BLAKE3_TABLE: usize = N_TABLES - 1;

/// BLAKE3 value-column LOCAL indices in canonical slot order
/// `[a0, a1, b0, b1, c0, c1]` (matches `blake3_flock::SLOTS`). These columns are
/// VIRTUAL (never committed): `q_pkd` already holds those words at fixed packed
/// slots, so `cpu` routes their memory-bus evaluation claims straight to `q_pkd`
/// (`slot_claims`) — the value the bus flushes IS the flock-proven word.
pub(crate) const BLAKE3_VALUE_COLS: [usize; 6] = [
    blake3t::VA0,
    blake3t::VA1,
    blake3t::VB0,
    blake3t::VB1,
    blake3t::VC0,
    blake3t::VC1,
];

// ---- ARITH (XOR + MUL) -------------------------------------------------------

/// One table serving BOTH arithmetic opcodes — `XOR` (field add, `vc = va + vb`)
/// and `MUL_NATIVE` (`vc = va·vb`). Instead of two tables each padded to its own
/// power of two, the executed XOR and MUL rows share one block. A committed
/// per-row opcode column `OP` (`OP_XOR = 1` or `OP_MUL = g`), placed on the
/// bytecode bus so it is pinned to the program's opcode at `pc`, selects the
/// identity. The product is broken out into its own committed column `PROD =
/// va·vb`, so the mul branch enters the result identity as a single degree-1
/// column and the whole constraint stays degree 2.
struct Arith;

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
    /// Committed opcode of the row: `OP_XOR` (`= g^0 = 1`) or `OP_MUL` (`= g^1 =
    /// g`). Lives on the bytecode bus (pinned to the program's opcode at `pc`) and
    /// drives the add/mul selection. Padding rows hold `OP_XOR` (see
    /// [`Table::unit_padded_columns`]).
    pub const OP: usize = 15;
    /// Committed product `va·vb`, so the mul branch is a single degree-1 column in
    /// the result identity (keeping the constraint degree 2).
    pub const PROD: usize = 16;
    pub const N: usize = 17;
}

/// The merged arithmetic (XOR + MUL) table's committed column count — its per-row
/// width. Public so tools can report the table's committed footprint,
/// `ARITH_COLUMNS · 2^tau_arith`, where `2^tau_arith` is the executed XOR+MUL row
/// count rounded up to a power of two.
pub const ARITH_COLUMNS: usize = arith::N;

impl Table for Arith {
    fn n_committed_columns(&self) -> usize {
        arith::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use arith::*;
        &[RA, RB, RC, RBC]
    }
    fn unit_padded_columns(&self) -> &'static [usize] {
        &[arith::OP]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use arith::*;
        &[FP, OA, OB, OC, AA, AB, AC, VA, VB, VC, OP, PROD]
    }
    fn eval_constraint(&self, eta: F128, cols: &Cols) -> F128 {
        use arith::*;
        let one = F128::ONE;
        let sum = cols[VA] + cols[VB];
        // Result selection. `is_mul ∈ {0,1}` is the affine image of `OP ∈ {1, g}`:
        // `is_mul = (OP + 1)/(g + 1)`. Multiplying the selection through by `(g+1)`
        // clears the field inverse and keeps it degree 2:
        //   (g+1)·(vc + va + vb) + (OP + 1)·(PROD + va + vb) = 0
        //   OP = 1 (XOR) ⇒ (g+1)(vc + va + vb) = 0 ⇒ vc = va + vb
        //   OP = g (MUL) ⇒ (g+1)(vc + PROD)     = 0 ⇒ vc = PROD  (= va·vb)
        let result = (G + one) * (cols[VC] + sum) + (cols[OP] + one) * (cols[PROD] + sum);
        // Opcode validity `(OP + OP_XOR)(OP + OP_MUL) = 0` pins `OP ∈ {1, g}`. This
        // is what stops a non-arithmetic instruction being routed into this table:
        // the bytecode bus would force `OP` to that opcode's tag (g²…g⁵), which
        // this identity then rejects. (In the split tables the per-table constant
        // opcode played that role.)
        let op_valid = (cols[OP] + one) * (cols[OP] + G);
        (cols[AA] + cols[FP] * cols[OA])
            + eta * (cols[AB] + cols[FP] * cols[OB])
            + eta * eta * (cols[AC] + cols[FP] * cols[OC])
            + eta * eta * eta * (cols[PROD] + cols[VA] * cols[VB])
            + eta * eta * eta * eta * result
            + eta * eta * eta * eta * eta * op_valid
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use arith::*;
        f.state_step(PC, FP);
        f.bytecode_col(
            PC,
            RBC,
            OP,
            &[Col(OA), Col(OB), Col(OC), Const(F128::ZERO), Const(F128::ZERO)],
        );
        f.memory(AA, RA, VA);
        f.memory(AB, RB, VB);
        f.memory(AC, RC, VC);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use arith::*;
        // The executed XOR rows first, then the MUL rows, as one block. Every
        // column uses this same concatenation, so a given row index names the same
        // instruction across all columns; `OP` records which half it came from.
        let (xor, mul) = (&ctx.trace.xor, &ctx.trace.mul);
        macro_rules! both {
            ($f:expr) => {
                xor.par_iter().map($f).chain(mul.par_iter().map($f)).collect()
            };
        }
        out[PC] = both!(|r| ctx.g_at(r.pc));
        out[FP] = both!(|r| ctx.g_at(r.fp));
        out[OA] = both!(|r| ctx.g_at(r.aa - r.fp));
        out[OB] = both!(|r| ctx.g_at(r.ab - r.fp));
        out[OC] = both!(|r| ctx.g_at(r.ac - r.fp));
        out[AA] = both!(|r| ctx.g_at(r.aa));
        out[AB] = both!(|r| ctx.g_at(r.ab));
        out[AC] = both!(|r| ctx.g_at(r.ac));
        out[VA] = both!(|r| ctx.mem[r.aa as usize]);
        out[VB] = both!(|r| ctx.mem[r.ab as usize]);
        out[VC] = both!(|r| ctx.mem[r.ac as usize]);
        out[RA] = both!(|r| r.ra);
        out[RB] = both!(|r| r.rb);
        out[RC] = both!(|r| r.rc);
        out[RBC] = both!(|r| r.bytecode_read);
        out[PROD] = both!(|r| ctx.mem[r.aa as usize] * ctx.mem[r.ab as usize]);
        // `OP`: OP_XOR on the xor half, OP_MUL on the mul half.
        out[OP] = xor
            .par_iter()
            .map(|_| OP_XOR)
            .chain(mul.par_iter().map(|_| OP_MUL))
            .collect();
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
    fn eval_constraint(&self, _eta: F128, cols: &Cols) -> F128 {
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
            &[Col(O), Col(K), Const(F128::ZERO), Const(F128::ZERO), Const(F128::ZERO)],
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
    fn eval_constraint(&self, eta: F128, cols: &Cols) -> F128 {
        use deref::*;
        // Three addresses (a2 = p·obe is pointer-relative) plus the flag-selected
        // store `v2 = src`, where `src = (1+f_pc+f_fp)·v3 + f_pc·(g²·pc) + f_fp·fp`
        // over the two boolean store-mode flags. The `pc` source is the virtual
        // return target g²·pc (a free ×g² of the committed pc), so no column.
        let src =
            (F128::ONE + cols[FPC] + cols[FFP]) * cols[V3] + cols[FPC] * (G * G * cols[PC]) + cols[FFP] * cols[FP];
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
    fn eval_constraint(&self, eta: F128, cols: &Cols) -> F128 {
        use jump::*;
        let one = F128::ONE;
        let fall_through = G * cols[PC]; // next pc when the branch is not taken
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
            &[Col(OC), Col(OD), Col(OF), Const(F128::ZERO), Const(F128::ZERO)],
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

/// `BLAKE3` (doc §7.6): each of the three operands names a 256-bit value in two
/// consecutive memory words, so the row reads six cells — the two inputs `a, b`
/// and the two output words `c` — at base addresses `aa, ab, ac` and their
/// successors `g·aa, g·ab, g·ac`. Only the three base-address bindings are
/// constrained; the compression relating output words to input words is
/// *unproven* (deferred), so no constraint links `vc*` to the inputs.
///
/// The six value columns are listed in `n_committed_columns` (they need a local
/// index for the flushes and are filled from the trace for the bus), but `cpu`
/// treats them as VIRTUAL — not committed — and routes their bus claims to
/// `q_pkd`, which already holds those words (see [`BLAKE3_VALUE_COLS`]).
struct Blake3Table;

mod blake3t {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    pub const AA: usize = 5; // base address of input a (word 0); word 1 is g·AA
    pub const AB: usize = 6;
    pub const AC: usize = 7;
    pub const VA0: usize = 8;
    pub const VA1: usize = 9;
    pub const VB0: usize = 10;
    pub const VB1: usize = 11;
    pub const VC0: usize = 12;
    pub const VC1: usize = 13;
    pub const RA0: usize = 14;
    pub const RA1: usize = 15;
    pub const RB0: usize = 16;
    pub const RB1: usize = 17;
    pub const RC0: usize = 18;
    pub const RC1: usize = 19;
    pub const RBC: usize = 20;
    pub const N: usize = 21;
}

impl Table for Blake3Table {
    fn n_committed_columns(&self) -> usize {
        blake3t::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use blake3t::*;
        &[RA0, RA1, RB0, RB1, RC0, RC1, RBC]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use blake3t::*;
        &[FP, OA, OB, OC, AA, AB, AC]
    }
    fn eval_constraint(&self, eta: F128, cols: &Cols) -> F128 {
        use blake3t::*;
        // Only the three base-address bindings a_X = fp·o_X. The compression is
        // unproven, so the output words carry no constraint (doc §7.6).
        (cols[AA] + cols[FP] * cols[OA])
            + eta * (cols[AB] + cols[FP] * cols[OB])
            + eta * eta * (cols[AC] + cols[FP] * cols[OC])
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use blake3t::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            OP_BLAKE3,
            &[Col(OA), Col(OB), Col(OC), Const(F128::ZERO), Const(F128::ZERO)],
        );
        // Six reads: each input/output occupies two consecutive words, the second
        // at the successor address g·base.
        f.memory(AA, RA0, VA0);
        f.memory_succ(AA, RA1, VA1);
        f.memory(AB, RB0, VB0);
        f.memory_succ(AB, RB1, VB1);
        f.memory(AC, RC0, VC0);
        f.memory_succ(AC, RC1, VC1);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use blake3t::*;
        let rows = &ctx.trace.blake3;
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[OA] = rows.par_iter().map(|r| ctx.g_at(r.aa - r.fp)).collect();
        out[OB] = rows.par_iter().map(|r| ctx.g_at(r.ab - r.fp)).collect();
        out[OC] = rows.par_iter().map(|r| ctx.g_at(r.ac - r.fp)).collect();
        out[AA] = rows.par_iter().map(|r| ctx.g_at(r.aa)).collect();
        out[AB] = rows.par_iter().map(|r| ctx.g_at(r.ab)).collect();
        out[AC] = rows.par_iter().map(|r| ctx.g_at(r.ac)).collect();
        out[VA0] = rows.par_iter().map(|r| r.va0).collect();
        out[VA1] = rows.par_iter().map(|r| r.va1).collect();
        out[VB0] = rows.par_iter().map(|r| r.vb0).collect();
        out[VB1] = rows.par_iter().map(|r| r.vb1).collect();
        out[VC0] = rows.par_iter().map(|r| r.vc0).collect();
        out[VC1] = rows.par_iter().map(|r| r.vc1).collect();
        out[RA0] = rows.par_iter().map(|r| r.ra0).collect();
        out[RA1] = rows.par_iter().map(|r| r.ra1).collect();
        out[RB0] = rows.par_iter().map(|r| r.rb0).collect();
        out[RB1] = rows.par_iter().map(|r| r.rb1).collect();
        out[RC0] = rows.par_iter().map(|r| r.rc0).collect();
        out[RC1] = rows.par_iter().map(|r| r.rc1).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}
