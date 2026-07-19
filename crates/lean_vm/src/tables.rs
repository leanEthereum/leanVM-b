//! Per-instruction tables (§7). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.
//!
//! Columns are `K`-valued (`F64`). Addresses, the pc/fp, operands, counts,
//! opcodes and separators are single `K`-columns; a **machine word** (memory
//! value) is 192-bit (`E = F192`), committed as THREE `K`-lane columns. A
//! constraint is evaluated at an `E`-point, so `eval_constraint` receives
//! `E`-values; a word is reassembled as `c0 + c1·y + c2·y²`, and value
//! relations (`XOR`, `MUL`, the `DEREF` store,
//! the `JUMP` selection) are written as `E`-relations — still degree 2 in the
//! lane columns.

use rayon::prelude::*;

use crate::cpu::Trace;
use crate::leaf::Coord::{self, Col, Const, GCol};
use crate::witness::Column;
use primitives::field::{F64, F192, G, mul_by_g};

/// Reassemble a 192-bit machine word from its three `K`-limbs (as folded
/// `E`-column values).
#[inline]
fn e192(c0: F192, c1: F192, c2: F192) -> F192 {
    c0 + c1 * F192::Y + c2 * (F192::Y * F192::Y)
}

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

// Opcodes (coordinate 3 of a bytecode tuple).
pub(crate) const OP_XOR: F64 = g_pow(0);
pub(crate) const OP_MUL: F64 = g_pow(1);
pub(crate) const OP_SET: F64 = g_pow(2);
pub(crate) const OP_DEREF: F64 = g_pow(3);
pub(crate) const OP_JUMP: F64 = g_pow(4);
pub(crate) const OP_BLAKE3: F64 = g_pow(5);
pub(crate) const OP_BLAKE3_TRANSCRIPT: F64 = g_pow(6);
pub(crate) const OP_PACK64X2: F64 = g_pow(7);

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
        self.bytecode_coord(pc, count, Const(opcode), operands);
    }

    pub(crate) fn bytecode_coord(&mut self, pc: usize, count: usize, opcode: Coord, operands: &[Coord]) {
        let mut push = vec![Const(SEP_BYTECODE), Col(pc), GCol(count, 1), opcode.clone()];
        let mut pull = vec![Const(SEP_BYTECODE), Col(pc), Col(count), opcode];
        push.extend_from_slice(operands);
        pull.extend_from_slice(operands);
        self.pair(push, pull);
    }

    /// Memory access: read the three-limb word at `addr`, advancing the cell's
    /// access count by ×g.
    pub(crate) fn memory(&mut self, addr: usize, count: usize, val0: usize, val1: usize, val2: usize) {
        self.pair(
            vec![
                Const(SEP_MEM),
                Col(addr),
                GCol(count, 1),
                Col(val0),
                Col(val1),
                Col(val2),
            ],
            vec![Const(SEP_MEM), Col(addr), Col(count), Col(val0), Col(val1), Col(val2)],
        );
    }

    /// Memory read of a K-valued word: both higher limbs are literal zero. Used for words the
    /// constraints force into K (e.g. the DEREF pointer). Sound because the bus
    /// balances only if the stored value's HI lane is likewise 0.
    pub(crate) fn memory_k(&mut self, addr: usize, count: usize, val: usize) {
        self.pair(
            vec![
                Const(SEP_MEM),
                Col(addr),
                GCol(count, 1),
                Col(val),
                Const(F64::ZERO),
                Const(F64::ZERO),
            ],
            vec![
                Const(SEP_MEM),
                Col(addr),
                Col(count),
                Col(val),
                Const(F64::ZERO),
                Const(F64::ZERO),
            ],
        );
    }

    /// Memory access to a canonical 128-bit word `(lo, hi, 0)`.
    pub(crate) fn memory_128(&mut self, addr: usize, count: usize, lo: usize, hi: usize) {
        self.pair(
            vec![
                Const(SEP_MEM),
                Col(addr),
                GCol(count, 1),
                Col(lo),
                Col(hi),
                Const(F64::ZERO),
            ],
            vec![
                Const(SEP_MEM),
                Col(addr),
                Col(count),
                Col(lo),
                Col(hi),
                Const(F64::ZERO),
            ],
        );
    }

    pub(crate) fn memory_succ(&mut self, addr: usize, k: u32, count: usize, val0: usize, val1: usize, val2: usize) {
        self.pair(
            vec![
                Const(SEP_MEM),
                GCol(addr, k),
                GCol(count, 1),
                Col(val0),
                Col(val1),
                Col(val2),
            ],
            vec![
                Const(SEP_MEM),
                GCol(addr, k),
                Col(count),
                Col(val0),
                Col(val1),
                Col(val2),
            ],
        );
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows, the final memory
/// image (for read values), and `g^0..` for O(1) address/operand lookups.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a [F192],
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
    values: &'a [F192],
    position: &'a [usize],
}

impl<'a> Cols<'a> {
    pub(crate) fn new(values: &'a [F192], position: &'a [usize]) -> Self {
        Self { values, position }
    }
}

impl std::ops::Index<usize> for Cols<'_> {
    type Output = F192;
    fn index(&self, local: usize) -> &F192 {
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
    fn eval_constraint(&self, eta: F192, cols: &Cols) -> F192;
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns (`out[i]` is local column `i`) from the trace.
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]);
}

/// The tables in fixed order `[XOR, MUL, SET, DEREF, JUMP, BLAKE3, PACK64X2]` — the
/// order of `row_counts` / `taus` throughout `cpu`.
pub const N_TABLES: usize = 7;

pub fn tables() -> [&'static dyn Table; N_TABLES] {
    [
        &Arith { is_xor: true },
        &Arith { is_xor: false },
        &SetTable,
        &DerefTable,
        &JumpTable,
        &Blake3Table,
        &Pack64x2Table,
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
// The twelve value lanes are laid out contiguously (VA0..VA0+11), so they map
// 1:1 onto `blake3_flock::SLOTS`.
const _: () = assert!(blake3t::VB0 == blake3t::VA0 + 4 && blake3t::VC0 == blake3t::VA0 + 8);

/// Declare consecutive local column indices and the resulting column count.
// Kept from main's table refactor as a tool for future single-lane column sets;
// this branch's tables use explicit LO/HI/TOP constants (192-bit memory words).
#[allow(unused_macros)]
macro_rules! columns {
    ($($column:ident),+ $(,)?) => {
        columns!(@define 0; $($column),+);
    };
    (@define $index:expr; $column:ident, $($rest:ident),+) => {
        pub const $column: usize = $index;
        columns!(@define $index + 1; $($rest),+);
    };
    (@define $index:expr; $column:ident) => {
        pub const $column: usize = $index;
        pub const N: usize = $index + 1;
    };
}

// ---- XOR / MUL ---------------------------------------------------------------

/// `XOR` and `MUL_NATIVE` share their column layout, flushes, and fill; they
/// differ only in the opcode tag and the third-operand identity (`vc = va + vb`
/// for `XOR`, `vc = va·vb` in `E = K[y]/(y³+y+1)` for `MUL`, degree 2 in the
/// committed K-lane columns).
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
    // The three read words, each three K-limbs.
    pub const VA_LO: usize = 8;
    pub const VA_HI: usize = 9;
    pub const VA_TOP: usize = 10;
    pub const VB_LO: usize = 11;
    pub const VB_HI: usize = 12;
    pub const VB_TOP: usize = 13;
    pub const VC_LO: usize = 14;
    pub const VC_HI: usize = 15;
    pub const VC_TOP: usize = 16;
    pub const RA: usize = 17;
    pub const RB: usize = 18;
    pub const RC: usize = 19;
    pub const RBC: usize = 20;
    pub const N: usize = 21;
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
        &[
            FP, OA, OB, OC, AA, AB, AC, VA_LO, VA_HI, VA_TOP, VB_LO, VB_HI, VB_TOP, VC_LO, VC_HI, VC_TOP,
        ]
    }
    fn eval_constraint(&self, eta: F192, cols: &Cols) -> F192 {
        use arith::*;
        // The three words as full 192-bit E-values.
        let va = e192(cols[VA_LO], cols[VA_HI], cols[VA_TOP]);
        let vb = e192(cols[VB_LO], cols[VB_HI], cols[VB_TOP]);
        let vc = e192(cols[VC_LO], cols[VC_HI], cols[VC_TOP]);
        // XOR = E-addition, MUL = E-multiplication — both degree 2
        // in the lane columns, so the round univariate stays degree 2.
        let third = if self.is_xor { va + vb } else { va * vb };
        (cols[AA] + cols[FP] * cols[OA])
            + eta * (cols[AB] + cols[FP] * cols[OB])
            + eta * eta * (cols[AC] + cols[FP] * cols[OC])
            + eta * eta * eta * (vc + third)
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
        f.memory(AA, RA, VA_LO, VA_HI, VA_TOP);
        f.memory(AB, RB, VB_LO, VB_HI, VB_TOP);
        f.memory(AC, RC, VC_LO, VC_HI, VC_TOP);
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
        out[VA_LO] = rows.par_iter().map(|r| F64(ctx.mem[r.aa as usize].c0)).collect();
        out[VA_HI] = rows.par_iter().map(|r| F64(ctx.mem[r.aa as usize].c1)).collect();
        out[VA_TOP] = rows.par_iter().map(|r| F64(ctx.mem[r.aa as usize].c2)).collect();
        out[VB_LO] = rows.par_iter().map(|r| F64(ctx.mem[r.ab as usize].c0)).collect();
        out[VB_HI] = rows.par_iter().map(|r| F64(ctx.mem[r.ab as usize].c1)).collect();
        out[VB_TOP] = rows.par_iter().map(|r| F64(ctx.mem[r.ab as usize].c2)).collect();
        out[VC_LO] = rows.par_iter().map(|r| F64(ctx.mem[r.ac as usize].c0)).collect();
        out[VC_HI] = rows.par_iter().map(|r| F64(ctx.mem[r.ac as usize].c1)).collect();
        out[VC_TOP] = rows.par_iter().map(|r| F64(ctx.mem[r.ac as usize].c2)).collect();
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
    // The stored immediate's three K-limbs ride the bytecode's spare slots.
    pub const K_LO: usize = 3;
    pub const K_HI: usize = 4;
    pub const K_TOP: usize = 5;
    pub const A: usize = 6;
    pub const R: usize = 7;
    pub const RBC: usize = 8;
    pub const N: usize = 9;
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
    fn eval_constraint(&self, _eta: F192, cols: &Cols) -> F192 {
        use set::*;
        // The address a = fp·o.
        cols[A] + cols[FP] * cols[O]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use set::*;
        f.state_step(PC, FP);
        // The immediate's three limbs occupy bytecode operand slots o2..o4
        // (matching layout::operands for SET).
        f.bytecode(
            PC,
            RBC,
            OP_SET,
            &[Col(O), Col(K_LO), Col(K_HI), Col(K_TOP), Const(F64::ZERO)],
        );
        f.memory(A, R, K_LO, K_HI, K_TOP); // the stored constant K is the cell's value
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use set::*;
        let rows = &ctx.trace.set;
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[O] = rows.par_iter().map(|r| ctx.g_at(r.o)).collect();
        out[K_LO] = rows.par_iter().map(|r| F64(r.k.c0)).collect();
        out[K_HI] = rows.par_iter().map(|r| F64(r.k.c1)).collect();
        out[K_TOP] = rows.par_iter().map(|r| F64(r.k.c2)).collect();
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
    // The pointer word — a SINGLE K-lane. The address constraint a2 = p·obe
    // (with a2 a single-lane K column) forces `p` into K, so its extension
    // limbs are provably zero: they are NOT committed, and the memory read
    // carries literal zeros there.
    pub const P: usize = 10;
    // The store target and the local cell, each a full 192-bit word.
    pub const V2_LO: usize = 11;
    pub const V2_HI: usize = 12;
    pub const V2_TOP: usize = 13;
    pub const V3_LO: usize = 14;
    pub const V3_HI: usize = 15;
    pub const V3_TOP: usize = 16;
    pub const R1: usize = 17;
    pub const R2: usize = 18;
    pub const R3: usize = 19;
    pub const RBC: usize = 20;
    pub const N: usize = 21;
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
        &[
            FP, OAL, OBE, OGA, A1, A2, A3, P, FPC, FFP, V2_LO, V2_HI, V2_TOP, V3_LO, V3_HI, V3_TOP, PC,
        ]
    }
    fn eval_constraint(&self, eta: F192, cols: &Cols) -> F192 {
        use deref::*;
        // The pointer is K-valued; the target and local words are full F192 values.
        let p = cols[P]; // single K-lane pointer; extension limbs are zero
        let v2 = e192(cols[V2_LO], cols[V2_HI], cols[V2_TOP]);
        let v3 = e192(cols[V3_LO], cols[V3_HI], cols[V3_TOP]);
        // Three addresses (a2 = p·obe is pointer-relative — with a2 a single K
        // column, this forces the pointer word `p` into K) plus the flag-selected
        // store `v2 = src`, where `src = (1+f_pc+f_fp)·v3 + f_pc·(g²·pc) + f_fp·fp`
        // over the two boolean store-mode flags. The `pc` source is the virtual
        // return target g²·pc (a free ×g² of the committed pc), so no column.
        let src =
            (F192::ONE + cols[FPC] + cols[FFP]) * v3 + cols[FPC] * cols[PC].mul_base(G * G) + cols[FFP] * cols[FP];
        (cols[A1] + cols[FP] * cols[OAL])
            + eta * (cols[A2] + p * cols[OBE])
            + eta * eta * (cols[A3] + cols[FP] * cols[OGA])
            + eta * eta * eta * (v2 + src)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_DEREF, &[Col(OAL), Col(OBE), Col(OGA), Col(FPC), Col(FFP)]);
        f.memory_k(A1, R1, P);
        f.memory(A2, R2, V2_LO, V2_HI, V2_TOP);
        f.memory(A3, R3, V3_LO, V3_HI, V3_TOP);
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
        debug_assert!(
            rows.iter().all(|r| r.p.c1 == 0 && r.p.c2 == 0),
            "deref pointer must be K-valued"
        );
        out[P] = rows.par_iter().map(|r| F64(r.p.c0)).collect();
        out[V2_LO] = rows.par_iter().map(|r| F64(r.v2.c0)).collect();
        out[V2_HI] = rows.par_iter().map(|r| F64(r.v2.c1)).collect();
        out[V2_TOP] = rows.par_iter().map(|r| F64(r.v2.c2)).collect();
        out[V3_LO] = rows.par_iter().map(|r| F64(r.v3.c0)).collect();
        out[V3_HI] = rows.par_iter().map(|r| F64(r.v3.c1)).collect();
        out[V3_TOP] = rows.par_iter().map(|r| F64(r.v3.c2)).collect();
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
    pub const NPC: usize = 2; // next pc — a K address (single lane)
    pub const NFP: usize = 3; // next fp — a K address (single lane)
    pub const OC: usize = 4;
    pub const OD: usize = 5;
    pub const OF: usize = 6;
    pub const AC: usize = 7;
    pub const AD: usize = 8;
    pub const AF: usize = 9;
    // The condition is an arbitrary F192 word. Destination/frame words are
    // K-valued addresses read through the full three-limb memory bus.
    pub const C_LO: usize = 10;
    pub const C_HI: usize = 11;
    pub const C_TOP: usize = 12;
    pub const D_LO: usize = 13;
    pub const D_HI: usize = 14;
    pub const D_TOP: usize = 15;
    pub const F_LO: usize = 16;
    pub const F_HI: usize = 17;
    pub const F_TOP: usize = 18;
    pub const RC: usize = 19;
    pub const RD: usize = 20;
    pub const RF: usize = 21;
    pub const RBC: usize = 22;
    // Local witness columns (committed, never flushed): the inverse hint `w`
    // (192-bit: c⁻¹ in E) and the taken indicator `b = [c ≠ 0]` it certifies
    // (doc §7.5). `b` is a single K-lane (0/1).
    pub const W_LO: usize = 23;
    pub const W_HI: usize = 24;
    pub const W_TOP: usize = 25;
    pub const B: usize = 26;
    pub const N: usize = 27;
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
        &[
            PC, FP, NPC, NFP, OC, OD, OF, AC, AD, AF, C_LO, C_HI, C_TOP, D_LO, D_HI, D_TOP, F_LO, F_HI, F_TOP, W_LO,
            W_HI, W_TOP, B,
        ]
    }
    fn eval_constraint(&self, eta: F192, cols: &Cols) -> F192 {
        use jump::*;
        let one = F192::ONE;
        // The condition / destination / frame / inverse as F192 values.
        let c = e192(cols[C_LO], cols[C_HI], cols[C_TOP]);
        let d = e192(cols[D_LO], cols[D_HI], cols[D_TOP]);
        let ff = e192(cols[F_LO], cols[F_HI], cols[F_TOP]);
        let w = e192(cols[W_LO], cols[W_HI], cols[W_TOP]);
        let fall_through = cols[PC].mul_base(G); // next pc when the branch is not taken
        let addrs = (cols[AC] + cols[FP] * cols[OC])
            + eta * (cols[AD] + cols[FP] * cols[OD])
            + eta * eta * (cols[AF] + cols[FP] * cols[OF]);
        let eta3 = eta * eta * eta;
        // `b = cond·w` and `cond·(b+1) = 0` together force `b = [cond ≠ 0]` (doc §7.5),
        // now over E: when `cond ≠ 0` the second gives `b = 1` (and the first
        // `w = cond⁻¹` in E); when `cond = 0` the first gives `b = 0`. NPC/NFP are
        // single K columns, so the selections force the chosen word (d or f) into K.
        let ind_def = eta3 * (cols[B] + c * w);
        let ind_nz = eta3 * eta * (c * (cols[B] + one));
        let sel_pc = eta3 * eta * eta * (cols[NPC] + cols[B] * d + (cols[B] + one) * fall_through);
        let sel_fp = eta3 * eta * eta * eta * (cols[NFP] + cols[B] * ff + (cols[B] + one) * cols[FP]);
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
        f.memory(AC, RC, C_LO, C_HI, C_TOP);
        f.memory(AD, RD, D_LO, D_HI, D_TOP);
        f.memory(AF, RF, F_LO, F_HI, F_TOP);
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
        out[C_LO] = rows.par_iter().map(|r| F64(r.c.c0)).collect();
        out[C_HI] = rows.par_iter().map(|r| F64(r.c.c1)).collect();
        out[C_TOP] = rows.par_iter().map(|r| F64(r.c.c2)).collect();
        out[D_LO] = rows.par_iter().map(|r| F64(r.d.c0)).collect();
        out[D_HI] = rows.par_iter().map(|r| F64(r.d.c1)).collect();
        out[D_TOP] = rows.par_iter().map(|r| F64(r.d.c2)).collect();
        out[F_LO] = rows.par_iter().map(|r| F64(r.f.c0)).collect();
        out[F_HI] = rows.par_iter().map(|r| F64(r.f.c1)).collect();
        out[F_TOP] = rows.par_iter().map(|r| F64(r.f.c2)).collect();
        out[W_LO] = rows.par_iter().map(|r| F64(r.w.c0)).collect();
        out[W_HI] = rows.par_iter().map(|r| F64(r.w.c1)).collect();
        out[W_TOP] = rows.par_iter().map(|r| F64(r.w.c2)).collect();
        out[B] = rows.par_iter().map(|r| r.b).collect();
        out[RC] = rows.par_iter().map(|r| r.rc).collect();
        out[RD] = rows.par_iter().map(|r| r.rd).collect();
        out[RF] = rows.par_iter().map(|r| r.rf).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}

// ---- PACK64X2 ----------------------------------------------------------------

/// Pack two K-valued memory cells into one canonical 128-bit cell. There are
/// deliberately no source extension-limb columns: `memory_k` puts literal
/// zeros in those bus coordinates, so the global memory permutation can
/// balance only when the actual source words are in K. Likewise `memory_128`
/// writes the destination as `(va, vb, 0)` directly through the bus.
struct Pack64x2Table;

mod pack64 {
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
    pub const RA: usize = 10;
    pub const RB: usize = 11;
    pub const RC: usize = 12;
    pub const RBC: usize = 13;
    pub const N: usize = 14;
}

impl Table for Pack64x2Table {
    fn opcode_tag(&self) -> F64 {
        OP_PACK64X2
    }

    fn n_committed_columns(&self) -> usize {
        pack64::N
    }

    fn count_columns(&self) -> &'static [usize] {
        use pack64::*;
        &[RA, RB, RC, RBC]
    }

    fn constraint_columns(&self) -> &'static [usize] {
        use pack64::*;
        &[FP, OA, OB, OC, AA, AB, AC]
    }

    fn eval_constraint(&self, eta: F192, cols: &Cols) -> F192 {
        use pack64::*;
        (cols[AA] + cols[FP] * cols[OA])
            + eta * (cols[AB] + cols[FP] * cols[OB])
            + eta * eta * (cols[AC] + cols[FP] * cols[OC])
    }

    fn flushes(&self, f: &mut FlushBuilder) {
        use pack64::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            OP_PACK64X2,
            &[Col(OA), Col(OB), Col(OC), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory_k(AA, RA, VA);
        f.memory_k(AB, RB, VB);
        f.memory_128(AC, RC, VA, VB);
    }

    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use pack64::*;
        let rows = &ctx.trace.pack64x2;
        out[PC] = rows.par_iter().map(|r| ctx.g_at(r.pc)).collect();
        out[FP] = rows.par_iter().map(|r| ctx.g_at(r.fp)).collect();
        out[OA] = rows.par_iter().map(|r| ctx.g_at(r.aa - r.fp)).collect();
        out[OB] = rows.par_iter().map(|r| ctx.g_at(r.ab - r.fp)).collect();
        out[OC] = rows.par_iter().map(|r| ctx.g_at(r.ac - r.fp)).collect();
        out[AA] = rows.par_iter().map(|r| ctx.g_at(r.aa)).collect();
        out[AB] = rows.par_iter().map(|r| ctx.g_at(r.ab)).collect();
        out[AC] = rows.par_iter().map(|r| ctx.g_at(r.ac)).collect();
        out[VA] = rows.par_iter().map(|r| F64(ctx.mem[r.aa as usize].c0)).collect();
        out[VB] = rows.par_iter().map(|r| F64(ctx.mem[r.ab as usize].c0)).collect();
        out[RA] = rows.par_iter().map(|r| r.ra).collect();
        out[RB] = rows.par_iter().map(|r| r.rb).collect();
        out[RC] = rows.par_iter().map(|r| r.rc).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}

// ---- BLAKE3 ------------------------------------------------------------------

/// `BLAKE3` (doc §7.6): the four 128-bit input chunks are addressed
/// *independently* at `aa0, aa1, ab0, ab1` (`= fp·g^{ins[i]}`), each a single
/// 128-bit cell — no forced contiguity between chunks, so a caller hashing e.g.
/// `(tweak, pp)` need not copy them into adjacent cells. The 32-byte output
/// occupies the two consecutive words `ac`, `g·ac`, so the row reads six cells in
/// all. Five address bindings `a_X = fp·o_X` are constrained; the compression
/// relating output words to input words carries no table constraint here: it is
/// proven by flock's R1CS validity via `q_pkd` (§blake3_flock).
///
/// A 128-bit cell is two flock 64-bit words (lo, hi lanes), so the twelve flock
/// words are twelve value LANE columns over six cells. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL — not committed —
/// and routes their bus claims to `q_pkd`, which already holds those words (see
/// [`BLAKE3_VALUE_COLS`]).
struct Blake3Table;

pub(crate) mod blake3t {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA0: usize = 2; // operand g-powers (offsets) of the four input cells …
    pub const OA1: usize = 3;
    pub const OB0: usize = 4;
    pub const OB1: usize = 5;
    pub const OC: usize = 6; // … and the output base
    pub const AA0: usize = 7; // the four independent input cell addresses …
    pub const AA1: usize = 8;
    pub const AB0: usize = 9;
    pub const AB1: usize = 10;
    pub const AC: usize = 11; // … and the output base (the second word is g·AC)
    // The twelve flock words as value lanes: a's cells (AA0, AA1), b's cells
    // (AB0, AB1), c's cells (AC, g·AC), two lanes (lo, hi) each.
    pub const VA0: usize = 12; // AA0.lo, AA0.hi, AA1.lo, AA1.hi
    pub const VB0: usize = 16; // AB0.lo, AB0.hi, AB1.lo, AB1.hi
    pub const VC0: usize = 20; // AC.lo, AC.hi, (g·AC).lo, (g·AC).hi
    pub const RA0: usize = 24; // per-cell read counts (two a cells) …
    pub const RA1: usize = 25;
    pub const RB0: usize = 26; // … two b cells …
    pub const RB1: usize = 27;
    pub const RC0: usize = 28; // … two c cells.
    pub const RC1: usize = 29;
    pub const RBC: usize = 30;
    // Actual three-limb memory words.  Flock byte lanes above are virtual;
    // these committed columns let the AIR select the serialization mode and
    // bind every physical memory limb to the corresponding Flock lane.
    pub const MI0: usize = 31; // 4 inputs * 3 limbs
    pub const MO0: usize = 43; // 2 outputs * 3 limbs
    pub const PACK: usize = 49;
    pub const OP: usize = 50;
    pub const N: usize = 51;
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
        &[RA0, RA1, RB0, RB1, RC0, RC1, RBC]
    }
    fn constraint_columns(&self) -> &'static [usize] {
        use blake3t::*;
        &[
            FP,
            OA0,
            OA1,
            OB0,
            OB1,
            OC,
            AA0,
            AA1,
            AB0,
            AB1,
            AC,
            VA0,
            VA0 + 1,
            VA0 + 2,
            VA0 + 3,
            VB0,
            VB0 + 1,
            VB0 + 2,
            VB0 + 3,
            VC0,
            VC0 + 1,
            VC0 + 2,
            VC0 + 3,
            MI0,
            MI0 + 1,
            MI0 + 2,
            MI0 + 3,
            MI0 + 4,
            MI0 + 5,
            MI0 + 6,
            MI0 + 7,
            MI0 + 8,
            MI0 + 9,
            MI0 + 10,
            MI0 + 11,
            MO0,
            MO0 + 1,
            MO0 + 2,
            MO0 + 3,
            MO0 + 4,
            MO0 + 5,
            PACK,
            OP,
        ]
    }
    fn eval_constraint(&self, eta: F192, cols: &Cols) -> F192 {
        use blake3t::*;
        // The five address bindings a_X = fp·o_X (degree 2). The compression
        // carries no table constraint here: flock's R1CS validity proves it
        // via q_pkd (§blake3_flock).
        let bind = |a: usize, o: usize| cols[a] + cols[FP] * cols[o];
        let mut acc = bind(AA0, OA0)
            + eta * bind(AA1, OA1)
            + eta * eta * bind(AB0, OB0)
            + eta * eta * eta * bind(AB1, OB1)
            + eta * eta * eta * eta * bind(AC, OC);
        let mut ep = eta * eta * eta * eta * eta;
        let mut add = |v: F192| {
            acc += ep * v;
            ep *= eta;
        };
        let s = cols[PACK];
        add(s * (s + F192::ONE));
        add(cols[OP] + F192::from(OP_BLAKE3) + s * F192::from(OP_BLAKE3 + OP_BLAKE3_TRANSCRIPT));
        // Input lane serialization. Bytes128: 2+2 lanes. Transcript192: 3+1.
        add(cols[VA0] + cols[MI0]);
        add(cols[VA0 + 1] + cols[MI0 + 1]);
        add(cols[VA0 + 2] + (F192::ONE + s) * cols[MI0 + 3] + s * cols[MI0 + 2]);
        add(cols[VA0 + 3] + (F192::ONE + s) * cols[MI0 + 4] + s * cols[MI0 + 3]);
        add(cols[VB0] + cols[MI0 + 6]);
        add(cols[VB0 + 1] + cols[MI0 + 7]);
        add(cols[VB0 + 2] + (F192::ONE + s) * cols[MI0 + 9] + s * cols[MI0 + 8]);
        add(cols[VB0 + 3] + (F192::ONE + s) * cols[MI0 + 10] + s * cols[MI0 + 9]);
        add((F192::ONE + s) * cols[MI0 + 2]);
        add(s * cols[MI0 + 4]);
        add(cols[MI0 + 5]);
        add((F192::ONE + s) * cols[MI0 + 8]);
        add(s * cols[MI0 + 10]);
        add(cols[MI0 + 11]);
        // Digest serialization: canonical 128+128 or transcript 192+64.
        add(cols[MO0] + cols[VC0]);
        add(cols[MO0 + 1] + cols[VC0 + 1]);
        add(cols[MO0 + 2] + s * cols[VC0 + 2]);
        add(cols[MO0 + 3] + (F192::ONE + s) * cols[VC0 + 2] + s * cols[VC0 + 3]);
        add(cols[MO0 + 4] + (F192::ONE + s) * cols[VC0 + 3]);
        add(cols[MO0 + 5]);
        acc
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use blake3t::*;
        f.state_step(PC, FP);
        f.bytecode_coord(PC, RBC, Col(OP), &[Col(OA0), Col(OA1), Col(OB0), Col(OB1), Col(OC)]);
        // Six cell reads: four independent 128-bit input cells, then the output's
        // two consecutive cells (AC, g·AC). Each carries its word's two lanes.
        f.memory(AA0, RA0, MI0, MI0 + 1, MI0 + 2);
        f.memory(AA1, RA1, MI0 + 3, MI0 + 4, MI0 + 5);
        f.memory(AB0, RB0, MI0 + 6, MI0 + 7, MI0 + 8);
        f.memory(AB1, RB1, MI0 + 9, MI0 + 10, MI0 + 11);
        f.memory(AC, RC0, MO0, MO0 + 1, MO0 + 2);
        f.memory_succ(AC, 1, RC1, MO0 + 3, MO0 + 4, MO0 + 5);
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
        }
        for word in 0..4 {
            for limb in 0..3 {
                out[MI0 + 3 * word + limb] = rows
                    .par_iter()
                    .map(|r| {
                        let w = r.words[word];
                        F64([w.c0, w.c1, w.c2][limb])
                    })
                    .collect();
            }
        }
        for word in 0..2 {
            for limb in 0..3 {
                out[MO0 + 3 * word + limb] = rows
                    .par_iter()
                    .map(|r| {
                        let w = r.words[4 + word];
                        F64([w.c0, w.c1, w.c2][limb])
                    })
                    .collect();
            }
        }
        out[PACK] = rows
            .par_iter()
            .map(|r| F64(u64::from(r.packing == crate::cpu::Blake3Packing::Transcript192)))
            .collect();
        out[OP] = rows
            .par_iter()
            .map(|r| {
                if r.packing == crate::cpu::Blake3Packing::Transcript192 {
                    OP_BLAKE3_TRANSCRIPT
                } else {
                    OP_BLAKE3
                }
            })
            .collect();
        out[RA0] = rows.par_iter().map(|r| r.ra[0]).collect();
        out[RA1] = rows.par_iter().map(|r| r.ra[1]).collect();
        out[RB0] = rows.par_iter().map(|r| r.rb[0]).collect();
        out[RB1] = rows.par_iter().map(|r| r.rb[1]).collect();
        out[RC0] = rows.par_iter().map(|r| r.rc[0]).collect();
        out[RC1] = rows.par_iter().map(|r| r.rc[1]).collect();
        out[RBC] = rows.par_iter().map(|r| r.bytecode_read).collect();
    }
}
