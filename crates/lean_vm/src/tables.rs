//! Per-instruction tables (`doc/body/07-instruction-tables.tex`). Each opcode is one [`Table`] impl that declares,
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
//! the `JUMP` selection) are written as `E`-relations, still degree 2 in the
//! lane columns.

use crate::colval::ColVal;
use crate::cpu::Trace;
use crate::leaf::Coord::{self, Col, Const, GCol};
use crate::witness::Column;
use primitives::field::{F64, F192, G, mul_by_g};

/// Fill one column from the trace rows, in parallel: `parallel::map_collect`
/// with the row-slice indexing folded in, so a column definition stays one line.
fn map_rows<R: Sync, T: Send>(rows: &[R], f: impl Fn(&R) -> T + Sync) -> Vec<T> {
    parallel::map_collect(rows.len(), |i| f(&rows[i]))
}

// ---- the identities ----------------------------------------------------------
//
// Each is written ONCE, generic over the column type: `F64` in the round a table
// joins the batch, `F192` afterwards (see [`ColVal`]). Products of two `K`
// columns stay 64-bit, an `η`-power or a word multiplies through `mul_e`, and a
// machine word from three `K` lanes costs nothing to assemble.

fn arith_identity<T: ColVal>(is_xor: bool, pows: &[F192], cols: &[T]) -> F192 {
    use arith::*;
    let va = T::word(cols[VA_LO], cols[VA_HI], cols[VA_TOP]);
    let vb = T::word(cols[VB_LO], cols[VB_HI], cols[VB_TOP]);
    let vc = T::word(cols[VC_LO], cols[VC_HI], cols[VC_TOP]);
    let third = if is_xor { va + vb } else { va * vb };
    (cols[AA] + cols[FP] * cols[OA]).mul_e(pows[0])
        + (cols[AB] + cols[FP] * cols[OB]).mul_e(pows[1])
        + (cols[AC] + cols[FP] * cols[OC]).mul_e(pows[2])
        + pows[3] * (vc + third)
}

fn set_identity<T: ColVal>(pows: &[F192], cols: &[T]) -> F192 {
    use set::*;
    // The address a = fp·o.
    (cols[A] + cols[FP] * cols[O]).mul_e(pows[0])
}

fn deref_identity<T: ColVal>(pows: &[F192], cols: &[T]) -> F192 {
    use deref::*;
    // The pointer is K-valued; the target and local words are full 192-bit values.
    let p = cols[P]; // single K-lane pointer; extension limbs are zero
    let v2 = T::word(cols[V2_LO], cols[V2_HI], cols[V2_TOP]);
    let v3 = T::word(cols[V3_LO], cols[V3_HI], cols[V3_TOP]);
    // Three addresses (a2 = p·obe is pointer-relative: with a2 a single K
    // column, this forces the pointer word `p` into K) plus the flag-selected
    // store `v2 = src`, where `src = (1+f_pc+f_fp)·v3 + f_pc·(g²·pc) + f_fp·fp`
    // over the two boolean store-mode flags. The `pc` source is the virtual
    // return target g²·pc (a free ×g² of the committed pc), so no column.
    let src = (T::ONE + cols[FPC] + cols[FFP]).mul_e(v3)
        + (cols[FPC] * cols[PC].mul_k(G * G)).to_e()
        + (cols[FFP] * cols[FP]).to_e();
    (cols[A1] + cols[FP] * cols[OAL]).mul_e(pows[0])
        + (cols[A2] + p * cols[OBE]).mul_e(pows[1])
        + (cols[A3] + cols[FP] * cols[OGA]).mul_e(pows[2])
        + pows[3] * (v2 + src)
}

fn jump_identity<T: ColVal>(pows: &[F192], cols: &[T]) -> F192 {
    use jump::*;
    let c = T::word(cols[C_LO], cols[C_HI], cols[C_TOP]);
    let d = T::word(cols[D_LO], cols[D_HI], cols[D_TOP]);
    let ff = T::word(cols[F_LO], cols[F_HI], cols[F_TOP]);
    let w = T::word(cols[W_LO], cols[W_HI], cols[W_TOP]);
    let fall_through = cols[PC].mul_k(G);
    let b1 = cols[B] + T::ONE;
    let addrs = (cols[AC] + cols[FP] * cols[OC]).mul_e(pows[0])
        + (cols[AD] + cols[FP] * cols[OD]).mul_e(pows[1])
        + (cols[AF] + cols[FP] * cols[OF]).mul_e(pows[2]);
    // `b = cond·w` and `cond·(b+1) = 0` together force `b = [cond ≠ 0]`:
    // when `cond ≠ 0` the second gives `b = 1` (and the first `w = cond⁻¹`);
    // when `cond = 0` the first gives `b = 0`.
    let ind_def = pows[3] * (cols[B].to_e() + c * w);
    let ind_nz = pows[4] * b1.mul_e(c);
    let sel_pc = pows[5] * (cols[NPC].to_e() + cols[B].mul_e(d) + (b1 * fall_through).to_e());
    let sel_fp = pows[6] * (cols[NFP].to_e() + cols[B].mul_e(ff) + (b1 * cols[FP]).to_e());
    addrs + ind_def + ind_nz + sel_pc + sel_fp
}

fn pack64_identity<T: ColVal>(pows: &[F192], cols: &[T]) -> F192 {
    use pack64::*;
    (cols[AA] + cols[FP] * cols[OA]).mul_e(pows[0])
        + (cols[AB] + cols[FP] * cols[OB]).mul_e(pows[1])
        + (cols[AC] + cols[FP] * cols[OC]).mul_e(pows[2])
}

fn blake3_identity<T: ColVal>(pows: &[F192], cols: &[T]) -> F192 {
    use blake3t::*;
    // The six address bindings a_X = fp·o_X (degree 2). The compression carries no
    // table constraint here: flock's R1CS validity proves it via q_pkd.
    let bind = |a: usize, o: usize| cols[a] + cols[FP] * cols[o];
    bind(AA0, OA0).mul_e(pows[0])
        + bind(AA1, OA1).mul_e(pows[1])
        + bind(AB0, OB0).mul_e(pows[2])
        + bind(AB1, OB1).mul_e(pows[3])
        + bind(ACV, OCV).mul_e(pows[4])
        + bind(AC, OC).mul_e(pows[5])
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
pub(crate) const OP_PACK64X2: F64 = g_pow(6);

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

    /// Bytecode read at `pc`: the program tuple (opcode + seven operand slots),
    /// with the per-pc execution count advanced by ×g on the push side.
    pub(crate) fn bytecode(&mut self, pc: usize, count: usize, opcode: F64, operands: &[Coord]) {
        let mut push = vec![Const(SEP_BYTECODE), Col(pc), GCol(count, 1), Const(opcode)];
        let mut pull = vec![Const(SEP_BYTECODE), Col(pc), Col(count), Const(opcode)];
        push.extend_from_slice(operands);
        pull.extend_from_slice(operands);
        self.pair(push, pull);
    }

    /// The shape every memory interaction shares: the word at `addr` carried as
    /// three value coordinates, with the cell's access count advanced by ×g on the
    /// push side.
    fn mem_pair(&mut self, addr: Coord, count: usize, vals: [Coord; 3]) {
        let mut push = vec![Const(SEP_MEM), addr.clone(), GCol(count, 1)];
        let mut pull = vec![Const(SEP_MEM), addr, Col(count)];
        push.extend_from_slice(&vals);
        pull.extend_from_slice(&vals);
        self.pair(push, pull);
    }

    /// Memory access: read the three-limb word at `addr`.
    pub(crate) fn memory(&mut self, addr: usize, count: usize, val0: usize, val1: usize, val2: usize) {
        self.mem_pair(Col(addr), count, [Col(val0), Col(val1), Col(val2)]);
    }

    /// Memory read of a K-valued word: both higher limbs are literal zero. Used for words the
    /// constraints force into K (e.g. the DEREF pointer). Sound because the bus
    /// balances only if the stored value's HI lane is likewise 0.
    pub(crate) fn memory_k(&mut self, addr: usize, count: usize, val: usize) {
        self.mem_pair(Col(addr), count, [Col(val), Const(F64::ZERO), Const(F64::ZERO)]);
    }

    /// Memory access to a canonical 128-bit word `(lo, hi, 0)`.
    pub(crate) fn memory_128(&mut self, addr: usize, count: usize, lo: usize, hi: usize) {
        self.mem_pair(Col(addr), count, [Col(lo), Col(hi), Const(F64::ZERO)]);
    }

    /// Memory access to the successor of `addr`, carrying `(lo, hi, 0)`.
    pub(crate) fn memory_128_succ(&mut self, addr: usize, count: usize, lo: usize, hi: usize) {
        self.mem_pair(GCol(addr, 1), count, [Col(lo), Col(hi), Const(F64::ZERO)]);
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

// ---- the trait ---------------------------------------------------------------

/// One instruction table. Indices in [`flushes`](Table::flushes) and
/// [`count_columns`](Table::count_columns) are local to this table.
pub trait Table: Sync {
    /// Number of committed columns (local indices `0..n_committed_columns`).
    fn n_committed_columns(&self) -> usize;
    /// Local indices of this table's read-count columns: the `g^{count}` values
    /// recording how many times each accessed cell (and the pc) was read. The
    /// framework treats them specially: each gets its own single-column "count"
    /// bus block, and padding rows fill them with `1` (= g^0) instead of `0`.
    fn count_columns(&self) -> &'static [usize];
    /// How many identities [`eval_constraint`](Table::eval_constraint) folds.
    /// Sizes this table's slice of the batch's disjoint `eta`-range (§constraints).
    fn n_constraints(&self) -> usize;
    /// Evaluate the table's degree-2 constraint at one row, reading column values
    /// by local index from `cols` (e.g. `cols[arith::AA]`) and weighting identity
    /// `i` by `pows[i]`, this table's slice of the batch's `eta`-powers. The slice is
    /// is exactly [`n_constraints`](Table::n_constraints) long: an identity indexed
    /// past its end panics rather than silently reaching into the next table's
    /// range. The batched zerocheck carries every committed column of a table, in
    /// local order, so `cols` is indexed directly. Returns `0` on every valid row (§4.1).
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192;
    /// The same identity over `K`-valued columns, for the round a table joins the
    /// batch, before its columns have been folded into `E` (§5.1). Both entry
    /// points delegate to one generic definition per table, so they cannot drift.
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192;
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns (`out[i]` is local column `i`) from the trace.
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]);
}

/// The tables in fixed order `[XOR, MUL, SET, DEREF, JUMP, BLAKE3, PACK64X2]`, the
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
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]` (matches
/// `blake3_flock::SLOTS`). These columns are
/// VIRTUAL (never committed): `q_pkd` already holds those words at fixed packed
/// slots, so `cpu` routes their memory-bus evaluation claims straight to `q_pkd`
/// (`slot_claims`): the value the bus flushes IS the flock-proven word.
pub const BLAKE3_VALUE_COLS: [usize; 18] = [
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
    blake3t::VCV0,
    blake3t::VCV0 + 1,
    blake3t::VCV0 + 2,
    blake3t::VCV0 + 3,
    blake3t::MD0,
    blake3t::MD1,
];
// The eighteen value lanes are laid out contiguously (VA0..VA0+17), so they map
// 1:1 onto `blake3_flock::SLOTS`.
const _: () = assert!(
    blake3t::VB0 == blake3t::VA0 + 4
        && blake3t::VC0 == blake3t::VA0 + 8
        && blake3t::VCV0 == blake3t::VA0 + 12
        && blake3t::MD0 == blake3t::VA0 + 16
        && blake3t::MD1 == blake3t::VA0 + 17
);

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
    fn n_committed_columns(&self) -> usize {
        arith::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use arith::*;
        &[RA, RB, RC, RBC]
    }
    fn n_constraints(&self) -> usize {
        4 // three addresses + the third-operand identity
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        arith_identity(self.is_xor, pows, cols)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        arith_identity(self.is_xor, pows, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use arith::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            if self.is_xor { OP_XOR } else { OP_MUL },
            &[Col(OA), Col(OB), Col(OC), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(AA, RA, VA_LO, VA_HI, VA_TOP);
        f.memory(AB, RB, VB_LO, VB_HI, VB_TOP);
        f.memory(AC, RC, VC_LO, VC_HI, VC_TOP);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use arith::*;
        let rows = if self.is_xor { &ctx.trace.xor } else { &ctx.trace.mul };
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OA] = map_rows(rows, |r| ctx.g_at(r.aa - r.fp));
        out[OB] = map_rows(rows, |r| ctx.g_at(r.ab - r.fp));
        out[OC] = map_rows(rows, |r| ctx.g_at(r.ac - r.fp));
        out[AA] = map_rows(rows, |r| ctx.g_at(r.aa));
        out[AB] = map_rows(rows, |r| ctx.g_at(r.ab));
        out[AC] = map_rows(rows, |r| ctx.g_at(r.ac));
        out[VA_LO] = map_rows(rows, |r| F64(ctx.mem[r.aa as usize].c0));
        out[VA_HI] = map_rows(rows, |r| F64(ctx.mem[r.aa as usize].c1));
        out[VA_TOP] = map_rows(rows, |r| F64(ctx.mem[r.aa as usize].c2));
        out[VB_LO] = map_rows(rows, |r| F64(ctx.mem[r.ab as usize].c0));
        out[VB_HI] = map_rows(rows, |r| F64(ctx.mem[r.ab as usize].c1));
        out[VB_TOP] = map_rows(rows, |r| F64(ctx.mem[r.ab as usize].c2));
        out[VC_LO] = map_rows(rows, |r| F64(ctx.mem[r.ac as usize].c0));
        out[VC_HI] = map_rows(rows, |r| F64(ctx.mem[r.ac as usize].c1));
        out[VC_TOP] = map_rows(rows, |r| F64(ctx.mem[r.ac as usize].c2));
        out[RA] = map_rows(rows, |r| r.ra);
        out[RB] = map_rows(rows, |r| r.rb);
        out[RC] = map_rows(rows, |r| r.rc);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
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
    fn n_committed_columns(&self) -> usize {
        set::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use set::*;
        &[R, RBC]
    }
    fn n_constraints(&self) -> usize {
        1 // the single address binding
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        set_identity(pows, cols)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        set_identity(pows, cols)
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
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[O] = map_rows(rows, |r| ctx.g_at(r.o));
        out[K_LO] = map_rows(rows, |r| F64(r.k.c0));
        out[K_HI] = map_rows(rows, |r| F64(r.k.c1));
        out[K_TOP] = map_rows(rows, |r| F64(r.k.c2));
        out[A] = map_rows(rows, |r| ctx.g_at(r.a));
        out[R] = map_rows(rows, |r| r.r);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
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
    // The pointer word is a SINGLE K-lane. The address constraint a2 = p·obe
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
    fn n_committed_columns(&self) -> usize {
        deref::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use deref::*;
        &[R1, R2, R3, RBC]
    }
    fn n_constraints(&self) -> usize {
        4 // three addresses + the flag-selected store
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        deref_identity(pows, cols)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        deref_identity(pows, cols)
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
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OAL] = map_rows(rows, |r| ctx.g_at(r.alpha));
        out[OBE] = map_rows(rows, |r| ctx.g_at(r.beta));
        out[OGA] = map_rows(rows, |r| ctx.g_at(r.gamma));
        out[FPC] = map_rows(rows, |r| r.mode.f_pc());
        out[FFP] = map_rows(rows, |r| r.mode.f_fp());
        out[A1] = map_rows(rows, |r| ctx.g_at(r.a1));
        out[A2] = map_rows(rows, |r| ctx.gpow[r.a2]); // a2 is a full memory index
        out[A3] = map_rows(rows, |r| ctx.g_at(r.a3));
        debug_assert!(
            rows.iter().all(|r| r.p.c1 == 0 && r.p.c2 == 0),
            "deref pointer must be K-valued"
        );
        out[P] = map_rows(rows, |r| F64(r.p.c0));
        out[V2_LO] = map_rows(rows, |r| F64(r.v2.c0));
        out[V2_HI] = map_rows(rows, |r| F64(r.v2.c1));
        out[V2_TOP] = map_rows(rows, |r| F64(r.v2.c2));
        out[V3_LO] = map_rows(rows, |r| F64(r.v3.c0));
        out[V3_HI] = map_rows(rows, |r| F64(r.v3.c1));
        out[V3_TOP] = map_rows(rows, |r| F64(r.v3.c2));
        out[R1] = map_rows(rows, |r| r.r1);
        out[R2] = map_rows(rows, |r| r.r2);
        out[R3] = map_rows(rows, |r| r.r3);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const NPC: usize = 2; // next pc, a K address (single lane)
    pub const NFP: usize = 3; // next fp, a K address (single lane)
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
    // (the `JUMP` table in `doc/body/07-instruction-tables.tex`). `b` is a single K-lane (0/1).
    pub const W_LO: usize = 23;
    pub const W_HI: usize = 24;
    pub const W_TOP: usize = 25;
    pub const B: usize = 26;
    pub const N: usize = 27;
}

impl Table for JumpTable {
    fn n_committed_columns(&self) -> usize {
        jump::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use jump::*;
        &[RC, RD, RF, RBC]
    }
    fn n_constraints(&self) -> usize {
        7 // three addresses + two indicator identities + the pc/fp selections
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        jump_identity(pows, cols)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        jump_identity(pows, cols)
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
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[NPC] = map_rows(rows, |r| r.npc);
        out[NFP] = map_rows(rows, |r| r.nfp);
        out[OC] = map_rows(rows, |r| ctx.g_at(r.oc));
        out[OD] = map_rows(rows, |r| ctx.g_at(r.od));
        out[OF] = map_rows(rows, |r| ctx.g_at(r.of));
        out[AC] = map_rows(rows, |r| ctx.g_at(r.ac));
        out[AD] = map_rows(rows, |r| ctx.g_at(r.ad));
        out[AF] = map_rows(rows, |r| ctx.g_at(r.af));
        out[C_LO] = map_rows(rows, |r| F64(r.c.c0));
        out[C_HI] = map_rows(rows, |r| F64(r.c.c1));
        out[C_TOP] = map_rows(rows, |r| F64(r.c.c2));
        out[D_LO] = map_rows(rows, |r| F64(r.d.c0));
        out[D_HI] = map_rows(rows, |r| F64(r.d.c1));
        out[D_TOP] = map_rows(rows, |r| F64(r.d.c2));
        out[F_LO] = map_rows(rows, |r| F64(r.f.c0));
        out[F_HI] = map_rows(rows, |r| F64(r.f.c1));
        out[F_TOP] = map_rows(rows, |r| F64(r.f.c2));
        out[W_LO] = map_rows(rows, |r| F64(r.w.c0));
        out[W_HI] = map_rows(rows, |r| F64(r.w.c1));
        out[W_TOP] = map_rows(rows, |r| F64(r.w.c2));
        out[B] = map_rows(rows, |r| r.b);
        out[RC] = map_rows(rows, |r| r.rc);
        out[RD] = map_rows(rows, |r| r.rd);
        out[RF] = map_rows(rows, |r| r.rf);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
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
    fn n_committed_columns(&self) -> usize {
        pack64::N
    }

    fn count_columns(&self) -> &'static [usize] {
        use pack64::*;
        &[RA, RB, RC, RBC]
    }

    fn n_constraints(&self) -> usize {
        3 // the three address bindings
    }

    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        pack64_identity(pows, cols)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        pack64_identity(pows, cols)
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
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OA] = map_rows(rows, |r| ctx.g_at(r.aa - r.fp));
        out[OB] = map_rows(rows, |r| ctx.g_at(r.ab - r.fp));
        out[OC] = map_rows(rows, |r| ctx.g_at(r.ac - r.fp));
        out[AA] = map_rows(rows, |r| ctx.g_at(r.aa));
        out[AB] = map_rows(rows, |r| ctx.g_at(r.ab));
        out[AC] = map_rows(rows, |r| ctx.g_at(r.ac));
        out[VA] = map_rows(rows, |r| F64(ctx.mem[r.aa as usize].c0));
        out[VB] = map_rows(rows, |r| F64(ctx.mem[r.ab as usize].c0));
        out[RA] = map_rows(rows, |r| r.ra);
        out[RB] = map_rows(rows, |r| r.rb);
        out[RC] = map_rows(rows, |r| r.rc);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}

// ---- BLAKE3 ------------------------------------------------------------------

/// `BLAKE3` (“BLAKE3” in `doc/body/07-instruction-tables.tex`): one standard compression. The four 128-bit message
/// chunks are addressed *independently* at `aa0, aa1, ab0, ab1`
/// (`= fp·g^{ins[i]}`), each a single cell, with no forced contiguity between
/// chunks, so a caller hashing e.g. `(tweak, pp)` need not copy them into
/// adjacent cells. The chaining value and the 32-byte output each occupy two
/// consecutive cells, based at `acv` and `ac`, so the row reads eight cells in
/// all. Six address bindings `a_X = fp·o_X` are constrained; the compression
/// relating output words to input words carries no table constraint here: it is
/// proven by flock's R1CS validity via `q_pkd` (§blake3_flock).
///
/// A 128-bit chunk is two flock 64-bit words (lo, hi lanes), so the sixteen
/// memory-borne flock words are sixteen value LANE columns over eight cells,
/// plus the metadata immediate's two lanes. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL (not committed)
/// and routes their bus claims to `q_pkd`, which already holds those words (see
/// [`BLAKE3_VALUE_COLS`]).
struct Blake3Table;

pub(crate) mod blake3t {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA0: usize = 2; // operand g-powers (offsets) of the four message cells …
    pub const OA1: usize = 3;
    pub const OB0: usize = 4;
    pub const OB1: usize = 5;
    pub const OCV: usize = 6; // … the chaining-value base …
    pub const OC: usize = 7; // … and the output base
    pub const AA0: usize = 8; // the four independent message cell addresses …
    pub const AA1: usize = 9;
    pub const AB0: usize = 10;
    pub const AB1: usize = 11;
    pub const ACV: usize = 12; // … the cv base (the second cell is g·ACV) …
    pub const AC: usize = 13; // … and the output base (the second cell is g·AC)
    // The eighteen flock words as value lanes: a's cells (AA0, AA1), b's cells
    // (AB0, AB1), c's cells (AC, g·AC), cv's cells (ACV, g·ACV), two lanes
    // (lo, hi) each, then the bytecode metadata immediate's two lanes.
    pub const VA0: usize = 14; // AA0.lo, AA0.hi, AA1.lo, AA1.hi
    pub const VB0: usize = 18; // AB0.lo, AB0.hi, AB1.lo, AB1.hi
    pub const VC0: usize = 22; // AC.lo, AC.hi, (g·AC).lo, (g·AC).hi
    pub const VCV0: usize = 26; // ACV.lo, ACV.hi, (g·ACV).lo, (g·ACV).hi
    pub const MD0: usize = 30; // metadata: the counter lane …
    pub const MD1: usize = 31; // … and the block_len‖flags lane
    pub const RA0: usize = 32; // per-cell read counts (two a cells) …
    pub const RA1: usize = 33;
    pub const RB0: usize = 34; // … two b cells …
    pub const RB1: usize = 35;
    pub const RCV0: usize = 36; // … two cv cells …
    pub const RCV1: usize = 37;
    pub const RC0: usize = 38; // … two c cells.
    pub const RC1: usize = 39;
    pub const RBC: usize = 40;
    pub const N: usize = 41;
}

impl Table for Blake3Table {
    fn n_committed_columns(&self) -> usize {
        blake3t::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use blake3t::*;
        &[RA0, RA1, RB0, RB1, RCV0, RCV1, RC0, RC1, RBC]
    }
    fn n_constraints(&self) -> usize {
        6 // the six address bindings
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        blake3_identity(pows, cols)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        blake3_identity(pows, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use blake3t::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            OP_BLAKE3,
            &[
                Col(OA0),
                Col(OA1),
                Col(OB0),
                Col(OB1),
                Col(OCV),
                Col(OC),
                Col(MD0),
                Col(MD1),
            ],
        );
        // Eight cell reads: four independent 128-bit message cells, the chaining
        // value's two consecutive cells (ACV, g·ACV), then the output's two
        // consecutive cells (AC, g·AC). Each carries its chunk's two lanes with a
        // literal-zero top limb (`memory_128`), so the canonical embedding is
        // proof-enforced and the zero limbs are never committed.
        f.memory_128(AA0, RA0, VA0, VA0 + 1);
        f.memory_128(AA1, RA1, VA0 + 2, VA0 + 3);
        f.memory_128(AB0, RB0, VB0, VB0 + 1);
        f.memory_128(AB1, RB1, VB0 + 2, VB0 + 3);
        f.memory_128(ACV, RCV0, VCV0, VCV0 + 1);
        f.memory_128_succ(ACV, RCV1, VCV0 + 2, VCV0 + 3);
        f.memory_128(AC, RC0, VC0, VC0 + 1);
        f.memory_128_succ(AC, RC1, VC0 + 2, VC0 + 3);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use blake3t::*;
        let rows = &ctx.trace.blake3;
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OA0] = map_rows(rows, |r| ctx.g_at(r.aa0 - r.fp));
        out[OA1] = map_rows(rows, |r| ctx.g_at(r.aa1 - r.fp));
        out[OB0] = map_rows(rows, |r| ctx.g_at(r.ab0 - r.fp));
        out[OB1] = map_rows(rows, |r| ctx.g_at(r.ab1 - r.fp));
        out[OCV] = map_rows(rows, |r| ctx.g_at(r.acv - r.fp));
        out[OC] = map_rows(rows, |r| ctx.g_at(r.ac - r.fp));
        out[AA0] = map_rows(rows, |r| ctx.g_at(r.aa0));
        out[AA1] = map_rows(rows, |r| ctx.g_at(r.aa1));
        out[AB0] = map_rows(rows, |r| ctx.g_at(r.ab0));
        out[AB1] = map_rows(rows, |r| ctx.g_at(r.ab1));
        out[ACV] = map_rows(rows, |r| ctx.g_at(r.acv));
        out[AC] = map_rows(rows, |r| ctx.g_at(r.ac));
        for k in 0..4 {
            out[VA0 + k] = map_rows(rows, |r| r.va[k]);
            out[VB0 + k] = map_rows(rows, |r| r.vb[k]);
            out[VC0 + k] = map_rows(rows, |r| r.vc[k]);
            out[VCV0 + k] = map_rows(rows, |r| r.vcv[k]);
        }
        out[MD0] = map_rows(rows, |r| F64(r.metadata.c0));
        out[MD1] = map_rows(rows, |r| F64(r.metadata.c1));
        out[RA0] = map_rows(rows, |r| r.ra[0]);
        out[RA1] = map_rows(rows, |r| r.ra[1]);
        out[RB0] = map_rows(rows, |r| r.rb[0]);
        out[RB1] = map_rows(rows, |r| r.rb[1]);
        out[RCV0] = map_rows(rows, |r| r.rcv[0]);
        out[RCV1] = map_rows(rows, |r| r.rcv[1]);
        out[RC0] = map_rows(rows, |r| r.rc[0]);
        out[RC1] = map_rows(rows, |r| r.rc[1]);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}
