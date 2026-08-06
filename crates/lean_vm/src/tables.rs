//! Per-instruction tables (`doc/body/07-instruction-tables.tex`). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.
//!
//! Columns are `K`-valued (`F64`). Addresses, the pc/fp, operands, counts,
//! opcodes, separators, and every memory word are single `K`-columns. Explicit
//! extension operations reassemble three consecutive base words as one
//! `E = F192` value inside their constraints.

use crate::cpu::Trace;
use crate::leaf::Coord::{self, Col, Const, GCol, Prod};
use crate::witness::Column;
use primitives::field::{F64, F192, mul_by_g};

/// Fill one column from the trace rows, in parallel: `parallel::map_collect`
/// with the row-slice indexing folded in, so a column definition stays one line.
fn map_rows<R: Sync, T: Send>(rows: &[R], f: impl Fn(&R) -> T + Sync) -> Vec<T> {
    parallel::map_collect(rows.len(), |i| f(&rows[i]))
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
pub(crate) const OP_ADD_EXT: F64 = g_pow(6);
pub(crate) const OP_MUL_EXT: F64 = g_pow(7);
pub(crate) const OP_DEREF_EXT: F64 = g_pow(8);

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

    /// Explicit state transition (JUMP): push the next state, which the row DERIVES
    /// from its columns rather than committing, and pull `(pc, fp)`.
    pub(crate) fn state_derived(&mut self, pc: usize, fp: usize, npc: Coord, nfp: Coord) {
        self.pair(
            vec![Const(SEP_STATE), npc, nfp],
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

    /// Memory access to one base-field word.
    /// `val` is a coordinate, not a column: a word the row DERIVES (an `XOR`/`MUL`
    /// result, a `DEREF` store) is passed as its form, so the cell holds whatever
    /// the form says and bus balance IS the assertion (§5).
    pub(crate) fn memory(&mut self, addr: Coord, count: usize, val: Coord) {
        self.pair(
            vec![Const(SEP_MEM), addr.clone(), GCol(count, 1), val.clone()],
            vec![Const(SEP_MEM), addr, Col(count), val],
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

/// One row's committed column values, indexed by *local* column index, so a
/// constraint reads `cols[arith::AA]` directly rather than a positional `v[5]`.
/// The batched zerocheck carries every committed column of a table, in local
/// order, so this is a plain slice.
pub struct Cols<'a> {
    values: &'a [F192],
}

impl<'a> Cols<'a> {
    pub(crate) fn new(values: &'a [F192]) -> Self {
        Self { values }
    }
}

impl std::ops::Index<usize> for Cols<'_> {
    type Output = F192;
    fn index(&self, local: usize) -> &F192 {
        &self.values[local]
    }
}

// ---- the trait ---------------------------------------------------------------

/// One instruction table. Indices in [`flushes`](Table::flushes) and
/// [`count_columns`](Table::count_columns) are local to this table.
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
    /// How many identities [`eval_constraint`](Table::eval_constraint) folds.
    /// Sizes this table's slice of the batch's disjoint `eta`-range (§constraints).
    fn n_constraints(&self) -> usize;
    /// Evaluate the table's degree-2 constraint at one row, reading column values
    /// by local index from `cols` (e.g. `cols[arith::AA]`) and weighting identity
    /// `i` by `pows[i]`, this table's slice of the batch's `eta`-powers. The slice is
    /// is exactly [`n_constraints`](Table::n_constraints) long: an identity indexed
    /// past its end panics rather than silently reaching into the next table's
    /// range. Returns `0` on every valid row (§4.1).
    fn eval_constraint(&self, pows: &[F192], cols: &Cols) -> F192;
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns (`out[i]` is local column `i`) from the trace.
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]);
}

/// The tables in fixed order `[ADD, MUL, ADD_EXT, MUL_EXT, SET, DEREF,
/// DEREF_EXT, JUMP, BLAKE3]` — the
/// order of `row_counts` / `taus` throughout `cpu`.
pub const N_TABLES: usize = 9;

pub fn tables() -> [&'static dyn Table; N_TABLES] {
    [
        &Arith { is_xor: true },
        &Arith { is_xor: false },
        &ExtArith { is_add: true },
        &ExtArith { is_add: false },
        &SetTable,
        &DerefTable,
        &DerefExtTable,
        &JumpTable,
        &Blake3Table,
    ]
}

/// Index of the BLAKE3 table in [`tables`].
pub const BLAKE3_TABLE: usize = 8;

/// BLAKE3 value-column LOCAL indices in canonical slot order
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]` (matches
/// `blake3_flock::SLOTS`). These columns are
/// VIRTUAL (never committed): `q_flock` already holds those words at fixed packed
/// slots, so `cpu` routes their memory-bus evaluation claims straight to `q_flock`
/// (`slot_claims`) — the value the bus flushes IS the flock-proven word.
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

/// Base-field addition (`XOR`) and multiplication share one layout.
struct Arith {
    is_xor: bool,
}

mod arith {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    // No address column: the bus carries each as the product `fp·o`. No result
    // column either: the destination's flush carries `v_A + v_B` for `XOR` and the
    // base product `v_A·v_B` for `MUL`.
    pub const VA: usize = 5;
    pub const VB: usize = 6;
    pub const RA: usize = 7;
    pub const RB: usize = 8;
    pub const RC: usize = 9;
    pub const RBC: usize = 10;
    pub const N: usize = 11;
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
    fn n_constraints(&self) -> usize {
        0
    }
    fn eval_constraint(&self, _pows: &[F192], _cols: &Cols) -> F192 {
        F192::ZERO
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
        f.memory(Prod(FP, OA, 0), RA, Col(VA));
        f.memory(Prod(FP, OB, 0), RB, Col(VB));
        let result = if self.is_xor {
            Coord::Sum(vec![Col(VA), Col(VB)])
        } else {
            Prod(VA, VB, 0)
        };
        f.memory(Prod(FP, OC, 0), RC, result);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use arith::*;
        let rows = if self.is_xor { &ctx.trace.xor } else { &ctx.trace.mul };
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OA] = map_rows(rows, |r| ctx.g_at(r.aa - r.fp));
        out[OB] = map_rows(rows, |r| ctx.g_at(r.ab - r.fp));
        out[OC] = map_rows(rows, |r| ctx.g_at(r.ac - r.fp));
        out[VA] = map_rows(rows, |r| ctx.mem[r.aa as usize]);
        out[VB] = map_rows(rows, |r| ctx.mem[r.ab as usize]);
        out[RA] = map_rows(rows, |r| r.ra);
        out[RB] = map_rows(rows, |r| r.rb);
        out[RC] = map_rows(rows, |r| r.rc);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}

// ---- extension ADD / MUL ----------------------------------------------------

struct ExtArith {
    is_add: bool,
}

mod ext {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    // No address column, and no result run: each of the three destination cells
    // carries its lane of the result as a form over the operand lanes.
    pub const VA0: usize = 5;
    pub const VB0: usize = 8;
    pub const RA0: usize = 11;
    pub const RB0: usize = 14;
    pub const RC0: usize = 17;
    pub const RBC: usize = 20;
    pub const MEM_A1: usize = 21;
    pub const MEM_A2: usize = 22;
    pub const BASE_A: usize = 23;
    pub const N_ADD: usize = 21;
    pub const N_MUL: usize = 24;
}

/// The result run's three lanes as forms over the operand lanes. `ADD_EXT` is the
/// lane-wise sum; `MUL_EXT` is the tower product with `y³ = y+1`, whose five
/// partial sums fold into `c0 = p0+p3`, `c1 = p1+p3+p4`, `c2 = p2+p4`. Both are
/// degree 2 in the committed lanes, so the destination run carries them and
/// neither the lanes nor the identity that tied them is committed (§5).
fn ext_result(is_add: bool) -> [Coord; 3] {
    use ext::*;
    let (a, b) = ([VA0, VA0 + 1, VA0 + 2], [VB0, VB0 + 1, VB0 + 2]);
    if is_add {
        return std::array::from_fn(|k| Coord::Sum(vec![Col(a[k]), Col(b[k])]));
    }
    let p = |i: usize, j: usize| Prod(a[i], b[j], 0);
    [
        Coord::Sum(vec![p(0, 0), p(1, 2), p(2, 1)]),
        Coord::Sum(vec![p(0, 1), p(1, 0), p(1, 2), p(2, 1), p(2, 2)]),
        Coord::Sum(vec![p(0, 2), p(1, 1), p(2, 0), p(2, 2)]),
    ]
}

impl Table for ExtArith {
    fn opcode_tag(&self) -> F64 {
        if self.is_add { OP_ADD_EXT } else { OP_MUL_EXT }
    }
    fn n_committed_columns(&self) -> usize {
        if self.is_add { ext::N_ADD } else { ext::N_MUL }
    }
    fn count_columns(&self) -> &'static [usize] {
        use ext::*;
        &[RA0, RA0 + 1, RA0 + 2, RB0, RB0 + 1, RB0 + 2, RC0, RC0 + 1, RC0 + 2, RBC]
    }
    fn n_constraints(&self) -> usize {
        // The product itself rides the bus; only the scalar mode's two
        // effective-lane bindings remain, and `ADD_EXT` has neither. They cannot
        // become forms: those lanes feed a product, which would reach degree three.
        if self.is_add { 0 } else { 2 }
    }
    fn eval_constraint(&self, pows: &[F192], cols: &Cols) -> F192 {
        use ext::*;
        if self.is_add {
            return F192::ZERO;
        }
        let full = F192::ONE + cols[BASE_A];
        pows[0] * (cols[VA0 + 1] + full * cols[MEM_A1]) + pows[1] * (cols[VA0 + 2] + full * cols[MEM_A2])
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use ext::*;
        f.state_step(PC, FP);
        let base_a = if self.is_add { Const(F64::ZERO) } else { Col(BASE_A) };
        f.bytecode(
            PC,
            RBC,
            self.opcode_tag(),
            &[Col(OA), Col(OB), Col(OC), base_a, Const(F64::ZERO)],
        );
        let result = ext_result(self.is_add);
        for k in 0usize..3 {
            // The k-th word of a run is the base product times g^k, for free.
            let va = if self.is_add || k == 0 {
                VA0 + k
            } else if k == 1 {
                MEM_A1
            } else {
                MEM_A2
            };
            f.memory(Prod(FP, OA, k as u32), RA0 + k, Col(va));
            f.memory(Prod(FP, OB, k as u32), RB0 + k, Col(VB0 + k));
            f.memory(Prod(FP, OC, k as u32), RC0 + k, result[k].clone());
        }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use ext::*;
        let rows = if self.is_add {
            &ctx.trace.add_ext
        } else {
            &ctx.trace.mul_ext
        };
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OA] = map_rows(rows, |r| ctx.g_at(r.aa - r.fp));
        out[OB] = map_rows(rows, |r| ctx.g_at(r.ab - r.fp));
        out[OC] = map_rows(rows, |r| ctx.g_at(r.ac - r.fp));
        for k in 0..3 {
            out[VA0 + k] = map_rows(rows, |r| {
                if !self.is_add && r.base_a == F64::ONE && k > 0 {
                    F64::ZERO
                } else {
                    ctx.mem[r.aa as usize + k]
                }
            });
            out[VB0 + k] = map_rows(rows, |r| ctx.mem[r.ab as usize + k]);
            out[RA0 + k] = map_rows(rows, |r| r.ra[k]);
            out[RB0 + k] = map_rows(rows, |r| r.rb[k]);
            out[RC0 + k] = map_rows(rows, |r| r.rc[k]);
        }
        if !self.is_add {
            out[MEM_A1] = map_rows(rows, |r| ctx.mem[r.aa as usize + 1]);
            out[MEM_A2] = map_rows(rows, |r| ctx.mem[r.aa as usize + 2]);
            out[BASE_A] = map_rows(rows, |r| r.base_a);
        }
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}

// ---- SET ---------------------------------------------------------------------

struct SetTable;

mod set {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O: usize = 2;
    pub const K: usize = 3;
    pub const R: usize = 4;
    pub const RBC: usize = 5;
    pub const N: usize = 6;
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
    fn n_constraints(&self) -> usize {
        0 // the bus reads the address as `fp·o`, leaving nothing to constrain
    }
    fn eval_constraint(&self, _pows: &[F192], _cols: &Cols) -> F192 {
        F192::ZERO
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
        f.memory(Prod(FP, O, 0), R, Col(K));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use set::*;
        let rows = &ctx.trace.set;
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[O] = map_rows(rows, |r| ctx.g_at(r.o));
        out[K] = map_rows(rows, |r| r.k);
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
    // The pointer word. Being a column is what puts it in K, and the
    // pointer-relative address it forms on the bus, `p·obe`, is a K product for the
    // same reason. The store target is DERIVED from the local cell, the two flags,
    // `pc` and `fp`, so it is no column either.
    pub const P: usize = 7;
    pub const V3: usize = 8;
    pub const R1: usize = 9;
    pub const R2: usize = 10;
    pub const R3: usize = 11;
    pub const RBC: usize = 12;
    pub const N: usize = 13;
}

/// The stored word as a form: `v_2 = (1+f_pc+f_fp)·v_3 + f_pc·(g²·pc) + f_fp·fp`,
/// the flag-selected source, written out in characteristic two. The `pc` source is
/// the virtual return target `g²·pc`, a free `×g²` on the product coordinate.
fn deref_store() -> Coord {
    use deref::*;
    Coord::Sum(vec![
        Col(V3),
        Prod(FPC, V3, 0),
        Prod(FFP, V3, 0),
        Prod(FPC, PC, 2),
        Prod(FFP, FP, 0),
    ])
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
    fn n_constraints(&self) -> usize {
        0
    }
    fn eval_constraint(&self, _pows: &[F192], _cols: &Cols) -> F192 {
        F192::ZERO
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_DEREF, &[Col(OAL), Col(OBE), Col(OGA), Col(FPC), Col(FFP)]);
        // The pointer cell and the local cell are frame-relative; the store target
        // is pointer-relative, so its address is `p·obe` and its value the form.
        f.memory(Prod(FP, OAL, 0), R1, Col(P));
        f.memory(Prod(P, OBE, 0), R2, deref_store());
        f.memory(Prod(FP, OGA, 0), R3, Col(V3));
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

        out[P] = map_rows(rows, |r| r.p);
        out[V3] = map_rows(rows, |r| r.v3);
        out[R1] = map_rows(rows, |r| r.r1);
        out[R2] = map_rows(rows, |r| r.r2);
        out[R3] = map_rows(rows, |r| r.r3);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}

// ---- three-word extension DEREF ---------------------------------------------

struct DerefExtTable;

mod deref_ext {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OAL: usize = 2;
    pub const OBE: usize = 3;
    pub const OGA: usize = 4;
    pub const P: usize = 5;
    // Only the heap run's THIRD word is a column: in two-word mode it is an
    // independent padding read, so nothing derives it. Its first two words are the
    // local run's, which is what the equality said.
    pub const V22: usize = 6;
    pub const V30: usize = 7;
    pub const R1: usize = 10;
    pub const R20: usize = 11;
    pub const R30: usize = 14;
    pub const RBC: usize = 17;
    pub const WIDTH3: usize = 18;
    pub const N: usize = 19;
}

/// The heap run's three words as forms. Words 0 and 1 are always the local run's,
/// so they are that column outright. Word 2 is `w·v3_2 + (1+w)·v2_2`: the local
/// lane in three-word mode, its own independent read in two-word mode. All degree
/// 2, which is the whole width-selected equality, so the table has no identity.
fn deref_ext_run() -> [Coord; 3] {
    use deref_ext::*;
    [
        Col(V30),
        Col(V30 + 1),
        Coord::Sum(vec![Prod(WIDTH3, V30 + 2, 0), Col(V22), Prod(WIDTH3, V22, 0)]),
    ]
}

impl Table for DerefExtTable {
    fn opcode_tag(&self) -> F64 {
        OP_DEREF_EXT
    }
    fn n_committed_columns(&self) -> usize {
        deref_ext::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use deref_ext::*;
        &[R1, R20, R20 + 1, R20 + 2, R30, R30 + 1, R30 + 2, RBC]
    }
    fn n_constraints(&self) -> usize {
        0
    }
    fn eval_constraint(&self, _pows: &[F192], _cols: &Cols) -> F192 {
        F192::ZERO
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref_ext::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            OP_DEREF_EXT,
            &[Col(OAL), Col(OBE), Col(OGA), Col(WIDTH3), Const(F64::ZERO)],
        );
        f.memory(Prod(FP, OAL, 0), R1, Col(P));
        let heap = deref_ext_run();
        for k in 0usize..3 {
            f.memory(Prod(P, OBE, k as u32), R20 + k, heap[k].clone());
            f.memory(Prod(FP, OGA, k as u32), R30 + k, Col(V30 + k));
        }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use deref_ext::*;
        let rows = &ctx.trace.deref_ext;
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OAL] = map_rows(rows, |r| ctx.g_at(r.alpha));
        out[OBE] = map_rows(rows, |r| ctx.g_at(r.beta));
        out[OGA] = map_rows(rows, |r| ctx.g_at(r.gamma));
        out[P] = map_rows(rows, |r| r.p);
        out[WIDTH3] = map_rows(rows, |r| r.width3);
        // Only the heap run's third word: the first two ARE the local run's.
        out[V22] = map_rows(rows, |r| r.v2[2]);
        for k in 0..3 {
            out[V30 + k] = map_rows(rows, |r| r.v3[k]);
            out[R20 + k] = map_rows(rows, |r| r.r2[k]);
            out[R30 + k] = map_rows(rows, |r| r.r3[k]);
        }
        out[R1] = map_rows(rows, |r| r.r1);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    // The successor state is DERIVED from `b`, the words read and `(pc, fp)`, so
    // neither `next_pc` nor `next_fp` is a column, and no address is either.
    pub const OC: usize = 2;
    pub const OD: usize = 3;
    pub const OF: usize = 4;
    pub const C: usize = 5;
    pub const D: usize = 6;
    pub const F: usize = 7;
    pub const RC: usize = 8;
    pub const RD: usize = 9;
    pub const RF: usize = 10;
    pub const RBC: usize = 11;
    pub const W: usize = 12;
    pub const B: usize = 13;
    pub const N: usize = 14;
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
    fn n_constraints(&self) -> usize {
        2 // the two indicator identities; the selections ride the state push
    }
    fn eval_constraint(&self, pows: &[F192], cols: &Cols) -> F192 {
        use jump::*;
        // `b = cond·w` and `cond·(b+1) = 0` together force `b = [cond ≠ 0]` (doc
        // §7.5): when `cond ≠ 0` the second gives `b = 1` (and the first
        // `w = cond⁻¹`); when `cond = 0` the first gives `b = 0`. The two selections
        // need no identity: the state push carries each as its own coordinate.
        pows[0] * (cols[B] + cols[C] * cols[W]) + pows[1] * (cols[C] * (cols[B] + F192::ONE))
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use jump::*;
        // The successor state is DERIVED: `b·d + (b+1)·g·pc` and `b·f + (b+1)·fp`,
        // each degree 2 in K columns, written out in characteristic 2 as
        // `b·d + b·(g·pc) + g·pc`. Both force the chosen word into K, which is what
        // the dropped selection identities did.
        f.state_derived(
            PC,
            FP,
            Coord::Sum(vec![Prod(B, D, 0), Prod(B, PC, 1), GCol(PC, 1)]),
            Coord::Sum(vec![Prod(B, F, 0), Prod(B, FP, 0), Col(FP)]),
        );
        f.bytecode(
            PC,
            RBC,
            OP_JUMP,
            &[Col(OC), Col(OD), Col(OF), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(Prod(FP, OC, 0), RC, Col(C));
        f.memory(Prod(FP, OD, 0), RD, Col(D));
        f.memory(Prod(FP, OF, 0), RF, Col(F));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [Column]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        out[PC] = map_rows(rows, |r| ctx.g_at(r.pc));
        out[FP] = map_rows(rows, |r| ctx.g_at(r.fp));
        out[OC] = map_rows(rows, |r| ctx.g_at(r.oc));
        out[OD] = map_rows(rows, |r| ctx.g_at(r.od));
        out[OF] = map_rows(rows, |r| ctx.g_at(r.of));
        out[C] = map_rows(rows, |r| r.c);
        out[D] = map_rows(rows, |r| r.d);
        out[F] = map_rows(rows, |r| r.f);
        out[W] = map_rows(rows, |r| r.w);
        out[B] = map_rows(rows, |r| r.b);
        out[RC] = map_rows(rows, |r| r.rc);
        out[RD] = map_rows(rows, |r| r.rd);
        out[RF] = map_rows(rows, |r| r.rf);
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}

// ---- BLAKE3 ------------------------------------------------------------------

/// `BLAKE3` (doc §7.6): each 256-bit input is addressed as two independent
/// 128-bit chunks (`aa0`, `aa1` and `ab0`, `ab1`), each covering two
/// consecutive base-field words. The output is four consecutive words at
/// `ac`. Five start addresses are committed and bound to bytecode operands;
/// the other seven addresses are virtual generator multiples. The compression
/// relating output words to input words carries no table constraint here: it is
/// proven by flock's R1CS validity via `q_flock` (§blake3_flock).
///
/// The twelve flock words are twelve virtual value columns. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL — not committed —
/// and routes their bus claims to `q_flock`, which already holds those words (see
/// [`BLAKE3_VALUE_COLS`]).
struct Blake3Table;

pub(crate) mod blake3t {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA0: usize = 2;
    pub const OA1: usize = 3;
    pub const OB0: usize = 4;
    pub const OB1: usize = 5;
    pub const OCV: usize = 6;
    pub const OC: usize = 7;
    // No address column: each rides the bus as the product `fp·o_X` times a free
    // `g^k` for the run's k-th successor.
    pub const VA0: usize = 8;
    pub const VB0: usize = 12;
    pub const VC0: usize = 16;
    pub const VCV0: usize = 20;
    pub const MD0: usize = 24;
    pub const MD1: usize = 25;
    pub const RA0: usize = 26;
    pub const RB0: usize = 30;
    pub const RCV0: usize = 34;
    pub const RC0: usize = 38;
    pub const RBC: usize = 42;
    pub const N: usize = 43;
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
            RCV0,
            RCV0 + 1,
            RCV0 + 2,
            RCV0 + 3,
            RC0,
            RC0 + 1,
            RC0 + 2,
            RC0 + 3,
            RBC,
        ]
    }
    fn n_constraints(&self) -> usize {
        // The bus reads each address as `fp·o`, and flock's R1CS validity proves
        // the compression via q_flock (§blake3_flock), so nothing is left.
        0
    }
    fn eval_constraint(&self, _pows: &[F192], _cols: &Cols) -> F192 {
        F192::ZERO
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
        for k in 0usize..4 {
            // A chunk is two consecutive words, so its second is the base product
            // times g; the chaining value and output are four, at g^0..g^3.
            let oa = if k < 2 { OA0 } else { OA1 };
            let ob = if k < 2 { OB0 } else { OB1 };
            let within = (k % 2) as u32;
            f.memory(Prod(FP, oa, within), RA0 + k, Col(VA0 + k));
            f.memory(Prod(FP, ob, within), RB0 + k, Col(VB0 + k));
            f.memory(Prod(FP, OCV, k as u32), RCV0 + k, Col(VCV0 + k));
            f.memory(Prod(FP, OC, k as u32), RC0 + k, Col(VC0 + k));
        }
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
        for k in 0..4 {
            out[VA0 + k] = map_rows(rows, |r| r.va[k]);
            out[VB0 + k] = map_rows(rows, |r| r.vb[k]);
            out[VC0 + k] = map_rows(rows, |r| r.vc[k]);
            out[VCV0 + k] = map_rows(rows, |r| r.vcv[k]);
            out[RCV0 + k] = map_rows(rows, |r| r.rcv[k]);
        }
        out[MD0] = map_rows(rows, |r| r.metadata[0]);
        out[MD1] = map_rows(rows, |r| r.metadata[1]);
        for k in 0..4 {
            out[RA0 + k] = map_rows(rows, |r| r.ra[k]);
            out[RB0 + k] = map_rows(rows, |r| r.rb[k]);
            out[RC0 + k] = map_rows(rows, |r| r.rc[k]);
        }
        out[RBC] = map_rows(rows, |r| r.bytecode_read);
    }
}
