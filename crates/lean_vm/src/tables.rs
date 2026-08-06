//! Per-instruction tables (`doc/body/07-instruction-tables.tex`). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.
//!
//! Columns are `K`-valued (`F64`). The pc/fp, operands, counts, opcodes,
//! separators and every memory word are single `K`-columns. Nothing a row DERIVES
//! is a column at all: an operand address `fp·o`, an `XOR`/`MUL` result, an
//! extension result lane, the `DEREF` store, the `DEREF_WIDE` run, the `JUMP`
//! successors are each written out as the degree-2 bus coordinate that carries
//! them (§sec:m3), and a `g^k` factor on such a product reaches a run's `k`-th
//! successor for free. That leaves two identities in the whole machine: `JUMP`'s
//! is-nonzero indicator, and `MUL_EXT`'s scalar mode, whose effective lanes feed a
//! product and so cannot themselves be forms without reaching degree three. A
//! constraint is evaluated at an `E`-point after the table joins the batch, so
//! each is written once against [`ColVal`] and instantiated over both `F64` and
//! `F192`.

use crate::colval::ColVal;
use crate::cpu::{Brow, Drow, EDrow, Erow, Jrow, Op, Srow, Trace};
use crate::leaf::Coord::{self, Col, Const, GCol, Prod};
use primitives::field::{F64, F192, mul_by_g};

// ---- the identities ----------------------------------------------------------
//
// Each is written ONCE, generic over the column type: `F64` in the round a table
// joins the batch, `F192` afterwards (see [`ColVal`]). Products of two `K`
// columns stay 64-bit, an `η`-power or a word multiplies through `mul_e`, and a
// three-word extension value from three `K` lanes costs nothing to assemble.

/// `MUL_EXT_BASE` reads its first operand as a single base word. `base_a = 1`
/// forces that run's two upper lanes to zero while leaving the cells' actual
/// contents (`MEM_A1`, `MEM_A2`) free, so the memory bus still balances. These two
/// stay identities rather than becoming coordinates: the effective lanes are
/// multiplied by the other operand's, and an effective lane that was itself a form
/// would put that product at degree three.
fn ext_identity<T: ColVal>(pows: &[F192], cols: &[T]) -> F192 {
    use ext::*;
    let full = T::ONE + cols[BASE_A];
    (cols[VA0 + 1] + full * cols[MEM_A1]).mul_e(pows[0]) + (cols[VA0 + 2] + full * cols[MEM_A2]).mul_e(pows[1])
}

fn jump_identity<T: ColVal>(pows: &[F192], cols: &[T]) -> F192 {
    use jump::*;
    let b1 = cols[B] + T::ONE;
    // `b = cond·w` and `cond·(b+1) = 0` together force `b = [cond ≠ 0]`:
    // when `cond ≠ 0` the second gives `b = 1` (and the first `w = cond⁻¹`);
    // when `cond = 0` the first gives `b = 0`. The two selections need no identity:
    // the state push carries each as its own degree-2 coordinate (§sec:m3).
    (cols[B] + cols[C] * cols[W]).mul_e(pows[0]) + (cols[C] * b1).mul_e(pows[1])
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

    /// Explicit state transition (JUMP): push the next state, which the row
    /// DERIVES from its columns rather than committing, and pull `(pc, fp)`.
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

    /// Memory access to one base-field word at `addr`, with the cell's access
    /// count advanced by ×g on the push side.
    pub(crate) fn memory(&mut self, addr: Coord, count: usize, val: usize) {
        self.memory_coord(addr, count, Col(val));
    }

    /// The same, for a word the row DERIVES rather than commits (an `XOR`/`MUL`
    /// result, a `DEREF` store): the cell holds whatever the form says, which
    /// removes both the value column and the identity that used to tie them
    /// (§sec:m3).
    pub(crate) fn memory_coord(&mut self, addr: Coord, count: usize, val: Coord) {
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
    pub(crate) prog: &'a [Op],
    /// This table's height `2^tau`, the length of every window in `out`, and its row
    /// count too: every row is a row the program executed (`cpu::filler`).
    pub(crate) rows: usize,
    /// Which local columns [`Self::col`] / [`Self::cols`] have written. A fill that
    /// misses one would leave the stacked witness holding uninitialized slots, so
    /// [`fill_table`] checks the whole set was covered.
    written: std::sync::atomic::AtomicU64,
}

/// Where one column's values go: its window in the stacked witness, or a private
/// buffer if the column is virtual.
pub type ColumnOut<'a> = &'a mut [F64];

impl<'a> FillCtx<'a> {
    pub(crate) fn new(trace: &'a Trace, mem: &'a [F64], gpow: &'a [F64], prog: &'a [Op], rows: usize) -> Self {
        Self {
            trace,
            mem,
            gpow,
            prog,
            rows,
            written: std::sync::atomic::AtomicU64::new(0),
        }
    }

    fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }

    /// The three frame offsets of an `XOR`/`MUL`/extension-arithmetic row. A row
    /// records only its `(pc, fp)`; the operands are the instruction's, so they
    /// are read back from the bytecode rather than copied into every row (§the
    /// trace rows in `cpu::trace`).
    fn ternary_operands(&self, pc: u32) -> (u32, u32, u32) {
        match self.prog[pc as usize] {
            Op::Xor { a, b, c }
            | Op::Mul { a, b, c }
            | Op::AddExt { a, b, c }
            | Op::MulExt { a, b, c }
            | Op::MulExtBase { a, b, c } => (a, b, c),
            op => unreachable!("a three-operand row's pc {pc} holds {op:?}"),
        }
    }

    /// Write local column `at`: `f` over the trace rows, then its pad value to the
    /// end of the window.
    fn col<R: Sync>(&self, out: &mut [ColumnOut], rows: &[R], at: usize, f: impl Fn(&R) -> F64 + Sync) {
        self.cols(out, rows, at, |r| [f(r)]);
    }

    /// Write the `N` local columns at `at..at + N` from one closure per row.
    /// Columns fed by the same read fill together: the words of one memory run
    /// are one random access, and splitting them across `N` passes pays for it
    /// `N` times.
    fn cols<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &[R],
        at: usize,
        f: impl Fn(&R) -> [F64; N] + Sync,
    ) {
        self.cols_at(out, rows.len(), at, |i| f(&rows[i]));
    }

    /// [`Self::cols`] over row indices, for values held in a side buffer rather
    /// than read off the row.
    fn cols_at<const N: usize>(
        &self,
        out: &mut [ColumnOut],
        n_rows: usize,
        at: usize,
        f: impl Fn(usize) -> [F64; N] + Sync,
    ) {
        let n = self.rows;
        let dst: [parallel::SendPtr<F64>; N] = std::array::from_fn(|k| {
            assert_eq!(out[at + k].len(), n, "column {} has the wrong window length", at + k);
            self.written
                .fetch_or(1 << (at + k), std::sync::atomic::Ordering::Relaxed);
            parallel::SendPtr(out[at + k].as_mut_ptr())
        });
        // Every row is a row the program executed: a table's height is its row
        // count (`cpu::filler`), so there is nothing to pad with.
        assert_eq!(n_rows, n, "a table's rows must fill its cube");
        parallel::for_each(n, |i| {
            let v = f(i);
            for (k, p) in dst.iter().enumerate() {
                // SAFETY: distinct `i` write disjoint in-bounds slots of each of the
                // `N` windows, each exactly once, and the dispatch blocks until
                // every write is finished.
                unsafe { p.add(i).write(v[k]) };
            }
        });
    }

    /// The `N` consecutive memory words based at `addr`.
    fn run<const N: usize>(&self, addr: u32) -> [F64; N] {
        std::array::from_fn(|k| self.mem[addr as usize + k])
    }
}

/// Fill one table's columns and check that every window was written. The stack is
/// allocated uninitialized, so a column the table forgot would be read as
/// indeterminate bytes rather than caught by a length mismatch.
pub(crate) fn fill_table(table: &dyn Table, ctx: &FillCtx, out: &mut [ColumnOut]) {
    table.fill(ctx, out);
    let n = table.n_committed_columns();
    assert!(n <= 64, "the write mask covers at most 64 columns per table");
    let all = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    let written = ctx.written.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(written, all, "a table left one of its columns unwritten");
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
    /// Defaults to none, which is every table but `JUMP`: a relation whose value
    /// rides the bus as a coordinate needs no identity to tie it (§sec:m3).
    fn n_constraints(&self) -> usize {
        0
    }
    /// Evaluate the table's degree-2 constraint at one row, reading column values
    /// by local index from `cols` (e.g. `cols[arith::VA]`) and weighting identity
    /// `i` by `pows[i]`, this table's slice of the batch's `eta`-powers. The slice is
    /// is exactly [`n_constraints`](Table::n_constraints) long: an identity indexed
    /// past its end panics rather than silently reaching into the next table's
    /// range. The batched zerocheck carries every committed column of a table, in
    /// local order, so `cols` is indexed directly. Returns `0` on every valid row (§sec:air).
    /// The default is the constraint-free case; a table that declares constraints
    /// and forgets to evaluate them trips the assert instead of dropping them.
    fn eval_constraint(&self, pows: &[F192], _cols: &[F192]) -> F192 {
        assert!(pows.is_empty(), "a table with constraints must evaluate them");
        F192::ZERO
    }
    /// The same identity over `K`-valued columns, for the round a table joins the
    /// batch, before its columns have been folded into `E` (§sec:air). Both entry
    /// points delegate to one generic definition per table, so they cannot drift.
    fn eval_constraint_k(&self, pows: &[F192], _cols: &[F64]) -> F192 {
        assert!(pows.is_empty(), "a table with constraints must evaluate them");
        F192::ZERO
    }
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns from the trace: `out[i]` is local column `i`'s
    /// window, already at its padded length. Every window must be written in full;
    /// use `FillCtx::col` / `FillCtx::cols`, which append the column's pad value
    /// past the last trace row and record the coverage `fill_table` checks.
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]);
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

/// Index of the scalar `DEREF` table in [`tables`].
pub const DEREF_TABLE: usize = 5;

/// The six base addresses a `BLAKE3` row reads: the four message-chunk bases
/// (two words each), the chaining-value base and the output base (four words
/// each). Recovered from the instruction, not stored per row.
pub(crate) fn blake3_addresses(prog: &[Op], r: &Brow) -> [u32; 6] {
    match prog[r.pc as usize] {
        Op::Blake3 { ins, cv, out, .. } => [
            r.fp + ins[0],
            r.fp + ins[1],
            r.fp + ins[2],
            r.fp + ins[3],
            r.fp + cv,
            r.fp + out,
        ],
        op => unreachable!("a BLAKE3 row's pc {} holds {op:?}", r.pc),
    }
}

/// A `BLAKE3` row's metadata immediate (`counter | block_len‖flags`), as its two
/// base-field lanes.
pub(crate) fn blake3_metadata(prog: &[Op], pc: u32) -> [F64; 2] {
    match prog[pc as usize] {
        Op::Blake3 { metadata, .. } => metadata,
        op => unreachable!("a BLAKE3 row's pc {pc} holds {op:?}"),
    }
}

/// BLAKE3 value-column LOCAL indices in canonical slot order
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]` (matches
/// `blake3_flock::SLOTS`). These columns are
/// VIRTUAL (never committed): `q_flock` already holds those words at fixed packed
/// slots, so `cpu` routes their memory-bus evaluation claims straight to `q_flock`
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
    // No absolute-address columns: the memory bus carries `fp·o` as a product
    // coordinate (§sec:m3), which is why there is no address binding below.
    // The two read words. The third, the result, is DERIVED.
    pub const VA: usize = 5;
    pub const VB: usize = 6;
    pub const RA: usize = 7;
    pub const RB: usize = 8;
    pub const RC: usize = 9;
    pub const RBC: usize = 10;
    pub const N: usize = 11;
}

impl Table for Arith {
    fn n_committed_columns(&self) -> usize {
        arith::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use arith::*;
        &[RA, RB, RC, RBC]
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
        f.memory(Prod(FP, OA, 0), RA, VA);
        f.memory(Prod(FP, OB, 0), RB, VB);
        // The destination cell holds the result, carried as a degree-≤2 coordinate
        // over the operand columns, so bus balance IS the assertion: `v_A + v_B`
        // for `XOR`, the base product `v_A·v_B` for `MUL`.
        let result = if self.is_xor {
            Coord::Sum(vec![Col(VA), Col(VB)])
        } else {
            Prod(VA, VB, 0)
        };
        f.memory_coord(Prod(FP, OC, 0), RC, result);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use arith::*;
        let rows = if self.is_xor { &ctx.trace.xor } else { &ctx.trace.mul };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [ctx.g_at(a), ctx.g_at(b), ctx.g_at(c)]
        });
        ctx.cols(out, rows, VA, |r| {
            let (a, b, _) = ctx.ternary_operands(r.pc);
            [ctx.mem[(r.fp + a) as usize], ctx.mem[(r.fp + b) as usize]]
        });
        ctx.cols(out, rows, RA, |r| [r.ra, r.rb, r.rc]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- extension ADD / MUL ----------------------------------------------------

/// `ADD_EXT` / `MUL_EXT`: each operand is a run of three consecutive base words
/// read as one `E` value. Only the run's base rides the bus as `fp·o`; its two
/// successors are the same product times `g` and `g²` (§sec:m3).
struct ExtArith {
    is_add: bool,
}

mod ext {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    // The two read runs. The third, the result, is DERIVED lane by lane.
    pub const VA0: usize = 5;
    pub const VB0: usize = 8;
    pub const RA0: usize = 11;
    pub const RB0: usize = 14;
    pub const RC0: usize = 17;
    pub const RBC: usize = 20;
    // `MUL_EXT_BASE` only: the two upper cells of the first operand's run, read
    // for the bus but forced out of the value by `BASE_A`.
    pub const MEM_A1: usize = 21;
    pub const MEM_A2: usize = 22;
    pub const BASE_A: usize = 23;
    pub const N_ADD: usize = 21;
    pub const N_MUL: usize = 24;
}

/// The result run's three lanes as forms over the operand lanes. `ADD_EXT` is the
/// lane-wise sum; `MUL_EXT` is the tower product with `y³ = y+1`, whose five
/// partial sums fold into `c0 = p0+p3`, `c1 = p1+p3+p4`, `c2 = p2+p4`. Both are
/// degree 2 in the committed lanes, so the destination run carries them on the bus
/// and neither the lanes nor the identity that tied them is committed (§sec:m3).
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
    fn n_committed_columns(&self) -> usize {
        if self.is_add { ext::N_ADD } else { ext::N_MUL }
    }
    fn count_columns(&self) -> &'static [usize] {
        use ext::*;
        &[RA0, RA0 + 1, RA0 + 2, RB0, RB0 + 1, RB0 + 2, RC0, RC0 + 1, RC0 + 2, RBC]
    }
    fn n_constraints(&self) -> usize {
        // The product itself rides the bus; only the scalar mode's two
        // effective-lane bindings remain, and `ADD_EXT` has neither.
        if self.is_add { 0 } else { 2 }
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        if self.is_add { F192::ZERO } else { ext_identity(pows, cols) }
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        if self.is_add { F192::ZERO } else { ext_identity(pows, cols) }
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use ext::*;
        f.state_step(PC, FP);
        let base_a = if self.is_add { Const(F64::ZERO) } else { Col(BASE_A) };
        f.bytecode(
            PC,
            RBC,
            if self.is_add { OP_ADD_EXT } else { OP_MUL_EXT },
            &[Col(OA), Col(OB), Col(OC), base_a, Const(F64::ZERO)],
        );
        let result = ext_result(self.is_add);
        for k in 0u32..3 {
            // The k-th word of a run is the base product times g^k, for free.
            let va = if self.is_add || k == 0 {
                VA0 + k as usize
            } else if k == 1 {
                MEM_A1
            } else {
                MEM_A2
            };
            f.memory(Prod(FP, OA, k), RA0 + k as usize, va);
            f.memory(Prod(FP, OB, k), RB0 + k as usize, VB0 + k as usize);
            f.memory_coord(Prod(FP, OC, k), RC0 + k as usize, result[k as usize].clone());
        }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use ext::*;
        let rows = if self.is_add {
            &ctx.trace.add_ext
        } else {
            &ctx.trace.mul_ext
        };
        // `MUL_EXT_BASE` shares the MUL_EXT table and differs only in this flag.
        let base_a = |r: &Erow| match ctx.prog[r.pc as usize] {
            Op::MulExtBase { .. } => F64::ONE,
            _ => F64::ZERO,
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [ctx.g_at(a), ctx.g_at(b), ctx.g_at(c)]
        });
        ctx.cols(out, rows, VA0, |r| {
            let a = r.fp + ctx.ternary_operands(r.pc).0;
            let w: [F64; 3] = ctx.run(a);
            if base_a(r) == F64::ONE { [w[0], F64::ZERO, F64::ZERO] } else { w }
        });
        ctx.cols(out, rows, VB0, |r| ctx.run::<3>(r.fp + ctx.ternary_operands(r.pc).1));
        ctx.cols(out, rows, RA0, |r| r.ra);
        ctx.cols(out, rows, RB0, |r| r.rb);
        ctx.cols(out, rows, RC0, |r| r.rc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
        if !self.is_add {
            ctx.cols(out, rows, MEM_A1, |r| {
                let a = r.fp + ctx.ternary_operands(r.pc).0;
                [ctx.mem[a as usize + 1], ctx.mem[a as usize + 2]]
            });
            ctx.col(out, rows, BASE_A, base_a);
        }
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
    fn n_committed_columns(&self) -> usize {
        set::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use set::*;
        &[R, RBC]
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
        // The stored constant K is the cell's value.
        f.memory(Prod(FP, O, 0), R, K);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use set::*;
        let rows = &ctx.trace.set;
        // The offset and the stored immediate are the instruction's.
        let imm = |r: &Srow| match ctx.prog[r.pc as usize] {
            Op::Set { o, k } => (o, k),
            op => unreachable!("a SET row's pc {} holds {op:?}", r.pc),
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, O, |r| {
            let (o, k) = imm(r);
            [ctx.g_at(o), k]
        });
        ctx.col(out, rows, R, |r| r.r);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
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
    // pointer-relative address it forms on the bus, `p·obe`, is a K product for
    // the same reason.
    pub const P: usize = 7;
    // The local cell. The store target is DERIVED from it, the two flags, `pc`
    // and `fp`, so it is no column.
    pub const V3: usize = 8;
    pub const R1: usize = 9;
    pub const R2: usize = 10;
    pub const R3: usize = 11;
    pub const RBC: usize = 12;
    pub const N: usize = 13;
}

/// The stored word as a form: `v_2 = (1+f_pc+f_fp)·v_3 + f_pc·(g²·pc) + f_fp·fp`,
/// the flag-selected source of §sec:tab-deref, written out in characteristic two.
/// The `pc` source is the virtual return target `g²·pc`, a free `×g²` on the
/// product coordinate.
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
    fn n_committed_columns(&self) -> usize {
        deref::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use deref::*;
        &[R1, R2, R3, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_DEREF, &[Col(OAL), Col(OBE), Col(OGA), Col(FPC), Col(FFP)]);
        // The pointer cell and the local cell are frame-relative; the store target
        // is pointer-relative, so its address is `p·obe`.
        f.memory(Prod(FP, OAL, 0), R1, P);
        f.memory_coord(Prod(P, OBE, 0), R2, deref_store());
        f.memory(Prod(FP, OGA, 0), R3, V3);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use deref::*;
        let rows = &ctx.trace.deref;
        // Offsets and store mode are the instruction's. Neither the store target's
        // address nor its value is committed.
        let ins = |r: &Drow| match ctx.prog[r.pc as usize] {
            Op::Deref {
                alpha,
                beta,
                gamma,
                mode,
            } => (alpha, beta, gamma, mode),
            op => unreachable!("a DEREF row's pc {} holds {op:?}", r.pc),
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OAL, |r| {
            let (alpha, beta, gamma, _) = ins(r);
            [ctx.g_at(alpha), ctx.g_at(beta), ctx.g_at(gamma)]
        });
        ctx.cols(out, rows, FPC, |r| {
            let mode = ins(r).3;
            [mode.f_pc(), mode.f_fp()]
        });
        ctx.col(out, rows, P, |r| ctx.mem[(r.fp + ins(r).0) as usize]);
        ctx.col(out, rows, V3, |r| ctx.mem[(r.fp + ins(r).2) as usize]);
        ctx.cols(out, rows, R1, |r| [r.r1, r.r2, r.r3]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- multi-word extension DEREF ---------------------------------------------

struct DerefExtTable;

mod deref_ext {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OAL: usize = 2;
    pub const OBE: usize = 3;
    pub const OGA: usize = 4;
    pub const P: usize = 5;
    // Only the heap run's THIRD word is a column: in two-word mode it is an
    // independent padding read, so nothing derives it. Its first two words are
    // the local run's, which is what the equality said.
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
    fn n_committed_columns(&self) -> usize {
        deref_ext::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use deref_ext::*;
        &[R1, R20, R20 + 1, R20 + 2, R30, R30 + 1, R30 + 2, RBC]
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
        f.memory(Prod(FP, OAL, 0), R1, P);
        let heap = deref_ext_run();
        for k in 0u32..3 {
            f.memory_coord(Prod(P, OBE, k), R20 + k as usize, heap[k as usize].clone());
            f.memory(Prod(FP, OGA, k), R30 + k as usize, V30 + k as usize);
        }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use deref_ext::*;
        let rows = &ctx.trace.deref_ext;
        let ins = |r: &EDrow| match ctx.prog[r.pc as usize] {
            Op::Deref128 { alpha, beta, gamma } | Op::DerefExt { alpha, beta, gamma } => (alpha, beta, gamma),
            op => unreachable!("a DEREF_EXT row's pc {} holds {op:?}", r.pc),
        };
        // `DEREF_128` and `DEREF_EXT` share this table and differ only in width.
        let width3 = |r: &EDrow| match ctx.prog[r.pc as usize] {
            Op::DerefExt { .. } => F64::ONE,
            _ => F64::ZERO,
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OAL, |r| {
            let (alpha, beta, gamma) = ins(r);
            [ctx.g_at(alpha), ctx.g_at(beta), ctx.g_at(gamma)]
        });
        ctx.col(out, rows, P, |r| ctx.mem[(r.fp + ins(r).0) as usize]);
        // Only the heap run's third word: the first two ARE the local run's.
        ctx.col(out, rows, V22, |r| ctx.mem[r.a2 as usize + 2]);
        ctx.cols(out, rows, V30, |r| ctx.run::<3>(r.fp + ins(r).2));
        ctx.col(out, rows, R1, |r| r.r1);
        ctx.cols(out, rows, R20, |r| r.r2);
        ctx.cols(out, rows, R30, |r| r.r3);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
        ctx.col(out, rows, WIDTH3, width3);
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    // The successor state is DERIVED from `b`, the words read and `(pc, fp)`, so
    // neither `next_pc` nor `next_fp` is a column.
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
    // Local witness columns (committed, never flushed): the inverse hint `w`
    // and the taken indicator `b = [c ≠ 0]` it certifies
    // (the `JUMP` table in `doc/body/07-instruction-tables.tex`).
    pub const W: usize = 12;
    pub const B: usize = 13;
    pub const N: usize = 14;
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
        2 // the two indicator identities; the selections ride the state push
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192]) -> F192 {
        jump_identity(pows, cols)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64]) -> F192 {
        jump_identity(pows, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use jump::*;
        // The successor state is DERIVED: `b·d + (b+1)·g·pc` and `b·f + (b+1)·fp`,
        // each degree 2 in K columns, so neither successor is committed. Written
        // out in characteristic 2 as `b·d + b·(g·pc) + g·pc`.
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
        f.memory(Prod(FP, OC, 0), RC, C);
        f.memory(Prod(FP, OD, 0), RD, D);
        f.memory(Prod(FP, OF, 0), RF, F);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        let ins = |r: &Jrow| match ctx.prog[r.pc as usize] {
            Op::Jump { oc, od, of } => (oc, od, of),
            op => unreachable!("a JUMP row's pc {} holds {op:?}", r.pc),
        };
        let cell = |r: &Jrow, o: u32| ctx.mem[(r.fp + o) as usize];
        let cond = |r: &Jrow| cell(r, ins(r).0);
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OC, |r| {
            let (oc, od, of) = ins(r);
            [ctx.g_at(oc), ctx.g_at(od), ctx.g_at(of)]
        });
        ctx.cols(out, rows, C, |r| {
            let (oc, od, of) = ins(r);
            [cell(r, oc), cell(r, od), cell(r, of)]
        });
        ctx.cols(out, rows, RC, |r| [r.rc, r.rd, r.rf]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
        // The is-nonzero witness `w = c⁻¹` (0 where c = 0) for every row, in ONE
        // batched Montgomery inversion: a single field inverse plus ~2 multiplies
        // per row, instead of an inverse per taken branch. `prefix[i]` is the
        // running product of the nonzero conditions before row `i`, so `acc` ends
        // as their full product (nonzero, hence invertible).
        let w = {
            let mut acc = F64::ONE;
            let mut prefix: Vec<F64> = Vec::with_capacity(rows.len());
            for r in rows {
                prefix.push(acc);
                let c = cond(r);
                if !c.is_zero() {
                    acc *= c;
                }
            }
            let mut inv = acc.inv();
            let mut w = vec![F64::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate().rev() {
                let c = cond(r);
                if !c.is_zero() {
                    w[i] = inv * prefix[i];
                    inv *= c;
                }
            }
            w
        };
        ctx.cols_at(out, rows.len(), W, |i| [w[i]]);
        ctx.col(out, rows, B, |r| if cond(r).is_zero() { F64::ZERO } else { F64::ONE });
    }
}

// ---- BLAKE3 ------------------------------------------------------------------

/// `BLAKE3` (“BLAKE3” in `doc/body/07-instruction-tables.tex`): one standard compression. The four 128-bit message
/// chunks are addressed *independently* at `fp·o_i` (`o_i = g^{ins[i]}`), each two
/// consecutive words, with no forced contiguity between chunks, so a caller hashing
/// e.g. `(tweak, pp)` need not copy them into adjacent cells. The chaining value and
/// the 32-byte output each occupy four consecutive words, based at `fp·o_cv` and
/// `fp·o_c`, so the row reads twelve words in all. No address is committed: each rides
/// the bus as the product `fp·o_X` times a free `g^k` (§sec:m3). The compression
/// relating output words to input words carries no table constraint either: it is
/// proven by flock's R1CS validity via `q_flock` (§blake3_flock), which leaves this
/// table with no identity of its own.
///
/// The eighteen flock words are eighteen virtual value columns. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL (not committed)
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
    pub const OCV: usize = 6; // … the chaining-value base …
    pub const OC: usize = 7; // … and the output base
    // The eighteen flock words as value lanes: a's two chunks, b's two chunks,
    // the four output words, the four chaining-value words, then the bytecode
    // metadata immediate's two lanes.
    pub const VA0: usize = 8;
    pub const VB0: usize = 12;
    pub const VC0: usize = 16;
    pub const VCV0: usize = 20;
    pub const MD0: usize = 24; // metadata: the counter lane …
    pub const MD1: usize = 25; // … and the block_len‖flags lane
    pub const RA0: usize = 26; // per-word read counts (the two a chunks) …
    pub const RB0: usize = 30; // … the two b chunks …
    pub const RCV0: usize = 34; // … the four cv words …
    pub const RC0: usize = 38; // … the four output words.
    pub const RBC: usize = 42;
    pub const N: usize = 43;
}

impl Table for Blake3Table {
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
        // Twelve word reads: four two-word message chunks, then the chaining
        // value's and the output's four consecutive words. A consecutive word is a
        // free ×g on the product's g-power, so only the six bases ride an operand.
        for k in 0u32..2 {
            f.memory(Prod(FP, OA0, k), RA0 + k as usize, VA0 + k as usize);
            f.memory(Prod(FP, OA1, k), RA0 + 2 + k as usize, VA0 + 2 + k as usize);
            f.memory(Prod(FP, OB0, k), RB0 + k as usize, VB0 + k as usize);
            f.memory(Prod(FP, OB1, k), RB0 + 2 + k as usize, VB0 + 2 + k as usize);
        }
        for k in 0u32..4 {
            f.memory(Prod(FP, OCV, k), RCV0 + k as usize, VCV0 + k as usize);
            f.memory(Prod(FP, OC, k), RC0 + k as usize, VC0 + k as usize);
        }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use blake3t::*;
        let rows = &ctx.trace.blake3;
        let ad = |r: &Brow| blake3_addresses(ctx.prog, r);
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        // OA0..OC are the six base addresses' offsets, from the instruction decode.
        ctx.cols(out, rows, OA0, |r| ad(r).map(|a| ctx.g_at(a - r.fp)));
        // The sixteen memory-borne flock words: the four message chunks (two words
        // each), then the four output words and the four chaining-value words.
        ctx.cols(out, rows, VA0, |r| {
            let a = ad(r);
            let (c0, c1): ([F64; 2], [F64; 2]) = (ctx.run(a[0]), ctx.run(a[1]));
            [c0[0], c0[1], c1[0], c1[1]]
        });
        ctx.cols(out, rows, VB0, |r| {
            let a = ad(r);
            let (c0, c1): ([F64; 2], [F64; 2]) = (ctx.run(a[2]), ctx.run(a[3]));
            [c0[0], c0[1], c1[0], c1[1]]
        });
        ctx.cols(out, rows, VC0, |r| ctx.run::<4>(ad(r)[5]));
        ctx.cols(out, rows, VCV0, |r| ctx.run::<4>(ad(r)[4]));
        ctx.cols(out, rows, MD0, |r| blake3_metadata(ctx.prog, r.pc));
        ctx.cols(out, rows, RA0, |r| r.ra);
        ctx.cols(out, rows, RB0, |r| r.rb);
        ctx.cols(out, rows, RCV0, |r| r.rcv);
        ctx.cols(out, rows, RC0, |r| r.rc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}
