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
use crate::cpu::{Brow, Drow, Jrow, Op, Srow, Trace, Xrow};
use crate::leaf::Coord::{self, Col, Const, GCol};
use primitives::field::{F64, F192, G, mul_by_g};

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
    // table constraint here: flock's R1CS validity proves it via q_flock.
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
    pub(crate) prog: &'a [Op],
    /// This table's per-column padding values, in local index order: `1 = g^0` for
    /// a count column, else 0, except for the `BLAKE3` output words, which pad with
    /// the padding block's digest (§4.4, §e2e-pad).
    pub(crate) pad: &'a [F64],
    /// This table's padded row count `2^tau`, the length of every window in `out`.
    pub(crate) rows_padded: usize,
    /// Which local columns [`Self::col`] / [`Self::cols`] have written. A fill that
    /// misses one would leave the stacked witness holding uninitialized slots, so
    /// [`fill_table`] checks the whole set was covered.
    written: std::sync::atomic::AtomicU64,
}

/// Where one column's values go: its window in the stacked witness, or a private
/// buffer if the column is virtual.
pub type ColumnOut<'a> = &'a mut [F64];

impl<'a> FillCtx<'a> {
    pub(crate) fn new(
        trace: &'a Trace,
        mem: &'a [F192],
        gpow: &'a [F64],
        prog: &'a [Op],
        pad: &'a [F64],
        rows_padded: usize,
    ) -> Self {
        Self {
            trace,
            mem,
            gpow,
            prog,
            pad,
            rows_padded,
            written: std::sync::atomic::AtomicU64::new(0),
        }
    }

    fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }

    /// The three frame offsets of an `XOR`/`MUL`/`PACK64X2` row. A row records
    /// only its `(pc, fp)`; the operands are the instruction's, so they are read
    /// back from the bytecode rather than copied into every row (§the trace rows
    /// in `cpu::trace`).
    fn ternary_operands(&self, pc: u32) -> (u32, u32, u32) {
        match self.prog[pc as usize] {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } | Op::Pack64x2 { a, b, c } => (a, b, c),
            op => unreachable!("a three-operand row's pc {pc} holds {op:?}"),
        }
    }

    /// Write local column `at`: `f` over the trace rows, then its pad value to the
    /// end of the window.
    fn col<R: Sync>(&self, out: &mut [ColumnOut], rows: &[R], at: usize, f: impl Fn(&R) -> F64 + Sync) {
        self.cols(out, rows, at, |r| [f(r)]);
    }

    /// Write the `N` local columns at `at..at + N` from one closure per row.
    /// Columns fed by the same read fill together: the three lanes of a 192-bit
    /// memory word are one random access, and splitting them across `N` passes
    /// pays for it `N` times.
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
        let n = self.rows_padded;
        let dst: [parallel::SendPtr<F64>; N] = std::array::from_fn(|k| {
            assert_eq!(out[at + k].len(), n, "column {} has the wrong window length", at + k);
            self.written
                .fetch_or(1 << (at + k), std::sync::atomic::Ordering::Relaxed);
            parallel::SendPtr(out[at + k].as_mut_ptr())
        });
        let pad: [F64; N] = std::array::from_fn(|k| self.pad[at + k]);
        parallel::for_each(n, |i| {
            let v = if i < n_rows { f(i) } else { pad };
            for (k, p) in dst.iter().enumerate() {
                // SAFETY: distinct `i` write disjoint in-bounds slots of each of the
                // `N` windows, each exactly once, and the dispatch blocks until
                // every write is finished.
                unsafe { p.add(i).write(v[k]) };
            }
        });
    }

    /// The three `K`-lanes of the 192-bit word in memory cell `addr`.
    fn limbs(&self, addr: u32) -> [F64; 3] {
        let w = self.mem[addr as usize];
        [F64(w.c0), F64(w.c1), F64(w.c2)]
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
    /// Fill this table's columns from the trace: `out[i]` is local column `i`'s
    /// window, already at its padded length. Every window must be written in full;
    /// use [`FillCtx::col`] / [`FillCtx::cols`], which append the column's pad value
    /// past the last trace row and record the coverage [`fill_table`] checks.
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]);
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

/// The six base addresses a `BLAKE3` row reads: the four message cells, the
/// chaining-value base and the output base (each of the last two spans that cell
/// and its successor). Recovered from the instruction, not stored per row.
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

/// A `BLAKE3` row's metadata immediate (`counter | block_len‖flags`).
pub(crate) fn blake3_metadata(prog: &[Op], pc: u32) -> F192 {
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
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use arith::*;
        let rows = if self.is_xor { &ctx.trace.xor } else { &ctx.trace.mul };
        let addrs = |r: &Xrow| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [r.fp + a, r.fp + b, r.fp + c]
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [ctx.g_at(a), ctx.g_at(b), ctx.g_at(c)]
        });
        ctx.cols(out, rows, AA, |r| addrs(r).map(|a| ctx.g_at(a)));
        ctx.cols(out, rows, VA_LO, |r| ctx.limbs(addrs(r)[0]));
        ctx.cols(out, rows, VB_LO, |r| ctx.limbs(addrs(r)[1]));
        ctx.cols(out, rows, VC_LO, |r| ctx.limbs(addrs(r)[2]));
        ctx.cols(out, rows, RA, |r| [r.ra, r.rb, r.rc]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
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
        ctx.col(out, rows, O, |r| ctx.g_at(imm(r).0));
        ctx.cols(out, rows, K_LO, |r| {
            let k = imm(r).1;
            [F64(k.c0), F64(k.c1), F64(k.c2)]
        });
        ctx.col(out, rows, A, |r| ctx.g_at(r.fp + imm(r).0));
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
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use deref::*;
        let rows = &ctx.trace.deref;
        // Offsets and store mode are the instruction's; the pointer cell and the
        // local cell sit at `fp` plus two of them. Only the store target `a2`,
        // which needs the pointer's discrete log, rides the row.
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
        ctx.cols(out, rows, A1, |r| {
            let (alpha, _, gamma, _) = ins(r);
            [ctx.g_at(r.fp + alpha), ctx.g_at(r.a2), ctx.g_at(r.fp + gamma)]
        });
        debug_assert!(
            rows.iter().all(|r| {
                let p = ctx.mem[(r.fp + ins(r).0) as usize];
                p.c1 == 0 && p.c2 == 0
            }),
            "deref pointer must be K-valued"
        );
        ctx.col(out, rows, P, |r| F64(ctx.mem[(r.fp + ins(r).0) as usize].c0));
        ctx.cols(out, rows, V2_LO, |r| ctx.limbs(r.a2));
        ctx.cols(out, rows, V3_LO, |r| ctx.limbs(r.fp + ins(r).2));
        ctx.cols(out, rows, R1, |r| [r.r1, r.r2, r.r3]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
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
        // The successor state: a taken branch goes to the destination/frame words
        // it read, an untaken one falls through to `(g·pc, fp)`.
        ctx.cols(out, rows, NPC, |r| {
            let (oc, od, of) = ins(r);
            if cell(r, oc).is_zero() {
                [mul_by_g(ctx.g_at(r.pc)), ctx.g_at(r.fp)]
            } else {
                [F64(cell(r, od).c0), F64(cell(r, of).c0)]
            }
        });
        ctx.cols(out, rows, OC, |r| {
            let (oc, od, of) = ins(r);
            [ctx.g_at(oc), ctx.g_at(od), ctx.g_at(of)]
        });
        ctx.cols(out, rows, AC, |r| {
            let (oc, od, of) = ins(r);
            [ctx.g_at(r.fp + oc), ctx.g_at(r.fp + od), ctx.g_at(r.fp + of)]
        });
        ctx.cols(out, rows, C_LO, |r| ctx.limbs(r.fp + ins(r).0));
        ctx.cols(out, rows, D_LO, |r| ctx.limbs(r.fp + ins(r).1));
        ctx.cols(out, rows, F_LO, |r| ctx.limbs(r.fp + ins(r).2));
        // The is-nonzero witness `w = c⁻¹` (0 where c = 0) for every row, in ONE
        // batched Montgomery inversion: a single field inverse plus ~2 multiplies
        // per row, instead of an inverse per taken branch. `prefix[i]` is the
        // running product of the nonzero conditions before row `i`, so `acc` ends
        // as their full product (nonzero, hence invertible).
        let w = {
            let mut acc = F192::ONE;
            let mut prefix: Vec<F192> = Vec::with_capacity(rows.len());
            for r in rows {
                prefix.push(acc);
                let c = cond(r);
                if !c.is_zero() {
                    acc *= c;
                }
            }
            let mut inv = acc.inv();
            let mut w = vec![F192::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate().rev() {
                let c = cond(r);
                if !c.is_zero() {
                    w[i] = inv * prefix[i];
                    inv *= c;
                }
            }
            w
        };
        ctx.cols_at(out, rows.len(), W_LO, |i| [F64(w[i].c0), F64(w[i].c1), F64(w[i].c2)]);
        ctx.col(out, rows, B, |r| if cond(r).is_zero() { F64::ZERO } else { F64::ONE });
        ctx.cols(out, rows, RC, |r| [r.rc, r.rd, r.rf]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
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

    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use pack64::*;
        let rows = &ctx.trace.pack64x2;
        let addrs = |r: &Xrow| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [r.fp + a, r.fp + b, r.fp + c]
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [ctx.g_at(a), ctx.g_at(b), ctx.g_at(c)]
        });
        ctx.cols(out, rows, AA, |r| addrs(r).map(|a| ctx.g_at(a)));
        ctx.cols(out, rows, VA, |r| {
            let a = addrs(r);
            [F64(ctx.mem[a[0] as usize].c0), F64(ctx.mem[a[1] as usize].c0)]
        });
        ctx.cols(out, rows, RA, |r| [r.ra, r.rb, r.rc]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
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
/// proven by flock's R1CS validity via `q_flock` (§blake3_flock).
///
/// A 128-bit chunk is two flock 64-bit words (lo, hi lanes), so the sixteen
/// memory-borne flock words are sixteen value LANE columns over eight cells,
/// plus the metadata immediate's two lanes. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL (not committed)
/// and routes their bus claims to `q_flock`, which already holds those words (see
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
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use blake3t::*;
        let rows = &ctx.trace.blake3;
        let ad = |r: &Brow| blake3_addresses(ctx.prog, r);
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        // OA0..OC and AA0..AC are the six base addresses' offsets and values, both
        // from the one instruction decode.
        ctx.cols(out, rows, OA0, |r| ad(r).map(|a| ctx.g_at(a - r.fp)));
        ctx.cols(out, rows, AA0, |r| ad(r).map(|a| ctx.g_at(a)));
        // The sixteen memory-borne flock words are the eight cells' lo/hi lanes:
        // the four message cells, then the cv pair and the output pair. A cell's
        // two lanes are one read, so each group of four takes two.
        let word_pair = |c0: u32, c1: u32| {
            let (w0, w1) = (ctx.mem[c0 as usize], ctx.mem[c1 as usize]);
            [F64(w0.c0), F64(w0.c1), F64(w1.c0), F64(w1.c1)]
        };
        ctx.cols(out, rows, VA0, |r| word_pair(ad(r)[0], ad(r)[1]));
        ctx.cols(out, rows, VB0, |r| word_pair(ad(r)[2], ad(r)[3]));
        ctx.cols(out, rows, VC0, |r| word_pair(ad(r)[5], ad(r)[5] + 1));
        ctx.cols(out, rows, VCV0, |r| word_pair(ad(r)[4], ad(r)[4] + 1));
        ctx.cols(out, rows, MD0, |r| {
            let md = blake3_metadata(ctx.prog, r.pc);
            [F64(md.c0), F64(md.c1)]
        });
        ctx.cols(out, rows, RA0, |r| {
            [r.ra[0], r.ra[1], r.rb[0], r.rb[1], r.rcv[0], r.rcv[1], r.rc[0], r.rc[1]]
        });
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}
