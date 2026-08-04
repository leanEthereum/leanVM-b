//! The public column schema and bus layout: the committed-column indices, and
//! the flush/count blocks the verifier reconstructs from the program + announced
//! sizes and public input. Plus the prover-side witness build.

use super::*;

// ---- column schema -----------------------------------------------------------

// Shared committed columns (indices `0..N_SHARED`). The program (opcode +
// operands) is PUBLIC, not committed: it rides the bytecode seed/finalize blocks
// as `Coord::Public`; only the witness-dependent finalize counts are committed.
// The data-memory image, a 192-bit word per cell committed as three K-lane columns.
pub const MEM_LO: usize = 0;
pub const MEM_HI: usize = 1;
pub const MEM_TOP: usize = 2;
pub const MFCNT: usize = 3; // per-cell memory access count, g^{A[i]}
pub const BFCNT: usize = 4; // per-pc bytecode execution count, g^{A[pc]}
// flock's packed BLAKE3 witness `q_pkd`, committed in the SAME stack as every
// other column (single PCS). Size `2^(K_LOG+n_log-6)` F64 words, always ≥ 1
// instance (a no-BLAKE3 program commits one full padding instance). It is the
// SOLE copy of the input/output words: the VM's BLAKE3 value columns are
// virtual and their memory-bus claims route to `q_pkd` slots (§blake3_flock), so
// nothing duplicates them. flock's R1CS validity is discharged by the single
// stacked WHIR opening over this commitment.
pub const QPKD: usize = 5;
pub const N_SHARED: usize = 6;

/// Global column indexing: the shared columns occupy `0..N_SHARED`, then each
/// table `t` (in [`tables::tables`] order) owns the contiguous block `[base[t],
/// base[t] + n_committed_columns_t)`. Both prover and verifier derive this identically
/// from the table set, so every column claim lines up.
pub struct Schema {
    pub base: [usize; tables::N_TABLES],
    pub n: usize,
}

/// The schema is a pure function of the fixed table set, so compute it once.
pub fn schema() -> &'static Schema {
    static SCHEMA: std::sync::OnceLock<Schema> = std::sync::OnceLock::new();
    SCHEMA.get_or_init(|| {
        let mut base = [0usize; tables::N_TABLES];
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
            Coord::GCol(i, k) => Coord::GCol(base + i, k),
            other => other,
        })
        .collect()
}

/// The public proof structure: everything the verifier reconstructs from the
/// program, the announced sizes, and the public input, with no witness values. The
/// flush blocks reference columns by INDEX (see [`crate::leaf::Coord`]), so they
/// are pure public structure.
pub struct Layout {
    pub push: Vec<Block>,
    pub pull: Vec<Block>,
    /// Count channel: read-count columns whose product must be nonzero (§sec:memchan).
    pub count: Vec<Block>,
    /// Per-column padding value (count columns pad with 1, else 0), so the verifier
    /// can form the default-padding surplus it divides out of the bus (§sec:gp).
    pub pad: Vec<F64>,
    /// Per-column placement (offset + n_vars) in the stacked witness; from the
    /// columns' log-sizes alone, so reconstructable by the verifier.
    pub placements: Vec<witness::Placement>,
    /// `log2` of the stacked witness length.
    pub m: usize,
    /// Public input: the first two memory cells `m[0], m[1]` (each a 192-bit
    /// word), bound to the committed memory at verification (§8).
    pub pi: [F192; 2],
    pub taus: [usize; tables::N_TABLES],
    /// Real (non-padded) per-table row counts, as announced. `row_counts[5]` is
    /// the executed `BLAKE3` count, which gates the flock sub-proof.
    pub row_counts: [usize; tables::N_TABLES],
}

/// The prover's witness bundle: the committed column values + their stacked
/// multilinear `q` + the public [`Layout`] (plus the sizes needed to announce it).
pub(crate) struct Witness {
    pub(crate) cols: Vec<Column>,
    pub(crate) q: Vec<F64>,
    pub(crate) layout: Layout,
    pub(crate) log_mem: usize,
    /// `Option` lets `prove` take and free the large reduction-only buffers
    /// immediately after reduction, before the mixed PCS opening.
    pub(crate) flock_reduction: Option<crate::blake3_flock::PreparedReductionWitness>,
}

/// The committed columns' kappa SOURCES, for the recursion guest's
/// in-circuit certification of the stacked size m = max(log2_ceil(sum of
/// 2^kappa), MIN_MU). Per committed column: `Some((source, adj))` with
/// kappa = value(source) + adj, where source 0 is the constant 0 (kappa =
/// adj; used for the fixed-size columns and the program bytecode length,
/// which the caller passes as `log_bytecode`), source 1 is log_mem, and
/// source 2 + t is tau_t. `None` = virtual (never committed). `col_kappas`
/// is derived from this, so the two cannot drift apart.
pub fn col_kappa_sources(log_bytecode: usize) -> Vec<Option<(usize, usize)>> {
    let sch = schema();
    let mut k = vec![Some((0usize, 0usize)); sch.n];
    k[MEM_LO] = Some((1, 0));
    k[MEM_HI] = Some((1, 0));
    k[MEM_TOP] = Some((1, 0));
    k[MFCNT] = Some((1, 0));
    k[BFCNT] = Some((0, log_bytecode));
    // q_pkd is `2^(K_LOG + n_blocks_log - LOG_PACKING)` F64 words, always ≥ 1
    // instance (a no-BLAKE3 program commits one padding instance), and tau_5 IS
    // n_blocks_log (the announced-size certification uses the same floor), so this
    // reproduces `qpkd_kappa`.
    k[QPKD] = Some((2 + tables::BLAKE3_TABLE, flock::blake3::K_LOG - ::pcs::LOG_PACKING));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some((2 + t, 0)));
    }
    // The BLAKE3 value columns are ALWAYS virtual: `q_pkd` already holds those
    // words at fixed packed slots, so committing them again is redundant. Their
    // memory-bus claims route directly to `q_pkd` slot evaluations (`slot_claims`),
    // which both binds them to the proven witness AND removes the separate
    // value-binding sub-protocol.
    let b3 = sch.base[tables::BLAKE3_TABLE];
    for &c in &tables::BLAKE3_VALUE_COLS {
        k[b3 + c] = None;
    }
    k
}

/// The bus flush blocks' kappa SOURCES, flattened in side order (push, pull,
/// count) exactly as the blocks are constructed below: per block
/// `(source, adj)` with kappa = value(source) + adj, source 0 = the constant
/// 0, 1 = log_mem, 2 + t = tau_t. For the recursion guest's in-circuit pin
/// of every hinted block kappa. Keep in lockstep with the block
/// construction in [`layout`].
pub fn block_kappa_sources(log_bytecode: usize) -> Vec<(usize, usize)> {
    let mut push = vec![(0, 0), (1, 0), (0, log_bytecode)];
    let mut pull = vec![(0, 0), (1, 0), (0, log_bytecode)];
    let mut count = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let mut fb = tables::FlushBuilder::new();
        table.flushes(&mut fb);
        push.extend(std::iter::repeat_n((2 + t, 0), fb.push.len()));
        pull.extend(std::iter::repeat_n((2 + t, 0), fb.pull.len()));
        count.extend(std::iter::repeat_n((2 + t, 0), table.count_columns().len()));
    }
    push.extend(pull);
    push.extend(count);
    push
}

/// Column → log-size (`kappa`) map, derived from [`col_kappa_sources`] by
/// substituting the announced sizes: source 0 is the constant 0, source 1 is
/// `log_mem`, source `2 + t` is `tau_t`. `None` marks a **virtual**
/// (uncommitted) column. Depends only on the public sizes, so the verifier can
/// reconstruct the placements.
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; tables::N_TABLES]) -> Vec<Option<usize>> {
    let mut values = vec![0usize, log_mem];
    values.extend(taus);
    col_kappa_sources(log_bytecode)
        .iter()
        .map(|s| s.map(|(source, adj)| values[source] + adj))
        .collect()
}

/// Build the public [`Layout`] from the program, the memory log-size `log_mem`, the
/// instruction tables' real row counts `row_counts`, and the public input `pi`. The flush
/// blocks reference columns only by INDEX and the program only through its
/// public columns, so this needs no committed witness: both prover and verifier
/// reconstruct exactly the same structure.
pub fn layout(prog: &[Op], log_mem: usize, row_counts: [usize; tables::N_TABLES], pi: [F192; 2]) -> Layout {
    let bytecode_size = prog.len();
    let log_bytecode = crate::log2_strict_usize(bytecode_size);
    let cells = 1usize << log_mem;

    // Per-table padded log-row-counts (the boundary block is fixed). The real
    // (non-padded) `row_counts[t]` tell each flush how many of its 2^kappa rows
    // are padding (default rows divided out of the bus, §sec:gp).
    let mut taus = [0usize; tables::N_TABLES];
    for (i, &r) in row_counts.iter().enumerate() {
        taus[i] = crate::log2_ceil_usize(r.max(1));
    }
    // The BLAKE3 table is ALWAYS sized to flock's `2^n_log` instance count
    // (`max(count,1)`, lincheck floor ≥ 8) so its per-instance (virtual) value
    // columns share `q_pkd`'s instance cube: a value-column bus claim at instance
    // point `r` maps to a strided `q_pkd` slot claim at `r` (`slot_claims`).
    taus[tables::BLAKE3_TABLE] = crate::blake3_flock::n_blocks_log(row_counts[tables::BLAKE3_TABLE].max(1));

    // Derived boundary: the run starts at (pc,fp) = (0,0) and, by convention, the
    // final pc is the bytecode's last cell g^{B-1} (the compiler emits a halt jump
    // there), with fp returned to 0. All public, no trace needed.
    let pc0 = 0u32;
    let fp0 = 0u32;
    let final_pc = (bytecode_size - 1) as u32;
    let final_fp = 0u32;

    let one = F64::ONE;
    // The public program columns map operand *offsets* (small, ≤ frame size) to
    // g-powers (not memory addresses), so precompute only up to the largest
    // operand, an O(1) lookup each, rather than over the whole 2^log_mem memory.
    let max_op = prog
        .iter()
        .map(|op| match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => a.max(b).max(c),
            Op::Set { o, .. } => o,
            Op::Deref { alpha, beta, gamma, .. } => alpha.max(beta).max(gamma),
            Op::Jump { oc, od, of } => oc.max(od).max(of),
            Op::Pack64x2 { a, b, c } => a.max(b).max(c),
            Op::Blake3 { ins, cv, out, .. } => ins[0].max(ins[1]).max(ins[2]).max(ins[3]).max(cv).max(out),
        })
        .max()
        .unwrap_or(0) as usize;
    let gpow = primitives::field::g_powers((max_op + 1).max(2));
    let g_at = |i: u32| gpow[i as usize]; // operand g-power

    let opcode = |op: &Op| match op {
        Op::Xor { .. } => OP_XOR,
        Op::Mul { .. } => OP_MUL,
        Op::Set { .. } => OP_SET,
        Op::Deref { .. } => OP_DEREF,
        Op::Jump { .. } => OP_JUMP,
        Op::Pack64x2 { .. } => tables::OP_PACK64X2,
        Op::Blake3 { .. } => OP_BLAKE3,
    };
    let operands = |op: &Op| -> (F64, F64, F64) {
        match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (g_at(a), g_at(b), g_at(c)),
            // The immediate's first two K-limbs ride operand slots o2/o3; c2
            // rides the fpc slot below.
            Op::Set { o, k } => (g_at(o), F64(k.c0), F64(k.c1)),
            Op::Deref { alpha, beta, gamma, .. } => (g_at(alpha), g_at(beta), g_at(gamma)),
            Op::Jump { oc, od, of } => (g_at(oc), g_at(od), g_at(of)),
            Op::Pack64x2 { a, b, c } => (g_at(a), g_at(b), g_at(c)),
            // BLAKE3's first three input-word offsets; the last two ride the
            // fpc/ffp bytecode slots below.
            Op::Blake3 { ins, .. } => (g_at(ins[0]), g_at(ins[1]), g_at(ins[2])),
        }
    };
    // The 4th/5th bytecode operand slots: the two DEREF store-mode flags, or
    // BLAKE3's remaining input word / chaining-value base (0 elsewhere).
    let fpc = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_pc(),
        Op::Blake3 { ins, .. } => g_at(ins[3]),
        Op::Set { k, .. } => F64(k.c2),
        _ => F64::ZERO,
    };
    let ffp = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_fp(),
        Op::Blake3 { cv, .. } => g_at(*cv),
        _ => F64::ZERO,
    };
    // The 6th/7th/8th bytecode operand slots: BLAKE3's output base and the two
    // K-lanes of its metadata immediate (0 elsewhere).
    let extra0 = |op: &Op| match op {
        Op::Blake3 { out, .. } => g_at(*out),
        _ => F64::ZERO,
    };
    let extra1 = |op: &Op| match op {
        Op::Blake3 { metadata, .. } => F64(metadata.c0),
        _ => F64::ZERO,
    };
    let extra2 = |op: &Op| match op {
        Op::Blake3 { metadata, .. } => F64(metadata.c1),
        _ => F64::ZERO,
    };
    // The program is PUBLIC (not committed): nine public columns over the
    // program cube, embedded in the bytecode seed/finalize blocks below.
    let column = |f: &(dyn Fn(&Op) -> F64 + Sync)| parallel::map_collect(prog.len(), |i| f(&prog[i]));
    let prog_op: Vec<F64> = column(&opcode);
    let prog_o1: Vec<F64> = column(&|o| operands(o).0);
    let prog_o2: Vec<F64> = column(&|o| operands(o).1);
    let prog_o3: Vec<F64> = column(&|o| operands(o).2);
    let prog_fpc: Vec<F64> = column(&fpc);
    let prog_ffp: Vec<F64> = column(&ffp);
    let prog_extra0: Vec<F64> = column(&extra0);
    let prog_extra1: Vec<F64> = column(&extra1);
    let prog_extra2: Vec<F64> = column(&extra2);

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
    // memory seed + finalize (every address real, no padding). The value is the
    // full three-limb 192-bit word.
    push.push(blk(
        log_mem,
        cells,
        vec![
            Const(SEP_MEM),
            Index,
            Const(one),
            Col(MEM_LO),
            Col(MEM_HI),
            Col(MEM_TOP),
        ],
    ));
    pull.push(blk(
        log_mem,
        cells,
        vec![
            Const(SEP_MEM),
            Index,
            Col(MFCNT),
            Col(MEM_LO),
            Col(MEM_HI),
            Col(MEM_TOP),
        ],
    ));
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
            Public(prog_extra0.clone()),
            Public(prog_extra1.clone()),
            Public(prog_extra2.clone()),
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
            Public(prog_extra0),
            Public(prog_extra1),
            Public(prog_extra2),
        ],
    ));

    // Per-table blocks: each table declares its flushes and read-count columns in
    // local indices; offset them to the table's global columns. The count columns
    // also fix the per-column padding to `1` (so they never zero the bus product).
    let sch = schema();
    let mut count_blocks: Vec<Block> = Vec::new();
    let mut pad = vec![F64::ZERO; sch.n];
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
            pad[base + c] = F64::ONE;
        }
    }
    // BLAKE3 padding rows must match flock's padding instance (the all-zero-input
    // compression): zero inputs but a NONZERO output `out_lo`. So the four output
    // value columns pad with that digest, not 0: the memory bus flushes these
    // (virtual) columns, and their padding rows must equal `q_pkd`'s padding slots
    // so the default-padding surplus divides out and the routed claims agree.
    // Inputs/counts keep their 0/1 defaults. Always applied (the BLAKE3 table is
    // always present, all-padding for a no-BLAKE3 program).
    {
        let b3 = sch.base[tables::BLAKE3_TABLE];
        let pc = crate::blake3_flock::padding_digest();
        let md = crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS);
        for k in 0..4 {
            pad[b3 + tables::BLAKE3_VALUE_COLS[8 + k]] = pc[k]; // c0..c3
            pad[b3 + tables::BLAKE3_VALUE_COLS[12 + k]] = crate::blake3_flock::IV[k]; // cv0..cv3
        }
        pad[b3 + tables::BLAKE3_VALUE_COLS[16]] = F64(md.c0); // metadata counter lane
        pad[b3 + tables::BLAKE3_VALUE_COLS[17]] = F64(md.c1); // metadata blen‖flags lane
    }

    let (placements, m) = witness::placements_of(&col_kappas(log_mem, log_bytecode, taus));
    Layout {
        push,
        pull,
        count: count_blocks,
        pad,
        placements,
        m,
        pi,
        taus,
        row_counts,
    }
}

impl Program {
    pub(crate) fn build(&self, exec: &Execution) -> Witness {
        assert!(self.prog.len().is_power_of_two());
        assert!(exec.mem.len().is_power_of_two());
        // The trace was emitted in the same walk as the memory image (no re-walk).
        let tr = &exec.trace;
        let cells = exec.mem.len();
        let bytecode_size = self.prog.len();
        let log_mem = crate::log2_strict_usize(cells);

        let sch = schema();
        let mut cols = vec![Column::new(); sch.n];
        // Precompute g^0..g^{span-1} once so every address/pc/operand fill is an
        // O(1) lookup instead of an O(log) power.
        let span = cells.max(bytecode_size);
        let gpow = primitives::field::g_powers(span);

        // Each table fills its own columns from the trace (local indices, offset
        // into its global block).
        let ctx = FillCtx {
            trace: tr,
            mem: &exec.mem,
            gpow: &gpow,
        };
        crate::stage!("Fill columns", || {
            for (t, table) in tables::tables().iter().enumerate() {
                let (base, n) = (sch.base[t], table.n_committed_columns());
                table.fill(&ctx, &mut cols[base..base + n]);
            }
            // Shared columns. The 192-bit memory image splits into three K-limbs.
            cols[MEM_LO] = parallel::map_collect(exec.mem.len(), |i| F64(exec.mem[i].c0));
            cols[MEM_HI] = parallel::map_collect(exec.mem.len(), |i| F64(exec.mem[i].c1));
            cols[MEM_TOP] = parallel::map_collect(exec.mem.len(), |i| F64(exec.mem[i].c2));
            cols[MFCNT] = tr.mem_count.clone(); // running counts ended at g^{A[i]}
            cols[BFCNT] = tr.bytecode_count.clone(); // running counts ended at g^{A[pc]}
        });
        // flock's packed BLAKE3 witness q_pkd, ALWAYS committed in this same stack:
        // built from the executed BLAKE3 rows in order (row j = flock instance j),
        // padded to `2^n_blocks_log(max(count,1))` all-padding instances, so a
        // program with no BLAKE3 still carries a single padding instance.
        let (q_pkd, flock_reduction) = crate::stage!("Build q_pkd", || {
            let blocks: Vec<_> = tr
                .blake3
                .iter()
                .map(|r| crate::blake3_flock::compression(r.va, r.vb, r.vcv, r.metadata))
                .collect();
            crate::blake3_flock::build_qpkd_prepared(&blocks)
        });
        cols[QPKD] = q_pkd;

        // The public layout (flush/count blocks, per-column padding, placements,
        // boundary, taus) is a pure function of the program + announced sizes +
        // public input, with no committed witness; reconstruct it here so the
        // prover and verifier share exactly the same structure.
        let row_counts = [
            tr.xor.len(),
            tr.mul.len(),
            tr.set.len(),
            tr.deref.len(),
            tr.jump.len(),
            tr.blake3.len(),
            tr.pack64x2.len(),
        ];
        assert!(
            row_counts.iter().all(|&r| r <= 1 << MAX_LOG_ROWS),
            "a table exceeds 2^{MAX_LOG_ROWS} rows"
        );
        let pi = [exec.mem[0], exec.mem[1]];
        let l = layout(&self.prog, log_mem, row_counts, pi);

        // Pad each per-opcode table to its power-of-two row count: count columns
        // with g^0 = 1, every other column with 0 (§4.4, §e2e-pad). A default padding
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
        let q = crate::stage!("Stack witness", || { witness::stack_q(&cols, &l.placements, l.m) });
        Witness {
            cols,
            q,
            layout: l,
            log_mem,
            flock_reduction: Some(flock_reduction),
        }
    }
}
