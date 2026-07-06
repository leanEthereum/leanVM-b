//! The public column schema and bus layout: the committed-column indices, and
//! the flush/count blocks the verifier reconstructs from the program + announced
//! sizes + public input (\S7, \S8). Plus the prover-side witness build.

use super::*;

// ---- column schema -----------------------------------------------------------

// Shared committed columns (indices `0..N_SHARED`). The program (opcode +
// operands) is PUBLIC, not committed: it rides the bytecode seed/finalize blocks
// as `Coord::Public`; only the witness-dependent finalize counts are committed.
pub(crate) const MEM: usize = 0; // the data-memory image
pub(crate) const MFCNT: usize = 1; // per-cell memory access count, g^{A[i]}
pub(crate) const BFCNT: usize = 2; // per-pc bytecode execution count, g^{A[pc]}
// flock's packed BLAKE3 witness `q_pkd`, committed in the SAME stack as every
// other column (single PCS). Size `2^(K_LOG+n_log-7)` when the program runs ≥1
// BLAKE3, else a size-1 dummy (kept in the static schema). It is the SOLE copy of
// the input/output words: the VM's BLAKE3 value columns are virtual and their
// memory-bus claims route to `q_pkd` slots (§blake3_flock), so nothing duplicates
// them. flock's R1CS validity is discharged by a basefold over this commitment.
pub(crate) const QPKD: usize = 3;
pub(crate) const N_SHARED: usize = 4;

/// Global column indexing: the shared columns occupy `0..N_SHARED`, then each
/// table `t` (in [`tables::tables`] order) owns the contiguous block `[base[t],
/// base[t] + n_committed_columns_t)`. Both prover and verifier derive this identically
/// from the table set, so every column claim lines up.
pub(crate) struct Schema {
    pub(crate) base: [usize; tables::N_TABLES],
    pub(crate) n: usize,
}

/// The schema is a pure function of the fixed table set, so compute it once.
pub(crate) fn schema() -> &'static Schema {
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
            Coord::GCol(i) => Coord::GCol(base + i),
            other => other,
        })
        .collect()
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
    /// Public input: the first two memory cells `m[0], m[1]` (256 bits), bound to
    /// the committed memory at verification (§8).
    pub pi: [F128; 2],
    pub taus: [usize; tables::N_TABLES], // (arith, set, deref, jump, blake3) log row counts
    /// Real (non-padded) per-table row counts, as announced. `row_counts[0]` is the
    /// merged XOR+MUL arithmetic count; `row_counts[BLAKE3_TABLE]` is the executed
    /// `BLAKE3` count, which gates the flock sub-proof.
    pub row_counts: [usize; tables::N_TABLES],
}

/// The prover's witness bundle: the committed column values + their stacked
/// multilinear `q` + the public [`Layout`] (plus the sizes needed to announce it).
pub(crate) struct Witness {
    pub(crate) cols: Vec<Column>,
    pub(crate) q: Vec<F128>,
    pub(crate) layout: Layout,
    pub(crate) log_mem: usize,
    pub(crate) row_counts: [usize; tables::N_TABLES],
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
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; tables::N_TABLES], n_blake3: usize) -> Vec<Option<usize>> {
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
/// five tables' real row counts `row_counts`, and the public input `pi`. The flush
/// blocks reference columns only by INDEX and the program only through its
/// public columns, so this needs no committed witness — both prover and verifier
/// reconstruct exactly the same structure (§7, §8).
pub(crate) fn layout(prog: &[Op], log_mem: usize, row_counts: [usize; tables::N_TABLES], pi: [F128; 2]) -> Layout {
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
        // Columns padded with g^0 = 1 (but raising no count block): the merged
        // arithmetic table's OP column, so its padding rows read as no-op XORs.
        for &c in table.unit_padded_columns() {
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
        pi,
        taus,
        row_counts,
    }
}

impl Program {
    pub(crate) fn build(&self, exec: &Execution) -> Witness {
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
            tr.xor.len() + tr.mul.len(), // arith: XOR and MUL share one merged table
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
