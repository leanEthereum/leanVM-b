//! The public column schema and bus layout: the committed-column indices, and
//! the flush/count blocks the verifier reconstructs from the program + announced
//! sizes + public input (§7, §8). Plus the prover-side witness build.

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
// flock's packed SHA256 witness `q_pkd`, committed in the SAME stack as every
// other column (single PCS). Size `2^(K_LOG+n_log-6)` F64 words, always ≥ 1
// instance (a no-SHA256 program commits one full padding instance). It is the
// SOLE copy of the input/output words: the VM's SHA256 value columns are
// virtual and their memory-bus claims route to `q_pkd` slots (§sha256_flock), so
// nothing duplicates them. flock's R1CS validity is discharged by the single
// stacked Ligerito-K opening over this commitment.
pub const QPKD: usize = 5;
pub const N_SHARED: usize = 6;

/// Global column indexing: the shared columns occupy `0..N_SHARED`, then each
/// table `t` (in [`tables::tables`] order) owns the contiguous block `[base[t],
/// base[t] + n_committed_columns_t)`. Both prover and verifier derive this identically
/// from the table set, so every column claim lines up.
pub struct Schema {
    pub base: [usize; 6],
    pub n: usize,
}

/// The schema is a pure function of the fixed table set, so compute it once.
pub fn schema() -> &'static Schema {
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
            Coord::GCol(i, k) => Coord::GCol(base + i, k),
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
    pub pad: Vec<F64>,
    /// Per-column placement (offset + n_vars) in the stacked witness; from the
    /// columns' log-sizes alone, so reconstructable by the verifier.
    pub placements: Vec<witness::Placement>,
    /// `log2` of the stacked witness length.
    pub m: usize,
    /// Public input: the first two memory cells `m[0], m[1]` (each a 192-bit
    /// word), bound to the committed memory at verification (§8).
    pub pi: [F192; 2],
    pub taus: [usize; 6], // (xor, mul, set, deref, jump, sha256) log row counts
    /// Real (non-padded) per-table row counts, as announced. `row_counts[5]` is
    /// the executed `SHA256` count, which gates the flock sub-proof.
    pub row_counts: [usize; 6],
}

/// The prover's witness bundle: the committed column values + their stacked
/// multilinear `q` + the public [`Layout`] (plus the sizes needed to announce it).
pub(crate) struct Witness {
    pub(crate) cols: Vec<Column>,
    pub(crate) q: Vec<F64>,
    pub(crate) layout: Layout,
    pub(crate) log_mem: usize,
    pub(crate) row_counts: [usize; 6],
}

/// The committed columns' kappa SOURCES, for the recursion guest's
/// in-circuit certification of the stacked size m = max(log2_ceil(sum of
/// 2^kappa), MIN_MU). Per committed column: `Some((source, adj))` with
/// kappa = value(source) + adj, where source 0 is the constant 0 (kappa =
/// adj; used for the fixed-size columns and the program bytecode length,
/// which the caller passes as `log_bytecode`), source 1 is log_mem, and
/// source 2 + t is tau_t. `None` = virtual (never committed). Mirrors
/// [`col_kappas`] exactly; keep the two in lockstep.
pub fn col_kappa_sources(log_bytecode: usize) -> Vec<Option<(usize, usize)>> {
    let sch = schema();
    let mut k = vec![Some((0usize, 0usize)); sch.n];
    k[MEM_LO] = Some((1, 0));
    k[MEM_HI] = Some((1, 0));
    k[MEM_TOP] = Some((1, 0));
    k[MFCNT] = Some((1, 0));
    k[BFCNT] = Some((0, log_bytecode));
    // qpkd_kappa(n) = K_LOG + n_blocks_log - LOG_PACKING, and tau_5 IS
    // n_blocks_log (the announced-size certification uses the same floor).
    k[QPKD] = Some((2 + tables::SHA256_TABLE, flock::sha256::K_LOG - ::pcs::LOG_PACKING));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some((2 + t, 0)));
    }
    let b3 = sch.base[tables::SHA256_TABLE];
    for &c in &tables::SHA256_VALUE_COLS {
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

/// Column → log-size (`kappa`) map: the shared MEM/MFCNT columns are `2^log_mem`,
/// the bytecode finalize count is `2^log_bytecode`, and every column of table `t`
/// is `2^taus[t]` (its padded log-row-count). `None` marks a **virtual**
/// (uncommitted) column. Depends only on the public sizes, so the verifier can
/// reconstruct the placements.
///
/// The SHA256 value columns (`va0..vc3`) are always virtual: `q_pkd`
/// already holds those words at fixed packed slots, so committing them again is
/// redundant. Their memory-bus claims route directly to `q_pkd` slot evaluations
/// (see [`slot_claims`]), which both binds them to
/// the proven witness AND eliminates the separate value-binding sub-protocol.
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; 6], n_sha256: usize) -> Vec<Option<usize>> {
    let sch = schema();
    let mut k = vec![Some(0usize); sch.n];
    k[MEM_LO] = Some(log_mem);
    k[MEM_HI] = Some(log_mem);
    k[MEM_TOP] = Some(log_mem);
    k[MFCNT] = Some(log_mem);
    k[BFCNT] = Some(log_bytecode);
    // q_pkd: `2^(K_LOG+n_log-6)` F64 words, always ≥ 1 instance (`qpkd_kappa`
    // floors `n_sha256` at 1 — padding instance for a no-SHA256 program).
    k[QPKD] = Some(crate::sha256_flock::qpkd_kappa(n_sha256));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some(taus[t]));
    }
    // SHA256 value columns are ALWAYS virtual (read from q_pkd, never committed).
    let b3 = sch.base[tables::SHA256_TABLE];
    for &c in &tables::SHA256_VALUE_COLS {
        k[b3 + c] = None;
    }
    k
}

/// Build the public [`Layout`] from the program, the memory log-size `log_mem`, the
/// six tables' real row counts `row_counts`, and the public input `pi`. The flush
/// blocks reference columns only by INDEX and the program only through its
/// public columns, so this needs no committed witness — both prover and verifier
/// reconstruct exactly the same structure (§7, §8).
pub fn layout(prog: &[Op], log_mem: usize, row_counts: [usize; 6], pi: [F192; 2]) -> Layout {
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
    // The SHA256 table is ALWAYS sized to flock's `2^n_log` instance count
    // (`max(count,1)`, lincheck floor ≥ 8) so its per-instance (virtual) value
    // columns share `q_pkd`'s instance cube — a value-column bus claim at instance
    // point `r` maps to a strided `q_pkd` slot claim at `r` (`slot_claims`).
    taus[tables::SHA256_TABLE] = crate::sha256_flock::n_blocks_log(row_counts[tables::SHA256_TABLE].max(1));

    // Derived boundary: the run starts at (pc,fp) = (0,0) and, by convention, the
    // final pc is the bytecode's last cell g^{B-1} (the compiler emits a halt jump
    // there), with fp returned to 0. All public, no trace needed.
    let pc0 = 0u32;
    let fp0 = 0u32;
    let final_pc = (bytecode_size - 1) as u32;
    let final_fp = 0u32;

    let one = F64::ONE;
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
            Op::Sha256 { ins, out, .. } => ins[0].max(ins[1]).max(ins[2]).max(ins[3]).max(out),
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
        Op::Sha256 {
            packing: crate::cpu::Sha256Packing::Bytes128,
            ..
        } => OP_SHA256,
        Op::Sha256 {
            packing: crate::cpu::Sha256Packing::Transcript192,
            ..
        } => tables::OP_SHA256_TRANSCRIPT,
    };
    let operands = |op: &Op| -> (F64, F64, F64) {
        match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (g_at(a), g_at(b), g_at(c)),
            // The immediate's first two K-limbs ride operand slots o2/o3; c2
            // rides the fpc slot below.
            Op::Set { o, k } => (g_at(o), F64(k.c0), F64(k.c1)),
            Op::Deref { alpha, beta, gamma, .. } => (g_at(alpha), g_at(beta), g_at(gamma)),
            Op::Jump { oc, od, of } => (g_at(oc), g_at(od), g_at(of)),
            // SHA256's first three input-word offsets; the last two ride the
            // fpc/ffp bytecode slots below.
            Op::Sha256 { ins, .. } => (g_at(ins[0]), g_at(ins[1]), g_at(ins[2])),
        }
    };
    // The 4th/5th bytecode operand slots: the two DEREF store-mode flags, or
    // SHA256's remaining input word / output base (0 elsewhere).
    let fpc = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_pc(),
        Op::Sha256 { ins, .. } => g_at(ins[3]),
        Op::Set { k, .. } => F64(k.c2),
        _ => F64::ZERO,
    };
    let ffp = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_fp(),
        Op::Sha256 { out, .. } => g_at(*out),
        _ => F64::ZERO,
    };
    // The program is PUBLIC (not committed): six public columns over the
    // program cube, embedded in the bytecode seed/finalize blocks below.
    let prog_op: Vec<F64> = prog.par_iter().map(opcode).collect();
    let prog_o1: Vec<F64> = prog.par_iter().map(|o| operands(o).0).collect();
    let prog_o2: Vec<F64> = prog.par_iter().map(|o| operands(o).1).collect();
    let prog_o3: Vec<F64> = prog.par_iter().map(|o| operands(o).2).collect();
    let prog_fpc: Vec<F64> = prog.par_iter().map(fpc).collect();
    let prog_ffp: Vec<F64> = prog.par_iter().map(ffp).collect();

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
    // SHA256 padding rows must match flock's padding instance (the all-zero-input
    // compression): zero inputs but a NONZERO output `out_lo`. So the four output
    // value columns pad with that digest, not 0 — the memory bus flushes these
    // (virtual) columns, and their padding rows must equal `q_pkd`'s padding slots
    // so the default-padding surplus divides out and the routed claims agree.
    // Inputs/counts keep their 0/1 defaults. Always applied (the SHA256 table is
    // always present, all-padding for a no-SHA256 program).
    {
        let b3 = sch.base[tables::SHA256_TABLE];
        let pc = crate::sha256_flock::padding_digest();
        for k in 0..4 {
            pad[b3 + tables::SHA256_VALUE_COLS[8 + k]] = pc[k]; // c0..c3
        }
        use tables::sha256t::{MO0, OP};
        pad[b3 + MO0] = pc[0];
        pad[b3 + MO0 + 1] = pc[1];
        pad[b3 + MO0 + 3] = pc[2];
        pad[b3 + MO0 + 4] = pc[3];
        pad[b3 + OP] = tables::OP_SHA256;
    }

    let (placements, m) = witness::placements_of(&col_kappas(
        log_mem,
        log_bytecode,
        taus,
        row_counts[tables::SHA256_TABLE],
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
        let gpow = primitives::field::g_powers(span);

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
        // Shared columns. The 192-bit memory image splits into three K-limbs.
        cols[MEM_LO] = exec.mem.par_iter().map(|w| F64(w.c0)).collect();
        cols[MEM_HI] = exec.mem.par_iter().map(|w| F64(w.c1)).collect();
        cols[MEM_TOP] = exec.mem.par_iter().map(|w| F64(w.c2)).collect();
        cols[MFCNT] = tr.mem_count.clone(); // running counts ended at g^{A[i]}
        cols[BFCNT] = tr.bytecode_count.clone(); // running counts ended at g^{A[pc]}
        // flock's packed SHA256 witness q_pkd, ALWAYS committed in this same stack:
        // built from the executed SHA256 rows in order (row j = flock instance j),
        // padded to `2^n_blocks_log(max(count,1))` all-padding instances — so a
        // program with no SHA256 still carries a single padding instance.
        let fill_ms = t_fill.elapsed().as_secs_f64() * 1e3;
        let t_qpkd = std::time::Instant::now();
        cols[QPKD] = {
            let blocks: Vec<_> = tr
                .sha256
                .iter()
                .map(|r| crate::sha256_flock::compression(r.va, r.vb))
                .collect();
            crate::sha256_flock::build_qpkd(&blocks)
        };
        let qpkd_ms = t_qpkd.elapsed().as_secs_f64() * 1e3;

        if prof {
            eprintln!("[build] fill cols   : {fill_ms:>7.2} ms");
            eprintln!("[build] build q_pkd : {qpkd_ms:>7.2} ms");
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
            tr.sha256.len(),
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
        // SHA256, which `layout` rounds up to flock's `2^n_log`).
        for (t, table) in tables::tables().iter().enumerate() {
            let n = 1usize << l.taus[t];
            let base = sch.base[t];
            for (i, col) in cols[base..base + table.n_committed_columns()].iter_mut().enumerate() {
                col.resize(n, l.pad[base + i]);
            }
        }
        // (`execute` already asserts the run halts at the sentinel (pc, fp) =
        // (g^{B-1}, 0), exactly the boundary the public layout derives.)
        let t_stack = std::time::Instant::now();
        let q = witness::stack_q(&cols, &l.placements, l.m);
        if prof {
            eprintln!(
                "[build] stack_q     : {:>7.2} ms",
                t_stack.elapsed().as_secs_f64() * 1e3
            );
        }
        Witness {
            cols,
            q,
            layout: l,
            log_mem,
            row_counts,
        }
    }
}
