//! The public column schema and bus layout: the committed-column indices, and
//! the flush/count blocks the verifier reconstructs from the program + announced
//! sizes + public input (§7, §8). Plus the prover-side witness build.

use super::*;

// ---- column schema -----------------------------------------------------------

// Shared committed columns (indices `0..N_SHARED`). The program (opcode +
// operands) is PUBLIC, not committed: it rides the bytecode seed/finalize blocks
// as `Coord::Public`; only the witness-dependent finalize counts are committed.
pub const MEM: usize = 0; // the data-memory image
pub const MFCNT: usize = 1; // per-cell memory access count, g^{A[i]}
pub const BFCNT: usize = 2; // per-pc bytecode execution count, g^{A[pc]}
// flock's packed BLAKE3 witness `q_pkd`, committed in the SAME stack as every
// other column (single PCS). Size `2^(K_LOG+n_log-7)`, always ≥ 1 instance (a
// no-BLAKE3 program commits one full padding instance). It is the SOLE copy of
// the input/output words: the VM's BLAKE3 value columns are virtual and their
// memory-bus claims route to `q_pkd` slots (§blake3_flock), so nothing duplicates
// them. flock's R1CS validity is discharged by the single stacked Ligerito
// opening over this commitment.
pub const QPKD: usize = 3;
pub const N_SHARED: usize = 4;

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
    /// Power-of-two equal-height column blocks used by the row-major Jagged
    /// commitment layout. Virtual columns are absent; q_pkd is a singleton.
    pub jagged_blocks: Vec<Vec<usize>>,
    /// `log2` of the stacked witness length.
    pub m: usize,
    /// Public input: the first two memory cells `m[0], m[1]` (256 bits), bound to
    /// the committed memory at verification (§8).
    pub pi: [F128; 2],
    pub taus: [usize; 6], // (xor, mul, set, deref, jump, blake3) log row counts
    /// Real (non-padded) per-table row counts, as announced. `row_counts[5]` is
    /// the executed `BLAKE3` count, which gates the flock sub-proof.
    pub row_counts: [usize; 6],
}

/// Shape-independent Jagged block partition. Columns share a block only when
/// they have the same public height source and identical membership in every
/// bus/constraint/PI opening row-group. Schema adjacency is irrelevant: the
/// explicit placement map can globally cluster compatible columns. Consequently
/// every point group claims either a whole block or none of it.
fn jagged_column_blocks(log_bytecode: usize, sides: [&[Block]; 3]) -> Vec<Vec<usize>> {
    let sources = col_height_sources(log_bytecode);
    let mut signatures: Vec<Vec<usize>> = vec![Vec::new(); sources.len()];
    let kappa_sources = block_kappa_sources(log_bytecode);
    let mut block_index = 0usize;
    let mut group_of_source = std::collections::BTreeMap::new();
    for blocks in sides {
        for block in blocks {
            let source = kappa_sources[block_index];
            block_index += 1;
            let next = group_of_source.len();
            let group = *group_of_source.entry(source).or_insert(next);
            for coord in &block.coords {
                if let Coord::Col(col) | Coord::GCol(col) = coord
                    && sources[*col].is_some()
                {
                    signatures[*col].push(group);
                }
            }
        }
    }
    assert_eq!(block_index, kappa_sources.len());

    let mut next_group = group_of_source.len();
    let sch = schema();
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        for &col in table.constraint_columns() {
            if sources[base + col].is_some() {
                signatures[base + col].push(next_group);
            }
        }
        next_group += 1;
    }
    signatures[MEM].push(next_group); // public-input claim
    for signature in &mut signatures {
        signature.sort_unstable();
        signature.dedup();
    }

    let mut blocks = vec![vec![QPKD]];
    let committed: Vec<usize> = (0..sources.len()).filter(|&col| col != QPKD && sources[col].is_some()).collect();
    let mut consumed = vec![false; sources.len()];
    for &first in &committed {
        if consumed[first] {
            continue;
        }
        let group: Vec<usize> = committed
            .iter()
            .copied()
            .filter(|&col| !consumed[col] && sources[col] == sources[first] && signatures[col] == signatures[first])
            .collect();
        for &col in &group {
            consumed[col] = true;
        }
        let mut start = 0usize;
        let mut remaining = group.len();
        while remaining != 0 {
            let width = 1usize << (usize::BITS - 1 - remaining.leading_zeros());
            blocks.push(group[start..start + width].to_vec());
            start += width;
            remaining -= width;
        }
    }
    blocks
}

/// The prover's witness bundle: the committed column values + their stacked
/// multilinear `q` + the public [`Layout`] (plus the sizes needed to announce it).
pub(crate) struct Witness {
    pub(crate) cols: Vec<Column>,
    pub(crate) q: Vec<F128>,
    pub(crate) layout: Layout,
    pub(crate) log_mem: usize,
    pub(crate) row_counts: [usize; 6],
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
/// source 2 + t is tau_t. `None` = virtual (never committed). Mirrors
/// [`col_kappas`] exactly; keep the two in lockstep.
pub fn col_kappa_sources(log_bytecode: usize) -> Vec<Option<(usize, usize)>> {
    let sch = schema();
    let mut k = vec![Some((0usize, 0usize)); sch.n];
    k[MEM] = Some((1, 0));
    k[MFCNT] = Some((1, 0));
    k[BFCNT] = Some((0, log_bytecode));
    // qpkd_kappa(n) = K_LOG + n_blocks_log - LOG_PACKING, and tau_5 IS
    // n_blocks_log (the announced-size certification uses the same floor).
    k[QPKD] = Some((
        2 + tables::BLAKE3_TABLE,
        flock::blake3::K_LOG - ::pcs::LOG_PACKING,
    ));
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        k[base..base + table.n_committed_columns()].fill(Some((2 + t, 0)));
    }
    let b3 = sch.base[tables::BLAKE3_TABLE];
    for &c in &tables::BLAKE3_VALUE_COLS {
        k[b3 + c] = None;
    }
    k
}

/// Public source of a committed Jagged column's real height. `Pow2` means
/// `2^(source + adjustment)` where the source indices match
/// [`col_kappa_sources`]; `TableRows(t)` is the announced, unpadded row count
/// of opcode table `t`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColHeightSource {
    Pow2 { source: usize, adjustment: usize },
    TableRows(usize),
}

/// Height sources in global schema order; `None` marks virtual columns.
pub fn col_height_sources(log_bytecode: usize) -> Vec<Option<ColHeightSource>> {
    let sch = schema();
    let mut out = vec![None; sch.n];
    out[MEM] = Some(ColHeightSource::Pow2 { source: 1, adjustment: 0 });
    out[MFCNT] = Some(ColHeightSource::Pow2 { source: 1, adjustment: 0 });
    out[BFCNT] = Some(ColHeightSource::Pow2 {
        source: 0,
        adjustment: log_bytecode,
    });
    out[QPKD] = Some(ColHeightSource::Pow2 {
        source: 2 + tables::BLAKE3_TABLE,
        adjustment: flock::blake3::K_LOG - ::pcs::LOG_PACKING,
    });
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        out[base..base + table.n_committed_columns()]
            .fill(Some(ColHeightSource::TableRows(t)));
    }
    let b3 = sch.base[tables::BLAKE3_TABLE];
    for &c in &tables::BLAKE3_VALUE_COLS {
        out[b3 + c] = None;
    }
    out
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

/// Resolve the symbolic column-size sources used by recursion into concrete
/// log-sizes. `None` marks a virtual (uncommitted) column.
fn col_kappas(log_mem: usize, log_bytecode: usize, taus: [usize; 6]) -> Vec<Option<usize>> {
    let values = [0, log_mem, taus[0], taus[1], taus[2], taus[3], taus[4], taus[5]];
    col_kappa_sources(log_bytecode)
        .into_iter()
        .map(|source| source.map(|(index, adjustment)| values[index] + adjustment))
        .collect()
}

/// Real Jagged heights for the committed columns. Shared memory/bytecode data
/// and flock's `q_pkd` remain full power-of-two columns. Per-opcode columns
/// commit only their executed-row prefix; their fixed padding is reconstructed
/// publicly when claims are routed to the PCS.
fn col_heights(
    log_mem: usize,
    log_bytecode: usize,
    row_counts: [usize; 6],
    kappas: &[Option<usize>],
) -> Vec<usize> {
    let sch = schema();
    let mut heights = vec![0usize; sch.n];
    heights[MEM] = 1usize << log_mem;
    heights[MFCNT] = 1usize << log_mem;
    heights[BFCNT] = 1usize << log_bytecode;
    heights[QPKD] = 1usize << kappas[QPKD].expect("q_pkd is committed");
    for (t, table) in tables::tables().iter().enumerate() {
        let base = sch.base[t];
        for height in &mut heights[base..base + table.n_committed_columns()] {
            *height = row_counts[t];
        }
    }
    for (height, kappa) in heights.iter_mut().zip(kappas) {
        if kappa.is_none() {
            *height = 0;
        }
    }
    heights
}

/// Build the public [`Layout`] from the program, the memory log-size `log_mem`, the
/// six tables' real row counts `row_counts`, and the public input `pi`. The flush
/// blocks reference columns only by INDEX and the program only through its
/// public columns, so this needs no committed witness — both prover and verifier
/// reconstruct exactly the same structure (§7, §8).
pub fn layout(prog: &[Op], log_mem: usize, row_counts: [usize; 6], pi: [F128; 2]) -> Layout {
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
    // The BLAKE3 table is ALWAYS sized to flock's `2^n_log` instance count
    // (`max(count,1)`, lincheck floor ≥ 8) so its per-instance (virtual) value
    // columns share `q_pkd`'s instance cube — a value-column bus claim at instance
    // point `r` maps to a strided `q_pkd` slot claim at `r` (`slot_claims`).
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
        Op::Blake3 { .. } => OP_BLAKE3,
    };
    let operands = |op: &Op| -> (F128, F128, F128) {
        match *op {
            Op::Xor { a, b, c } | Op::Mul { a, b, c } => (g_at(a), g_at(b), g_at(c)),
            Op::Set { o, k } => (g_at(o), k, F128::ZERO),
            Op::Deref { alpha, beta, gamma, .. } => (g_at(alpha), g_at(beta), g_at(gamma)),
            Op::Jump { oc, od, of } => (g_at(oc), g_at(od), g_at(of)),
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
        _ => F128::ZERO,
    };
    let ffp = |op: &Op| match op {
        Op::Deref { mode, .. } => mode.f_fp(),
        Op::Blake3 { cv, .. } => g_at(*cv),
        _ => F128::ZERO,
    };
    let extra0 = |op: &Op| match op {
        Op::Blake3 { out, .. } => g_at(*out),
        _ => F128::ZERO,
    };
    let extra1 = |op: &Op| match op {
        Op::Blake3 { metadata, .. } => *metadata,
        _ => F128::ZERO,
    };
    // The program is PUBLIC (not committed): eight public columns over the
    // program cube, embedded in the bytecode seed/finalize blocks below.
    let prog_op: Vec<F128> = prog.par_iter().map(opcode).collect();
    let prog_o1: Vec<F128> = prog.par_iter().map(|o| operands(o).0).collect();
    let prog_o2: Vec<F128> = prog.par_iter().map(|o| operands(o).1).collect();
    let prog_o3: Vec<F128> = prog.par_iter().map(|o| operands(o).2).collect();
    let prog_fpc: Vec<F128> = prog.par_iter().map(fpc).collect();
    let prog_ffp: Vec<F128> = prog.par_iter().map(ffp).collect();
    let prog_extra0: Vec<F128> = prog.par_iter().map(extra0).collect();
    let prog_extra1: Vec<F128> = prog.par_iter().map(extra1).collect();

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
            Public(prog_extra0.clone()),
            Public(prog_extra1.clone()),
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
        pad[b3 + tables::BLAKE3_VALUE_COLS[6]] = crate::blake3_flock::IV[0]; // cv0
        pad[b3 + tables::BLAKE3_VALUE_COLS[7]] = crate::blake3_flock::IV[1]; // cv1
        pad[b3 + tables::BLAKE3_VALUE_COLS[8]] = crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS);
    }

    let kappas = col_kappas(log_mem, log_bytecode, taus);
    let heights = col_heights(log_mem, log_bytecode, row_counts, &kappas);
    // q_pkd stays at offset zero so its ring-switched weight remains an aligned
    // subcube. Every ordinary column after it is packed tightly and opened via
    // the Jagged indicator.
    let jagged_blocks = jagged_column_blocks(log_bytecode, [&push, &pull, &count_blocks]);
    let (placements, m) = witness::placements_of_blocks(&kappas, &heights, &jagged_blocks);
    Layout {
        push,
        pull,
        count: count_blocks,
        pad,
        placements,
        jagged_blocks,
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
        // Shared columns.
        cols[MEM] = exec.mem.clone();
        cols[MFCNT] = tr.mem_count.clone(); // running counts ended at g^{A[i]}
        cols[BFCNT] = tr.bytecode_count.clone(); // running counts ended at g^{A[pc]}
        // flock's packed BLAKE3 witness q_pkd, ALWAYS committed in this same stack:
        // built from the executed BLAKE3 rows in order (row j = flock instance j),
        // padded to `2^n_blocks_log(max(count,1))` all-padding instances — so a
        // program with no BLAKE3 still carries a single padding instance.
        let fill_ms = t_fill.elapsed().as_secs_f64() * 1e3;
        let t_qpkd = std::time::Instant::now();
        let (q_pkd, flock_reduction) = {
            let blocks: Vec<_> = tr
                .blake3
                .iter()
                .map(|r| {
                    crate::blake3_flock::compression(
                        [r.va0, r.va1],
                        [r.vb0, r.vb1],
                        [r.vcv0, r.vcv1],
                        r.metadata,
                    )
                })
                .collect();
            crate::blake3_flock::build_qpkd_prepared(&blocks)
        };
        cols[QPKD] = q_pkd;
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
        let t_stack = std::time::Instant::now();
        let q = witness::stack_q(&cols, &l.placements, l.m);
        if prof {
            eprintln!("[build] stack_q     : {:>7.2} ms", t_stack.elapsed().as_secs_f64() * 1e3);
        }
        Witness {
            cols,
            q,
            layout: l,
            log_mem,
            row_counts,
            flock_reduction: Some(flock_reduction),
        }
    }
}
