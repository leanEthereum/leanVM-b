//! Whole-program assembly over GF(2^64) (§7, §8): instruction tables share a
//! state grand-product bus and two logup* indexed lookups for memory and
//! bytecode. Addresses and the program counter are g-powers, so every increment
//! is a free ×g. Machine-word arithmetic
//! is over `E = F192 = K[y]/(y³+y+1)` (XOR degree 1, MUL_NATIVE degree 2),
//! with each word represented by three `K = F64` limbs; access-side limbs are
//! virtual and only memory-table limbs are committed. `BLAKE3`
//! (§7.6) adds the memory/state/bytecode plumbing for a 64→32-byte compression
//! whose relation is discharged by flock (see [`crate::blake3_flock`]). All
//! Challenges and transcript scalars live in the same tower E.

use std::collections::HashMap;

use rayon::prelude::*;

use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::logup_star::{self, Family};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_BLAKE3, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM, SEP_STATE,
};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::{self, Column};
use primitives::field::{F64, F192, g_pow};

mod execute;
pub mod hints;
mod isa;
mod layout;
mod trace;
pub use execute::Execution;
pub use isa::{DerefMode, Op};
pub use layout::*;
pub(crate) use trace::{Brow, Drow, Jrow, Srow, Trace, Xrow};

/// Witness-gen `BLAKE3` compression (doc §7.6): the eight input words are the two
/// 256-bit operands `a = va[0..4]`, `b = vb[0..4]` laid out little-endian into
/// 64 bytes (8 bytes per 64-bit word); the 32-byte digest is split back into the
/// four output words `c`. The BLAKE3 hash of the 64-byte input — the relation
/// flock then proves ([`crate::blake3_flock`]). Delegates to
/// [`crate::vmhash::compress`], THE primitive every VM-native hash chains.
fn blake3_compress(va: [F64; 4], vb: [F64; 4]) -> [F64; 4] {
    crate::vmhash::compress(va, vb)
}

/// Data-memory size bounds (doc §Memory): memory is `2^h` cells with
/// `MIN_LOG_MEM ≤ h ≤ MAX_LOG_MEM`. The prover pads up to the minimum; the
/// verifier rejects any announced `h` outside the range. `MIN_LOG_MEM` is also
/// the static cap on range-check bounds (`compiler::Stmt::AssertLt`): a bound
/// `≤ 2^MIN_LOG_MEM` keeps the complement argument sound for every memory size
/// the prover may announce.
pub const MIN_LOG_MEM: usize = 16;
const MAX_LOG_MEM: usize = 32;

/// Each per-opcode table holds at most `2^MAX_LOG_ROWS` rows (executed
/// instructions of that opcode). Together with `MAX_LOG_MEM` and the bytecode
/// cap these are the *instance caps* (transition doc §caps). They keep every
/// generator-power index distinct and the reduction degrees within the stated
/// soundness budget, so the verifier rejects oversized announcements up front.
const MAX_LOG_ROWS: usize = 32;

/// Bytecode-length instance cap (see [`MAX_LOG_ROWS`]): programs are at most
/// `2^32` instructions.
const MAX_LOG_BYTECODE: usize = 32;

/// A binding digest of the program bytecode (BLAKE3 of every instruction's
/// canonical encoding — opcode, operands, and the DEREF store-mode), as two field
/// elements. Seeded into the transcript alongside the public input, so EVERY
/// challenge depends on the exact program.
///
/// Without this the program's instruction content would enter verification only
/// through the public bytecode-table evaluation produced by logup* — a single
/// point an attacker recovers from a finished proof. It could then
/// craft a different program `P'` agreeing with `P`'s bytecode columns at that one
/// `ζ` and re-present the same proof for `P'` (adaptive-statement forgery). Seeding
/// `H(program)` before any challenge makes the whole statement — (program, public
/// input) — bound up front, so a different program yields a different sponge from
/// the very first squeeze. Both sides hold the program, so both compute this
/// identically; the announced sizes ride the stream (`announce_public`).
fn program_digest(prog: &[Op]) -> [F64; 4] {
    // VM-native: encode the program as a field-element slice and hash it with the
    // Merkle–Damgård slice hash ([`crate::vmhash::hash_slice`]), so a recursive
    // verifier can recompute this digest with the `Blake3` opcode alone.
    let mut words: Vec<F64> = Vec::with_capacity(5 * prog.len() + 2);
    // Domain/version marker (the MD IV also binds the total length).
    words.push(F64(prog.len() as u64));
    words.push(F64(2));
    for op in prog {
        // Encode every op injectively as (tag, four u32 operands, one 192-bit
        // immediate) → five words: two operand-offset words packed with the tag,
        // then the immediate's three lanes. BLAKE3 carries five offsets, so its
        // 4th/5th ride the (otherwise-zero) immediate's low lane.
        let (tag, a, b, c, k) = match *op {
            Op::Xor { a, b, c } => (0u8, a, b, c, F192::ZERO),
            Op::Mul { a, b, c } => (1, a, b, c, F192::ZERO),
            Op::Set { o, k } => (2, o, 0, 0, k),
            Op::Deref {
                alpha,
                beta,
                gamma,
                mode,
            } => {
                (3 + mode as u8, alpha, beta, gamma, F192::ZERO) // mode ∈ {Cell,Pc,Fp} ⇒ tag 3/4/5
            }
            Op::Jump { oc, od, of } => (6, oc, od, of, F192::ZERO),
            Op::Pack64x2 { a, b, c } => (9, a, b, c, F192::ZERO),
            Op::Blake3 { ins, out } => (
                7,
                ins[0],
                ins[1],
                ins[2],
                F192::new(ins[3] as u64 | ((out as u64) << 32), 0, 0),
            ),
        };
        words.push(F64(a as u64 | ((b as u64) << 32)));
        words.push(F64(c as u64 | ((tag as u64) << 32)));
        words.push(F64(k.c0));
        words.push(F64(k.c1));
        words.push(F64(k.c2));
    }
    crate::vmhash::hash_slice(&words)
}

/// The Fiat–Shamir seed: ONE 32-byte digest, as two field words, committing
/// to everything fixed about the proving environment — the flock circuit
/// family (its per-block R1CS matrices, [`crate::blake3_flock::family_digest`])
/// and the program's bytecode digest. It leads every transcript, so all
/// challenges depend on the circuit version and the program before anything
/// else; a recursion guest carries the INNER program's seed in its public
/// input, pinning both with one word pair.
pub fn fs_seed(program: &Program) -> [F192; 2] {
    let mut h = blake3::Hasher::new();
    h.update(b"leanvm-b-fs-seed-v1");
    h.update(&crate::blake3_flock::family_digest());
    for w in program.digest {
        h.update(&w.0.to_le_bytes());
    }
    let d = *h.finalize().as_bytes();
    let word = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F192::new(word(0), word(8), 0), F192::new(word(16), word(24), 0)]
}

/// The transcript seed: the public statement bound before any challenge, the
/// public input `pi` prefixed by the [`fs_seed`]. Both sides build it identically.
fn transcript_seed(program: &Program, pi: &[F192; 2]) -> [F192; 4] {
    let seed = fs_seed(program);
    [seed[0], seed[1], pi[0], pi[1]]
}

/// Announce the prover's per-table log-sizes (`log_mem` + all `row_counts`) by
/// writing them onto the scalar stream (which binds them into the sponge and lets
/// the verifier reconstruct the layout). The public statement (program + input) is
/// not announced here — it seeds the transcript at construction (see
/// [`transcript_seed`]). The boundary states and per-table log-sizes (`taus`) are
/// derived (constants from the program, and `padlen(row_counts)`), so they need no
/// separate binding.
fn announce_public(ps: &mut ProverState, log_mem: usize, row_counts: [usize; tables::N_TABLES], log_inv_rate: usize) {
    ps.add_scalar(F192::new(log_mem as u64, 0, 0));
    for r in row_counts {
        ps.add_scalar(F192::new(r as u64, 0, 0));
    }
    ps.add_scalar(F192::new(log_inv_rate as u64, 0, 0));
}

/// Verifier side of [`announce_public`]: read the announced sizes and PCS
/// rate from the stream, validate them, and reconstruct the public [`Layout`]
/// from the program + sizes + public input. (The public input was already bound
/// by seeding the transcript.)
fn read_public(vs: &mut VerifierState, prog: &Program, public_input: &[F192; 2]) -> Result<(Layout, usize), Error> {
    let log_mem = vs.next_scalar().map_err(Error::Transcript)?.c0 as usize;
    let mut row_counts = [0usize; tables::N_TABLES];
    for r in &mut row_counts {
        *r = vs.next_scalar().map_err(Error::Transcript)?.c0 as usize;
    }
    let rate_word = vs.next_scalar().map_err(Error::Transcript)?;
    let log_inv_rate = rate_word.c0 as usize;
    // The instance caps (transition doc §caps): with `ord(g) = 2^64 − 1`, the
    // counting arguments (memory soundness, count non-wrap, exponent range checks)
    // are theorems only when the announced instance keeps the total read-flush
    // count provably below `2^64 − 1`, so reject any announcement exceeding the
    // caps BEFORE running any reduction. (A table's row count is the number of
    // times its opcode runs — unbounded by the bytecode size, since a small loop
    // body runs many times — so it gets its own cap, not `bytecode_size`.)
    let bytecode_size = prog.prog.len();
    if !bytecode_size.is_power_of_two()
        || bytecode_size > (1usize << MAX_LOG_BYTECODE)
        || !(MIN_LOG_MEM..=MAX_LOG_MEM).contains(&log_mem)
        || row_counts.iter().any(|&r| r >= (1usize << MAX_LOG_ROWS))
        || rate_word != F192::new(log_inv_rate as u64, 0, 0)
        || ::pcs::ligerito::validate_log_inv_rate(log_inv_rate).is_err()
    {
        return Err(Error::PublicInput);
    }
    let l = layout(&prog.prog, log_mem, row_counts, *public_input);
    Ok((l, log_inv_rate))
}

#[derive(Clone)]
pub struct Program {
    pub prog: Vec<Op>, // bytecode (size B, power of two)
    pub pc0: u32,
    pub fp0: u32,
    /// A binding digest of `prog` ([`program_digest`]), computed once at assembly
    /// and seeded into the transcript so every challenge depends on the exact
    /// program. Trusted to match `prog` — always set by [`Program::assemble`] from
    /// the bytecode, so a `Program` value cannot carry a digest inconsistent with
    /// its own `prog`.
    pub(crate) digest: [F64; 4],
    /// Prover-side frame/buffer allocation hints (keyed by global pc) and the
    /// size of `main`'s frame — the nondeterminism [`Program::execute`] needs to
    /// run the program. Public verification (§ `verify`) ignores them.
    pub(crate) hints: HashMap<u32, Vec<hints::RHint>>,
    pub(crate) main_frame: u32,
    /// Named prover witness streams for the program's `hint_witness` calls
    /// ([`Program::set_witness`]): a stream is a sequence of *entries* (one
    /// slice of values per `hint_witness` call — the same symbol may be
    /// hinted many times); each call pops the next entry, whose length must
    /// match its destination. Prover-side only; verification ignores them.
    pub(crate) witness: HashMap<String, Vec<Vec<F192>>>,
    /// Function pc-ranges `(name, entry, len)` from the compiler, for the
    /// `DBG_PROF=1` per-function cycle profile ([`Program::execute`]). Purely
    /// diagnostic; empty for hand-assembled programs.
    pub fn_ranges: Vec<(String, u32, u32)>,
}

impl Program {
    /// Assemble a [`Program`], computing its bytecode [`digest`](Program::digest)
    /// from `prog`. The single funnel for construction, so the digest is always
    /// consistent with the bytecode.
    pub fn assemble(
        prog: Vec<Op>,
        pc0: u32,
        fp0: u32,
        hints: HashMap<u32, Vec<hints::RHint>>,
        main_frame: u32,
    ) -> Self {
        let digest = program_digest(&prog);
        Self {
            prog,
            pc0,
            fp0,
            digest,
            hints,
            main_frame,
            witness: HashMap::new(),
            fn_ranges: Vec::new(),
        }
    }

    /// Supply the entries of witness stream `name`: one slice of values per
    /// `hint_witness(dest, "name")` call, popped in order (the same symbol
    /// may be hinted many times). Prover-side data: entirely unconstrained,
    /// invisible to verification.
    pub fn set_witness(&mut self, name: impl Into<String>, entries: Vec<Vec<F192>>) {
        self.witness.insert(name.into(), entries);
    }
}

impl Program {
    /// Assemble a program directly from a fixed bytecode vector, starting at
    /// `(pc, fp) = (0, 0)` with no allocation hints. Suitable for straight-line
    /// programs that never change the frame pointer and touch only the first
    /// `main_frame` memory cells (so the prover needs no nondeterministic frame
    /// allocation). `prog.len()` must be a power of two with a never-executed
    /// sentinel in its last slot — the run halts on reaching `g^{len-1}` (§state).
    pub fn from_bytecode(prog: Vec<Op>, main_frame: u32) -> Self {
        Self::assemble(prog, 0, 0, HashMap::new(), main_frame)
    }
}

/// The whole proof is the transcript: a scalar stream plus the PCS hint
/// channels (see [`crate::transcript::Proof`]).
pub use crate::transcript::Proof;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Bus(leaf::Error),
    Constraint(usize, constraints::Error),
    Open(pcs::Error),
    OpenPush(pcs::Error),
    Logup(logup_star::Error),
    LookupValue,
    PublicInput,
    Transcript(crate::transcript::Error),
    /// flock's BLAKE3 R1CS validity sub-proof failed to verify. (A missing or
    /// malformed sub-proof surfaces as [`Error::Transcript`] when the shared
    /// `stream`/`openings` fail to reconstruct or fully consume.)
    Blake3(flock::verifier::VerifyError),
}

/// Lift each table's constraint evals (at its zerocheck point `rho`) to global
/// column claims, offsetting the table's local constraint columns by its base.
fn constraint_claims(table_claims: &[constraints::Claims]) -> Vec<ColumnClaim> {
    let sch = schema();
    let mut v = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        for (k, &c) in table.constraint_columns().iter().enumerate() {
            v.push(ColumnClaim {
                col: sch.base[t] + c,
                start: 0,
                point: table_claims[t].rho.clone(),
                value: table_claims[t].evals[k],
            });
        }
    }
    v
}

type EvalMaps = Vec<std::collections::HashMap<usize, F192>>;

fn constraint_eval_maps(table_claims: &[constraints::Claims]) -> EvalMaps {
    let sch = schema();
    tables::tables()
        .iter()
        .enumerate()
        .map(|(t, table)| {
            table
                .constraint_columns()
                .iter()
                .copied()
                .zip(table_claims[t].evals.iter().copied())
                .map(|(col, value)| (sch.base[t] + col, value))
                .collect()
        })
        .collect()
}

fn openable_claim(layout: &Layout, claim: &ColumnClaim) -> bool {
    !layout.placements[claim.col].is_virtual() || blake3_value_slot(claim.col).is_some()
}

fn complete_value_evals_prove(
    layout: &Layout,
    table_claims: &[constraints::Claims],
    cols: &[Column],
    ps: &mut ProverState,
) -> (EvalMaps, Vec<ColumnClaim>) {
    let mut maps = constraint_eval_maps(table_claims);
    let mut claims = Vec::new();
    for lookup in [&layout.memory_lookup, &layout.bytecode_lookup] {
        for site in &lookup.sites {
            if site.real == 0 {
                continue;
            }
            for coord in &site.values {
                let col = match coord {
                    Coord::Col(col) | Coord::GCol(col, _) => *col,
                    Coord::Const(_) => continue,
                    _ => panic!("unsupported lookup value coordinate"),
                };
                if maps[site.table].contains_key(&col) {
                    continue;
                }
                let point = &table_claims[site.table].rho;
                let value = primitives::multilinear::mle_eval(&cols[col], point);
                ps.add_scalar(value);
                maps[site.table].insert(col, value);
                let claim = ColumnClaim {
                    col,
                    start: 0,
                    point: point.clone(),
                    value,
                };
                if openable_claim(layout, &claim) {
                    claims.push(claim);
                }
            }
        }
    }
    (maps, claims)
}

fn complete_value_evals_verify(
    layout: &Layout,
    table_claims: &[constraints::Claims],
    vs: &mut VerifierState,
) -> Result<(EvalMaps, Vec<ColumnClaim>), Error> {
    let mut maps = constraint_eval_maps(table_claims);
    let mut claims = Vec::new();
    for lookup in [&layout.memory_lookup, &layout.bytecode_lookup] {
        for site in &lookup.sites {
            if site.real == 0 {
                continue;
            }
            for coord in &site.values {
                let col = match coord {
                    Coord::Col(col) | Coord::GCol(col, _) => *col,
                    Coord::Const(_) => continue,
                    _ => return Err(Error::LookupValue),
                };
                if maps[site.table].contains_key(&col) {
                    continue;
                }
                let value = vs.next_scalar().map_err(Error::Transcript)?;
                maps[site.table].insert(col, value);
                let claim = ColumnClaim {
                    col,
                    start: 0,
                    point: table_claims[site.table].rho.clone(),
                    value,
                };
                if openable_claim(layout, &claim) {
                    claims.push(claim);
                }
            }
        }
    }
    Ok((maps, claims))
}

fn lookup_site_values(
    lookup: &logup_star::AccessLayout,
    table_claims: &[constraints::Claims],
    maps: &EvalMaps,
    pad: &[F64],
    theta: F192,
) -> Vec<F192> {
    lookup
        .sites
        .iter()
        .map(|site| {
            if site.real == 0 {
                return F192::ZERO;
            }
            let prefix = logup_star::real_prefix_weight(&table_claims[site.table].rho, site.real);
            let mut value = F192::ZERO;
            let mut theta_power = F192::ONE;
            for coord in &site.values {
                let (full, padding) = match coord {
                    Coord::Const(v) => (F192::from(*v), *v),
                    Coord::Col(col) => (maps[site.table][col], pad[*col]),
                    Coord::GCol(col, k) => (
                        maps[site.table][col].mul_base(primitives::field::g_pow(*k as usize)),
                        pad[*col] * primitives::field::g_pow(*k as usize),
                    ),
                    _ => panic!("unsupported lookup value coordinate"),
                };
                let real = full + F192::from(padding) * (F192::ONE + prefix);
                value += theta_power * real;
                theta_power *= theta;
            }
            value
        })
        .collect()
}

fn memory_table(memory: &[F192], theta: F192) -> Vec<F192> {
    memory
        .iter()
        .map(|word| {
            F192::new(word.c0, 0, 0) + theta * F192::new(word.c1, 0, 0) + theta * theta * F192::new(word.c2, 0, 0)
        })
        .collect()
}

/// If `col` is a BLAKE3 **value** column (global index), its `q_pkd` packed slot.
/// These columns are virtual (uncommitted): their memory-bus evaluation claims
/// are re-routed to `q_pkd` slot evaluations, which is the whole binding — the
/// bus-tied value IS the proven `q_pkd` word, no separate check needed.
fn blake3_value_slot(col: usize) -> Option<usize> {
    let base = schema().base[tables::BLAKE3_TABLE];
    tables::BLAKE3_VALUE_COLS
        .iter()
        .position(|&c| base + c == col)
        .map(|i| crate::blake3_flock::SLOTS[i])
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode counts
/// `[XOR, MUL, SET, DEREF, JUMP, BLAKE3, PACK64X2]`, and the
/// committed witness size — the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize,
    pub counts: [usize; tables::N_TABLES],
    pub committed: usize,
    /// Data memory is `2^log_mem` cells (the padded write-once image).
    pub log_mem: usize,
    /// Cells actually touched, before the pad to `2^log_mem` — the real memory
    /// footprint (`log2` is fractional).
    pub mem_used: usize,
}

/// Prove the program on the given public input: run it (witness generation),
/// then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof and the
/// run [`Stats`]. `log_inv_rate` selects the PCS rate and is announced in the
/// Fiat–Shamir transcript before the commitment.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate))]
pub fn prove(program: &Program, public_input: [F192; 2], log_inv_rate: usize) -> (Proof, Stats) {
    ::pcs::ligerito::validate_log_inv_rate(log_inv_rate).expect("valid log_inv_rate");
    let prof = std::env::var("LEANVM_PROFILE").is_ok();
    let ms = |t: std::time::Instant| t.elapsed().as_secs_f64() * 1e3;
    let t = std::time::Instant::now();
    let exec = tracing::info_span!("Execute program").in_scope(|| program.execute(public_input));
    if prof {
        eprintln!("[prove] execute     : {:>7.2} ms", ms(t));
    }
    // The BLAKE3 R1CS setup (circuit construction) is a ~hundreds-of-ms cost that
    // depends only on the compression count (the circuit *shape*), not the witness
    // — but it is otherwise built synchronously inside the final reduction, adding
    // that latency serially with nothing overlapping it. Now that `execute` has
    // told us the count, build it on a background thread: it constructs
    // concurrently with the build/commit/bus/constraint stages (~1 s of work) and
    // lands in the shared setup cache, so the reduction's `setup_for` is a cache
    // hit. Pure warm-up — the result is fetched from the cache, nothing here joins
    // the handle. (A no-BLAKE3 program still warms the size-1 padding shape.)
    let n_b3_warm = exec.trace.blake3.len().max(1);
    std::thread::spawn(move || crate::blake3_flock::warm_setup(n_b3_warm));
    let cycles = exec.cycles;
    let w = tracing::info_span!("Build witness").in_scope(|| program.build(&exec));
    let counts = w.row_counts;
    // Real committed data, before zero-pad to 2^m. Virtual access-value and
    // operand columns are filled for AIR/logup* but excluded from the PCS.
    let mut committed_size: usize = w
        .cols
        .iter()
        .zip(&w.layout.placements)
        .filter(|(_, p)| !p.is_virtual())
        .map(|(c, _)| c.len())
        .sum();
    // The public statement (program digest + input) seeds the transcript, so
    // every challenge depends on the exact program and public input.
    let mut ps = ProverState::new(b"leanvm-b", &transcript_seed(program, &public_input));

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.log_mem, w.row_counts, log_inv_rate);
    let t = std::time::Instant::now();
    let committed = tracing::info_span!("Commit").in_scope(|| pcs::commit(&mut ps, &w.q, log_inv_rate));
    if prof {
        eprintln!("[prove] commit      : {:>7.2} ms", ms(t));
    }
    let l = &w.layout;

    // BLAKE3 ↔ flock (§blake3_flock), single PCS: q_pkd is ALWAYS a column in
    // `w.q` (≥1 instance — a program with no BLAKE3 carries one padding instance,
    // so the proof shape is uniform and there is no has/hasn't-BLAKE3 fork). flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE
    // Ligerito over this commitment (below). The input/output words bind via the
    // memory lookup (virtual value columns route to q_pkd); the constant pins reuse a
    // bus point, so no dedicated binding challenge is drawn. Mirrored in `verify`.
    let t = std::time::Instant::now();
    let bus_claims =
        tracing::info_span!("Prove state bus").in_scope(|| leaf::prove_balance(&l.push, &l.pull, &w.cols, &mut ps));
    if prof {
        eprintln!("[prove] bus(grand-p): {:>7.2} ms", ms(t));
    }
    let t = std::time::Instant::now();
    let table_claims = tracing::info_span!("Prove constraints").in_scope(|| {
        let sch = schema();
        let mut table_claims = Vec::new();
        for (ti, table) in tables::tables().iter().enumerate() {
            let involved = table.constraint_columns();
            let position = tables::column_positions(involved);
            let cols: Vec<Column> = involved.iter().map(|&c| w.cols[sch.base[ti] + c].clone()).collect();
            table_claims.push(constraints::prove(
                &cols,
                |eta, vals| table.eval_constraint(eta, &tables::Cols::new(vals, &position)),
                &mut ps,
            ));
        }
        table_claims
    });
    if prof {
        eprintln!("[prove] constraints : {:>7.2} ms", ms(t));
    }

    // The access-side value/operand columns are not committed. Their AIR-point
    // evaluations ride the transcript first; only then do we sample the value
    // RLC and per-site batching challenges. This makes the two transparent
    // numerators bind every virtual value claim without a value-column PCS.
    let (value_maps, mut value_source_claims) = complete_value_evals_prove(l, &table_claims, &w.cols, &mut ps);
    let theta = ps.sample();
    let table_points: Vec<Vec<F192>> = table_claims.iter().map(|claim| claim.rho.clone()).collect();
    let mem_site_values = lookup_site_values(&l.memory_lookup, &table_claims, &value_maps, &l.pad, theta);
    let bc_site_values = lookup_site_values(&l.bytecode_lookup, &table_claims, &value_maps, &l.pad, theta);
    let mem_gammas = ps.sample_vec(l.memory_lookup.sites.len());
    let bc_gammas = ps.sample_vec(l.bytecode_lookup.sites.len());
    let mem_batched = l
        .memory_lookup
        .batch_values(&table_points, &mem_site_values, &mem_gammas);
    let bc_batched = l
        .bytecode_lookup
        .batch_values(&table_points, &bc_site_values, &bc_gammas);
    let memory_table = memory_table(&exec.mem, theta);
    let bytecode_table = logup_star::bytecode_table(&l.bytecode_rows, theta);
    let memory_access = l.memory_lookup.materialize(&w.cols, 1usize << w.log_mem);
    let bytecode_access = l.bytecode_lookup.materialize(&w.cols, l.bytecode_rows.len());
    let y_mem = memory_access.pushforward(&mem_batched.weights, 1usize << w.log_mem);
    let y_bc = bytecode_access.pushforward(&bc_batched.weights, l.bytecode_rows.len());
    let push_witness = logup_star::PushforwardWitness::new(&y_mem, &y_bc);
    committed_size += push_witness.cols.iter().map(Vec::len).sum::<usize>();
    let push_committed =
        tracing::info_span!("Commit pushforwards").in_scope(|| pcs::commit(&mut ps, &push_witness.q, log_inv_rate));
    let mem_lookup = logup_star::prove_lookup(
        Family::Memory,
        &l.memory_lookup,
        &memory_access,
        &mem_batched,
        memory_table,
        &y_mem,
        &push_witness,
        theta,
        F192::ONE,
        &w.cols,
        &mut ps,
    );
    let bc_lookup = logup_star::prove_lookup(
        Family::Bytecode,
        &l.bytecode_lookup,
        &bytecode_access,
        &bc_batched,
        bytecode_table,
        &y_bc,
        &push_witness,
        theta,
        F192::ONE,
        &w.cols,
        &mut ps,
    );

    let mut claims = constraint_claims(&table_claims)
        .into_iter()
        .filter(|claim| openable_claim(l, claim))
        .collect::<Vec<_>>();
    claims.append(&mut value_source_claims);
    claims.extend(mem_lookup.main_claims);
    claims.extend(bc_lookup.main_claims);
    claims.extend(bus_claims);
    let mut push_claims = mem_lookup.push_claims;
    push_claims.extend(bc_lookup.push_claims);
    // The PI binding transmits the low/high memory-limb evaluations. The full
    // F192 public-input interpolation then determines the top-limb evaluation.
    let r_pi = ps.sample();
    let pi_lo = primitives::multilinear::interp_k(F64(w.layout.pi[0].c0), F64(w.layout.pi[1].c0), r_pi);
    let pi_hi = primitives::multilinear::interp_k(F64(w.layout.pi[0].c1), F64(w.layout.pi[1].c1), r_pi);
    ps.add_scalar(pi_lo);
    ps.add_scalar(pi_hi);
    claims.extend(bind_pi_claim(r_pi, &w.layout.placements, &w.layout.pi, pi_lo, pi_hi));
    // The input/output words bind via the memory lookup (value columns are virtual and
    // route to q_pkd, see `slot_claims`); cv/counter/blen/flags are constants baked
    // into flock's per-block matrices, so no pin claims are needed.
    let slots = slot_claims(&w.layout, &claims);

    // Run flock's reduction (zerocheck + lincheck) over the executed compressions
    // (or a single padding instance when none ran); it returns the `(ab, c)`
    // validity claims on the committed `q_pkd`, discharged by the PCS below in the
    // SAME Ligerito as every leanVM point claim (the point claims become the
    // opener's `point_claims`).
    let t = std::time::Instant::now();
    use flock::blake3::Compression;
    let blocks: Vec<Compression> = if exec.trace.blake3.is_empty() {
        vec![crate::blake3_flock::padding_compression()]
    } else {
        exec.trace
            .blake3
            .iter()
            .map(|r| crate::blake3_flock::compression(r.va, r.vb))
            .collect()
    };
    let (_z_packed, reduced) = tracing::info_span!("Flock reduction")
        .in_scope(|| crate::blake3_flock::prove_reduction(&blocks, &committed.commitment, &mut ps));
    if prof {
        eprintln!("[prove]   reduction : {:>7.2} ms", ms(t));
    }
    let t = std::time::Instant::now();
    let offset = w.layout.placements[QPKD].offset;
    let ring = tracing::info_span!("Package ring switch")
        .in_scope(|| crate::blake3_flock::ring_switch_open(blocks.len(), offset, &reduced));
    if prof {
        eprintln!("[prove]   ring pkg  : {:>7.2} ms", ms(t));
    }
    let t = std::time::Instant::now();
    let mixed_open = tracing::info_span!("PCS open").in_scope(|| pcs::open(&mut ps, &committed, &w.q, &slots, &ring));
    if prof {
        eprintln!("[prove]   stack open: {:>7.2} ms", ms(t));
    }
    // flock's scalar sub-proof already rode the shared stream (add_scalar at its
    // protocol points); only the Merkle-bearing stacked opening needs the hint
    // channel.
    ps.hint_opening(mixed_open);
    let push_open = tracing::info_span!("Pushforward PCS open")
        .in_scope(|| pcs::open_plain(&mut ps, &push_committed, &push_witness.q, &push_claims));
    ps.hint_opening(push_open);
    if prof {
        eprintln!("[prove] open        : {:>7.2} ms", ms(t));
    }
    (
        ps.into_proof(),
        Stats {
            cycles,
            counts,
            committed: committed_size,
            log_mem: w.log_mem,
            mem_used: exec.mem_used,
        },
    )
}

/// The public-input binding (§8): the committed `MEM` at `(r, 0,…,0)` must equal
/// `interp(pi[0], pi[1], r)`, split into its three physical `K` limbs. The
/// prover transmits `MEM_LO(r)` and `MEM_HI(r)`; both sides derive `MEM_TOP(r)`
/// from the full F192 interpolation. The opening discharges all three claims.
/// `placements` and `pi` come from the prover's or verifier's layout, so both
/// sides build byte-identical claims.
fn bind_pi_claim(
    r: F192,
    placements: &[witness::Placement],
    pi: &[F192; 2],
    v_lo: F192,
    v_hi: F192,
) -> [ColumnClaim; 3] {
    let mut point = vec![F192::ZERO; placements[MEM_LO].n_vars];
    point[0] = r;
    let y2 = F192::Y * F192::Y;
    let v_top = (primitives::multilinear::interp(pi[0], pi[1], r) + v_lo + F192::Y * v_hi) * y2.inv();
    [
        ColumnClaim {
            col: MEM_LO,
            start: 0,
            point: point.clone(),
            value: v_lo,
        },
        ColumnClaim {
            col: MEM_HI,
            start: 0,
            point: point.clone(),
            value: v_hi,
        },
        ColumnClaim {
            col: MEM_TOP,
            start: 0,
            point,
            value: v_top,
        },
    ]
}

/// Everything a recursion harness needs from an accepting verify run: the
/// deferred bytecode RLC claim, phase-boundary sponge states, flock reductions,
/// and summaries of both PCS openings.
pub struct VerifySummary {
    /// Transcript-bound inverse-rate logarithm used by this proof's PCS.
    pub log_inv_rate: usize,
    /// Evaluation of the public, RLC-batched bytecode table produced by logup*.
    pub bytecode_claim: (Vec<F192>, F192),
    /// RLC challenge for the bytecode columns.
    pub bytecode_rlc: F192,
    /// Sponge states after: the bus, the zerochecks, the PI sample, and the
    /// flock reduction.
    pub checkpoints: [[F64; 4]; 4],
    pub zc_claim: flock::zerocheck::ZerocheckClaim,
    pub lc_claim: flock::lincheck::LincheckClaim,
    pub opening: pcs::StackedOpeningSummary,
    pub push_opening: pcs::StackedOpeningSummary,
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs — never the prover's witness.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify(program: &Program, public_input: &[F192; 2], proof: &Proof) -> Result<VerifySummary, Error> {
    let mut vs = VerifierState::new(b"leanvm-b", proof, &transcript_seed(program, public_input));
    let (l, log_inv_rate) = read_public(&mut vs, program, public_input)?;
    let root = pcs::read_commitment(&mut vs).map_err(Error::Transcript)?;

    // BLAKE3 ↔ flock (single PCS): flock's R1CS validity and every leanVM point
    // claim are verified together by ONE Ligerito opening at the end. The executed-
    // BLAKE3 count is public (announced); its flock sub-proof rides the shared
    // `stream`/`openings`, and presence is enforced by consumption below plus
    // `vs.finish()` (a proof with `n_b3 = 0` but trailing flock data, or vice versa,
    // fails to fully consume). No dedicated binding challenge: the input/output
    // words bind via the memory lookup, while the pins reuse committed q_pkd data.
    let n_b3 = l.row_counts[tables::BLAKE3_TABLE];

    let bus = leaf::verify_balance(&l.push, &l.pull, &l.pad, &mut vs).map_err(Error::Bus)?;
    let checkpoint_bus = vs.sponge_state();

    let mut table_claims = Vec::new();
    for (ti, table) in tables::tables().iter().enumerate() {
        let involved = table.constraint_columns();
        let position = tables::column_positions(involved);
        let cl = constraints::verify(
            l.taus[ti],
            involved.len(),
            |eta, vals| table.eval_constraint(eta, &tables::Cols::new(vals, &position)),
            &mut vs,
        )
        .map_err(|e| Error::Constraint(ti, e))?;
        table_claims.push(cl);
    }
    let checkpoint_zerochecks = vs.sponge_state();

    let (value_maps, mut value_source_claims) = complete_value_evals_verify(&l, &table_claims, &mut vs)?;
    let theta = vs.sample();
    let table_points: Vec<Vec<F192>> = table_claims.iter().map(|claim| claim.rho.clone()).collect();
    let mem_site_values = lookup_site_values(&l.memory_lookup, &table_claims, &value_maps, &l.pad, theta);
    let bc_site_values = lookup_site_values(&l.bytecode_lookup, &table_claims, &value_maps, &l.pad, theta);
    let mem_gammas = vs.sample_vec(l.memory_lookup.sites.len());
    let bc_gammas = vs.sample_vec(l.bytecode_lookup.sites.len());
    let mem_batched = l
        .memory_lookup
        .batch_values(&table_points, &mem_site_values, &mem_gammas);
    let bc_batched = l
        .bytecode_lookup
        .batch_values(&table_points, &bc_site_values, &bc_gammas);
    let bytecode_table = logup_star::bytecode_table(&l.bytecode_rows, theta);
    let push_layout =
        logup_star::PushforwardLayout::new(l.placements[MEM_LO].n_vars, l.bytecode_rows.len().ilog2() as usize);
    let push_root = pcs::read_commitment(&mut vs).map_err(Error::Transcript)?;
    let mem_lookup = logup_star::verify_lookup(
        Family::Memory,
        &l.memory_lookup,
        &mem_batched,
        &[],
        l.placements[MEM_LO].n_vars,
        &push_layout,
        theta,
        F192::ONE,
        &mut vs,
    )
    .map_err(Error::Logup)?;
    let bc_lookup = logup_star::verify_lookup(
        Family::Bytecode,
        &l.bytecode_lookup,
        &bc_batched,
        &bytecode_table,
        l.bytecode_rows.len().ilog2() as usize,
        &push_layout,
        theta,
        F192::ONE,
        &mut vs,
    )
    .map_err(Error::Logup)?;

    let mut claims = constraint_claims(&table_claims)
        .into_iter()
        .filter(|claim| openable_claim(&l, claim))
        .collect::<Vec<_>>();
    claims.append(&mut value_source_claims);
    claims.extend(mem_lookup.main_claims);
    claims.extend(bc_lookup.main_claims);
    claims.extend(bus.claims);
    let mut push_claims = mem_lookup.push_claims;
    push_claims.extend(bc_lookup.push_claims);
    let r_pi = vs.sample();
    let pi_lo = vs.next_scalar().map_err(Error::Transcript)?;
    let pi_hi = vs.next_scalar().map_err(Error::Transcript)?;
    claims.extend(bind_pi_claim(r_pi, &l.placements, &l.pi, pi_lo, pi_hi));
    let checkpoint_pi = vs.sponge_state();
    let slots = slot_claims(&l, &claims);

    // Replay flock's reduction straight off the shared stream (each scalar bound
    // as it is read) to recover its `(ab, c)` validity claims on q_pkd, then
    // verify them alongside every point claim in the ONE Ligerito opening
    // (mirroring `prove`). `n_blocks = max(n_b3, 1)` — always ≥ 1 instance.
    let n_blocks = n_b3.max(1);
    let offset = l.placements[QPKD].offset;
    let replay = crate::blake3_flock::verify_reduction(n_blocks, &root, l.m, &mut vs).map_err(Error::Blake3)?;
    let checkpoint_flock = vs.sponge_state();
    let open = vs.next_opening().map_err(Error::Transcript)?;
    let ring = crate::blake3_flock::ring_switch_verify(n_blocks, offset, replay.ab, replay.c);
    let opening = pcs::verify(&mut vs, &slots, &ring, open, l.m, log_inv_rate, &root).map_err(Error::Open)?;
    let push_open = vs.next_opening().map_err(Error::Transcript)?;
    let push_opening = pcs::verify_plain(
        &mut vs,
        &push_claims,
        push_open,
        push_layout.mu,
        log_inv_rate,
        &push_root,
    )
    .map_err(Error::OpenPush)?;
    vs.finish().map_err(Error::Transcript)?;
    Ok(VerifySummary {
        bytecode_claim: bc_lookup
            .bytecode_table_claim
            .expect("bytecode lookup yields a public-table claim"),
        bytecode_rlc: theta,
        checkpoints: [checkpoint_bus, checkpoint_zerochecks, checkpoint_pi, checkpoint_flock],
        zc_claim: replay.zc_claim,
        lc_claim: replay.lc_claim,
        opening,
        push_opening,
        log_inv_rate,
    })
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// BLAKE3 value columns are virtual — they have no committed placement. A
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_pkd` slot evaluation: an ordinary claim on the committed
/// `QPKD` column at the point freezing the low 8 coords to the slot's bits and
/// the high coords to `r`. No downstream special-casing — it folds into the
/// one opening like every other point claim.
fn slot_claims(l: &Layout, claims: &[ColumnClaim]) -> Vec<pcs::SlotClaim> {
    claims
        .iter()
        .map(|c| {
            // A virtual BLAKE3 value column: its lookup-source claim at
            // instance point `c.point` is the q_pkd slot value — a boolean-selector
            // (strided) claim on QPKD, folded sparsely (2^n_log, not the 2^(8+n_log)
            // dense QPKD block).
            if let Some(slot) = blake3_value_slot(c.col) {
                return pcs::SlotClaim::Strided {
                    offset: l.placements[QPKD].offset + (c.start << crate::blake3_flock::SLOT_STRIDE_LOG),
                    slot,
                    stride_log: crate::blake3_flock::SLOT_STRIDE_LOG,
                    point: c.point.clone(),
                    value: c.value,
                };
            }
            pcs::SlotClaim::Point {
                offset: l.placements[c.col].offset + c.start,
                low_point: c.point.clone(),
                value: c.value,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A K-embedded immediate (both extension limbs zero).
    fn w(x: u64) -> F192 {
        F192::new(x, 0, 0)
    }

    #[test]
    fn access_value_columns_are_absent_from_the_pcs() {
        let virtual_values = lookup_value_columns();
        let sources = col_kappa_sources(3);
        assert!(virtual_values.iter().filter(|&&v| v).count() > 40);
        for (col, &is_value) in virtual_values.iter().enumerate() {
            if is_value {
                assert!(
                    sources[col].is_none(),
                    "access value column {col} was assigned a PCS region"
                );
            }
        }
        assert!(sources[MEM_LO].is_some() && sources[MEM_HI].is_some() && sources[MEM_TOP].is_some());
        assert!(sources[QPKD].is_some());
    }

    /// Pack two 64-bit flock words into the canonical BLAKE3 subspace of F192.
    fn cell(lo: F64, hi: F64) -> F192 {
        F192::new(lo.0, hi.0, 0)
    }

    /// A hand-built straight-line program with one BLAKE3 row: set up the two
    /// 256-bit inputs (`a` at cells 2,3, `b` at cells 4,5 — one 128-bit word per
    /// cell), hash them into the output `c` (cells 6,7), pad with filler SETs so
    /// the last executed instruction lands one before the sentinel, and halt
    /// there. The flock validity sub-proof, memory/bytecode lookups, and state bus
    /// are verified end-to-end (the proof carries the Ligerito
    /// opening they assert on).
    fn blake3_program(a: [F64; 4], b: [F64; 4]) -> Program {
        // a → cells 2,3 and b → cells 4,5 (two flock lanes per BLAKE3 cell).
        let mut prog = vec![
            Op::Set {
                o: 2,
                k: cell(a[0], a[1]),
            },
            Op::Set {
                o: 3,
                k: cell(a[2], a[3]),
            },
            Op::Set {
                o: 4,
                k: cell(b[0], b[1]),
            },
            Op::Set {
                o: 5,
                k: cell(b[2], b[3]),
            },
            Op::Blake3 {
                ins: [2, 3, 4, 5],
                out: 6,
            },
        ]; // c → cells 6,7
        // 16 slots: 5 executed so far; 10 filler SETs step the pc to 15 (halt);
        // slot 15 is the never-executed sentinel.
        for k in 0..10u32 {
            prog.push(Op::Set {
                o: 16 + k,
                k: F192::ONE,
            });
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel (never executed)
        assert_eq!(prog.len(), 16);
        Program::from_bytecode(prog, 32)
    }

    #[test]
    fn blake3_proves_and_verifies() {
        let a: [F64; 4] = [
            F64(0x0123_4567_89ab_cdef),
            F64(0xfedc_ba98_7654_3210),
            F64(0x1111_2222_3333_4444),
            F64(0x5555_6666_7777_8888),
        ];
        let b: [F64; 4] = [
            F64(0xdead_beef_cafe_babe),
            F64(0x0badf00d_0badf00d),
            F64(0x9999_aaaa_bbbb_cccc),
            F64(0xdddd_eeee_ffff_0000),
        ];
        let program = blake3_program(a, b);

        let pi = [w(7), w(11)];
        let exec = program.execute(pi);

        // The output cells hold the digest of the two inputs (two 128-bit words).
        let d = blake3_compress(a, b);
        assert_eq!(exec.mem[6], cell(d[0], d[1]));
        assert_eq!(exec.mem[7], cell(d[2], d[3]));
        assert_eq!(exec.trace.blake3.len(), 1);

        let (proof, stats) = prove(&program, pi, pcs::LOG_INV_RATE);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        // flock's sub-proof rides the shared channels: its Ligerito is the proof's
        // one opening, its scalar reduction trails the `stream`.
        assert!(!proof.openings.is_empty(), "BLAKE3 program carries a Ligerito opening");
        verify(&program, &pi, &proof).expect("BLAKE3 program verifies");
    }

    /// BLAKE consumes the `(c0,c1,0)` embedding. This is not an extra AIR
    /// constraint: the full three-limb memory lookup makes a request carrying a
    /// literal zero in limb 2 match only such a stored word.
    #[test]
    #[should_panic(expected = "BLAKE3 input cell must be a canonical 128-bit embedding")]
    fn blake3_requires_zero_third_limb() {
        let mut program = blake3_program([F64::ZERO; 4], [F64::ZERO; 4]);
        program.prog[0] = Op::Set {
            o: 2,
            k: F192::new(0, 0, 1),
        };
        let _ = program.execute([w(7), w(11)]);
    }

    /// A self-hash `BLAKE3(h, h)` (the hash-chain step) passes the *same* input
    /// chunks as both `a` and `b` (`ins[0..2] == ins[2..4]`), so one 256-bit quad
    /// feeds both inputs with no copy. The row reads those cells twice; the
    /// logup* naturally permits those repeated indexed accesses. This is the
    /// aliasing the DSL's hash-chain lowering relies on.
    #[test]
    fn blake3_self_hash_aliased_operands() {
        let h: [F64; 4] = [
            F64(0xfeed_face_dead_beef),
            F64(0x0123_4567_89ab_cdef),
            F64(0xcafe_d00d_1337_c0de),
            F64(0x8877_6655_4433_2211),
        ];
        // 8 slots: 2 SETs (h at cells 2,3), the aliased BLAKE3 (output 4,5),
        // 2 filler SETs stepping the pc to 7 (the sentinel, halt).
        let mut prog = Vec::new();
        prog.push(Op::Set {
            o: 2,
            k: cell(h[0], h[1]),
        });
        prog.push(Op::Set {
            o: 3,
            k: cell(h[2], h[3]),
        });
        prog.push(Op::Blake3 {
            ins: [2, 3, 2, 3],
            out: 4,
        }); // a == b: hash h ‖ h into cells 4,5
        for k in 0..4u32 {
            prog.push(Op::Set {
                o: 12 + k,
                k: F192::ONE,
            }); // fillers step pc to the sentinel
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 8);
        let program = Program::from_bytecode(prog, 16);
        let pi = [w(3), w(5)];

        let exec = program.execute(pi);
        let d = blake3_compress(h, h);
        assert_eq!(exec.mem[4], cell(d[0], d[1]));
        assert_eq!(exec.mem[5], cell(d[2], d[3]));

        let (proof, stats) = prove(&program, pi, pcs::LOG_INV_RATE);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        verify(&program, &pi, &proof).expect("self-hash BLAKE3 verifies");
    }

    /// Tampering flock's validity sub-proof (its Ligerito, opened over the same
    /// stacked commitment) must make verification fail.
    #[test]
    fn blake3_rejects_tampered_validity() {
        let program = blake3_program(
            [F64(0xABCD), F64(0x1234), F64(0x5678), F64(0x9999)],
            [F64(0x1111), F64(0x2222), F64(0x3333), F64(0x4444)],
        );
        let pi = [w(7), w(11)];
        let (mut proof, _) = prove(&program, pi, pcs::LOG_INV_RATE);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // The ordinary-witness opening is first; tamper its sumcheck transcript.
        let lig = proof.openings.first_mut().expect("ordinary stacked Ligerito opening");
        lig.ligerito.sumcheck_transcript[0].u_0 += F192::ONE;
        assert!(
            verify(&program, &pi, &proof).is_err(),
            "tampered BLAKE3 validity proof must be rejected"
        );
    }

    /// flock's REDUCTION sub-proof (zerocheck / lincheck / ring-switch) rides the
    /// `stream` as raw transport, but its VALUES still re-enter the sponge through
    /// the verifier's reduction/opening replay — so tampering a transport word
    /// diverges the recovered `(ab, c)` claims (or breaks decoding) and
    /// verification must reject. (Complements `blake3_rejects_tampered_validity`,
    /// which tampers the Ligerito opening.)
    #[test]
    fn blake3_rejects_tampered_reduction() {
        let program = blake3_program(
            [F64(0xABCD), F64(0x1234), F64(0x5678), F64(0x9999)],
            [F64(0x1111), F64(0x2222), F64(0x3333), F64(0x4444)],
        );
        let pi = [w(7), w(11)];
        let (proof, _) = prove(&program, pi, pcs::LOG_INV_RATE);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // The reduction is serialized onto the stream tail (after the last bound
        // scalar). Flip a full transport word there — the second-to-last word is
        // always meaningful bytes (only the final word may be zero-padded).
        let mut tampered = proof.clone();
        let n = tampered.stream.len();
        tampered.stream[n - 2] += F192::ONE;
        assert!(
            verify(&program, &pi, &tampered).is_err(),
            "tampered reduction transport must be rejected"
        );
    }

    /// A program with no BLAKE3 instructions still proves and verifies through the
    /// unified path: `q_pkd` carries a single padding instance and the flock
    /// sub-proof (over that padding) rides the shared channels like any BLAKE3
    /// program — there is no separate no-BLAKE3 code path.
    #[test]
    fn non_blake3_program_verifies() {
        let prog = vec![
            Op::Set { o: 2, k: w(5) },
            Op::Set { o: 3, k: w(6) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [F192::new(1, 2, 3), F192::new(4, 5, 6)];
        let (proof, stats) = prove(&program, pi, pcs::LOG_INV_RATE);
        assert_eq!(stats.counts[5], 0, "no real BLAKE3 rows");
        // The ordinary witness and the logup* pushforwards are opened separately.
        assert_eq!(proof.openings.len(), 2, "one opening per PCS commitment");
        verify(&program, &pi, &proof).expect("non-BLAKE3 program verifies");
    }

    #[test]
    fn rejects_tampered_pushforward_opening() {
        let prog = vec![
            Op::Set { o: 2, k: w(5) },
            Op::Set { o: 3, k: w(6) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 },
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [F192::new(1, 2, 3), F192::new(4, 5, 6)];
        let (mut proof, _) = prove(&program, pi, pcs::LOG_INV_RATE);
        proof.openings[1].ligerito.sumcheck_transcript[0].u_0 += F192::ONE;
        assert!(
            verify(&program, &pi, &proof).is_err(),
            "tampered pushforward PCS opening must be rejected"
        );
    }

    /// A 192-bit-word MUL: the E-product of two full machine words is proven and
    /// verified. Exercises the tower-product constraint (all limbs nonzero).
    #[test]
    fn mul_192bit_word() {
        let x = F192::new(0x0123_4567_89ab_cdef, 0xfeed_face_dead_beef, 0x1111_2222_3333_4444);
        let y = F192::new(0x9999_aaaa_bbbb_cccc, 0x1357_9bdf_2468_ace0, 0x5555_6666_7777_8888);
        let prog = vec![
            Op::Set { o: 2, k: x },
            Op::Set { o: 3, k: y },
            Op::Mul { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [w(1), w(2)];
        let exec = program.execute(pi);
        assert_eq!(exec.mem[4], x * y, "MUL computes the E product");
        let (proof, _) = prove(&program, pi, pcs::LOG_INV_RATE);
        verify(&program, &pi, &proof).expect("192-bit MUL verifies");
    }

    /// A proof is bound to its exact program: presenting it against a *different*
    /// program (same sizes/layout, one instruction constant changed) must be
    /// rejected — the program digest seeds the transcript, so a modified program
    /// diverges the sponge from the first squeeze. Guards the adaptive-statement
    /// forgery the bytecode-bus single-point MLE check does not, on its own, prevent.
    #[test]
    fn proof_bound_to_program() {
        let prog = vec![
            Op::Set { o: 2, k: w(5) },
            Op::Set { o: 3, k: w(6) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog.clone(), 5);
        let pi = [w(1), w(2)];
        let (proof, _) = prove(&program, pi, pcs::LOG_INV_RATE);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // Same shape (4 ops, same opcodes/operands, so identical layout + announced
        // sizes) but only the SET constant's third limb changed. Must be rejected.
        let mut prog2 = prog;
        prog2[0] = Op::Set {
            o: 2,
            k: F192::new(5, 0, 1),
        };
        let program2 = Program::from_bytecode(prog2, 5);
        assert!(
            verify(&program2, &pi, &proof).is_err(),
            "a proof must not verify against a different program"
        );
    }

    /// Out-of-process verification: a BLAKE3 proof (whose flock sub-proof rides
    /// the shared `stream` + `openings`, no side field) serializes to bytes,
    /// deserializes on the other side, and verifies — everything travels in the two
    /// channels, nothing out of band. A flipped encoded byte must not verify.
    #[test]
    fn proof_roundtrips_through_bytes_and_verifies() {
        let program = blake3_program(
            [F64(0xABCD), F64(0x1234), F64(0x5678), F64(0x9999)],
            [F64(0x1111), F64(0x2222), F64(0x3333), F64(0x4444)],
        );
        let pi = [w(7), w(11)];
        let (proof, _) = prove(&program, pi, pcs::LOG_INV_RATE);

        let bytes = bincode::serialize(&proof).expect("proof serializes");
        let decoded: Proof = bincode::deserialize(&bytes).expect("proof deserializes");
        verify(&program, &pi, &decoded).expect("deserialized BLAKE3 proof verifies");

        let mut bad_rate = decoded.clone();
        bad_rate.stream[1 + tables::N_TABLES] = F192::new(5, 0, 0);
        assert!(
            matches!(verify(&program, &pi, &bad_rate), Err(Error::PublicInput)),
            "the transcript-announced PCS rate must be in 1..=4"
        );

        let mut tampered = bytes.clone();
        let i = tampered.len() / 2;
        tampered[i] ^= 0x01;
        if let Ok(bad) = bincode::deserialize::<Proof>(&tampered) {
            assert!(
                verify(&program, &pi, &bad).is_err(),
                "a corrupted encoded proof must not verify"
            );
        }
    }
}
