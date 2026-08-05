//! Whole-program assembly over GF(2^64) (`doc/main.tex`): the instruction tables
//! sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free. Addresses, the program counter, and read
//! counts are g-powers, so every increment is a free ×g. Machine-word arithmetic
//! is over `E = F192 = K[y]/(y³+y+1)` (XOR degree 1, MUL_NATIVE degree 2),
//! with each word carried by three committed `K = F64` limbs. `BLAKE3`
//! adds the memory/state/bytecode plumbing for a 64→32-byte compression
//! whose relation is discharged by flock (see [`crate::blake3_flock`]). All
//! Challenges and transcript scalars live in the same tower E.

use std::collections::HashMap;

use crate::constraints;
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_BLAKE3, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM, SEP_STATE,
};
use crate::transcript::{ProverState, VerifierState};
use crate::witness;
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

/// Witness-gen `BLAKE3` compression: the four message cells' eight
/// words are laid out little-endian into 64 bytes, combined with the supplied
/// chaining value and metadata, and the 32-byte result is split back into the
/// four output words `c`. Flock proves this same compression relation
/// ([`crate::blake3_flock`]).
fn blake3_compress(va: [F64; 4], vb: [F64; 4], vcv: [F64; 4], metadata: F192) -> [F64; 4] {
    crate::blake3_flock::digest(&crate::blake3_flock::compression(va, vb, vcv, metadata))
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
/// cap these are the instance caps from “Counts must not wrap” in `doc/body/06-memory-and-bytecode-lookups.tex`: at `ord(g) = 2^64−1`
/// the memory-soundness and count-non-wrap counting arguments are theorems only
/// for instances whose total read-flush count stays far below `2^64`, so the
/// verifier rejects any announcement exceeding them before running a reduction.
const MAX_LOG_ROWS: usize = 32;

/// Bytecode-length instance cap (see [`MAX_LOG_ROWS`]): programs are at most
/// `2^32` instructions.
const MAX_LOG_BYTECODE: usize = 32;

/// A binding digest of the program bytecode (BLAKE3 of every instruction's
/// canonical encoding: opcode, operands, and the DEREF store-mode), as two field
/// elements. Seeded into the transcript alongside the public input, so EVERY
/// challenge depends on the exact program.
///
/// Without this the program's instruction content would enter verification only
/// through the bytecode bus's `Public`-coordinate MLE evaluation at the GKR point
/// `ζ`, a single point an attacker recovers from a finished proof. It could then
/// craft a different program `P'` agreeing with `P`'s bytecode columns at that one
/// `ζ` and re-present the same proof for `P'` (adaptive-statement forgery). Seeding
/// `H(program)` before any challenge makes the whole statement (program, public
/// input) bound up front, so a different program yields a different sponge from
/// the very first squeeze. Both sides hold the program, so both compute this
/// identically; the announced sizes ride the stream (`announce_public`).
fn program_digest(prog: &[Op]) -> [F64; 4] {
    // VM-native: encode the program as a field-element slice and hash its exact
    // little-endian bytes with standard BLAKE3 ([`crate::vmhash::hash_slice`]).
    let mut words: Vec<F64> = Vec::with_capacity(7 * prog.len() + 2);
    // Domain/version marker; standard BLAKE3 binds the total byte length.
    words.push(F64(prog.len() as u64));
    words.push(F64(3));
    for op in prog {
        // Fixed seven-word encoding per instruction: two operand-offset words
        // packed with the tag, the 192-bit immediate's three lanes, then two
        // words for BLAKE3's remaining offsets (zero for other opcodes).
        let (tag, a, b, c, k, x, y) = match *op {
            Op::Xor { a, b, c } => (0u8, a, b, c, F192::ZERO, 0u64, 0u64),
            Op::Mul { a, b, c } => (1, a, b, c, F192::ZERO, 0, 0),
            Op::Set { o, k } => (2, o, 0, 0, k, 0, 0),
            Op::Deref {
                alpha,
                beta,
                gamma,
                mode,
            } => {
                (3 + mode as u8, alpha, beta, gamma, F192::ZERO, 0, 0) // mode ∈ {Cell,Pc,Fp} ⇒ tag 3/4/5
            }
            Op::Jump { oc, od, of } => (6, oc, od, of, F192::ZERO, 0, 0),
            Op::Blake3 { ins, cv, out, metadata } => (
                7,
                ins[0],
                ins[1],
                ins[2],
                metadata,
                ins[3] as u64 | ((cv as u64) << 32),
                out as u64,
            ),
            Op::Pack64x2 { a, b, c } => (9, a, b, c, F192::ZERO, 0, 0),
        };
        words.push(F64(a as u64 | ((b as u64) << 32)));
        words.push(F64(c as u64 | ((tag as u64) << 32)));
        words.push(F64(k.c0));
        words.push(F64(k.c1));
        words.push(F64(k.c2));
        words.push(F64(x));
        words.push(F64(y));
    }
    crate::vmhash::hash_slice(&words)
}

/// The Fiat-Shamir seed: ONE 32-byte digest, as two field words, committing
/// to everything fixed about the proving environment: the flock circuit
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
/// not announced here; it seeds the transcript at construction (see
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
    let read_size = |vs: &mut VerifierState| -> Result<usize, Error> {
        let word = vs.next_scalar().map_err(Error::Transcript)?;
        if word.c1 != 0 || word.c2 != 0 {
            return Err(Error::PublicInput);
        }
        usize::try_from(word.c0).map_err(|_| Error::PublicInput)
    };

    let log_mem = read_size(vs)?;
    let mut row_counts = [0usize; tables::N_TABLES];
    for r in &mut row_counts {
        *r = read_size(vs)?;
    }
    let log_inv_rate = read_size(vs)?;
    // The public instance caps ensure that, with `ord(g) = 2^64 − 1`, the
    // counting arguments (memory soundness, count non-wrap, exponent range checks)
    // are theorems only when the announced instance keeps the total read-flush
    // count provably below `2^64 − 1`, so reject any announcement exceeding the
    // caps BEFORE running any reduction. (A table's row count is the number of
    // times its opcode runs, unbounded by the bytecode size since a small loop
    // body runs many times, so it gets its own cap, not `bytecode_size`.)
    let bytecode_size = prog.prog.len();
    if !bytecode_size.is_power_of_two()
        || bytecode_size > (1usize << MAX_LOG_BYTECODE)
        || !(MIN_LOG_MEM..=MAX_LOG_MEM).contains(&log_mem)
        || row_counts.iter().any(|&r| r >= (1usize << MAX_LOG_ROWS))
        || ::pcs::whir::validate_log_inv_rate(log_inv_rate).is_err()
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
    /// program. Trusted to match `prog`: always set by [`Program::assemble`] from
    /// the bytecode, so a `Program` value cannot carry a digest inconsistent with
    /// its own `prog`.
    pub(crate) digest: [F64; 4],
    /// Prover-side frame/buffer allocation hints (keyed by global pc) and the
    /// size of `main`'s frame: the nondeterminism [`Program::execute`] needs to
    /// run the program. Public verification (§ `verify`) ignores them.
    pub(crate) hints: HashMap<u32, Vec<hints::RHint>>,
    pub(crate) main_frame: u32,
    /// Named prover witness streams for the program's `hint_witness` calls
    /// ([`Program::set_witness`]): a stream is a sequence of *entries* (one
    /// slice of values per `hint_witness` call; the same symbol may be
    /// hinted many times); each call pops the next entry, whose length must
    /// match its destination. Prover-side only; verification ignores them.
    pub(crate) witness: HashMap<String, Vec<Vec<F192>>>,
    /// Function pc-ranges `(name, entry, len)` from the compiler, for the
    /// `DBG_PROF=1` per-function cycle profile ([`Program::execute`]). Purely
    /// diagnostic; empty for hand-assembled programs.
    pub fn_ranges: Vec<(String, u32, u32)>,
}

impl Program {
    /// Assemble a [`Program`], computing its bytecode digest
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

    /// Assemble a program directly from a fixed bytecode vector, starting at
    /// `(pc, fp) = (0, 0)` with no allocation hints. Suitable for straight-line
    /// programs that never change the frame pointer and touch only the first
    /// `main_frame` memory cells (so the prover needs no nondeterministic frame
    /// allocation). `prog.len()` must be a power of two with a never-executed
    /// sentinel in its last slot: the run halts on reaching `g^{len-1}` (§sec:state).
    #[cfg(test)]
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
    Constraint(constraints::Error),
    Open(pcs::Error),
    PublicInput,
    Transcript(crate::transcript::Error),
    /// flock's BLAKE3 R1CS validity sub-proof failed to verify. (A missing or
    /// malformed sub-proof surfaces as [`Error::Transcript`] when the shared
    /// `stream`/`openings` fail to reconstruct or fully consume.)
    Blake3(flock::verifier::VerifyError),
}

/// Per side, which table (if any) owns each bus block, as `(table, column base)`.
type BlockOwners = [Vec<Option<(usize, usize)>>; 3];
/// Each table's `(column base, committed column count)` in the global schema.
type TableSpans = Vec<(usize, usize)>;

/// Blocks sourced from a table's height belong to it; the boundary, memory and
/// bytecode blocks belong to none and keep their own column claims at ζ.
fn block_owners(log_bytecode: usize, sides: [usize; 3]) -> BlockOwners {
    let sch = schema();
    let src = block_kappa_sources(log_bytecode);
    let mut it = src
        .into_iter()
        .map(|(source, _)| source.checked_sub(2).map(|t| (t, sch.base[t])));
    sides.map(|n| it.by_ref().take(n).collect())
}

/// The bus's public wiring: per side which table owns each block, and each table's
/// column span. Derived from the program and the announced layout alone, so prover
/// and verifier build it identically.
fn bus_wiring(program: &Program, l: &Layout) -> (BlockOwners, TableSpans) {
    let owners = block_owners(
        crate::log2_strict_usize(program.prog.len()),
        [l.push.len(), l.pull.len(), l.count.len()],
    );
    (owners, table_spans())
}

/// The batched zerocheck carries every committed column of a table, because its bus
/// forms reference the flushed ones and its constraint the rest.
fn table_spans() -> TableSpans {
    let sch = schema();
    tables::tables()
        .iter()
        .enumerate()
        .map(|(t, tb)| (sch.base[t], tb.n_committed_columns()))
        .collect()
}

/// The per-table inputs to the batched zerocheck (§constraints), in schema order.
/// Prover and verifier both call this, so their column order and constraint
/// closures agree by construction.
/// The airs carry every committed column of their table, so a constraint indexes the
/// value array directly and each table's three bus forms can be
/// evaluated on the same values. The identities take the air's own `η`-range; the
/// three forms take the shared powers at [`eta_form_base`].
fn airs<'a>(
    taus: &[usize; tables::N_TABLES],
    forms: &'a [Vec<leaf::BusForm>; 3],
    form_pows: [F192; 3],
) -> Vec<constraints::Air<'a>> {
    tables::tables()
        .iter()
        .zip(taus)
        .enumerate()
        .map(|(t, (&table, &tau))| {
            let bus: Vec<&leaf::BusForm> = (0..3).map(|s| &forms[s][t]).collect();
            let bus_k = bus.clone();
            constraints::Air {
                tau,
                n_cols: table.n_committed_columns(),
                n_constraints: table.n_constraints(),
                eval: Box::new(move |p, vals| {
                    let air = table.eval_constraint(p, vals);
                    bus.iter()
                        .zip(form_pows)
                        .fold(air, |acc, (form, w)| acc + w * form.eval(vals))
                }),
                // The same expression over K columns: the identity's K-only products
                // stay 64-bit and each bus form becomes a mixed dot product.
                eval_k: Box::new(move |p, vals| {
                    let air = table.eval_constraint_k(p, vals);
                    bus_k
                        .iter()
                        .zip(form_pows)
                        .fold(air, |acc, (form, w)| acc + w * form.eval(vals))
                }),
            }
        })
        .collect()
}

/// Each table's claimed sum: its identities vanish, so what its summand comes to
/// is its three bus forms, `η`-weighted. Prover-side only, to build the waiting
/// line each round; the verifier needs just their total, which it derives.
fn sigmas(bus: &[Vec<F192>; 3], form_pows: [F192; 3]) -> Vec<F192> {
    (0..tables::tables().len())
        .map(|t| (0..3).fold(F192::ZERO, |acc, s| acc + form_pows[s] * bus[s][t]))
        .collect()
}

/// Where the three bus forms sit in the batch's `η`-powers: the last three, AFTER
/// every table's identity range, and shared by all tables rather than one triple
/// per table. That sharing is what keeps the batch tied to the bus: with a common
/// `η^{base+s}` per side, the batch's target is `Σ_s η^{FORM_POWS+s}·R_s` for
/// the sides' table shares `R_s`, which the verifier DERIVES from the leaf claims
/// (`eta_form_pows`; a mismatch surfaces as [`Error::Constraint`]). Were the
/// powers per table, the target
/// would not factor through the `R_s` and nothing would pin the tables' share of
/// the bus.
pub fn eta_form_base() -> usize {
    tables::tables().iter().map(|t| t.n_constraints()).sum()
}

/// The three shared form powers `η^{base}, η^{base+1}, η^{base+2}`.
fn eta_form_pows(eta: F192) -> [F192; 3] {
    let base = eta_form_base();
    let pows = primitives::field::powers(eta, base + 3);
    [pows[base], pows[base + 1], pows[base + 2]]
}

/// Lift each table's zerocheck evals (at its point `rho`) to global column claims.
/// The batch carries every committed column of a table, so eval `c` is local
/// column `c`; these are the ONLY claims those columns raise, the bus having been
/// settled inside the batch.
fn constraint_claims(table_claims: &[constraints::Claims]) -> Vec<ColumnClaim> {
    let sch = schema();
    let mut v = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        for c in 0..table.n_committed_columns() {
            v.push(ColumnClaim {
                col: sch.base[t] + c,
                point: table_claims[t].rho.clone(),
                value: table_claims[t].evals[c],
            });
        }
    }
    v
}

/// If `col` is a BLAKE3 **value** column (global index), its `q_flock` packed slot.
/// These columns are virtual (uncommitted): their memory-bus evaluation claims
/// are re-routed to `q_flock` slot evaluations, which is the whole binding: the
/// bus-tied value IS the proven `q_flock` word, no separate check needed.
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
/// committed witness size, the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize,
    pub counts: [usize; tables::N_TABLES],
    pub committed: usize,
    /// Data memory is `2^log_mem` cells (the padded write-once image).
    pub log_mem: usize,
    /// Cells actually touched, before the pad to `2^log_mem`, i.e. the real memory
    /// footprint (`log2` is fractional).
    pub mem_used: usize,
}

impl Stats {
    /// Table names in `counts` order.
    pub const TABLES: [&'static str; tables::N_TABLES] = ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3", "PACK64X2"];

    /// One line of run sizes, every one a power of two: the per-table instruction
    /// counts with their share of the run, largest first, then the data memory and
    /// the committed witness. Reads as
    /// `"DEREF 2^18.838 (33.6%)  SET 2^18.265 (22.6%)  …  MEMORY 2^21.701  TOTAL_COMMITTED 2^26.364"`.
    ///
    /// The per-table counts sum to `cycles`, so the percentages are shares of the
    /// whole run. Every exponent is an actual count, never a padded one, so the
    /// figures are directly comparable; `log_mem` holds the padded memory size the
    /// commitment covers. Zero-count tables are omitted.
    #[must_use]
    pub fn details(&self) -> String {
        if self.cycles == 0 {
            return "-".to_string();
        }
        let mut shares: Vec<(&str, usize)> = Self::TABLES
            .iter()
            .zip(&self.counts)
            .filter(|&(_, &c)| c > 0)
            .map(|(&name, &c)| (name, c))
            .collect();
        shares.sort_unstable_by_key(|&(_, c)| std::cmp::Reverse(c));
        let mut parts: Vec<String> = shares
            .iter()
            .map(|&(name, c)| {
                let pct = 100.0 * c as f64 / self.cycles as f64;
                format!("{name} 2^{} ({pct:.1}%)", primitives::pretty_f64((c as f64).log2()))
            })
            .collect();
        let log2 = |n: usize| primitives::pretty_f64((n.max(1) as f64).log2());
        parts.push(format!("MEMORY 2^{}", log2(self.mem_used)));
        parts.push(format!("TOTAL_COMMITTED 2^{}", log2(self.committed)));
        parts.join("  ")
    }
}

/// Prove the program on the given public input: run it (witness generation),
/// then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof and the
/// run [`Stats`]. `log_inv_rate` selects the PCS rate and is announced in the
/// Fiat-Shamir transcript before the commitment.
#[tracing::instrument(name = "Prove", skip_all, fields(log_inv_rate))]
pub fn prove(program: &Program, public_input: [F192; 2], log_inv_rate: usize) -> (Proof, Stats) {
    ::pcs::whir::validate_log_inv_rate(log_inv_rate).expect("valid log_inv_rate");
    // One proof is one arena phase: every transient buffer below is bump-allocated
    // and reclaimed wholesale here, rather than faulted in and unmapped again per
    // proof. Bound first so it outlives them; inert unless `init_prover` opted in.
    // The returned `Proof` is system-allocated (`ps.into_proof()` builds `Vec`s),
    // so it survives the next phase.
    let _phase = zk_alloc::enter_phase();
    let exec = crate::stage!("Execute program", || program.execute(public_input));
    // The BLAKE3 R1CS setup (circuit construction) is a ~hundreds-of-ms cost that
    // depends only on the compression count (the circuit *shape*), not the witness,
    // but it is otherwise built synchronously inside the final reduction, adding
    // that latency serially with nothing overlapping it. Now that `execute` has
    // told us the count, build it on a background thread: it constructs
    // concurrently with the build/commit/bus/constraint stages (~1 s of work) and
    // lands in the shared setup cache, so the reduction's `setup_for` is a cache
    // hit. Pure warm-up: the result is fetched from the cache, nothing here joins
    // the handle. (A no-BLAKE3 program still warms the size-1 padding shape.)
    let n_b3_warm = exec.trace.blake3.len().max(1);
    std::thread::spawn(move || crate::blake3_flock::warm_setup(n_b3_warm));
    let cycles = exec.cycles;
    let mut w = crate::stage!("Build witness", || program.build(&exec));
    let counts = w.layout.row_counts;
    let committed_size = w.committed_size();
    // The public statement (program digest + input) seeds the transcript, so
    // every challenge depends on the exact program and public input.
    let mut ps = ProverState::new(b"leanvm-b", &transcript_seed(program, &public_input));

    // Announce the prover's sizes, then commit, before sampling any challenge.
    announce_public(&mut ps, w.log_mem, w.layout.row_counts, log_inv_rate);
    let committed = crate::stage!("Commit", || { pcs::commit(&mut ps, &w.q, log_inv_rate) });

    // BLAKE3 to flock (§blake3_flock), single PCS: q_flock is ALWAYS a column in
    // `w.q` (≥1 instance, a program with no BLAKE3 carries one padding instance,
    // so the proof shape is uniform and there is no has/hasn't-BLAKE3 fork). flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE
    // WHIR over this commitment (below). The input/output words bind via the
    // memory bus (virtual value columns route to q_flock); the constant pins reuse a
    // bus point, so no dedicated binding challenge is drawn. Mirrored in `verify`.
    let (owners, spans) = bus_wiring(program, &w.layout);
    // The columns are windows into `w.q`, so both stages read them in place: the
    // batched zerocheck lifts each K-column into a fresh `E` copy on the round it
    // joins and never writes the K-columns back.
    let (bus, table_claims) = {
        let l = &w.layout;
        let cols = w.columns();
        let bus = crate::stage!("Prove bus", || {
            leaf::prove_balance(&l.push, &l.pull, &l.count, &cols, &owners, &spans, &mut ps)
        });
        let table_claims = crate::stage!("Prove constraints", || {
            // One sumcheck for all seven tables (§constraints).
            let table_cols: Vec<Vec<&[F64]>> = spans
                .iter()
                .map(|&(base, n)| (0..n).map(|c| cols[base + c]).collect())
                .collect();
            // The eq point is the bus GKR's ζ, not a fresh one: that is what lets the
            // batch settle the bus forms alongside the constraints.
            let eta = ps.sample();
            let form_pows = eta_form_pows(eta);
            let sigma = sigmas(&bus.sigmas, form_pows);
            constraints::prove(
                &airs(&l.taus, &bus.forms, form_pows),
                &table_cols,
                eta,
                &bus.point,
                &sigma,
                &mut ps,
            )
        });
        (bus, table_claims)
    };
    let l = &w.layout;

    // The PI binding transmits the low/high memory-limb evaluations. The full
    // F192 public-input interpolation then determines the top-limb evaluation.
    let r_pi = ps.sample();
    let pi_lo = primitives::multilinear::interp_k(F64(l.pi[0].c0), F64(l.pi[1].c0), r_pi);
    let pi_hi = primitives::multilinear::interp_k(F64(l.pi[0].c1), F64(l.pi[1].c1), r_pi);
    ps.add_scalar(pi_lo);
    ps.add_scalar(pi_hi);
    // The input/output words bind via the memory bus (value columns are virtual and
    // route to q_flock, see `slot_claims`); cv/counter/blen/flags are constants baked
    // into flock's per-block matrices, so no pin claims are needed.
    let slots = finish_claims(l, bus.claims, &table_claims, r_pi, pi_lo, pi_hi);

    // Run flock's reduction (zerocheck + lincheck) over the prepared native
    // layouts retained from the fused q_flock build pass; it returns the `(ab, c)`
    // validity claims on the committed `q_flock`, discharged by the PCS below in the
    // SAME WHIR as every leanVM point claim (the point claims become the
    // opener's `point_claims`).
    let flock_reduction = w
        .flock_reduction
        .take()
        .expect("prepared flock reduction witness is present");
    let reduced = crate::stage!("Flock reduction", || { flock_reduction.prove(&mut ps) });
    let n_blocks = flock_reduction.n_blocks();
    drop(flock_reduction);
    let offset = w.layout.placements[QFLOCK].offset;
    let ring = crate::blake3_flock::ring_switch_open(n_blocks, offset, &reduced);
    let mixed_open = crate::stage!("PCS open", || { pcs::open(&mut ps, &committed, &w.q, &slots, &ring) });
    // flock's scalar sub-proof already rode the shared stream (add_scalar at its
    // protocol points); only the Merkle-bearing stacked opening needs the hint
    // channel.
    ps.hint_opening(mixed_open);
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

/// Everything the PCS has to open, in the ORDER that feeds the batch's weights:
/// the bus's framework claims, then the zerocheck's per-table column claims, then
/// the three public-input limb claims, each located in its committed slot. Both
/// sides assemble it here, so a claim can never shift by one element.
fn finish_claims(
    l: &Layout,
    bus_claims: Vec<ColumnClaim>,
    table_claims: &[constraints::Claims],
    r_pi: F192,
    pi_lo: F192,
    pi_hi: F192,
) -> Vec<pcs::SlotClaim> {
    let mut claims = bus_claims;
    claims.extend(constraint_claims(table_claims));
    claims.extend(bind_pi_claim(r_pi, &l.placements, &l.pi, pi_lo, pi_hi));
    slot_claims(l, &claims)
}

/// The public-input binding (§sec:e2e-pi): the committed `MEM` at `(r, 0,…,0)` must equal
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
            point: point.clone(),
            value: v_lo,
        },
        ColumnClaim {
            col: MEM_HI,
            point: point.clone(),
            value: v_hi,
        },
        ColumnClaim {
            col: MEM_TOP,
            point,
            value: v_top,
        },
    ]
}

/// Everything a recursion harness needs from an accepting verify run, named
/// and typed: the deferred bytecode claims, the count-channel root, flock's
/// reduction claims, and the stacked-opening summary (ring-switch challenges +
/// WHIR fold/query data). The sub-proof scalars themselves live on
/// `proof.stream` at fixed offsets from its tail. Ordinary callers just
/// `?`-discard it.
pub struct VerifySummary {
    /// Transcript-bound inverse-rate logarithm used by this proof's PCS.
    pub log_inv_rate: usize,
    pub bytecode_claims: Vec<leaf::BytecodeClaim>,
    pub count_root: F192,
    pub zc_claim: flock::zerocheck::ZerocheckClaim,
    pub lc_claim: flock::lincheck::LincheckClaim,
    pub opening: pcs::StackedOpeningSummary,
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs, never the prover's witness.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify(program: &Program, public_input: &[F192; 2], proof: &Proof) -> Result<VerifySummary, Error> {
    let mut vs = VerifierState::new(b"leanvm-b", proof, &transcript_seed(program, public_input));
    let (l, log_inv_rate) = read_public(&mut vs, program, public_input)?;
    let root = pcs::read_commitment(&mut vs).map_err(Error::Transcript)?;

    // BLAKE3 ↔ flock (single PCS): flock's R1CS validity and every leanVM point
    // claim are verified together by ONE WHIR opening at the end. The executed-
    // BLAKE3 count is public (announced); its flock sub-proof rides the shared
    // `stream`/`openings`, and presence is enforced by consumption below plus
    // `vs.finish()` (a proof with `n_b3 = 0` but trailing flock data, or vice versa,
    // fails to fully consume). No dedicated binding challenge: the input/output
    // words bind via the memory bus, the pins reuse a bus point.
    let n_b3 = l.row_counts[tables::BLAKE3_TABLE];

    let (owners, spans) = bus_wiring(program, &l);
    let bus = leaf::verify_balance(&l.push, &l.pull, &l.count, &l.pad, &owners, &spans, &mut vs).map_err(Error::Bus)?;

    let zc_eta = vs.sample();
    let form_pows = eta_form_pows(zc_eta);
    // THE tie between the batch and the bus, and the reason the batch's target is
    // never transmitted. Each side's leaf claim less what its framework blocks
    // account for is the tables' share `R_s`, which the verifier just derived; the
    // batch must sum to `Σ_s η^{base+s}·R_s`. Since `η` is sampled after the `R_s`
    // are fixed, hitting that one number forces `Σ_t σ_{s,t} = R_s` on all three
    // sides. A transmitted target would be a free value in its own check, and the
    // tables' bus blocks would be settled by nothing at all.
    let target = (0..3).fold(F192::ZERO, |a, s| a + form_pows[s] * bus.totals[s]);
    let table_claims = constraints::verify(
        &airs(&l.taus, &bus.forms, form_pows),
        zc_eta,
        &bus.point,
        target,
        &mut vs,
    )
    .map_err(Error::Constraint)?;

    let r_pi = vs.sample();
    let pi_lo = vs.next_scalar().map_err(Error::Transcript)?;
    let pi_hi = vs.next_scalar().map_err(Error::Transcript)?;
    let slots = finish_claims(&l, bus.claims, &table_claims, r_pi, pi_lo, pi_hi);

    // Replay flock's reduction straight off the shared stream (each scalar bound
    // as it is read) to recover its `(ab, c)` validity claims on q_flock, then
    // verify them alongside every point claim in the ONE WHIR opening
    // (mirroring `prove`). `n_blocks = max(n_b3, 1)`, always ≥ 1 instance.
    let n_blocks = n_b3.max(1);
    let offset = l.placements[QFLOCK].offset;
    let replay = crate::blake3_flock::verify_reduction(n_blocks, &mut vs).map_err(Error::Blake3)?;
    let open = vs.next_opening().map_err(Error::Transcript)?;
    let ring = crate::blake3_flock::ring_switch_verify(n_blocks, offset, replay.ab, replay.c);
    let opening = pcs::verify(&mut vs, &slots, &ring, open, l.m, log_inv_rate, &root).map_err(Error::Open)?;
    vs.finish().map_err(Error::Transcript)?;
    Ok(VerifySummary {
        bytecode_claims: bus.bytecode_claims,
        count_root: bus.count_root,
        zc_claim: replay.zc_claim,
        lc_claim: replay.lc_claim,
        opening,
        log_inv_rate,
    })
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// BLAKE3 value columns are virtual: they have no committed placement. A bus
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_flock` slot evaluation: an ordinary claim on the committed
/// `QFLOCK` column at the point freezing the low 8 coords to the slot's bits and
/// the high coords to `r`. No downstream special-casing: it folds into the
/// one opening like every other point claim.
fn slot_claims(l: &Layout, claims: &[ColumnClaim]) -> Vec<pcs::SlotClaim> {
    claims
        .iter()
        .map(|c| {
            // A virtual BLAKE3 value column (always virtual): its bus claim at
            // instance point `c.point` is the q_flock slot value, a boolean-selector
            // (strided) claim on QFLOCK, folded sparsely (2^n_log, not the 2^(8+n_log)
            // dense QFLOCK block).
            if let Some(slot) = blake3_value_slot(c.col) {
                return pcs::SlotClaim::Strided {
                    offset: l.placements[QFLOCK].offset,
                    slot,
                    stride_log: crate::blake3_flock::SLOT_STRIDE_LOG,
                    point: c.point.clone(),
                    value: c.value,
                };
            }
            pcs::SlotClaim::Point {
                offset: l.placements[c.col].offset,
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

    /// Pack two 64-bit flock words into the canonical BLAKE3 subspace of F192.
    fn cell(lo: F64, hi: F64) -> F192 {
        F192::new(lo.0, hi.0, 0)
    }

    /// The default one-block-root metadata for a hand-built BLAKE3 op.
    fn md() -> F192 {
        crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS)
    }

    /// The four chaining-value lanes of the two cv cells.
    fn cv_lanes(cv0: F192, cv1: F192) -> [F64; 4] {
        [F64(cv0.c0), F64(cv0.c1), F64(cv1.c0), F64(cv1.c1)]
    }

    /// A hand-built straight-line program with one BLAKE3 row: set up the two
    /// 256-bit inputs (`a` at cells 2,3, `b` at cells 4,5, one 128-bit word per
    /// cell), hash them into the output `c` (cells 6,7), pad with filler SETs so
    /// the last executed instruction lands one before the sentinel, and halt
    /// there. The flock validity sub-proof plus the memory / state / bytecode bus
    /// interactions are verified end-to-end (the proof carries the WHIR
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
            // The chaining value reads cells 0,1 (the public input); any
            // canonical cv is legal.
            Op::Blake3 {
                ins: [2, 3, 4, 5],
                cv: 0,
                out: 6,
                metadata: crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS),
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

        // The output cells hold the compression of the two inputs under the
        // pi-supplied chaining value (two 128-bit chunks).
        let d = blake3_compress(a, b, cv_lanes(pi[0], pi[1]), md());
        assert_eq!(exec.mem[6], cell(d[0], d[1]));
        assert_eq!(exec.mem[7], cell(d[2], d[3]));
        assert_eq!(exec.trace.blake3.len(), 1);

        let (proof, stats) = prove(&program, pi, pcs::LOG_INV_RATE);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        // flock's sub-proof rides the shared channels: its WHIR is the proof's
        // one opening, its scalar reduction trails the `stream`.
        assert!(!proof.openings.is_empty(), "BLAKE3 program carries a WHIR opening");
        verify(&program, &pi, &proof).expect("BLAKE3 program verifies");
    }

    /// BLAKE consumes the `(c0,c1,0)` embedding. This is not an extra AIR
    /// constraint: the full three-limb memory bus makes a request carrying a
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
    /// running access counts thread through and the bus still balances. This is
    /// the aliasing the DSL's hash-chain lowering relies on.
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
            cv: 0,
            out: 4,
            metadata: crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS),
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
        let d = blake3_compress(h, h, cv_lanes(pi[0], pi[1]), md());
        assert_eq!(exec.mem[4], cell(d[0], d[1]));
        assert_eq!(exec.mem[5], cell(d[2], d[3]));

        let (proof, stats) = prove(&program, pi, pcs::LOG_INV_RATE);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        verify(&program, &pi, &proof).expect("self-hash BLAKE3 verifies");
    }

    /// Tampering flock's validity sub-proof (its WHIR, opened over the same
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

        // The stacked opening is the proof's one hint; tamper a sumcheck
        // round message (the inner-product transcript); must be rejected.
        let lig = proof.openings.last_mut().expect("stacked WHIR opening");
        lig.whir.sumcheck_transcript[0].u_0 += F192::ONE;
        assert!(
            verify(&program, &pi, &proof).is_err(),
            "tampered BLAKE3 validity proof must be rejected"
        );
    }

    /// flock's REDUCTION sub-proof (zerocheck / lincheck / ring-switch) rides the
    /// `stream` as raw transport, but its VALUES still re-enter the sponge through
    /// the verifier's reduction/opening replay, so tampering a transport word
    /// diverges the recovered `(ab, c)` claims (or breaks decoding) and
    /// verification must reject. (Complements `blake3_rejects_tampered_validity`,
    /// which tampers the WHIR opening.)
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
        // scalar). Flip a full transport word there: the second-to-last word is
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
    /// unified path: `q_flock` carries a single padding instance and the flock
    /// sub-proof (over that padding) rides the shared channels like any BLAKE3
    /// program, and there is no separate no-BLAKE3 code path.
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
        // The proof still carries exactly one WHIR opening (over the padding).
        assert_eq!(proof.openings.len(), 1, "unified path: one opening always");
        verify(&program, &pi, &proof).expect("non-BLAKE3 program verifies");
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
    /// rejected: the program digest seeds the transcript, so a modified program
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
    /// deserializes on the other side, and verifies: everything travels in the two
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

        for announcement in 0..=tables::N_TABLES + 1 {
            for high_limb in [F192::new(0, 1, 0), F192::new(0, 0, 1)] {
                let mut malformed = decoded.clone();
                malformed.stream[announcement] += high_limb;
                assert!(
                    matches!(verify(&program, &pi, &malformed), Err(Error::PublicInput)),
                    "announcement {announcement} with a nonzero high limb must be rejected"
                );
            }
        }

        let root_offset = tables::N_TABLES + 2;
        for root_word in root_offset..root_offset + 2 {
            let mut malformed = decoded.clone();
            malformed.stream[root_word].c2 = 1;
            assert!(
                matches!(
                    verify(&program, &pi, &malformed),
                    Err(Error::Transcript(crate::transcript::Error::NonCanonicalEncoding))
                ),
                "commitment root word {} with a nonzero top limb must be rejected",
                root_word - root_offset
            );
        }

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
