//! Whole-program assembly over GF(2^128) (§7, §8): the six instruction tables
//! sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free. Addresses, the program counter, and read
//! counts are g-powers, so every increment is a free ×g; arithmetic is the field's
//! own (XOR = degree-1, MUL_NATIVE = degree-2). `BLAKE3` (§7.6) adds the
//! memory/state/bytecode plumbing for a 64→32-byte compression whose relation is
//! discharged by flock (see [`crate::blake3_flock`]).

use std::collections::HashMap;

use rayon::prelude::*;

use crate::constraints;
use primitives::field::{F128, g_pow};
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_BLAKE3, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM, SEP_STATE,
};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::{self, Column};

mod execute;
pub mod hints;
mod isa;
mod layout;
mod trace;
pub use execute::Execution;
pub use isa::{DerefMode, Op};
pub use layout::*;
pub(crate) use trace::{Brow, Drow, Jrow, Srow, Trace, Xrow};

/// Witness-gen `BLAKE3` compression (doc §7.6): the four message words are laid
/// out little-endian into 64 bytes, combined with the supplied chaining value
/// and metadata, and split back into `c = (vc0, vc1)`. Flock proves this same
/// compression relation ([`crate::blake3_flock`]).
fn blake3_compress(
    va0: F128,
    va1: F128,
    vb0: F128,
    vb1: F128,
    cv0: F128,
    cv1: F128,
    metadata: F128,
) -> (F128, F128) {
    let block = crate::blake3_flock::compression(
        [va0, va1],
        [vb0, vb1],
        [cv0, cv1],
        metadata,
    );
    let [c0, c1] = crate::blake3_flock::digest(&block);
    (c0, c1)
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
/// instructions of that opcode).
const MAX_LOG_ROWS: usize = 32;

/// A binding digest of the program bytecode (BLAKE3 of every instruction's
/// canonical encoding — opcode, operands, and the DEREF store-mode), as two field
/// elements. Seeded into the transcript alongside the public input, so EVERY
/// challenge depends on the exact program.
///
/// Without this the program's instruction content would enter verification only
/// through the bytecode bus's `Public`-coordinate MLE evaluation at the GKR point
/// `ζ` — a single point an attacker recovers from a finished proof. It could then
/// craft a different program `P'` agreeing with `P`'s bytecode columns at that one
/// `ζ` and re-present the same proof for `P'` (adaptive-statement forgery). Seeding
/// `H(program)` before any challenge makes the whole statement — (program, public
/// input) — bound up front, so a different program yields a different sponge from
/// the very first squeeze. Both sides hold the program, so both compute this
/// identically; the announced sizes ride the stream (`announce_public`).
fn program_digest(prog: &[Op]) -> [F128; 2] {
    // VM-native: encode the program as a field-element slice and hash its exact
    // little-endian bytes with standard BLAKE3 ([`crate::vmhash::hash_slice`]).
    let mut words: Vec<F128> = Vec::with_capacity(4 * prog.len() + 1);
    // Domain/version marker; standard BLAKE3 binds the total byte length.
    words.push(F128::new(prog.len() as u64, 1));
    for op in prog {
        // Fixed four-word encoding per instruction. The final two words carry
        // BLAKE3's remaining offsets; they are zero for other opcodes.
        let (tag, a, b, c, k, x, y) = match *op {
            Op::Xor { a, b, c } => (0u8, a, b, c, F128::ZERO, F128::ZERO, F128::ZERO),
            Op::Mul { a, b, c } => (1, a, b, c, F128::ZERO, F128::ZERO, F128::ZERO),
            Op::Set { o, k } => (2, o, 0, 0, k, F128::ZERO, F128::ZERO),
            Op::Deref {
                alpha,
                beta,
                gamma,
                mode,
            } => {
                (3 + mode as u8, alpha, beta, gamma, F128::ZERO, F128::ZERO, F128::ZERO)
            }
            Op::Jump { oc, od, of } => (6, oc, od, of, F128::ZERO, F128::ZERO, F128::ZERO),
            Op::Blake3 { ins, cv, out, metadata } => {
                (7, ins[0], ins[1], ins[2], metadata, F128::new(ins[3] as u64, cv as u64), F128::new(out as u64, 0))
            }
        };
        let lo = a as u64 | ((b as u64) << 32);
        let hi = c as u64 | ((tag as u64) << 32);
        words.push(F128::new(lo, hi));
        words.push(k);
        words.push(x);
        words.push(y);
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
pub fn fs_seed(program: &Program) -> [F128; 2] {
    let mut h = blake3::Hasher::new();
    h.update(b"leanvm-b-fs-seed-v1");
    h.update(&crate::blake3_flock::family_digest());
    for w in program.digest {
        h.update(&w.lo.to_le_bytes());
        h.update(&w.hi.to_le_bytes());
    }
    let d = *h.finalize().as_bytes();
    let word = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F128::new(word(0), word(8)), F128::new(word(16), word(24))]
}

/// The transcript seed: the public statement bound before any challenge, the
/// public input `pi` prefixed by the [`fs_seed`]. Both sides build it identically.
fn transcript_seed(program: &Program, pi: &[F128; 2]) -> [F128; 4] {
    let seed = fs_seed(program);
    [seed[0], seed[1], pi[0], pi[1]]
}

/// Announce the prover's per-table log-sizes (`log_mem` + the six `row_counts`) by
/// writing them onto the scalar stream (which binds them into the sponge and lets
/// the verifier reconstruct the layout). The public statement (program + input) is
/// not announced here — it seeds the transcript at construction (see
/// [`transcript_seed`]). The boundary states and per-table log-sizes (`taus`) are
/// derived (constants from the program, and `padlen(row_counts)`), so they need no
/// separate binding.
fn announce_public(ps: &mut ProverState, log_mem: usize, row_counts: [usize; 6]) {
    ps.add_scalar(F128::new(log_mem as u64, 0));
    for r in row_counts {
        ps.add_scalar(F128::new(r as u64, 0));
    }
}

/// Verifier side of [`announce_public`]: read the seven announced sizes from the
/// stream and reconstruct the public [`Layout`] from the program + sizes + public
/// input. (The public input was already bound by seeding the transcript.)
fn read_public(vs: &mut VerifierState, prog: &Program, public_input: &[F128; 2]) -> Result<Layout, Error> {
    let log_mem = vs.next_scalar().map_err(Error::Transcript)?.lo as usize;
    let mut row_counts = [0usize; 6];
    for r in &mut row_counts {
        *r = vs.next_scalar().map_err(Error::Transcript)?.lo as usize;
    }
    // Sanity-bound the announced sizes (a table's row count is the number of times
    // its opcode runs — unbounded by the bytecode size, since a small loop body
    // runs many times — so cap it generously, not by `bytecode_size`). The bus balance and
    // GKR pin the actual sizes; this only guards against absurd/overflowing values.
    let bytecode_size = prog.prog.len();
    if !bytecode_size.is_power_of_two()
        || !(MIN_LOG_MEM..=MAX_LOG_MEM).contains(&log_mem)
        || row_counts.iter().any(|&r| r >= (1usize << MAX_LOG_ROWS))
    {
        return Err(Error::PublicInput);
    }
    let l = layout(&prog.prog, log_mem, row_counts, *public_input);
    Ok(l)
}

pub struct Program {
    pub prog: Vec<Op>, // bytecode (size B, power of two)
    pub pc0: u32,
    pub fp0: u32,
    /// A binding digest of `prog` ([`program_digest`]), computed once at assembly
    /// and seeded into the transcript so every challenge depends on the exact
    /// program. Trusted to match `prog` — always set by [`Program::assemble`] from
    /// the bytecode, so a `Program` value cannot carry a digest inconsistent with
    /// its own `prog`.
    pub(crate) digest: [F128; 2],
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
    pub(crate) witness: HashMap<String, Vec<Vec<F128>>>,
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
    pub fn set_witness(&mut self, name: impl Into<String>, entries: Vec<Vec<F128>>) {
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
                point: table_claims[t].rho.clone(),
                value: table_claims[t].evals[k],
            });
        }
    }
    v
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
        .map(|i| crate::blake3_flock::VM_SLOTS[i])
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode counts `[XOR, MUL, SET, DEREF, JUMP, BLAKE3]`, and the
/// committed witness size — the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize,
    pub counts: [usize; 6],
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
/// run [`Stats`].
#[tracing::instrument(name = "Prove", skip_all)]
pub fn prove(program: &Program, public_input: [F128; 2]) -> (Proof, Stats) {
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
    let mut w = tracing::info_span!("Build witness").in_scope(|| program.build(&exec));
    let counts = w.row_counts;
    // Real committed data, before zero-pad to 2^m. Virtual columns (the BLAKE3
    // value columns) carry data for the bus but are NOT committed, so exclude them.
    let committed_size: usize = w
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
    announce_public(&mut ps, w.log_mem, w.row_counts);
    let t = std::time::Instant::now();
    let committed = tracing::info_span!("Commit").in_scope(|| pcs::commit(&mut ps, &w.q));
    if prof {
        eprintln!("[prove] commit      : {:>7.2} ms", ms(t));
    }

    // BLAKE3 ↔ flock (§blake3_flock), single PCS: q_pkd is ALWAYS a column in
    // `w.q` (≥1 instance — a program with no BLAKE3 carries one padding instance,
    // so the proof shape is uniform and there is no has/hasn't-BLAKE3 fork). flock's
    // R1CS validity and EVERY leanVM point claim are discharged together by ONE
    // Ligerito over this commitment (below). The input/output words bind via the
    // memory bus (virtual value columns route to q_pkd); the constant pins reuse a
    // bus point, so no dedicated binding challenge is drawn. Mirrored in `verify`.
    let t = std::time::Instant::now();
    let l = &w.layout;
    let (bus_claims, _bytecode_claims) = tracing::info_span!("Prove bus")
        .in_scope(|| leaf::prove_balance(&l.push, &l.pull, &l.count, &w.cols, &mut ps));
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

    let mut claims = bus_claims;
    claims.extend(constraint_claims(&table_claims));
    claims.push(bind_pi_claim(ps.sample(), &w.layout.placements, &w.layout.pi));
    // The input/output words bind via the memory bus (value columns are virtual and
    // route to q_pkd, see `slot_claims`); cv/counter/blen/flags are constants baked
    // into flock's per-block matrices, so no pin claims are needed.
    let slots = slot_claims(&w.layout, &claims);

    // Run flock's reduction (zerocheck + lincheck) over the prepared witness
    // layouts retained from the fused q_pkd build pass; it returns the `(ab, c)`
    // validity claims on the committed `q_pkd`, discharged by the PCS below in the
    // SAME Ligerito as every leanVM point claim (the point claims become the
    // opener's `stack_pd`).
    let t = std::time::Instant::now();
    let flock_reduction = w
        .flock_reduction
        .take()
        .expect("prepared flock reduction witness is present");
    let reduced = tracing::info_span!("Flock reduction")
        .in_scope(|| flock_reduction.prove(&w.cols[QPKD], &mut ps));
    let n_blocks = flock_reduction.n_blocks();
    drop(flock_reduction);
    let offset = w.layout.placements[QPKD].offset;
    let ring = tracing::info_span!("Package ring switch")
        .in_scope(|| crate::blake3_flock::ring_switch_open(n_blocks, offset, &reduced));
    if prof {
        eprintln!("[open]  reduction   : {:>7.2} ms", ms(t));
    }
    let t_pcs = std::time::Instant::now();
    let mixed_open = tracing::info_span!("PCS open")
        .in_scope(|| pcs::open(&mut ps, &committed, &w.q, &slots, &ring));
    if prof {
        eprintln!("[open]  pcs::open   : {:>7.2} ms", ms(t_pcs));
    }
    // flock's scalar sub-proof already rode the shared stream (add_scalar at its
    // protocol points); only the Merkle-bearing Ligerito needs the hint channel.
    ps.hint_opening(mixed_open);
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

/// The public-input binding claim (§8): `MEM(r, 0,…,0) = interp(m[0], m[1], r)`.
/// The value is a deterministic function of the (seeded) public input `pi` and the
/// challenge `r`, so it is NOT transmitted — both sides compute it, and the single
/// opening proves the committed `MEM` really evaluates to it (a memory whose first
/// two cells disagree with `pi` then fails the opening). `pi` is already bound (the
/// seed), so `r` is sampled directly. `placements`/`pi` come from the prover's or
/// verifier's layout; both build the byte-identical claim.
fn bind_pi_claim(r: F128, placements: &[witness::Placement], pi: &[F128; 2]) -> ColumnClaim {
    let mut point = vec![F128::ZERO; placements[MEM].n_vars];
    point[0] = r;
    ColumnClaim {
        col: MEM,
        point,
        value: primitives::multilinear::interp(pi[0], pi[1], r),
    }
}

/// Everything a recursion harness needs from an accepting verify run, named
/// and typed: the deferred bytecode claims, the count-channel root, the sponge
/// states at the phase boundaries (guest debug checkpoints), flock's reduction
/// claims, and the stacked-opening summary (ring-switch challenges + Ligerito
/// fold/query data). The sub-proof scalars themselves live on `proof.stream`
/// at fixed offsets from its tail. Ordinary callers just `?`-discard it.
pub struct VerifySummary {
    pub bytecode_claims: Vec<leaf::BytecodeClaim>,
    pub count_root: F128,
    /// Sponge states after: the bus, the zerochecks, the PI sample, and the
    /// flock reduction.
    pub checkpoints: [[F128; 2]; 4],
    pub zc_claim: flock::zerocheck::ZerocheckClaim,
    pub lc_claim: flock::lincheck::LincheckClaim,
    pub opening: pcs::StackedOpeningSummary,
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs — never the prover's witness.
#[tracing::instrument(name = "Verify", skip_all)]
pub fn verify(
    program: &Program,
    public_input: &[F128; 2],
    proof: &Proof,
) -> Result<VerifySummary, Error> {
    let mut vs = VerifierState::new(b"leanvm-b", proof, &transcript_seed(program, public_input));
    let l = read_public(&mut vs, program, public_input)?;
    let root = pcs::read_commitment(&mut vs).map_err(Error::Transcript)?;

    // BLAKE3 ↔ flock (single PCS): flock's R1CS validity and every leanVM point
    // claim are verified together by ONE Ligerito opening at the end. The executed-
    // BLAKE3 count is public (announced); its flock sub-proof rides the shared
    // `stream`/`openings`, and presence is enforced by consumption below plus
    // `vs.finish()` (a proof with `n_b3 = 0` but trailing flock data, or vice versa,
    // fails to fully consume). No dedicated binding challenge: the input/output
    // words bind via the memory bus, the pins reuse a bus point.
    let n_b3 = l.row_counts[tables::BLAKE3_TABLE];

    let bus = leaf::verify_balance(&l.push, &l.pull, &l.count, &l.pad, &mut vs).map_err(Error::Bus)?;
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

    let mut claims = bus.claims;
    claims.extend(constraint_claims(&table_claims));
    claims.push(bind_pi_claim(vs.sample(), &l.placements, &l.pi));
    let checkpoint_pi = vs.sponge_state();
    let slots = slot_claims(&l, &claims);

    // Replay flock's reduction straight off the shared stream (each scalar bound
    // as it is read) to recover its `(ab, c)` validity claims on q_pkd, then
    // verify them alongside every point claim in the ONE Ligerito opening
    // (mirroring `prove`). `n_blocks = max(n_b3, 1)` — always ≥ 1 instance.
    let n_blocks = n_b3.max(1);
    let offset = l.placements[QPKD].offset;
    let replay = crate::blake3_flock::verify_reduction(n_blocks, &root, l.m, &mut vs)
        .map_err(Error::Blake3)?;
    let checkpoint_flock = vs.sponge_state();
    let open = vs.next_opening().map_err(Error::Transcript)?;
    let ring = crate::blake3_flock::ring_switch_verify(n_blocks, offset, replay.ab, replay.c);
    let opening = pcs::verify(&mut vs, &slots, &ring, open, l.m, &root).map_err(Error::Open)?;
    vs.finish().map_err(Error::Transcript)?;
    Ok(VerifySummary {
        bytecode_claims: bus.bytecode_claims,
        count_root: bus.count_root,
        checkpoints: [checkpoint_bus, checkpoint_zerochecks, checkpoint_pi, checkpoint_flock],
        zc_claim: replay.zc_claim,
        lc_claim: replay.lc_claim,
        opening,
    })
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// BLAKE3 value columns are virtual — they have no committed placement. A bus
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_pkd` slot evaluation: an ordinary claim on the committed
/// `QPKD` column at the point freezing the low 7 coords to the slot's bits and
/// the high coords to `r`. No downstream special-casing — it folds into the
/// one opening like every other point claim.
fn slot_claims(l: &Layout, claims: &[ColumnClaim]) -> Vec<pcs::SlotClaim> {
    claims
        .iter()
        .map(|c| {
            // A virtual BLAKE3 value column (always virtual): its bus claim at
            // instance point `c.point` is the q_pkd slot value — a boolean-selector
            // (strided) claim on QPKD, folded sparsely (2^n_log, not the 2^(7+n_log)
            // dense QPKD block).
            if let Some(slot) = blake3_value_slot(c.col) {
                return pcs::SlotClaim::Strided {
                    offset: l.placements[QPKD].offset,
                    slot,
                    stride_log: crate::blake3_flock::SLOT_STRIDE_LOG,
                    point: c.point.clone(),
                    value: c.value,
                };
            }
            pcs::SlotClaim::Slot {
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

    /// A hand-built straight-line program exercising the `BLAKE3` table: set up
    /// the two 256-bit inputs (`a` at cells 2,3 and `b` at cells 4,5), hash them
    /// into the output `c` (cells 6,7), and halt at the sentinel. The flock
    /// validity sub-proof plus the memory / state / bytecode bus interactions
    /// are verified end-to-end (the proof carries the Ligerito opening they
    /// assert on).
    #[test]
    fn blake3_proves_and_verifies() {
        let x0 = F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
        let x1 = F128::new(0x1111_2222_3333_4444, 0x5555_6666_7777_8888);
        let y0 = F128::new(0xdead_beef_cafe_babe, 0x0badf00d_0badf00d);
        let y1 = F128::new(0x9999_aaaa_bbbb_cccc, 0xdddd_eeee_ffff_0000);

        // 8 slots (power of two). Slots 4 and 6 are filler SETs whose only job is to
        // step the pc so the last executed instruction lands at slot 6 (→ pc 7,
        // halt). Slot 7 is the never-executed sentinel.
        let prog = vec![
            Op::Set { o: 2, k: x0 },
            Op::Set { o: 3, k: x1 },
            Op::Set { o: 4, k: y0 },
            Op::Set { o: 5, k: y1 },
            Op::Set { o: 8, k: F128::ONE },
            Op::Blake3 {
                ins: [2, 3, 4, 5],
                cv: 0,
                out: 6,
                metadata: crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS),
            },
            Op::Set { o: 9, k: F128::ONE },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel (never executed)
        ];
        let program = Program::assemble(prog, 0, 0, HashMap::new(), 10);

        let pi = crate::blake3_flock::IV;
        let exec = program.execute(pi);

        // The output cells hold the digest of the two inputs (the prover computes
        // a definite value even though nothing constrains it).
        let (d0, d1) = blake3_compress(x0, x1, y0, y1, pi[0], pi[1], crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS));
        assert_eq!(exec.mem[6], d0);
        assert_eq!(exec.mem[7], d1);
        assert_eq!(exec.trace.blake3.len(), 1);

        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        // flock's sub-proof rides the shared channels: its Ligerito is the proof's
        // one opening, its scalar reduction trails the `stream`.
        assert!(!proof.openings.is_empty(), "BLAKE3 program carries a Ligerito opening");
        verify(&program, &pi, &proof).expect("BLAKE3 program verifies");
    }

    /// A self-hash `BLAKE3(h, h)` (the hash-chain step) passes the *same* operand
    /// base as both `a` and `b` (`a == b`), so one 256-bit pair feeds both inputs
    /// with no copy. The row reads those two cells twice; the running access counts
    /// thread through and the bus still balances. This is the aliasing the
    /// consecutive-pair DSL lowering relies on.
    #[test]
    fn blake3_self_hash_aliased_operands() {
        let h0 = F128::new(0xfeed_face_dead_beef, 0x0123_4567_89ab_cdef);
        let h1 = F128::new(0xcafe_d00d_1337_c0de, 0x8877_6655_4433_2211);
        // 8 slots (power of two). Slots 2,3,6 are filler SETs stepping the pc so the
        // last executed instruction (slot 6) lands at pc 7 (the sentinel, halt).
        let prog = vec![
            Op::Set { o: 2, k: h0 }, // operand pair h = (cell 2, cell 3)
            Op::Set { o: 3, k: h1 },
            Op::Set { o: 8, k: F128::ONE },  // filler
            Op::Set { o: 9, k: F128::ONE },  // filler
            Op::Set { o: 10, k: F128::ONE }, // filler
            Op::Blake3 {
                ins: [2, 3, 2, 3],
                cv: 0,
                out: 6,
                metadata: crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS),
            }, // a == b: hash h ‖ h into cells 6,7
            Op::Set { o: 11, k: F128::ONE }, // filler
            Op::Xor { a: 0, b: 0, c: 0 },    // sentinel
        ];
        let program = Program::from_bytecode(prog, 16);
        let pi = crate::blake3_flock::IV;

        let exec = program.execute(pi);
        let (d0, d1) = blake3_compress(h0, h1, h0, h1, pi[0], pi[1], crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS));
        assert_eq!(exec.mem[6], d0);
        assert_eq!(exec.mem[7], d1);

        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        verify(&program, &pi, &proof).expect("self-hash BLAKE3 verifies");
    }

    /// Tampering flock's validity sub-proof (its Ligerito `final_b`, opened over
    /// the same stacked commitment) must make verification fail.
    #[test]
    fn blake3_rejects_tampered_validity() {
        let prog = vec![
            Op::Set {
                o: 2,
                k: F128::new(0xABCD, 0x1234),
            },
            Op::Set {
                o: 3,
                k: F128::new(0x5678, 0x9999),
            },
            Op::Set {
                o: 4,
                k: F128::new(0x1111, 0x2222),
            },
            Op::Set {
                o: 5,
                k: F128::new(0x3333, 0x4444),
            },
            Op::Set { o: 8, k: F128::ONE },
            Op::Blake3 {
                ins: [2, 3, 4, 5], cv: 0, out: 6,
                metadata: crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS),
            },
            Op::Set { o: 9, k: F128::ONE },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 10);
        let pi = crate::blake3_flock::IV;
        let (mut proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // flock's Ligerito opening is the proof's one hint; tamper an opened
        // row (the Merkle-bound query data) — must be rejected. (The sumcheck
        // round messages ride the stream and are covered by the stream-tamper
        // test below.)
        let lig = proof.openings.last_mut().expect("flock Ligerito opening");
        lig.initial_proof.opened_rows[0][0] += F128::ONE;
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
        let prog = vec![
            Op::Set {
                o: 2,
                k: F128::new(0xABCD, 0x1234),
            },
            Op::Set {
                o: 3,
                k: F128::new(0x5678, 0x9999),
            },
            Op::Set {
                o: 4,
                k: F128::new(0x1111, 0x2222),
            },
            Op::Set {
                o: 5,
                k: F128::new(0x3333, 0x4444),
            },
            Op::Set { o: 8, k: F128::ONE },
            Op::Blake3 {
                ins: [2, 3, 4, 5], cv: 0, out: 6,
                metadata: crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS),
            },
            Op::Set { o: 9, k: F128::ONE },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 10);
        let pi = crate::blake3_flock::IV;
        let (proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // The reduction is serialized onto the stream tail (after the last bound
        // scalar). Flip a full transport word there — the second-to-last word is
        // always meaningful bytes (only the final word may be zero-padded).
        let mut tampered = proof.clone();
        let n = tampered.stream.len();
        tampered.stream[n - 2] += F128::ONE;
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
            Op::Set {
                o: 2,
                k: F128::new(5, 0),
            },
            Op::Set {
                o: 3,
                k: F128::new(6, 0),
            },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [F128::new(1, 0), F128::new(2, 0)];
        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 0, "no real BLAKE3 rows");
        // The proof still carries exactly one Ligerito opening (over the padding).
        assert_eq!(proof.openings.len(), 1, "unified path: one opening always");
        verify(&program, &pi, &proof).expect("non-BLAKE3 program verifies");
    }

    /// A proof is bound to its exact program: presenting it against a *different*
    /// program (same sizes/layout, one instruction constant changed) must be
    /// rejected — the program digest seeds the transcript, so a modified program
    /// diverges the sponge from the first squeeze. Guards the adaptive-statement
    /// forgery the bytecode-bus single-point MLE check does not, on its own, prevent.
    #[test]
    fn proof_bound_to_program() {
        let prog = vec![
            Op::Set {
                o: 2,
                k: F128::new(5, 0),
            },
            Op::Set {
                o: 3,
                k: F128::new(6, 0),
            },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog.clone(), 5);
        let pi = [F128::new(1, 0), F128::new(2, 0)];
        let (proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // Same shape (4 ops, same opcodes/operands, so identical layout + announced
        // sizes) but one SET constant changed. Must be rejected.
        let mut prog2 = prog;
        prog2[0] = Op::Set {
            o: 2,
            k: F128::new(99, 0),
        };
        let program2 = Program::from_bytecode(prog2, 5);
        assert!(
            verify(&program2, &pi, &proof).is_err(),
            "a proof must not verify against a different program"
        );
    }

    /// Out-of-process verification: a BLAKE3 proof (whose flock sub-proof now rides
    /// the shared `stream` + `openings`, no side field) serializes to bytes,
    /// deserializes on the other side, and verifies — everything travels in the two
    /// channels, nothing out of band. A flipped encoded byte must not verify.
    #[test]
    fn proof_roundtrips_through_bytes_and_verifies() {
        let prog = vec![
            Op::Set {
                o: 2,
                k: F128::new(0xABCD, 0x1234),
            },
            Op::Set {
                o: 3,
                k: F128::new(0x5678, 0x9999),
            },
            Op::Set {
                o: 4,
                k: F128::new(0x1111, 0x2222),
            },
            Op::Set {
                o: 5,
                k: F128::new(0x3333, 0x4444),
            },
            Op::Set { o: 8, k: F128::ONE },
            Op::Blake3 {
                ins: [2, 3, 4, 5], cv: 0, out: 6,
                metadata: crate::blake3_flock::metadata(0, 64, crate::blake3_flock::FLAGS),
            },
            Op::Set { o: 9, k: F128::ONE },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 10);
        let pi = crate::blake3_flock::IV;
        let (proof, _) = prove(&program, pi);

        let bytes = bincode::serialize(&proof).expect("proof serializes");
        let decoded: Proof = bincode::deserialize(&bytes).expect("proof deserializes");
        verify(&program, &pi, &decoded).expect("deserialized BLAKE3 proof verifies");

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
