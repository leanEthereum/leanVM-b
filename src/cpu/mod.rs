//! Whole-program assembly over GF(2^64) (§7, §8): the six instruction tables
//! sharing the state / memory / bytecode buses, bound to one field-valued
//! commitment and verified oracle-free. Addresses, the program counter, and read
//! counts are g-powers, so every increment is a free ×g; arithmetic is the field's
//! own (XOR = degree-1, MUL_NATIVE = degree-2, both over `K = F64`). `BLAKE3`
//! (§7.6) adds the memory/state/bytecode plumbing for a 64→32-byte compression
//! whose relation is discharged by flock (see [`crate::blake3_flock`]). All
//! challenges and transcript scalars live in the tower `E = F128T`.

use std::collections::HashMap;

use rayon::prelude::*;

use crate::constraints;
use crate::field::{F64, F128T, G, g_pow};
use crate::leaf::{self, Block, ColumnClaim, Coord};
use crate::pcs;
use crate::tables::{
    self, FillCtx, FlushBuilder, OP_BLAKE3, OP_DEREF, OP_JUMP, OP_MUL, OP_SET, OP_XOR, SEP_BYTECODE, SEP_MEM, SEP_STATE,
};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::{self, Column};

mod execute;
mod isa;
mod layout;
mod trace;
pub use execute::Execution;
pub use isa::{DerefMode, Op};
pub(crate) use layout::*;
pub(crate) use trace::{Brow, Drow, Jrow, Srow, Trace, Xrow};

/// Witness-gen `BLAKE3` compression (doc §7.6): the eight input words are the two
/// 256-bit operands `a = va[0..4]`, `b = vb[0..4]` laid out little-endian into
/// 64 bytes (8 bytes per 64-bit word); the 32-byte digest is split back into the
/// four output words `c`. The BLAKE3 hash of the 64-byte input — the relation
/// flock then proves ([`crate::blake3_flock`]).
fn blake3_compress(va: [F64; 4], vb: [F64; 4]) -> [F64; 4] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(8).zip(va.into_iter().chain(vb)) {
        slot.copy_from_slice(&w.0.to_le_bytes());
    }
    let digest = blake3::hash(&input);
    let d = digest.as_bytes();
    std::array::from_fn(|k| F64(u64::from_le_bytes(d[8 * k..8 * k + 8].try_into().unwrap())))
}

/// Data-memory size bounds (doc §Memory): memory is `2^h` cells with
/// `MIN_LOG_MEM ≤ h ≤ MAX_LOG_MEM`. The prover pads up to the minimum; the
/// verifier rejects any announced `h` outside the range. `MIN_LOG_MEM` is also
/// the static cap on range-check bounds (`compiler::Stmt::AssertLt`): a bound
/// `≤ 2^MIN_LOG_MEM` keeps the complement argument sound for every memory size
/// the prover may announce.
pub(crate) const MIN_LOG_MEM: usize = 16;
const MAX_LOG_MEM: usize = 32;

/// Each per-opcode table holds at most `2^MAX_LOG_ROWS` rows (executed
/// instructions of that opcode). Together with `MAX_LOG_MEM` and the bytecode
/// cap these are the *instance caps* (transition doc §caps): at `ord(g) = 2^64−1`
/// the memory-soundness and count-non-wrap counting arguments are theorems only
/// for instances whose total read-flush count stays far below `2^64`, so the
/// verifier rejects any announcement exceeding them before running a reduction.
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
/// through the bytecode bus's `Public`-coordinate MLE evaluation at the GKR point
/// `ζ` — a single point an attacker recovers from a finished proof. It could then
/// craft a different program `P'` agreeing with `P`'s bytecode columns at that one
/// `ζ` and re-present the same proof for `P'` (adaptive-statement forgery). Seeding
/// `H(program)` before any challenge makes the whole statement — (program, public
/// input) — bound up front, so a different program yields a different sponge from
/// the very first squeeze. Both sides hold the program, so both compute this
/// identically; the announced sizes ride the stream (`announce_public`).
fn program_digest(prog: &[Op]) -> [F128T; 2] {
    let mut h = blake3::Hasher::new();
    h.update(b"leanvm-b/program/v0");
    h.update(&(prog.len() as u64).to_le_bytes());
    for op in prog {
        let (tag, a, b, c, k) = match *op {
            Op::Xor { a, b, c } => (0u8, a, b, c, F64::ZERO),
            Op::Mul { a, b, c } => (1, a, b, c, F64::ZERO),
            Op::Set { o, k } => (2, o, 0, 0, k),
            Op::Deref {
                alpha,
                beta,
                gamma,
                mode,
            } => {
                (3 + mode as u8, alpha, beta, gamma, F64::ZERO) // mode ∈ {Cell,Pc,Fp} ⇒ tag 3/4/5
            }
            Op::Jump { oc, od, of } => (6, oc, od, of, F64::ZERO),
            Op::Blake3 { a, b, c } => (7, a, b, c, F64::ZERO),
        };
        h.update(&[tag]);
        h.update(&a.to_le_bytes());
        h.update(&b.to_le_bytes());
        h.update(&c.to_le_bytes());
        h.update(&k.0.to_le_bytes());
    }
    let d = *h.finalize().as_bytes();
    let w = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    [F128T::new(w(0), w(8)), F128T::new(w(16), w(24))]
}

/// The transcript seed: the public statement bound before any challenge — the
/// public input `pi` followed by the program's stored [`digest`](Program::digest)
/// (computed once at assembly, not re-hashed here). Both sides build it identically.
fn transcript_seed(program: &Program, pi: &[F64; 2]) -> [F128T; 4] {
    [
        F128T::from(pi[0]),
        F128T::from(pi[1]),
        program.digest[0],
        program.digest[1],
    ]
}

/// Announce the prover's per-table log-sizes (`log_mem` + the six `row_counts`) by
/// writing them onto the scalar stream (which binds them into the sponge and lets
/// the verifier reconstruct the layout). The public statement (program + input) is
/// not announced here — it seeds the transcript at construction (see
/// [`transcript_seed`]). The boundary states and per-table log-sizes (`taus`) are
/// derived (constants from the program, and `padlen(row_counts)`), so they need no
/// separate binding.
fn announce_public(ps: &mut ProverState, log_mem: usize, row_counts: [usize; 6]) {
    ps.add_scalar(F128T::new(log_mem as u64, 0));
    for r in row_counts {
        ps.add_scalar(F128T::new(r as u64, 0));
    }
}

/// Verifier side of [`announce_public`]: read the seven announced sizes from the
/// stream, check them against the instance caps, and reconstruct the public
/// [`Layout`] from the program + sizes + public input. (The public input was
/// already bound by seeding the transcript.)
fn read_public(vs: &mut VerifierState, prog: &Program, public_input: &[F64; 2]) -> Result<Layout, Error> {
    let log_mem = vs.next_scalar().map_err(Error::Transcript)?.c0 as usize;
    let mut row_counts = [0usize; 6];
    for r in &mut row_counts {
        *r = vs.next_scalar().map_err(Error::Transcript)?.c0 as usize;
    }
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
    pub(crate) digest: [F128T; 2],
    /// Prover-side frame/buffer allocation hints (keyed by global pc) and the
    /// size of `main`'s frame — the nondeterminism [`Program::execute`] needs to
    /// run the program. Public verification (\S `verify`) ignores them.
    pub(crate) hints: HashMap<u32, Vec<crate::compiler::RHint>>,
    pub(crate) main_frame: u32,
    /// Named prover witness streams for the program's `hint_witness` calls
    /// ([`Program::set_witness`]): a stream is a sequence of *entries* (one
    /// slice of values per `hint_witness` call — the same symbol may be
    /// hinted many times); each call pops the next entry, whose length must
    /// match its destination. Prover-side only; verification ignores them.
    pub(crate) witness: HashMap<String, Vec<Vec<F64>>>,
}

impl Program {
    /// Assemble a [`Program`], computing its bytecode [`digest`](Program::digest)
    /// from `prog`. The single funnel for construction, so the digest is always
    /// consistent with the bytecode.
    pub(crate) fn assemble(
        prog: Vec<Op>,
        pc0: u32,
        fp0: u32,
        hints: HashMap<u32, Vec<crate::compiler::RHint>>,
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
        }
    }

    /// Supply the entries of witness stream `name`: one slice of values per
    /// `hint_witness(dest, "name")` call, popped in order (the same symbol
    /// may be hinted many times). Prover-side data: entirely unconstrained,
    /// invisible to verification.
    pub fn set_witness(&mut self, name: impl Into<String>, entries: Vec<Vec<F64>>) {
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

/// Render the bytecode as a disassembly listing (also gives `Program::to_string`).
impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&crate::compiler::disassemble(&self.prog))
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
    Blake3(flock_prover::verifier::VerifyError),
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
        .map(|i| crate::blake3_flock::SLOTS[i])
}

/// The instance-cube point the BLAKE3 constant pins are checked at: any BLAKE3
/// value-column bus claim's point (the memory bus's push-side GKR output, an
/// FS-random, post-commit, `n_log`-dim point). Reusing it avoids a dedicated
/// binding challenge. `claims` must already hold the bus claims, and BLAKE3 must
/// have run (so a value-column claim exists). Deterministic and identical across
/// prove/verify (both build the bus claims in the same order).
fn blake3_pin_point(claims: &[ColumnClaim]) -> Vec<F128T> {
    claims
        .iter()
        .find(|c| blake3_value_slot(c.col).is_some())
        .expect("BLAKE3 ran ⇒ a value-column bus claim exists")
        .point
        .clone()
}

/// MLE of `[1;n, 0;…]` at `point` (LSB-first), i.e. `Σ_{j<n} eq(j, point)`, in
/// `O(point.len()²)` — one term per set bit of `n` (an aligned `2^t` block sums to
/// `eq` of its high bits), never materializing the `2^point.len()` vector.
fn mle_of_ones_then_zeros(n: usize, point: &[F128T]) -> F128T {
    let l = point.len();
    debug_assert!(n <= 1usize << l);
    let mut sum = F128T::ZERO;
    let mut base = 0usize; // low indices already covered
    // Include t = l so the full cube (n = 2^l, bit l set) is one block whose free
    // coords all sum to 1; `point[l..]` is then empty ⇒ eq = 1.
    for t in (0..=l).rev() {
        if (n >> t) & 1 == 1 {
            // Block [base, base + 2^t): its high bits (coords t..l) are `base >> t`.
            let a = base >> t;
            let mut e = F128T::ONE;
            for (i, &x) in point[t..].iter().enumerate() {
                e *= if (a >> i) & 1 == 1 { x } else { F128T::ONE + x };
            }
            sum += e;
            base += 1 << t;
        }
    }
    sum
}

/// BLAKE3 `q_pkd` **pin** claims at the instance point `point` (a memory-bus
/// point, see [`blake3_pin_point`]): per pin slot, `q_pkd(pin_slot‖point) =
/// pin_col(point)` against the PUBLIC constant column (`cv = IV`,
/// counter = 0, blen/flags = 64/11), pinning the compression to a real
/// BLAKE3-of-64-bytes. The pin column is `pin[k]` on the first `n_blocks`
/// instances and `0` on padding, so its MLE is `pin[k] · Σ_{j<n_blocks} eq(j,
/// point)` — computed in `O(n_log²)` by [`mle_of_ones_then_zeros`], never materialized. The
/// input/output words are NOT pinned here — they bind via the memory bus routing
/// to `q_pkd` (see [`blake3_value_slot`]). Values are public; symmetric across
/// prove/verify.
fn blake3_pin_claims(point: &[F128T], n_blocks: usize) -> Vec<ColumnClaim> {
    use crate::blake3_flock::{PIN_SLOTS, pin_constants, slot_point};
    let pin = pin_constants();
    let prefix = mle_of_ones_then_zeros(n_blocks, point);
    let mut v = Vec::with_capacity(PIN_SLOTS.len());
    for (k, &pslot) in PIN_SLOTS.iter().enumerate() {
        v.push(ColumnClaim {
            col: QPKD,
            point: slot_point(pslot, point),
            value: prefix.mul_base(pin[k]),
        });
    }
    v
}

/// Run statistics returned alongside the proof: the cycle count (total executed
/// instructions), the per-opcode counts `[XOR, MUL, SET, DEREF, JUMP, BLAKE3]`, and the
/// committed witness size — the sum of the column lengths, i.e. the real data
/// before the stacked witness is zero-padded to a power of two `2^m`.
pub struct Stats {
    pub cycles: usize,
    pub counts: [usize; 6],
    pub committed: usize,
}

/// Prove the program on the given public input: run it (witness generation),
/// then emit everything the verifier needs through the returned [`Proof`]
/// (scalar stream + PCS commitment / opening hints). Returns the proof and the
/// run [`Stats`].
pub fn prove(program: &Program, public_input: [F64; 2]) -> (Proof, Stats) {
    let prof = std::env::var("LEANVM_PROFILE").is_ok();
    let ms = |t: std::time::Instant| t.elapsed().as_secs_f64() * 1e3;
    let exec = program.execute(public_input);
    let cycles = exec.cycles;
    let w = program.build(&exec);
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
    let committed = pcs::commit(&mut ps, &w.q);
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
    let bus_claims = leaf::prove_balance(&l.push, &l.pull, &l.count, &w.cols, &mut ps);
    if prof {
        eprintln!("[prove] bus(grand-p): {:>7.2} ms", ms(t));
    }
    let t = std::time::Instant::now();
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
    if prof {
        eprintln!("[prove] constraints : {:>7.2} ms", ms(t));
    }

    let mut claims = bus_claims;
    claims.extend(constraint_claims(&table_claims));
    claims.push(bind_pi_claim(ps.sample(), &w.layout.placements, &w.layout.pi));
    // The input/output words bind via the memory bus (value columns are virtual and
    // route to q_pkd, see `slot_claims`); only q_pkd's constant slots need pinning,
    // at a memory-bus point. The pin prefix uses the REAL BLAKE3 count (0 pins
    // nothing — padding instances hold 0).
    let pin_point = blake3_pin_point(&claims);
    claims.extend(blake3_pin_claims(&pin_point, exec.trace.blake3.len()));
    let slots = slot_claims(&w.layout, &claims);

    // Run flock's reduction (zerocheck + lincheck) over the executed compressions
    // (or a single padding instance when none ran); it returns the `(ab, c)`
    // validity claims on the committed `q_pkd`, discharged by the PCS below in the
    // SAME Ligerito as every leanVM point claim (the point claims become the
    // opener's `point_claims`).
    let t = std::time::Instant::now();
    use flock_prover::r1cs_hashes::blake3::Compression;
    let blocks: Vec<Compression> = if exec.trace.blake3.is_empty() {
        vec![crate::blake3_flock::padding_compression()]
    } else {
        exec.trace
            .blake3
            .iter()
            .map(|r| crate::blake3_flock::compression(r.va, r.vb))
            .collect()
    };
    let (_z_packed, zc, lc, reduced) =
        crate::blake3_flock::prove_reduction(&blocks, &committed.commitment.root, committed.mu, &mut ps);
    let offset = w.layout.placements[QPKD].offset;
    let ring = crate::blake3_flock::ring_switch_open(blocks.len(), offset, &reduced);
    let mixed_open = pcs::open(&mut ps, &committed, &w.q, &slots, &ring);
    // Carry flock's sub-proof on the shared channels: its scalar reduction on the
    // `stream` (raw transport), its Ligerito on the `openings` hint channel.
    crate::blake3_flock::write_stack_proof(&mut ps, zc, lc, mixed_open);
    if prof {
        eprintln!("[prove] open        : {:>7.2} ms", ms(t));
    }
    (
        ps.into_proof(),
        Stats {
            cycles,
            counts,
            committed: committed_size,
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
fn bind_pi_claim(r: F128T, placements: &[witness::Placement], pi: &[F64; 2]) -> ColumnClaim {
    let mut point = vec![F128T::ZERO; placements[MEM].n_vars];
    point[0] = r;
    ColumnClaim {
        col: MEM,
        point,
        value: crate::multilinear::interp_k(pi[0], pi[1], r),
    }
}

/// Verify a proof against the public statement (program + public input): replay
/// the transcript, reconstruct the public layout from the announced sizes, read
/// every scalar the prover wrote and pull the PCS hints, then assert the stream
/// was fully consumed. Takes only public inputs — never the prover's witness.
pub fn verify(program: &Program, public_input: &[F64; 2], proof: &Proof) -> Result<(), Error> {
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

    let bus_claims = leaf::verify_balance(&l.push, &l.pull, &l.count, &l.pad, &mut vs).map_err(Error::Bus)?;

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

    let mut claims = bus_claims;
    claims.extend(constraint_claims(&table_claims));
    claims.push(bind_pi_claim(vs.sample(), &l.placements, &l.pi));
    // Value columns are virtual (routed to q_pkd via `slot_claims`); only the
    // constant pins are added here, at a memory-bus point, mirroring `prove`. The
    // pin prefix uses the REAL count `n_b3` (0 pins nothing).
    let pin_point = blake3_pin_point(&claims);
    claims.extend(blake3_pin_claims(&pin_point, n_b3));
    // Read flock's BLAKE3 sub-proof off the shared channels (mirrors prove's
    // `write_stack_proof`): the scalar reduction from the `stream` as raw transport
    // (right after the last bound scalar), its Ligerito from `openings`.
    let (zerocheck, lincheck, open) = crate::blake3_flock::read_stack_proof(&mut vs).map_err(Error::Transcript)?;
    let slots = slot_claims(&l, &claims);

    // Replay flock's reduction to recover its `(ab, c)` validity claims on q_pkd,
    // then verify them alongside every point claim in the ONE Ligerito opening
    // (mirroring `prove`). `n_blocks = max(n_b3, 1)` — always ≥ 1 instance.
    let n_blocks = n_b3.max(1);
    let offset = l.placements[QPKD].offset;
    let (ab, c) = crate::blake3_flock::verify_reduction(n_blocks, &root, l.m, &zerocheck, &lincheck, &mut vs)
        .map_err(Error::Blake3)?;
    let ring = crate::blake3_flock::ring_switch_verify(n_blocks, offset, ab, c);
    pcs::verify(&mut vs, &slots, &ring, &open, l.m, &root).map_err(Error::Open)?;
    vs.finish().map_err(Error::Transcript)
}

/// Lift `ColumnClaim`s to located PCS claims: a claim on column `c` lives in
/// the slot at `placements[c].offset`, with the claim's point as the low point.
///
/// BLAKE3 value columns are virtual — they have no committed placement. A bus
/// claim `value_col(r) = v` (at the `n_log`-dim instance point `r`) is re-routed
/// to the equal `q_pkd` slot evaluation: an ordinary claim on the committed
/// `QPKD` column at `slot_point(slot, r)` (the packed point freezing the low 8
/// coords to the slot's bits). No downstream special-casing — it folds into the
/// one opening like every other point claim.
fn slot_claims(l: &Layout, claims: &[ColumnClaim]) -> Vec<pcs::SlotClaim> {
    claims
        .iter()
        .map(|c| {
            // A virtual BLAKE3 value column (always virtual): its bus claim at
            // instance point `c.point` is the q_pkd slot value — a boolean-selector
            // (strided) claim on QPKD, folded sparsely (2^n_log, not the 2^(8+n_log)
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

    /// The O(n_log²) `mle_of_ones_then_zeros` must equal the naive MLE of the prefix
    /// indicator `[1;n, 0;…]` — the pin value depends on it, so any mismatch is a
    /// soundness bug, not just a perf regression.
    #[test]
    fn mle_of_ones_then_zeros_matches_dense() {
        for l in 0..=6usize {
            let point: Vec<F128T> = (0..l)
                .map(|i| F128T::new(0x9e37 * (i as u64 + 1) + 3, 0x51 * i as u64 + 7))
                .collect();
            for n in 0..=(1usize << l) {
                let mut col = vec![F64::ZERO; 1usize << l];
                for c in col.iter_mut().take(n) {
                    *c = F64::ONE;
                }
                let dense = if l == 0 {
                    if n >= 1 { F128T::ONE } else { F128T::ZERO }
                } else {
                    crate::multilinear::mle_eval(&col, &point)
                };
                assert_eq!(mle_of_ones_then_zeros(n, &point), dense, "l={l} n={n}");
            }
        }
    }

    /// A hand-built straight-line program with one BLAKE3 row: set up the two
    /// 256-bit inputs (`a` at cells 2..6, `b` at cells 6..10), hash them into the
    /// output `c` (cells 10..14), pad with filler SETs so the last executed
    /// instruction lands one before the sentinel, and halt there.
    fn blake3_program(a: [F64; 4], b: [F64; 4]) -> Program {
        let mut prog = Vec::new();
        for (k, &w) in a.iter().enumerate() {
            prog.push(Op::Set { o: 2 + k as u32, k: w });
        }
        for (k, &w) in b.iter().enumerate() {
            prog.push(Op::Set { o: 6 + k as u32, k: w });
        }
        prog.push(Op::Blake3 { a: 2, b: 6, c: 10 });
        // 16 slots: 9 executed so far; 6 filler SETs step the pc to 15 (halt);
        // slot 15 is the never-executed sentinel.
        for k in 0..6u32 {
            prog.push(Op::Set {
                o: 16 + k,
                k: F64::ONE,
            });
        }
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel (never executed)
        assert_eq!(prog.len(), 16);
        Program::from_bytecode(prog, 24)
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

        let pi = [F64(7), F64(11)];
        let exec = program.execute(pi);

        // The output cells hold the digest of the two inputs.
        let d = blake3_compress(a, b);
        assert_eq!(&exec.mem[10..14], &d);
        assert_eq!(exec.trace.blake3.len(), 1);

        let (proof, stats) = prove(&program, pi);
        assert_eq!(stats.counts[5], 1, "one BLAKE3 row");
        // flock's sub-proof rides the shared channels: its Ligerito is the proof's
        // one opening, its scalar reduction trails the `stream`.
        assert!(!proof.openings.is_empty(), "BLAKE3 program carries a Ligerito opening");
        verify(&program, &pi, &proof).expect("BLAKE3 program verifies");
    }

    /// A self-hash `BLAKE3(h, h)` (the hash-chain step) passes the *same* operand
    /// base as both `a` and `b` (`a == b`), so one 256-bit quad feeds both inputs
    /// with no copy. The row reads those four cells twice; the running access counts
    /// thread through and the bus still balances. This is the aliasing the
    /// consecutive-quad DSL lowering relies on.
    #[test]
    fn blake3_self_hash_aliased_operands() {
        let h: [F64; 4] = [
            F64(0xfeed_face_dead_beef),
            F64(0x0123_4567_89ab_cdef),
            F64(0xcafe_d00d_1337_c0de),
            F64(0x8877_6655_4433_2211),
        ];
        // 8 slots: 4 SETs (h at cells 2..6), the aliased BLAKE3 (output 6..10),
        // 2 filler SETs stepping the pc to 7 (the sentinel, halt).
        let mut prog = Vec::new();
        for (k, &w) in h.iter().enumerate() {
            prog.push(Op::Set { o: 2 + k as u32, k: w });
        }
        prog.push(Op::Blake3 { a: 2, b: 2, c: 6 }); // a == b: hash h ‖ h into cells 6..10
        prog.push(Op::Set { o: 12, k: F64::ONE }); // filler
        prog.push(Op::Set { o: 13, k: F64::ONE }); // filler
        prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel
        assert_eq!(prog.len(), 8);
        let program = Program::from_bytecode(prog, 16);
        let pi = [F64(3), F64(5)];

        let exec = program.execute(pi);
        let d = blake3_compress(h, h);
        assert_eq!(&exec.mem[6..10], &d);

        let (proof, stats) = prove(&program, pi);
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
        let pi = [F64(7), F64(11)];
        let (mut proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // The Ligerito opening is the proof's one hint; tamper a sumcheck
        // round message (the inner-product transcript) — must be rejected.
        let lig = proof.openings.last_mut().expect("Ligerito opening");
        lig.sumcheck_transcript[0].u_0 += F128T::ONE;
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
        let pi = [F64(7), F64(11)];
        let (proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // The reduction is serialized onto the stream tail (after the last bound
        // scalar). Flip a full transport word there — the second-to-last word is
        // always meaningful bytes (only the final word may be zero-padded).
        let mut tampered = proof.clone();
        let n = tampered.stream.len();
        tampered.stream[n - 2] += F128T::ONE;
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
            Op::Set { o: 2, k: F64(5) },
            Op::Set { o: 3, k: F64(6) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog, 5);
        let pi = [F64(1), F64(2)];
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
            Op::Set { o: 2, k: F64(5) },
            Op::Set { o: 3, k: F64(6) },
            Op::Xor { a: 2, b: 3, c: 4 },
            Op::Xor { a: 0, b: 0, c: 0 }, // sentinel
        ];
        let program = Program::from_bytecode(prog.clone(), 5);
        let pi = [F64(1), F64(2)];
        let (proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).expect("honest proof verifies");

        // Same shape (4 ops, same opcodes/operands, so identical layout + announced
        // sizes) but one SET constant changed. Must be rejected.
        let mut prog2 = prog;
        prog2[0] = Op::Set { o: 2, k: F64(99) };
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
        let pi = [F64(7), F64(11)];
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
