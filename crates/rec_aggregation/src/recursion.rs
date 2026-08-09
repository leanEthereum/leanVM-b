//! End-to-end N→1 recursion: one guest program (`guests/recursion.py`)
//! replays `cpu::verify` for a hinted number of proofs of a fixed inner program, batches
//! their deferred claims with the two aggregation sumchecks, and binds the sub
//! statements + the three reduced claims (stacked bytecode, A0, B0) to its own
//! public input (`doc/main.tex` §Recursive aggregation, §Deferred evaluation claims).
//!
//! The transcript trace of a real `cpu::verify` run
//! (`transcript::trace_start`/`trace_take`) keeps the native and guest verifiers
//! synchronized: `gen_verify` walks it structurally, while `cpu::layout`
//! supplies every compile-time shape. `aggregate_deferred_claims` builds the guest's aggregation
//! transcript and the two batching-sumcheck proofs.
//! [`RecursiveProof::verify`] is the only public acceptance path: it verifies
//! the outer VM proof and evaluates every deferred fixed polynomial.

use std::collections::BTreeMap;

use lean_compiler::{compile, parse, parse_with_replacements};
use lean_vm::cpu::{Program, prove, verify};
use lean_vm::leaf::{Block, Coord};
use lean_vm::transcript::{Sponge, TraceOp, trace_start, trace_take};
use primitives::bench::Plan;
use primitives::multilinear::mle_eval;
use primitives::{
    field::{F64, F192, G, g_pow},
    pretty_f64, pretty_integer,
};

/// Why the guest reads every `q_flock` slot claim's instance point off `rho`: a
/// virtual value column is referenced only by its own table's bus blocks, which
/// the table sumcheck settles, so no framework block can raise one at `zeta`.
const VALCOL_FRAMEWORK: &str = "a framework block must not reference a virtual value column";
const RECURSION_AGG_LABEL: &[u8] = b"leanvm-b/recursion-aggregation/v1";
const RECURSION_STATEMENT_LABEL: &[u8] = b"leanvm-b/recursive-statement/v1";

/// Aggregation arity bound: the guest hints the count and range-checks its
/// exponent against this (`NSUB_BOUND`), which is what makes its per-sub walks
/// terminate. The bytecode does not otherwise depend on the arity.
const NSUB_BOUND: usize = 1024;

/// The aggregation arity, as the guest carries it: in the exponent, `g^nsub`.
/// Both aggregation transcripts absorb it in this form, ahead of every
/// variable-length sequence.
fn nsub_word(nsub: usize) -> F192 {
    assert!(nsub < NSUB_BOUND, "recursion arity {nsub} exceeds the guest bound");
    F192::new(g_pow(nsub).0, 0, 0)
}

/// A field element as the decimal `u128` literal the zkDSL parser accepts.
fn u(f: F192) -> u128 {
    assert_eq!(f.c2, 0, "u128 DSL literal cannot encode the top F192 limb");
    (f.c0 as u128) | ((f.c1 as u128) << 64)
}

fn f192_literal(f: F192) -> String {
    format!("f192({},{},{})", f.c0, f.c1, f.c2)
}

/// Native replay of the VM's `blake3(cur, cur, nxt)` over two 128-bit words:
/// pack the two `F192` words into the four `F64` lanes the sponge compression
/// consumes, compress, and unpack.
///
/// Word→lane packing confirmed against the VM's blake3 opcode (`cpu::mod`
/// `blake3_self_hash_aliased_operands`): a `[F64;4]` operand loaded from two
/// 128-bit words is `[w0.c0, w0.c1, w1.c0, w1.c1]` (word-major, lo=c0 then
/// hi=c1), and the two output words pack back the same way
/// (`mem[out] == cell(d[0], d[1])`, `cell(d[2], d[3])`).
fn vmhash_compress2(st: [F192; 2]) -> [F192; 2] {
    let inb = [F64(st[0].c0), F64(st[0].c1), F64(st[1].c0), F64(st[1].c1)];
    let out = lean_vm::vmhash::compress(inb, inb);
    [F192::new(out[0].0, out[1].0, 0), F192::new(out[2].0, out[3].0, 0)]
}

/// Pack the sponge's four K lanes as two canonical 128-bit VM cells.
fn pack_state(s: [F64; 4]) -> [F192; 2] {
    [F192::new(s[0].0, s[1].0, 0), F192::new(s[2].0, s[3].0, 0)]
}

/// Pack a 32-byte Merkle node as the same canonical 128+128 cell pair used by
/// the VM's sole BLAKE3 representation.
fn pack_hash_state(hash: &[u8; 32]) -> [F192; 2] {
    let w = |o: usize| u64::from_le_bytes(hash[o..o + 8].try_into().unwrap());
    [F192::new(w(0), w(8), 0), F192::new(w(16), w(24), 0)]
}

/// The non-trivial inner program: a runtime-bounded BLAKE3 hash chain seeded
/// from the public input, a runtime-bounded `mul_range` product loop with heap
/// traffic, and a final assert tying them together. BOTH loop bounds ride
/// witness hints ("n_hash", "iters"), so a single program (one bytecode, one
/// digest) proves runs with wildly different opcode profiles and sizes - the
/// exact genericity the recursion guest is built for. Exercises every table
/// (XOR/MUL/SET/DEREF/JUMP/BLAKE3/PACK64X2).
fn inner_program() -> Program {
    let src = "from snark_lib import *\n\
        def main():\n\
        \x20   p = GEN ** 0\n\
        \x20   nh = HeapBuf(1)\n\
        \x20   hint_witness(nh[0:1], \"n_hash\")\n\
        \x20   hbound = nh[GEN ** 0]\n\
        \x20   assert log(hbound) < 65536\n\
        \x20   hc0 = HeapBuf(hbound * GEN)\n\
        \x20   hc1 = HeapBuf(hbound * GEN)\n\
        \x20   hc0[GEN ** 0] = p[1]\n\
        \x20   hc1[GEN ** 0] = p[GEN]\n\
        \x20   for h in mul_range(1, hbound):\n\
        \x20       cur = StackBuf(2)\n\
        \x20       cur[0] = hc0[h]\n\
        \x20       cur[1] = hc1[h]\n\
        \x20       nxt = StackBuf(2)\n\
        \x20       blake3(cur, cur, nxt)\n\
        \x20       hc0[h * GEN] = nxt[0]\n\
        \x20       hc1[h * GEN] = nxt[1]\n\
        \x20   st0 = hc0[hbound]\n\
        \x20   s1 = hc1[hbound]\n\
        \x20   nb = HeapBuf(1)\n\
        \x20   hint_witness(nb[0:1], \"iters\")\n\
        \x20   bound = nb[GEN ** 0]\n\
        \x20   assert log(bound) < 65536\n\
        \x20   buf = HeapBuf(bound)\n\
        \x20   acc = HeapBuf(bound * GEN)\n\
        \x20   acc[GEN ** 0] = st0\n\
        \x20   for x in mul_range(1, bound):\n\
        \x20       buf[x] = acc[x] * acc[x] + s1\n\
        \x20       acc[x * GEN] = buf[x] + x\n\
        \x20   out = acc[bound]\n\
        \x20   nz = HeapBuf(1)\n\
        \x20   hint_witness(nz[0:1], \"outinv\")\n\
        \x20   prod = out * nz[GEN ** 0]\n\
        \x20   assert prod == 1\n\
        \x20   return\n";
    compile(&parse(src).expect("parse inner"))
}

/// Prove one run of the inner program: `hashes` BLAKE3 compressions then
/// `iters` product-loop steps (both runtime, driven by the witness hints).
/// The witness generator replays both natively to supply the final-inverse
/// hint. Returns (program, proof, guest-cycle count, committed witness size).
fn prove_inner(
    pi: [F192; 2],
    hashes: usize,
    iters: usize,
    log_inv_rate: usize,
) -> (Program, lean_vm::cpu::Proof, usize, usize) {
    assert!(hashes >= 1 && iters >= 1, "both loops run at least once");
    let mut program = inner_program();
    // Replay natively: the hash chain, then the product loop, to fetch the
    // final accumulator (nonzero, for the hinted-inverse assert).
    let mut st = [pi[0], pi[1]];
    for _ in 0..hashes {
        st = vmhash_compress2(st);
    }
    let mut acc = st[0];
    let mut x = F192::ONE;
    let g = F192::new(primitives::field::g_pow(1).0, 0, 0); // embedded base generator
    for _ in 0..iters {
        let b = acc * acc + st[1];
        acc = b + x;
        x *= g;
    }
    let out = acc;
    assert!(out != F192::ZERO, "inner accumulator must be nonzero");
    program.set_witness("outinv", vec![vec![out.inv()]]);
    program.set_witness("n_hash", vec![vec![F192::new(g_pow(hashes).0, 0, 0)]]);
    program.set_witness("iters", vec![vec![F192::new(g_pow(iters).0, 0, 0)]]);
    let (proof, stats) = prove(&program, pi, log_inv_rate);
    // Reported once, by `run_recursion_with_rates` from `Batch::inner_stats`. The
    // inner guest's own work, not its filled row count, so the figure means the same
    // thing as the outer one.
    (program, proof, stats.base_counts.iter().sum(), stats.committed)
}

/// The deferred-claim data the guest binds to the outer public input: the outer
/// verifier checks each claim natively (`doc/main.tex` §Deferred evaluation claims;
/// n_rec = 1 forwards fresh claims without batching).
struct DeferredSubproof {
    public_input: [F192; 2],
    bytecode_log: usize,
    bytecode_row_point: Vec<F192>,
    bytecode_selector_point: Vec<F192>,
    bytecode_value: F192,
    matrix_a_coefficient: F192,
    skip_point: F192,
    zerocheck_row_point: Vec<F192>,
    lincheck_round_point: Vec<F192>,
    lincheck_terminal_values: Vec<F192>,
    matrix_claim: F192,
}

/// The deferred claims the aggregation exports: one point and value on
/// the stacked bytecode polynomial, one point + two values on the flock
/// matrices (`doc/main.tex` §Deferred evaluation claims).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct DeferredClaims {
    bytecode_point: Vec<F192>,
    bytecode_value: F192,
    matrix_point: Vec<F192>,
    matrix_a_value: F192,
    matrix_b_value: F192,
}

/// Everything committed by the outer public input. Keeping this private makes
/// the deferred claims an implementation detail of recursive verification.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct RecursiveStatement {
    sub_statements: Vec<[F192; 2]>,
    reduced: DeferredClaims,
}

impl RecursiveStatement {
    fn public_input(&self, inner_environment: [F192; 2]) -> [F192; 2] {
        let mut sponge = Sponge::new(RECURSION_STATEMENT_LABEL, &[]);
        sponge.observe(nsub_word(self.sub_statements.len()));
        for &v in &inner_environment {
            sponge.observe(v);
        }
        for statement in &self.sub_statements {
            for &v in statement {
                sponge.observe(v);
            }
        }
        for &v in &self.reduced.bytecode_point {
            sponge.observe(v);
        }
        sponge.observe(self.reduced.bytecode_value);
        for &v in &self.reduced.matrix_point {
            sponge.observe(v);
        }
        sponge.observe(self.reduced.matrix_a_value);
        sponge.observe(self.reduced.matrix_b_value);
        pack_state(sponge.state())
    }
}

/// A complete N→1 recursive proof.
///
/// Its contents are deliberately opaque. [`RecursiveProof::verify`] is the
/// only acceptance path and checks both the outer VM proof and the fixed
/// polynomial evaluations deferred by the recursion guest.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RecursiveProof {
    statement: RecursiveStatement,
    outer_proof: lean_vm::cpu::Proof,
}

impl RecursiveProof {
    /// Statements aggregated by this proof, in transcript order.
    pub fn sub_statements(&self) -> &[[F192; 2]] {
        &self.statement.sub_statements
    }

    /// Verify the complete recursive proof against the expected inner program.
    pub fn verify(&self, inner_program: &Program) -> Result<(), RecursiveVerifyError> {
        let statement = &self.statement;
        if statement.sub_statements.is_empty() {
            return Err(RecursiveVerifyError::EmptyBatch);
        }
        // Verification only reads the compiled guest; prover witness streams
        // live on owned clones.
        let guest = recursion_guest_arc(inner_program);
        let public_input = statement.public_input(lean_vm::cpu::fs_seed(inner_program));
        verify(&guest, &public_input, &self.outer_proof).map_err(RecursiveVerifyError::OuterProof)?;
        check_deferred_claims(inner_program, &statement.reduced)
    }
}

#[derive(Clone, Debug)]
pub enum RecursiveVerifyError {
    EmptyBatch,
    InvalidDeferredShape,
    OuterProof(lean_vm::cpu::Error),
    BytecodeClaim,
    MatrixAClaim,
    MatrixBClaim,
}

fn fold_lsb(t: &mut Vec<F192>, r: F192) {
    let half = t.len() / 2;
    for i in 0..half {
        t[i] = t[2 * i] + r * (t[2 * i] + t[2 * i + 1]);
    }
    t.truncate(half);
}

/// Compressed product-sumcheck round message over γ-weighted table pairs:
/// (g1, g∞) with g0 recovered from the running claim.
fn round_msg(pairs: &[(&[F192], &[F192], F192)]) -> (F192, F192) {
    let (mut g1, mut gi) = (F192::ZERO, F192::ZERO);
    for &(u, m, gamma) in pairs {
        let (mut a1, mut ai) = (F192::ZERO, F192::ZERO);
        for i in 0..u.len() / 2 {
            a1 += u[2 * i + 1] * m[2 * i + 1];
            ai += (u[2 * i] + u[2 * i + 1]) * (m[2 * i] + m[2 * i + 1]);
        }
        g1 += gamma * a1;
        gi += gamma * ai;
    }
    (g1, gi)
}

/// One round of a batching sumcheck, in the transcript order the guest mirrors
/// word for word: observe `(g1, g_inf)`, squeeze the fold challenge, record
/// both, and advance the running claim through the compressed round polynomial.
/// Returns the challenge, which the caller folds its tables with.
fn absorb_round(
    h: &mut Sponge,
    msgs: &mut Vec<F192>,
    points: &mut Vec<F192>,
    run: &mut F192,
    (g1, gi): (F192, F192),
) -> F192 {
    h.observe(g1);
    h.observe(gi);
    let r = h.sample();
    msgs.extend([g1, gi]);
    points.push(r);
    let g0 = *run + g1;
    let c1 = g0 + g1 + gi;
    *run = (gi * r + c1) * r + g0;
    r
}

/// The stacked bytecode polynomial of the inner program (leaf's canonical
/// table, built from the real layout).
fn stacked_bytecode(program: &Program) -> Vec<F64> {
    // Public bytecode coordinates depend only on the program. The remaining
    // layout inputs affect private witness/table shapes, so fixed valid dummy
    // sizes are sufficient and avoid retaining a representative inner proof.
    let l = lean_vm::cpu::layout(
        &program.prog,
        20,
        [1usize << 10; lean_vm::tables::N_TABLES],
        [F192::ZERO; 2],
    );
    lean_vm::leaf::stacked_bytecode_table(&l.push)
}

/// Mirror the guest's aggregation transcript and prove the two batching
/// sumchecks: dense for bytecode and two-phase sparse for the matrices. Returns
/// the guest hints, deferred claims, and outer public input.
#[allow(clippy::type_complexity)]
fn aggregate_deferred_claims(
    program: &Program,
    subs: &[DeferredSubproof],
) -> (Vec<(String, Vec<F192>)>, [F192; 2], DeferredClaims) {
    let nsub = subs.len();
    let kbc = subs[0].bytecode_log;
    let kbcv = kbc + lean_vm::leaf::N_BYTECODE_SELECTORS;
    let klog = flock::blake3::K_LOG;

    // ---- the aggregation transcript (mirrors the guest exactly) ----
    let mut h = Sponge::new(RECURSION_AGG_LABEL, &[]);
    h.observe(nsub_word(nsub));
    for d in subs {
        h.observe(d.public_input[0]);
        h.observe(d.public_input[1]);
        for &v in &d.bytecode_row_point {
            h.observe(v);
        }
        for &v in &d.bytecode_selector_point {
            h.observe(v);
        }
        h.observe(d.bytecode_value);
        h.observe(d.matrix_a_coefficient);
        h.observe(d.skip_point);
        for &v in &d.zerocheck_row_point {
            h.observe(v);
        }
        for &v in &d.lincheck_round_point {
            h.observe(v);
        }
        for &v in &d.lincheck_terminal_values {
            h.observe(v);
        }
        h.observe(d.matrix_claim);
    }

    // ---- bytecode batching sumcheck (dense, 2^kbcv; ONE claim per sub, at
    // the shared push/pull point) ----
    let gbc: Vec<F192> = (0..nsub).map(|_| h.sample()).collect();
    let mut bt: Vec<F192> = stacked_bytecode(program)
        .into_iter()
        .map(|x| F192::new(x.0, 0, 0))
        .collect();
    let mut wt = vec![F192::ZERO; 1 << kbcv];
    let points: Vec<Vec<F192>> = subs
        .iter()
        .map(|d| {
            d.bytecode_row_point
                .iter()
                .chain(&d.bytecode_selector_point)
                .copied()
                .collect::<Vec<_>>()
        })
        .collect();
    for (t, p) in points.iter().enumerate() {
        let eqt = pcs::whir::build_eq_table_ext(p);
        for (w, &e) in wt.iter_mut().zip(eqt.iter()) {
            *w += gbc[t] * e;
        }
    }
    let mut brun: F192 = (0..nsub)
        .map(|t| gbc[t] * subs[t].bytecode_value)
        .fold(F192::ZERO, |a, x| a + x);
    let mut bscr = Vec::new();
    let mut r_bc = Vec::new();
    for _ in 0..kbcv {
        let msg = round_msg(&[(&bt, &wt, F192::ONE)]);
        let r = absorb_round(&mut h, &mut bscr, &mut r_bc, &mut brun, msg);
        fold_lsb(&mut bt, r);
        fold_lsb(&mut wt, r);
    }
    let v_bc = bt[0];
    assert_eq!(brun, v_bc * wt[0], "bytecode sumcheck terminal");

    // ---- matrix batching sumcheck (two-phase sparse, per the probe) ----
    let gmt: Vec<F192> = (0..nsub).map(|_| h.sample()).collect();
    let (ma, mb) = flock::blake3::matrices();
    // per-claim dense weight tables: rows = quirky eq, cols = eq(top rounds) x z_partial.
    let mut us: Vec<Vec<F192>> = subs
        .iter()
        .map(|d| flock::lincheck::build_quirky_eq_table(d.skip_point, &d.zerocheck_row_point, 6))
        .collect();
    let ws: Vec<Vec<F192>> = subs
        .iter()
        .map(|d| {
            (0..1usize << klog)
                .map(|c| {
                    let mut w = d.lincheck_terminal_values[c & 63];
                    for (j, &rj) in d.lincheck_round_point.iter().enumerate() {
                        let bit = (c >> (klog - 1 - j)) & 1;
                        w *= if bit == 1 { rj } else { F192::ONE + rj };
                    }
                    w
                })
                .collect()
        })
        .collect();
    let contract_cols = |m: &flock::r1cs::SparseBinaryMatrix, w: &[F192]| -> Vec<F192> {
        m.rows
            .iter()
            .map(|row| row.iter().map(|&j| w[j]).fold(F192::ZERO, |a, x| a + x))
            .collect()
    };
    let mut ms: Vec<Vec<F192>> = Vec::new();
    for w in &ws {
        ms.push(contract_cols(ma, w));
        ms.push(contract_cols(mb, w));
    }
    let ga: Vec<F192> = (0..nsub).map(|t| gmt[t] * subs[t].matrix_a_coefficient).collect();
    let gb: Vec<F192> = gmt.clone();
    let mut mrun: F192 = (0..nsub)
        .map(|t| gmt[t] * subs[t].matrix_claim)
        .fold(F192::ZERO, |a, x| a + x);
    // sanity: the deferred matpart equals the bilinear form over the matrices.
    #[cfg(debug_assertions)]
    for (t, d) in subs.iter().enumerate() {
        let direct = d.matrix_a_coefficient
            * ms[2 * t]
                .iter()
                .zip(&us[t])
                .map(|(&m, &u)| m * u)
                .fold(F192::ZERO, |a, x| a + x)
            + ms[2 * t + 1]
                .iter()
                .zip(&us[t])
                .map(|(&m, &u)| m * u)
                .fold(F192::ZERO, |a, x| a + x);
        assert_eq!(direct, d.matrix_claim, "matrix bilinear identity, sub {t}");
    }
    let mut mscr = Vec::new();
    let mut r_row = Vec::new();
    for _ in 0..klog {
        let pairs: Vec<(&[F192], &[F192], F192)> = (0..nsub)
            .flat_map(|t| {
                [
                    (&us[t][..], &ms[2 * t][..], ga[t]),
                    (&us[t][..], &ms[2 * t + 1][..], gb[t]),
                ]
            })
            .collect();
        let msg = round_msg(&pairs);
        let r = absorb_round(&mut h, &mut mscr, &mut r_row, &mut mrun, msg);
        for u in us.iter_mut() {
            fold_lsb(u, r);
        }
        for m in ms.iter_mut() {
            fold_lsb(m, r);
        }
    }
    let eq_rstar = pcs::whir::build_eq_table_ext(&r_row);
    let contract_rows = |m: &flock::r1cs::SparseBinaryMatrix| -> Vec<F192> {
        let mut out = vec![F192::ZERO; 1 << klog];
        for (i, row) in m.rows.iter().enumerate() {
            let e = eq_rstar[i];
            for &j in row {
                out[j] += e;
            }
        }
        out
    };
    let mut acol = contract_rows(ma);
    let mut bcol = contract_rows(mb);
    let mut wa = vec![F192::ZERO; 1 << klog];
    let mut wb = vec![F192::ZERO; 1 << klog];
    for t in 0..nsub {
        let (sa, sb2) = (ga[t] * us[t][0], gb[t] * us[t][0]);
        for j in 0..1 << klog {
            wa[j] += sa * ws[t][j];
            wb[j] += sb2 * ws[t][j];
        }
    }
    let mut r_col = Vec::new();
    for _ in 0..klog {
        let pairs: Vec<(&[F192], &[F192], F192)> = vec![(&acol, &wa, F192::ONE), (&bcol, &wb, F192::ONE)];
        let msg = round_msg(&pairs);
        let r = absorb_round(&mut h, &mut mscr, &mut r_col, &mut mrun, msg);
        for tb in [&mut acol, &mut bcol, &mut wa, &mut wb] {
            fold_lsb(tb, r);
        }
    }
    let (v_a, v_b) = (acol[0], bcol[0]);
    assert_eq!(mrun, v_a * wa[0] + v_b * wb[0], "matrix sumcheck terminal");
    // sanity for the GUEST's succinct terminal-weight formulas.
    #[cfg(debug_assertions)]
    {
        let eqr = pcs::whir::build_eq_table_ext(&r_row[..6]);
        let eqc = pcs::whir::build_eq_table_ext(&r_col[..6]);
        let (mut wam, mut wbm) = (F192::ZERO, F192::ZERO);
        for (t, d) in subs.iter().enumerate() {
            let lam = primitives::multilinear::lagrange_weights_naive(6, d.skip_point);
            let mut urow: F192 = (0..64).map(|i| lam[i] * eqr[i]).fold(F192::ZERO, |a, x| a + x);
            for (k, &z) in d.zerocheck_row_point.iter().enumerate() {
                urow *= F192::ONE + z + r_row[6 + k];
            }
            let mut wcol: F192 = (0..64)
                .map(|i| d.lincheck_terminal_values[i] * eqc[i])
                .fold(F192::ZERO, |a, x| a + x);
            for (j, &rj) in d.lincheck_round_point.iter().enumerate() {
                wcol *= F192::ONE + rj + r_col[klog - 1 - j];
            }
            let u = urow * wcol;
            wam += ga[t] * u;
            wbm += gb[t] * u;
        }
        assert_eq!(mrun, v_a * wam + v_b * wbm, "guest terminal-weight formulas");
    }

    // ---- outer public input: FS seed + sub statements + reduced claims ----
    // The inner proving environment (flock circuit family + program bytecode)
    // is identified by ONE seed digest in the recursion's PUBLIC INPUT (not
    // baked into the guest), so one compiled guest serves any inner program.
    let seed = lean_vm::cpu::fs_seed(program);
    let mut e = Sponge::new(RECURSION_STATEMENT_LABEL, &[]);
    e.observe(nsub_word(nsub));
    e.observe(seed[0]);
    e.observe(seed[1]);
    for d in subs {
        e.observe(d.public_input[0]);
        e.observe(d.public_input[1]);
    }
    for &v in &r_bc {
        e.observe(v);
    }
    e.observe(v_bc);
    let r_m: Vec<F192> = r_row.iter().chain(&r_col).copied().collect();
    for &v in &r_m {
        e.observe(v);
    }
    e.observe(v_a);
    e.observe(v_b);

    let hints = vec![
        ("nsub".to_string(), vec![nsub_word(nsub)]),
        ("fs_seed".to_string(), vec![seed[0], seed[1]]),
        ("bc_sumcheck_msgs".to_string(), bscr),
        ("mat_sumcheck_msgs".to_string(), mscr),
        ("bc_star_hint".to_string(), vec![v_bc]),
        ("mat_stars_hint".to_string(), vec![v_a, v_b]),
    ];
    (
        hints,
        pack_state(e.state()),
        DeferredClaims {
            bytecode_point: r_bc,
            bytecode_value: v_bc,
            matrix_point: r_m,
            matrix_a_value: v_a,
            matrix_b_value: v_b,
        },
    )
}

/// Discharge the three fixed-polynomial claims deferred by the guest.
fn check_deferred_claims(program: &Program, claims: &DeferredClaims) -> Result<(), RecursiveVerifyError> {
    let stacked = stacked_bytecode(program);
    let expected_bc = stacked.len().trailing_zeros() as usize;
    if claims.bytecode_point.len() != expected_bc {
        return Err(RecursiveVerifyError::InvalidDeferredShape);
    }
    if mle_eval(&stacked, &claims.bytecode_point) != claims.bytecode_value {
        return Err(RecursiveVerifyError::BytecodeClaim);
    }
    let klog = flock::blake3::K_LOG;
    if claims.matrix_point.len() != 2 * klog {
        return Err(RecursiveVerifyError::InvalidDeferredShape);
    }
    let eq_r = pcs::whir::build_eq_table_ext(&claims.matrix_point[..klog]);
    let eq_c = pcs::whir::build_eq_table_ext(&claims.matrix_point[klog..]);
    let (v_a, v_b) = flock::blake3::bilinear_walk_pair(&eq_r, &eq_c);
    if v_a != claims.matrix_a_value {
        return Err(RecursiveVerifyError::MatrixAClaim);
    }
    if v_b != claims.matrix_b_value {
        return Err(RecursiveVerifyError::MatrixBClaim);
    }
    Ok(())
}

/// The verifier-side WHIR config for one committed size and rate, plus the
/// query packing derived from it. The hint builder needs it for the real
/// opening and the placeholder map for every candidate size, so it lives here:
/// a candidate whose shape differed from the real one would compile a guest
/// that cannot open the proof it is handed.
struct WhirShape {
    config: pcs::whir::VerifierConfig,
    levels: pcs::whir::LevelShapes,
    /// Merkle tree depth per level.
    depth: Vec<usize>,
    /// Query positions carried by one squeezed F192 word, per level.
    per_squeeze: Vec<usize>,
}

fn whir_shape(mu: usize, log_inv_rate: usize) -> WhirShape {
    let config = pcs::whir::WhirSecurityConfig::derive_config_with_log_inv_rate(mu + pcs::LOG_PACKING, log_inv_rate)
        .and_then(|s| s.to_prover_verifier_configs())
        .expect("stacked whir config")
        .1;
    let levels = config.level_shapes(mu);
    let depth: Vec<usize> = levels.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    let per_squeeze = depth.iter().map(|&d| 192 / d).collect();
    WhirShape {
        config,
        levels,
        depth,
        per_squeeze,
    }
}

/// The BLAKE3 table's virtual value columns, in `blake3_flock::SLOTS` order.
fn blake3_value_columns() -> Vec<usize> {
    let base = lean_vm::cpu::schema().base[5];
    lean_vm::tables::BLAKE3_VALUE_COLS.iter().map(|&c| base + c).collect()
}

/// One entry of the guest's claim pool.
enum ClaimSite {
    /// A framework bus block reads a committed column at this kappa.
    Framework { column: usize, kappa: usize },
    /// A committed column of `table`; `is_virtual` marks the q_flock-backed value
    /// columns, whose claim is a strided slot rather than a plain column.
    TableColumn {
        table: usize,
        column: usize,
        is_virtual: bool,
    },
    /// One of the three PI memory limbs (MEM_LO, MEM_HI, MEM_TOP).
    MemoryLimb { column: usize },
}

/// The guest's `COORD_KIND_*` code for a coordinate (`guests/recursion.py`),
/// shared by its `COORD_TYPE` and `TERM_TYPE` arrays.
fn coord_kind(c: &Coord) -> usize {
    match c {
        Coord::Const(_) => 0,
        Coord::Col(_) => 1,
        Coord::GCol(..) => 2,
        Coord::Index => 3,
        Coord::Public(_) => 4,
        Coord::Prod(..) => 5,
        Coord::Sum(..) => 6,
    }
}

/// The `K` scalar a coordinate carries beside its columns: the constant itself,
/// or the `g^k` a `GCol`/`Prod` scales by. Zero for every other kind.
fn coord_scale(c: &Coord) -> F192 {
    match c {
        Coord::Const(v) => F192::new(v.0, 0, 0),
        Coord::GCol(_, k) | Coord::Prod(_, _, k) => F192::new(g_pow(*k as usize).0, 0, 0),
        _ => F192::ZERO,
    }
}

/// Flatten one table-block coordinate into the guest's term arrays, in local
/// column indices. A [`Coord::Sum`]'s children are its terms; every other kind is
/// one term. `Index`/`Public` never reach a table block.
fn push_coord_terms(
    c: &Coord,
    base: usize,
    ty: &mut Vec<usize>,
    val: &mut Vec<u128>,
    col_a: &mut Vec<usize>,
    col_b: &mut Vec<usize>,
) {
    let (a, b) = match c {
        Coord::Const(_) => (0, 0),
        Coord::Col(i) | Coord::GCol(i, _) => (*i - base, 0),
        Coord::Prod(i, j, _) => (*i - base, *j - base),
        Coord::Sum(cs) => {
            for c in cs {
                push_coord_terms(c, base, ty, val, col_a, col_b);
            }
            return;
        }
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    };
    ty.push(coord_kind(c));
    val.push(u(coord_scale(c)));
    col_a.push(a);
    col_b.push(b);
}

/// Visit the claim pool in the exact order the guest indexes it: the framework
/// bus claims (deduped by `(column, kappa)`, as `leaf.rs` pools them), then every
/// table's committed columns, then the PI memory triple. Both the per-sub hints
/// and the placeholder map descriptors are built from this one walk, so the two
/// stay index-aligned by construction rather than by two matching count asserts.
fn walk_claims(l: &lean_vm::cpu::Layout, kbc: usize, mut visit: impl FnMut(ClaimSite)) {
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let valcols = blake3_value_columns();
    // Only the framework blocks raise claims: a table's coords are settled inside
    // the table sumcheck.
    let is_framework: Vec<bool> = lean_vm::cpu::block_kappa_sources(kbc)
        .into_iter()
        .map(|(src, _)| src < 2)
        .collect();
    let mut seen: std::collections::HashSet<(usize, usize)> = Default::default();
    let mut bi = 0usize;
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            let framework = is_framework[bi];
            bi += 1;
            if !framework {
                continue;
            }
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i, _) = c {
                    if !seen.insert((*i, blk.kappa)) {
                        continue; // deduped: pooled once at its first occurrence
                    }
                    assert!(!valcols.contains(i), "{VALCOL_FRAMEWORK}");
                    visit(ClaimSite::Framework {
                        column: *i,
                        kappa: blk.kappa,
                    });
                }
            }
        }
    }
    let sch = lean_vm::cpu::schema();
    for (t, table) in lean_vm::tables::tables().iter().enumerate() {
        for c in 0..table.n_committed_columns() {
            let column = sch.base[t] + c;
            visit(ClaimSite::TableColumn {
                table: t,
                column,
                is_virtual: l.placements[column].is_virtual(),
            });
        }
    }
    for &column in &[lean_vm::cpu::MEM_LO, lean_vm::cpu::MEM_HI, lean_vm::cpu::MEM_TOP] {
        visit(ClaimSite::MemoryLimb { column });
    }
}

/// Config + hints for the recursion guest (`guests/recursion.py`), built
/// from the REAL `cpu::layout` of the inner program and the transcript trace of
/// a real `cpu::verify` run (zero hand-mirroring drift).
fn gen_verify(
    program: &Program,
    pi: [F192; 2],
    proof: &lean_vm::cpu::Proof,
    summary: &lean_vm::cpu::VerifySummary,
    ops: &[TraceOp],
) -> (Vec<(String, Vec<F192>)>, DeferredSubproof) {
    let l = lean_vm::cpu::layout(
        &program.prog,
        proof.stream[0].c0 as usize,
        std::array::from_fn(|i| proof.stream[1 + i].c0 as usize),
        pi,
    );
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let lays: Vec<lean_vm::leaf::Layout> = sides.iter().map(|b| lean_vm::leaf::layout(b)).collect();
    let smu: Vec<usize> = lays.iter().map(|x| x.mu).collect();
    // Fixed capacities: every buffer/stride placeholder is a global cap so
    // the placeholder map is SHAPE-INDEPENDENT (the definition of generic).
    let mumax = 40usize;
    let stream_cap = 8192usize;
    assert!(*smu.iter().max().unwrap() <= mumax && proof.stream.len() <= stream_cap);

    // ---- pool sizes (the descriptors themselves are baked by `placeholder_map`) ----
    let mut nclaims = 0usize;
    // Claim dedup (mirrors leaf.rs): ALL three trees share their GKR point, so
    // a column read by two same-kappa blocks streams/opens once. Key: (col, kappa).
    let mut seen_claims: std::collections::HashSet<(usize, usize)> = Default::default();
    // Only the framework blocks raise claims: a table's coords are settled inside
    // the table sumcheck. Indexed by block, in `sides` order.
    let is_framework: Vec<bool> = lean_vm::cpu::block_kappa_sources(program.prog.len().trailing_zeros() as usize)
        .into_iter()
        .map(|(src, _)| src < 2)
        .collect();
    let mut vi = 0usize;
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            let framework = is_framework[vi];
            vi += 1;
            for c in &blk.coords {
                match c {
                    Coord::Col(i) | Coord::GCol(i, _) => {
                        if framework && seen_claims.insert((*i, blk.kappa)) {
                            nclaims += 1;
                        }
                    }
                    // A public coordinate raises no claim of its own: the program's
                    // whole share is one deferred evaluation (§sec:e2e-bc). Nor does a
                    // degree-2 coordinate, which lives only in a table block.
                    Coord::Public(_) | Coord::Const(_) | Coord::Index | Coord::Prod(..) | Coord::Sum(..) => {}
                }
            }
        }
    }

    // ---- typed extraction: proof structs + the verifier's summary ----
    // Drift check: replaying the recorded trace from the seed must reproduce
    // every challenge and grind the native run produced.
    let fs_seed = lean_vm::cpu::fs_seed(program);
    let seed = Sponge::new(b"leanvm-b", &[fs_seed[0], fs_seed[1], pi[0], pi[1]]);
    seed.clone().replay(ops);

    // Grinding digests are the only trace-borne data (they are functions of
    // sponge states): fold grinds carry bits > 0 and query-phase grinds carry
    // bits = 0.
    let pows: Vec<(F192, u32, F64)> = ops
        .iter()
        .filter_map(|op| match op {
            TraceOp::Pow { nonce, bits, digest } => Some((*nonce, *bits, *digest)),
            _ => None,
        })
        .collect();
    // Bus: the bytecode claims carry the push/pull ζ_lo points and sb.
    let kbc = summary.bytecode_claims[0].point.len() - lean_vm::leaf::N_BYTECODE_SELECTORS;
    let zeta: Vec<F192> = summary.bytecode_claims[0].point[..kbc].to_vec();
    let sb: Vec<F192> = summary.bytecode_claims[0].point[kbc..].to_vec();

    let taus = l.taus;
    // Flock replay data, all named struct fields.
    let n_log_b3 = l.taus[5];
    let lcrounds = flock::blake3::K_LOG - 6;
    let zcf = [summary.zc_claim.a_eval, summary.zc_claim.b_eval];
    let zc_z = summary.zc_claim.z;
    let zrho = summary.zc_claim.mlv_challenges.clone();
    let lc_alpha = summary.lc_claim.alpha;
    let lc_beta = summary.lc_claim.beta;
    let lrr = summary.lc_claim.r_rounds.clone();

    let evtot_e: usize = lean_vm::tables::tables().iter().map(|t| t.n_committed_columns()).sum();
    let ncl = nclaims + evtot_e + 3; // bus + constraint + the three PI memory-limb claims

    // ---- the stacked opening: config + the opening summary ----
    let stack = whir_shape(l.m, summary.log_inv_rate);
    let (vcfg, shapes) = (&stack.config, &stack.levels);
    let (nlev, r) = (shapes.levels, vcfg.level_steps);
    let klvl = &shapes.ks;
    let queries = &vcfg.queries;
    let (depth, per) = (&stack.depth, &stack.per_squeeze);
    let fgb = |lvl: usize| vcfg.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;

    // flock's reduction ends at `flock_stream_end`, where the WHIR opening's own
    // scalars start: its last 64 scalars are lincheck's `z_partial`, immediately
    // preceded by the `(e1, e_inf)` pairs of the `lcrounds` lincheck rounds.
    let ns = summary.flock_stream_end;
    let lcr: Vec<F192> = proof.stream[ns - 64 - 2 * lcrounds..ns - 64].to_vec();
    let lcz: Vec<F192> = proof.stream[ns - 64..ns].to_vec();

    // matpart = the deferred weighted matrix evaluation: the lincheck running
    // claim minus (= plus, char 2) the const-pin contribution.
    let r1cs = flock::blake3::build_block_r1cs(n_log_b3);
    let pincol = r1cs.const_pin.expect("blake3 r1cs has a const pin");
    let mut lrun = lc_alpha * zcf[0] + zcf[1] + lc_beta;
    for i in 0..lcrounds {
        let (e1, ei, rv) = (lcr[2 * i], lcr[2 * i + 1], lrr[i]);
        let e0 = lrun + e1;
        let c1q = e0 + e1 + ei;
        lrun = (ei * rv + c1q) * rv + e0;
    }
    let mut pinw = lc_beta;
    for (j, &rv) in lrr.iter().enumerate() {
        let bit = (pincol >> (flock::blake3::K_LOG - 1 - j)) & 1;
        pinw *= if bit == 1 { rv } else { F192::ONE + rv };
    }
    pinw *= lcz[pincol % 64];
    let matpart = lrun + pinw;

    let whir_raw = summary.opening.lig.query_squeezes.clone();
    // Grind sanity: in transcript order, per level, the fold grinds (bits > 0
    // per the config schedule) then ONE query-phase
    // grind. The nonces themselves ride the shared stream now (raw words);
    // the trace is only cross-checked here.
    let qbits: Vec<u32> = (0..nlev).map(|lvl| vcfg.grinding_bits[lvl] as u32).collect();
    let mut grinds = pows.iter();
    for lvl in 0..nlev {
        for j in 0..klvl[lvl] {
            let bits = (fgb(lvl) - j as i64).max(0) as u32;
            if bits > 0 {
                let &(_, b2, _) = grinds.next().expect("fold grind recorded");
                assert_eq!(b2, bits);
            }
        }
        let &(_, b2, _) = grinds.next().expect("query grind recorded");
        assert_eq!(b2, qbits[lvl], "level {lvl} query grind bits");
    }
    assert!(grinds.next().is_none(), "every grind consumed");

    // ---- hints ----
    // The program's whole share of a bytecode leaf: ONE value, the stacked
    // polynomial at (ζ_lo, α⃗), the slot coordinates of the claim's own point being
    // the fingerprint challenges (§sec:e2e-bc).
    let bytecode_value = summary.bytecode_claims[0].value;
    let bcv = vec![bytecode_value];

    // ---- per-sub HINT data (the placeholder map is built once, elsewhere) ----
    // Per side, the kappa-descending packing order (as in leaf.rs::layout):
    // sort_order[side_base + rank] = g^{side-local index of the rank-r block}.
    // The guest only perm-checks it and derives offsets; any aligned tiling is
    // sound, so this canonical order just has to match the committed leaf.
    let mut sort_order: Vec<F192> = Vec::new();
    let mut gbase = 0usize;
    for blocks in sides.iter() {
        let n = blocks.len();
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by(|&a, &b| blocks[b].kappa.cmp(&blocks[a].kappa).then(a.cmp(&b)));
        for &i in &order {
            sort_order.push(F192::new(g_pow(gbase + i).0, 0, 0)); // g^{global block index}
        }
        gbase += n;
    }
    // The stacked commitment uses witness::placements_of: committed columns
    // sorted by descending kappa, then by their native column index. Transport
    // compact committed-column indices; the guest certifies the permutation,
    // ordering, and accumulated offsets before using them as claim selectors.
    let col_sources = lean_vm::cpu::col_kappa_sources(kbc);
    let committed_globals: Vec<usize> = col_sources
        .iter()
        .enumerate()
        .filter_map(|(i, source)| source.map(|_| i))
        .collect();
    let mut compact_col = vec![usize::MAX; col_sources.len()];
    for (compact, &global) in committed_globals.iter().enumerate() {
        compact_col[global] = compact;
    }
    let mut col_order = committed_globals.clone();
    col_order.sort_by_key(|&global| l.placements[global].offset);
    let col_sort_order: Vec<F192> = col_order
        .iter()
        .map(|&global| F192::new(g_pow(compact_col[global]).0, 0, 0))
        .collect();
    let log_mem = proof.stream[0].c0 as usize;

    // ---- Phase E2 hints (the stacked WHIR opening) ----
    let lig = &proof.openings[0];
    let numinter: Vec<usize> = klvl.iter().map(|&k| 1usize << k).collect();
    let lenris: usize = klvl.iter().sum();
    // positions per level from the packed squeezes.
    let positions: Vec<Vec<usize>> = (0..nlev)
        .map(|lv| {
            let d = depth[lv];
            let mut out = Vec::with_capacity(queries[lv]);
            for v in &whir_raw[lv] {
                for j in 0..per[lv].min(queries[lv] - out.len()) {
                    let off = j * d;
                    let limbs = [v.c0, v.c1, v.c2];
                    let (li, sh) = (off / 64, off % 64);
                    let mut chunk = limbs[li] >> sh;
                    if sh + d > 64 {
                        chunk |= limbs[li + 1] << (64 - sh);
                    }
                    out.push(chunk as usize & (shapes.block_len[lv] - 1));
                }
            }
            out
        })
        .collect();
    let path_of = |lv: usize| -> &Vec<[u8; 32]> {
        if lv == 0 {
            &lig.whir.initial_proof.merkle_proof
        } else if lv == r {
            &lig.whir.final_proof.merkle_proof
        } else {
            &lig.whir.recursive_proofs[lv - 1].merkle_proof
        }
    };
    // Level 0 rows are embedded F64 values. For levels ≥1, each F192 word is
    // flattened into three embedded limbs so the guest can reproduce the exact
    // 24-byte Merkle-leaf preimage before reconstructing the field value.
    let (mut lrows_flat, mut lpaths_flat): (Vec<F192>, Vec<F192>) = (Vec::new(), Vec::new());
    for lv in 0..nlev {
        let path_exp = if lv == 0 {
            let (rows_exp, path_exp) = pcs::whir::expand_level_opening_base(
                shapes.block_len[lv],
                &positions[lv],
                &lig.whir.initial_proof.opened_rows,
                numinter[lv],
                path_of(lv),
            )
            .expect("expand base (level 0) stacked opening");
            for row in &rows_exp {
                for &x in row {
                    lrows_flat.push(F192::new(x.0, 0, 0));
                }
            }
            path_exp
        } else {
            let rows_ref = if lv == r {
                &lig.whir.final_proof.opened_rows
            } else {
                &lig.whir.recursive_proofs[lv - 1].opened_rows
            };
            let (rows_exp, path_exp) = pcs::whir::expand_level_opening_ext(
                shapes.block_len[lv],
                &positions[lv],
                rows_ref,
                numinter[lv],
                path_of(lv),
            )
            .expect("expand ext (level ≥1) stacked opening");
            for row in &rows_exp {
                for &x in row {
                    lrows_flat.extend([F192::new(x.c0, 0, 0), F192::new(x.c1, 0, 0), F192::new(x.c2, 0, 0)]);
                }
            }
            path_exp
        };
        for &h in &path_exp {
            lpaths_flat.extend_from_slice(&pack_hash_state(&h));
        }
    }
    // claim descriptors, in exact clv order.
    let mut nover_v = Vec::new();
    walk_claims(&l, program.prog.len().trailing_zeros() as usize, |site| {
        // Per claim, `nvt` is the full low span; when it exceeds `lenris` the point
        // overlaps the residual y region by `nover` coords. Stack selectors are not
        // emitted: the guest derives them from the certified committed-column offsets.
        let nvt = match site {
            ClaimSite::Framework { kappa, .. } => kappa,
            ClaimSite::TableColumn { table, is_virtual, .. } => {
                if is_virtual {
                    lean_vm::blake3_flock::SLOT_STRIDE_LOG + taus[table]
                } else {
                    taus[table]
                }
            }
            // The three PI memory lanes share one point [r_m, 0, 0, ...]; the coords
            // beyond `lenris` are const zero, so they fold into the y pattern instead
            // of a runtime overlap factor.
            ClaimSite::MemoryLimb { column } => l.placements[column].n_vars.min(lenris),
        };
        nover_v.push(nvt.saturating_sub(lenris));
    });
    assert_eq!(nover_v.len(), ncl, "descriptor count == pool size");

    let deferred = DeferredSubproof {
        public_input: pi,
        bytecode_log: kbc,
        bytecode_row_point: zeta,
        bytecode_selector_point: sb.clone(),
        bytecode_value,
        matrix_a_coefficient: lc_alpha,
        skip_point: zc_z,
        zerocheck_row_point: zrho[..lcrounds].to_vec(),
        lincheck_round_point: lrr.clone(),
        lincheck_terminal_values: lcz.clone(),
        matrix_claim: matpart,
    };

    let hints = vec![
        ("stream".to_string(), {
            // The guest replays the WHIR opening off the same stream the native
            // verifier reads: every transmitted scalar (sumcheck messages, level
            // roots, OOD claims, grind nonces, `yr`) is already there in protocol
            // order, so there is nothing to reassemble. The guest's `open_stacked`
            // picks it up at `msg_cursor = cursor`, which sits where the flock
            // reduction stopped; the ring-switch messages are struct-observed and
            // still do not advance that cursor.
            let mut v = proof.stream.clone();
            assert!(
                v.len() <= stream_cap,
                "stream {} exceeds stream_cap {stream_cap}",
                v.len()
            );
            v.resize(stream_cap, F192::ZERO);
            v
        }),
        ("rs_shatv".to_string(), {
            // Only C's 64-entry ring-switch slice travels in the opening. The
            // guest reconstructs AB from lincheck's already-read z_partial.
            let lig = &proof.openings[0];
            let mut v = Vec::new();
            for rsw in &lig.ring_switches {
                v.extend_from_slice(&rsw.s_hat_v);
            }
            v
        }),
        ("bytecode_val".to_string(), bcv),
        ("matpart".to_string(), vec![matpart]),
        ("merkle_leaf_rows".to_string(), lrows_flat),
        ("merkle_paths".to_string(), lpaths_flat),
        ("sub_pis".to_string(), vec![pi[0], pi[1]]),
        // per-claim overlap count, for the exact length pin: nover = the
        // amount by which the claim's total vars exceed the fold rounds.
        (
            "claim_nover".to_string(),
            (0..ncl).map(|j| F192::new(g_pow(nover_v[j]).0, 0, 0)).collect(),
        ),
        // the pi claim's low dimension is min(log_mem, lenris); certify it as
        // a min (<= both, == one) so pi is pinned like every other claim.
        (
            "pi_cplen".to_string(),
            vec![F192::new(g_pow(log_mem.min(lenris)).0, 0, 0)],
        ),
        // the table sumcheck's round count: max_t tau_t, certified in-guest as a
        // maximum (one of the taus, and dominating them all).
        (
            "zc_tau_max".to_string(),
            vec![F192::new(g_pow(*taus.iter().max().unwrap()).0, 0, 0)],
        ),
        ("col_sort_order".to_string(), col_sort_order),
        ("sort_order".to_string(), sort_order.clone()),
    ];
    (hints, deferred)
}

/// The guest's stacked-size dispatch range: one `match_range` opening arm per
/// candidate `mu` in `MU_MIN..=MU_MAX` (mirrored by the soundness test's
/// residual-log cap).
const MU_MIN: usize = 22;
const MU_MAX: usize = 28;

/// Everything needed to run one N→1 recursion batch EXCEPT compiling the
/// guest: the merged per-sub witness entries, the outer statement, and the
/// data to discharge the reduced claims. Splitting the build from the compile
/// lets one compiled guest serve many batches (see `recursion_generic_many`).
struct Batch {
    merged: Vec<(String, Vec<Vec<F192>>)>,
    program0: Program,
    statement: RecursiveStatement,
    /// Per inner proof, in transcript order: (guest cycles, committed witness size).
    inner_stats: Vec<(usize, usize)>,
    outer_log_inv_rate: usize,
}

impl Batch {
    fn public_input(&self) -> [F192; 2] {
        self.statement.public_input(lean_vm::cpu::fs_seed(&self.program0))
    }

    /// Install this batch's generated hints and produce the complete proof
    /// bundle. Keeping assembly here makes it impossible for tests and callers
    /// to accidentally omit or mismatch one of the deferred components.
    fn prove(&self, guest: &mut Program) -> (RecursiveProof, lean_vm::cpu::Stats) {
        for (name, entries) in &self.merged {
            guest.set_witness(name, entries.clone());
        }
        let (outer_proof, stats) = prove(guest, self.public_input(), self.outer_log_inv_rate);
        (
            RecursiveProof {
                statement: self.statement.clone(),
                outer_proof,
            },
            stats,
        )
    }
}

/// Prove `inner.len()` inner runs (same program, distinct statements + shapes),
/// verify each inside the recursion guest, and assemble the aggregation inputs.
/// `inner[k] = (hashes, iters)` sets sub k's opcode profile.
fn build_batch(inner: &[(usize, usize)], log_inv_rates: &[usize], outer_log_inv_rate: usize) -> Batch {
    assert!(!inner.is_empty(), "a recursion batch cannot be empty");
    assert_eq!(inner.len(), log_inv_rates.len(), "one PCS rate per inner proof");
    let mut inner_stats = Vec::with_capacity(inner.len());
    let mut protos = Vec::new();
    for (k, (&(hashes, iters), &log_inv_rate)) in inner.iter().zip(log_inv_rates).enumerate() {
        let pi = [
            F192::new(0x1111_2222 + k as u64, 0x3333_4444, 0),
            F192::new(0x5555_6666, 0x7777_8888 + k as u64, 0),
        ];
        let (program, proof, inner_cycles, inner_committed) = prove_inner(pi, hashes, iters, log_inv_rate);
        inner_stats.push((inner_cycles, inner_committed));
        trace_start();
        let summary = verify(&program, &pi, &proof).expect("inner verifies");
        let ops = trace_take();
        protos.push((program, pi, proof, summary, ops));
    }
    let mut merged: Vec<(String, Vec<Vec<F192>>)> = Vec::new();
    let mut subs = Vec::new();
    for (program, pi, proof, summary, ops) in &protos {
        let (hints, defer) = gen_verify(program, *pi, proof, summary, ops);
        // one witness ENTRY per sub-proof and stream: verify_sub pops the
        // next entry of every stream on each call.
        if merged.is_empty() {
            merged = hints.into_iter().map(|(n, v)| (n, vec![v])).collect();
        } else {
            for ((name, acc), (n2, more)) in merged.iter_mut().zip(hints) {
                assert_eq!(*name, n2);
                acc.push(more);
            }
        }
        subs.push(defer);
    }
    let (program0, _, _, _, _) = &protos[0];
    let (agg_hints, gpi, reduced) = aggregate_deferred_claims(program0, &subs);
    merged.extend(agg_hints.into_iter().map(|(n, v)| (n, vec![v])));
    let statement = RecursiveStatement {
        sub_statements: subs.iter().map(|d| d.public_input).collect(),
        reduced,
    };
    assert_eq!(
        statement.public_input(lean_vm::cpu::fs_seed(program0)),
        gpi,
        "native recursive statement reconstruction must mirror the guest",
    );
    // Move the representative Program out (Program is not Clone) now that all
    // aggregation borrows have ended. No representative proof is retained.
    let (program0, _, _, _, _) = protos.swap_remove(0);
    Batch {
        merged,
        program0,
        statement,
        inner_stats,
        outer_log_inv_rate,
    }
}

struct OpeningShape {
    n_levels: usize,
    yr_level: usize,
    yr_log_len: usize,
    folds: Vec<usize>,
    log_message_columns: Vec<usize>,
    queries: Vec<usize>,
    tree_depths: Vec<usize>,
    positions_per_squeeze: Vec<usize>,
    squeezes: Vec<usize>,
    interleaving: Vec<usize>,
    query_grinding_bits: Vec<usize>,
    fold_grinding_bits: Vec<usize>,
    row_offsets: Vec<usize>,
    path_offsets: Vec<usize>,
    positions_offsets: Vec<usize>,
    vanish_offsets: Vec<usize>,
    fold_offsets: Vec<usize>,
    residual_fold_offsets: Vec<usize>,
    vanish_values: Vec<F192>,
    vanish_inverses: Vec<F192>,
    ood_samples: Vec<usize>,
}

/// The recursion program's placeholder map (the SHAPE-INDEPENDENT constants the
/// generic guest is compiled from), built from the inner program's STRUCTURE and
/// bytecode SIZE alone — no proof. Dummy layout sizes are fine: `rep` reads only the
/// size-independent block/coord structure and `kbc = log2(bytecode)`, so the guest
/// can be compiled BEFORE any inner proof exists. Because the map is a function of
/// the inner bytecode size alone, one compiled guest serves every shape.
fn placeholder_map(program: &Program) -> BTreeMap<String, String> {
    // Any valid sizes drive the layout — rep depends only on structure + kbc.
    let l = lean_vm::cpu::layout(
        &program.prog,
        20,
        [1usize << 10; lean_vm::tables::N_TABLES],
        [F192::ZERO, F192::ZERO],
    );
    let kbc = program.prog.len().trailing_zeros() as usize;
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let mumax = 40usize;
    let stream_cap = 8192usize;
    let taus = l.taus;
    let lcrounds = flock::blake3::K_LOG - 6;

    // ---- flattened block/coord descriptors (structural) ----
    let (mut sblk, mut bc0, mut bcn) = (vec![0usize], vec![], vec![]);
    let (mut ct, mut cval) = (vec![], vec![]);
    let (mut nclaims, mut nbcv, mut nblocks) = (0usize, 0usize, 0usize);
    // Claim dedup (mirrors leaf.rs): per coord, fresh = first (group, col,
    // kappa) occurrence gets the next pool slot; duplicates point at it.
    let mut slot_of: std::collections::HashMap<(usize, usize), usize> = Default::default();
    let (mut coord_fresh, mut coord_slot) = (vec![], vec![]);
    // A TABLE block's coordinates, flattened into terms: the guest rebuilds each as
    // `Σ_terms`, so a derived value (an XOR/MUL result, a DEREF store, a JUMP
    // successor) costs terms rather than columns. A framework coordinate has none:
    // it decomposes into pooled claims instead.
    let (mut coord_toff, mut coord_tcount) = (vec![], vec![]);
    let (mut term_type, mut term_const) = (vec![], vec![]);
    let (mut term_col_a, mut term_col_b) = (vec![], vec![]);
    // A table's blocks raise no claim any more: the table sumcheck settles them
    //, so only the framework blocks stream column values.
    let sch_pm = lean_vm::cpu::schema();
    let owner_pm: Vec<Option<usize>> = lean_vm::cpu::block_kappa_sources(kbc)
        .into_iter()
        .map(|(src, _)| src.checked_sub(2))
        .collect();
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            bc0.push(ct.len());
            bcn.push(blk.coords.len());
            let owner = owner_pm[nblocks];
            nblocks += 1;
            for c in &blk.coords {
                // One COORD_FRESH/COORD_CLAIM_SLOT entry PER coord (the guest
                // indexes them by global coord offset); only a framework block's
                // Col/GCol raises a claim.
                let (mut fresh, mut slot) = (0usize, 0usize);
                if let (Coord::Col(i) | Coord::GCol(i, _), None) = (c, owner) {
                    let key = (*i, blk.kappa);
                    if let Some(&known) = slot_of.get(&key) {
                        slot = known;
                    } else {
                        slot_of.insert(key, nclaims);
                        fresh = 1;
                        slot = nclaims;
                        nclaims += 1;
                    }
                }
                coord_fresh.push(fresh);
                coord_slot.push(slot);
                // A table's coord becomes terms; a framework one has none, having
                // decomposed into the pooled claim above.
                let toff = term_type.len();
                if let Some(t) = owner {
                    push_coord_terms(
                        c,
                        sch_pm.base[t],
                        &mut term_type,
                        &mut term_const,
                        &mut term_col_a,
                        &mut term_col_b,
                    );
                }
                coord_toff.push(toff);
                coord_tcount.push(term_type.len() - toff);
                nbcv += usize::from(matches!(c, Coord::Public(_)));
                ct.push(coord_kind(c) as u128);
                cval.push(u(coord_scale(c)));
            }
        }
        sblk.push(nblocks);
    }
    let evtot: usize = lean_vm::tables::tables().iter().map(|t| t.n_committed_columns()).sum();
    let ncl = nclaims + evtot + 3; // bus + constraint + the three PI memory-limb claims

    // ---- claim descriptor buffer ids (structural) ----
    let valcols = blake3_value_columns();
    let col_sources_pm = lean_vm::cpu::col_kappa_sources(kbc);
    let mut compact_col_pm = vec![usize::MAX; col_sources_pm.len()];
    let mut n_committed = 0usize;
    for (global, source) in col_sources_pm.iter().enumerate() {
        if source.is_some() {
            compact_col_pm[global] = n_committed;
            n_committed += 1;
        }
    }
    let qflock_compact = compact_col_pm[lean_vm::cpu::QFLOCK];
    assert_ne!(qflock_compact, usize::MAX, "QFLOCK must be committed");
    let (mut cpbuf, mut cpcol, mut cpqslot): (Vec<usize>, Vec<usize>, Vec<usize>) = (vec![], vec![], vec![]);
    // `cpbuf` codes are the guest's POINT_BUF_*: 0 zeta, 1 rho, 2 pi, 3 qflock-rho.
    walk_claims(&l, kbc, |site| match site {
        ClaimSite::Framework { column, .. } => {
            let compact = compact_col_pm[column];
            assert_ne!(compact, usize::MAX, "framework claim must target a committed column");
            cpbuf.push(0);
            cpcol.push(compact);
            cpqslot.push(0);
        }
        ClaimSite::TableColumn { column, is_virtual, .. } => {
            cpbuf.push(if is_virtual { 3 } else { 1 });
            cpcol.push(if is_virtual {
                qflock_compact
            } else {
                compact_col_pm[column]
            });
            cpqslot.push(if is_virtual {
                lean_vm::blake3_flock::SLOTS[valcols.iter().position(|&v| v == column).unwrap()]
            } else {
                0
            });
        }
        ClaimSite::MemoryLimb { column } => {
            cpbuf.push(2);
            cpcol.push(compact_col_pm[column]);
            cpqslot.push(0);
        }
    });
    assert_eq!(cpbuf.len(), ncl, "descriptor count == pool size");
    assert_eq!(cpcol.len(), ncl, "every descriptor has a committed-column target");
    assert_eq!(cpqslot.len(), ncl, "every descriptor has a fixed QFLOCK slot");

    // ---- the placeholder map ----
    let ints = |v: &[usize]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let us = |v: &[u128]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let flds = |v: &[F192]| {
        format!(
            "[{}]",
            v.iter().map(|&x| f192_literal(x)).collect::<Vec<_>>().join(", ")
        )
    };
    let mut rep = BTreeMap::new();
    let mut ps = |k: &str, v: String| {
        rep.insert(format!("{k}_PLACEHOLDER"), v);
    };
    ps("STREAM_CAP", stream_cap.to_string());
    ps("MIN_LOG_MEM", lean_vm::cpu::MIN_LOG_MEM.to_string());
    ps("INV_GEN", u(F192::new(G.inv().0, 0, 0)).to_string());
    // The table sumcheck sends its round polynomial WHOLE, at {0, 1, g, g^2}, so
    // it interpolates a cubic: one baked inverse denominator per node.
    {
        let q = primitives::multilinear::quad_nodes();
        for i in 0..4 {
            let den = (0..4).filter(|&j| j != i).fold(F192::ONE, |acc, j| acc * (q[i] + q[j]));
            ps(&format!("LAG4_INV_{i}"), f192_literal(den.inv()));
        }
    }
    ps("MU_CAP", mumax.to_string());
    ps("NO_TABLE", l.taus.len().to_string());
    ps("GKR_ROUNDS_CAP", (mumax * (mumax + 1) / 2 + mumax + 2).to_string());
    ps("GKR_POINTS_CAP", ((mumax + 1) * mumax).to_string());
    ps("SIDE_BLOCK_START", ints(&sblk));
    ps("N_BLOCKS", nblocks.to_string());
    let bks = lean_vm::cpu::block_kappa_sources(kbc);
    // Push and pull emit bus blocks in matched pairs, so their baked kappa-source
    // segments are identical; the guest computes only push's side total and
    // aliases pull's mu to push's on this basis.
    assert_eq!(
        bks[sblk[0]..sblk[1]],
        bks[sblk[1]..sblk[2]],
        "push/pull kappa sources must match"
    );
    ps(
        "BLOCK_KAPPA_SRC",
        ints(&bks.iter().map(|&(s, _)| s).collect::<Vec<_>>()),
    );
    ps(
        "BLOCK_KAPPA_ADJ",
        ints(&bks.iter().map(|&(_, a)| a).collect::<Vec<_>>()),
    );
    ps(
        "BLOCK_TABLE",
        ints(
            &bks.iter()
                .map(|&(s, _)| if s >= 2 { s - 2 } else { l.taus.len() })
                .collect::<Vec<_>>(),
        ),
    );
    let mut block_side = Vec::new();
    for (s, blocks) in sides.iter().enumerate() {
        block_side.extend(std::iter::repeat_n(s, blocks.len()));
    }
    ps("BLOCK_SIDE", ints(&block_side));
    ps("BLOCK_COORD_OFF", ints(&bc0));
    ps("BLOCK_COORD_COUNT", ints(&bcn));
    ps("COORD_TYPE", us(&ct));
    ps("COORD_CONST", us(&cval));
    ps("COORD_FRESH", ints(&coord_fresh));
    ps("COORD_CLAIM_SLOT", ints(&coord_slot));
    ps("COORD_TERM_OFF", ints(&coord_toff));
    ps("COORD_TERM_COUNT", ints(&coord_tcount));
    ps("TERM_TYPE", ints(&term_type));
    ps("TERM_CONST", us(&term_const));
    ps("TERM_COL_A", ints(&term_col_a));
    ps("TERM_COL_B", ints(&term_col_b));
    ps("N_BUS_CLAIMS", nclaims.to_string());
    let idxc: Vec<u128> = (0..34)
        .map(|i| {
            let mut g2k = F192::new(G.0, 0, 0);
            for _ in 0..i {
                g2k = g2k * g2k;
            }
            u(F192::ONE + g2k)
        })
        .collect();
    ps("INDEX_MLE_FACTORS", us(&idxc));
    ps("N_CLAIMS", ncl.to_string());
    ps("N_TABLES", l.taus.len().to_string());
    // The table sumcheck's eta layout, from the native verifier's own numbers:
    // a disjoint range of identities per table, then THREE powers shared by every
    // table, one per bus side. Sharing is what lets the target be derived from the
    // three leaf claims instead of trusted (lean_vm::cpu::eta_form_base).
    let n_id: Vec<usize> = lean_vm::tables::tables().iter().map(|t| t.n_constraints()).collect();
    let form_base = lean_vm::cpu::eta_form_base();
    ps(
        "ETA_OFFSET",
        ints(&lean_vm::constraints::eta_offsets(n_id.iter().copied())),
    );
    ps("ETA_FORM_BASE", form_base.to_string());
    ps("N_ETA_POWS", (form_base + 3).to_string());
    let committed: Vec<usize> = lean_vm::tables::tables()
        .iter()
        .map(|t| t.n_committed_columns())
        .collect();
    ps("N_TABLE_COLS", ints(&committed));
    ps("TABLE_COLS_CAP", (committed.iter().max().unwrap() + 1).to_string());
    const MINB3: usize = 3;
    let fixed_challenges: Vec<F192> = flock::zerocheck::univariate_skip_optimized::small_challenges()
        .into_iter()
        .chain(flock::zerocheck::univariate_skip_optimized::medium_challenges())
        .collect();
    ps("FIXED_CHALLENGES", flds(&fixed_challenges));
    // Flock univariate skip: 6 skipped variables, then the fixed inner rounds.
    ps("K_SKIP", "6".to_string());
    ps("N_FIXED_CHALLENGE_ROUNDS", fixed_challenges.len().to_string());
    let one_plus_challenge_inv: Vec<F192> = fixed_challenges.iter().map(|&c| (F192::ONE + c).inv()).collect();
    ps("ONE_PLUS_CHALLENGE_INV", flds(&one_plus_challenge_inv));
    let phi: Vec<F192> = primitives::field::PHI_8_TABLE_192[..128].to_vec();
    ps("PHI8_NODES", flds(&phi));
    // Tower F192 = F64[Y]/(Y^3+Y+1), Y = new(0,1,0). Y_TOWER embeds Y for
    // AIR lane reassembly; Y_INV helps derive the top PI-memory limb.
    let y_tower = F192::new(0, 1, 0);
    ps("Y_TOWER", u(y_tower).to_string());
    ps("Y_INV", f192_literal(y_tower.inv()));
    // Coordinate basis e_i of F192 over F2 (spans the whole field): the 64
    // binary basis vectors in each of the three tower limbs. The guest uses
    // these vectors to reconstruct a word from its 192 coordinate bits.
    let coord_basis: Vec<F192> = (0..192)
        .map(|i| match i / 64 {
            0 => F192::new(1u64 << i, 0, 0),
            1 => F192::new(0, 1u64 << (i - 64), 0),
            2 => F192::new(0, 0, 1u64 << (i - 128)),
            _ => unreachable!(),
        })
        .collect();
    ps("COORD_BASIS", flds(&coord_basis));
    let inv_den = |nodes: &[F192], node: F192, skip: F192| {
        let mut d = F192::ONE;
        for &s in nodes {
            if s != skip {
                d *= node + s;
            }
        }
        d.inv()
    };
    let ilam: Vec<F192> = (0..64)
        .map(|i| inv_den(&phi[64..128], phi[64 + i], phi[64 + i]))
        .collect();
    let icmb: Vec<F192> = (0..64)
        .map(|i| inv_den(&phi[..128], phi[64 + i], phi[64 + i]))
        .collect();
    let isdom: Vec<F192> = (0..64).map(|i| inv_den(&phi[..64], phi[i], phi[i])).collect();
    ps("LAGRANGE_INV_LAMBDA", flds(&ilam));
    ps("LAGRANGE_INV_COMBINED", flds(&icmb));
    ps("LAGRANGE_INV_S", flds(&isdom));
    ps("LINCHECK_ROUNDS", lcrounds.to_string());
    let pincol = flock::blake3::build_block_r1cs(taus[5].max(MINB3))
        .const_pin
        .expect("blake3 r1cs has a const pin");
    ps("PIN_COLUMN", pincol.to_string());
    ps("K_LOG", flock::blake3::K_LOG.to_string());
    // The q_flock Strided-claim slot stride is K_LOG - LOG_PACKING (= 8), so the
    // qflock point-claim slot must use THIS, not LOG2_FIELD_BITS.
    ps("SLOT_STRIDE_LOG", lean_vm::blake3_flock::SLOT_STRIDE_LOG.to_string());

    // ---- LIG candidate tables (fixed [minm, maxm] range; open_stacked config) ----
    let oshape = |m: usize, log_inv_rate: usize| {
        let shape = whir_shape(m, log_inv_rate);
        let (vc, sh) = (&shape.config, &shape.levels);
        let (cn, cr) = (sh.levels, vc.level_steps);
        // The final message sits at the LAST level. The guest fills level_roots slot 0
        // with the commitment root and every later slot from that level's root read,
        // then checks each query's Merkle walk with a write-once store into its slot.
        // A slot no read had filled would turn that check into a write, so this
        // relation is what keeps the query phase binding.
        assert_eq!(cr, cn - 1, "the yr level must be the last one");
        let (ck, cl, cyr) = (sh.ks.clone(), sh.log_msg_cols.clone(), sh.yr_log_n);
        let cq = vc.queries.clone();
        let (cd, cp) = (&shape.depth, &shape.per_squeeze);
        let cs: Vec<usize> = (0..cn).map(|i| cq[i].div_ceil(cp[i])).collect();
        let cni: Vec<usize> = ck.iter().map(|&k| 1usize << k).collect();
        let cqb: Vec<usize> = (0..cn).map(|lvl| vc.grinding_bits[lvl]).collect();
        assert!(
            cni.iter().enumerate().all(|(lv, &n)| {
                let (bytes, whole_blocks) = if lv == 0 {
                    (8 * n, n % 8 == 0)
                } else {
                    (24 * n, (3 * n) % 8 == 0)
                };
                bytes <= 1024 && whole_blocks
            }),
            "recursive WHIR guest supports whole-block Merkle rows of at most one 1024-byte BLAKE3 chunk"
        );
        let cfgb = |lvl: usize| vc.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;
        let mut cfb: Vec<usize> = Vec::new();
        for (lvl, &k) in ck.iter().enumerate().take(cn) {
            for j in 0..k {
                cfb.push((cfgb(lvl) - j as i64).max(0) as usize);
            }
        }
        let psum = |f: &dyn Fn(usize) -> usize| -> Vec<usize> {
            let mut o = Vec::with_capacity(cn);
            let mut acc = 0;
            for lv in 0..cn {
                o.push(acc);
                acc += f(lv);
            }
            o
        };
        let c_rowoff = psum(&|lv| cq[lv] * cni[lv] * if lv == 0 { 1 } else { 3 });
        let c_pathoff = psum(&|lv| cq[lv] * cd[lv] * 2);
        let c_qpoff = psum(&|lv| cs[lv] * cp[lv]);
        let c_svkoff = psum(&|lv| cl[lv] + 1);
        let c_foldbase = psum(&|lv| ck[lv]);
        let c_risstart: Vec<usize> = (0..cn).map(|k| c_foldbase[k] + ck[k]).collect();
        let mut c_svk = Vec::new();
        let mut c_ivk = Vec::new();
        for &cl_lv in cl.iter().take(cn) {
            for &v in &pcs::whir::eval_sk_at_vks(cl_lv) {
                c_svk.push(F192::new(v.0, 0, 0));
                c_ivk.push(if v == F64::ZERO {
                    F192::ZERO
                } else {
                    F192::new(v.inv().0, 0, 0)
                });
            }
        }
        OpeningShape {
            n_levels: cn,
            yr_level: cr,
            yr_log_len: cyr,
            folds: ck,
            log_message_columns: cl,
            queries: cq,
            tree_depths: cd.clone(),
            positions_per_squeeze: cp.clone(),
            squeezes: cs,
            interleaving: cni,
            query_grinding_bits: cqb,
            fold_grinding_bits: cfb,
            row_offsets: c_rowoff,
            path_offsets: c_pathoff,
            positions_offsets: c_qpoff,
            vanish_offsets: c_svkoff,
            fold_offsets: c_foldbase,
            residual_fold_offsets: c_risstart,
            vanish_values: c_svk,
            vanish_inverses: c_ivk,
            ood_samples: vc.ood_samples.clone(),
        }
    };
    let (minm, maxm) = (MU_MIN, MU_MAX);
    let rates = pcs::whir::MIN_LOG_INV_RATE..=pcs::whir::MAX_LOG_INV_RATE;
    let cands: Vec<_> = rates
        .clone()
        .flat_map(|r| (minm..=maxm).map(move |m| oshape(m, r)))
        .collect();
    let maxlev = cands.iter().map(|c| c.n_levels).max().unwrap();
    let maxfolds = cands.iter().map(|c| c.fold_grinding_bits.len()).max().unwrap();
    let maxsvk = cands.iter().map(|c| c.vanish_values.len()).max().unwrap();
    let maxood = cands.iter().flat_map(|c| &c.ood_samples).copied().max().unwrap_or(0);
    ps("LIG_MAX_LEVELS", maxlev.to_string());
    ps("LIG_MAX_TOTAL_FOLDS", maxfolds.to_string());
    ps("LIG_MAX_VANISH_LEN", maxsvk.to_string());
    ps("LIG_MAX_OOD_SAMPLES", maxood.to_string());
    ps("LIG_MIN_LOG_SIZE", minm.to_string());
    let cks: Vec<(usize, usize)> = lean_vm::cpu::col_kappa_sources(kbc).into_iter().flatten().collect();
    ps("N_COMMITTED_COLS", cks.len().to_string());
    ps("COL_KAPPA_SRC", ints(&cks.iter().map(|&(s, _)| s).collect::<Vec<_>>()));
    ps("COL_KAPPA_ADJ", ints(&cks.iter().map(|&(_, a)| a).collect::<Vec<_>>()));
    ps("PCS_MIN_MU", lean_vm::pcs::MIN_MU.to_string());
    ps(
        "LIG_LOG_MSG_COLS_CAP",
        cands
            .iter()
            .map(|c| *c.log_message_columns.iter().max().unwrap())
            .max()
            .unwrap()
            .to_string(),
    );
    ps(
        "YR_LOG_CAP",
        cands.iter().map(|c| c.yr_log_len).max().unwrap().to_string(),
    );
    {
        let pad = |v: &[usize], stride: usize| -> Vec<usize> {
            let mut o = v.to_vec();
            o.resize(stride, 0);
            o
        };
        let flat = |f: &dyn Fn(&OpeningShape) -> Vec<usize>, stride: usize| -> Vec<usize> {
            cands.iter().flat_map(|c| pad(&f(c), stride)).collect()
        };
        let scal = |f: &dyn Fn(&OpeningShape) -> usize| -> Vec<usize> { cands.iter().map(f).collect() };
        ps("LIG_N_LEVELS", ints(&scal(&|c| c.n_levels)));
        ps("LIG_YR_LEVEL", ints(&scal(&|c| c.yr_level)));
        ps("LIG_YR_LOG_LEN", ints(&scal(&|c| c.yr_log_len)));
        ps("LIG_YR_LEN", ints(&scal(&|c| 1usize << c.yr_log_len)));
        ps("LIG_TOTAL_FOLDS", ints(&scal(&|c| c.folds.iter().sum())));
        ps("LIG_MAX_QUERIES", ints(&scal(&|c| *c.queries.iter().max().unwrap())));
        ps("LIG_MAX_SQUEEZES", ints(&scal(&|c| *c.squeezes.iter().max().unwrap())));
        ps(
            "LIG_MAX_INTERLEAVE",
            ints(&scal(&|c| *c.interleaving.iter().max().unwrap())),
        );
        // StackBuf cap for the packed leaf row AND the raw-limb `lanes` scratch
        // that shares it (`open_stacked`). Level 0 packs 2 base-field lanes per
        // cell (n/2 cells). Deeper levels first load 3 raw tower limbs per word
        // into `lanes` (3n cells), then pack them into the 3n/2-cell leaf row,
        // so `lanes` (3n) is the binding size there. Sizing the deeper term at
        // 3n/2 happened to hold only while L0's n/2 dominated (small folds);
        // it under-provisions once a deeper interleave exceeds L0's.
        let packed_cells = |c: &Vec<usize>| -> usize {
            c.iter()
                .enumerate()
                .map(|(lv, &n)| if lv == 0 { n / 2 } else { 3 * n })
                .max()
                .unwrap()
        };
        ps(
            "LIG_PACKED_ROW_CAP",
            cands
                .iter()
                .map(|c| packed_cells(&c.interleaving))
                .max()
                .unwrap()
                .to_string(),
        );
        ps(
            "LIG_POSITIONS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.squeezes[level] * c.positions_per_squeeze[level])
                    .sum()
            })),
        );
        ps(
            "LIG_ROWS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.queries[level] * c.interleaving[level] * if level == 0 { 1 } else { 3 })
                    .sum()
            })),
        );
        ps(
            "LIG_PATHS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.queries[level] * c.tree_depths[level] * 2)
                    .sum()
            })),
        );
        ps(
            "LIG_QUERY_GRIND_BITS",
            ints(&flat(&|c| c.query_grinding_bits.clone(), maxlev)),
        );
        ps(
            "LIG_OOD_SAMPLES",
            ints(
                &cands
                    .iter()
                    .flat_map(|shape| pad(&shape.ood_samples, maxlev))
                    .collect::<Vec<_>>(),
            ),
        );
        ps("LIG_QUERIES", ints(&flat(&|c| c.queries.clone(), maxlev)));
        ps("LIG_FOLDS", ints(&flat(&|c| c.folds.clone(), maxlev)));
        ps("LIG_INTERLEAVE", ints(&flat(&|c| c.interleaving.clone(), maxlev)));
        ps(
            "LIG_LEAF_PAIRS",
            ints(&flat(
                &|c| {
                    c.interleaving
                        .iter()
                        .enumerate()
                        .map(|(lv, &n)| if lv == 0 { n / 4 } else { 3 * n / 4 })
                        .collect()
                },
                maxlev,
            )),
        );
        // 64-byte BLAKE3 blocks per leaf row: level 0's committed rows are
        // base-field F64 (8 bytes/lane); deeper levels are native F192
        // (24 bytes/word, received as three embedded K limbs each). Rows are
        // whole blocks only (asserted at candidate construction).
        ps(
            "LIG_LEAF_BLOCKS",
            ints(&flat(
                &|c| {
                    c.interleaving
                        .iter()
                        .enumerate()
                        .map(|(lv, &n)| if lv == 0 { n / 8 } else { 3 * n / 8 })
                        .collect()
                },
                maxlev,
            )),
        );
        ps("LIG_TREE_DEPTH", ints(&flat(&|c| c.tree_depths.clone(), maxlev)));
        ps("LIG_SQUEEZES", ints(&flat(&|c| c.squeezes.clone(), maxlev)));
        ps(
            "LIG_POSITIONS_OFF",
            ints(&flat(&|c| c.positions_offsets.clone(), maxlev)),
        );
        ps(
            "LIG_LOG_MSG_COLS",
            ints(&flat(&|c| c.log_message_columns.clone(), maxlev)),
        );
        ps(
            "LIG_RESIDUAL_FOLD_OFF",
            ints(&flat(&|c| c.residual_fold_offsets.clone(), maxlev)),
        );
        ps(
            "LIG_RESIDUAL_PREFIX_LEN",
            ints(&flat(
                &|c| {
                    c.log_message_columns
                        .iter()
                        .map(|&columns| columns - c.yr_log_len)
                        .collect()
                },
                maxlev,
            )),
        );
        ps("LIG_FOLDS_OFF", ints(&flat(&|c| c.fold_offsets.clone(), maxlev)));
        ps("LIG_ROWS_OFF", ints(&flat(&|c| c.row_offsets.clone(), maxlev)));
        ps("LIG_PATHS_OFF", ints(&flat(&|c| c.path_offsets.clone(), maxlev)));
        ps("LIG_VANISH_OFF", ints(&flat(&|c| c.vanish_offsets.clone(), maxlev)));
        ps(
            "LIG_FOLD_GRIND_BITS",
            ints(&flat(&|c| c.fold_grinding_bits.clone(), maxfolds)),
        );
        let mut svk2 = Vec::new();
        let mut ivk2 = Vec::new();
        for c in &cands {
            let mut s = c.vanish_values.clone();
            let mut iv = c.vanish_inverses.clone();
            s.resize(maxsvk, F192::ZERO);
            iv.resize(maxsvk, F192::ZERO);
            svk2.extend(s);
            ivk2.extend(iv);
        }
        ps("LIG_VANISH_VALS", flds(&svk2));
        ps("LIG_VANISH_INVS", flds(&ivk2));
    }
    let n_log_sizes = maxm - minm + 1;
    let n_rates = pcs::whir::MAX_LOG_INV_RATE - pcs::whir::MIN_LOG_INV_RATE + 1;
    ps("LIG_N_LOG_SIZES", n_log_sizes.to_string());
    ps("LIG_N_RATES", n_rates.to_string());
    ps("LIG_N_CANDIDATES", (n_log_sizes * n_rates).to_string());
    ps("LIG_MIN_SHIFT_INV", u(F192::new(g_pow(minm).inv().0, 0, 0)).to_string());
    ps("CLAIM_POINT_BUF", ints(&cpbuf));
    ps("CLAIM_COMMITTED_COL", ints(&cpcol));
    let slot_stride_log = lean_vm::blake3_flock::SLOT_STRIDE_LOG;
    let cpqbits: Vec<usize> = cpqslot
        .iter()
        .flat_map(|&slot| (0..slot_stride_log).map(move |k| (slot >> k) & 1))
        .collect();
    ps("CLAIM_QFLOCK_SLOT_BITS", ints(&cpqbits));
    ps("QFLOCK_COMMITTED_COL", qflock_compact.to_string());
    ps("QFLOCK_VARS_CAP", (33 + slot_stride_log).to_string());
    ps("BYTECODE_LOG", kbc.to_string());
    // The stacked bytecode: nbcv/2 encoding columns per side, aligned with the bus
    // tuple, so their slots span the fingerprint's own bits. The defer region is
    // 2*kbc points + sel bits + 2 reduced + alpha + z_skip + 2*lcrounds rounds
    // + 64 z_partial + 1 matpart.
    let bc_cols = nbcv / 2;
    let log2_bc_cols = lean_vm::leaf::N_TUPLE_BITS;
    ps("BYTECODE_COLS", bc_cols.to_string());
    ps("LOG2_BYTECODE_COLS", log2_bc_cols.to_string());
    ps("DEFER_SIZE", (kbc + log2_bc_cols + 2 * lcrounds + 68).to_string());
    ps("BYTECODE_VARS", (kbc + log2_bc_cols).to_string());
    ps("NSUB_BOUND", NSUB_BOUND.to_string());
    let label_state = pack_state(Sponge::new(b"leanvm-b", &[]).state());
    ps("TRANSCRIPT_SEED_0", u(label_state[0]).to_string());
    ps("TRANSCRIPT_SEED_1", u(label_state[1]).to_string());
    let agg_state = pack_state(Sponge::new(RECURSION_AGG_LABEL, &[]).state());
    ps("AGG_SEED_0", u(agg_state[0]).to_string());
    ps("AGG_SEED_1", u(agg_state[1]).to_string());
    let statement_state = pack_state(Sponge::new(RECURSION_STATEMENT_LABEL, &[]).state());
    ps("STATEMENT_SEED_0", u(statement_state[0]).to_string());
    ps("STATEMENT_SEED_1", u(statement_state[1]).to_string());
    rep
}

/// Return the process-cached recursion guest for this program. The batch arity
/// is a runtime hint, so it is not part of the key.
fn recursion_guest_arc(inner_program: &Program) -> std::sync::Arc<Program> {
    use std::sync::{Arc, Mutex, OnceLock};

    type Key = [u64; 6];
    static CACHE: OnceLock<Mutex<std::collections::HashMap<Key, Arc<Program>>>> = OnceLock::new();
    const GUEST_CACHE_CAP: usize = 8;

    let seed = lean_vm::cpu::fs_seed(inner_program);
    let key = [seed[0].c0, seed[0].c1, seed[0].c2, seed[1].c0, seed[1].c1, seed[1].c2];
    let cache = CACHE.get_or_init(Default::default);
    if let Some(guest) = cache.lock().expect("recursion guest cache poisoned").get(&key) {
        return Arc::clone(guest);
    }

    let replacements = placeholder_map(inner_program);
    // `DBG_PLACEHOLDERS=path`: dump the baked guest constants, to read alongside
    // a `DBG_PROF_DUMP` profile (the guest's shape is entirely in these).
    if let Ok(path) = std::env::var("DBG_PLACEHOLDERS") {
        let dump: String = replacements.iter().map(|(k, v)| format!("{k} = {v}\n")).collect();
        std::fs::write(&path, dump).expect("write DBG_PLACEHOLDERS");
    }
    let guest = Arc::new(compile(
        &parse_with_replacements(include_str!("../guests/recursion.py"), &replacements)
            .expect("the repository recursion guest must parse"),
    ));

    // `DBG_DISASM=path`: dump the guest's disassembly, to read alongside a
    // `DBG_PROF_DUMP` per-pc profile.
    if let Ok(path) = std::env::var("DBG_DISASM") {
        std::fs::write(&path, lean_compiler::disassemble(&guest.prog)).expect("write DBG_DISASM");
    }

    let mut map = cache.lock().expect("recursion guest cache poisoned");
    if let Some(cached) = map.get(&key) {
        return Arc::clone(cached);
    }
    if map.len() < GUEST_CACHE_CAP {
        map.insert(key, Arc::clone(&guest));
    }
    guest
}

/// Return an owned guest whose witness streams may be mutated by the prover.
fn recursion_guest(inner_program: &Program) -> Program {
    (*recursion_guest_arc(inner_program)).clone()
}

/// Run an `inner.len()`→1 recursive aggregation and verify the outer proof;
/// each entry `(hashes, iters)` shapes one inner proof of the fixed inner
/// program. Prints the benchmark report. The flow:
/// 1. compile the inner program (→ its bytecode size);
/// 2. compile the recursion guest (`guests/recursion.py` — the generic
///    map needs only that size);
/// 3. prove the inner proofs (and extract their hints);
/// 4. prove the recursion, verify, discharge the three reduced claims.
///
/// Outer proving runs one discarded warmup pass followed by `plan.repeat`
/// measured passes (see [`primitives::bench`]); the inner proofs are built once.
pub fn run_recursion(
    inner: &[(usize, usize)],
    log_inv_rate: usize,
    enable_tracing: bool,
    plan: Plan,
) -> RecursiveProof {
    let rates = vec![log_inv_rate; inner.len()];
    run_recursion_with_rates(inner, &rates, log_inv_rate, enable_tracing, plan)
}

/// Run recursion with one transcript-bound PCS rate per inner proof. The guest
/// bytecode is independent of these values and supports mixed-rate batches.
fn run_recursion_with_rates(
    inner: &[(usize, usize)],
    log_inv_rates: &[usize],
    outer_log_inv_rate: usize,
    enable_tracing: bool,
    plan: Plan,
) -> RecursiveProof {
    // 1 + 2: the recursion program is generic — its map needs only the inner
    // bytecode size — so it is compiled FIRST, before any inner proof.
    let program = inner_program();
    let t = std::time::Instant::now();
    let mut guest = recursion_guest(&program);
    let t_compile = t.elapsed();
    // The recursion program size + compile time, BEFORE any inner proving.
    let real_instrs: usize = guest.fn_ranges.iter().map(|(_, _, len)| *len as usize).sum();
    // 3: prove the inner proofs and extract the recursion witness (hints).
    let batch = build_batch(inner, log_inv_rates, outer_log_inv_rate);
    let nsub = batch.inner_stats.len();
    let total_inner_cycles: usize = batch.inner_stats.iter().map(|&(cycles, _)| cycles).sum();
    if enable_tracing {
        primitives::init_tracing();
    }
    let trace_span =
        tracing::info_span!("Recursive aggregation", n = nsub, log_inv_rate = outer_log_inv_rate).entered();
    // Only the final measured pass of each stage is traced: the tree describes the
    // proof the reported timings are about, instead of repeating itself per pass.
    let ((recursive_proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        batch.prove(&mut guest)
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        recursive_proof
            .verify(&batch.program0)
            .expect("complete recursive proof verifies");
    });
    drop(trace_span);

    println!(
        "recursion program: {} instructions (2^{} padded), compiled in {} s",
        pretty_integer(real_instrs),
        guest.prog.len().trailing_zeros(),
        pretty_f64(t_compile.as_secs_f64())
    );
    for &(cycles, committed) in &batch.inner_stats {
        println!(
            "[inner] cycles={} committed=2^{}",
            pretty_integer(cycles),
            pretty_f64((committed as f64).log2())
        );
    }
    let nsub_pretty = pretty_integer(nsub);
    println!(
        "\nrecursion {nsub_pretty}\u{2192}1: {nsub_pretty} inner proofs of {} cycles each",
        pretty_integer(total_inner_cycles / nsub)
    );
    // The guest's own work, then what gets proven: each table is filled to a power of
    // two so that none needs padding rows (`lean_vm::cpu::filler`).
    let base_cycles: usize = stats.base_counts.iter().sum();
    println!(
        "  guest cycles (VM steps)     : {} = {}   ({} / inner cycle)",
        pretty_integer(base_cycles),
        crate::report::pow(base_cycles),
        pretty_f64(base_cycles as f64 / total_inner_cycles as f64)
    );
    println!(
        "    proven rows               : {} = {}  (filled to powers of two)",
        pretty_integer(stats.cycles),
        crate::report::pow(stats.cycles)
    );
    println!("    details                   : {}", stats.details());
    crate::report::print_proof_size(&recursive_proof);
    println!(
        "recursion proving         : {} s{}      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        crate::report::peak_gib()
    );
    println!("verification              : {} s", pretty_f64(verify_time.mean()));
    recursive_proof
}

/// End-to-end recursion test: two ordinary proofs are verified and aggregated
/// by one guest, then its three reduced claims are discharged natively.
#[test]
fn recursion_2to1() {
    run_recursion(
        &[(8, 1 << 15), (8, 1 << 15)],
        lean_vm::pcs::LOG_INV_RATE,
        false,
        Plan::default(),
    );
}

/// THE genericity milestone: ONE compiled guest bytecode verifies two inner
/// proofs of DIFFERENT sizes and rates in the same aggregation (the placeholder
/// map depends only on the inner bytecode size, so one map covers both shapes).
#[test]
fn recursion_2to1_mixed() {
    run_recursion_with_rates(&[(4, 1 << 13), (64, 1 << 15)], &[1, 4], 3, false, Plan::default());
}

/// Adversarial check that the remaining hints and native-format bounds bind:
/// the honest proof verifies; malformed sizes/nonces and corrupted certified
/// hints reject; and all commitment-placement descriptors are absent from the
/// witness. Ignored because it runs several full inner+outer proofs.
#[test]
#[ignore]
fn recursion_soundness_binds() {
    let cfg: &[(usize, usize)] = &[(4, 1 << 12)];
    let batch = build_batch(cfg, &[lean_vm::pcs::LOG_INV_RATE], lean_vm::pcs::LOG_INV_RATE);
    let mut guest = recursion_guest(&batch.program0);
    let public_input = batch.public_input();

    let run = |g: &mut Program, merged: &[(String, Vec<Vec<F192>>)]| -> bool {
        for (name, entries) in merged {
            g.set_witness(name, entries.clone());
        }
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (proof, _) = prove(g, public_input, lean_vm::pcs::LOG_INV_RATE);
            verify(g, &public_input, &proof).is_ok()
        }))
        .unwrap_or(false)
    };

    assert!(run(&mut guest, &batch.merged), "honest proof must verify");
    assert!(
        batch.merged.iter().all(|(name, _)| !matches!(
            name.as_str(),
            "claim_sel_bits" | "claim_yslot_bits" | "claim_qflock_slot_bits" | "rs_sel_bits" | "rs_yslot_bits"
        )),
        "claim and ring placement descriptors must be derived, not hinted"
    );

    // each tamper flips one hint to a definitely-invalid value.
    let tampers: Vec<(&str, usize, F192)> = vec![
        ("fs_seed", 0, F192::ONE), // wrong proving environment: own_pi must reject
        ("nsub", 0, F192::ONE),    // g^0: dropping a sub-proof must not keep the statement
        ("stream", 0, F192::new((lean_vm::cpu::MIN_LOG_MEM - 1) as u64, 0, 0)), // native memory floor
        ("stream", 1, F192::new(1u64 << 32, 0, 0)), // native row counts are strictly below 2^32
        ("claim_nover", 0, F192::new(g_pow(5).0, 0, 0)),
        ("pi_cplen", 0, F192::new(g_pow(2).0, 0, 0)),
        ("zc_tau_max", 0, F192::new(g_pow(2).0, 0, 0)),
    ];
    for &(stream, idx, val) in &tampers {
        let mut merged = batch.merged.clone();
        let pos = merged.iter().position(|(n, _)| n == stream).expect("stream present");
        let orig = merged[pos].1[0][idx];
        assert_ne!(orig, val, "{stream}[{idx}] tamper must change it");
        merged[pos].1[0][idx] = val;
        assert!(
            !run(&mut guest, &merged),
            "tampering {stream}[{idx}] must be rejected by the guest"
        );
    }
    // sort_order: duplicate a rank (break the packing bijection).
    {
        let mut merged = batch.merged.clone();
        let pos = merged.iter().position(|(n, _)| n == "sort_order").expect("sort_order");
        merged[pos].1[0][0] = merged[pos].1[0][1];
        assert!(!run(&mut guest, &merged), "duplicated sort_order rank must be rejected");
    }
    // col_sort_order: swapping two distinct entries preserves a valid
    // permutation but violates either descending kappa or the native-index
    // tie-break, so the reconstructed commitment offsets must reject it.
    {
        let mut merged = batch.merged.clone();
        let pos = merged
            .iter()
            .position(|(n, _)| n == "col_sort_order")
            .expect("col_sort_order");
        assert!(merged[pos].1[0].len() >= 2);
        merged[pos].1[0].swap(0, 1);
        assert!(
            !run(&mut guest, &merged),
            "non-canonical col_sort_order must be rejected"
        );
    }
    eprintln!("all recursion soundness tamperings correctly rejected");
}

/// One compiled guest bytecode proves MANY inner runs with wildly different
/// opcode profiles and sizes, without recompilation. The configs span four
/// committed sizes (m in {23,24,25,26}, four distinct match_range opening
/// arms) and four BLAKE3 log-instance-counts (tau_5 in {3,4,5,6}, different
/// r1cs statement digests, flock reduction sizes, and pin prefixes). The
/// guest is compiled ONCE from the placeholder map, which is a function of the
/// inner bytecode size alone, so every shape is verified on the same Program
/// object. Ignored: ~6 full inner+outer proofs, minutes.
#[test]
#[ignore]
fn recursion_generic_many() {
    // (hashes, iters) per inner run - deliberately diverse profiles.
    let configs: &[(usize, usize)] = &[
        (4, 1 << 12),  // m=23, tau_5=3
        (8, 1 << 13),  // m=24, tau_5=3
        (16, 1 << 14), // m=25, tau_5=4
        (8, 1 << 15),  // m=26, tau_5=3
        (32, 1 << 13), // m=24, tau_5=5
        (64, 1 << 13), // m=24, tau_5=6
    ];
    // The recursion program is generic: compile it ONCE, from the inner program's
    // size alone, BEFORE any inner proof exists. Genericity is then shown directly
    // — every shape below verifies against this one bytecode.
    let mut guest = recursion_guest(&inner_program());
    eprintln!("guest compiled ONCE ({} instrs)", pretty_integer(guest.prog.len()));
    for &cfg in configs {
        let batch = build_batch(&[cfg], &[lean_vm::pcs::LOG_INV_RATE], lean_vm::pcs::LOG_INV_RATE);
        let (recursive_proof, _) = batch.prove(&mut guest);
        recursive_proof
            .verify(&batch.program0)
            .expect("complete recursive proof verifies");
        eprintln!(
            "  verified: hashes={:>2}, iters=2^{}",
            pretty_integer(cfg.0),
            (cfg.1 as f64).log2() as u32
        );
    }
    eprintln!(
        "all {} shapes verified by the SAME guest bytecode",
        pretty_integer(configs.len())
    );
}

/// Guest cycle profile WITHOUT proving the recursion: build one sub-proof's hints,
/// then just execute the guest. Runs in about a second, which makes it the loop for
/// attributing (and reducing) the guest's ~470k cycles:
///
/// ```text
/// DBG_PROF=1 DBG_PROF_DUMP=/tmp/prof DBG_DISASM=/tmp/disasm \
///   cargo test --release -p rec_aggregation recursion_guest_profile -- --ignored --nocapture
/// ```
///
/// `DBG_PROF=1` prints cycles by function (each lowered `for` body is its own
/// entry); the dumps tie a hot function's pc range back to its instructions.
#[test]
#[ignore]
fn recursion_guest_profile() {
    let cfg: &[(usize, usize)] = &[(4, 1 << 12)];
    let batch = build_batch(cfg, &[lean_vm::pcs::LOG_INV_RATE], lean_vm::pcs::LOG_INV_RATE);
    let mut guest = recursion_guest(&batch.program0);
    for (name, entries) in &batch.merged {
        guest.set_witness(name, entries.clone());
    }
    let _ = guest.execute(batch.public_input());
}
