//! End-to-end N→1 recursion: one guest program (`guests/recursion.py`)
//! replays `cpu::verify` for NSUB proofs of a fixed inner program, batches
//! their deferred claims with the two aggregation sumchecks, and binds the sub
//! statements + the three reduced claims (stacked bytecode, A0, B0) to its own
//! public input (doc.tex §Recursive aggregation, §Deferred evaluation claims).
//!
//! Zero hand-mirroring: the transcript trace of a REAL `cpu::verify` run
//! (`transcript::trace_start`/`trace_take`) is the guest's mechanical spec —
//! `gen_verify` walks it structurally (a `Walk` cursor; `Sponge::replay` yields
//! the checkpoint states) to extract every hint value, and the real
//! `cpu::layout` supplies every compile-time shape. `gen_agg` mirrors the
//! guest's aggregation transcript and runs the two batching-sumcheck provers
//! (dense for the bytecode, two-phase sparse for the flock matrices).
//! [`RecursiveProof::verify`] is the only public acceptance path: it verifies
//! the outer VM proof and evaluates every deferred fixed polynomial.

use std::collections::BTreeMap;

use pcs::ligerito::log2_ceil;
use lean_compiler::{compile, parse, parse_file_with_replacements};
use lean_vm::cpu::{Program, prove, verify};
use primitives::field::{g_pow, F128, G};
use lean_vm::leaf::{Block, Coord};
use primitives::multilinear::mle_eval;
use lean_vm::transcript::{Sponge, TraceOp, trace_start, trace_take};

/// A field element as the decimal `u128` literal the zkDSL parser accepts.
fn u(f: F128) -> u128 {
    (f.lo as u128) | ((f.hi as u128) << 64)
}

/// The non-trivial inner program: a runtime-bounded BLAKE3 hash chain seeded
/// from the public input, a runtime-bounded `mul_range` product loop with heap
/// traffic, and a final assert tying them together. BOTH loop bounds ride
/// witness hints ("n_hash", "iters"), so a single program (one bytecode, one
/// digest) proves runs with wildly different opcode profiles and sizes - the
/// exact genericity the recursion guest is built for. Exercises every table
/// (XOR/MUL/SET/DEREF/JUMP/BLAKE3).
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
/// hint. Returns (program, proof, guest-cycle count).
fn prove_inner(pi: [F128; 2], hashes: usize, iters: usize) -> (Program, lean_vm::cpu::Proof, usize) {
    assert!(hashes >= 1 && iters >= 1, "both loops run at least once");
    let mut program = inner_program();
    // Replay natively: the hash chain, then the product loop, to fetch the
    // final accumulator (nonzero, for the hinted-inverse assert).
    let mut st = [pi[0], pi[1]];
    for _ in 0..hashes {
        st = lean_vm::vmhash::compress(st, st);
    }
    let mut acc = st[0];
    let mut x = F128::ONE;
    let g = primitives::field::g_pow(1);
    for _ in 0..iters {
        let b = acc * acc + st[1];
        acc = b + x;
        x *= g;
    }
    let out = acc;
    assert!(out != F128::ZERO, "inner accumulator must be nonzero");
    program.set_witness("outinv", vec![vec![out.inv()]]);
    program.set_witness("n_hash", vec![vec![g_pow(hashes)]]);
    program.set_witness("iters", vec![vec![g_pow(iters)]]);
    let (proof, stats) = prove(&program, pi);
    eprintln!(
        "[inner] cycles={} committed=2^{:.2}",
        stats.cycles,
        (stats.committed as f64).log2()
    );
    (program, proof, stats.cycles)
}

/// The deferred-claim data the guest binds to the outer public input: the outer
/// verifier checks each claim natively (doc.tex §Deferred evaluation claims;
/// n_rec = 1 forwards fresh claims without batching).
struct SubDefer {
    pi: [F128; 2],
    kbc: usize,
    zeta: Vec<F128>,
    sb: Vec<F128>,
    wbc: Vec<F128>,
    lc_alpha: F128,
    zz: F128,
    zrho8: Vec<F128>,
    lrr: Vec<F128>,
    lcz: Vec<F128>,
    matpart: F128,
}

/// The batched reduced claims the aggregation exports: one point + value on
/// the stacked bytecode polynomial, one point + two values on the flock
/// matrices (doc.tex §Deferred evaluation claims).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct ReducedClaims {
    r_bc: Vec<F128>,
    v_bc: F128,
    r_m: Vec<F128>,
    v_a: F128,
    v_b: F128,
}

/// Everything committed by the outer public input. Keeping this private makes
/// the deferred claims an implementation detail of recursive verification.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct RecursiveStatement {
    sub_statements: Vec<[F128; 2]>,
    reduced: ReducedClaims,
}

impl RecursiveStatement {
    fn public_input(&self, inner_environment: [F128; 2]) -> [F128; 2] {
        let mut sponge = Sponge::empty();
        for &v in &inner_environment {
            sponge.observe(v);
        }
        for statement in &self.sub_statements {
            for &v in statement {
                sponge.observe(v);
            }
        }
        for &v in &self.reduced.r_bc {
            sponge.observe(v);
        }
        sponge.observe(self.reduced.v_bc);
        for &v in &self.reduced.r_m {
            sponge.observe(v);
        }
        sponge.observe(self.reduced.v_a);
        sponge.observe(self.reduced.v_b);
        sponge.state()
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
    pub fn sub_statements(&self) -> &[[F128; 2]] {
        &self.statement.sub_statements
    }

    /// Verify the complete recursive proof against the expected inner program.
    pub fn verify(&self, inner_program: &Program) -> Result<(), RecursiveVerifyError> {
        let statement = &self.statement;
        if statement.sub_statements.is_empty() {
            return Err(RecursiveVerifyError::EmptyBatch);
        }
        let guest = recursion_guest(inner_program, statement.sub_statements.len());
        let public_input = statement.public_input(lean_vm::cpu::fs_seed(inner_program));
        verify(&guest, &public_input, &self.outer_proof)
            .map_err(RecursiveVerifyError::OuterProof)?;
        check_reduced(inner_program, &statement.reduced)
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

fn fold_lsb(t: &mut Vec<F128>, r: F128) {
    let half = t.len() / 2;
    for i in 0..half {
        t[i] = t[2 * i] + r * (t[2 * i] + t[2 * i + 1]);
    }
    t.truncate(half);
}

/// Compressed product-sumcheck round message over γ-weighted table pairs:
/// (g1, g∞) with g0 recovered from the running claim.
fn round_msg(pairs: &[(&[F128], &[F128], F128)]) -> (F128, F128) {
    let (mut g1, mut gi) = (F128::ZERO, F128::ZERO);
    for &(u, m, gamma) in pairs {
        let (mut a1, mut ai) = (F128::ZERO, F128::ZERO);
        for i in 0..u.len() / 2 {
            a1 += u[2 * i + 1] * m[2 * i + 1];
            ai += (u[2 * i] + u[2 * i + 1]) * (m[2 * i] + m[2 * i + 1]);
        }
        g1 += gamma * a1;
        gi += gamma * ai;
    }
    (g1, gi)
}

/// The stacked bytecode polynomial of the inner program (leaf's canonical
/// table, built from the real layout).
fn stacked_bytecode(program: &Program) -> Vec<F128> {
    // Public bytecode coordinates depend only on the program. The remaining
    // layout inputs affect private witness/table shapes, so fixed valid dummy
    // sizes are sufficient and avoid retaining a representative inner proof.
    let l = lean_vm::cpu::layout(
        &program.prog,
        20,
        [1usize << 10; 6],
        [F128::ZERO; 2],
    );
    lean_vm::leaf::stacked_bytecode_table(&l.push)
}

/// The aggregation layer: mirror the guest's aggregation transcript, run the
/// two batching-sumcheck PROVERS (dense bytecode; two-phase sparse matrices),
/// and return the round-message hints, the terminal hints, the reduced claims,
/// and the outer public input.
#[allow(clippy::type_complexity)]
fn gen_agg(
    program: &Program,
    subs: &[SubDefer],
) -> (Vec<(String, Vec<F128>)>, [F128; 2], ReducedClaims) {
    let nsub = subs.len();
    let kbc = subs[0].kbc;
    let kbcv = kbc + 3;
    let klog = flock::blake3::K_LOG;

    // ---- the aggregation transcript (mirrors the guest exactly) ----
    let mut h = Sponge::empty();
    for d in subs {
        h.observe(d.pi[0]);
        h.observe(d.pi[1]);
        for &v in &d.zeta {
            h.observe(v);
        }
        for &v in &d.sb {
            h.observe(v);
        }
        for &v in &d.wbc {
            h.observe(v);
        }
        h.observe(d.lc_alpha);
        h.observe(d.zz);
        for &v in &d.zrho8 {
            h.observe(v);
        }
        for &v in &d.lrr {
            h.observe(v);
        }
        for &v in &d.lcz {
            h.observe(v);
        }
        h.observe(d.matpart);
    }

    // ---- bytecode batching sumcheck (dense, 2^kbcv; ONE claim per sub, at
    // the shared push/pull point) ----
    let gbc: Vec<F128> = (0..nsub).map(|_| h.sample()).collect();
    let mut bt = stacked_bytecode(program);
    let mut wt = vec![F128::ZERO; 1 << kbcv];
    let points: Vec<Vec<F128>> = subs
        .iter()
        .map(|d| d.zeta.iter().chain(&d.sb).copied().collect::<Vec<_>>())
        .collect();
    for (t, p) in points.iter().enumerate() {
        let eqt = primitives::multilinear::build_eq(p);
        for (w, &e) in wt.iter_mut().zip(eqt.iter()) {
            *w += gbc[t] * e;
        }
    }
    let mut brun: F128 = (0..nsub).map(|t| gbc[t] * subs[t].wbc[0]).fold(F128::ZERO, |a, x| a + x);
    let mut bscr = Vec::new();
    let mut r_bc = Vec::new();
    for _ in 0..kbcv {
        let (g1, gi) = round_msg(&[(&bt, &wt, F128::ONE)]);
        h.observe(g1);
        h.observe(gi);
        let r = h.sample();
        bscr.extend([g1, gi]);
        r_bc.push(r);
        let g0 = brun + g1;
        let c1 = g0 + g1 + gi;
        brun = gi * r * r + c1 * r + g0;
        fold_lsb(&mut bt, r);
        fold_lsb(&mut wt, r);
    }
    let v_bc = bt[0];
    assert_eq!(brun, v_bc * wt[0], "bytecode sumcheck terminal");

    // ---- matrix batching sumcheck (two-phase sparse, per the probe) ----
    let gmt: Vec<F128> = (0..nsub).map(|_| h.sample()).collect();
    let (ma, mb) = flock::blake3::matrices();
    // per-claim dense weight tables: rows = quirky eq, cols = eq(top rounds) x z_partial.
    let mut us: Vec<Vec<F128>> = subs
        .iter()
        .map(|d| flock::lincheck::build_quirky_eq_table(d.zz, &d.zrho8, 6))
        .collect();
    let ws: Vec<Vec<F128>> = subs
        .iter()
        .map(|d| {
            (0..1usize << klog)
                .map(|c| {
                    let mut w = d.lcz[c & 63];
                    for (j, &rj) in d.lrr.iter().enumerate() {
                        let bit = (c >> (klog - 1 - j)) & 1;
                        w *= if bit == 1 { rj } else { F128::ONE + rj };
                    }
                    w
                })
                .collect()
        })
        .collect();
    let contract_cols = |m: &flock::r1cs::SparseBinaryMatrix, w: &[F128]| -> Vec<F128> {
        m.rows
            .iter()
            .map(|row| row.iter().map(|&j| w[j]).fold(F128::ZERO, |a, x| a + x))
            .collect()
    };
    let mut ms: Vec<Vec<F128>> = Vec::new();
    for w in &ws {
        ms.push(contract_cols(ma, w));
        ms.push(contract_cols(mb, w));
    }
    let ga: Vec<F128> = (0..nsub).map(|t| gmt[t] * subs[t].lc_alpha).collect();
    let gb: Vec<F128> = gmt.clone();
    let mut mrun: F128 = (0..nsub).map(|t| gmt[t] * subs[t].matpart).fold(F128::ZERO, |a, x| a + x);
    // sanity: the deferred matpart equals the bilinear form over the matrices.
    for (t, d) in subs.iter().enumerate() {
        let direct = d.lc_alpha
            * ms[2 * t].iter().zip(&us[t]).map(|(&m, &u)| m * u).fold(F128::ZERO, |a, x| a + x)
            + ms[2 * t + 1].iter().zip(&us[t]).map(|(&m, &u)| m * u).fold(F128::ZERO, |a, x| a + x);
        assert_eq!(direct, d.matpart, "matpart bilinear identity, sub {t}");
    }
    let mut mscr = Vec::new();
    let mut r_row = Vec::new();
    for _ in 0..klog {
        let pairs: Vec<(&[F128], &[F128], F128)> = (0..nsub)
            .flat_map(|t| [(&us[t][..], &ms[2 * t][..], ga[t]), (&us[t][..], &ms[2 * t + 1][..], gb[t])])
            .collect();
        let (g1, gi) = round_msg(&pairs);
        h.observe(g1);
        h.observe(gi);
        let r = h.sample();
        mscr.extend([g1, gi]);
        r_row.push(r);
        let g0 = mrun + g1;
        let c1 = g0 + g1 + gi;
        mrun = gi * r * r + c1 * r + g0;
        for u in us.iter_mut() {
            fold_lsb(u, r);
        }
        for m in ms.iter_mut() {
            fold_lsb(m, r);
        }
    }
    let eq_rstar = primitives::multilinear::build_eq(&r_row);
    let contract_rows = |m: &flock::r1cs::SparseBinaryMatrix| -> Vec<F128> {
        let mut out = vec![F128::ZERO; 1 << klog];
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
    let mut wa = vec![F128::ZERO; 1 << klog];
    let mut wb = vec![F128::ZERO; 1 << klog];
    for t in 0..nsub {
        let (sa, sb2) = (ga[t] * us[t][0], gb[t] * us[t][0]);
        for j in 0..1 << klog {
            wa[j] += sa * ws[t][j];
            wb[j] += sb2 * ws[t][j];
        }
    }
    let mut r_col = Vec::new();
    for _ in 0..klog {
        let pairs: Vec<(&[F128], &[F128], F128)> =
            vec![(&acol, &wa, F128::ONE), (&bcol, &wb, F128::ONE)];
        let (g1, gi) = round_msg(&pairs);
        h.observe(g1);
        h.observe(gi);
        let r = h.sample();
        mscr.extend([g1, gi]);
        r_col.push(r);
        let g0 = mrun + g1;
        let c1 = g0 + g1 + gi;
        mrun = gi * r * r + c1 * r + g0;
        for tb in [&mut acol, &mut bcol, &mut wa, &mut wb] {
            fold_lsb(tb, r);
        }
    }
    let (v_a, v_b) = (acol[0], bcol[0]);
    assert_eq!(mrun, v_a * wa[0] + v_b * wb[0], "matrix sumcheck terminal");
    // sanity for the GUEST's succinct terminal-weight formulas.
    {
        let eqr = primitives::multilinear::build_eq(&r_row[..6]);
        let eqc = primitives::multilinear::build_eq(&r_col[..6]);
        let (mut wam, mut wbm) = (F128::ZERO, F128::ZERO);
        for (t, d) in subs.iter().enumerate() {
            let lam = flock::zerocheck::multilinear::lagrange_weights_naive(6, d.zz);
            let mut urow: F128 = (0..64).map(|i| lam[i] * eqr[i]).fold(F128::ZERO, |a, x| a + x);
            for (k, &z) in d.zrho8.iter().enumerate() {
                urow *= F128::ONE + z + r_row[6 + k];
            }
            let mut wcol: F128 = (0..64).map(|i| d.lcz[i] * eqc[i]).fold(F128::ZERO, |a, x| a + x);
            for (j, &rj) in d.lrr.iter().enumerate() {
                wcol *= F128::ONE + rj + r_col[klog - 1 - j];
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
    let mut e = Sponge::empty();
    e.observe(seed[0]);
    e.observe(seed[1]);
    for d in subs {
        e.observe(d.pi[0]);
        e.observe(d.pi[1]);
    }
    for &v in &r_bc {
        e.observe(v);
    }
    e.observe(v_bc);
    let r_m: Vec<F128> = r_row.iter().chain(&r_col).copied().collect();
    for &v in &r_m {
        e.observe(v);
    }
    e.observe(v_a);
    e.observe(v_b);

    let hints = vec![
        ("fs_seed".to_string(), vec![seed[0], seed[1]]),
        ("bc_sumcheck_msgs".to_string(), bscr),
        ("mat_sumcheck_msgs".to_string(), mscr),
        ("bc_star_hint".to_string(), vec![v_bc]),
        ("mat_stars_hint".to_string(), vec![v_a, v_b]),
    ];
    (
        hints,
        e.state(),
        ReducedClaims {
            r_bc,
            v_bc,
            r_m,
            v_a,
            v_b,
        },
    )
}

/// Discharge the three fixed-polynomial claims deferred by the guest.
fn check_reduced(program: &Program, red: &ReducedClaims) -> Result<(), RecursiveVerifyError> {
    let stacked = stacked_bytecode(program);
    let expected_bc = stacked.len().trailing_zeros() as usize;
    if red.r_bc.len() != expected_bc {
        return Err(RecursiveVerifyError::InvalidDeferredShape);
    }
    if mle_eval(&stacked, &red.r_bc) != red.v_bc {
        return Err(RecursiveVerifyError::BytecodeClaim);
    }
    let (ma, mb) = flock::blake3::matrices();
    let klog = flock::blake3::K_LOG;
    if red.r_m.len() != 2 * klog {
        return Err(RecursiveVerifyError::InvalidDeferredShape);
    }
    let eq_r = primitives::multilinear::build_eq(&red.r_m[..klog]);
    let eq_c = primitives::multilinear::build_eq(&red.r_m[klog..]);
    let direct = |m: &flock::r1cs::SparseBinaryMatrix| -> F128 {
        let mut acc = F128::ZERO;
        for (i, row) in m.rows.iter().enumerate() {
            let s = row.iter().map(|&j| eq_c[j]).fold(F128::ZERO, |a, x| a + x);
            acc += eq_r[i] * s;
        }
        acc
    };
    if direct(ma) != red.v_a {
        return Err(RecursiveVerifyError::MatrixAClaim);
    }
    if direct(mb) != red.v_b {
        return Err(RecursiveVerifyError::MatrixBClaim);
    }
    Ok(())
}

/// Config + hints for the recursion guest (`guests/recursion.py`), built
/// from the REAL `cpu::layout` of the inner program and the transcript trace of
/// a real `cpu::verify` run (zero hand-mirroring drift).
fn gen_verify(
    program: &Program,
    pi: [F128; 2],
    proof: &lean_vm::cpu::Proof,
    summary: &lean_vm::cpu::VerifySummary,
    ops: &[TraceOp],
) -> (Vec<(String, Vec<F128>)>, SubDefer) {
    let l = lean_vm::cpu::layout(
        &program.prog,
        proof.stream[0].lo as usize,
        [1, 2, 3, 4, 5, 6].map(|i| proof.stream[i].lo as usize),
        pi,
    );
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let lays: Vec<lean_vm::leaf::Layout> = sides.iter().map(|b| lean_vm::leaf::layout(b)).collect();
    let smu: Vec<usize> = lays.iter().map(|x| x.mu).collect();
    // Fixed capacities: every buffer/stride placeholder is a global cap so
    // the placeholder map is SHAPE-INDEPENDENT (the definition of generic).
    let mumax = 40usize;
    let taumax_cap = 33usize;
    let stream_cap = 8192usize;
    assert!(*smu.iter().max().unwrap() <= mumax && proof.stream.len() <= stream_cap);

    // ---- flattened block/coord descriptors ----
    let (mut sblk, mut bkappa, mut bc0, mut bcn) = (vec![0usize], vec![], vec![], vec![]);
    let (mut ct, mut cval, mut fpv) = (vec![], vec![], vec![]);
    let mut nclaims = 0usize;
    // Claim dedup (mirrors leaf.rs): ALL three trees share their GKR point, so
    // a column read by two same-kappa blocks streams/opens once. Key: (col, kappa).
    let mut seen_claims: std::collections::HashSet<(usize, usize)> = Default::default();
    let mut nbcv = 0usize;
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            bkappa.push(blk.kappa);
            bc0.push(ct.len());
            bcn.push(blk.coords.len());
            for c in &blk.coords {
                let (t, v, f) = match c {
                    Coord::Const(v) => (0u128, *v, *v),
                    Coord::Col(i) => {
                        if seen_claims.insert((*i, blk.kappa)) {
                            nclaims += 1;
                        }
                        (1, F128::ZERO, l.pad[*i])
                    }
                    Coord::GCol(i) => {
                        if seen_claims.insert((*i, blk.kappa)) {
                            nclaims += 1;
                        }
                        (2, F128::ZERO, G * l.pad[*i])
                    }
                    Coord::Index => (3, F128::ZERO, F128::ZERO),
                    Coord::Public(_) => {
                        nbcv += 1;
                        (4, F128::ZERO, F128::ZERO)
                    }
                };
                ct.push(t);
                cval.push(u(v));
                fpv.push(u(f));
            }
        }
        sblk.push(bkappa.len());
    }

    // ---- typed extraction: proof structs + the verifier's summary ----
    // Drift check: replaying the recorded trace from the seed must reproduce
    // every challenge and grind the native run produced.
    let fs_seed = lean_vm::cpu::fs_seed(program);
    let seed = Sponge::new(b"leanvm-b", &[fs_seed[0], fs_seed[1], pi[0], pi[1]]);
    seed.clone().replay(ops);

    // Grinding digests are the only trace-borne data (they are functions of
    // sponge states): the first Pow is the bus grind; among the rest, fold
    // grinds carry bits > 0 and query-phase grinds carry bits = 0.
    let pows: Vec<(u64, u32, F128)> = ops
        .iter()
        .filter_map(|op| match op {
            TraceOp::Pow { nonce, bits, digest } => Some((*nonce, *bits, *digest)),
            _ => None,
        })
        .collect();
    let _gdig = pows[0].2; // digest bits now advice-decomposed in-guest

    // Bus: the bytecode claims carry the push/pull ζ_lo points and sb.
    let kbc = summary.bytecode_claims[0].point.len() - 3;
    let zeta: Vec<F128> = summary.bytecode_claims[0].point[..kbc].to_vec();
    let sb: Vec<F128> = summary.bytecode_claims[0].point[kbc..].to_vec();

    let taus = l.taus;
    let ncol: Vec<usize> = lean_vm::tables::tables().iter().map(|t| t.constraint_columns().len()).collect();

    // Flock replay data, all named struct fields.
    let n_log_b3 = l.taus[5];
    let lcrounds = flock::blake3::K_LOG - 6;
    let zcf = [summary.zc_claim.a_eval, summary.zc_claim.b_eval];
    let zc_z = summary.zc_claim.z;
    let zrho = summary.zc_claim.mlv_challenges.clone();
    let lc_alpha = summary.lc_claim.alpha;
    let lc_beta = summary.lc_claim.beta;
    let lrr = summary.lc_claim.r_rounds.clone();


    let evtot_e: usize = ncol.iter().sum();
    let ncl = nclaims + evtot_e + 1; // bus + constraint + the PI claim

    // ---- the stacked opening: config + the opening summary ----
    let stack_mu = l.m;
    let vcfg = pcs::ligerito::LigeritoSecurityConfig::derive_config(stack_mu + 7)
        .and_then(|s| s.to_config())
        .expect("stack ligerito config");
    let log_n = stack_mu;
    let shapes = vcfg.level_shapes(log_n);
    let (nlev, r) = (shapes.levels, vcfg.level_steps);
    let (klvl, lmc, _yr_log_n) = (shapes.ks, shapes.log_msg_cols, shapes.yr_log_n);
    let queries = vcfg.queries.clone();
    // query packing: each squeezed word carries 128/depth positions.
    let depth: Vec<usize> = shapes.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    let per: Vec<usize> = depth.iter().map(|&d| 128 / d).collect();
    let fgb = |lvl: usize| vcfg.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;

    // The Ligerito opening's scalars close the stream: start msg (2), per
    // level the fold (nonce? + msg) words, then root (2) / yr words, one
    // query-grind nonce, and an intro msg (2) at every non-final level.
    let lig_stream_words: usize = 2
        + (0..nlev)
            .map(|lvl| {
                let folds: usize =
                    (0..klvl[lvl]).map(|j| 2 + usize::from(fgb(lvl) - j as i64 > 0)).sum();
                folds
                    + if lvl == nlev - 1 { (1 << shapes.yr_log_n) + 1 } else { 2 + 1 + 2 }
            })
            .sum::<usize>();
    // The lincheck rounds and z_partial sit at fixed offsets from the FLOCK
    // tail (the stream up to the opening): [.. (e1,e_inf) x lcrounds |
    // z_partial (64) | s_hat_v (2 x 128) | the opening's scalars].
    let ns = proof.stream.len() - lig_stream_words;
    let lcr: Vec<F128> = proof.stream[ns - 256 - 64 - 2 * lcrounds..ns - 256 - 64].to_vec();
    let lcz: Vec<F128> = proof.stream[ns - 256 - 64..ns - 256].to_vec();

    // matpart = the deferred weighted matrix evaluation: the lincheck running
    // claim minus (= plus, char 2) the const-pin contribution.
    let r1cs = flock::blake3::build_block_r1cs(n_log_b3);
    let pincol = r1cs.const_pin.expect("blake3 r1cs has a const pin");
    let mut lrun = lc_alpha * zcf[0] + zcf[1] + lc_beta;
    for i in 0..lcrounds {
        let (e1, ei, rv) = (lcr[2 * i], lcr[2 * i + 1], lrr[i]);
        let e0 = lrun + e1;
        let c1q = e0 + e1 + ei;
        lrun = ei * rv * rv + c1q * rv + e0;
    }
    let mut pinw = lc_beta;
    for (j, &rv) in lrr.iter().enumerate() {
        let bit = (pincol >> (flock::blake3::K_LOG - 1 - j)) & 1;
        pinw *= if bit == 1 { rv } else { F128::ONE + rv };
    }
    pinw *= lcz[pincol % 64];
    let matpart = lrun + pinw;

    let lig_raw = summary.opening.lig.query_squeezes.clone();
    // Grind sanity: in transcript order after the bus grind — per level, the
    // fold grinds (bits > 0 per the config schedule) then ONE query-phase
    // grind. The nonces themselves ride the shared stream now (raw words);
    // the trace is only cross-checked here.
    let qbits: Vec<u32> = (0..nlev).map(|lvl| vcfg.grinding_bits[lvl] as u32).collect();
    let mut grinds = pows[1..].iter();
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
    // bcv: the deferred bytecode evaluations at the SHARED push/pull point
    // (leaf's own scan, coord order; both bytecode blocks carry the same six).
    let (kbc2, bcv) = lean_vm::leaf::public_evals(&l.push, &zeta);
    assert_eq!(kbc2, kbc);
    assert_eq!(bcv.len(), nbcv / 2);
    let sb3: [F128; 3] = sb.clone().try_into().unwrap();
    let wbc = vec![lean_vm::leaf::stacked_bytecode_value(&bcv, &sb3)];
    // checkpoints: the verifier's phase-boundary sponge states (guest cvh).

    // ---- per-sub HINT data (the placeholder map is built once, elsewhere) ----
    // Per side, the kappa-descending packing order (as in leaf.rs::layout):
    // sort_order[side_base + rank] = g^{side-local index of the rank-r block}.
    // The guest only perm-checks it and derives offsets; any aligned tiling is
    // sound, so this canonical order just has to match the committed leaf.
    let mut sort_order: Vec<F128> = Vec::new();
    let mut gbase = 0usize;
    for blocks in sides.iter() {
        let n = blocks.len();
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by(|&a, &b| blocks[b].kappa.cmp(&blocks[a].kappa).then(a.cmp(&b)));
        for &i in &order {
            sort_order.push(g_pow(gbase + i)); // g^{global block index}
        }
        gbase += n;
    }
    let sch = lean_vm::cpu::schema();
    let b3base = sch.base[5];
    let valcols: Vec<usize> = lean_vm::tables::BLAKE3_VALUE_COLS.iter().map(|&c| b3base + c).collect();
    let log_mem = proof.stream[0].lo as usize;

    // ---- Phase E2 hints (the stacked Ligerito opening) ----
    let lig = &proof.openings[0];
    let numinter: Vec<usize> = klvl.iter().map(|&k| 1usize << k).collect();
    let lenris: usize = klvl.iter().sum();
    // positions per level from the packed squeezes.
    let positions: Vec<Vec<usize>> = (0..nlev)
        .map(|lv| {
            let d = depth[lv];
            let mut out = Vec::with_capacity(queries[lv]);
            for v in &lig_raw[lv] {
                let bits = (v.lo as u128) | ((v.hi as u128) << 64);
                for j in 0..per[lv].min(queries[lv] - out.len()) {
                    out.push(((bits >> (j * d)) as usize) & (shapes.block_len[lv] - 1));
                }
            }
            out
        })
        .collect();
    let rows_of = |lv: usize| -> &Vec<Vec<F128>> {
        if lv == 0 {
            &lig.initial_proof.opened_rows
        } else if lv == r {
            &lig.final_proof.opened_rows
        } else {
            &lig.level_proofs[lv - 1].opened_rows
        }
    };
    let path_of = |lv: usize| -> &Vec<[u8; 32]> {
        if lv == 0 {
            &lig.initial_proof.merkle_proof
        } else if lv == r {
            &lig.final_proof.merkle_proof
        } else {
            &lig.level_proofs[lv - 1].merkle_proof
        }
    };
    let hb32 = |h: [u8; 32]| {
        let wd = |o: usize| u64::from_le_bytes(h[o..o + 8].try_into().unwrap());
        [F128::new(wd(0), wd(8)), F128::new(wd(16), wd(24))]
    };
    let (mut lrows_flat, mut lpaths_flat) = (Vec::new(), Vec::new());
    for lv in 0..nlev {
        let (rows_exp, path_exp) =
            pcs::ligerito::expand_level_opening(shapes.block_len[lv], &positions[lv], rows_of(lv), numinter[lv], path_of(lv))
                .expect("expand stacked level opening");
        for row in &rows_exp {
            lrows_flat.extend_from_slice(row);
        }
        for &h in &path_exp {
            lpaths_flat.extend_from_slice(&hb32(h));
        }
    }
    let qpkdv = l.placements[lean_vm::cpu::QPKD].n_vars;

    // claim descriptors, in exact clv order.
    let (mut cpbuf, mut cpoff, mut cplen, mut cslot, mut csel, mut yt) = (vec![], vec![], vec![], vec![], vec![], vec![]);
    let (mut nover_v, mut seln_v): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
    let qpkd_pl = l.placements[lean_vm::cpu::QPKD];
    // Per claim: nvt = full low span; when nvt > lenris the point overlaps the
    // residual y region by nover coords (runtime factors in the terminal); the
    // selector's in-ris part has seln bits; the y-pattern is the rest.
    let mut push_desc = |buf: usize, off: usize, plen: usize, slot: usize, sel_full: usize, nvt: usize| {
        let nover = nvt.saturating_sub(lenris);
        let seln = lenris.saturating_sub(nvt);
        cpbuf.push(buf);
        cpoff.push(off);
        cplen.push(plen);
        cslot.push(slot);
        csel.push(if seln == 0 { 0 } else { sel_full & ((1usize << seln) - 1) });
        nover_v.push(nover);
        seln_v.push(seln);
        yt.push(sel_full >> seln);
    };
    let mut desc_seen: std::collections::HashSet<(usize, usize)> = Default::default();
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i) = c {
                    if !desc_seen.insert((*i, blk.kappa)) {
                        continue; // deduped: pooled once at its first occurrence
                    }
                    if valcols.contains(i) {
                        let slot_i = lean_vm::blake3_flock::SLOTS[valcols.iter().position(|v| v == i).unwrap()];
                        let nvt = 7 + blk.kappa;
                        push_desc(3, 0, blk.kappa, slot_i, qpkd_pl.offset >> nvt, nvt);
                    } else {
                        let pl = l.placements[*i];
                        push_desc(0, 0, blk.kappa, 0, pl.offset >> blk.kappa, blk.kappa);
                    }
                }
            }
        }
    }
    for (t, table) in lean_vm::tables::tables().iter().enumerate() {
        for &c in table.constraint_columns() {
            let col = sch.base[t] + c;
            let pl = l.placements[col];
            if pl.is_virtual() {
                let slot_i = lean_vm::blake3_flock::SLOTS
                    [valcols.iter().position(|v| *v == col).unwrap()];
                let nvt = 7 + taus[t];
                push_desc(3, 0, taus[t], slot_i, qpkd_pl.offset >> nvt, nvt);
            } else {
                push_desc(1, t * taumax_cap, taus[t], 0, pl.offset >> taus[t], taus[t]);
            }
        }
    }
    {
        // PI claim on MEM: point = [r_m, 0, 0, ...]. Coords beyond lenris are
        // const zero, so they fold into the y pattern (required-zero bits)
        // instead of runtime overlap factors: cap the low span at lenris and
        // shift the selector pattern left by the folded coord count.
        let pl = l.placements[lean_vm::cpu::MEM];
        let folded = pl.n_vars.saturating_sub(lenris);
        let low = pl.n_vars - folded;
        push_desc(2, 0, low, 0, (pl.offset >> pl.n_vars) << folded, low);
    }
    assert_eq!(cpbuf.len(), ncl, "descriptor count == pool size");
    let rssel_full = qpkd_pl.offset >> qpkdv;
    let yrs = rssel_full >> (lenris - qpkdv);
    let rssel = rssel_full & ((1usize << (lenris - qpkdv)) - 1);

    let mut svk_flat = Vec::new();
    let mut ivk_flat = Vec::new();
    for &lmc_lv in lmc.iter().take(nlev) {
        let s2 = pcs::ligerito::eval_sk_at_vks(lmc_lv);
        for &v in &s2 {
            svk_flat.push(v);
            ivk_flat.push(if v == F128::ZERO { F128::ZERO } else { v.inv() });
        }
    }
    let deferred = SubDefer {
        pi,
        kbc,
        zeta,
        sb: sb.clone(),
        wbc: wbc.clone(),
        lc_alpha,
        zz: zc_z,
        zrho8: zrho[..lcrounds].to_vec(),
        lrr: lrr.clone(),
        lcz: lcz.clone(),
        matpart,
    };

    let hints = vec![
        ("stream".to_string(), {
            let mut v = proof.stream.clone();
            v.resize(stream_cap, F128::ZERO);
            v
        }),
        ("bytecode_vals".to_string(), bcv),
        ("matpart".to_string(), vec![matpart]),
        ("merkle_leaf_rows".to_string(), lrows_flat),
        ("merkle_paths".to_string(), lpaths_flat),
        ("sub_pis".to_string(), vec![pi[0], pi[1]]),
        // slacks bounding each claim'"'"'s reads to the written regions (so an
        // over-long hint cannot pull free padding): low_len <= mu_s/tau_t
        // (zeta/rho) and low_len(+7 for qpkd) <= lenris (fold challenges).
        // per-claim overlap count, for the exact length pin: nover = the
        // amount by which the claim's total vars exceed the fold rounds.
        ("claim_nover".to_string(), (0..ncl).map(|j| g_pow(nover_v[j])).collect()),
        // the pi claim's low dimension is min(log_mem, lenris); certify it as
        // a min (<= both, == one) so pi is pinned like every other claim.
        ("pi_cplen".to_string(), vec![g_pow(log_mem.min(lenris))]),
        ("claim_qpkd_slot_bits".to_string(), {
            let mut v = Vec::new();
            for &slot in cslot.iter().take(ncl) {
                for k in 0..7 {
                    v.push(F128::new(((slot >> k) & 1) as u64, 0));
                }
            }
            v
        }),
        ("claim_sel_bits".to_string(), {
            let mut v = Vec::new();
            for &sel in csel.iter().take(ncl) {
                for k in 0..33 {
                    v.push(F128::new(((sel >> k) & 1) as u64, 0));
                }
            }
            v
        }),
        // (no overlap-mask stream: the guest bakes every prefix mask and
        // selects row nover, so the mask is not prover-chosen at all.)
        ("claim_yslot_bits".to_string(), {
            let mut v = Vec::new();
            for j in 0..ncl {
                for k in 0..8 {
                    let b = if k < nover_v[j] { 0 } else { (yt[j] >> (k - nover_v[j])) & 1 };
                    v.push(F128::new(b as u64, 0));
                }
            }
            v
        }),
        ("rs_yslot_bits".to_string(), (0..8).map(|k| F128::new(((yrs >> k) & 1) as u64, 0)).collect()),
        ("rs_sel_bits".to_string(), (0..33).map(|k| F128::new(((rssel >> k) & 1) as u64, 0)).collect()),
        ("sort_order".to_string(), sort_order.clone()),
    ];
    (hints, deferred)
}

/// Everything needed to run one N→1 recursion batch EXCEPT compiling the
/// guest: the placeholder map (identical for every shape of the fixed inner
/// program), the merged per-sub witness entries, the outer statement, and the
/// data to discharge the reduced claims. Splitting the build from the compile
/// lets one compiled guest serve many batches (see `recursion_generic_many`).
struct Batch {
    merged: Vec<(String, Vec<Vec<F128>>)>,
    program0: Program,
    statement: RecursiveStatement,
    nsub: usize,
    total_inner_cycles: usize,
}

impl Batch {
    fn public_input(&self) -> [F128; 2] {
        self.statement.public_input(lean_vm::cpu::fs_seed(&self.program0))
    }

    /// Install this batch's generated hints and produce the complete proof
    /// bundle. Keeping assembly here makes it impossible for tests and callers
    /// to accidentally omit or mismatch one of the deferred components.
    fn prove(&self, guest: &mut Program) -> (RecursiveProof, lean_vm::cpu::Stats) {
        for (name, entries) in &self.merged {
            guest.set_witness(name, entries.clone());
        }
        let (outer_proof, stats) = prove(guest, self.public_input());
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
fn build_batch(inner: &[(usize, usize)]) -> Batch {
    assert!(!inner.is_empty(), "a recursion batch cannot be empty");
    let nsub = inner.len();
    let mut total_inner_cycles = 0usize;
    let mut protos = Vec::new();
    for (k, &(hashes, iters)) in inner.iter().enumerate() {
        let pi = [
            F128::new(0x1111_2222 + k as u64, 0x3333_4444),
            F128::new(0x5555_6666, 0x7777_8888 + k as u64),
        ];
        let (program, proof, inner_cycles) = prove_inner(pi, hashes, iters);
        total_inner_cycles += inner_cycles;
        trace_start();
        let summary = verify(&program, &pi, &proof).expect("inner verifies");
        let ops = trace_take();
        protos.push((program, pi, proof, summary, ops));
    }
    let mut merged: Vec<(String, Vec<Vec<F128>>)> = Vec::new();
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
    // spi is main-level (one hint site): merge the statements into one entry.
    let spi_all: Vec<F128> = subs.iter().flat_map(|d| [d.pi[0], d.pi[1]]).collect();
    let spi_pos = merged.iter().position(|(n, _)| n == "sub_pis").expect("spi hint");
    merged[spi_pos].1 = vec![spi_all];
    let (agg_hints, gpi, reduced) = gen_agg(program0, &subs);
    merged.extend(agg_hints.into_iter().map(|(n, v)| (n, vec![v])));
    let statement = RecursiveStatement {
        sub_statements: subs.iter().map(|d| d.pi).collect(),
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
        nsub,
        total_inner_cycles,
    }
}

/// The recursion program's placeholder map (the SHAPE-INDEPENDENT constants the
/// generic guest is compiled from), built from the inner program's STRUCTURE and
/// bytecode SIZE alone — no proof. Dummy layout sizes are fine: `rep` reads only the
/// size-independent block/coord structure and `kbc = log2(bytecode)`, so the guest
/// can be compiled BEFORE any inner proof exists. Because the map is a function of
/// the inner bytecode size alone, one compiled guest serves every shape.
#[allow(clippy::type_complexity)]
fn placeholder_map(program: &Program) -> BTreeMap<String, String> {
    // Any valid sizes drive the layout — rep depends only on structure + kbc.
    let l = lean_vm::cpu::layout(&program.prog, 20, [1usize << 10; 6], [F128::ZERO, F128::ZERO]);
    let kbc = program.prog.len().trailing_zeros() as usize;
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let mumax = 40usize;
    let taumax_cap = 33usize;
    let stream_cap = 8192usize;
    let taus = l.taus;
    let lcrounds = flock::blake3::K_LOG - 6;

    // ---- flattened block/coord descriptors (structural) ----
    let (mut sblk, mut bc0, mut bcn) = (vec![0usize], vec![], vec![]);
    let (mut ct, mut cval, mut fpv) = (vec![], vec![], vec![]);
    let (mut nclaims, mut nbcv, mut nblocks) = (0usize, 0usize, 0usize);
    // Claim dedup (mirrors leaf.rs): per coord, fresh = first (group, col,
    // kappa) occurrence gets the next pool slot; duplicates point at it.
    let mut slot_of: std::collections::HashMap<(usize, usize), usize> = Default::default();
    let (mut coord_fresh, mut coord_slot) = (vec![], vec![]);
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            bc0.push(ct.len());
            bcn.push(blk.coords.len());
            nblocks += 1;
            for c in &blk.coords {
                // One COORD_FRESH/COORD_CLAIM_SLOT entry PER coord (the guest
                // indexes them by global coord offset); only Col/GCol matter.
                let (mut fresh, mut slot) = (0usize, 0usize);
                if let Coord::Col(i) | Coord::GCol(i) = c {
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
                let (t, v, f) = match c {
                    Coord::Const(v) => (0u128, *v, *v),
                    Coord::Col(i) => (1, F128::ZERO, l.pad[*i]),
                    Coord::GCol(i) => (2, F128::ZERO, G * l.pad[*i]),
                    Coord::Index => (3, F128::ZERO, F128::ZERO),
                    Coord::Public(_) => { nbcv += 1; (4, F128::ZERO, F128::ZERO) }
                };
                ct.push(t); cval.push(u(v)); fpv.push(u(f));
            }
        }
        sblk.push(nblocks);
    }
    let ncol: Vec<usize> = lean_vm::tables::tables().iter().map(|t| t.constraint_columns().len()).collect();
    let evtot: usize = ncol.iter().sum();
    let ncl = nclaims + evtot + 1; // bus + constraint + the PI claim

    // ---- claim descriptors: buffer id + offset only (both structural) ----
    let sch = lean_vm::cpu::schema();
    let b3base = sch.base[5];
    let valcols: Vec<usize> = lean_vm::tables::BLAKE3_VALUE_COLS.iter().map(|&c| b3base + c).collect();
    let (mut cpbuf, mut cpoff) = (vec![], vec![]);
    let mut desc_seen: std::collections::HashSet<(usize, usize)> = Default::default();
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i) = c {
                    if !desc_seen.insert((*i, blk.kappa)) {
                        continue; // deduped: pooled once at its first occurrence
                    }
                    cpbuf.push(if valcols.contains(i) { 3 } else { 0 });
                    cpoff.push(0); // the ONE shared zeta lives at region 0
                }
            }
        }
    }
    for (t, table) in lean_vm::tables::tables().iter().enumerate() {
        for &c in table.constraint_columns() {
            let col = sch.base[t] + c;
            if l.placements[col].is_virtual() { cpbuf.push(3); cpoff.push(0); }
            else { cpbuf.push(1); cpoff.push(t * taumax_cap); }
        }
    }
    cpbuf.push(2); cpoff.push(0); // PI claim on MEM
    assert_eq!(cpbuf.len(), ncl, "descriptor count == pool size");

    // ---- the placeholder map ----
    let ints = |v: &[usize]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let us = |v: &[u128]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let flds = |v: &[F128]| format!("[{}]", v.iter().map(|&x| u(x).to_string()).collect::<Vec<_>>().join(", "));
    let mut rep = BTreeMap::new();
    let mut ps = |k: &str, v: String| { rep.insert(format!("{k}_PLACEHOLDER"), v); };
    ps("STREAM_CAP", stream_cap.to_string());
    ps("INV_GEN", u(G.inv()).to_string());
    ps("LAGRANGE_INV_0", u(G.inv()).to_string());
    ps("LAGRANGE_INV_1", u((F128::ONE + G).inv()).to_string());
    ps("LAGRANGE_INV_2", u((G * (F128::ONE + G)).inv()).to_string());
    ps("MU_CAP", mumax.to_string());
    ps("GKR_ROUNDS_CAP", (mumax * (mumax + 1) / 2 + mumax + 2).to_string());
    ps("GKR_POINTS_CAP", ((mumax + 1) * mumax).to_string());
    ps("SIDE_BLOCK_START", ints(&sblk));
    ps("N_BLOCKS", nblocks.to_string());
    let bks = lean_vm::cpu::block_kappa_sources(kbc);
    // Push and pull emit bus blocks in matched pairs, so their baked kappa-source
    // segments are identical; the guest computes only push's side total and
    // aliases pull's mu to push's on this basis.
    assert_eq!(bks[sblk[0]..sblk[1]], bks[sblk[1]..sblk[2]], "push/pull kappa sources must match");
    ps("BLOCK_KAPPA_SRC", ints(&bks.iter().map(|&(s, _)| s).collect::<Vec<_>>()));
    ps("BLOCK_KAPPA_ADJ", ints(&bks.iter().map(|&(_, a)| a).collect::<Vec<_>>()));
    ps("BLOCK_REAL_TABLE", ints(&bks.iter().map(|&(s, _)| if s >= 2 { s - 2 } else { 6 }).collect::<Vec<_>>()));
    let mut block_side = Vec::new();
    for (s, blocks) in sides.iter().enumerate() { block_side.extend(std::iter::repeat_n(s, blocks.len())); }
    ps("BLOCK_SIDE", ints(&block_side));
    ps("BLOCK_COORD_OFF", ints(&bc0));
    ps("BLOCK_COORD_COUNT", ints(&bcn));
    ps("COORD_TYPE", us(&ct));
    ps("COORD_CONST", us(&cval));
    ps("COORD_PAD_VAL", us(&fpv));
    ps("COORD_FRESH", ints(&coord_fresh));
    ps("COORD_CLAIM_SLOT", ints(&coord_slot));
    ps("N_BUS_CLAIMS", nclaims.to_string());
    let idxc: Vec<u128> = (0..34).map(|i| { let mut g2k = G; for _ in 0..i { g2k = g2k * g2k; } u(F128::ONE + g2k) }).collect();
    ps("INDEX_MLE_FACTORS", us(&idxc));
    ps("N_CLAIMS", ncl.to_string());
    ps("N_AIR_COLS", ints(&ncol));
    ps("AIR_COLS_CAP", (ncol.iter().max().unwrap() + 1).to_string());
    ps("N_TABLES", l.taus.len().to_string());
    ps("TAU_CAP", taumax_cap.to_string());
    // g^(push.mu - BUS_GRIND_SHIFT) is the bus PoW window
    // (leaf::grand_product_grinding_bits: bits = mu - (127 - SECURITY_BITS)).
    ps("BUS_GRIND_SHIFT", (127 - lean_vm::SECURITY_BITS).to_string());
    // Per-claim y-slot hint stride (overlap mask / slot bit rows).
    ps("YR_SLOT_STRIDE", "8".to_string());
    const MINB3: usize = 3;
    let fixed_challenges: Vec<F128> = flock::zerocheck::univariate_skip_optimized::small_challenges_ghash().into_iter().chain(flock::zerocheck::univariate_skip_optimized::medium_challenges_ghash()).collect();
    ps("FIXED_CHALLENGES", flds(&fixed_challenges));
    // Flock univariate skip: 6 skipped variables, then the fixed inner rounds.
    ps("K_SKIP", "6".to_string());
    ps("N_FIXED_CHALLENGE_ROUNDS", fixed_challenges.len().to_string());
    let one_plus_challenge_inv: Vec<F128> = fixed_challenges.iter().map(|&c| (F128::ONE + c).inv()).collect();
    ps("ONE_PLUS_CHALLENGE_INV", flds(&one_plus_challenge_inv));
    let phi: Vec<F128> = primitives::field::phi8::PHI_8_TABLE[..128].to_vec();
    ps("PHI8_NODES", flds(&phi));
    let inv_den = |nodes: &[F128], node: F128, skip: F128| { let mut d = F128::ONE; for &s in nodes { if s != skip { d *= node + s; } } d.inv() };
    let ilam: Vec<F128> = (0..64).map(|i| inv_den(&phi[64..128], phi[64 + i], phi[64 + i])).collect();
    let icmb: Vec<F128> = (0..64).map(|i| inv_den(&phi[..128], phi[64 + i], phi[64 + i])).collect();
    let isdom: Vec<F128> = (0..64).map(|i| inv_den(&phi[..64], phi[i], phi[i])).collect();
    ps("LAGRANGE_INV_LAMBDA", flds(&ilam));
    ps("LAGRANGE_INV_COMBINED", flds(&icmb));
    ps("LAGRANGE_INV_S", flds(&isdom));
    ps("LINCHECK_ROUNDS", lcrounds.to_string());
    let pincol = flock::blake3::build_block_r1cs(taus[5].max(MINB3)).const_pin.expect("blake3 r1cs has a const pin");
    ps("PIN_COLUMN", pincol.to_string());
    ps("K_LOG", flock::blake3::K_LOG.to_string());

    // ---- LIG candidate tables (fixed [minm, maxm] range; open_stacked config) ----
    let oshape = |m: usize| {
        let vc = pcs::ligerito::LigeritoSecurityConfig::derive_config(m + 7)
            .and_then(|s| s.to_config())
            .expect("candidate ligerito config");
        let sh = vc.level_shapes(m);
        let (cn, cr) = (sh.levels, vc.level_steps);
        let (ck, cl, cyr) = (sh.ks.clone(), sh.log_msg_cols.clone(), sh.yr_log_n);
        let cq = vc.queries.clone();
        let cd: Vec<usize> = sh.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
        let cp: Vec<usize> = cd.iter().map(|&d| 128 / d).collect();
        let cs: Vec<usize> = (0..cn).map(|i| cq[i].div_ceil(cp[i])).collect();
        let cni: Vec<usize> = ck.iter().map(|&k| 1usize << k).collect();
        let cqb: Vec<usize> = (0..cn).map(|lvl| vc.grinding_bits[lvl]).collect();
        let cfgb = |lvl: usize| vc.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;
        let mut cfb: Vec<usize> = Vec::new();
        for (lvl, &k) in ck.iter().enumerate().take(cn) { for j in 0..k { cfb.push((cfgb(lvl) - j as i64).max(0) as usize); } }
        let psum = |f: &dyn Fn(usize) -> usize| -> Vec<usize> { let mut o = Vec::with_capacity(cn); let mut acc = 0; for lv in 0..cn { o.push(acc); acc += f(lv); } o };
        let c_rowoff = psum(&|lv| cq[lv] * cni[lv]);
        let c_pathoff = psum(&|lv| cq[lv] * cd[lv] * 2);
        let c_sbitsoff = psum(&|lv| cs[lv] * 128);
        let c_qpoff = psum(&|lv| cs[lv] * cp[lv]);
        let c_svkoff = psum(&|lv| cl[lv] + 1);
        let c_foldbase = psum(&|lv| ck[lv]);
        let c_risstart: Vec<usize> = (0..cn).map(|k| c_foldbase[k] + ck[k]).collect();
        let mut c_svk = Vec::new();
        let mut c_ivk = Vec::new();
        for &cl_lv in cl.iter().take(cn) { for &v in &pcs::ligerito::eval_sk_at_vks(cl_lv) { c_svk.push(v); c_ivk.push(if v == F128::ZERO { F128::ZERO } else { v.inv() }); } }
        (cn, cr, cyr, ck, cl, cq, cd, cp, cs, cni, cqb, cfb, c_rowoff, c_pathoff, c_sbitsoff, c_qpoff, c_svkoff, c_foldbase, c_risstart, c_svk, c_ivk)
    };
    let (minm, maxm) = (22usize, 28usize);
    let cands: Vec<_> = (minm..=maxm).map(oshape).collect();
    let maxlev = cands.iter().map(|c| c.0).max().unwrap();
    let maxfolds = cands.iter().map(|c| c.11.len()).max().unwrap();
    let maxsvk = cands.iter().map(|c| c.19.len()).max().unwrap();
    ps("LIG_MAX_LEVELS", maxlev.to_string());
    ps("LIG_MAX_TOTAL_FOLDS", maxfolds.to_string());
    ps("LIG_MAX_VANISH_LEN", maxsvk.to_string());
    ps("LIG_MIN_LOG_SIZE", minm.to_string());
    let cks: Vec<(usize, usize)> = lean_vm::cpu::col_kappa_sources(kbc).into_iter().flatten().collect();
    ps("N_COMMITTED_COLS", cks.len().to_string());
    ps("COL_KAPPA_SRC", ints(&cks.iter().map(|&(s, _)| s).collect::<Vec<_>>()));
    ps("COL_KAPPA_ADJ", ints(&cks.iter().map(|&(_, a)| a).collect::<Vec<_>>()));
    ps("PCS_MIN_MU", lean_vm::pcs::MIN_MU.to_string());
    ps("LIG_LOG_MSG_COLS_CAP", cands.iter().map(|c| *c.4.iter().max().unwrap()).max().unwrap().to_string());
    ps("YR_LOG_CAP", cands.iter().map(|c| c.2).max().unwrap().to_string());
    {
        let pad = |v: &[usize], stride: usize| -> Vec<usize> { let mut o = v.to_vec(); o.resize(stride, 0); o };
        let flat = |f: &dyn Fn(&(usize, usize, usize, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<F128>, Vec<F128>)) -> Vec<usize>, stride: usize| -> Vec<usize> { cands.iter().flat_map(|c| pad(&f(c), stride)).collect() };
        let scal = |f: &dyn Fn(&(usize, usize, usize, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>, Vec<F128>, Vec<F128>)) -> usize| -> Vec<usize> { cands.iter().map(f).collect() };
        ps("LIG_N_LEVELS", ints(&scal(&|c| c.0)));
        ps("LIG_YR_LEVEL", ints(&scal(&|c| c.1)));
        ps("LIG_YR_LOG_LEN", ints(&scal(&|c| c.2)));
        ps("LIG_YR_LEN", ints(&scal(&|c| 1usize << c.2)));
        ps("LIG_TOTAL_FOLDS", ints(&scal(&|c| c.3.iter().sum())));
        ps("LIG_MAX_QUERIES", ints(&scal(&|c| *c.5.iter().max().unwrap())));
        ps("LIG_MAX_SQUEEZES", ints(&scal(&|c| *c.8.iter().max().unwrap())));
        ps("LIG_MAX_LOG_MSG_COLS", ints(&scal(&|c| *c.4.iter().max().unwrap())));
        ps("LIG_MAX_INTERLEAVE", ints(&scal(&|c| *c.9.iter().max().unwrap())));
        ps("LIG_POSITIONS_LEN", ints(&scal(&|c| (0..c.0).map(|lv| c.8[lv] * c.7[lv]).sum())));
        ps("LIG_SUMCHECK_LEN", ints(&scal(&|c| 2 * (c.3.iter().sum::<usize>() + c.0))));
        ps("LIG_ROWS_LEN", ints(&scal(&|c| (0..c.0).map(|lv| c.5[lv] * c.9[lv]).sum())));
        ps("LIG_PATHS_LEN", ints(&scal(&|c| (0..c.0).map(|lv| c.5[lv] * c.6[lv] * 2).sum())));
        ps("LIG_FOLD_GRIND_LEN", ints(&scal(&|c| c.3.iter().sum::<usize>() * 128)));
        ps("LIG_QUERY_GRIND_BITS", ints(&flat(&|c| c.10.clone(), maxlev)));
        ps("LIG_QUERIES", ints(&flat(&|c| c.5.clone(), maxlev)));
        ps("LIG_FOLDS", ints(&flat(&|c| c.3.clone(), maxlev)));
        ps("LIG_INTERLEAVE", ints(&flat(&|c| c.9.clone(), maxlev)));
        ps("LIG_LEAF_BYTES", ints(&flat(&|c| c.9.iter().map(|&n| n * 16).collect(), maxlev)));
        ps("LIG_LEAF_PAIRS", ints(&flat(&|c| c.9.iter().map(|&n| n / 2).collect(), maxlev)));
        ps("LIG_TREE_DEPTH", ints(&flat(&|c| c.6.clone(), maxlev)));
        ps("LIG_SQUEEZES", ints(&flat(&|c| c.8.clone(), maxlev)));
        ps("LIG_POSITIONS_OFF", ints(&flat(&|c| c.15.clone(), maxlev)));
        ps("LIG_LOG_QUERIES", ints(&flat(&|c| c.5.iter().map(|&q| log2_ceil(q)).collect(), maxlev)));
        ps("LIG_LOG_MSG_COLS", ints(&flat(&|c| c.4.clone(), maxlev)));
        ps("LIG_RESIDUAL_FOLD_OFF", ints(&flat(&|c| c.18.clone(), maxlev)));
        ps("LIG_RESIDUAL_PREFIX_LEN", ints(&flat(&|c| c.4.iter().map(|&m2| m2 - c.2).collect(), maxlev)));
        ps("LIG_FOLDS_OFF", ints(&flat(&|c| c.17.clone(), maxlev)));
        ps("LIG_ROWS_OFF", ints(&flat(&|c| c.12.clone(), maxlev)));
        ps("LIG_PATHS_OFF", ints(&flat(&|c| c.13.clone(), maxlev)));
        ps("LIG_VANISH_OFF", ints(&flat(&|c| c.16.clone(), maxlev)));
        ps("LIG_FOLD_GRIND_BITS", ints(&flat(&|c| c.11.clone(), maxfolds)));
        let mut svk2 = Vec::new();
        let mut ivk2 = Vec::new();
        for c in &cands {
            let mut s = c.19.clone();
            let mut iv = c.20.clone();
            s.resize(maxsvk, F128::ZERO);
            iv.resize(maxsvk, F128::ZERO);
            svk2.extend(s);
            ivk2.extend(iv);
        }
        ps("LIG_VANISH_VALS", flds(&svk2));
        ps("LIG_VANISH_INVS", flds(&ivk2));
    }
    ps("LIG_N_CANDIDATES", (maxm - minm + 1).to_string());
    ps("LIG_MIN_SHIFT_INV", u(g_pow(minm).inv()).to_string());
    ps("CLAIM_POINT_BUF", ints(&cpbuf));
    ps("CLAIM_POINT_OFF", ints(&cpoff));
    ps("QPKD_VARS_CAP", (33 + flock::blake3::K_LOG - 7).to_string());
    ps("BYTECODE_LOG", kbc.to_string());
    // The stacked bytecode: nbcv/2 encoding columns per side, packed along
    // log2_ceil(cols) selector bits. The defer region is 2*kbc points + sel
    // bits + 2 reduced + alpha + z_skip + 2*lcrounds rounds + 64 z_partial
    // + 1 matpart.
    let bc_cols = nbcv / 2;
    let log2_bc_cols = log2_ceil(bc_cols);
    ps("BYTECODE_COLS", bc_cols.to_string());
    ps("LOG2_BYTECODE_COLS", log2_bc_cols.to_string());
    ps("DEFER_SIZE", (kbc + log2_bc_cols + 2 * lcrounds + 68).to_string());
    ps("BYTECODE_VARS", (kbc + log2_bc_cols).to_string());
    let label_state = Sponge::new(b"leanvm-b", &[]).state();
    ps("TRANSCRIPT_SEED_0", u(label_state[0]).to_string());
    ps("TRANSCRIPT_SEED_1", u(label_state[1]).to_string());
    ps("TRACE_DUAL_BASIS", flds(&pcs::ring_switch::trace_dual_basis()[..]));
    rep
}

/// Compile the canonical recursion guest for this program and batch arity.
/// Both proving and verification use this function so they cannot drift.
fn recursion_guest(inner_program: &Program, nsub: usize) -> Program {
    let mut replacements = placeholder_map(inner_program);
    replacements.insert("NSUB_PLACEHOLDER".to_string(), nsub.to_string());
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/guests/recursion.py");
    compile(
        &parse_file_with_replacements(path, &replacements)
            .expect("the repository recursion guest must parse"),
    )
}

/// Run an `inner.len()`→1 recursive aggregation and verify the outer proof;
/// each entry `(hashes, iters)` shapes one inner proof of the fixed inner
/// program. Prints the benchmark report. The flow:
/// 1. compile the inner program (→ its bytecode size);
/// 2. compile the recursion guest (`guests/recursion.py` — the generic
///    map needs only that size);
/// 3. prove the inner proofs (and extract their hints);
/// 4. prove the recursion, verify, discharge the three reduced claims.
pub fn run_recursion(inner: &[(usize, usize)]) -> RecursiveProof {
    // 1 + 2: the recursion program is generic — its map needs only the inner
    // bytecode size — so it is compiled FIRST, before any inner proof.
    let program = inner_program();
    let t = std::time::Instant::now();
    let mut guest = recursion_guest(&program, inner.len());
    let t_compile = t.elapsed();
    // The recursion program size + compile time, BEFORE any inner proving.
    let real_instrs: usize = guest.fn_ranges.iter().map(|(_, _, len)| *len as usize).sum();
    eprintln!(
        "recursion program: {real_instrs} instructions (2^{} padded), compiled in {t_compile:?}",
        guest.prog.len().trailing_zeros()
    );
    // 3: prove the inner proofs and extract the recursion witness (hints).
    let batch = build_batch(inner);
    let nsub = batch.nsub;
    let total_inner_cycles = batch.total_inner_cycles;
    let t = std::time::Instant::now();
    let (recursive_proof, stats) = batch.prove(&mut guest);
    let t_prove = t.elapsed();
    let t = std::time::Instant::now();
    recursive_proof
        .verify(&batch.program0)
        .expect("complete recursive proof verifies");
    let t_verify = t.elapsed();
    let proof_bytes = bincode::serialized_size(&recursive_proof).expect("recursive proof is serializable");
    let pow = |x: usize| if x == 0 { "     -".into() } else { format!("2^{:.2}", (x as f64).log2()) };
    println!("\nrecursion {nsub}\u{2192}1: {nsub} inner proofs of {} cycles each", total_inner_cycles / nsub);
    println!(
        "  guest cycles (VM steps)     : {:>10} = {:>7}   ({:.2} / inner cycle)",
        stats.cycles,
        pow(stats.cycles),
        stats.cycles as f64 / total_inner_cycles as f64
    );
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"].iter().zip(&stats.counts) {
        println!("    {name:<6} instructions     : {c:>10} = {:>7}", pow(c));
    }
    println!("  committed witness size      : 2^{:.3}", (stats.committed as f64).log2());
    println!(
        "  data memory                 : 2^{} padded (2^{:.2} used)",
        stats.log_mem,
        (stats.mem_used as f64).log2()
    );
    println!("  recursive proof size        : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  outer proving               : {t_prove:?}");
    println!("  complete recursive verify   : {t_verify:?}");
    recursive_proof
}

/// THE recursion test: two ~1M-cycle inner proofs (log_mem 21, committed
/// 2^24.6, an m=33 stacked opening each), verified and aggregated by one
/// guest into one outer proof, whose three reduced claims are then discharged
/// natively.
#[test]
fn recursion_2to1() {
    run_recursion(&[(8, 1 << 15), (8, 1 << 15)]);
}

/// THE genericity milestone: ONE compiled guest bytecode verifies two inner
/// proofs of DIFFERENT sizes in the same aggregation (the placeholder map
/// depends only on the inner bytecode size, so one map covers both shapes).
#[test]
fn recursion_2to1_mixed() {
    run_recursion(&[(4, 1 << 13), (64, 1 << 15)]);
}

/// One compiled guest bytecode proves MANY inner runs with wildly different
/// opcode profiles and sizes, without recompilation. The configs span four
/// committed sizes (m in {22,23,24,25} - four distinct match_range opening
/// arms) and four BLAKE3 log-instance-counts (tau_5 in {3,4,5,6} - different
/// r1cs statement digests, flock reduction sizes, and pin prefixes). The
/// guest is compiled ONCE from the placeholder map, which is a function of the
/// inner bytecode size alone, so every shape is verified on the same Program
/// object. Ignored: ~6 full inner+outer proofs, minutes.
#[test]
#[ignore]
fn recursion_soundness_binds() {
    // Adversarial check that the layout-hint certifications actually BIND:
    // the honest proof verifies, and corrupting any of the once-free hints
    // (padding surplus, bus-leaf selectors + their packing order, and the
    // residual-slot pad coordinates) makes the guest reject. Uses the m=22
    // candidate, whose yr_log_n is below YR_LOG_CAP so the slot over-read
    // path is live. Ignored: several full inner+outer proofs.
    let cfg: &[(usize, usize)] = &[(4, 1 << 12)];
    let batch = build_batch(cfg);
    let mut guest = recursion_guest(&batch.program0, cfg.len());
    let public_input = batch.public_input();

    let run = |g: &mut Program, merged: &[(String, Vec<Vec<F128>>)]| -> bool {
        for (name, entries) in merged {
            g.set_witness(name, entries.clone());
        }
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (proof, _) = prove(g, public_input);
            verify(g, &public_input, &proof).is_ok()
        }))
        .unwrap_or(false)
    };

    assert!(run(&mut guest, &batch.merged), "honest proof must verify");

    // The first residual-slot PADDING coordinate (k = yr_log_n), shape-derived
    // from the fold ladder so the test survives changes to the fold constants
    // (INITIAL_K / LEVEL_K / RESIDUAL_MAX_LOG). This inner commits a stack of
    // log-size 22 (flock m = 22 + 7); YR_LOG_CAP is the max residual log over
    // the guest's dispatch candidates (mu 22..=28, mirroring gen_verify). The
    // guest only reads YR_LOG_CAP slot coords, so a pad coordinate to tamper
    // exists only when this candidate's yr_log_n sits BELOW the cap.
    let yr_log = |mu: usize| {
        pcs::ligerito::LigeritoSecurityConfig::derive_config(mu + 7)
            .and_then(|s| s.to_config())
            .expect("stacked opening config")
            .level_shapes(mu)
            .yr_log_n
    };
    let (stack_mu, yr_cap) = (22usize, (22..=28).map(yr_log).max().unwrap());
    let yr_pad_idx = yr_log(stack_mu);

    // each tamper flips one hint to a definitely-invalid value.
    let mut tampers: Vec<(&str, usize, F128)> = vec![
        ("fs_seed", 0, F128::ONE),          // wrong proving environment: own_pi (public input) must reject
        ("claim_nover", 0, g_pow(5)),        // wrong overlap: exact length pin must reject
        ("pi_cplen", 0, g_pow(2)),           // wrong pi dimension: min-cert must reject
    ];
    if yr_pad_idx < yr_cap {
        // pad coord (k >= yr_log_n): over-read weight must be zero-pinned
        tampers.push(("rs_yslot_bits", yr_pad_idx, F128::ONE));
    } else {
        eprintln!("rs_yslot_bits tamper skipped: yr_log_n == YR_LOG_CAP (no pad coordinate)");
    }
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
    // (The overlap mask is no longer a hint: the guest selects a baked
    // prefix-mask row by the pinned nover, so the point-reuse y-slot
    // over-read path is covered by the claim_nover tamper above.)
    eprintln!("all layout-hint tamperings correctly rejected");
}

#[test]
#[ignore]
fn recursion_generic_many() {
    // (hashes, iters) per inner run - deliberately diverse profiles.
    let configs: &[(usize, usize)] = &[
        (4, 1 << 12),  // m=22, tau_5=3
        (8, 1 << 13),  // m=23, tau_5=3
        (16, 1 << 14), // m=24, tau_5=4
        (8, 1 << 15),  // m=25, tau_5=3
        (32, 1 << 13), // m=23, tau_5=5
        (64, 1 << 13), // m=23, tau_5=6
    ];
    // The recursion program is generic: compile it ONCE, from the inner program's
    // size alone, BEFORE any inner proof exists. Genericity is then shown directly
    // — every shape below verifies against this one bytecode.
    let mut guest = recursion_guest(&inner_program(), 1);
    eprintln!("guest compiled ONCE ({} instrs)", guest.prog.len());
    for &cfg in configs {
        let batch = build_batch(&[cfg]);
        let (recursive_proof, _) = batch.prove(&mut guest);
        recursive_proof
            .verify(&batch.program0)
            .expect("complete recursive proof verifies");
        eprintln!("  verified: hashes={:>2}, iters=2^{}", cfg.0, (cfg.1 as f64).log2() as u32);
    }
    eprintln!("all {} shapes verified by the SAME guest bytecode", configs.len());
}
