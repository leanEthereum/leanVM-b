//! End-to-end N→1 recursion: one guest program (`guests/recursion.py`)
//! replays `cpu::verify` for NSUB proofs of a fixed inner program, batches
//! their deferred claims with three aggregation sumchecks, and binds the sub
//! statements, four reduced fixed-table evaluations, and transparent
//! ring-switch transpose checks to its own public input (doc.tex §Recursive
//! aggregation, §Deferred evaluation claims).
//!
//! Zero hand-mirroring: the transcript trace of a REAL `cpu::verify` run
//! (`transcript::trace_start`/`trace_take`) is the guest's mechanical spec —
//! `gen_verify` walks it structurally (a `Walk` cursor; `Sponge::replay` yields
//! the checkpoint states) to extract every hint value, and the real
//! `cpu::layout` supplies every compile-time shape. `gen_agg` mirrors the
//! guest's aggregation transcript and runs the three batching-sumcheck provers
//! (dense bytecode, two-phase sparse matrices, and trace-dual certification).
//! [`RecursiveProof::verify`] is the only public acceptance path: it verifies
//! the outer VM proof, evaluates every deferred fixed polynomial, and checks
//! every proof-bound transparent relation.

use std::collections::BTreeMap;

use pcs::ligerito::log2_ceil;
use lean_compiler::{compile, parse, parse_file_with_replacements};
use lean_vm::cpu::{Program, prove, verify};
use lean_vm::leaf::{Block, Coord};
use lean_vm::transcript::{Sponge, TraceOp, trace_start, trace_take};
use primitives::{
    field::{F128, G, g_pow},
    multilinear::mle_eval,
    pretty_f64, pretty_integer,
};

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
        "[inner] cycles={} committed=2^{}",
        pretty_integer(stats.cycles),
        pretty_f64((stats.committed as f64).log2())
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
    rs_coeffs: Vec<F128>,
    r_dprime: Vec<F128>,
    s_hat_v: Vec<F128>,
    rs_transposed: Vec<F128>,
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
    r_d: Vec<F128>,
    v_d: F128,
}

/// Proof-bound ring-switch data whose transparent bit-transpose relation is
/// cheaper to discharge natively than inside the recursion VM.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct RingChecks {
    r_dprime: Vec<F128>,
    s_hat_v: Vec<F128>,
    transposed: Vec<F128>,
}

/// Everything committed by the outer public input. Keeping this private makes
/// the deferred checks an implementation detail of recursive verification.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct RecursiveStatement {
    sub_statements: Vec<[F128; 2]>,
    reduced: ReducedClaims,
    ring_checks: Vec<RingChecks>,
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
        for &v in &self.reduced.r_d {
            sponge.observe(v);
        }
        sponge.observe(self.reduced.v_d);
        for check in &self.ring_checks {
            for &v in &check.r_dprime {
                sponge.observe(v);
            }
            for &v in &check.s_hat_v {
                sponge.observe(v);
            }
            for &v in &check.transposed {
                sponge.observe(v);
            }
        }
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
        if statement.ring_checks.len() != statement.sub_statements.len() {
            return Err(RecursiveVerifyError::InvalidDeferredShape);
        }
        let guest = recursion_guest(inner_program, statement.sub_statements.len());
        let public_input = statement.public_input(lean_vm::cpu::fs_seed(inner_program));
        verify(&guest, &public_input, &self.outer_proof)
            .map_err(RecursiveVerifyError::OuterProof)?;
        check_reduced(inner_program, &statement.reduced)?;
        check_ring_transposes(&statement.ring_checks)
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
    DualBasisClaim,
    RingTransposeClaim,
}

/// The fixed 14-var multilinear table
/// `D(k, i) = trace_dual_basis[i]^(2^k)`, with the seven `k` variables
/// occupying the low-order dimensions and the seven `i` variables the high.
fn trace_dual_frobenius_table() -> Vec<F128> {
    let basis = pcs::ring_switch::trace_dual_basis();
    let mut table = vec![F128::ZERO; 128 * 128];
    for (i, &delta) in basis.iter().enumerate() {
        let mut v = delta;
        for k in 0..128 {
            table[k + 128 * i] = v;
            v *= v;
        }
    }
    table
}

fn check_ring_transposes(checks: &[RingChecks]) -> Result<(), RecursiveVerifyError> {
    for check in checks {
        if check.r_dprime.len() != 7 || check.s_hat_v.len() != 256 || check.transposed.len() != 2 {
            return Err(RecursiveVerifyError::InvalidDeferredShape);
        }
        let eq = primitives::multilinear::build_eq(&check.r_dprime);
        let coeffs = pcs::ring_switch::linearized_eq_coeffs(&eq);
        for rs in 0..2 {
            let got = pcs::ring_switch::transposed_claim_linearized(
                &check.s_hat_v[128 * rs..128 * (rs + 1)],
                &coeffs,
            );
            if got != check.transposed[rs] {
                return Err(RecursiveVerifyError::RingTransposeClaim);
            }
        }
    }
    Ok(())
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
/// three batching-sumcheck PROVERS (dense bytecode; two-phase sparse matrices;
/// trace-dual coefficient certification),
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
        for &v in &d.rs_coeffs {
            h.observe(v);
        }
        for &v in &d.r_dprime {
            h.observe(v);
        }
        for &v in &d.s_hat_v {
            h.observe(v);
        }
        for &v in &d.rs_transposed {
            h.observe(v);
        }
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

    // ---- trace-dual Frobenius batching sumcheck ----
    //
    // Each sub-proof used a hinted coefficient vector
    //   c_t[k] = Σ_i eq(r''_t, i) D(k, i)
    // in its ring-switch computations. Batch all 128 identities per sub at a
    // random k-point `rho`, then reduce the remaining i-sum to one evaluation
    // of the fixed 14-var table D. This moves the 128x128 fixed transform out
    // of the recursion guest without trusting the hint.
    let gdt: Vec<F128> = (0..nsub).map(|_| h.sample()).collect();
    let rho: Vec<F128> = (0..7).map(|_| h.sample()).collect();
    let eq_rho = primitives::multilinear::build_eq(&rho);
    let mut drun = F128::ZERO;
    for (t, d) in subs.iter().enumerate() {
        drun += gdt[t]
            * d.rs_coeffs
                .iter()
                .zip(&eq_rho)
                .map(|(&c, &e)| c * e)
                .fold(F128::ZERO, |a, x| a + x);
    }
    let dtable = trace_dual_frobenius_table();
    let mut drow = vec![F128::ZERO; 128];
    for i in 0..128 {
        drow[i] = (0..128)
            .map(|k| eq_rho[k] * dtable[k + 128 * i])
            .fold(F128::ZERO, |a, x| a + x);
    }
    let mut dw = vec![F128::ZERO; 128];
    for (t, d) in subs.iter().enumerate() {
        let eq_dprime = primitives::multilinear::build_eq(&d.r_dprime);
        for i in 0..128 {
            dw[i] += gdt[t] * eq_dprime[i];
        }
    }
    let mut dscr = Vec::new();
    let mut r_dcol = Vec::new();
    for _ in 0..7 {
        let (g1, gi) = round_msg(&[(&drow, &dw, F128::ONE)]);
        h.observe(g1);
        h.observe(gi);
        let r = h.sample();
        dscr.extend([g1, gi]);
        r_dcol.push(r);
        let g0 = drun + g1;
        let c1 = g0 + g1 + gi;
        drun = gi * r * r + c1 * r + g0;
        fold_lsb(&mut drow, r);
        fold_lsb(&mut dw, r);
    }
    let v_d = drow[0];
    assert_eq!(drun, v_d * dw[0], "trace-dual sumcheck terminal");

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
    let r_d: Vec<F128> = rho.iter().chain(&r_dcol).copied().collect();
    for &v in &r_d {
        e.observe(v);
    }
    e.observe(v_d);
    for d in subs {
        for &v in &d.r_dprime {
            e.observe(v);
        }
        for &v in &d.s_hat_v {
            e.observe(v);
        }
        for &v in &d.rs_transposed {
            e.observe(v);
        }
    }

    let hints = vec![
        ("fs_seed".to_string(), vec![seed[0], seed[1]]),
        ("bc_sumcheck_msgs".to_string(), bscr),
        ("mat_sumcheck_msgs".to_string(), mscr),
        ("dual_sumcheck_msgs".to_string(), dscr),
        ("bc_star_hint".to_string(), vec![v_bc]),
        ("mat_stars_hint".to_string(), vec![v_a, v_b]),
        ("dual_star_hint".to_string(), vec![v_d]),
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
            r_d,
            v_d,
        },
    )
}

/// Discharge the four fixed-polynomial claims deferred by the guest.
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
    if red.r_d.len() != 14 {
        return Err(RecursiveVerifyError::InvalidDeferredShape);
    }
    if mle_eval(&trace_dual_frobenius_table(), &red.r_d) != red.v_d {
        return Err(RecursiveVerifyError::DualBasisClaim);
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
    // Fixed capacities: every buffer/stride placeholder is a global cap so
    // the placeholder map is SHAPE-INDEPENDENT (the definition of generic).
    let stream_cap = 8192usize;
    assert!(proof.stream.len() <= stream_cap);
    let nbcv = sides
        .iter()
        .flat_map(|blocks| blocks.iter())
        .flat_map(|block| &block.coords)
        .filter(|coord| matches!(coord, Coord::Public(_)))
        .count();

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

    // Flock replay data, all named struct fields.
    let n_log_b3 = l.taus[5];
    let lcrounds = flock::blake3::K_LOG - 6;
    let zcf = [summary.zc_claim.a_eval, summary.zc_claim.b_eval];
    let zc_z = summary.zc_claim.z;
    let zrho = summary.zc_claim.mlv_challenges.clone();
    let lc_alpha = summary.lc_claim.alpha;
    let lc_beta = summary.lc_claim.beta;
    let lrr = summary.lc_claim.r_rounds.clone();


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
    let s_hat_v = proof.stream[ns - 256..ns].to_vec();
    let r_dprime = summary.opening.r_dprime.clone();
    let eq_dprime = primitives::multilinear::build_eq(&r_dprime);
    let rs_coeffs = pcs::ring_switch::linearized_eq_coeffs(&eq_dprime);
    let rs_transposed: Vec<F128> = (0..2)
        .map(|rs| {
            pcs::ring_switch::transposed_claim_linearized(
                &s_hat_v[128 * rs..128 * (rs + 1)],
                &rs_coeffs,
            )
        })
        .collect();

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
    // ---- Phase E2 hints (the stacked Ligerito opening) ----
    let lig = &proof.openings[0];
    let numinter: Vec<usize> = klvl.iter().map(|&k| 1usize << k).collect();
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
        rs_coeffs: rs_coeffs.to_vec(),
        r_dprime,
        s_hat_v,
        rs_transposed: rs_transposed.clone(),
    };

    let hints = vec![
        ("stream".to_string(), {
            let mut v = proof.stream.clone();
            v.resize(stream_cap, F128::ZERO);
            v
        }),
        ("bytecode_vals".to_string(), bcv),
        ("matpart".to_string(), vec![matpart]),
        ("rs_coeffs".to_string(), deferred.rs_coeffs.clone()),
        ("rs_transposed".to_string(), rs_transposed),
        ("merkle_leaf_rows".to_string(), lrows_flat),
        ("merkle_paths".to_string(), lpaths_flat),
        ("sub_pis".to_string(), vec![pi[0], pi[1]]),
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
        ring_checks: subs
            .iter()
            .map(|d| RingChecks {
                r_dprime: d.r_dprime.clone(),
                s_hat_v: d.s_hat_v.clone(),
                transposed: d.rs_transposed.clone(),
            })
            .collect(),
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
    let block_index: std::collections::HashMap<usize, usize> = l
        .jagged_blocks
        .iter()
        .enumerate()
        .map(|(block, cols)| (l.placements[cols[0]].offset, block))
        .collect();
    let bks_for_claims = lean_vm::cpu::block_kappa_sources(kbc);
    let (mut cpbuf, mut cpoff, mut cpcol, mut cppad, mut cpslot, mut cpblockslot, mut cpblocklog, mut cprowkey) =
        (vec![], vec![], vec![], vec![], vec![], vec![], vec![], vec![]);
    let mut desc_seen: std::collections::HashSet<(usize, usize)> = Default::default();
    let mut block_idx = 0usize;
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i) = c {
                    if !desc_seen.insert((*i, blk.kappa)) {
                        continue; // deduped: pooled once at its first occurrence
                    }
                    cpbuf.push(if valcols.contains(i) { 3 } else { 0 });
                    cpoff.push(0); // the ONE shared zeta lives at region 0
                    let dense_col = if valcols.contains(i) { lean_vm::cpu::QPKD } else { *i };
                    let placement = l.placements[dense_col];
                    cpcol.push(block_index[&placement.offset]);
                    cpblockslot.push(placement.slot);
                    cpblocklog.push(placement.block_width_log);
                    cppad.push(if valcols.contains(i) { F128::ZERO } else { l.pad[*i] });
                    cpslot.push(
                        valcols
                            .iter()
                            .position(|v| v == i)
                            .map(|p| lean_vm::blake3_flock::VM_SLOTS[p])
                            .unwrap_or(0),
                    );
                    cprowkey.push(if valcols.contains(i) {
                        (3usize, 0usize, 0usize)
                    } else {
                        let (source, adjustment) = bks_for_claims[block_idx];
                        (0, source, adjustment)
                    });
                }
            }
            block_idx += 1;
        }
    }
    for (t, table) in lean_vm::tables::tables().iter().enumerate() {
        for &c in table.constraint_columns() {
            let col = sch.base[t] + c;
            if l.placements[col].is_virtual() {
                cpbuf.push(3);
                cpoff.push(0);
                let placement = l.placements[lean_vm::cpu::QPKD];
                cpcol.push(block_index[&placement.offset]);
                cpblockslot.push(placement.slot);
                cpblocklog.push(placement.block_width_log);
                cppad.push(F128::ZERO);
                let p = valcols.iter().position(|&v| v == col).unwrap();
                cpslot.push(lean_vm::blake3_flock::VM_SLOTS[p]);
                cprowkey.push((3, 0, 0));
            } else {
                cpbuf.push(1);
                cpoff.push(t * taumax_cap);
                let placement = l.placements[col];
                cpcol.push(block_index[&placement.offset]);
                cpblockslot.push(placement.slot);
                cpblocklog.push(placement.block_width_log);
                cppad.push(l.pad[col]);
                cpslot.push(0);
                cprowkey.push((1, t, 0));
            }
        }
    }
    cpbuf.push(2);
    cpoff.push(0); // PI claim on MEM
    let placement = l.placements[lean_vm::cpu::MEM];
    cpcol.push(block_index[&placement.offset]);
    cpblockslot.push(placement.slot);
    cpblocklog.push(placement.block_width_log);
    cppad.push(l.pad[lean_vm::cpu::MEM]);
    cpslot.push(0);
    cprowkey.push((2, 0, 0));
    assert_eq!(cpbuf.len(), ncl, "descriptor count == pool size");
    let mut row_ids = std::collections::HashMap::new();
    let mut claim_row_group = vec![0usize; ncl];
    let mut claim_row_rep = Vec::new();
    for j in 0..ncl {
        if cpbuf[j] == 3 {
            continue;
        }
        let next = row_ids.len();
        let group = *row_ids.entry(cprowkey[j]).or_insert_with(|| {
            claim_row_rep.push(j);
            next
        });
        claim_row_group[j] = group;
    }

    // Match pcs::geometric_claim_weights structurally: complete row-major
    // blocks get consecutive gamma exponents in selector order; q_pkd and
    // singleton blocks retain one rank each. The batch list contains only the
    // ordinary Jagged groups evaluated by the recursion terminal.
    let mut claim_gamma_rank = vec![usize::MAX; ncl];
    let (mut batch_rep, mut batch_row, mut batch_col, mut batch_log, mut batch_base) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let mut next_rank = 0usize;
    for i in 0..ncl {
        if claim_gamma_rank[i] != usize::MAX {
            continue;
        }
        if cpbuf[i] == 3 {
            claim_gamma_rank[i] = next_rank;
            next_rank += 1;
            continue;
        }
        let width = 1usize << cpblocklog[i];
        if width == 1 {
            claim_gamma_rank[i] = next_rank;
            batch_rep.push(i);
            batch_row.push(claim_row_group[i]);
            batch_col.push(cpcol[i]);
            batch_log.push(0);
            batch_base.push(next_rank);
            next_rank += 1;
            continue;
        }
        let mut by_slot = vec![None; width];
        for j in i..ncl {
            if claim_gamma_rank[j] == usize::MAX
                && cpbuf[j] != 3
                && claim_row_group[j] == claim_row_group[i]
                && cpcol[j] == cpcol[i]
                && cpblocklog[j] == cpblocklog[i]
            {
                assert!(by_slot[cpblockslot[j]].replace(j).is_none(), "duplicate claim for one Jagged block slot");
            }
        }
        assert!(by_slot.iter().all(Option::is_some), "Jagged membership partition must produce complete blocks");
        let members: Vec<usize> = by_slot.into_iter().map(Option::unwrap).collect();
        for (slot, &j) in members.iter().enumerate() {
            claim_gamma_rank[j] = next_rank + slot;
        }
        batch_rep.push(members[0]);
        batch_row.push(claim_row_group[i]);
        batch_col.push(cpcol[i]);
        batch_log.push(cpblocklog[i]);
        batch_base.push(next_rank);
        next_rank += width;
    }
    assert_eq!(next_rank, ncl);

    // Padding-prefix indicators depend only on (logical row point, physical
    // Jagged block), not on the column slot. Cache one per distinct pair used
    // by a nonzero padding value.
    let mut pad_prefix_ids = std::collections::HashMap::new();
    let mut claim_pad_prefix = vec![0usize; ncl];
    let (mut pad_prefix_row, mut pad_prefix_col) = (Vec::new(), Vec::new());
    for j in 0..ncl {
        if cpbuf[j] == 3 || cppad[j] == F128::ZERO {
            continue;
        }
        let key = (claim_row_group[j], cpcol[j]);
        let next = pad_prefix_ids.len();
        let prefix = *pad_prefix_ids.entry(key).or_insert_with(|| {
            pad_prefix_row.push(key.0);
            pad_prefix_col.push(key.1);
            next
        });
        claim_pad_prefix[j] = prefix;
    }

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
        assert!(
            cni.iter().all(|&n| n <= 64),
            "recursive Ligerito guest supports Merkle rows of at most one 1024-byte BLAKE3 chunk"
        );
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
    // Jagged packs only real prefixes, so small executions can reach the PCS
    // floor instead of the former aligned-stack minimum of 22. Tight packing
    // cannot exceed the old aligned layout, hence the upper bound is unchanged.
    let (minm, maxm) = (lean_vm::pcs::MIN_MU, 28usize);
    let cands: Vec<_> = (minm..=maxm).map(oshape).collect();
    let maxlev = cands.iter().map(|c| c.0).max().unwrap();
    let maxfolds = cands.iter().map(|c| c.11.len()).max().unwrap();
    let maxsvk = cands.iter().map(|c| c.19.len()).max().unwrap();
    ps("LIG_MAX_LEVELS", maxlev.to_string());
    ps("LIG_MAX_TOTAL_FOLDS", maxfolds.to_string());
    ps("LIG_MAX_VANISH_LEN", maxsvk.to_string());
    ps("LIG_MIN_LOG_SIZE", minm.to_string());
    let height_sources = lean_vm::cpu::col_height_sources(kbc);
    let ordered_heights: Vec<_> = l
        .jagged_blocks
        .iter()
        .map(|cols| (height_sources[cols[0]].unwrap(), cols.len().trailing_zeros() as usize))
        .collect();
    ps("N_COMMITTED_COLS", ordered_heights.len().to_string());
    ps(
        "COL_HEIGHT_KIND",
        ints(
            &ordered_heights
                .iter()
                .map(|(s, _)| usize::from(matches!(s, lean_vm::cpu::ColHeightSource::TableRows(_))))
                .collect::<Vec<_>>(),
        ),
    );
    ps(
        "COL_HEIGHT_SRC",
        ints(
            &ordered_heights
                .iter()
                .map(|(s, _)| match *s {
                    lean_vm::cpu::ColHeightSource::Pow2 { source, .. } => source,
                    lean_vm::cpu::ColHeightSource::TableRows(t) => t,
                })
                .collect::<Vec<_>>(),
        ),
    );
    ps(
        "COL_HEIGHT_ADJ",
        ints(
            &ordered_heights
                .iter()
                .map(|(s, width_log)| match *s {
                    lean_vm::cpu::ColHeightSource::Pow2 { adjustment, .. } => adjustment + *width_log,
                    lean_vm::cpu::ColHeightSource::TableRows(_) => *width_log,
                })
                .collect::<Vec<_>>(),
        ),
    );
    ps("COL_BLOCK_LOG", ints(&ordered_heights.iter().map(|(_, width_log)| *width_log).collect::<Vec<_>>()));
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
        ps("LIG_LEAF_PAIRS", ints(&flat(&|c| c.9.iter().map(|&n| n / 2).collect(), maxlev)));
        ps("LIG_LEAF_BLOCKS", ints(&flat(&|c| c.9.iter().map(|&n| n / 4).collect(), maxlev)));
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
    ps("CLAIM_COL", ints(&cpcol));
    ps("CLAIM_PAD", flds(&cppad));
    ps("CLAIM_QPKD_SLOT", ints(&cpslot));
    ps("CLAIM_BLOCK_SLOT", ints(&cpblockslot));
    ps("CLAIM_BLOCK_LOG", ints(&cpblocklog));
    ps("CLAIM_GAMMA_RANK", ints(&claim_gamma_rank));
    ps("N_CLAIM_ROWS", claim_row_rep.len().to_string());
    ps("CLAIM_ROW_GROUP", ints(&claim_row_group));
    ps("CLAIM_ROW_REP", ints(&claim_row_rep));
    ps("N_PAD_PREFIXES", pad_prefix_row.len().to_string());
    ps("PAD_PREFIX_ROW", ints(&pad_prefix_row));
    ps("PAD_PREFIX_COL", ints(&pad_prefix_col));
    ps("CLAIM_PAD_PREFIX", ints(&claim_pad_prefix));
    ps("N_JAGGED_BATCHES", batch_rep.len().to_string());
    ps("JAGGED_BATCH_REP", ints(&batch_rep));
    ps("JAGGED_BATCH_ROW", ints(&batch_row));
    ps("JAGGED_BATCH_COL", ints(&batch_col));
    ps("JAGGED_BATCH_LOG", ints(&batch_log));
    ps("JAGGED_BATCH_BASE", ints(&batch_base));
    ps("QPKD_VARS_CAP", (33 + flock::blake3::K_LOG - 7).to_string());
    ps("BYTECODE_LOG", kbc.to_string());
    // The stacked bytecode: nbcv/2 encoding columns per side, packed along
    // log2_ceil(cols) selector bits. The defer region is 2*kbc points + sel
    // bits + 2 reduced + alpha + z_skip + 2*lcrounds rounds + 64 z_partial
    // + 1 matpart + 128 ring-switch coefficients + 7 r_dprime coordinates
    // + 256 s_hat_v words + 2 transposed claims.
    let bc_cols = nbcv / 2;
    let log2_bc_cols = log2_ceil(bc_cols);
    ps("BYTECODE_COLS", bc_cols.to_string());
    ps("LOG2_BYTECODE_COLS", log2_bc_cols.to_string());
    ps("DEFER_SIZE", (kbc + log2_bc_cols + 2 * lcrounds + 461).to_string());
    ps("BYTECODE_VARS", (kbc + log2_bc_cols).to_string());
    let label_state = Sponge::new(b"leanvm-b", &[]).state();
    ps("TRANSCRIPT_SEED_0", u(label_state[0]).to_string());
    ps("TRANSCRIPT_SEED_1", u(label_state[1]).to_string());
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
/// 4. prove the recursion, verify, discharge the four reduced evaluations.
/// When `enable_tracing` is true, tracing starts after the inner proofs so the
/// emitted tree profiles the recursive aggregation itself.
pub fn run_recursion(inner: &[(usize, usize)], enable_tracing: bool) -> RecursiveProof {
    // 1 + 2: the recursion program is generic — its map needs only the inner
    // bytecode size — so it is compiled FIRST, before any inner proof.
    let program = inner_program();
    let t = std::time::Instant::now();
    let mut guest = recursion_guest(&program, inner.len());
    let t_compile = t.elapsed();
    // The recursion program size + compile time, BEFORE any inner proving.
    let real_instrs: usize = guest.fn_ranges.iter().map(|(_, _, len)| *len as usize).sum();
    eprintln!(
        "recursion program: {} instructions (2^{} padded), compiled in {} s",
        pretty_integer(real_instrs),
        pretty_integer(guest.prog.len().trailing_zeros()),
        pretty_f64(t_compile.as_secs_f64())
    );
    // 3: prove the inner proofs and extract the recursion witness (hints).
    let batch = build_batch(inner);
    let nsub = batch.nsub;
    let total_inner_cycles = batch.total_inner_cycles;
    if enable_tracing {
        primitives::init_tracing();
    }
    let trace_span =
        tracing::info_span!("Recursive aggregation", n = %pretty_integer(nsub)).entered();
    let t = std::time::Instant::now();
    let (recursive_proof, stats) = batch.prove(&mut guest);
    let t_prove = t.elapsed();
    let t = std::time::Instant::now();
    recursive_proof
        .verify(&batch.program0)
        .expect("complete recursive proof verifies");
    let t_verify = t.elapsed();
    let proof_bytes = bincode::serialized_size(&recursive_proof).expect("recursive proof is serializable");
    // tracing-forest renders the tree when its root span closes. Close it
    // before printing the benchmark report so the complete trace appears first.
    drop(trace_span);

    let pow = |x: usize| {
        if x == 0 {
            "     -".into()
        } else {
            format!("2^{}", pretty_f64((x as f64).log2()))
        }
    };
    println!(
        "\nrecursion {}\u{2192}1: {} inner proofs of {} cycles each",
        pretty_integer(nsub),
        pretty_integer(nsub),
        pretty_integer(total_inner_cycles / nsub)
    );
    println!(
        "  guest cycles (VM steps)     : {:>14} = {:>9}   ({} / inner cycle)",
        pretty_integer(stats.cycles),
        pow(stats.cycles),
        pretty_f64(stats.cycles as f64 / total_inner_cycles as f64)
    );
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"].iter().zip(&stats.counts) {
        println!(
            "    {name:<6} instructions     : {:>14} = {:>9}",
            pretty_integer(c),
            pow(c)
        );
    }
    println!(
        "  committed witness size      : 2^{}",
        pretty_f64((stats.committed as f64).log2())
    );
    println!(
        "  data memory                 : 2^{} padded (2^{} used)",
        pretty_integer(stats.log_mem),
        pretty_f64((stats.mem_used as f64).log2())
    );
    println!(
        "  recursive proof size        : {} KiB",
        pretty_f64(proof_bytes as f64 / 1024.0)
    );
    println!(
        "  outer proving               : {} s",
        pretty_f64(t_prove.as_secs_f64())
    );
    println!(
        "  complete recursive verify   : {} s",
        pretty_f64(t_verify.as_secs_f64())
    );
    recursive_proof
}

/// Minimum-shape recursion-guest execution smoke test. The full integration
/// test below additionally proves and verifies the outer execution.
#[test]
fn recursion_1to1_smoke() {
    let cfg = [(4, 1 << 12)];
    let batch = build_batch(&cfg);
    check_reduced(&batch.program0, &batch.statement.reduced).expect("honest reduced claims");
    check_ring_transposes(&batch.statement.ring_checks).expect("honest ring transposes");
    let mut bad_reduced = batch.statement.reduced.clone();
    bad_reduced.v_d += F128::ONE;
    assert!(matches!(
        check_reduced(&batch.program0, &bad_reduced),
        Err(RecursiveVerifyError::DualBasisClaim)
    ));
    let mut bad_ring = batch.statement.ring_checks.clone();
    bad_ring[0].transposed[0] += F128::ONE;
    assert!(matches!(
        check_ring_transposes(&bad_ring),
        Err(RecursiveVerifyError::RingTransposeClaim)
    ));
    let mut guest = recursion_guest(&batch.program0, cfg.len());
    for (name, entries) in &batch.merged {
        guest.set_witness(name, entries.clone());
    }
    let exec = guest.execute(batch.public_input());
    eprintln!("recursion smoke guest cycles: {}", pretty_integer(exec.cycles));

    // The coefficients are advice, but not trusted: changing one while
    // retaining the honest batched certificate must make the guest reject.
    let mut bad_merged = batch.merged.clone();
    let pos = bad_merged
        .iter()
        .position(|(name, _)| name == "rs_coeffs")
        .expect("ring-switch coefficient hint");
    bad_merged[pos].1[0][0] += F128::ONE;
    let mut bad_guest = recursion_guest(&batch.program0, cfg.len());
    for (name, entries) in &bad_merged {
        bad_guest.set_witness(name, entries.clone());
    }
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            bad_guest.execute(batch.public_input());
        }))
        .is_err(),
        "tampered ring-switch coefficient must be rejected"
    );
}

/// Two ~1M-cycle inner proofs, verified and aggregated by one guest into one
/// outer proof, whose four reduced evaluations are then discharged natively.
#[test]
fn recursion_2to1() {
    run_recursion(&[(8, 1 << 15), (8, 1 << 15)], false);
}

/// THE genericity milestone: ONE compiled guest bytecode verifies two inner
/// proofs of DIFFERENT sizes in the same aggregation (the placeholder map
/// depends only on the inner bytecode size, so one map covers both shapes).
#[test]
fn recursion_2to1_mixed() {
    run_recursion(&[(4, 1 << 13), (64, 1 << 15)], false);
}

/// Adversarial checks for the remaining named recursion hints. Jagged interval
/// bounds and padding adjustments are derived from public counts in-circuit,
/// rather than supplied as named witness streams.
#[test]
#[ignore]
fn recursion_soundness_binds() {
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

    for &(stream, idx, val) in &[("fs_seed", 0, F128::ONE)] {
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
    eprintln!("all named-hint tamperings correctly rejected");
}

/// One compiled guest bytecode proves many inner runs with different opcode
/// profiles, Jagged committed sizes, and BLAKE3 instance counts.
#[test]
#[ignore]
fn recursion_generic_many() {
    // (hashes, iters) per inner run - deliberately diverse profiles.
    let configs: &[(usize, usize)] = &[
        (4, 1 << 12),
        (8, 1 << 13),
        (16, 1 << 14),
        (8, 1 << 15),
        (32, 1 << 13),
        (64, 1 << 13),
    ];
    // The recursion program is generic: compile it ONCE, from the inner program's
    // size alone, BEFORE any inner proof exists. Genericity is then shown directly
    // — every shape below verifies against this one bytecode.
    let mut guest = recursion_guest(&inner_program(), 1);
    eprintln!("guest compiled ONCE ({} instrs)", pretty_integer(guest.prog.len()));
    for &cfg in configs {
        let batch = build_batch(&[cfg]);
        let (recursive_proof, _) = batch.prove(&mut guest);
        recursive_proof
            .verify(&batch.program0)
            .expect("complete recursive proof verifies");
        eprintln!(
            "  verified: hashes={:>2}, iters=2^{}",
            pretty_integer(cfg.0),
            pretty_integer((cfg.1 as f64).log2() as u32)
        );
    }
    eprintln!(
        "all {} shapes verified by the SAME guest bytecode",
        pretty_integer(configs.len())
    );
}
