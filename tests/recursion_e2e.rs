//! End-to-end N→1 recursion: one guest program (`tests/verify_recursive.py`)
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
//! `check_reduced` is the outer verifier's entire native duty: one evaluation
//! of each fixed polynomial at its reduced point.

use std::collections::BTreeMap;

use leanvm_b::compiler::{compile, parse, parse_file_with_replacements};
use leanvm_b::cpu::{Program, prove, verify};
use leanvm_b::field::{F128, G};
use leanvm_b::leaf::{Block, Coord};
use leanvm_b::multilinear::mle_eval;
use leanvm_b::transcript::{Sponge, TraceOp, trace_start, trace_take};

/// A field element as the decimal `u128` literal the zkDSL parser accepts.
fn u(f: F128) -> u128 {
    (f.lo as u128) | ((f.hi as u128) << 64)
}

/// The 128 polynomial-basis coefficients of `v`, LSB first, as 0/1 field values.
fn bits_of(v: F128) -> Vec<F128> {
    let mut out = Vec::with_capacity(128);
    for w in [v.lo, v.hi] {
        for b in 0..64 {
            out.push(F128::new((w >> b) & 1, 0));
        }
    }
    out
}

/// The non-trivial inner program: a BLAKE3 hash chain seeded from the public
/// input, a `mul_range` product loop with heap traffic, and a final assert tying
/// them together — exercises every table (XOR/MUL/SET/DEREF/JUMP/BLAKE3).
fn inner_program(iters: usize) -> Program {
    let src = format!(
        "from snark_lib import *\n\
        N = 8\n\
        ITERS = {iters}\n\
        def main():\n\
        \x20   p = GEN ** 0\n\
        \x20   st = StackBuf(2)\n\
        \x20   st[0] = p[1]\n\
        \x20   st[1] = p[GEN]\n\
        \x20   for i in unroll(0, N):\n\
        \x20       nx = StackBuf(2)\n\
        \x20       blake3(st, st, nx)\n\
        \x20       st = nx\n\
        \x20   s1 = 1 * st[1]\n\
        \x20   buf = HeapBuf(ITERS)\n\
        \x20   acc = HeapBuf(ITERS + 1)\n\
        \x20   acc[GEN ** 0] = st[0]\n\
        \x20   for x in mul_range(1, GEN ** ITERS):\n\
        \x20       buf[x] = acc[x] * acc[x] + s1\n\
        \x20       acc[x * GEN] = buf[x] + x\n\
        \x20   out = acc[GEN ** ITERS]\n\
        \x20   nz = HeapBuf(1)\n\
        \x20   hint_witness(nz[0:1], \"outinv\")\n\
        \x20   prod = out * nz[GEN ** 0]\n\
        \x20   assert prod == 1\n\
        \x20   return\n"
    );
    compile(&parse(&src).expect("parse inner"))
}

/// Prove the inner program, returning (program, proof).
fn prove_inner(pi: [F128; 2], iters: usize) -> (Program, leanvm_b::cpu::Proof) {
    let mut program = inner_program(iters);
    // The final accumulator must be nonzero for the hinted-inverse assert; the
    // witness generator computes it, so run once natively to fetch the value.
    // (Cheap: the inverse hint is the only witness stream.)
    // First run without the hint to discover `out` would panic; instead compute
    // `out` by replaying the same arithmetic natively.
    let mut st = [pi[0], pi[1]];
    for _ in 0..8 {
        st = leanvm_b::vmhash::compress(st, st);
    }
    let mut acc = st[0];
    let mut x = F128::ONE;
    let g = leanvm_b::field::g_pow(1);
    for _ in 0..iters {
        let b = acc * acc + st[1];
        acc = b + x;
        x *= g;
    }
    let out = acc;
    assert!(out != F128::ZERO, "inner accumulator must be nonzero");
    program.set_witness("outinv", vec![vec![out.inv()]]);
    let (proof, stats) = prove(&program, pi);
    eprintln!(
        "[inner] cycles={} counts={:?} committed=2^{:.2}",
        stats.cycles,
        stats.counts,
        (stats.committed as f64).log2()
    );
    (program, proof)
}

/// The deferred-claim data the guest binds to the outer public input: the outer
/// verifier checks each claim natively (doc.tex §Deferred evaluation claims;
/// n_rec = 1 forwards fresh claims without batching).
struct SubDefer {
    pi: [F128; 2],
    kbc: usize,
    zeta_push: Vec<F128>,
    zeta_pull: Vec<F128>,
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
struct Reduced {
    outer_pi: [F128; 2],
    r_bc: Vec<F128>,
    v_bc: F128,
    r_m: Vec<F128>,
    v_a: F128,
    v_b: F128,
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
fn stacked_bytecode(program: &Program, proof: &leanvm_b::cpu::Proof, pi: [F128; 2]) -> Vec<F128> {
    let l = leanvm_b::cpu::layout(
        &program.prog,
        proof.stream[0].lo as usize,
        [1, 2, 3, 4, 5, 6].map(|i| proof.stream[i].lo as usize),
        pi,
    );
    leanvm_b::leaf::stacked_bytecode_table(&l.push)
}

/// The aggregation layer: mirror the guest's aggregation transcript, run the
/// two batching-sumcheck PROVERS (dense bytecode; two-phase sparse matrices),
/// and return the round-message hints, the terminal hints, the reduced claims,
/// and the outer public input.
#[allow(clippy::type_complexity)]
fn gen_agg(
    program: &Program,
    proof0: &leanvm_b::cpu::Proof,
    subs: &[SubDefer],
) -> (Vec<(String, Vec<F128>)>, Reduced) {
    let nsub = subs.len();
    let kbc = subs[0].kbc;
    let kbcv = kbc + 3;
    let klog = flock_prover::r1cs_hashes::blake3::K_LOG;

    // ---- the aggregation transcript (mirrors the guest exactly) ----
    let mut h = Sponge::empty();
    for d in subs {
        h.observe(d.pi[0]);
        h.observe(d.pi[1]);
        for &v in d.zeta_push.iter().chain(&d.zeta_pull) {
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

    // ---- bytecode batching sumcheck (dense, 2^kbcv) ----
    let gbc: Vec<F128> = (0..2 * nsub).map(|_| h.sample()).collect();
    let mut bt = stacked_bytecode(program, proof0, subs[0].pi);
    let mut wt = vec![F128::ZERO; 1 << kbcv];
    let points: Vec<Vec<F128>> = subs
        .iter()
        .flat_map(|d| {
            [
                d.zeta_push.iter().chain(&d.sb).copied().collect::<Vec<_>>(),
                d.zeta_pull.iter().chain(&d.sb).copied().collect::<Vec<_>>(),
            ]
        })
        .collect();
    for (t, p) in points.iter().enumerate() {
        let eqt = flare::zerocheck::univariate_skip::build_eq(p);
        for (w, &e) in wt.iter_mut().zip(eqt.iter()) {
            *w += gbc[t] * e;
        }
    }
    let mut brun: F128 = (0..2 * nsub).map(|t| gbc[t] * subs[t / 2].wbc[t % 2]).fold(F128::ZERO, |a, x| a + x);
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
    let (ma, mb) = flock_prover::r1cs_hashes::blake3::build_matrices();
    // per-claim dense weight tables: rows = quirky eq, cols = eq(top rounds) x z_partial.
    let mut us: Vec<Vec<F128>> = subs
        .iter()
        .map(|d| flare::lincheck::build_quirky_eq_table(d.zz, &d.zrho8, 6))
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
    let contract_cols = |m: &flare::r1cs::SparseBinaryMatrix, w: &[F128]| -> Vec<F128> {
        m.rows
            .iter()
            .map(|row| row.iter().map(|&j| w[j]).fold(F128::ZERO, |a, x| a + x))
            .collect()
    };
    let mut ms: Vec<Vec<F128>> = Vec::new();
    for w in &ws {
        ms.push(contract_cols(&ma, w));
        ms.push(contract_cols(&mb, w));
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
    let eq_rstar = flare::zerocheck::univariate_skip::build_eq(&r_row);
    let contract_rows = |m: &flare::r1cs::SparseBinaryMatrix| -> Vec<F128> {
        let mut out = vec![F128::ZERO; 1 << klog];
        for (i, row) in m.rows.iter().enumerate() {
            let e = eq_rstar[i];
            for &j in row {
                out[j] += e;
            }
        }
        out
    };
    let mut acol = contract_rows(&ma);
    let mut bcol = contract_rows(&mb);
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
        let eqr = flare::zerocheck::univariate_skip::build_eq(&r_row[..6]);
        let eqc = flare::zerocheck::univariate_skip::build_eq(&r_col[..6]);
        let (mut wam, mut wbm) = (F128::ZERO, F128::ZERO);
        for (t, d) in subs.iter().enumerate() {
            let lam = flare::zerocheck::multilinear::lagrange_weights_naive(6, d.zz);
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

    // ---- outer public input: sub statements + the reduced claims ----
    let mut e = Sponge::empty();
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
        ("bscr".to_string(), bscr),
        ("mscr".to_string(), mscr),
        ("bst".to_string(), vec![v_bc]),
        ("mst".to_string(), vec![v_a, v_b]),
    ];
    (
        hints,
        Reduced {
            outer_pi: e.state(),
            r_bc,
            v_bc,
            r_m,
            v_a,
            v_b,
        },
    )
}

/// The outermost native verifier's whole remaining duty: evaluate the three
/// fixed polynomials at the reduced points (one pass each).
fn check_reduced(program: &Program, proof0: &leanvm_b::cpu::Proof, pi0: [F128; 2], red: &Reduced) {
    let stacked = stacked_bytecode(program, proof0, pi0);
    assert_eq!(mle_eval(&stacked, &red.r_bc), red.v_bc, "reduced bytecode claim");
    let (ma, mb) = flock_prover::r1cs_hashes::blake3::build_matrices();
    let klog = flock_prover::r1cs_hashes::blake3::K_LOG;
    let eq_r = flare::zerocheck::univariate_skip::build_eq(&red.r_m[..klog]);
    let eq_c = flare::zerocheck::univariate_skip::build_eq(&red.r_m[klog..]);
    let direct = |m: &flare::r1cs::SparseBinaryMatrix| -> F128 {
        let mut acc = F128::ZERO;
        for (i, row) in m.rows.iter().enumerate() {
            let s = row.iter().map(|&j| eq_c[j]).fold(F128::ZERO, |a, x| a + x);
            acc += eq_r[i] * s;
        }
        acc
    };
    assert_eq!(direct(&ma), red.v_a, "reduced A claim");
    assert_eq!(direct(&mb), red.v_b, "reduced B claim");
}

/// Config + hints for the recursion guest (`tests/verify_recursive.py`), built
/// from the REAL `cpu::layout` of the inner program and the transcript trace of
/// a real `cpu::verify` run (zero hand-mirroring drift).
fn gen_verify(
    program: &Program,
    pi: [F128; 2],
    proof: &leanvm_b::cpu::Proof,
    summary: &leanvm_b::cpu::VerifySummary,
    ops: &[TraceOp],
) -> (BTreeMap<String, String>, Vec<(String, Vec<F128>)>, SubDefer) {
    let dig = program.digest();
    let l = leanvm_b::cpu::layout(
        &program.prog,
        proof.stream[0].lo as usize,
        [1, 2, 3, 4, 5, 6].map(|i| proof.stream[i].lo as usize),
        pi,
    );
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let lays: Vec<leanvm_b::leaf::Layout> = sides.iter().map(|b| leanvm_b::leaf::layout(b)).collect();
    let smu: Vec<usize> = lays.iter().map(|x| x.mu).collect();
    let mumax = *smu.iter().max().unwrap();

    // ---- flattened block/coord descriptors ----
    let (mut sblk, mut bkappa, mut bsel, mut bdelta, mut bc0, mut bcn) = (vec![0usize], vec![], vec![], vec![], vec![], vec![]);
    let (mut ct, mut cval, mut fpv) = (vec![], vec![], vec![]);
    let mut nclaims = 0usize;
    let mut nbcv = 0usize;
    for (s, blocks) in sides.iter().enumerate() {
        for (b, blk) in blocks.iter().enumerate() {
            bkappa.push(blk.kappa);
            bsel.push(lays[s].offsets[b] >> blk.kappa);
            bdelta.push((1usize << blk.kappa) - blk.real);
            bc0.push(ct.len());
            bcn.push(blk.coords.len());
            for c in &blk.coords {
                let (t, v, f) = match c {
                    Coord::Const(v) => (0u128, *v, *v),
                    Coord::Col(i) => {
                        nclaims += 1;
                        (1, F128::ZERO, l.pad[*i])
                    }
                    Coord::GCol(i) => {
                        nclaims += 1;
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
    let seed = Sponge::new(b"leanvm-b", &[pi[0], pi[1], dig[0], dig[1]]);
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
    let (gbits, gdig) = (pows[0].1, pows[0].2);

    // Bus: the bytecode claims carry the push/pull ζ_lo points and sb.
    let kbc = summary.bytecode_claims[0].point.len() - 3;
    let zeta_push: Vec<F128> = summary.bytecode_claims[0].point[..kbc].to_vec();
    let zeta_pull: Vec<F128> = summary.bytecode_claims[1].point[..kbc].to_vec();
    let sb: Vec<F128> = summary.bytecode_claims[0].point[kbc..].to_vec();

    let taus = l.taus;
    let ncol: Vec<usize> = leanvm_b::tables::tables().iter().map(|t| t.constraint_columns().len()).collect();

    // Flock replay data, all named struct fields.
    let n_log_b3 = l.taus[5];
    let m_r1cs = flock_prover::r1cs_hashes::blake3::K_LOG + n_log_b3;
    let n_mlv = m_r1cs - 6;
    let lcrounds = flock_prover::r1cs_hashes::blake3::K_LOG - 6;
    let zc1: Vec<F128> = summary.zerocheck.round1_ab.iter().chain(&summary.zerocheck.round1_c).copied().collect();
    let zcr: Vec<F128> = summary.zerocheck.multilinear_rounds.iter().flat_map(|&(a, b)| [a, b]).collect();
    let zcf = vec![summary.zerocheck.final_a_eval, summary.zerocheck.final_b_eval];
    let zc_z = summary.zc_claim.z;
    let zrho = summary.zc_claim.mlv_challenges.clone();
    let r_rest = &summary.zc_claim.r_rest;
    let lcr: Vec<F128> = summary.lincheck.rounds.iter().flat_map(|&(a, b)| [a, b]).collect();
    let lcz = summary.lincheck.z_partial.clone();
    let lc_alpha = summary.lc_claim.alpha;
    let lc_beta = summary.lc_claim.beta;
    let lrr = summary.lc_claim.r_rounds.clone();
    let shv: Vec<F128> = summary.ring_switches.iter().flat_map(|rs| rs.s_hat_v.iter().copied()).collect();

    // matpart = the deferred weighted matrix evaluation: the lincheck running
    // claim minus (= plus, char 2) the const-pin contribution.
    let r1cs = flock_prover::r1cs_hashes::blake3::build_block_r1cs(n_log_b3);
    let sd_bytes = r1cs.statement_digest();
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
        let bit = (pincol >> (flock_prover::r1cs_hashes::blake3::K_LOG - 1 - j)) & 1;
        pinw *= if bit == 1 { rv } else { F128::ONE + rv };
    }
    pinw *= lcz[pincol % 64];
    let matpart = lrun + pinw;

    let evtot_e: usize = ncol.iter().sum();
    let ncl = nclaims + evtot_e + 1 + 3;

    // ---- the stacked opening: config + the opening summary ----
    let stack_mu = l.m;
    let vcfg = flare::pcs::ligerito::LigeritoSecurityConfig::derive_profile(
        stack_mu + 7,
        flare::pcs::ligerito::LigeritoProfile::Secure,
    )
    .and_then(|s| s.to_prover_verifier_configs())
    .expect("stack ligerito config")
    .1;
    let log_n = stack_mu;
    let shapes = vcfg.level_shapes(log_n);
    let (nlev, r) = (shapes.levels, vcfg.level_steps);
    let (klvl, lmc, yr_log_n) = (shapes.ks, shapes.log_msg_cols, shapes.yr_log_n);
    let queries = vcfg.queries.clone();
    // query packing: each squeezed word carries 128/depth positions.
    let depth: Vec<usize> = shapes.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    let per: Vec<usize> = depth.iter().map(|&d| 128 / d).collect();
    let nsq: Vec<usize> = (0..nlev).map(|i| queries[i].div_ceil(per[i])).collect();
    let fgb = |lvl: usize| vcfg.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;

    let lig_raw = summary.opening.lig.query_squeezes.clone();
    let lig_sc: Vec<F128> = proof.openings[0]
        .sumcheck_transcript
        .iter()
        .flat_map(|m| [m.u_0, m.u_2])
        .collect();
    // Fold grinds: bits from the config, nonces from the proof, digests from
    // the trace (bits > 0 pows, in order).
    let mut fold_pow: Vec<(u32, u64, F128)> = Vec::new();
    let mut fold_grinds = pows[1..].iter().filter(|p| p.1 > 0);
    for lvl in 0..nlev {
        for j in 0..klvl[lvl] {
            let bits = (fgb(lvl) - j as i64).max(0) as u32;
            if bits > 0 {
                let &(nonce, b2, dig) = fold_grinds.next().expect("fold grind recorded");
                assert_eq!(b2, bits);
                fold_pow.push((bits, nonce, dig));
            } else {
                fold_pow.push((0, 0, F128::ZERO));
            }
        }
    }
    assert!(fold_grinds.next().is_none(), "every fold grind consumed");

    // ---- hints ----
    // bcv: the deferred bytecode evaluations (leaf's own scan, block/coord order).
    let (kbc2, bcv_push) = leanvm_b::leaf::public_evals(&l.push, &zeta_push);
    let (_, bcv_pull) = leanvm_b::leaf::public_evals(&l.pull, &zeta_pull);
    assert_eq!(kbc2, kbc);
    let bcv: Vec<F128> = bcv_push.iter().chain(&bcv_pull).copied().collect();
    assert_eq!(bcv.len(), nbcv);
    let sb3: [F128; 3] = sb.clone().try_into().unwrap();
    let wbc = vec![
        leanvm_b::leaf::stacked_bytecode_value(&bcv[..6], &sb3),
        leanvm_b::leaf::stacked_bytecode_value(&bcv[6..], &sb3),
    ];
    let cinv = summary.count_root.inv();
    // checkpoints: the verifier's phase-boundary sponge states (guest cvh).
    let cvh: Vec<F128> = summary.checkpoints.iter().map(|s| s[0]).collect();

    // ---- placeholder map ----
    let ints = |v: &[usize]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let us = |v: &[u128]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let mut rep = BTreeMap::new();
    let mut ps = |k: &str, v: String| {
        rep.insert(format!("{k}_PLACEHOLDER"), v);
    };
    ps("STREAM_LEN", proof.stream.len().to_string());
    let ann: Vec<u128> = (0..7).map(|i| u(proof.stream[i])).collect();
    ps("ANN", us(&ann));
    ps("GFULL", (gbits / 8).to_string());
    ps("GEXTRA", (gbits % 8).to_string());
    ps("GG", u(G).to_string());
    ps("ILD0", u(G.inv()).to_string());
    ps("ILD1", u((F128::ONE + G).inv()).to_string());
    ps("ILD2", u((G * (F128::ONE + G)).inv()).to_string());
    ps("SMU", ints(&smu));
    ps("ZOFF", ints(&[0, mumax, 2 * mumax]));
    ps("MUMAX", mumax.to_string());
    ps("SBLK", ints(&sblk));
    ps("BKAPPA", ints(&bkappa));
    ps("BSEL", ints(&bsel));
    ps("BDELTA", ints(&bdelta));
    ps("BC0", ints(&bc0));
    ps("BCN", ints(&bcn));
    ps("CT", us(&ct));
    ps("CVAL", us(&cval));
    ps("FPV", us(&fpv));
    let idxc: Vec<u128> = (0..mumax)
        .map(|i| {
            let mut g2k = G;
            for _ in 0..i {
                g2k = g2k * g2k;
            }
            u(F128::ONE + g2k)
        })
        .collect();
    ps("IDXC", us(&idxc));
    let evtot: usize = ncol.iter().sum();
    // claim pool size: bus coords + constraint evals + the PI claim + 3 pins.
    ps("NCLAIMS", (nclaims + evtot + 1 + 3).to_string());
    ps("NBCV", nbcv.to_string());
    ps("TAU", ints(&taus));
    ps("NCOL", ints(&ncol));
    ps("TAUMAX", taus.iter().max().unwrap().to_string());
    // The pin point: the first BLAKE3 value-column bus claim. Scan blocks/coords
    // exactly as the claims are ordered to find its side + kappa.
    let sch = leanvm_b::cpu::schema();
    let b3base = sch.base[5];
    let valcols: Vec<usize> = leanvm_b::tables::BLAKE3_VALUE_COLS.iter().map(|&c| b3base + c).collect();
    let mut pin_side_kappa: Option<(usize, usize)> = None;
    'outer: for (s, blocks) in sides.iter().enumerate() {
        for blk in blocks.iter() {
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i) = c
                    && valcols.contains(i)
                {
                    pin_side_kappa = Some((s, blk.kappa));
                    break 'outer;
                }
            }
        }
    }
    let (pin_side, pin_kappa) = pin_side_kappa.expect("BLAKE3 value-column claim exists");
    let n_b3 = proof.stream[6].lo as usize; // announced BLAKE3 row count
    ps("NB3", n_b3.to_string());
    ps("NLOGB3", pin_kappa.to_string());
    ps("PINZOFF", (pin_side * mumax).to_string());
    let pinv: Vec<u128> = leanvm_b::blake3_flock::pin_constants().iter().map(|&v| u(v)).collect();
    ps("PINV", us(&pinv));
    // ---- Phase D placeholders ----
    let word16 = |b: &[u8], o: usize| {
        let mut buf = [0u8; 16];
        let e = (b.len() - o).min(16);
        buf[..e].copy_from_slice(&b[o..o + e]);
        F128::new(
            u64::from_le_bytes(buf[..8].try_into().unwrap()),
            u64::from_le_bytes(buf[8..].try_into().unwrap()),
        )
    };
    ps("R1CSLBL", u(word16(b"flock-r1cs-v0", 0)).to_string());
    ps("SD0", u(word16(&sd_bytes, 0)).to_string());
    ps("SD1", u(word16(&sd_bytes, 16)).to_string());
    ps("ZCLBLA", u(word16(b"flock-zerocheck-v0", 0)).to_string());
    ps("ZCLBLB", u(word16(b"flock-zerocheck-v0", 16)).to_string());
    ps("LCLBLA", u(word16(b"flock-lincheck-v0", 0)).to_string());
    ps("LCLBLB", u(word16(b"flock-lincheck-v0", 16)).to_string());
    let flds = |v: &[F128]| format!("[{}]", v.iter().map(|&x| u(x).to_string()).collect::<Vec<_>>().join(", "));
    let inner7: Vec<F128> = flare::zerocheck::univariate_skip_optimized::small_challenges_ghash()
        .into_iter()
        .chain(flare::zerocheck::univariate_skip_optimized::medium_challenges_ghash())
        .collect();
    ps("INNER7", flds(&inner7));
    let i7inv: Vec<F128> = inner7.iter().map(|&c| (F128::ONE + c).inv()).collect();
    ps("I7INV", flds(&i7inv));
    let phi: Vec<F128> = flare::field::phi8::PHI_8_TABLE[..128].to_vec();
    ps("PHI", flds(&phi));
    let inv_den = |nodes: &[F128], node: F128, skip: F128| {
        let mut d = F128::ONE;
        for &s in nodes {
            if s != skip {
                d *= node + s;
            }
        }
        d.inv()
    };
    let ilam: Vec<F128> = (0..64).map(|i| inv_den(&phi[64..128], phi[64 + i], phi[64 + i])).collect();
    let icmb: Vec<F128> = (0..64).map(|i| inv_den(&phi[..128], phi[64 + i], phi[64 + i])).collect();
    let isdom: Vec<F128> = (0..64).map(|i| inv_den(&phi[..64], phi[i], phi[i])).collect();
    ps("ILAM", flds(&ilam));
    ps("ICMB", flds(&icmb));
    ps("ISDOM", flds(&isdom));
    ps("MR1CS", m_r1cs.to_string());
    ps("NMLV", n_mlv.to_string());
    ps("LCR", lcrounds.to_string());
    ps("PINCOL", pincol.to_string());
    ps("KLOG", flock_prover::r1cs_hashes::blake3::K_LOG.to_string());
    ps("OBLBLA", u(word16(b"flock-pcs-open-batch-v0", 0)).to_string());
    ps("OBLBLB", u(word16(b"flock-pcs-open-batch-v0", 16)).to_string());
    ps("RSLBLA", u(word16(b"flock-ring-switch-v0", 0)).to_string());
    ps("RSLBLB", u(word16(b"flock-ring-switch-v0", 16)).to_string());
    ps("PDLBLA", u(word16(b"flock-pcs-packed-direct-v0", 0)).to_string());
    ps("PDLBLB", u(word16(b"flock-pcs-packed-direct-v0", 16)).to_string());
    ps("NCL", ncl.to_string());

    // ---- Phase E2 placeholders + hints (the stacked Ligerito) ----
    let lig = &proof.openings[0];
    let numinter: Vec<usize> = klvl.iter().map(|&k| 1usize << k).collect();
    let lenris: usize = klvl.iter().sum();
    let prefix_sum2 = |f: &dyn Fn(usize) -> usize| -> Vec<usize> {
        let mut o = Vec::with_capacity(nlev);
        let mut acc = 0;
        for lv in 0..nlev {
            o.push(acc);
            acc += f(lv);
        }
        o
    };
    let rowoff = prefix_sum2(&|lv| queries[lv] * numinter[lv]);
    let pathoff = prefix_sum2(&|lv| queries[lv] * depth[lv] * 2);
    let sbitsoff = prefix_sum2(&|lv| nsq[lv] * 128);
    let qpoff = prefix_sum2(&|lv| nsq[lv] * per[lv]);
    let qp_len: usize = (0..nlev).map(|lv| nsq[lv] * per[lv]).sum();
    let svkoff = prefix_sum2(&|lv| lmc[lv] + 1);
    let foldbase = prefix_sum2(&|lv| klvl[lv]);
    let risstart: Vec<usize> = (0..nlev).map(|k| foldbase[k] + klvl[k]).collect();
    let total_folds: usize = klvl.iter().sum();
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
    let (mut lrows_flat, mut lpaths_flat, mut lsbits_flat) = (Vec::new(), Vec::new(), Vec::new());
    for lv in 0..nlev {
        let (rows_exp, path_exp) =
            flare::pcs::ligerito::expand_level_opening(shapes.block_len[lv], &positions[lv], rows_of(lv), numinter[lv], path_of(lv))
                .expect("expand stacked level opening");
        for row in &rows_exp {
            lrows_flat.extend_from_slice(row);
        }
        for &h in &path_exp {
            lpaths_flat.extend_from_slice(&hb32(h));
        }
        assert_eq!(lig_raw[lv].len(), nsq[lv]);
        for &v in &lig_raw[lv] {
            lsbits_flat.extend_from_slice(&bits_of(v));
        }
    }
    let mut lfpb_flat = vec![F128::ZERO; total_folds * 128];
    for (g, &(bits, _n, dig)) in fold_pow.iter().enumerate() {
        if bits > 0 {
            lfpb_flat[g * 128..g * 128 + 128].copy_from_slice(&bits_of(dig));
        }
    }
    let qpkdv = l.placements[leanvm_b::cpu::QPKD].n_vars;

    // claim descriptors, in exact clv order.
    let (mut cpbuf, mut cpoff, mut cplen, mut cslot, mut csel, mut yt) = (vec![], vec![], vec![], vec![], vec![], vec![]);
    let (mut nover_v, mut seln_v): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
    let qpkd_pl = l.placements[leanvm_b::cpu::QPKD];
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
    for (s, blocks) in sides.iter().enumerate() {
        for blk in blocks.iter() {
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i) = c {
                    if valcols.contains(i) {
                        let slot_i = leanvm_b::blake3_flock::SLOTS[valcols.iter().position(|v| v == i).unwrap()];
                        let nvt = 7 + blk.kappa;
                        push_desc(3, s * mumax, blk.kappa, slot_i, qpkd_pl.offset >> nvt, nvt);
                    } else {
                        let pl = l.placements[*i];
                        push_desc(0, s * mumax, blk.kappa, 0, pl.offset >> blk.kappa, blk.kappa);
                    }
                }
            }
        }
    }
    for (t, table) in leanvm_b::tables::tables().iter().enumerate() {
        for &c in table.constraint_columns() {
            let col = sch.base[t] + c;
            let pl = l.placements[col];
            if pl.is_virtual() {
                let slot_i = leanvm_b::blake3_flock::SLOTS
                    [valcols.iter().position(|v| *v == col).unwrap()];
                let nvt = 7 + taus[t];
                push_desc(3, 0, taus[t], slot_i, qpkd_pl.offset >> nvt, nvt);
            } else {
                push_desc(1, t * taus.iter().max().unwrap(), taus[t], 0, pl.offset >> taus[t], taus[t]);
            }
        }
    }
    {
        // PI claim on MEM: point = [r_m, 0, 0, ...]. Coords beyond lenris are
        // const zero, so they fold into the y pattern (required-zero bits)
        // instead of runtime overlap factors: cap the low span at lenris and
        // shift the selector pattern left by the folded coord count.
        let pl = l.placements[leanvm_b::cpu::MEM];
        let folded = pl.n_vars.saturating_sub(lenris);
        let low = pl.n_vars - folded;
        push_desc(2, 0, low, 0, (pl.offset >> pl.n_vars) << folded, low);
    }
    for &pslot in leanvm_b::blake3_flock::PIN_SLOTS.iter() {
        let nvt = 7 + pin_kappa;
        push_desc(3, pin_side * mumax, pin_kappa, pslot, qpkd_pl.offset >> nvt, nvt);
    }
    assert_eq!(cpbuf.len(), ncl, "descriptor count == pool size");
    let rssel_full = qpkd_pl.offset >> qpkdv;
    let yrs = rssel_full >> (lenris - qpkdv);
    let rssel = rssel_full & ((1usize << (lenris - qpkdv)) - 1);

    ps("LIGLBLA", u(word16(b"flock-ligerito-basis-v0", 0)).to_string());
    ps("LIGLBLB", u(word16(b"flock-ligerito-basis-v0", 16)).to_string());
    ps("NLEVELS", nlev.to_string());
    ps("R", r.to_string());
    ps("YR_LOG_N", yr_log_n.to_string());
    ps("YR_LEN", (1usize << yr_log_n).to_string());
    ps("LENRIS", lenris.to_string());
    ps("MAXNI", numinter.iter().max().unwrap().to_string());
    ps("MAXQ", queries.iter().max().unwrap().to_string());
    ps("MAXNSQ", nsq.iter().max().unwrap().to_string());
    ps("MAXLMC", lmc.iter().max().unwrap().to_string());
    ps("QP_LEN", qp_len.to_string());
    ps("LSC_LEN", lig_sc.len().to_string());
    ps("LROWS_LEN", lrows_flat.len().to_string());
    ps("LPATHS_LEN", lpaths_flat.len().to_string());
    ps("LSBITS_LEN", lsbits_flat.len().to_string());
    ps("LFPB_LEN", lfpb_flat.len().to_string());
    ps("QUERIES", ints(&queries));
    ps("KLVL", ints(&klvl));
    ps("NUMINTER", ints(&numinter));
    ps("NBYTES", ints(&numinter.iter().map(|&n| n * 16).collect::<Vec<_>>()));
    ps("BLOCKS", ints(&numinter.iter().map(|&n| n / 2).collect::<Vec<_>>()));
    ps("DEPTH", ints(&depth));
    ps("PER", ints(&per));
    ps("NSQ", ints(&nsq));
    ps("QPOFF", ints(&qpoff));
    ps("ALPHALEN", ints(&queries.iter().map(|&q| flare::pcs::ligerito::ceil_log2(q)).collect::<Vec<_>>()));
    ps("LMC", ints(&lmc));
    ps("RISSTART", ints(&risstart));
    ps("PREFIXLEN", ints(&lmc.iter().map(|&m2| m2 - yr_log_n).collect::<Vec<_>>()));
    let mut roota = vec![F128::ZERO];
    let mut rootb = vec![F128::ZERO];
    for lv in 1..nlev {
        let rw = hb32(if lv - 1 < lig.level_roots.len() {
            lig.level_roots[lv - 1]
        } else {
            panic!("missing level root")
        });
        roota.push(rw[0]);
        rootb.push(rw[1]);
    }
    ps("FOLDBASE", ints(&foldbase));
    ps("ROWOFF", ints(&rowoff));
    ps("PATHOFF", ints(&pathoff));
    ps("SBITSOFF", ints(&sbitsoff));
    ps("SVKOFF", ints(&svkoff));
    ps("BITS", ints(&fold_pow.iter().map(|&(b, _, _)| b as usize).collect::<Vec<_>>()));
    ps("FULL", ints(&fold_pow.iter().map(|&(b, _, _)| (b / 8) as usize).collect::<Vec<_>>()));
    ps("EXTRA8", ints(&fold_pow.iter().map(|&(b, _, _)| (b % 8) as usize).collect::<Vec<_>>()));
    let fnv: Vec<F128> = fold_pow.iter().map(|&(_, n, _)| F128::new(n, 0)).collect();
    let mut svk_flat = Vec::new();
    let mut ivk_flat = Vec::new();
    for lv in 0..nlev {
        let s2 = flare::pcs::ligerito::eval_sk_at_vks(lmc[lv]);
        for &v in &s2 {
            svk_flat.push(v);
            ivk_flat.push(if v == F128::ZERO { F128::ZERO } else { v.inv() });
        }
    }
    ps("SVK", flds(&svk_flat));
    ps("IVK", flds(&ivk_flat));
    ps("CPBUF", ints(&cpbuf));
    ps("CPOFF", ints(&cpoff));
    ps("CPLEN", ints(&cplen));
    ps("CSLOT", ints(&cslot));
    ps("CSEL", ints(&csel));
    ps("NOVER", ints(&nover_v));
    ps("SELN", ints(&seln_v));
    ps("YTHI", ints(&yt));
    ps("QPKDV", qpkdv.to_string());
    ps("RSSEL", rssel.to_string());
    ps("YRS", yrs.to_string());
    ps("KBC", kbc.to_string());
    ps("KBCV", (kbc + 3).to_string());
    let label_state = Sponge::new(b"leanvm-b", &[]).state();
    ps("SEEDB0", u(label_state[0]).to_string());
    ps("SEEDB1", u(label_state[1]).to_string());
    ps("DIG0", u(dig[0]).to_string());
    ps("DIG1", u(dig[1]).to_string());
    ps("DELTA", flds(&flare::pcs::ring_switch::trace_dual_basis()[..]));

    let deferred = SubDefer {
        pi,
        kbc,
        zeta_push,
        zeta_pull,
        sb: sb.clone(),
        wbc: wbc.clone(),
        lc_alpha,
        zz: zc_z,
        zrho8: zrho[..lcrounds].to_vec(),
        lrr: lrr.clone(),
        lcz: lcz.clone(),
        matpart,
    };

    let mut zinv = vec![F128::ONE; n_mlv];
    for (i, item) in zinv.iter_mut().enumerate().take(n_mlv).skip(7) {
        *item = (F128::ONE + r_rest[i]).inv();
    }
    let hints = vec![
        ("stream".to_string(), proof.stream.clone()),
        ("grind_bits".to_string(), bits_of(gdig)),
        ("bcv".to_string(), bcv),
        ("count_root_inv".to_string(), vec![cinv]),
        ("zc_round1".to_string(), zc1),
        ("zc_msgs".to_string(), zcr),
        ("zc_finals".to_string(), zcf.clone()),
        ("zc_invs".to_string(), zinv),
        ("lincheck_msgs".to_string(), lcr.clone()),
        ("z_partial".to_string(), lcz.clone()),
        ("matpart".to_string(), vec![matpart]),
        ("s_hat_v".to_string(), shv.clone()),
        ("lsc".to_string(), lig_sc.clone()),
        ("lrows".to_string(), lrows_flat),
        ("lpaths".to_string(), lpaths_flat),
        ("lsbits".to_string(), lsbits_flat),
        ("fold_grind_bits".to_string(), lfpb_flat),
        ("yr".to_string(), lig.final_proof.yr.clone()),
        ("spi".to_string(), vec![pi[0], pi[1]]),
        ("rta".to_string(), roota),
        ("rtb".to_string(), rootb),
        ("fnn".to_string(), fnv),
        ("cvh".to_string(), cvh),
    ];
    (rep, hints, deferred)
}

/// End-to-end N→1 recursion: prove `nsub` inner proofs (same program,
/// distinct statements), verify all of them inside ONE guest, batch the
/// deferred claims with the two aggregation sumchecks, prove the guest, and
/// natively discharge the three reduced claims.
fn run_recursion(nsub: usize, inner_iters: usize) {
    let mut protos = Vec::new();
    for k in 0..nsub {
        let pi = [
            F128::new(0x1111_2222 + k as u64, 0x3333_4444),
            F128::new(0x5555_6666, 0x7777_8888 + k as u64),
        ];
        let (program, proof) = prove_inner(pi, inner_iters);
        trace_start();
        let summary = verify(&program, &pi, &proof).expect("inner verifies");
        let ops = trace_take();
        protos.push((program, pi, proof, summary, ops));
    }
    let mut rep0 = None;
    let mut merged: Vec<(String, Vec<F128>)> = Vec::new();
    let mut subs = Vec::new();
    for (program, pi, proof, summary, ops) in &protos {
        let (rep, hints, defer) = gen_verify(program, *pi, proof, summary, ops);
        match &rep0 {
            None => rep0 = Some(rep),
            Some(r0) => assert_eq!(r0, &rep, "sub-proof shapes must agree"),
        }
        if merged.is_empty() {
            merged = hints;
        } else {
            for ((name, acc), (n2, more)) in merged.iter_mut().zip(hints) {
                assert_eq!(*name, n2);
                acc.extend(more);
            }
        }
        subs.push(defer);
    }
    let mut rep = rep0.unwrap();
    rep.insert("NSUB_PLACEHOLDER".to_string(), nsub.to_string());
    let (program0, pi0, proof0, _, _) = &protos[0];
    let (agg_hints, reduced) = gen_agg(program0, proof0, &subs);
    merged.extend(agg_hints);

    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/verify_recursive.py");
    let mut guest = compile(&parse_file_with_replacements(path, &rep).expect("parse verify_recursive.py"));
    for (name, vals) in &merged {
        guest.set_witness(name, vec![vals.clone()]);
    }
    let gpi = reduced.outer_pi;
    let t = std::time::Instant::now();
    let (gproof, stats) = prove(&guest, gpi);
    let t_prove = t.elapsed();
    let t = std::time::Instant::now();
    verify(&guest, &gpi, &gproof).expect("outer proof verifies");
    let t_verify = t.elapsed();
    let t = std::time::Instant::now();
    check_reduced(program0, proof0, *pi0, &reduced);
    let t_red = t.elapsed();
    let psize = bincode::serialize(&gproof).expect("serialize outer proof").len();
    eprintln!(
        "recursion_{nsub}to1 OK: guest {} cycles, {} BLAKE3; outer prove {:.2}s, verify {:.1}ms, reduced checks {:.1}ms, outer proof ~{} KiB",
        stats.cycles,
        stats.counts[5],
        t_prove.as_secs_f64(),
        t_verify.as_secs_f64() * 1e3,
        t_red.as_secs_f64() * 1e3,
        psize / 1024,
    );
}

#[test]
fn recursion_1to1() {
    run_recursion(1, 16);
}

#[test]
fn recursion_2to1() {
    run_recursion(2, 16);
}

/// 2→1 with a ~1M-cycle inner program (log_mem 21, an m=33 stacked opening):
/// the guest cost is structure-dominated, so it grows only with the log of
/// the inner execution length; at this size each in-circuit verification
/// costs fewer cycles than the execution it verifies. Heavy; run explicitly.
#[test]
#[ignore]
fn recursion_2to1_big() {
    run_recursion(2, 1 << 15);
}

