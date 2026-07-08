//! End-to-end 1→1 recursion: a guest program replays `cpu::verify` of a
//! non-trivial inner proof in-circuit, with the bytecode and flock-matrix
//! evaluations deferred to the public input (doc.tex §Deferred evaluation
//! claims). Built bottom-up: the transcript trace of a REAL `cpu::verify` run is
//! the guest's mechanical spec (`transcript::trace_start`/`trace_take`), and the
//! real `cpu::layout` supplies every compile-time shape.

use std::collections::BTreeMap;

use leanvm_b::compiler::{compile, parse, parse_file_with_replacements};
use leanvm_b::cpu::{Program, prove, verify};
use leanvm_b::field::{F128, G};
use leanvm_b::leaf::{Block, Coord};
use leanvm_b::multilinear::mle_eval;
use leanvm_b::transcript::{TraceOp, trace_start, trace_take};
use leanvm_b::vmhash::compress;

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

/// Minimal mirror of `transcript::Sponge` (same compress chain), for computing
/// the guest's baked seed and replaying trace prefixes to checkpoint values.
#[derive(Clone)]
struct Mirror {
    cv: [F128; 2],
}
impl Mirror {
    fn new(label: &[u8], statement: &[F128]) -> Self {
        let mut s = Self { cv: [F128::ZERO; 2] };
        s.absorb_bytes(b"leanvm-b/transcript/v1");
        s.absorb_bytes(label);
        for &x in statement {
            s.observe(x);
        }
        s
    }
    fn observe(&mut self, x: F128) {
        self.cv = compress(self.cv, [x, F128::new(1, 0)]);
    }
    fn absorb_bytes(&mut self, bytes: &[u8]) {
        self.cv = compress(self.cv, [F128::new(bytes.len() as u64, 0), F128::new(3, 0)]);
        for chunk in bytes.chunks(16) {
            let mut buf = [0u8; 16];
            buf[..chunk.len()].copy_from_slice(chunk);
            let w = F128::new(
                u64::from_le_bytes(buf[..8].try_into().unwrap()),
                u64::from_le_bytes(buf[8..].try_into().unwrap()),
            );
            self.cv = compress(self.cv, [w, F128::new(2, 0)]);
        }
    }
    fn sample(&mut self) -> F128 {
        let out = compress(self.cv, [F128::ZERO, F128::new(4, 0)]);
        self.cv = out;
        out[0]
    }
    fn absorb_nonce(&mut self, nonce: u64) {
        self.cv = compress(self.cv, [F128::new(nonce, 0), F128::new(5, 0)]);
    }
    /// Replay recorded trace ops (asserting every sample matches), so any prefix
    /// yields the exact sponge state the guest must reach there.
    fn replay(&mut self, ops: &[TraceOp]) {
        for op in ops {
            match op {
                TraceOp::StreamObserve(x) | TraceOp::Observe(x) => self.observe(*x),
                TraceOp::AbsorbBytes(b) => self.absorb_bytes(b),
                TraceOp::Sample(v) => assert_eq!(self.sample(), *v, "trace replay diverged"),
                TraceOp::Pow { nonce, .. } => self.absorb_nonce(*nonce),
                TraceOp::StreamRaw(_) | TraceOp::Opening => {}
            }
        }
    }
}

/// Structural cursor over the trace, for extracting challenge values.
struct Walk<'a> {
    ops: &'a [TraceOp],
    i: usize,
}
impl Walk<'_> {
    fn so(&mut self) -> F128 {
        let op = &self.ops[self.i];
        self.i += 1;
        match op {
            TraceOp::StreamObserve(x) => *x,
            other => panic!("expected StreamObserve at {}, got {other:?}", self.i - 1),
        }
    }
    fn sample(&mut self) -> F128 {
        let op = &self.ops[self.i];
        self.i += 1;
        match op {
            TraceOp::Sample(v) => *v,
            other => panic!("expected Sample at {}, got {other:?}", self.i - 1),
        }
    }
    fn raw(&mut self) -> F128 {
        let op = &self.ops[self.i];
        self.i += 1;
        match op {
            TraceOp::StreamRaw(x) => *x,
            other => panic!("expected StreamRaw at {}, got {other:?}", self.i - 1),
        }
    }
    fn pow(&mut self) -> (u64, u32) {
        let op = &self.ops[self.i];
        self.i += 1;
        match op {
            TraceOp::Pow { nonce, bits } => (*nonce, *bits),
            other => panic!("expected Pow at {}, got {other:?}", self.i - 1),
        }
    }
}

/// The non-trivial inner program: a BLAKE3 hash chain seeded from the public
/// input, a `mul_range` product loop with heap traffic, and a final assert tying
/// them together — exercises every table (XOR/MUL/SET/DEREF/JUMP/BLAKE3).
fn inner_program() -> Program {
    let src = "from snark_lib import *\n\
        N = 8\n\
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
        \x20   buf = HeapBuf(16)\n\
        \x20   acc = HeapBuf(17)\n\
        \x20   acc[GEN ** 0] = st[0]\n\
        \x20   for x in mul_range(1, GEN ** 16):\n\
        \x20       buf[x] = acc[x] * acc[x] + s1\n\
        \x20       acc[x * GEN] = buf[x] + x\n\
        \x20   out = acc[GEN ** 16]\n\
        \x20   nz = HeapBuf(1)\n\
        \x20   hint_witness(nz[0:1], \"outinv\")\n\
        \x20   prod = out * nz[GEN ** 0]\n\
        \x20   assert prod == 1\n\
        \x20   return\n";
    compile(&parse(src).expect("parse inner"))
}

/// Public input of the inner proof.
fn inner_pi() -> [F128; 2] {
    [F128::new(0x1111_2222, 0x3333_4444), F128::new(0x5555_6666, 0x7777_8888)]
}

/// Prove the inner program, returning (program, proof).
fn prove_inner() -> (Program, leanvm_b::cpu::Proof) {
    let mut program = inner_program();
    // The final accumulator must be nonzero for the hinted-inverse assert; the
    // witness generator computes it, so run once natively to fetch the value.
    // (Cheap: the inverse hint is the only witness stream.)
    let pi = inner_pi();
    // First run without the hint to discover `out` would panic; instead compute
    // `out` by replaying the same arithmetic natively.
    let mut st = [pi[0], pi[1]];
    for _ in 0..8 {
        st = leanvm_b::vmhash::compress(st, st);
    }
    let mut acc = st[0];
    let mut x = F128::ONE;
    let g = leanvm_b::field::g_pow(1);
    for _ in 0..16 {
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
struct Deferred {
    outer_pi: [F128; 2],
    kbc: usize,
    zetas01: [Vec<F128>; 2],
    sb: Vec<F128>,
    wbc: Vec<F128>,
    lc_alpha: F128,
    zz: F128,
    zrho: Vec<F128>,
    lrr: Vec<F128>,
    lcz: Vec<F128>,
    matpart: F128,
    shv: Vec<F128>,
    rdp: Vec<F128>,
    tclaim: Vec<F128>,
    rsq: Vec<F128>,
    lig_ris_lo: Vec<F128>,
    zc_r_tail: Vec<F128>,
    n_log_b3: usize,
}

/// The OUTER verifier's native discharge of the deferred claims: bytecode MLE
/// evaluations, the lincheck matrix evaluation, the ring-switch tensor
/// transposes, and the eval_rs_eq weights. Cheap native work (one nnz pass +
/// O(small) field ops); only this plus `cpu::verify(outer)` and the export-hash
/// recomputation constitute outer verification.
fn check_deferred(program: &Program, pi: [F128; 2], proof: &leanvm_b::cpu::Proof, d: &Deferred) {
    // (a) the two reduced bytecode claims: the six encoding columns stacked
    // along three selector bits form ONE multilinear polynomial B in
    // kbc + 3 variables; check B(zeta_lo, sb) per side.
    let l = leanvm_b::cpu::layout(
        &program.prog,
        proof.stream[0].lo as usize,
        [1, 2, 3, 4, 5, 6].map(|i| proof.stream[i].lo as usize),
        pi,
    );
    let mut stacked = vec![F128::ZERO; 8 << d.kbc];
    let mut c_idx = 0;
    for blk in l.push.iter() {
        for c in &blk.coords {
            if let Coord::Public(vals) = c {
                assert_eq!(blk.kappa, d.kbc);
                assert_eq!(vals.len(), 1 << d.kbc);
                stacked[(c_idx << d.kbc)..((c_idx + 1) << d.kbc)].copy_from_slice(vals);
                c_idx += 1;
            }
        }
    }
    assert_eq!(c_idx, 6);
    for s in 0..2 {
        let mut pt = d.zetas01[s][..d.kbc].to_vec();
        pt.extend_from_slice(&d.sb);
        assert_eq!(mle_eval(&stacked, &pt), d.wbc[s], "reduced bytecode claim {s}");
    }
    // (b) the deferred matrix evaluation (one sparse nnz pass).
    let r1cs = flock_prover::r1cs_hashes::blake3::build_block_r1cs(d.n_log_b3);
    let eqi = flare::lincheck::build_quirky_eq_table(d.zz, &d.zrho[..d.lrr.len()], 6);
    use flare::lincheck::LincheckCircuit as _;
    let mut comb = r1cs.csc_lincheck_circuit().fold_alpha_batched(d.lc_alpha, &eqi);
    for &rv in &d.lrr {
        flare::lincheck::sumcheck_bind_top_in_place_par(&mut comb, rv);
    }
    assert_eq!(
        flare::pcs::ring_switch::inner_product(&comb, &d.lcz),
        d.matpart,
        "deferred matrix claim"
    );
    // (c) the two transposed ring-switch sumcheck claims.
    for rs in 0..2 {
        let shu = flare::pcs::ring_switch::tensor_algebra_transpose(&d.shv[128 * rs..128 * rs + 128]);
        let eqd = flare::zerocheck::univariate_skip::build_eq(&d.rdp[7 * rs..7 * rs + 7]);
        assert_eq!(
            flare::pcs::ring_switch::inner_product(&shu, &eqd),
            d.tclaim[rs],
            "deferred tensor claim {rs}"
        );
    }
    // (d) the two eval_rs_eq weights.
    let inner7: Vec<F128> = flare::zerocheck::univariate_skip_optimized::small_challenges_ghash()
        .into_iter()
        .chain(flare::zerocheck::univariate_skip_optimized::medium_challenges_ghash())
        .collect();
    let lcr = d.lrr.len();
    let x_outer_ab: Vec<F128> = d.lrr.iter().rev().copied().chain(d.zrho[lcr..].iter().copied()).collect();
    let x_outer_c: Vec<F128> = inner7.into_iter().chain(d.zc_r_tail.iter().copied()).collect();
    for (rs, xo) in [x_outer_ab, x_outer_c].iter().enumerate() {
        let eqd = flare::zerocheck::univariate_skip::build_eq(&d.rdp[7 * rs..7 * rs + 7]);
        assert_eq!(
            flare::pcs::ring_switch::eval_rs_eq(&xo[1..], &d.lig_ris_lo, &eqd),
            d.rsq[rs],
            "deferred eval_rs_eq {rs}"
        );
    }
}

/// Config + hints for the recursion guest (`tests/verify_recursive.py`), built
/// from the REAL `cpu::layout` of the inner program and the transcript trace of
/// a real `cpu::verify` run (zero hand-mirroring drift).
fn gen_verify(
    program: &Program,
    pi: [F128; 2],
    proof: &leanvm_b::cpu::Proof,
    ops: &[TraceOp],
) -> (BTreeMap<String, String>, Vec<(String, Vec<F128>)>, Deferred) {
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

    // ---- structural walk: challenges + checkpoint ----
    let seed = Mirror::new(b"leanvm-b", &[pi[0], pi[1], dig[0], dig[1]]);
    let mut w = Walk { ops, i: 0 };
    let absorb = |w: &mut Walk| -> Vec<u8> {
        let op = &w.ops[w.i];
        w.i += 1;
        match op {
            TraceOp::AbsorbBytes(b) => b.clone(),
            other => panic!("expected AbsorbBytes, got {other:?}"),
        }
    };
    let observe = |w: &mut Walk| -> F128 {
        let op = &w.ops[w.i];
        w.i += 1;
        match op {
            TraceOp::Observe(x) => *x,
            other => panic!("expected Observe, got {other:?}"),
        }
    };
    for _ in 0..9 {
        w.so(); // 7 announced + 2 root words
    }
    let _alpha = w.sample();
    let _nonce_word = w.raw();
    let (nonce, gbits) = w.pow();
    let _gamma = w.sample();
    let mut zetas: Vec<Vec<F128>> = Vec::new();
    let mut roots: Vec<F128> = Vec::new();
    for &mu in &smu {
        roots.push(w.so());
        let mut r: Vec<F128> = Vec::new();
        for li in 0..mu {
            let mut rho = Vec::new();
            for _ in 0..li {
                for _ in 0..3 {
                    w.so();
                }
                rho.push(w.sample());
            }
            w.so();
            w.so();
            let c = w.sample();
            r = std::iter::once(c).chain(rho).collect();
        }
        zetas.push(r);
    }
    // decompose reads (claim values), in order — advances the walk to phase end.
    for _ in 0..nclaims {
        w.so();
    }
    // stacked-bytecode reduction (native protocol): 12 observes + 3 samples.
    let bcv_trace: Vec<F128> = (0..nbcv).map(|_| observe(&mut w)).collect();
    let sb: Vec<F128> = (0..3).map(|_| w.sample()).collect();
    let phase_a_end = w.i;

    // ---- Phase B walk: 6 zerochecks ----
    let taus = l.taus;
    let ncol: Vec<usize> = leanvm_b::tables::tables().iter().map(|t| t.constraint_columns().len()).collect();
    for t in 0..6 {
        w.sample(); // eta
        for _ in 0..taus[t] {
            w.sample(); // r
        }
        for _ in 0..taus[t] {
            for _ in 0..3 {
                w.so();
            }
            w.sample();
        }
        for _ in 0..ncol[t] {
            w.so();
        }
    }
    let phase_b_end = w.i;

    // ---- Phase C walk: r_m sample (the PI claim); pins are sponge-silent ----
    w.sample();
    let phase_c_end = w.i;

    // ---- Phase D walk: flock reduction (values straight from the trace) ----
    // hint-bytes transport (raw words) then the opening marker.
    while matches!(ops[w.i], TraceOp::StreamRaw(_)) {
        w.i += 1;
    }
    assert!(matches!(ops[w.i], TraceOp::Opening));
    w.i += 1;
    assert_eq!(absorb(&mut w), b"flock-r1cs-v0".to_vec());
    let sd_bytes = absorb(&mut w); // statement digest (32 bytes)
    let _root_bytes = absorb(&mut w);
    assert_eq!(absorb(&mut w), b"flock-zerocheck-v0".to_vec());
    let n_log_b3 = l.taus[5];
    let m_r1cs = flock_prover::r1cs_hashes::blake3::K_LOG + n_log_b3;
    let n_mlv = m_r1cs - 6;
    let mut zc_r = Vec::new();
    for _ in 0..6 {
        zc_r.push(w.sample());
    }
    let inner7: Vec<F128> = flare::zerocheck::univariate_skip_optimized::small_challenges_ghash()
        .into_iter()
        .chain(flare::zerocheck::univariate_skip_optimized::medium_challenges_ghash())
        .collect();
    zc_r.extend(&inner7);
    for _ in 0..m_r1cs - 13 {
        zc_r.push(w.sample());
    }
    let zc1: Vec<F128> = (0..128).map(|_| observe(&mut w)).collect();
    let _zz = w.sample();
    let mut zcr = Vec::new();
    let mut zrho = Vec::new();
    for _ in 0..n_mlv {
        zcr.push(observe(&mut w));
        zcr.push(observe(&mut w));
        zrho.push(w.sample());
    }
    let zcf = vec![observe(&mut w), observe(&mut w)];
    assert_eq!(absorb(&mut w), b"flock-lincheck-v0".to_vec());
    let lc_alpha = w.sample();
    let lc_beta = w.sample();
    let mut lcr = Vec::new();
    let mut lrr = Vec::new();
    let lcrounds = flock_prover::r1cs_hashes::blake3::K_LOG - 6;
    for _ in 0..lcrounds {
        lcr.push(observe(&mut w));
        lcr.push(observe(&mut w));
        lrr.push(w.sample());
    }
    let lcz: Vec<F128> = (0..64).map(|_| observe(&mut w)).collect();
    let _lsk = w.sample();
    let phase_d_end = w.i;

    // matpart = the deferred weighted matrix evaluation: the lincheck running
    // claim minus (= plus, char 2) the const-pin contribution.
    let r1cs = flock_prover::r1cs_hashes::blake3::build_block_r1cs(n_log_b3);
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

    // ---- Phase E1 walk: opening labels, ring-switch fronts, claim combine ----
    assert_eq!(absorb(&mut w), b"flock-pcs-open-batch-v0".to_vec());
    let mut shv = Vec::new();
    let mut rdp = Vec::new();
    for _ in 0..2 {
        assert_eq!(absorb(&mut w), b"flock-ring-switch-v0".to_vec());
        for _ in 0..128 {
            shv.push(observe(&mut w));
        }
        for _ in 0..7 {
            rdp.push(w.sample());
        }
    }
    let _g0 = w.sample();
    let _g1 = w.sample();
    let evtot_e: usize = ncol.iter().sum();
    let ncl = nclaims + evtot_e + 1 + 3;
    for _ in 0..ncl {
        assert_eq!(absorb(&mut w), b"flock-pcs-packed-direct-v0".to_vec());
        observe(&mut w);
    }
    for _ in 0..ncl {
        w.sample();
    }
    let phase_e1_end = w.i;

    // Deferred tensor claims: the transposed sumcheck claims per ring switch.
    let mut tclaim = Vec::new();
    for rs in 0..2 {
        let shu = flare::pcs::ring_switch::tensor_algebra_transpose(&shv[128 * rs..128 * rs + 128]);
        let eqd = flare::zerocheck::univariate_skip::build_eq(&rdp[7 * rs..7 * rs + 7]);
        tclaim.push(flare::pcs::ring_switch::inner_product(&shu, &eqd));
    }
    let tclaim_export = tclaim.clone();

    // ---- Phase E2 walk: the Ligerito core (mirror kept in lockstep for PoW) ----
    let stack_mu = l.m;
    let vcfg = flare::pcs::ligerito::LigeritoSecurityConfig::derive_profile(
        stack_mu + 7,
        flare::pcs::ligerito::LigeritoProfile::Secure,
    )
    .and_then(|s| s.to_prover_verifier_configs())
    .expect("stack ligerito config")
    .1;
    let log_n = stack_mu;
    let r = vcfg.level_steps;
    let nlev = r + 1;
    let klvl: Vec<usize> = std::iter::once(vcfg.initial_k).chain(vcfg.level_ks.iter().copied()).collect();
    let queries = vcfg.queries.clone();
    let mut lmc = vec![log_n - vcfg.initial_k];
    for i in 0..r {
        lmc.push(lmc[i] - vcfg.level_ks[i]);
    }
    let yr_log_n = *lmc.last().unwrap();
    let mut block_len = vec![1usize << (vcfg.initial_log_msg_cols + vcfg.log_inv_rates[0])];
    for i in 0..r {
        block_len.push(1usize << (vcfg.level_log_msg_cols[i] + vcfg.log_inv_rates[i + 1]));
    }
    let depth: Vec<usize> = block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    let per: Vec<usize> = depth.iter().map(|&d| 128 / d).collect();
    let nsq: Vec<usize> = (0..nlev).map(|i| queries[i].div_ceil(per[i])).collect();
    let fgb = |lvl: usize| vcfg.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;

    // Lockstep mirror through the ligerito section.
    let mut lm = seed.clone();
    lm.replay(&ops[0..phase_e1_end]);
    let mut fold_pow: Vec<(u32, u64, F128)> = Vec::new();
    let mut lig_sc: Vec<F128> = Vec::new();
    let mut lig_raw: Vec<Vec<F128>> = vec![Vec::new(); nlev]; // squeezes per level
    let mut lig_ris: Vec<F128> = Vec::new();
    let mut step = |w: &mut Walk, lm: &mut Mirror| {
        let op = w.ops[w.i].clone();
        w.i += 1;
        lm.replay(std::slice::from_ref(&op));
        op
    };
    let expect_obs = |op: TraceOp| match op {
        TraceOp::Observe(x) => x,
        other => panic!("lig walk: expected Observe, got {other:?}"),
    };
    let expect_sample = |op: TraceOp| match op {
        TraceOp::Sample(v) => v,
        other => panic!("lig walk: expected Sample, got {other:?}"),
    };
    // label + target + root
    assert!(matches!(step(&mut w, &mut lm), TraceOp::AbsorbBytes(b) if b == b"flock-ligerito-basis-v0"));
    let _walked_target = expect_obs(step(&mut w, &mut lm));
    assert!(matches!(step(&mut w, &mut lm), TraceOp::AbsorbBytes(_)));
    // prologue msg
    lig_sc.push(expect_obs(step(&mut w, &mut lm)));
    lig_sc.push(expect_obs(step(&mut w, &mut lm)));
    for lvl in 0..nlev {
        for j in 0..klvl[lvl] {
            let bits = (fgb(lvl) - j as i64).max(0) as u32;
            if bits > 0 {
                // PoW: digest from the mirror state BEFORE the nonce absorb.
                let (nonce, b2) = match w.ops[w.i] {
                    TraceOp::Pow { nonce, bits } => (nonce, bits),
                    ref other => panic!("expected Pow, got {other:?}"),
                };
                assert_eq!(b2, bits);
                let base = compress(lm.cv, [F128::ZERO, F128::new(5, 0)]);
                let dig = compress(base, [F128::new(nonce, 0), F128::new(5, 0)])[0];
                fold_pow.push((bits, nonce, dig));
                step(&mut w, &mut lm);
            } else {
                fold_pow.push((0, 0, F128::ZERO));
            }
            lig_ris.push(expect_sample(step(&mut w, &mut lm)));
            lig_sc.push(expect_obs(step(&mut w, &mut lm)));
            lig_sc.push(expect_obs(step(&mut w, &mut lm)));
        }
        if lvl == r {
            for _ in 0..(1usize << yr_log_n) {
                expect_obs(step(&mut w, &mut lm));
            }
        } else {
            assert!(matches!(step(&mut w, &mut lm), TraceOp::AbsorbBytes(_)));
        }
        // query-phase grind (0 bits) + squeezes + alphas
        assert!(matches!(step(&mut w, &mut lm), TraceOp::Pow { bits: 0, .. }));
        for _ in 0..nsq[lvl] {
            lig_raw[lvl].push(expect_sample(step(&mut w, &mut lm)));
        }
        let alphalen = flare::pcs::ligerito::ceil_log2(queries[lvl]);
        for _ in 0..alphalen {
            expect_sample(step(&mut w, &mut lm));
        }
        if lvl != r {
            lig_sc.push(expect_obs(step(&mut w, &mut lm)));
            lig_sc.push(expect_obs(step(&mut w, &mut lm)));
        }
        expect_sample(step(&mut w, &mut lm)); // beta
    }
    assert_eq!(w.i, ops.len(), "ligerito walk must consume the whole trace");

    // ---- hints ----
    // fpb: the grind digest bits. Base = compress(cv_after_alpha, [0, POW]).
    let mut m = seed.clone();
    // replay through the alpha sample (9 observes + 1 sample).
    m.replay(&ops[0..10]);
    let base = compress(m.cv, [F128::ZERO, F128::new(5, 0)]);
    let gdig = compress(base, [F128::new(nonce, 0), F128::new(5, 0)])[0];
    // bcv: the deferred bytecode evaluations, block/coord order.
    let mut bcv = Vec::new();
    let mut kbc = 0usize;
    for (s, blocks) in sides.iter().enumerate() {
        for blk in blocks.iter() {
            for c in &blk.coords {
                if let Coord::Public(vals) = c {
                    kbc = blk.kappa;
                    bcv.push(mle_eval(vals, &zetas[s][..blk.kappa]));
                }
            }
        }
    }
    assert_eq!(bcv.len(), nbcv);
    assert_eq!(bcv, bcv_trace, "layout-computed bytecode evals match the trace");
    let eq3 = |c: usize| -> F128 {
        let mut e = F128::ONE;
        for (t, &s) in sb.iter().enumerate() {
            e *= if (c >> t) & 1 == 1 { s } else { F128::ONE + s };
        }
        e
    };
    let wbc: Vec<F128> = (0..2)
        .map(|s| (0..6).map(|c| eq3(c) * bcv[6 * s + c]).fold(F128::ZERO, |a, x| a + x))
        .collect();
    let cinv = roots[2].inv();
    // checkpoint cvs after each phase.
    let mut m = seed.clone();
    m.replay(&ops[0..phase_a_end]);
    let cvchk_a = m.cv[0];
    let mut m = seed.clone();
    m.replay(&ops[0..phase_b_end]);
    let cvchk_b = m.cv[0];
    let mut m = seed.clone();
    m.replay(&ops[0..phase_c_end]);
    let cvchk_c = m.cv[0];
    let mut m = seed.clone();
    m.replay(&ops[0..phase_d_end]);
    let cvchk_d = m.cv[0];
    let mut m = seed.clone();
    m.replay(&ops[0..phase_e1_end]);
    let cvchk_e1 = m.cv[0];

    // ---- placeholder map ----
    let ints = |v: &[usize]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let us = |v: &[u128]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let mut rep = BTreeMap::new();
    let mut ps = |k: &str, v: String| {
        rep.insert(format!("{k}_PLACEHOLDER"), v);
    };
    ps("SEED0", u(seed.cv[0]).to_string());
    ps("SEED1", u(seed.cv[1]).to_string());
    ps("STREAM_LEN", proof.stream.len().to_string());
    let ann: Vec<u128> = (0..7).map(|i| u(proof.stream[i])).collect();
    ps("ANN", us(&ann));
    ps("GFULL", (gbits / 8).to_string());
    ps("GEXTRA", (gbits % 8).to_string());
    ps("GG", u(G).to_string());
    ps("ILD0", u(G.inv()).to_string());
    ps("ILD1", u((F128::ONE + G).inv()).to_string());
    ps("ILD2", u((G * (F128::ONE + G)).inv()).to_string());
    ps("CVCHK_A", u(cvchk_a).to_string());
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
    ps("NCLAIMS", (nclaims + evtot + 8).to_string());
    ps("NBCV", nbcv.to_string());
    ps("TAU", ints(&taus));
    ps("NCOL", ints(&ncol));
    let mut evoff = vec![0usize];
    for t in 0..5 {
        evoff.push(evoff[t] + ncol[t]);
    }
    ps("EVOFF", ints(&evoff));
    ps("TAUMAX", taus.iter().max().unwrap().to_string());
    ps("EVTOT", evtot.to_string());
    ps("CVCHK_B", u(cvchk_b).to_string());
    ps("PI0", u(pi[0]).to_string());
    ps("PI1", u(pi[1]).to_string());
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
    ps("CVCHK_C", u(cvchk_c).to_string());
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
    ps("CVCHK_D", u(cvchk_d).to_string());
    ps("OBLBLA", u(word16(b"flock-pcs-open-batch-v0", 0)).to_string());
    ps("OBLBLB", u(word16(b"flock-pcs-open-batch-v0", 16)).to_string());
    ps("RSLBLA", u(word16(b"flock-ring-switch-v0", 0)).to_string());
    ps("RSLBLB", u(word16(b"flock-ring-switch-v0", 16)).to_string());
    ps("PDLBLA", u(word16(b"flock-pcs-packed-direct-v0", 0)).to_string());
    ps("PDLBLB", u(word16(b"flock-pcs-packed-direct-v0", 16)).to_string());
    ps("NCL", ncl.to_string());
    ps("CVCHK_E1", u(cvchk_e1).to_string());

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
                    out.push(((bits >> (j * d)) as usize) & (block_len[lv] - 1));
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
            flare::pcs::ligerito::expand_level_opening(block_len[lv], &positions[lv], rows_of(lv), numinter[lv], path_of(lv))
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
    // deferred eval_rs_eq values (now that ris is known).
    let qpkdv = l.placements[leanvm_b::cpu::QPKD].n_vars;
    let zrho_tail: Vec<F128> = zrho[lcrounds..].to_vec();
    let x_outer_ab: Vec<F128> = lrr.iter().rev().copied().chain(zrho_tail.iter().copied()).collect();
    let x_outer_c: Vec<F128> = zc_r[6..m_r1cs].to_vec();
    let eqd_ab = flare::zerocheck::univariate_skip::build_eq(&rdp[0..7]);
    let eqd_c = flare::zerocheck::univariate_skip::build_eq(&rdp[7..14]);
    let rsq = vec![
        flare::pcs::ring_switch::eval_rs_eq(&x_outer_ab[1..], &lig_ris[..qpkdv], &eqd_ab),
        flare::pcs::ring_switch::eval_rs_eq(&x_outer_c[1..], &lig_ris[..qpkdv], &eqd_c),
    ];
    let rsq_hint = rsq.clone();

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
    ps("ROOTA", flds(&roota));
    ps("ROOTB", flds(&rootb));
    ps("FOLDBASE", ints(&foldbase));
    ps("ROWOFF", ints(&rowoff));
    ps("PATHOFF", ints(&pathoff));
    ps("SBITSOFF", ints(&sbitsoff));
    ps("SVKOFF", ints(&svkoff));
    ps("BITS", ints(&fold_pow.iter().map(|&(b, _, _)| b as usize).collect::<Vec<_>>()));
    ps("FULL", ints(&fold_pow.iter().map(|&(b, _, _)| (b / 8) as usize).collect::<Vec<_>>()));
    ps("EXTRA8", ints(&fold_pow.iter().map(|&(b, _, _)| (b % 8) as usize).collect::<Vec<_>>()));
    let fnv: Vec<u128> = fold_pow.iter().map(|&(_, n, _)| n as u128).collect();
    ps("FN", us(&fnv));
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

    // ---- outer public input: the deferred-data hash (mirrors guest Phase F) ----
    let mut h = Mirror { cv: [F128::ZERO; 2] };
    h.observe(pi[0]);
    h.observe(pi[1]);
    for zs in zetas.iter().take(2) {
        for k in 0..kbc {
            h.observe(zs[k]);
        }
    }
    for &v in &sb {
        h.observe(v);
    }
    for &v in &wbc {
        h.observe(v);
    }
    h.observe(lc_alpha);
    h.observe(_zz);
    for &v in &zrho[..lcrounds] {
        h.observe(v);
    }
    for &v in &lrr {
        h.observe(v);
    }
    for &v in &lcz {
        h.observe(v);
    }
    h.observe(matpart);
    for &v in &shv {
        h.observe(v);
    }
    for &v in &rdp {
        h.observe(v);
    }
    for &v in &tclaim_export {
        h.observe(v);
    }
    for &v in &rsq {
        h.observe(v);
    }
    for &v in &lig_ris[..qpkdv] {
        h.observe(v);
    }
    for &v in &zrho[lcrounds..] {
        h.observe(v);
    }
    for &v in &zc_r[13..] {
        h.observe(v);
    }
    let deferred = Deferred {
        outer_pi: h.cv,
        kbc,
        zetas01: [zetas[0].clone(), zetas[1].clone()],
        sb: sb.clone(),
        wbc: wbc.clone(),
        lc_alpha,
        zz: _zz,
        zrho: zrho.clone(),
        lrr: lrr.clone(),
        lcz: lcz.clone(),
        matpart,
        shv: shv.clone(),
        rdp: rdp.clone(),
        tclaim: tclaim_export.clone(),
        rsq: rsq.clone(),
        lig_ris_lo: lig_ris[..qpkdv].to_vec(),
        zc_r_tail: zc_r[13..].to_vec(),
        n_log_b3,
    };

    let mut zinv = vec![F128::ONE; n_mlv];
    for (i, item) in zinv.iter_mut().enumerate().take(n_mlv).skip(7) {
        *item = (F128::ONE + zc_r[6 + i]).inv();
    }
    let hints = vec![
        ("stream".to_string(), proof.stream.clone()),
        ("fpb".to_string(), bits_of(gdig)),
        ("bcv".to_string(), bcv),
        ("cinv".to_string(), vec![cinv]),
        ("zc1".to_string(), zc1),
        ("zcr".to_string(), zcr),
        ("zcf".to_string(), zcf.clone()),
        ("zinv".to_string(), zinv),
        ("lcr".to_string(), lcr.clone()),
        ("lcz".to_string(), lcz.clone()),
        ("matpart".to_string(), vec![matpart]),
        ("shv".to_string(), shv.clone()),
        ("tclaim".to_string(), tclaim),
        ("rsq".to_string(), rsq_hint),
        ("lsc".to_string(), lig_sc.clone()),
        ("lrows".to_string(), lrows_flat),
        ("lpaths".to_string(), lpaths_flat),
        ("lsbits".to_string(), lsbits_flat),
        ("lfpb".to_string(), lfpb_flat),
        ("lyr".to_string(), lig.final_proof.yr.clone()),
    ];
    (rep, hints, deferred)
}

/// Phase A of the recursion guest: seed → announced → root → the full bus
/// (grind, 3× GKR, count≠0, balance, decomposition with deferred bytecode),
/// proven and verified in-circuit against the real inner proof, with the final
/// sponge state checked against the trace replay.
#[test]
fn recursion_1to1() {
    let (program, proof) = prove_inner();
    let pi = inner_pi();
    trace_start();
    verify(&program, &pi, &proof).expect("inner verifies");
    let ops = trace_take();

    let (rep, hints, deferred) = gen_verify(&program, pi, &proof, &ops);
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/verify_recursive.py");
    let mut guest = compile(&parse_file_with_replacements(path, &rep).expect("parse verify_recursive.py"));
    for (name, vals) in &hints {
        guest.set_witness(name, vec![vals.clone()]);
    }
    // The outer public input IS the deferred-claim binding hash.
    let gpi = deferred.outer_pi;
    let t = std::time::Instant::now();
    let (gproof, stats) = prove(&guest, gpi);
    let t_prove = t.elapsed();
    let t = std::time::Instant::now();
    verify(&guest, &gpi, &gproof).expect("outer proof verifies");
    let t_verify = t.elapsed();
    // The outer verifier's remaining duty: discharge the deferred claims.
    let t = std::time::Instant::now();
    check_deferred(&program, pi, &proof, &deferred);
    let t_deferred = t.elapsed();
    let psize = bincode::serialize(&gproof).expect("serialize outer proof").len();
    eprintln!(
        "recursion_1to1 OK: guest {} cycles, {} BLAKE3; outer prove {:.2}s, verify {:.1}ms, deferred checks {:.1}ms, outer proof ~{} KiB",
        stats.cycles,
        stats.counts[5],
        t_prove.as_secs_f64(),
        t_verify.as_secs_f64() * 1e3,
        t_deferred.as_secs_f64() * 1e3,
        psize / 1024,
    );
}

/// Dump the transcript-op trace of a real `cpu::verify` run on the inner proof:
/// the guest's mechanical spec. Prints aggregate counts and the phase structure.
#[test]
fn inner_verify_trace() {
    let (program, proof) = prove_inner();
    let pi = inner_pi();
    trace_start();
    verify(&program, &pi, &proof).expect("inner verifies");
    let ops = trace_take();

    let mut counts: std::collections::BTreeMap<&'static str, usize> = Default::default();
    for op in &ops {
        *counts
            .entry(match op {
                TraceOp::StreamObserve(_) => "stream_observe",
                TraceOp::StreamRaw(_) => "stream_raw",
                TraceOp::Observe(_) => "observe",
                TraceOp::AbsorbBytes(_) => "absorb_bytes",
                TraceOp::Sample(_) => "sample",
                TraceOp::Pow { .. } => "pow",
                TraceOp::Opening => "opening",
            })
            .or_default() += 1;
    }
    eprintln!("[trace] total ops = {}", ops.len());
    for (k, v) in &counts {
        eprintln!("[trace]   {k:<16} {v}");
    }
    // Phase landmarks: print the first few ops and each absorb_bytes (labels/roots
    // delimit phases), with indices, so the guest structure can be aligned.
    for (i, op) in ops.iter().enumerate() {
        match op {
            TraceOp::AbsorbBytes(b) => {
                let txt = if b.len() == 32 {
                    "<32-byte root>".to_string()
                } else {
                    String::from_utf8_lossy(b).to_string()
                };
                eprintln!("[trace] {i:>6}: absorb_bytes {txt}");
            }
            TraceOp::Pow { nonce, bits } => eprintln!("[trace] {i:>6}: pow bits={bits} nonce={nonce}"),
            TraceOp::Opening => eprintln!("[trace] {i:>6}: opening"),
            _ => {}
        }
    }
}
