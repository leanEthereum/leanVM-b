//! End-to-end 1→1 recursion: a guest program replays `cpu::verify` of a
//! non-trivial inner proof in-circuit, with the bytecode and flock-matrix
//! evaluations deferred to the public input (doc.tex §Deferred evaluation
//! claims). Built bottom-up: the transcript trace of a REAL `cpu::verify` run is
//! the guest's mechanical spec (`transcript::trace_start`/`trace_take`), and the
//! real `cpu::layout` supplies every compile-time shape.

use std::collections::BTreeMap;

use leanvm_b::compiler::{compile, parse, parse_file_with_replacements};
use leanvm_b::cpu::{Program, prove, verify};
use leanvm_b::field::{F128, G, g_pow};
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

/// Config + hints for the recursion guest (`tests/verify_recursive.py`), built
/// from the REAL `cpu::layout` of the inner program and the transcript trace of
/// a real `cpu::verify` run (zero hand-mirroring drift).
fn gen_verify(
    program: &Program,
    pi: [F128; 2],
    proof: &leanvm_b::cpu::Proof,
    ops: &[TraceOp],
) -> (BTreeMap<String, String>, Vec<(String, Vec<F128>)>) {
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
    let mut w = Walk { ops, i: 0 };
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

    // ---- hints ----
    // fpb: the grind digest bits. Base = compress(cv_after_alpha, [0, POW]).
    let seed = Mirror::new(b"leanvm-b", &[pi[0], pi[1], dig[0], dig[1]]);
    let mut m = seed.clone();
    // replay through the alpha sample (9 observes + 1 sample).
    m.replay(&ops[0..10]);
    let base = compress(m.cv, [F128::ZERO, F128::new(5, 0)]);
    let gdig = compress(base, [F128::new(nonce, 0), F128::new(5, 0)])[0];
    // bcv: the deferred bytecode evaluations, block/coord order.
    let mut bcv = Vec::new();
    for (s, blocks) in sides.iter().enumerate() {
        for blk in blocks.iter() {
            for c in &blk.coords {
                if let Coord::Public(vals) = c {
                    bcv.push(mle_eval(vals, &zetas[s][..blk.kappa]));
                }
            }
        }
    }
    assert_eq!(bcv.len(), nbcv);
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

    let hints = vec![
        ("stream".to_string(), proof.stream.clone()),
        ("fpb".to_string(), bits_of(gdig)),
        ("bcv".to_string(), bcv),
        ("cinv".to_string(), vec![cinv]),
    ];
    (rep, hints)
}

/// Phase A of the recursion guest: seed → announced → root → the full bus
/// (grind, 3× GKR, count≠0, balance, decomposition with deferred bytecode),
/// proven and verified in-circuit against the real inner proof, with the final
/// sponge state checked against the trace replay.
#[test]
fn guest_phase_a() {
    let (program, proof) = prove_inner();
    let pi = inner_pi();
    trace_start();
    verify(&program, &pi, &proof).expect("inner verifies");
    let ops = trace_take();

    let (rep, hints) = gen_verify(&program, pi, &proof, &ops);
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/verify_recursive.py");
    let mut guest = compile(&parse_file_with_replacements(path, &rep).expect("parse verify_recursive.py"));
    for (name, vals) in &hints {
        guest.set_witness(name, vec![vals.clone()]);
    }
    let gpi = [F128::ZERO, F128::ZERO];
    let (gproof, stats) = prove(&guest, gpi);
    verify(&guest, &gpi, &gproof).expect("phase A verifies in-circuit");
    eprintln!("guest_phase_a OK: {} cycles, {} BLAKE3", stats.cycles, stats.counts[5]);
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
