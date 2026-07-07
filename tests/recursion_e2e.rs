//! End-to-end 1→1 recursion: a guest program replays `cpu::verify` of a
//! non-trivial inner proof in-circuit, with the bytecode and flock-matrix
//! evaluations deferred to the public input (doc.tex §Deferred evaluation
//! claims). Built bottom-up: the transcript trace of a REAL `cpu::verify` run is
//! the guest's mechanical spec (`transcript::trace_start`/`trace_take`), and the
//! real `cpu::layout` supplies every compile-time shape.

use leanvm_b::compiler::{compile, parse};
use leanvm_b::cpu::{Program, prove, verify};
use leanvm_b::field::F128;
use leanvm_b::transcript::{TraceOp, trace_start, trace_take};

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
