//! Recursion verifier gadgets, built bottom-up as zkDSL programs and proven +
//! verified end-to-end. Each test compiles a small program string, feeds any
//! prover witness, and asserts the leanVM-b prover/verifier accept it — the same
//! path a real recursive verifier will run on.
//!
//! Gadget 1: **bit decomposition**. A GF(2^128) element is its 128-bit
//! polynomial-basis vector `v = Σ b_i·x^i`, and here the basis monomial `x^i`
//! equals `GEN**i` for `i < 128`. So we hint the 128 bits, boolean-constrain each
//! (`b² = b`), reconstruct `Σ b_i·GEN**i`, and assert it equals `v`. Full-width so
//! the reconstruction is exact (no modular wraparound). This is the primitive
//! behind Merkle query-index extraction and PoW leading-zero checks.

use leanvm_b::compiler::{compile, parse};
use leanvm_b::cpu::{prove, verify};
use leanvm_b::field::F128;

/// The 128 polynomial-basis coefficients of `v`, LSB first (`bit i` = coeff of
/// `x^i` = the monomial `GEN**i`), each as a field 0/1.
fn bits_of(v: F128) -> Vec<F128> {
    let mut out = Vec::with_capacity(128);
    for i in 0..64 {
        out.push(F128::new((v.lo >> i) & 1, 0));
    }
    for i in 0..64 {
        out.push(F128::new((v.hi >> i) & 1, 0));
    }
    out
}

#[test]
fn bit_decompose_128() {
    let lo = 0x0123_4567_89ab_cdefu64;
    let hi = 0xfedc_ba98_7654_3210u64;
    let v = F128::new(lo, hi);
    let v_u128 = (lo as u128) | ((hi as u128) << 64);

    // The guest hints v's 128 bits, checks each is boolean, reconstructs
    // Σ b_i·GEN**i, and asserts it equals the compile-time constant V = v.
    // The weight GEN**i is carried as a compile-time-folded running constant
    // `w` (×GEN each unrolled step, zero instructions) — the parser only accepts
    // a literal exponent in `GEN ** k`, so we cannot write `GEN ** i`.
    let src = format!(
        "from snark_lib import *\n\
         V = {v_u128}\n\
         \n\
         def main():\n\
         \x20   bits = StackBuf(128)\n\
         \x20   hint_witness(bits, \"bits\")\n\
         \x20   b0 = bits[0]\n\
         \x20   sq0 = b0 * b0\n\
         \x20   assert sq0 == b0\n\
         \x20   acc = b0\n\
         \x20   w = GEN\n\
         \x20   for i in unroll(1, 128):\n\
         \x20       b = bits[i]\n\
         \x20       sq = b * b\n\
         \x20       assert sq == b\n\
         \x20       acc = acc + b * w\n\
         \x20       w = w * GEN\n\
         \x20   assert acc == V\n\
         \x20   return\n"
    );

    let mut program = compile(&parse(&src).expect("parse"));
    program.set_witness("bits", vec![bits_of(v)]);
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("bit-decompose verifies");
}

/// Gadget 2: **Fiat–Shamir sponge replay**. The transcript sponge
/// (`src/transcript.rs`) is a 256-bit chaining value advanced only by the fixed
/// 64→32 BLAKE3 compression the `blake3` opcode computes, domain-tagged in the
/// second input word: `observe(x)` = `compress(cv, [x, DS_SCALAR])`, `sample()` =
/// `compress(cv, [0, DS_SQUEEZE])` (its first output word is the challenge, the
/// full output the new state). Because it's exactly the `blake3` opcode, a guest
/// program re-derives byte-identical challenges. Here the guest observes two
/// scalars and squeezes, and asserts the challenge equals the value `vmhash`
/// (the opcode's Rust twin) computes for the same steps.
#[test]
fn sponge_observe_sample() {
    use leanvm_b::vmhash::compress;
    // Domain-separation tags (src/transcript.rs): carried in the SECOND word.
    let ds_scalar = F128::new(1, 0);
    let ds_squeeze = F128::new(4, 0);

    let x0 = F128::new(0x1111_2222_3333_4444, 0x5555_6666_7777_8888);
    let x1 = F128::new(0x9999_aaaa_bbbb_cccc, 0xdddd_eeee_ffff_0000);

    // Reference challenge: zero IV, observe x0, observe x1, squeeze.
    let mut cv = [F128::ZERO, F128::ZERO];
    cv = compress(cv, [x0, ds_scalar]);
    cv = compress(cv, [x1, ds_scalar]);
    let challenge = compress(cv, [F128::ZERO, ds_squeeze])[0];

    let u = |f: F128| (f.lo as u128) | ((f.hi as u128) << 64);
    let src = format!(
        "from snark_lib import *\n\
         X0 = {}\n\
         X1 = {}\n\
         CH = {}\n\
         DS_SCALAR = 1\n\
         DS_SQUEEZE = 4\n\
         \n\
         def main():\n\
         \x20   cv = StackBuf(2)\n\
         \x20   cv[0] = 0\n\
         \x20   cv[1] = 0\n\
         \x20   in0 = StackBuf(2)\n\
         \x20   in0[0] = X0\n\
         \x20   in0[1] = DS_SCALAR\n\
         \x20   cv1 = StackBuf(2)\n\
         \x20   blake3(cv, in0, cv1)\n\
         \x20   in1 = StackBuf(2)\n\
         \x20   in1[0] = X1\n\
         \x20   in1[1] = DS_SCALAR\n\
         \x20   cv2 = StackBuf(2)\n\
         \x20   blake3(cv1, in1, cv2)\n\
         \x20   sq = StackBuf(2)\n\
         \x20   sq[0] = 0\n\
         \x20   sq[1] = DS_SQUEEZE\n\
         \x20   out = StackBuf(2)\n\
         \x20   blake3(cv2, sq, out)\n\
         \x20   ch = out[0]\n\
         \x20   assert ch == CH\n\
         \x20   return\n",
        u(x0),
        u(x1),
        u(challenge)
    );

    let program = compile(&parse(&src).expect("parse"));
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("sponge replay verifies");
}

/// Gadget 3: **transcript reader** — the `next_scalar` loop. A recursive verifier
/// consumes the inner proof's scalar stream (fed here as a `hint_witness` array),
/// absorbing each scalar into the sponge as it reads it, then samples. The stream
/// is walked with a `× GEN` cursor (`sp[1]` is the current cell, `sp = sp*GEN`
/// steps — folded, free), and the 256-bit chaining value is threaded through two
/// rebinding scalars re-packed into a `blake3` operand each step (the copies are
/// forwarded, not emitted). This is the exact replay of `VerifierState` reading
/// `n` scalars via `next_scalar` (each observes) and then `sample`.
#[test]
fn transcript_reader_observe() {
    use leanvm_b::vmhash::compress;
    let ds_scalar = F128::new(1, 0);
    let ds_squeeze = F128::new(4, 0);

    // The inner proof's stream (arbitrary scalars).
    let stream: Vec<F128> = (0..5u64)
        .map(|k| F128::new(0x1000_0000_0000_0001u64.wrapping_mul(k + 1), 0xABCD_0000 ^ (k << 40)))
        .collect();

    // Reference: absorb each, then squeeze.
    let mut cv = [F128::ZERO, F128::ZERO];
    for &x in &stream {
        cv = compress(cv, [x, ds_scalar]);
    }
    let challenge = compress(cv, [F128::ZERO, ds_squeeze])[0];

    let u = |f: F128| (f.lo as u128) | ((f.hi as u128) << 64);
    let src = format!(
        "from snark_lib import *\n\
         N = 5\n\
         CH = {}\n\
         DS_SCALAR = 1\n\
         DS_SQUEEZE = 4\n\
         \n\
         def main():\n\
         \x20   stream = HeapBuf(N)\n\
         \x20   hint_witness(stream[0:N], \"stream\")\n\
         \x20   cv0 = 0\n\
         \x20   cv1 = 0\n\
         \x20   sp = stream\n\
         \x20   for i in unroll(0, N):\n\
         \x20       cvb = StackBuf(2)\n\
         \x20       cvb[0] = cv0\n\
         \x20       cvb[1] = cv1\n\
         \x20       inp = StackBuf(2)\n\
         \x20       inp[0] = sp[1]\n\
         \x20       inp[1] = DS_SCALAR\n\
         \x20       out = StackBuf(2)\n\
         \x20       blake3(cvb, inp, out)\n\
         \x20       cv0 = out[0]\n\
         \x20       cv1 = out[1]\n\
         \x20       sp = sp * GEN\n\
         \x20   final = StackBuf(2)\n\
         \x20   final[0] = cv0\n\
         \x20   final[1] = cv1\n\
         \x20   sqin = StackBuf(2)\n\
         \x20   sqin[0] = 0\n\
         \x20   sqin[1] = DS_SQUEEZE\n\
         \x20   outc = StackBuf(2)\n\
         \x20   blake3(final, sqin, outc)\n\
         \x20   ch = outc[0]\n\
         \x20   assert ch == CH\n\
         \x20   return\n",
        u(challenge)
    );

    let mut program = compile(&parse(&src).expect("parse"));
    program.set_witness("stream", vec![stream]);
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("transcript reader verifies");
}

/// Gadget 4: **`observe_bytes` on a Merkle root** — the last FS-challenger op the
/// Ligerito verifier needs (it `observe_bytes(&root)`s at every level commit).
/// `absorb_bytes` (src/transcript.rs) frames the length then absorbs 16-byte
/// words, each tagged `DS_BYTE`: a 32-byte root is `compress(cv,[32,DS_LEN])`
/// then two `compress(cv,[word,DS_BYTE])` over the two root scalars (exactly the
/// `root_to_scalars` split). Confirms the guest reproduces root binding + a
/// subsequent challenge.
#[test]
fn observe_root_bytes() {
    use leanvm_b::vmhash::compress;
    let ds_len = F128::new(3, 0);
    let ds_byte = F128::new(2, 0);
    let ds_squeeze = F128::new(4, 0);

    // A 32-byte root, viewed as its two field scalars (little-endian words).
    let r0 = F128::new(0x0011_2233_4455_6677, 0x8899_aabb_ccdd_eeff);
    let r1 = F128::new(0xffee_ddcc_bbaa_9988, 0x7766_5544_3322_1100);

    let mut cv = [F128::ZERO, F128::ZERO];
    cv = compress(cv, [F128::new(32, 0), ds_len]); // length frame (32 bytes)
    cv = compress(cv, [r0, ds_byte]); // word 0
    cv = compress(cv, [r1, ds_byte]); // word 1
    let challenge = compress(cv, [F128::ZERO, ds_squeeze])[0];

    let u = |f: F128| (f.lo as u128) | ((f.hi as u128) << 64);
    let src = format!(
        "from snark_lib import *\n\
         R0 = {}\n\
         R1 = {}\n\
         CH = {}\n\
         DS_LEN = 3\n\
         DS_BYTE = 2\n\
         DS_SQUEEZE = 4\n\
         \n\
         def main():\n\
         \x20   cv = StackBuf(2)\n\
         \x20   cv[0] = 0\n\
         \x20   cv[1] = 0\n\
         \x20   lenf = StackBuf(2)\n\
         \x20   lenf[0] = 32\n\
         \x20   lenf[1] = DS_LEN\n\
         \x20   cv1 = StackBuf(2)\n\
         \x20   blake3(cv, lenf, cv1)\n\
         \x20   w0 = StackBuf(2)\n\
         \x20   w0[0] = R0\n\
         \x20   w0[1] = DS_BYTE\n\
         \x20   cv2 = StackBuf(2)\n\
         \x20   blake3(cv1, w0, cv2)\n\
         \x20   w1 = StackBuf(2)\n\
         \x20   w1[0] = R1\n\
         \x20   w1[1] = DS_BYTE\n\
         \x20   cv3 = StackBuf(2)\n\
         \x20   blake3(cv2, w1, cv3)\n\
         \x20   sqin = StackBuf(2)\n\
         \x20   sqin[0] = 0\n\
         \x20   sqin[1] = DS_SQUEEZE\n\
         \x20   outc = StackBuf(2)\n\
         \x20   blake3(cv3, sqin, outc)\n\
         \x20   ch = outc[0]\n\
         \x20   assert ch == CH\n\
         \x20   return\n",
        u(r0),
        u(r1),
        u(challenge)
    );

    let program = compile(&parse(&src).expect("parse"));
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("observe-root verifies");
}
