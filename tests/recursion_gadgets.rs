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
