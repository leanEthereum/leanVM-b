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

/// A field element as the decimal `u128` the zkDSL parser accepts as a literal.
fn u(f: F128) -> u128 {
    (f.lo as u128) | ((f.hi as u128) << 64)
}

/// A faithful Rust mirror of `src/transcript.rs`'s `Sponge` seeding, so a test
/// can compute the exact chaining value the guest must start its transcript
/// replay from (the real `Sponge` is private). Same `compress`, same domain
/// tags, same framing — this is the value the recursion harness will bake into
/// the guest as a constant.
mod fs_ref {
    use leanvm_b::field::F128;
    use leanvm_b::vmhash::compress;
    const DS_SCALAR: F128 = F128::new(1, 0);
    const DS_BYTE: F128 = F128::new(2, 0);
    const DS_LEN: F128 = F128::new(3, 0);

    fn absorb_bytes(mut cv: [F128; 2], bytes: &[u8]) -> [F128; 2] {
        cv = compress(cv, [F128::new(bytes.len() as u64, 0), DS_LEN]);
        for chunk in bytes.chunks(16) {
            let mut buf = [0u8; 16];
            buf[..chunk.len()].copy_from_slice(chunk);
            let w = F128::new(
                u64::from_le_bytes(buf[..8].try_into().unwrap()),
                u64::from_le_bytes(buf[8..16].try_into().unwrap()),
            );
            cv = compress(cv, [w, DS_BYTE]);
        }
        cv
    }

    /// The chaining value after `Sponge::new(label, statement)`.
    pub fn seed_cv(label: &[u8], statement: &[F128]) -> [F128; 2] {
        let mut cv = [F128::ZERO, F128::ZERO];
        cv = absorb_bytes(cv, b"leanvm-b/transcript/v1");
        cv = absorb_bytes(cv, label);
        for &x in statement {
            cv = compress(cv, [x, DS_SCALAR]);
        }
        cv
    }
}

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

// ---- Gadget 5: the degree-2 sumcheck / GKR grand-product verifier ----
//
// This is the first *code-generated* verifier: a Rust emitter unrolls
// `gkr::verify_product` for a fixed `mu` into straight-line zkDSL (the real
// recursion verifier will dispatch a runtime `mu` to such unrolled variants via
// `match_range`, exactly as the reference's `whir.py` does). The guest replays a
// real `gkr::prove_product` transcript (fed as a `hint_witness` stream), running
// every round's eq-trick consistency check and Lagrange interpolation itself,
// and publishes the final leaf-claim value — which write-once pins to the value
// the native `gkr::verify_product` returns.

/// Append one 4-space-indented line to a `main()` body under construction.
fn line(s: &mut String, l: String) {
    s.push_str("    ");
    s.push_str(&l);
    s.push('\n');
}

/// Emit `next_scalar`: read `stream[cursor]` into `dst`, absorb it into the
/// sponge (`cv0,cv1`), and step the cursor (`sp *= GEN`). Mirrors
/// `VerifierState::next_scalar`.
fn emit_read(s: &mut String, n: &mut usize, dst: &str) {
    let k = *n;
    *n += 1;
    line(s, format!("{dst} = sp[1]"));
    line(s, format!("rb{k} = StackBuf(2)"));
    line(s, format!("rb{k}[0] = cv0"));
    line(s, format!("rb{k}[1] = cv1"));
    line(s, format!("ri{k} = StackBuf(2)"));
    line(s, format!("ri{k}[0] = {dst}"));
    line(s, format!("ri{k}[1] = 1")); // DS_SCALAR
    line(s, format!("ro{k} = StackBuf(2)"));
    line(s, format!("blake3(rb{k}, ri{k}, ro{k})"));
    line(s, format!("cv0 = ro{k}[0]"));
    line(s, format!("cv1 = ro{k}[1]"));
    line(s, "sp = sp * GEN".into());
}

/// Emit `sample`: squeeze a challenge into `dst` and ratchet the sponge.
fn emit_sample(s: &mut String, n: &mut usize, dst: &str) {
    let k = *n;
    *n += 1;
    line(s, format!("sb{k} = StackBuf(2)"));
    line(s, format!("sb{k}[0] = cv0"));
    line(s, format!("sb{k}[1] = cv1"));
    line(s, format!("si{k} = StackBuf(2)"));
    line(s, format!("si{k}[0] = 0"));
    line(s, format!("si{k}[1] = 4")); // DS_SQUEEZE
    line(s, format!("so{k} = StackBuf(2)"));
    line(s, format!("blake3(sb{k}, si{k}, so{k})"));
    line(s, format!("{dst} = so{k}[0]"));
    line(s, format!("cv0 = so{k}[0]"));
    line(s, format!("cv1 = so{k}[1]"));
}

/// Generate the full zkDSL program that replays `gkr::verify_product` for a
/// power-of-two leaf count `2^mu`, starting the transcript from `seed`, and
/// publishes the final leaf-claim value (pinned to `LEAF` via the public input).
fn gkr_verify_source(mu: usize, seed: [F128; 2], leaf_val: F128, n_stream: usize) -> String {
    let g = F128::generator();
    // Lagrange inverse-denominators at nodes {0,1,g} — compile-time constants.
    let inv0 = g.inv();
    let inv1 = (F128::ONE + g).inv();
    let inv2 = (g * (F128::ONE + g)).inv();

    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    s.push_str(&format!("SEED0 = {}\n", u(seed[0])));
    s.push_str(&format!("SEED1 = {}\n", u(seed[1])));
    s.push_str(&format!("INV0 = {}\n", u(inv0)));
    s.push_str(&format!("INV1 = {}\n", u(inv1)));
    s.push_str(&format!("INV2 = {}\n", u(inv2)));
    s.push_str(&format!("LEAF = {}\n", u(leaf_val)));
    s.push_str(&format!("N = {n_stream}\n\n"));
    s.push_str("def main():\n");

    let mut n = 0usize;
    line(&mut s, "stream = HeapBuf(N)".into());
    line(&mut s, "hint_witness(stream[0:N], \"stream\")".into());
    line(&mut s, format!("rbuf = HeapBuf({})", mu * mu));
    line(&mut s, "cv0 = SEED0".into());
    line(&mut s, "cv1 = SEED1".into());
    line(&mut s, "sp = stream".into());
    emit_read(&mut s, &mut n, "root"); // observe the product root
    line(&mut s, "claim = root".into());

    for p in 0..mu {
        let k = p; // rounds this layer
        let base = p * mu; // this layer's r-vector base in rbuf
        let mut eqacc = format!("ea{p}_0");
        line(&mut s, format!("{eqacc} = GEN ** 0")); // eq_acc = 1 (a field one)
        for round in 0..k {
            let (m0, m1, m2) = (
                format!("m{p}_{round}_0"),
                format!("m{p}_{round}_1"),
                format!("m{p}_{round}_2"),
            );
            emit_read(&mut s, &mut n, &m0);
            emit_read(&mut s, &mut n, &m1);
            emit_read(&mut s, &mut n, &m2);
            // rj = r[round] of the previous layer.
            let rj = format!("rj{p}_{round}");
            line(&mut s, format!("{rj} = rbuf[GEN ** {}]", (p - 1) * mu + round));
            // eq-trick round check: eq_acc*((1+rj)*m0 + rj*m1) == claim.
            line(&mut s, format!("or{p}_{round} = 1 + {rj}"));
            line(&mut s, format!("tm{p}_{round} = or{p}_{round} * {m0} + {rj} * {m1}"));
            line(&mut s, format!("ck{p}_{round} = {eqacc} * tm{p}_{round}"));
            line(&mut s, format!("assert ck{p}_{round} == claim"));
            // sample rk, record rho[round] at position round+1.
            let rk = format!("rk{p}_{round}");
            emit_sample(&mut s, &mut n, &rk);
            line(&mut s, format!("rbuf[GEN ** {}] = {rk}", base + round + 1));
            // eq_acc *= 1 + rj + rk.
            let neweq = format!("ea{p}_{}", round + 1);
            line(&mut s, format!("os{p}_{round} = 1 + {rj} + {rk}"));
            line(&mut s, format!("{neweq} = {eqacc} * os{p}_{round}"));
            eqacc = neweq;
            // claim = eq_acc * lagrange(msg, rk), nodes {0,1,g}.
            line(&mut s, format!("pa{p}_{round} = {rk} + 1"));
            line(&mut s, format!("pb{p}_{round} = {rk} + GEN"));
            line(&mut s, format!("l0{p}_{round} = {m0} * pa{p}_{round} * pb{p}_{round} * INV0"));
            line(&mut s, format!("l1{p}_{round} = {m1} * {rk} * pb{p}_{round} * INV1"));
            line(&mut s, format!("l2{p}_{round} = {m2} * {rk} * pa{p}_{round} * INV2"));
            line(&mut s, format!("lg{p}_{round} = l0{p}_{round} + l1{p}_{round} + l2{p}_{round}"));
            line(&mut s, format!("claim = {eqacc} * lg{p}_{round}"));
        }
        // Layer tail: read the two child evals, check, sample c, connect.
        let (e0, e1) = (format!("ev{p}_0"), format!("ev{p}_1"));
        emit_read(&mut s, &mut n, &e0);
        emit_read(&mut s, &mut n, &e1);
        line(&mut s, format!("pe{p} = {e0} * {e1}"));
        line(&mut s, format!("pv{p} = {eqacc} * pe{p}"));
        line(&mut s, format!("assert claim == pv{p}"));
        let c = format!("c{p}");
        emit_sample(&mut s, &mut n, &c);
        line(&mut s, format!("rbuf[GEN ** {base}] = {c}"));
        line(&mut s, format!("dd{p} = {e0} + {e1}"));
        line(&mut s, format!("claim = {e0} + {c} * dd{p}"));
    }

    // Publish the leaf-claim value into m[0]; write-once pins it to LEAF.
    line(&mut s, "pp = GEN ** 0".into());
    line(&mut s, "pp[1] = claim".into());
    line(&mut s, "return".into());
    s
}

/// Gadget 8: **runtime-count observe loop** — the write-once sponge chain over a
/// `mul_range` whose bound is a *runtime* g-power. The Ligerito verifier has loops
/// whose length is a runtime size (query counts, round counts), and `mul_range`
/// can't carry a `StackBuf` and memory is write-once, so the chaining value is
/// threaded through a HeapBuf: step `j` (counter `x = g^j`, base `b = x·x =
/// g^{2j}`) reads `cv_j` at cells `2j,2j+1` and writes `cv_{j+1}` at `2j+2,2j+3`
/// (the Fibonacci idiom). After `N` steps `cv_N` sits at cell `2N`, addressed by
/// the runtime `nbound·nbound`. This is the pattern every runtime-length loop in
/// the assembled verifier will use.
#[test]
fn runtime_observe_loop() {
    use leanvm_b::vmhash::compress;
    let ds_scalar = F128::new(1, 0);
    let ds_squeeze = F128::new(4, 0);

    let n = 5usize;
    let stream: Vec<F128> = (0..n as u64)
        .map(|k| F128::new(0xC0FFEE_00 ^ k.wrapping_mul(0x9E3779B9), 0x1357_9BDF ^ (k << 32)))
        .collect();
    let mut cv = [F128::ZERO, F128::ZERO];
    for &x in &stream {
        cv = compress(cv, [x, ds_scalar]);
    }
    let challenge = compress(cv, [F128::ZERO, ds_squeeze])[0];

    // nbound = g^N carries the loop length "in the exponent"; the runner walks the
    // counter x = g^0..g^{N-1} and stops on reaching nbound.
    let nbound = leanvm_b::field::g_pow(n);

    let src = format!(
        "from snark_lib import *\n\
         CH = {}\n\
         N = {n}\n\
         \n\
         def main():\n\
         \x20   nb = StackBuf(1)\n\
         \x20   hint_witness(nb, \"nbound\")\n\
         \x20   nbound = nb[0]\n\
         \x20   assert log(nbound) < 16\n\
         \x20   stream = HeapBuf(N)\n\
         \x20   hint_witness(stream[0:N], \"stream\")\n\
         \x20   cvbuf = HeapBuf(nbound * nbound * GEN ** 2)\n\
         \x20   cvbuf[1] = 0\n\
         \x20   cvbuf[GEN] = 0\n\
         \x20   for x in mul_range(1, nbound):\n\
         \x20       b = x * x\n\
         \x20       inp = StackBuf(2)\n\
         \x20       inp[0] = stream[x]\n\
         \x20       inp[1] = 1\n\
         \x20       blake3(cvbuf[b : b + 2], inp, cvbuf[b * GEN ** 2 : b * GEN ** 2 + 2])\n\
         \x20   fb = nbound * nbound\n\
         \x20   cvf = StackBuf(2)\n\
         \x20   cvf[0] = cvbuf[fb]\n\
         \x20   cvf[1] = cvbuf[fb * GEN]\n\
         \x20   sqin = StackBuf(2)\n\
         \x20   sqin[0] = 0\n\
         \x20   sqin[1] = 4\n\
         \x20   outc = StackBuf(2)\n\
         \x20   blake3(cvf, sqin, outc)\n\
         \x20   ch = outc[0]\n\
         \x20   assert ch == CH\n\
         \x20   return\n",
        u(challenge),
    );

    let mut program = compile(&parse(&src).expect("parse runtime-observe"));
    program.set_witness("nbound", vec![vec![nbound]]);
    program.set_witness("stream", vec![stream]);
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("runtime-observe loop verifies");
}

// ---- Ligerito core: native driver probe (tiny instance, 1 query/level) ----
//
// Drives flock's actual recursive Ligerito prover + succinct verifier at a tiny
// config with a leanVM-b ProverState challenger (the compress-sponge the zkDSL
// guest replays). With 1 query per level the octopus multi-proof degenerates to a
// single Merkle path, keeping the port tractable. Prints the concrete proof shapes
// the guest port must consume.
#[test]
fn ligerito_native_probe() {
    use leanvm_b::transcript::ProverState;
    use flare::lincheck::build_eq_table;
    use flare::ntt::AdditiveNttF128;
    use flare::pcs::ligerito::{
        ProverConfig, VerifierConfig, ligero_commit, recursive_prover_with_basis,
        recursive_verifier_with_basis_succinct,
    };
    use flare::zerocheck::multilinear::eq_eval;

    let log_n = 8usize;
    let initial_k = 2usize;
    let k_0 = 2usize;
    let rate = 1usize;

    let poly: Vec<F128> = (0..(1usize << log_n))
        .map(|i| F128::new(0x9E37_79B9u64.wrapping_mul(i as u64 + 1) + 1, 0x1234 ^ (i as u64)))
        .collect();
    let z: Vec<F128> = (0..log_n).map(|i| F128::new(0xABCD + i as u64, 0x55u64.wrapping_mul(i as u64) + 7)).collect();
    let b = build_eq_table(&z);
    let target: F128 = poly.iter().zip(b.iter()).map(|(&a, &c)| a * c).fold(F128::ZERO, |a, x| a + x);

    let lir = vec![rate, rate];
    let pc = ProverConfig {
        log_inv_rates: lir.clone(),
        recursive_steps: 1,
        initial_log_msg_cols: log_n - initial_k,
        initial_log_num_interleaved: initial_k,
        initial_k,
        recursive_log_msg_cols: vec![log_n - initial_k - k_0],
        recursive_ks: vec![k_0],
        queries: vec![1, 1],
        grinding_bits: vec![0; 2],
        fold_grinding_bits: vec![0; 2],
        ood_samples: vec![0; 2],
    };
    let vc = VerifierConfig {
        log_inv_rates: lir.clone(),
        recursive_steps: 1,
        initial_log_msg_cols: log_n - initial_k,
        initial_log_num_interleaved: initial_k,
        initial_k,
        recursive_log_msg_cols: vec![log_n - initial_k - k_0],
        recursive_ks: vec![k_0],
        queries: vec![1, 1],
        grinding_bits: vec![0; 2],
        fold_grinding_bits: vec![0; 2],
        ood_samples: vec![0; 2],
    };

    let ntt = AdditiveNttF128::standard(log_n - initial_k + rate);
    let wtns = ligero_commit(&poly, log_n - initial_k, initial_k, rate, &ntt);
    let initial_root = wtns.root();

    let label = b"ligtest";
    let mut pch = ProverState::new(label, &[]);
    let proof = recursive_prover_with_basis(&pc, poly.clone(), b.clone(), target, &wtns.mat, &wtns.tree, &mut pch);

    let zc = z.clone();
    let eval_b_residual = move |ris: &[F128], yr_log_n: usize| -> Vec<F128> {
        let mut point = ris.to_vec();
        point.resize(ris.len() + yr_log_n, F128::ZERO);
        (0..(1usize << yr_log_n))
            .map(|y| {
                for j in 0..yr_log_n {
                    point[ris.len() + j] = if (y >> j) & 1 == 1 { F128::ONE } else { F128::ZERO };
                }
                eq_eval(&zc, &point)
            })
            .collect()
    };
    let mut vch = ProverState::new(label, &[]);
    let ok = recursive_verifier_with_basis_succinct(&vc, &proof, log_n, target, &initial_root, eval_b_residual, &mut vch);
    assert!(ok, "native ligerito verifier accepts the honest proof");

    eprintln!("=== tiny ligerito proof shapes ===");
    eprintln!("sumcheck_transcript.len = {}", proof.sumcheck_transcript.len());
    let sh = |rows: &[Vec<F128>]| (rows.len(), rows.first().map(|r| r.len()).unwrap_or(0));
    eprintln!("initial_proof.opened_rows = {:?}, merkle_proof.len = {}", sh(&proof.initial_proof.opened_rows), proof.initial_proof.merkle_proof.len());
    eprintln!("recursive_roots.len = {}", proof.recursive_roots.len());
    eprintln!("final_proof.yr.len = {}", proof.final_proof.yr.len());
    eprintln!("final_proof.opened_rows = {:?}, merkle_proof.len = {}", sh(&proof.final_proof.opened_rows), proof.final_proof.merkle_proof.len());
}

// ---- Gadget 10: ring-switch claim check (φ₈ F₈-Lagrange, runtime) ----
//
// The first stage of the real Ligerito opening (`ring_switch::verify_succinct`):
// it rebuilds the 128 claim weights from the univariate-skip coord `z_skip` and
// the 7th prefix bit `x_outer_0` and checks `Σ weights[i]·s_hat_v[i] == claim`.
// `weights[i] = λ_{i&63}(z_skip) · eq(x_outer_0, i>>6)`, where λ_j(z) =
// (∏_{l≠j}(z + s_l))·ID_j is the F₈-Lagrange basis over the φ₈-embedded nodes
// `s_l = PHI_8_TABLE[l]` (constants) with `ID_j = (∏_{l≠j}(s_j+s_l))^{-1}`
// (constants). With `z_skip`/`x_outer_0` HINTED at runtime, this is genuine
// runtime F₈-Lagrange in-circuit — one of the opening's hard sub-problems. The
// 64 numerators `∏_{l≠j}(z+s_l)` are formed in O(64) via prefix/suffix products.

/// Generate the claim-check program. `sj[l]` = φ₈ node l, `id[j]` = the constant
/// inverse-denominator; `claim` is the value flock's `claim_check` returns.
fn claim_check_source(sj: &[F128], id: &[F128], claim: F128) -> String {
    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    for (j, v) in sj.iter().enumerate() {
        s.push_str(&format!("SJ_{j} = {}\n", u(*v)));
    }
    for (j, v) in id.iter().enumerate() {
        s.push_str(&format!("ID_{j} = {}\n", u(*v)));
    }
    s.push_str(&format!("CLAIM = {}\n\n", u(claim)));
    s.push_str("def main():\n");
    line(&mut s, "zin = StackBuf(1)".into());
    line(&mut s, "hint_witness(zin, \"z_skip\")".into());
    line(&mut s, "zskip = zin[0]".into());
    line(&mut s, "xin = StackBuf(1)".into());
    line(&mut s, "hint_witness(xin, \"x_outer0\")".into());
    line(&mut s, "x0 = xin[0]".into());
    line(&mut s, "shv = HeapBuf(128)".into());
    line(&mut s, "hint_witness(shv[0:128], \"s_hat_v\")".into());
    // t_l = z_skip + s_l  (64 terms)
    for l in 0..64 {
        line(&mut s, format!("t{l} = zskip + SJ_{l}"));
    }
    // prefix pre_j = ∏_{l<j} t_l  (pre_0 = 1)
    line(&mut s, "pre0 = GEN ** 0".into());
    for j in 1..64 {
        line(&mut s, format!("pre{j} = pre{} * t{}", j - 1, j - 1));
    }
    // suffix suf_j = ∏_{l>j} t_l  (suf_63 = 1)
    line(&mut s, "suf63 = GEN ** 0".into());
    for j in (0..63).rev() {
        line(&mut s, format!("suf{j} = suf{} * t{}", j + 1, j + 1));
    }
    // λ_j = pre_j · suf_j · ID_j
    for j in 0..64 {
        line(&mut s, format!("lam{j} = pre{j} * suf{j} * ID_{j}"));
    }
    // lo_sum = Σ_{i<64} λ_i·shv[i] ; hi_sum = Σ_{i<64} λ_i·shv[64+i]
    line(&mut s, "lo0 = lam0 * shv[GEN ** 0]".into());
    for i in 1..64 {
        line(&mut s, format!("lo{i} = lo{} + lam{i} * shv[GEN ** {i}]", i - 1));
    }
    line(&mut s, "hi0 = lam0 * shv[GEN ** 64]".into());
    for i in 1..64 {
        line(&mut s, format!("hi{i} = hi{} + lam{i} * shv[GEN ** {}]", i - 1, 64 + i));
    }
    // claim = eq(x0,0)·lo_sum + eq(x0,1)·hi_sum = (1+x0)·lo_sum + x0·hi_sum
    line(&mut s, "eqlo = GEN ** 0 + x0".into());
    line(&mut s, "acc = eqlo * lo63 + x0 * hi63".into());
    line(&mut s, "assert acc == CLAIM".into());
    line(&mut s, "return".into());
    s
}

#[test]
fn ring_switch_claim_check() {
    use flare::field::PHI_8_TABLE;
    use flare::pcs::ring_switch::{build_claim_weights, claim_check};

    let z_skip = F128::new(0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321);
    let x0 = F128::new(0x0f0f_0f0f_1111_2222, 0x3333_4444_5555_6666);
    let s_hat_v: Vec<F128> = (0..128u64)
        .map(|i| F128::new(0xABCD_0000 ^ i.wrapping_mul(0x9E37_79B9), 0x55 ^ (i << 40)))
        .collect();

    // Reference weights + claim from flock itself.
    let weights = build_claim_weights(z_skip, x0);
    let claim = claim_check(&weights, &s_hat_v);

    // φ₈ nodes and inverse-denominators (compile-time constants for the guest).
    let sj: Vec<F128> = (0..64).map(|j| PHI_8_TABLE[j]).collect();
    let id: Vec<F128> = (0..64)
        .map(|j| {
            let mut den = F128::ONE;
            for l in 0..64 {
                if l != j {
                    den *= sj[j] + sj[l];
                }
            }
            den.inv()
        })
        .collect();

    let src = claim_check_source(&sj, &id, claim);
    let mut program = compile(&parse(&src).expect("parse claim_check"));
    program.set_witness("z_skip", vec![vec![z_skip]]);
    program.set_witness("x_outer0", vec![vec![x0]]);
    program.set_witness("s_hat_v", vec![s_hat_v]);
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("ring-switch claim check verifies");
}

// ---- Gadget 11: ring-switch tensor transpose + sumcheck_claim ----
//
// The second half of `ring_switch::verify_succinct`: `s_hat_u =
// tensor_algebra_transpose(s_hat_v)` (bit i of s_hat_u[b] = bit b of s_hat_v[i]),
// then `sumcheck_claim = Σ_b s_hat_u[b]·eq_r_dprime[b]`. Reordering,
// `sumcheck_claim = Σ_i x^i·(Σ_b bit_b(s_hat_v[i])·eq[b])`, so per row i the guest
// hints the 128 bits of s_hat_v[i], boolean-checks them, reconstructs
// `Σ_b bit_b·GEN^b == s_hat_v[i]` (which pins the bits), and folds `Σ_b bit_b·eq[b]`.
// The inner b-loop lives in a helper function (compiled once, called 128×), so the
// ~80k-op transpose is a few hundred instructions of bytecode, not a flat unroll.

#[test]
fn ring_switch_transpose() {
    use flare::pcs::ring_switch::{inner_product, tensor_algebra_transpose};

    let s_hat_v: Vec<F128> = (0..128u64)
        .map(|i| F128::new(0x1357_9BDF_0000 ^ i.wrapping_mul(0x9E37_79B9), 0x2468_ACE0 ^ (i << 41)))
        .collect();
    let eq: Vec<F128> = (0..128u64)
        .map(|b| F128::new(0xF00D_0000 ^ b.wrapping_mul(0x100_0001), 0xBA11 ^ (b << 33)))
        .collect();
    let sumcheck_claim = inner_product(&tensor_algebra_transpose(&s_hat_v), &eq);

    // Flat bit matrix B[i*128 + b] = bit_b(s_hat_v[i]).
    let mut bits = Vec::with_capacity(128 * 128);
    for v in &s_hat_v {
        for b in 0..128 {
            let bit = if b < 64 { (v.lo >> b) & 1 } else { (v.hi >> (b - 64)) & 1 };
            bits.push(F128::new(bit, 0));
        }
    }

    let src = format!(
        "from snark_lib import *\n\
         SC = {}\n\
         \n\
         def main():\n\
         \x20   shv = HeapBuf(128)\n\
         \x20   hint_witness(shv[0:128], \"s_hat_v\")\n\
         \x20   eq = HeapBuf(128)\n\
         \x20   hint_witness(eq[0:128], \"eq\")\n\
         \x20   bits = HeapBuf(16384)\n\
         \x20   hint_witness(bits[0:16384], \"bits\")\n\
         \x20   brow = bits\n\
         \x20   srow = shv\n\
         \x20   wi = GEN ** 0\n\
         \x20   acc = 0\n\
         \x20   for i in unroll(0, 128):\n\
         \x20       inr, rec = process_row(brow, eq)\n\
         \x20       chk = srow[1]\n\
         \x20       assert rec == chk\n\
         \x20       acc = acc + wi * inr\n\
         \x20       brow = brow * (GEN ** 128)\n\
         \x20       srow = srow * GEN\n\
         \x20       wi = wi * GEN\n\
         \x20   assert acc == SC\n\
         \x20   return\n\
         \n\
         def process_row(brow, eq):\n\
         \x20   cb = brow\n\
         \x20   ep = eq\n\
         \x20   wb = GEN ** 0\n\
         \x20   recon = 0\n\
         \x20   inner = 0\n\
         \x20   for b in unroll(0, 128):\n\
         \x20       bb = cb[1]\n\
         \x20       bsq = bb * bb\n\
         \x20       assert bsq == bb\n\
         \x20       recon = recon + bb * wb\n\
         \x20       inner = inner + bb * ep[1]\n\
         \x20       cb = cb * GEN\n\
         \x20       ep = ep * GEN\n\
         \x20       wb = wb * GEN\n\
         \x20   return inner, recon\n",
        u(sumcheck_claim)
    );

    let mut program = compile(&parse(&src).expect("parse transpose"));
    program.set_witness("s_hat_v", vec![s_hat_v]);
    program.set_witness("eq", vec![eq]);
    program.set_witness("bits", vec![bits]);
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("ring-switch transpose verifies");
}

// ---- Gadget 12: the COMPLETE ring_switch::verify_succinct (opening stage 1) ----
//
// Assembles the validated pieces into a full port of `ring_switch::verify_succinct`
// and checks it end-to-end against native flock: seed the sponge, absorb the
// protocol label, observe the 128 s_hat_v, sample r'' (7), build eq(r''), run the
// claim check (Σ weights·s_hat_v == claim, weights precomputed since z_skip is a
// public statement input), then the transpose fold (Σ_i x^i·Σ_b bit_b(s_hat_v[i])
// ·eq[b]) and assert it equals native's sumcheck_claim. A complete, real Ligerito-
// opening sub-protocol verified in-circuit.

fn verify_succinct_source(seed: [F128; 2], lbl0: F128, lbl1: F128, weights: &[F128], claim: F128, sc: F128) -> String {
    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    s.push_str(&format!("SEED0 = {}\n", u(seed[0])));
    s.push_str(&format!("SEED1 = {}\n", u(seed[1])));
    s.push_str(&format!("LBL0 = {}\n", u(lbl0)));
    s.push_str(&format!("LBL1 = {}\n", u(lbl1)));
    for (i, w) in weights.iter().enumerate() {
        s.push_str(&format!("W{i} = {}\n", u(*w)));
    }
    s.push_str(&format!("CLAIM = {}\n", u(claim)));
    s.push_str(&format!("SC = {}\n\n", u(sc)));

    s.push_str("def main():\n");
    let mut n = 0usize;
    line(&mut s, "shv = HeapBuf(128)".into());
    line(&mut s, "hint_witness(shv[0:128], \"s_hat_v\")".into());
    line(&mut s, "bits = HeapBuf(16384)".into());
    line(&mut s, "hint_witness(bits[0:16384], \"bits\")".into());
    line(&mut s, "cv0 = SEED0".into());
    line(&mut s, "cv1 = SEED1".into());
    // observe_label("flock-ring-switch-v0") = absorb_bytes: len frame (20) + 2 words.
    let emit_absorb = |s: &mut String, n: &mut usize, w: &str, tag: u32| {
        let k = *n;
        *n += 1;
        line(s, format!("ab{k} = StackBuf(2)"));
        line(s, format!("ab{k}[0] = {w}"));
        line(s, format!("ab{k}[1] = {tag}"));
        line(s, format!("bc{k} = StackBuf(2)"));
        line(s, format!("bc{k}[0] = cv0"));
        line(s, format!("bc{k}[1] = cv1"));
        line(s, format!("bo{k} = StackBuf(2)"));
        line(s, format!("blake3(bc{k}, ab{k}, bo{k})"));
        line(s, "cv0 = bo".to_string() + &k.to_string() + "[0]");
        line(s, "cv1 = bo".to_string() + &k.to_string() + "[1]");
    };
    emit_absorb(&mut s, &mut n, "20", 3); // DS_LEN
    emit_absorb(&mut s, &mut n, "LBL0", 2); // DS_BYTE
    emit_absorb(&mut s, &mut n, "LBL1", 2);
    // observe the 128 s_hat_v (a helper compiled once).
    line(&mut s, "cv0, cv1 = observe_all(cv0, cv1, shv)".into());
    // sample r'' = 7 challenges.
    for k in 0..7 {
        emit_sample(&mut s, &mut n, &format!("r{k}"));
    }
    // build_eq(r''): eqb[b] = ∏_k (bit_k(b) ? r_k : 1+r_k).
    for k in 0..7 {
        line(&mut s, format!("om{k} = GEN ** 0 + r{k}"));
    }
    line(&mut s, "eqb = HeapBuf(128)".into());
    for b in 0..128usize {
        let factors: Vec<String> = (0..7)
            .map(|k| if (b >> k) & 1 == 1 { format!("r{k}") } else { format!("om{k}") })
            .collect();
        line(&mut s, format!("eqb[GEN ** {b}] = {}", factors.join(" * ")));
    }
    // claim check: Σ_i weights[i]·s_hat_v[i] == claim.
    line(&mut s, "cs0 = W0 * shv[GEN ** 0]".into());
    for i in 1..128 {
        line(&mut s, format!("cs{i} = cs{} + W{i} * shv[GEN ** {i}]", i - 1));
    }
    line(&mut s, "assert cs127 == CLAIM".into());
    // transpose fold: acc = Σ_i GEN^i · (Σ_b bit_b(s_hat_v[i])·eq[b]) == sumcheck_claim.
    line(&mut s, "brow = bits".into());
    line(&mut s, "srow = shv".into());
    line(&mut s, "wi = GEN ** 0".into());
    line(&mut s, "acc = 0".into());
    line(&mut s, "for i in unroll(0, 128):".into());
    s.push_str("        inr, rec = process_row(brow, eqb)\n");
    s.push_str("        chk = srow[1]\n");
    s.push_str("        assert rec == chk\n");
    s.push_str("        acc = acc + wi * inr\n");
    s.push_str("        brow = brow * (GEN ** 128)\n");
    s.push_str("        srow = srow * GEN\n");
    s.push_str("        wi = wi * GEN\n");
    line(&mut s, "assert acc == SC".into());
    line(&mut s, "return".into());
    // helper: observe 128 values, threading the chaining value; returns it.
    s.push_str("\ndef observe_all(c0, c1, ptr):\n");
    s.push_str("    sp = ptr\n");
    s.push_str("    for b in unroll(0, 128):\n");
    s.push_str("        pk = StackBuf(2)\n");
    s.push_str("        pk[0] = c0\n");
    s.push_str("        pk[1] = c1\n");
    s.push_str("        ip = StackBuf(2)\n");
    s.push_str("        ip[0] = sp[1]\n");
    s.push_str("        ip[1] = 1\n");
    s.push_str("        op = StackBuf(2)\n");
    s.push_str("        blake3(pk, ip, op)\n");
    s.push_str("        c0 = op[0]\n");
    s.push_str("        c1 = op[1]\n");
    s.push_str("        sp = sp * GEN\n");
    s.push_str("    return c0, c1\n");
    // helper: fold one row's 128 bits (boolean + reconstruct + inner product).
    s.push_str("\ndef process_row(brow, eqb):\n");
    s.push_str("    cb = brow\n");
    s.push_str("    ep = eqb\n");
    s.push_str("    wb = GEN ** 0\n");
    s.push_str("    recon = 0\n");
    s.push_str("    inner = 0\n");
    s.push_str("    for b in unroll(0, 128):\n");
    s.push_str("        bb = cb[1]\n");
    s.push_str("        bsq = bb * bb\n");
    s.push_str("        assert bsq == bb\n");
    s.push_str("        recon = recon + bb * wb\n");
    s.push_str("        inner = inner + bb * ep[1]\n");
    s.push_str("        cb = cb * GEN\n");
    s.push_str("        ep = ep * GEN\n");
    s.push_str("        wb = wb * GEN\n");
    s.push_str("    return inner, recon\n");
    s
}

#[test]
fn ring_switch_verify_succinct_full() {
    use leanvm_b::transcript::ProverState;
    use flare::field::PHI_8_TABLE;
    use flare::pcs::ring_switch::{RingSwitchProof, build_claim_weights, claim_check, verify_succinct};
    let _ = PHI_8_TABLE; // (weights come from build_claim_weights)

    let z_skip = F128::new(0x9abc_def0_1234_5678, 0x1122_3344_5566_7788);
    let x_outer = vec![F128::new(0xdead_beef_cafe_babe, 0x0bad_f00d_1337_c0de)];
    let s_hat_v: Vec<F128> = (0..128u64)
        .map(|i| F128::new(0x0246_8ACE ^ i.wrapping_mul(0x9E37_79B9), 0x1357 ^ (i << 39)))
        .collect();
    let weights = build_claim_weights(z_skip, x_outer[0]);
    let claim = claim_check(&weights, &s_hat_v);
    let proof = RingSwitchProof { s_hat_v: s_hat_v.clone() };

    // Native verify_succinct with a leanVM-b ProverState challenger (the
    // compress-sponge the guest replays), seeded with an empty statement.
    let label = b"rstest";
    let mut ch = ProverState::new(label, &[]);
    let out = verify_succinct(claim, z_skip, &x_outer, &proof, &mut ch).expect("native verify_succinct");
    let seed = fs_ref::seed_cv(label, &[]);

    // Protocol label "flock-ring-switch-v0" (20 bytes) as two absorbed words.
    let lbl = b"flock-ring-switch-v0";
    let word = |o: usize| {
        let mut buf = [0u8; 16];
        let end = (lbl.len() - o).min(16);
        buf[..end].copy_from_slice(&lbl[o..o + end]);
        F128::new(
            u64::from_le_bytes(buf[..8].try_into().unwrap()),
            u64::from_le_bytes(buf[8..].try_into().unwrap()),
        )
    };
    let (lbl0, lbl1) = (word(0), word(16));

    // Bit matrix B[i*128+b] = bit_b(s_hat_v[i]).
    let mut bits = Vec::with_capacity(128 * 128);
    for v in &s_hat_v {
        for b in 0..128 {
            let bit = if b < 64 { (v.lo >> b) & 1 } else { (v.hi >> (b - 64)) & 1 };
            bits.push(F128::new(bit, 0));
        }
    }

    let src = verify_succinct_source(seed, lbl0, lbl1, &weights, claim, out.sumcheck_claim);
    let mut program = compile(&parse(&src).expect("parse verify_succinct"));
    program.set_witness("s_hat_v", vec![s_hat_v]);
    program.set_witness("bits", vec![bits]);
    let pi = [F128::ZERO, F128::ZERO];
    let (gproof, _) = prove(&program, pi);
    verify(&program, &pi, &gproof).expect("full verify_succinct verifies");
}

// ---- Gadget 9: the Ligerito RoundQuad sumcheck fold ----
//
// The Ligerito opening runs one global sumcheck whose round message is
// `{u_0, u_2}` (2 evals) and whose running quadratic `u(X)=c+bX+aX²` is rebuilt
// each round as `c=u_0, b=t_r+u_2, a=u_2` — a choice that bakes the consistency
// `u(0)+u(1)=t_r` in (so no separate check), advancing `t_r ← u(ri)` per fold.
// This gadget replays that fold: read msg0 → build quad → per fold {sample ri;
// t_r=eval(ri); read next msg; rebuild quad}, and pins the final `t_r`.

fn roundquad_source(k: usize, seed: [F128; 2], target: F128, n_stream: usize) -> String {
    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    s.push_str(&format!("SEED0 = {}\n", u(seed[0])));
    s.push_str(&format!("SEED1 = {}\n", u(seed[1])));
    s.push_str(&format!("TARGET = {}\n", u(target)));
    s.push_str(&format!("N = {n_stream}\n\n"));
    s.push_str("def main():\n");
    let mut n = 0usize;
    line(&mut s, "stream = HeapBuf(N)".into());
    line(&mut s, "hint_witness(stream[0:N], \"stream\")".into());
    line(&mut s, "cv0 = SEED0".into());
    line(&mut s, "cv1 = SEED1".into());
    line(&mut s, "sp = stream".into());
    // msg0 → initial quad; t_r = target.
    emit_read(&mut s, &mut n, "u0i");
    emit_read(&mut s, &mut n, "u2i");
    line(&mut s, "qc = u0i".into());
    line(&mut s, "qb = TARGET + u2i".into());
    line(&mut s, "qa = u2i".into());
    line(&mut s, "tr = TARGET".into());
    for j in 0..k {
        let ri = format!("ri{j}");
        emit_sample(&mut s, &mut n, &ri);
        // t_r = c + ri·b + ri²·a
        line(&mut s, format!("r2_{j} = {ri} * {ri}"));
        line(&mut s, format!("tr = qc + {ri} * qb + r2_{j} * qa"));
        // read next message, rebuild quad with the new t_r.
        emit_read(&mut s, &mut n, &format!("u0_{j}"));
        emit_read(&mut s, &mut n, &format!("u2_{j}"));
        line(&mut s, format!("qc = u0_{j}"));
        line(&mut s, format!("qb = tr + u2_{j}"));
        line(&mut s, format!("qa = u2_{j}"));
    }
    // Pin the final t_r via the public input.
    line(&mut s, "pp = GEN ** 0".into());
    line(&mut s, "pp[1] = tr".into());
    line(&mut s, "return".into());
    s
}

#[test]
fn roundquad_sumcheck() {
    use leanvm_b::vmhash::compress;
    let ds_scalar = F128::new(1, 0);
    let ds_squeeze = F128::new(4, 0);
    let obs = |cv: &mut [F128; 2], x: F128| *cv = compress(*cv, [x, ds_scalar]);

    for k in [1usize, 3, 6] {
        let seed = fs_ref::seed_cv(b"rq", &[]);
        let target = F128::new(0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321);
        // K+1 arbitrary round messages (u_0, u_2).
        let msgs: Vec<(F128, F128)> = (0..=k as u64)
            .map(|j| {
                (
                    F128::new(0xA1_00 ^ j.wrapping_mul(0x9E37), 0xB2_00 ^ (j << 20)),
                    F128::new(0xC3_00 ^ j.wrapping_mul(0x7F4A), 0xD4_00 ^ (j << 24)),
                )
            })
            .collect();
        let stream: Vec<F128> = msgs.iter().flat_map(|&(a, b)| [a, b]).collect();

        // Reference t_r evolution.
        let mut cv = seed;
        obs(&mut cv, msgs[0].0);
        obs(&mut cv, msgs[0].1);
        let (mut qc, mut qb, mut qa) = (msgs[0].0, target + msgs[0].1, msgs[0].1);
        let mut tr = target;
        for j in 0..k {
            let ri = {
                let o = compress(cv, [F128::ZERO, ds_squeeze]);
                cv = o;
                o[0]
            };
            tr = qc + ri * qb + ri * ri * qa;
            obs(&mut cv, msgs[j + 1].0);
            obs(&mut cv, msgs[j + 1].1);
            qc = msgs[j + 1].0;
            qb = tr + msgs[j + 1].1;
            qa = msgs[j + 1].1;
        }
        let tr_final = tr;

        let src = roundquad_source(k, seed, target, stream.len());
        let mut program = compile(&parse(&src).unwrap_or_else(|e| panic!("k={k}: parse: {e}")));
        program.set_witness("stream", vec![stream]);
        let pi = [tr_final, F128::ZERO];
        let (proof, _) = prove(&program, pi);
        verify(&program, &pi, &proof).unwrap_or_else(|e| panic!("k={k}: verify: {e:?}"));
    }
}

/// Gadget 13: **squeeze in a runtime loop** — the query-phase sampling mechanic.
/// The Ligerito core's `sample_distinct_queries` draws a runtime number of
/// challenges (`sample_f128`) to derive query indices. This validates squeezing
/// inside a `mul_range` whose bound is a runtime g-power, threading BOTH the
/// sponge chaining value AND an accumulator through write-once HeapBufs: step j
/// squeezes `cv_{j+1} = compress(cv_j, [0, DS_SQUEEZE])` (challenge = `cv_{j+1}[0]`)
/// and folds it into a running XOR. The final accumulator is read back at the
/// runtime address `nbound`, and matches a native squeeze loop.
#[test]
fn runtime_sample_loop() {
    use leanvm_b::vmhash::compress;
    let ds_squeeze = F128::new(4, 0);

    let n = 6usize;
    let seed = fs_ref::seed_cv(b"qtest", &[]);
    let mut cv = seed;
    let mut acc = F128::ZERO;
    for _ in 0..n {
        let o = compress(cv, [F128::ZERO, ds_squeeze]);
        cv = o;
        acc += o[0]; // fold the sampled challenge
    }
    let nbound = leanvm_b::field::g_pow(n);

    let src = format!(
        "from snark_lib import *\n\
         SEED0 = {}\n\
         SEED1 = {}\n\
         ACC = {}\n\
         \n\
         def main():\n\
         \x20   nb = StackBuf(1)\n\
         \x20   hint_witness(nb, \"nbound\")\n\
         \x20   nbound = nb[0]\n\
         \x20   assert log(nbound) < 16\n\
         \x20   cvbuf = HeapBuf(nbound * nbound * GEN ** 2)\n\
         \x20   cvbuf[1] = SEED0\n\
         \x20   cvbuf[GEN] = SEED1\n\
         \x20   accbuf = HeapBuf(nbound * GEN)\n\
         \x20   accbuf[1] = 0\n\
         \x20   for x in mul_range(1, nbound):\n\
         \x20       b = x * x\n\
         \x20       sqin = StackBuf(2)\n\
         \x20       sqin[0] = 0\n\
         \x20       sqin[1] = 4\n\
         \x20       blake3(cvbuf[b : b + 2], sqin, cvbuf[b * GEN ** 2 : b * GEN ** 2 + 2])\n\
         \x20       accbuf[x * GEN] = accbuf[x] + cvbuf[b * GEN ** 2]\n\
         \x20   fin = accbuf[nbound]\n\
         \x20   assert fin == ACC\n\
         \x20   return\n",
        u(seed[0]),
        u(seed[1]),
        u(acc),
    );

    let mut program = compile(&parse(&src).expect("parse runtime-sample"));
    program.set_witness("nbound", vec![vec![nbound]]);
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("runtime-sample loop verifies");
}

// ---- Gadget 7: the per-table zerocheck verifier (constraints.rs replay) ----
//
// A verify() sub-protocol: the same degree-2 sumcheck core as GKR, but it samples
// the batching scalar `eta` and the zerocheck point `r` up front, starts the
// running claim at 0, and closes with `claim == eq_acc · c_eval(eta, evals)`.
// Here the test constraint is `c(a,b) = a + b` (proves column a == column b on
// every row), so `c_eval = ev0 + ev1`. The 6-table verifier will codegen a
// per-table `c_eval` (the AIR-evaluator codegen, mirroring the reference).

/// Emit the Lagrange interpolation of a degree-2 round univariate sent at nodes
/// {0,1,g} as evals `(m0,m1,m2)`, evaluated at `rk`, into result var `dst`.
/// Requires globals `INV0,INV1,INV2` (the inverse-denominators).
fn emit_lagrange(s: &mut String, tag: &str, m0: &str, m1: &str, m2: &str, rk: &str, dst: &str) {
    line(s, format!("pa{tag} = {rk} + 1"));
    line(s, format!("pb{tag} = {rk} + GEN"));
    line(s, format!("q0{tag} = {m0} * pa{tag} * pb{tag} * INV0"));
    line(s, format!("q1{tag} = {m1} * {rk} * pb{tag} * INV1"));
    line(s, format!("q2{tag} = {m2} * {rk} * pa{tag} * INV2"));
    line(s, format!("{dst} = q0{tag} + q1{tag} + q2{tag}"));
}

fn zerocheck_verify_source(tau: usize, seed: [F128; 2], n_stream: usize) -> String {
    let g = F128::generator();
    let (inv0, inv1, inv2) = (g.inv(), (F128::ONE + g).inv(), (g * (F128::ONE + g)).inv());

    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    s.push_str(&format!("SEED0 = {}\n", u(seed[0])));
    s.push_str(&format!("SEED1 = {}\n", u(seed[1])));
    s.push_str(&format!("INV0 = {}\n", u(inv0)));
    s.push_str(&format!("INV1 = {}\n", u(inv1)));
    s.push_str(&format!("INV2 = {}\n", u(inv2)));
    s.push_str(&format!("N = {n_stream}\n\n"));
    s.push_str("def main():\n");

    let mut n = 0usize;
    line(&mut s, "stream = HeapBuf(N)".into());
    line(&mut s, "hint_witness(stream[0:N], \"stream\")".into());
    line(&mut s, "cv0 = SEED0".into());
    line(&mut s, "cv1 = SEED1".into());
    line(&mut s, "sp = stream".into());
    emit_sample(&mut s, &mut n, "eta"); // batching scalar (unused by c=a+b, but keeps sponge in sync)
    for j in 0..tau {
        emit_sample(&mut s, &mut n, &format!("rr{j}")); // the zerocheck point r
    }
    line(&mut s, "claim = GEN ** 0 + GEN ** 0".into()); // an unambiguous field zero
    let mut eqacc = "ea0".to_string();
    line(&mut s, format!("{eqacc} = GEN ** 0"));
    for round in 0..tau {
        let (m0, m1, m2) = (format!("z{round}0"), format!("z{round}1"), format!("z{round}2"));
        emit_read(&mut s, &mut n, &m0);
        emit_read(&mut s, &mut n, &m1);
        emit_read(&mut s, &mut n, &m2);
        let rj = format!("rr{round}");
        line(&mut s, format!("or{round} = 1 + {rj}"));
        line(&mut s, format!("tm{round} = or{round} * {m0} + {rj} * {m1}"));
        line(&mut s, format!("ck{round} = {eqacc} * tm{round}"));
        line(&mut s, format!("assert ck{round} == claim"));
        let rk = format!("rk{round}");
        emit_sample(&mut s, &mut n, &rk);
        let neweq = format!("ea{}", round + 1);
        line(&mut s, format!("os{round} = 1 + {rj} + {rk}"));
        line(&mut s, format!("{neweq} = {eqacc} * os{round}"));
        eqacc = neweq;
        emit_lagrange(&mut s, &format!("_{round}"), &m0, &m1, &m2, &rk, &format!("lg{round}"));
        line(&mut s, format!("claim = {eqacc} * lg{round}"));
    }
    // Read the two column evals; final check claim == eq_acc·(ev0+ev1).
    emit_read(&mut s, &mut n, "ev0");
    emit_read(&mut s, &mut n, "ev1");
    line(&mut s, "cev = ev0 + ev1".into());
    line(&mut s, format!("fin = {eqacc} * cev"));
    line(&mut s, "assert claim == fin".into());
    line(&mut s, "return".into());
    s
}

#[test]
fn zerocheck_verify() {
    use leanvm_b::constraints;
    use leanvm_b::transcript::{ProverState, VerifierState};

    for tau in [1usize, 2, 3] {
        let col_len = 1usize << tau;
        // Two equal columns ⇒ constraint c = a + b vanishes on every row.
        let a: Vec<F128> = (0..col_len)
            .map(|i| F128::new(0x51_7c_c1_b7 ^ i as u64, 0x2f_2f ^ ((i as u64) << 12)))
            .collect();
        let cols = vec![a.clone(), a];
        let c_eval = |_eta: F128, vals: &[F128]| vals[0] + vals[1];

        let label = b"zctest";
        let mut ps = ProverState::new(label, &[]);
        let _ = constraints::prove(&cols, c_eval, &mut ps);
        let proof = ps.into_proof();
        // Sanity: the native verifier accepts.
        let mut vs = VerifierState::new(label, &proof, &[]);
        constraints::verify(tau, 2, c_eval, &mut vs).expect("ref zerocheck verify");

        let seed = fs_ref::seed_cv(label, &[]);
        let src = zerocheck_verify_source(tau, seed, proof.stream.len());
        let mut program = compile(&parse(&src).unwrap_or_else(|e| panic!("tau={tau}: parse: {e}")));
        program.set_witness("stream", vec![proof.stream.clone()]);
        let pi = [F128::ZERO, F128::ZERO];
        let (gproof, _) = prove(&program, pi);
        verify(&program, &pi, &gproof).unwrap_or_else(|e| panic!("tau={tau}: verify: {e:?}"));
    }
}

// ---- Gadget 6: single-path Merkle verification ----
//
// A Ligerito query opening proves a codeword column sits at a leaf of the commit
// Merkle tree. The leaf hash is the length-in-IV MD chain `vmhash::hash_slice`
// (proven equal to flock's `merkle::hash_leaf`); each internal node is
// `compress(left,right)` with sibling order chosen by the query-index bit
// (`idx&1`, LSB-first bottom-up). The guest hashes the leaf, then walks up: at
// each level it packs the running node, reads the sibling, and — branching on the
// (boolean-constrained) index bit — compresses `(node,sib)` or `(sib,node)`,
// asserting the final root. (The batched octopus multi-proof reuses this per
// query; shared-node handling is layered on at assembly time.)

/// Generate a zkDSL program verifying a depth-`h` Merkle path for a 2-cell leaf
/// (num_interleaved = 2, a single 32-byte leaf block), asserting the recomputed
/// root equals the constant `root`.
fn merkle_verify_source(h: usize, root: [F128; 2]) -> String {
    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    s.push_str(&format!("ROOT0 = {}\n", u(root[0])));
    s.push_str(&format!("ROOT1 = {}\n", u(root[1])));
    s.push_str(&format!("H = {h}\n\n"));
    s.push_str("def main():\n");
    line(&mut s, "leaf = HeapBuf(2)".into());
    line(&mut s, "hint_witness(leaf[0:2], \"leaf\")".into());
    line(&mut s, format!("path = HeapBuf({})", 2 * h));
    line(&mut s, format!("hint_witness(path[0:{}], \"path\")", 2 * h));
    line(&mut s, format!("bits = HeapBuf({h})"));
    line(&mut s, format!("hint_witness(bits[0:{h}], \"bits\")"));
    // Leaf hash: iv = (g^{32}, 0) (32 = 2 cells · 16 bytes), one compression.
    line(&mut s, "iv = StackBuf(2)".into());
    line(&mut s, "iv[0] = GEN ** 32".into());
    line(&mut s, "iv[1] = 0".into());
    line(&mut s, "lf = StackBuf(2)".into());
    line(&mut s, "lf[0] = leaf[1]".into());
    line(&mut s, "lf[1] = leaf[GEN]".into());
    line(&mut s, "lh = StackBuf(2)".into());
    line(&mut s, "blake3(iv, lf, lh)".into());
    line(&mut s, "node0 = lh[0]".into());
    line(&mut s, "node1 = lh[1]".into());
    for level in 0..h {
        line(&mut s, format!("bl{level} = bits[GEN ** {level}]"));
        line(&mut s, format!("bsq{level} = bl{level} * bl{level}"));
        line(&mut s, format!("assert bsq{level} == bl{level}")); // boolean
        line(&mut s, format!("nb{level} = StackBuf(2)"));
        line(&mut s, format!("nb{level}[0] = node0"));
        line(&mut s, format!("nb{level}[1] = node1"));
        line(&mut s, format!("sb{level} = StackBuf(2)"));
        line(&mut s, format!("sb{level}[0] = path[GEN ** {}]", 2 * level));
        line(&mut s, format!("sb{level}[1] = path[GEN ** {}]", 2 * level + 1));
        line(&mut s, format!("par{level} = StackBuf(2)"));
        line(&mut s, format!("if bl{level} == 0:"));
        s.push_str(&format!("        blake3(nb{level}, sb{level}, par{level})\n")); // node is left
        line(&mut s, "else:".into());
        s.push_str(&format!("        blake3(sb{level}, nb{level}, par{level})\n")); // node is right
        line(&mut s, format!("node0 = par{level}[0]"));
        line(&mut s, format!("node1 = par{level}[1]"));
    }
    line(&mut s, "assert node0 == ROOT0".into());
    line(&mut s, "assert node1 == ROOT1".into());
    line(&mut s, "return".into());
    s
}

#[test]
fn merkle_path_verify() {
    use leanvm_b::vmhash::{compress, hash_slice};

    for h in [1usize, 2, 3, 4] {
        let n_leaves = 1usize << h;
        let rows: Vec<[F128; 2]> = (0..n_leaves)
            .map(|i| {
                [
                    F128::new(0xdead_0000 ^ i as u64, 0xbeef_0000 ^ ((i as u64) << 8)),
                    F128::new(0xcafe_1234 ^ ((i as u64) << 3), 0xf00d_5678 ^ i as u64),
                ]
            })
            .collect();
        // Build the tree bottom-up.
        let leaf_hashes: Vec<[F128; 2]> = rows.iter().map(|r| hash_slice(&r[..])).collect();

        for q in 0..n_leaves {
            // Extract the sibling path and root for query q.
            let mut cur = leaf_hashes.clone();
            let mut idx = q;
            let mut path: Vec<[F128; 2]> = Vec::new();
            while cur.len() > 1 {
                path.push(cur[idx ^ 1]);
                cur = (0..cur.len() / 2).map(|j| compress(cur[2 * j], cur[2 * j + 1])).collect();
                idx >>= 1;
            }
            let root = cur[0];

            let src = merkle_verify_source(h, root);
            let mut program = compile(&parse(&src).unwrap_or_else(|e| panic!("h={h} q={q}: parse: {e}")));
            program.set_witness("leaf", vec![rows[q].to_vec()]);
            program.set_witness("path", vec![path.iter().flat_map(|p| p.to_vec()).collect()]);
            let bit_vals: Vec<F128> = (0..h).map(|l| F128::new(((q >> l) & 1) as u64, 0)).collect();
            program.set_witness("bits", vec![bit_vals]);

            let pi = [F128::ZERO, F128::ZERO];
            let (proof, _) = prove(&program, pi);
            verify(&program, &pi, &proof).unwrap_or_else(|e| panic!("h={h} q={q}: verify: {e:?}"));
        }
    }
}

/// Emit a full `gkr::verify_product` replay for `2^mu` leaves into an in-progress
/// `main()` body that has already set up the sponge (`cv0,cv1`) and stream cursor
/// (`sp`). All local names are `tag`-prefixed so several products can be verified
/// back-to-back over one shared transcript. Leaves `root{tag}` bound to the
/// product root; the internal asserts constitute the verification.
fn emit_gkr_verify_body(s: &mut String, n: &mut usize, mu: usize, tag: &str) {
    emit_read(s, n, &format!("root{tag}"));
    line(s, format!("clm{tag} = root{tag}"));
    line(s, format!("rbuf{tag} = HeapBuf({})", mu * mu));
    for p in 0..mu {
        let base = p * mu;
        let mut eqacc = format!("e{tag}_{p}_0");
        line(s, format!("{eqacc} = GEN ** 0"));
        for round in 0..p {
            let (m0, m1, m2) = (
                format!("g{tag}{p}_{round}_0"),
                format!("g{tag}{p}_{round}_1"),
                format!("g{tag}{p}_{round}_2"),
            );
            emit_read(s, n, &m0);
            emit_read(s, n, &m1);
            emit_read(s, n, &m2);
            let rj = format!("j{tag}{p}_{round}");
            line(s, format!("{rj} = rbuf{tag}[GEN ** {}]", (p - 1) * mu + round));
            line(s, format!("o{tag}{p}_{round} = 1 + {rj}"));
            line(s, format!("t{tag}{p}_{round} = o{tag}{p}_{round} * {m0} + {rj} * {m1}"));
            line(s, format!("k{tag}{p}_{round} = {eqacc} * t{tag}{p}_{round}"));
            line(s, format!("assert k{tag}{p}_{round} == clm{tag}"));
            let rk = format!("y{tag}{p}_{round}");
            emit_sample(s, n, &rk);
            line(s, format!("rbuf{tag}[GEN ** {}] = {rk}", base + round + 1));
            let neweq = format!("e{tag}_{p}_{}", round + 1);
            line(s, format!("s{tag}{p}_{round} = 1 + {rj} + {rk}"));
            line(s, format!("{neweq} = {eqacc} * s{tag}{p}_{round}"));
            eqacc = neweq;
            emit_lagrange(s, &format!("{tag}{p}_{round}"), &m0, &m1, &m2, &rk, &format!("L{tag}{p}_{round}"));
            line(s, format!("clm{tag} = {eqacc} * L{tag}{p}_{round}"));
        }
        let (e0, e1) = (format!("v{tag}{p}_0"), format!("v{tag}{p}_1"));
        emit_read(s, n, &e0);
        emit_read(s, n, &e1);
        line(s, format!("pe{tag}{p} = {e0} * {e1}"));
        line(s, format!("pv{tag}{p} = {eqacc} * pe{tag}{p}"));
        line(s, format!("assert clm{tag} == pv{tag}{p}"));
        let c = format!("c{tag}{p}");
        emit_sample(s, n, &c);
        line(s, format!("rbuf{tag}[GEN ** {base}] = {c}"));
        line(s, format!("dd{tag}{p} = {e0} + {e1}"));
        line(s, format!("clm{tag} = {e0} + {c} * dd{tag}{p}"));
    }
}

/// Grand-product **multiset-balance** verifier — the essence of leanVM-b's bus.
/// Verifies three GKR products (push/pull/count) over one shared transcript and
/// asserts `push_root == pull_root` (the two sides are the same multiset) and
/// `count_root != 0` (no read self-cancels). Demonstrates composing several
/// sumcheck sub-protocols + a cross-product relation in a single guest program.
fn balance_verify_source(mu: usize, seed: [F128; 2], n_stream: usize) -> String {
    let g = F128::generator();
    let (inv0, inv1, inv2) = (g.inv(), (F128::ONE + g).inv(), (g * (F128::ONE + g)).inv());
    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    s.push_str(&format!("SEED0 = {}\n", u(seed[0])));
    s.push_str(&format!("SEED1 = {}\n", u(seed[1])));
    s.push_str(&format!("INV0 = {}\n", u(inv0)));
    s.push_str(&format!("INV1 = {}\n", u(inv1)));
    s.push_str(&format!("INV2 = {}\n", u(inv2)));
    s.push_str(&format!("N = {n_stream}\n\n"));
    s.push_str("def main():\n");
    let mut n = 0usize;
    line(&mut s, "stream = HeapBuf(N)".into());
    line(&mut s, "hint_witness(stream[0:N], \"stream\")".into());
    line(&mut s, "cv0 = SEED0".into());
    line(&mut s, "cv1 = SEED1".into());
    line(&mut s, "sp = stream".into());
    emit_gkr_verify_body(&mut s, &mut n, mu, "P");
    emit_gkr_verify_body(&mut s, &mut n, mu, "Q");
    emit_gkr_verify_body(&mut s, &mut n, mu, "C");
    // Balance: the push and pull multisets coincide ⇒ equal grand products.
    line(&mut s, "assert rootP == rootQ".into());
    // No read self-cancels: count_root != 0, proven by exhibiting its inverse
    // (only 0 has none) — the idiomatic nonzero check (assert has no `!=`).
    line(&mut s, "cinv = StackBuf(1)".into());
    line(&mut s, "hint_witness(cinv, \"count_inv\")".into());
    line(&mut s, "cprod = rootC * cinv[0]".into());
    line(&mut s, "assert cprod == GEN ** 0".into());
    line(&mut s, "return".into());
    s
}

#[test]
fn balance_verify() {
    use leanvm_b::gkr;
    use leanvm_b::transcript::{ProverState, VerifierState};

    let mu = 3usize;
    let m = 1usize << mu;
    // push and pull are permutations of one another ⇒ identical grand product.
    let push: Vec<F128> = (0..m as u64).map(|i| F128::new(0x100 + i, 0x9 * i + 1)).collect();
    let mut pull = push.clone();
    pull.reverse(); // a permutation ⇒ same product
    let count: Vec<F128> = (0..m as u64).map(|i| F128::new(0x7 * i + 3, 0x5 + i)).collect();

    let label = b"bustest";
    let mut ps = ProverState::new(label, &[]);
    let _ = gkr::prove_product(push, &mut ps);
    let _ = gkr::prove_product(pull, &mut ps);
    let _ = gkr::prove_product(count, &mut ps);
    let proof = ps.into_proof();

    // Sanity: replay the three products natively (confirms the transcript shape).
    let mut vs = VerifierState::new(label, &proof, &[]);
    let (rp, _) = gkr::verify_product(mu, &mut vs).unwrap();
    let (rq, _) = gkr::verify_product(mu, &mut vs).unwrap();
    let (rc, _) = gkr::verify_product(mu, &mut vs).unwrap();
    assert_eq!(rp, rq, "permutation ⇒ equal product");
    assert_ne!(rc, F128::ZERO);

    let seed = fs_ref::seed_cv(label, &[]);
    let src = balance_verify_source(mu, seed, proof.stream.len());
    let mut program = compile(&parse(&src).expect("parse balance verifier"));
    program.set_witness("stream", vec![proof.stream.clone()]);
    program.set_witness("count_inv", vec![vec![rc.inv()]]);
    let pi = [F128::ZERO, F128::ZERO];
    let (gproof, _) = prove(&program, pi);
    verify(&program, &pi, &gproof).expect("balance verify replay verifies");
}

#[test]
fn gkr_product_verify() {
    use leanvm_b::gkr;
    use leanvm_b::transcript::{ProverState, VerifierState};

    // Exercise the emitter across sizes so the codegen is trusted for the
    // real verifier (μ = 1 has a single degenerate layer; μ = 5 has 10 rounds).
    for mu in [1usize, 2, 3, 5] {
        let leaves: Vec<F128> = (0..(1usize << mu))
            .map(|i| {
                F128::new(
                    0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 3) + 1,
                    0x1234_5678 ^ ((i as u64) << 20),
                )
            })
            .collect();

        let label = b"gkrtest";
        let mut ps = ProverState::new(label, &[]);
        let _ = gkr::prove_product(leaves, &mut ps);
        let proof = ps.into_proof();

        // Reference leaf-claim value from the native verifier.
        let mut vs = VerifierState::new(label, &proof, &[]);
        let (_root, leafclaim) = gkr::verify_product(mu, &mut vs).expect("ref verify_product");
        let leaf_val = leafclaim.value;

        let seed = fs_ref::seed_cv(label, &[]);
        let src = gkr_verify_source(mu, seed, leaf_val, proof.stream.len());

        let mut program = compile(&parse(&src).unwrap_or_else(|e| panic!("mu={mu}: parse: {e}")));
        program.set_witness("stream", vec![proof.stream.clone()]);
        let pi = [leaf_val, F128::ZERO];
        let (gproof, _) = prove(&program, pi);
        verify(&program, &pi, &gproof).unwrap_or_else(|e| panic!("mu={mu}: verify: {e:?}"));
    }
}
