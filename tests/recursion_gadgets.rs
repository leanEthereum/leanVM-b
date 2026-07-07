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
