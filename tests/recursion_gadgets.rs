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

    /// A stateful mirror of `src/transcript.rs`'s `Sponge`, so a test can replay
    /// the exact challenge sequence a `ProverState`-driven verifier produces (to
    /// extract the sampled query values that the guest must hint bits for).
    pub struct Sponge {
        pub cv: [F128; 2],
    }
    impl Sponge {
        pub fn new(label: &[u8], statement: &[F128]) -> Self {
            Self { cv: seed_cv(label, statement) }
        }
        pub fn observe(&mut self, x: F128) {
            self.cv = compress(self.cv, [x, DS_SCALAR]);
        }
        pub fn observe_bytes(&mut self, bytes: &[u8]) {
            self.cv = absorb_bytes(self.cv, bytes);
        }
        pub fn sample(&mut self) -> F128 {
            let out = compress(self.cv, [F128::ZERO, F128::new(4, 0)]); // DS_SQUEEZE
            self.cv = out;
            out[0]
        }
        pub fn absorb_nonce(&mut self, nonce: u64) {
            self.cv = compress(self.cv, [F128::new(nonce, 0), F128::new(5, 0)]); // DS_POW
        }
        /// Verifier PoW mirror (transcript.rs): base = compress(cv,[0,DS_POW]);
        /// for bits>0 check compress(base,[nonce,DS_POW]) has `bits` leading zero
        /// bits (LE byte order); then absorb the nonce. Returns the check result.
        pub fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
            let base = compress(self.cv, [F128::ZERO, F128::new(5, 0)]);
            let ok = if bits == 0 {
                nonce == 0
            } else {
                let h = compress(base, [F128::new(nonce, 0), F128::new(5, 0)]);
                leading_zero_bits(h, bits)
            };
            self.absorb_nonce(nonce);
            ok
        }
        /// sample_distinct_queries: sample until `count` distinct `v.lo % block_len`
        /// collected; returns (sorted distinct positions, the raw sampled values in
        /// order). block_len is a power of two.
        pub fn sample_distinct_queries(&mut self, block_len: usize, count: usize) -> (Vec<usize>, Vec<F128>) {
            use std::collections::HashSet;
            let mut seen = HashSet::new();
            let mut sorted = Vec::new();
            let mut raw = Vec::new();
            while sorted.len() < count {
                let v = self.sample();
                raw.push(v);
                let q = (v.lo as usize) % block_len;
                if seen.insert(q) {
                    sorted.push(q);
                }
            }
            sorted.sort_unstable();
            (sorted, raw)
        }
    }

    /// True iff `state_bytes(h)` has ≥ `bits` leading zero bits (mirrors
    /// transcript.rs `pow_bits_ok`): LE serialization, low `bits` bits of h[0].
    fn leading_zero_bits(h: [F128; 2], bits: u32) -> bool {
        let mut out = [0u8; 32];
        out[0..8].copy_from_slice(&h[0].lo.to_le_bytes());
        out[8..16].copy_from_slice(&h[0].hi.to_le_bytes());
        out[16..24].copy_from_slice(&h[1].lo.to_le_bytes());
        out[24..32].copy_from_slice(&h[1].hi.to_le_bytes());
        let full = (bits / 8) as usize;
        let extra = bits % 8;
        if out[..full].iter().any(|&b| b != 0) {
            return false;
        }
        extra == 0 || (out[full] >> (8 - extra)) == 0
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

/// Gadget 15: **fold-PoW leading-zero check** (the m33 config grinds fold
/// challenges). verify_pow computes `base = compress(cv,[0,DS_POW])`, then checks
/// `compress(base,[nonce,DS_POW])` has ≥ `bits` leading zero bits (LE byte order =
/// low `bits` coefficients of h[0]). The guest recomputes the two compressions,
/// decomposes h[0], and asserts its low `bits` bits are zero.
#[test]
fn fold_pow_check() {
    use leanvm_b::vmhash::compress;
    let ds_pow = F128::new(5, 0);
    let lz = |h: [F128; 2], bits: u32| {
        let mut o = [0u8; 32];
        o[0..8].copy_from_slice(&h[0].lo.to_le_bytes());
        o[8..16].copy_from_slice(&h[0].hi.to_le_bytes());
        let full = (bits / 8) as usize;
        let extra = bits % 8;
        o[..full].iter().all(|&b| b == 0) && (extra == 0 || (o[full] >> (8 - extra)) == 0)
    };
    let cv = fs_ref::seed_cv(b"powtest", &[F128::new(9, 9)]);
    let base = compress(cv, [F128::ZERO, ds_pow]);
    let bits = 12u32;
    let mut nonce = 0u64;
    while !lz(compress(base, [F128::new(nonce, 0), ds_pow]), bits) {
        nonce += 1;
    }
    let h = compress(base, [F128::new(nonce, 0), ds_pow]);

    // The zero-bit set of pow_bits_ok(bits): low `full` bytes (bits 0..8*full) +
    // the top `extra` bits of byte `full` (bits 8*full+8-extra .. 8*full+8).
    let full = (bits / 8) as usize;
    let extra = (bits % 8) as usize;
    let mut zero_bits: Vec<usize> = (0..8 * full).collect();
    if extra > 0 {
        zero_bits.extend(8 * full + 8 - extra..8 * full + 8);
    }
    let zero_asserts: String = zero_bits
        .iter()
        .map(|&i| format!("    zb{i} = hb[GEN ** {i}]\n    assert zb{i} == 0\n"))
        .collect();

    let src = format!(
        "from snark_lib import *\n\
         CV0 = {}\n\
         CV1 = {}\n\
         NONCE = {nonce}\n\
         \n\
         def main():\n\
         \x20   cvb = StackBuf(2)\n\
         \x20   cvb[0] = CV0\n\
         \x20   cvb[1] = CV1\n\
         \x20   zin = StackBuf(2)\n\
         \x20   zin[0] = 0\n\
         \x20   zin[1] = 5\n\
         \x20   base = StackBuf(2)\n\
         \x20   blake3(cvb, zin, base)\n\
         \x20   ni = StackBuf(2)\n\
         \x20   ni[0] = NONCE\n\
         \x20   ni[1] = 5\n\
         \x20   h = StackBuf(2)\n\
         \x20   blake3(base, ni, h)\n\
         \x20   hb = HeapBuf(128)\n\
         \x20   hint_witness(hb[0:128], \"hbits\")\n\
         \x20   h0 = h[0]\n\
         \x20   cb = hb\n\
         \x20   w = GEN ** 0\n\
         \x20   acc = 0\n\
         \x20   for i in unroll(0, 128):\n\
         \x20       b = cb[1]\n\
         \x20       sq = b * b\n\
         \x20       assert sq == b\n\
         \x20       acc = acc + b * w\n\
         \x20       cb = cb * GEN\n\
         \x20       w = w * GEN\n\
         \x20   assert acc == h0\n\
         {zero_asserts}\
         \x20   return\n",
        u(cv[0]),
        u(cv[1]),
    );
    let hbits: Vec<F128> = (0..128)
        .map(|i| {
            let bit = if i < 64 { (h[0].lo >> i) & 1 } else { (h[0].hi >> (i - 64)) & 1 };
            F128::new(bit, 0)
        })
        .collect();
    let mut program = compile(&parse(&src).expect("parse fold-pow"));
    program.set_witness("hbits", vec![hbits]);
    let pi = [F128::ZERO, F128::ZERO];
    let (proof, _) = prove(&program, pi);
    verify(&program, &pi, &proof).expect("fold-pow leading-zero check verifies");
}

/// A Ligerito config (the shape shared by prover + verifier). `r = recursive_ks.len()`.
#[derive(Clone)]
struct LigCfg {
    log_n: usize,
    initial_k: usize,
    log_inv_rates: Vec<usize>,
    recursive_ks: Vec<usize>,
    recursive_log_msg_cols: Vec<usize>,
    initial_log_msg_cols: usize,
    queries: Vec<usize>,
    fold_grinding_bits: Vec<usize>,
    yr_log_n: usize,
}
impl LigCfg {
    fn r(&self) -> usize {
        self.recursive_ks.len()
    }
    fn prover(&self) -> flare::pcs::ligerito::ProverConfig {
        flare::pcs::ligerito::ProverConfig {
            log_inv_rates: self.log_inv_rates.clone(),
            recursive_steps: self.r(),
            initial_log_msg_cols: self.initial_log_msg_cols,
            initial_log_num_interleaved: self.initial_k,
            initial_k: self.initial_k,
            recursive_log_msg_cols: self.recursive_log_msg_cols.clone(),
            recursive_ks: self.recursive_ks.clone(),
            queries: self.queries.clone(),
            grinding_bits: vec![0; self.r() + 1],
            fold_grinding_bits: self.fold_grinding_bits.clone(),
            ood_samples: vec![0; self.r() + 1],
        }
    }
    fn verifier(&self) -> flare::pcs::ligerito::VerifierConfig {
        flare::pcs::ligerito::VerifierConfig {
            log_inv_rates: self.log_inv_rates.clone(),
            recursive_steps: self.r(),
            initial_log_msg_cols: self.initial_log_msg_cols,
            initial_log_num_interleaved: self.initial_k,
            initial_k: self.initial_k,
            recursive_log_msg_cols: self.recursive_log_msg_cols.clone(),
            recursive_ks: self.recursive_ks.clone(),
            queries: self.queries.clone(),
            grinding_bits: vec![0; self.r() + 1],
            fold_grinding_bits: self.fold_grinding_bits.clone(),
            ood_samples: vec![0; self.r() + 1],
        }
    }
}

/// Per-level data extracted by the mirror.
struct MirLevel {
    sorted: Vec<usize>,  // distinct sorted query positions
    raw: Vec<F128>,      // raw sampled values (len = T ≥ N), for Merkle-bit extraction
    alpha: Vec<F128>,
    beta: F128,
}
struct MirOut {
    tr: F128,
    inner: F128,
    ris: Vec<F128>,
    ctx_lmc: Vec<usize>,       // log_msg_cols per level ctx (len r+1)
    ctx_ris_start: Vec<usize>, // ris_start per level ctx
    levels: Vec<MirLevel>,     // len r+1
}

/// Reusable, config-driven mirror of `recursive_verifier_with_basis_succinct`:
/// replays the whole verifier (fold-PoW, sample_distinct_queries, enforced sums,
/// residual), asserts `inner == t_r`, and returns the per-level query data the
/// guest port needs. Generalizes the (validated) inline m33 mirror.
fn run_mirror(cfg: &LigCfg, proof: &flare::pcs::ligerito::LigeritoProof, z: &[F128], target: F128, label: &[u8]) -> MirOut {
    use flare::pcs::ligerito::{ceil_log2, eval_sk_at_vks, induce_sumcheck_enforced_sum, induce_sumcheck_evaluate_at_residual};
    use flare::zerocheck::multilinear::eq_eval as eqe;
    let r = cfg.r();
    let sc = &proof.sumcheck_transcript;
    let fm = |u0: F128, u2: F128, tr: F128| (u0, tr + u2, u2);
    let evq = |q: (F128, F128, F128), x: F128| q.0 + x * q.1 + x * x * q.2;
    let foldq = |a: (F128, F128, F128), b: (F128, F128, F128), al: F128| (a.0 + al * b.0, a.1 + al * b.1, a.2 + al * b.2);
    let fgb = |lvl: usize| cfg.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;
    let n1 = cfg.log_n - cfg.initial_k;

    let mut sp = fs_ref::Sponge::new(label, &[]);
    sp.observe_bytes(b"flock-ligerito-basis-v0");
    sp.observe(target);
    sp.observe_bytes(&proof.initial_root);
    let mut tr = target;
    sp.observe(sc[0].u_0);
    sp.observe(sc[0].u_2);
    let mut quad = fm(sc[0].u_0, sc[0].u_2, tr);
    let mut txi = 1usize;
    let mut fni = 0usize;

    let mut r_lane = Vec::new();
    for j in 0..cfg.initial_k {
        let bits = (fgb(0) - j as i64).max(0) as u32;
        if bits > 0 {
            assert!(sp.verify_pow(proof.fold_grinding_nonces[fni], bits));
            fni += 1;
        }
        let ri = sp.sample();
        r_lane.push(ri);
        tr = evq(quad, ri);
        sp.observe(sc[txi].u_0);
        sp.observe(sc[txi].u_2);
        quad = fm(sc[txi].u_0, sc[txi].u_2, tr);
        txi += 1;
    }
    sp.observe_bytes(&proof.recursive_roots[0]);
    let mut ni = 0usize;
    assert!(sp.verify_pow(proof.grinding_nonces[ni], 0));
    ni += 1;
    let bl0 = 1usize << (cfg.initial_log_msg_cols + cfg.log_inv_rates[0]);
    let (q0, raw0) = sp.sample_distinct_queries(bl0, cfg.queries[0]);
    let a0: Vec<F128> = (0..ceil_log2(cfg.queries[0])).map(|_| sp.sample()).collect();
    let enf0 = induce_sumcheck_enforced_sum(&proof.initial_proof.opened_rows, &r_lane, &q0, &a0);
    sp.observe(sc[txi].u_0);
    sp.observe(sc[txi].u_2);
    let iq = fm(sc[txi].u_0, sc[txi].u_2, enf0);
    txi += 1;
    let beta0 = sp.sample();
    quad = foldq(quad, iq, beta0);
    tr += beta0 * enf0;

    let mut levels = vec![MirLevel { sorted: q0, raw: raw0, alpha: a0, beta: beta0 }];
    let mut ctx_lmc = vec![n1];
    let mut ctx_ris_start = vec![cfg.initial_k];
    let mut ris = r_lane.clone();
    let mut prev_lmc = n1 - cfg.recursive_ks[0];
    let mut prev_lir = cfg.log_inv_rates[1];
    let mut prev_lni = cfg.recursive_ks[0];
    let mut nri = 1usize;
    let mut rpi = 0usize;
    let mut n_current = n1;
    let mut inner = F128::ZERO;

    for i in 0..r {
        let k_i = cfg.recursive_ks[i];
        let mut level_rs = Vec::new();
        for j in 0..k_i {
            let bits = (fgb(i + 1) - j as i64).max(0) as u32;
            if bits > 0 {
                assert!(sp.verify_pow(proof.fold_grinding_nonces[fni], bits));
                fni += 1;
            }
            let ri = sp.sample();
            ris.push(ri);
            level_rs.push(ri);
            tr = evq(quad, ri);
            sp.observe(sc[txi].u_0);
            sp.observe(sc[txi].u_2);
            quad = fm(sc[txi].u_0, sc[txi].u_2, tr);
            txi += 1;
        }
        n_current -= k_i;
        let prev_block_len = 1usize << (prev_lmc + prev_lir);
        let _ = prev_lni;
        if i == r - 1 {
            let yr = &proof.final_proof.yr;
            for v in yr {
                sp.observe(*v);
            }
            assert!(sp.verify_pow(proof.grinding_nonces[ni], 0));
            let (ql, rawl) = sp.sample_distinct_queries(prev_block_len, cfg.queries[i + 1]);
            let al: Vec<F128> = (0..ceil_log2(cfg.queries[i + 1])).map(|_| sp.sample()).collect();
            let enfl = induce_sumcheck_enforced_sum(&proof.final_proof.opened_rows, &level_rs, &ql, &al);
            let betal = sp.sample();
            tr += betal * enfl;
            ctx_lmc.push(n_current);
            ctx_ris_start.push(ris.len());
            levels.push(MirLevel { sorted: ql, raw: rawl, alpha: al, beta: betal });
            let yr_log_n = cfg.yr_log_n;
            assert_eq!(n_current, yr_log_n);
            let resids: Vec<Vec<F128>> = (0..=r)
                .map(|k| {
                    let lmc = ctx_lmc[k];
                    let svk = eval_sk_at_vks(lmc);
                    let rfb = &ris[ctx_ris_start[k]..ctx_ris_start[k] + lmc - yr_log_n];
                    induce_sumcheck_evaluate_at_residual(lmc, &svk, &levels[k].sorted, &levels[k].alpha, rfb, yr_log_n)
                })
                .collect();
            for y in 0..(1usize << yr_log_n) {
                let mut point = ris.clone();
                for j in 0..yr_log_n {
                    point.push(if (y >> j) & 1 == 1 { F128::ONE } else { F128::ZERO });
                }
                let mut comb = eqe(z, &point);
                for k in 0..=r {
                    comb += levels[k].beta * resids[k][y];
                }
                inner += yr[y] * comb;
            }
        } else {
            let root_next = proof.recursive_roots[nri];
            nri += 1;
            sp.observe_bytes(&root_next);
            assert!(sp.verify_pow(proof.grinding_nonces[ni], 0));
            ni += 1;
            let (qi, rawi) = sp.sample_distinct_queries(prev_block_len, cfg.queries[i + 1]);
            let ai: Vec<F128> = (0..ceil_log2(cfg.queries[i + 1])).map(|_| sp.sample()).collect();
            let rp = &proof.recursive_proofs[rpi];
            rpi += 1;
            let enfi = induce_sumcheck_enforced_sum(&rp.opened_rows, &level_rs, &qi, &ai);
            sp.observe(sc[txi].u_0);
            sp.observe(sc[txi].u_2);
            let iqi = fm(sc[txi].u_0, sc[txi].u_2, enfi);
            txi += 1;
            let betai = sp.sample();
            quad = foldq(quad, iqi, betai);
            tr += betai * enfi;
            ctx_lmc.push(n_current);
            ctx_ris_start.push(ris.len());
            levels.push(MirLevel { sorted: qi, raw: rawi, alpha: ai, beta: betai });
            let k_next = cfg.recursive_ks[i + 1];
            prev_lni = k_next;
            prev_lmc = n_current - k_next;
            prev_lir = cfg.log_inv_rates[i + 2];
        }
    }
    assert_eq!(txi, sc.len(), "all sumcheck messages consumed");
    MirOut { tr, inner, ris, ctx_lmc, ctx_ris_start, levels }
}

#[test]
fn ligerito_small_mirror() {
    use leanvm_b::transcript::ProverState;
    use flare::lincheck::build_eq_table;
    use flare::ntt::AdditiveNttF128;
    use flare::pcs::ligerito::{ligero_commit, recursive_prover_with_basis, recursive_verifier_with_basis_succinct};
    use flare::zerocheck::multilinear::eq_eval;

    // A small multi-query, multi-level, fold-PoW config for fast iteration.
    let cfg = LigCfg {
        log_n: 12,
        initial_k: 3,
        log_inv_rates: vec![1, 2, 3],
        recursive_ks: vec![2, 2],
        recursive_log_msg_cols: vec![7, 5],
        initial_log_msg_cols: 9,
        queries: vec![6, 5, 4],
        fold_grinding_bits: vec![3, 2, 1],
        yr_log_n: 5,
    };
    let poly: Vec<F128> = (0..(1usize << cfg.log_n))
        .map(|i| F128::new(0x9E37_79B9u64.wrapping_mul(i as u64 + 1) + 1, 0x1234 ^ (i as u64)))
        .collect();
    let z: Vec<F128> = (0..cfg.log_n).map(|i| F128::new(0xABCD + i as u64, 7 * i as u64 + 1)).collect();
    let b = build_eq_table(&z);
    let target: F128 = poly.iter().zip(b.iter()).map(|(&a, &c)| a * c).fold(F128::ZERO, |a, x| a + x);

    let ntt = AdditiveNttF128::standard(cfg.initial_log_msg_cols + cfg.log_inv_rates[0]);
    let wtns = ligero_commit(&poly, cfg.initial_log_msg_cols, cfg.initial_k, cfg.log_inv_rates[0], &ntt);
    let initial_root = wtns.root();
    let label = b"smalltest";
    let mut pch = ProverState::new(label, &[]);
    let proof = recursive_prover_with_basis(&cfg.prover(), poly, b, target, &wtns.mat, &wtns.tree, &mut pch);

    let zc = z.clone();
    let eval_b = move |ris: &[F128], yl: usize| -> Vec<F128> {
        let mut p = ris.to_vec();
        p.resize(ris.len() + yl, F128::ZERO);
        (0..(1usize << yl))
            .map(|y| {
                for j in 0..yl {
                    p[ris.len() + j] = if (y >> j) & 1 == 1 { F128::ONE } else { F128::ZERO };
                }
                eq_eval(&zc, &p)
            })
            .collect()
    };
    let mut vch = ProverState::new(label, &[]);
    assert!(recursive_verifier_with_basis_succinct(&cfg.verifier(), &proof, cfg.log_n, target, &initial_root, eval_b, &mut vch));

    let m = run_mirror(&cfg, &proof, &z, target, label);
    assert_eq!(m.inner, m.tr, "small-config mirror inner == t_r");
    let ts: Vec<usize> = m.levels.iter().map(|l| l.raw.len()).collect();
    let ns: Vec<usize> = m.levels.iter().map(|l| l.sorted.len()).collect();
    eprintln!("small mirror OK: N per level = {ns:?}, T (raw samples) = {ts:?}");
}

/// Feasibility probe: can this machine drive a real m33_secure Ligerito proof

/// Feasibility probe: can this machine drive a real m33_secure Ligerito proof
/// (log_n=26, the config a 500-XMSS leanVM-b proof produces)? Times commit +
/// prove + native verify and prints the proof shapes the guest port must consume.
#[test]
#[ignore = "heavy: ~1 GiB witness; run explicitly for the production-config bench"]
fn ligerito_m33_native_probe() {
    use std::time::Instant;
    use leanvm_b::transcript::ProverState;
    use flare::lincheck::build_eq_table;
    use flare::ntt::AdditiveNttF128;
    use flare::pcs::ligerito::{
        ProverConfig, VerifierConfig, ligero_commit, recursive_prover_with_basis,
        recursive_verifier_with_basis_succinct,
    };
    use flare::zerocheck::multilinear::eq_eval;

    let log_n = 26usize;
    let initial_k = 6usize;
    let lir = vec![1usize, 2, 3, 4, 5, 6];
    let mkp = || ProverConfig {
        log_inv_rates: lir.clone(),
        recursive_steps: 5,
        initial_log_msg_cols: 20,
        initial_log_num_interleaved: initial_k,
        initial_k,
        recursive_log_msg_cols: vec![17, 14, 11, 8, 5],
        recursive_ks: vec![3, 3, 3, 3, 3],
        queries: vec![290, 177, 145, 132, 126, 124],
        grinding_bits: vec![0; 6],
        fold_grinding_bits: vec![11, 10, 8, 6, 4, 2],
        ood_samples: vec![0; 6],
    };
    let vc = VerifierConfig {
        log_inv_rates: lir.clone(),
        recursive_steps: 5,
        initial_log_msg_cols: 20,
        initial_log_num_interleaved: initial_k,
        initial_k,
        recursive_log_msg_cols: vec![17, 14, 11, 8, 5],
        recursive_ks: vec![3, 3, 3, 3, 3],
        queries: vec![290, 177, 145, 132, 126, 124],
        grinding_bits: vec![0; 6],
        fold_grinding_bits: vec![11, 10, 8, 6, 4, 2],
        ood_samples: vec![0; 6],
    };

    let t = Instant::now();
    let poly: Vec<F128> = (0..(1usize << log_n))
        .map(|i| F128::new(0x9E37_79B9u64.wrapping_mul(i as u64 + 1) + 1, 0x1234 ^ (i as u64)))
        .collect();
    eprintln!("[m33] witness gen: {:?}", t.elapsed());
    let z: Vec<F128> = (0..log_n).map(|i| F128::new(0xABCD + i as u64, 7 * i as u64 + 1)).collect();
    let b = build_eq_table(&z);
    let target: F128 = poly.iter().zip(b.iter()).map(|(&a, &c)| a * c).fold(F128::ZERO, |a, x| a + x);

    let t = Instant::now();
    let ntt = AdditiveNttF128::standard(20 + 1);
    let wtns = ligero_commit(&poly, 20, initial_k, 1, &ntt);
    eprintln!("[m33] commit: {:?}", t.elapsed());
    let initial_root = wtns.root();

    let label = b"m33probe";
    let t = Instant::now();
    let mut pch = ProverState::new(label, &[]);
    let proof = recursive_prover_with_basis(&mkp(), poly, b, target, &wtns.mat, &wtns.tree, &mut pch);
    eprintln!("[m33] recursive prove: {:?}", t.elapsed());

    let zc = z.clone();
    let eval_b = move |ris: &[F128], yl: usize| -> Vec<F128> {
        let mut p = ris.to_vec();
        p.resize(ris.len() + yl, F128::ZERO);
        (0..(1usize << yl))
            .map(|y| {
                for j in 0..yl {
                    p[ris.len() + j] = if (y >> j) & 1 == 1 { F128::ONE } else { F128::ZERO };
                }
                eq_eval(&zc, &p)
            })
            .collect()
    };
    let t = Instant::now();
    let mut vch = ProverState::new(label, &[]);
    let ok = recursive_verifier_with_basis_succinct(&vc, &proof, log_n, target, &initial_root, eval_b, &mut vch);
    eprintln!("[m33] native verify: {:?} -> {ok}", t.elapsed());
    assert!(ok);

    // ---- General mirror: reproduce the full 6-level verifier, confirm inner==t_r ----
    use flare::pcs::ligerito::{ceil_log2, eval_sk_at_vks, induce_sumcheck_enforced_sum, induce_sumcheck_evaluate_at_residual};
    use flare::zerocheck::multilinear::eq_eval as eqe;
    let tm = Instant::now();
    let rec_ks = [3usize, 3, 3, 3, 3];
    let cfgq = [290usize, 177, 145, 132, 126, 124];
    let fgb = [11i64, 10, 8, 6, 4, 2];
    let sc = &proof.sumcheck_transcript;
    let fm = |u0: F128, u2: F128, tr: F128| (u0, tr + u2, u2);
    let evq = |q: (F128, F128, F128), r: F128| q.0 + r * q.1 + r * r * q.2;
    let foldq = |a: (F128, F128, F128), b: (F128, F128, F128), al: F128| (a.0 + al * b.0, a.1 + al * b.1, a.2 + al * b.2);

    let n1 = log_n - initial_k; // 20
    let mut sp = fs_ref::Sponge::new(label, &[]);
    sp.observe_bytes(b"flock-ligerito-basis-v0");
    sp.observe(target);
    sp.observe_bytes(&proof.initial_root);
    let mut tr = target;
    sp.observe(sc[0].u_0);
    sp.observe(sc[0].u_2);
    let mut quad = fm(sc[0].u_0, sc[0].u_2, tr);
    let mut txi = 1usize;
    let mut fni = 0usize;
    let mut r_lane = Vec::new();
    for j in 0..initial_k {
        let bits = (fgb[0] - j as i64).max(0) as u32;
        if bits > 0 {
            assert!(sp.verify_pow(proof.fold_grinding_nonces[fni], bits));
            fni += 1;
        }
        let ri = sp.sample();
        r_lane.push(ri);
        tr = evq(quad, ri);
        sp.observe(sc[txi].u_0);
        sp.observe(sc[txi].u_2);
        quad = fm(sc[txi].u_0, sc[txi].u_2, tr);
        txi += 1;
    }
    sp.observe_bytes(&proof.recursive_roots[0]);
    let mut ni = 0usize;
    assert!(sp.verify_pow(proof.grinding_nonces[ni], 0));
    ni += 1;
    let bl0 = 1usize << (20 + 1);
    let (q0, _) = sp.sample_distinct_queries(bl0, cfgq[0]);
    let a0: Vec<F128> = (0..ceil_log2(cfgq[0])).map(|_| sp.sample()).collect();
    let enf0 = induce_sumcheck_enforced_sum(&proof.initial_proof.opened_rows, &r_lane, &q0, &a0);
    sp.observe(sc[txi].u_0);
    sp.observe(sc[txi].u_2);
    let iq = fm(sc[txi].u_0, sc[txi].u_2, enf0);
    txi += 1;
    let beta0 = sp.sample();
    quad = foldq(quad, iq, beta0);
    tr += beta0 * enf0;
    struct Ctx {
        lmc: usize,
        queries: Vec<usize>,
        alpha: Vec<F128>,
        ris_start: usize,
        beta: F128,
    }
    let mut ctxs = vec![Ctx { lmc: n1, queries: q0, alpha: a0, ris_start: initial_k, beta: beta0 }];
    let mut ris = r_lane.clone();
    let mut prev_lni = rec_ks[0];
    let mut prev_lmc = n1 - rec_ks[0];
    let mut prev_lir = lir[1];
    let mut nri = 1usize;
    let mut rpi = 0usize;
    let mut n_current = n1;
    let mut inner = F128::ZERO;
    for i in 0..5usize {
        let k_i = rec_ks[i];
        let mut level_rs = Vec::new();
        for j in 0..k_i {
            let bits = (fgb[i + 1] - j as i64).max(0) as u32;
            if bits > 0 {
                assert!(sp.verify_pow(proof.fold_grinding_nonces[fni], bits));
                fni += 1;
            }
            let ri = sp.sample();
            ris.push(ri);
            level_rs.push(ri);
            tr = evq(quad, ri);
            sp.observe(sc[txi].u_0);
            sp.observe(sc[txi].u_2);
            quad = fm(sc[txi].u_0, sc[txi].u_2, tr);
            txi += 1;
        }
        n_current -= k_i;
        let prev_block_len = 1usize << (prev_lmc + prev_lir);
        let _ = prev_lni;
        if i == 4 {
            let yr = &proof.final_proof.yr;
            for v in yr {
                sp.observe(*v);
            }
            assert!(sp.verify_pow(proof.grinding_nonces[ni], 0));
            let (ql, _) = sp.sample_distinct_queries(prev_block_len, cfgq[i + 1]);
            let al: Vec<F128> = (0..ceil_log2(cfgq[i + 1])).map(|_| sp.sample()).collect();
            let enfl = induce_sumcheck_enforced_sum(&proof.final_proof.opened_rows, &level_rs, &ql, &al);
            let betal = sp.sample();
            tr += betal * enfl;
            ctxs.push(Ctx { lmc: n_current, queries: ql, alpha: al, ris_start: ris.len(), beta: betal });
            let yr_log_n = n_current;
            let resids: Vec<Vec<F128>> = ctxs
                .iter()
                .map(|c| {
                    let svk = eval_sk_at_vks(c.lmc);
                    let rfb = &ris[c.ris_start..c.ris_start + c.lmc - yr_log_n];
                    induce_sumcheck_evaluate_at_residual(c.lmc, &svk, &c.queries, &c.alpha, rfb, yr_log_n)
                })
                .collect();
            for y in 0..(1usize << yr_log_n) {
                let mut point = ris.clone();
                for j in 0..yr_log_n {
                    point.push(if (y >> j) & 1 == 1 { F128::ONE } else { F128::ZERO });
                }
                let mut comb = eqe(&z, &point);
                for (k, c) in ctxs.iter().enumerate() {
                    comb += c.beta * resids[k][y];
                }
                inner += yr[y] * comb;
            }
        } else {
            let root_next = proof.recursive_roots[nri];
            nri += 1;
            sp.observe_bytes(&root_next);
            assert!(sp.verify_pow(proof.grinding_nonces[ni], 0));
            ni += 1;
            let (qi, _) = sp.sample_distinct_queries(prev_block_len, cfgq[i + 1]);
            let ai: Vec<F128> = (0..ceil_log2(cfgq[i + 1])).map(|_| sp.sample()).collect();
            let rp = &proof.recursive_proofs[rpi];
            rpi += 1;
            let enfi = induce_sumcheck_enforced_sum(&rp.opened_rows, &level_rs, &qi, &ai);
            sp.observe(sc[txi].u_0);
            sp.observe(sc[txi].u_2);
            let iqi = fm(sc[txi].u_0, sc[txi].u_2, enfi);
            txi += 1;
            let betai = sp.sample();
            quad = foldq(quad, iqi, betai);
            tr += betai * enfi;
            ctxs.push(Ctx { lmc: n_current, queries: qi, alpha: ai, ris_start: ris.len(), beta: betai });
            let k_next = rec_ks[i + 1];
            prev_lni = k_next;
            prev_lmc = n_current - k_next;
            prev_lir = lir[i + 2];
        }
    }
    assert_eq!(txi, sc.len(), "all sumcheck messages consumed");
    assert_eq!(inner, tr, "m33 mirror: inner == t_r (matches native accept)");
    eprintln!("[m33] mirror OK: inner == t_r  ({:?})", tm.elapsed());

    let tot_q: usize = proof.recursive_proofs.iter().map(|p| p.opened_rows.len()).sum::<usize>()
        + proof.initial_proof.opened_rows.len()
        + proof.final_proof.opened_rows.len();
    eprintln!(
        "[m33] shapes: sumcheck msgs={}, init rows={}x{}, mp={}, rec levels={}, final yr={}, total opened rows={}",
        proof.sumcheck_transcript.len(),
        proof.initial_proof.opened_rows.len(),
        proof.initial_proof.opened_rows.first().map(|r| r.len()).unwrap_or(0),
        proof.initial_proof.merkle_proof.len(),
        proof.recursive_proofs.len(),
        proof.final_proof.yr.len(),
        tot_q,
    );
}

// ---- Gadget 14: the COMPLETE tiny Ligerito opening verifier (end-to-end) ----
//
// A full port of `recursive_verifier_with_basis_succinct` for a tiny real instance
// (log_n=8, initial_k=2, k_0=2, r=1, 1 query/level), verified in-circuit against a
// real flock LigeritoProof: sponge replay (label, target, roots, sumcheck msgs,
// yr, nonces), the RoundQuad sumcheck (prologue + L0 lane fold + level fold), the
// enforced-sum glue, single-path Merkle opens (leaf hash + walk by query bits), and
// the residual check (novel-basis Ŵ_k recurrence + eval_b + terminal inner==t_r).
// This is leanVM-b's actual Ligerito opening scheme — the whir.py analog.

#[allow(clippy::too_many_arguments)]
fn ligerito_verify_source(
    seed: [F128; 2],
    target: F128,
    init_root: [F128; 2],
    rec_root: [F128; 2],
    lbl: [F128; 2],
    z: &[F128],
    sv6: &[F128],
    isv6: &[F128],
    sv4: &[F128],
    isv4: &[F128],
    evb: &[F128],
) -> String {
    let mut s = String::new();
    s.push_str("from snark_lib import *\n");
    s.push_str(&format!("SEED0 = {}\nSEED1 = {}\n", u(seed[0]), u(seed[1])));
    s.push_str(&format!("TARGET = {}\n", u(target)));
    s.push_str(&format!("INITROOT0 = {}\nINITROOT1 = {}\n", u(init_root[0]), u(init_root[1])));
    s.push_str(&format!("RECROOT0 = {}\nRECROOT1 = {}\n", u(rec_root[0]), u(rec_root[1])));
    s.push_str(&format!("LBLA = {}\nLBLB = {}\n", u(lbl[0]), u(lbl[1])));
    for (i, v) in z.iter().enumerate() {
        s.push_str(&format!("Z{i} = {}\n", u(*v)));
    }
    for (i, v) in sv6.iter().enumerate() {
        s.push_str(&format!("SV6_{i} = {}\n", u(*v)));
    }
    for (i, v) in isv6.iter().enumerate() {
        s.push_str(&format!("ISV6_{i} = {}\n", u(*v)));
    }
    for (i, v) in sv4.iter().enumerate() {
        s.push_str(&format!("SV4_{i} = {}\n", u(*v)));
    }
    for (i, v) in isv4.iter().enumerate() {
        s.push_str(&format!("ISV4_{i} = {}\n", u(*v)));
    }
    for (y, v) in evb.iter().enumerate() {
        s.push_str(&format!("EVB{y} = {}\n", u(*v)));
    }
    s.push('\n');
    s.push_str("def main():\n");
    let mut n = 0usize;
    // hints
    line(&mut s, "sc = HeapBuf(12)".into());
    line(&mut s, "hint_witness(sc[0:12], \"sc\")".into());
    for (nm, sz) in [("l0row", 4), ("l0path", 14), ("lastrow", 4), ("lastpath", 10), ("yr", 16), ("vq0", 128), ("vql", 128)] {
        line(&mut s, format!("{nm} = HeapBuf({sz})"));
        line(&mut s, format!("hint_witness({nm}[0:{sz}], \"{nm}\")"));
    }
    line(&mut s, "cv0 = SEED0".into());
    line(&mut s, "cv1 = SEED1".into());
    line(&mut s, "sp = sc".into());
    // observe_label("flock-ligerito-basis-v0") = len 23 + 2 words
    emit_absorb(&mut s, &mut n, "23", 3);
    emit_absorb(&mut s, &mut n, "LBLA", 2);
    emit_absorb(&mut s, &mut n, "LBLB", 2);
    emit_absorb(&mut s, &mut n, "TARGET", 1);
    emit_absorb(&mut s, &mut n, "32", 3);
    emit_absorb(&mut s, &mut n, "INITROOT0", 2);
    emit_absorb(&mut s, &mut n, "INITROOT1", 2);
    // prologue msg0 → quad; t_r = target
    emit_read(&mut s, &mut n, "u0");
    emit_read(&mut s, &mut n, "u2");
    line(&mut s, "qc = u0".into());
    line(&mut s, "qb = TARGET + u2".into());
    line(&mut s, "qa = u2".into());
    line(&mut s, "tr = TARGET".into());
    // L0 lane fold (initial_k = 2)
    for j in 0..2 {
        emit_sample(&mut s, &mut n, &format!("ri{j}"));
        line(&mut s, format!("r2_{j} = ri{j} * ri{j}"));
        line(&mut s, format!("tr = qc + ri{j} * qb + r2_{j} * qa"));
        emit_read(&mut s, &mut n, &format!("la{j}"));
        emit_read(&mut s, &mut n, &format!("lb{j}"));
        line(&mut s, format!("qc = la{j}"));
        line(&mut s, format!("qb = tr + lb{j}"));
        line(&mut s, format!("qa = lb{j}"));
    }
    // observe root_1, absorb L0 query nonce (0), sample v_q0
    emit_absorb(&mut s, &mut n, "32", 3);
    emit_absorb(&mut s, &mut n, "RECROOT0", 2);
    emit_absorb(&mut s, &mut n, "RECROOT1", 2);
    emit_absorb(&mut s, &mut n, "0", 5);
    emit_sample(&mut s, &mut n, "vq0v");
    // enforced_0 = <l0row, eq_table([ri0, ri1])>
    line(&mut s, "om0 = 1 + ri0".into());
    line(&mut s, "om1 = 1 + ri1".into());
    line(&mut s, "eq0 = om0 * om1".into());
    line(&mut s, "eq1 = ri0 * om1".into());
    line(&mut s, "eq2 = om0 * ri1".into());
    line(&mut s, "eq3 = ri0 * ri1".into());
    line(&mut s, "enf0 = l0row[GEN ** 0] * eq0 + l0row[GEN ** 1] * eq1 + l0row[GEN ** 2] * eq2 + l0row[GEN ** 3] * eq3".into());
    // intro0 glue: read msg, sample beta0, fold quad, t_r += beta0·enf0
    emit_read(&mut s, &mut n, "iu0");
    emit_read(&mut s, &mut n, "iu2");
    emit_sample(&mut s, &mut n, "beta0");
    line(&mut s, "ib = enf0 + iu2".into());
    line(&mut s, "qc = qc + beta0 * iu0".into());
    line(&mut s, "qb = qb + beta0 * ib".into());
    line(&mut s, "qa = qa + beta0 * iu2".into());
    line(&mut s, "tr = tr + beta0 * enf0".into());
    // level-0 (last) fold (k_0 = 2)
    for j in 0..2 {
        emit_sample(&mut s, &mut n, &format!("ry{j}"));
        line(&mut s, format!("s2_{j} = ry{j} * ry{j}"));
        line(&mut s, format!("tr = qc + ry{j} * qb + s2_{j} * qa"));
        emit_read(&mut s, &mut n, &format!("ma{j}"));
        emit_read(&mut s, &mut n, &format!("mb{j}"));
        line(&mut s, format!("qc = ma{j}"));
        line(&mut s, format!("qb = tr + mb{j}"));
        line(&mut s, format!("qa = mb{j}"));
    }
    // observe yr (16), absorb last-level nonce (0), sample v_qlast
    for y in 0..16 {
        emit_absorb(&mut s, &mut n, &format!("yr[GEN ** {y}]"), 1);
    }
    emit_absorb(&mut s, &mut n, "0", 5);
    emit_sample(&mut s, &mut n, "vqlv");
    // enforced_last = <lastrow, eq_table([ry0, ry1])>; sample beta_last; t_r += beta_last·enf
    line(&mut s, "pm0 = 1 + ry0".into());
    line(&mut s, "pm1 = 1 + ry1".into());
    line(&mut s, "fq0 = pm0 * pm1".into());
    line(&mut s, "fq1 = ry0 * pm1".into());
    line(&mut s, "fq2 = pm0 * ry1".into());
    line(&mut s, "fq3 = ry0 * ry1".into());
    line(&mut s, "enfL = lastrow[GEN ** 0] * fq0 + lastrow[GEN ** 1] * fq1 + lastrow[GEN ** 2] * fq2 + lastrow[GEN ** 3] * fq3".into());
    emit_sample(&mut s, &mut n, "betaL");
    line(&mut s, "tr = tr + betaL * enfL".into());
    // bit-check the sampled query values, then verify the Merkle opens
    line(&mut s, "chk(vq0, vq0v)".into());
    line(&mut s, "chk(vql, vqlv)".into());
    line(&mut s, "d0, d1 = hleaf(l0row[GEN ** 0], l0row[GEN ** 1], l0row[GEN ** 2], l0row[GEN ** 3])".into());
    for lvl in 0..7 {
        line(&mut s, format!("d0, d1 = mstep(d0, d1, l0path[GEN ** {}], l0path[GEN ** {}], vq0[GEN ** {lvl}])", 2 * lvl, 2 * lvl + 1));
    }
    line(&mut s, "assert d0 == INITROOT0".into());
    line(&mut s, "assert d1 == INITROOT1".into());
    line(&mut s, "e0, e1 = hleaf(lastrow[GEN ** 0], lastrow[GEN ** 1], lastrow[GEN ** 2], lastrow[GEN ** 3])".into());
    for lvl in 0..5 {
        line(&mut s, format!("e0, e1 = mstep(e0, e1, lastpath[GEN ** {}], lastpath[GEN ** {}], vql[GEN ** {lvl}])", 2 * lvl, 2 * lvl + 1));
    }
    line(&mut s, "assert e0 == RECROOT0".into());
    line(&mut s, "assert e1 == RECROOT1".into());
    // residual level L0: q_field, raw s, Ŵ, prefix_prod
    let qf = |bits: &str, k: usize| -> String {
        (0..k).map(|i| format!("{bits}[GEN ** {i}] * (GEN ** {i})")).collect::<Vec<_>>().join(" + ")
    };
    line(&mut s, format!("qf0 = {}", qf("vq0", 7)));
    line(&mut s, "sw6_0 = qf0".into());
    for k in 1..6 {
        line(&mut s, format!("sw6_{k} = sw6_{} * sw6_{} + SV6_{} * sw6_{}", k - 1, k - 1, k - 1, k - 1));
    }
    for k in 0..6 {
        line(&mut s, format!("w6_{k} = sw6_{k} * ISV6_{k}"));
    }
    // prefix_prod uses ris_for_basis = [ry0, ry1] and Ŵ_0, Ŵ_1
    line(&mut s, "pp0a = 1 + ry0 * (1 + w6_0)".into());
    line(&mut s, "pp0b = 1 + ry1 * (1 + w6_1)".into());
    line(&mut s, "pp0 = pp0a * pp0b".into());
    // residual level last: q_field, raw s, Ŵ (prefix_len = 0 ⇒ pp = 1)
    line(&mut s, format!("qfL = {}", qf("vql", 5)));
    line(&mut s, "sw4_0 = qfL".into());
    for k in 1..4 {
        line(&mut s, format!("sw4_{k} = sw4_{} * sw4_{} + SV4_{} * sw4_{}", k - 1, k - 1, k - 1, k - 1));
    }
    for k in 0..4 {
        line(&mut s, format!("w4_{k} = sw4_{k} * ISV4_{k}"));
    }
    // eqris = Π_{k<4} (1 + Z_k + ri_k),  ris = [ri0, ri1, ry0, ry1]
    line(&mut s, "er0 = 1 + Z0 + ri0".into());
    line(&mut s, "er1 = 1 + Z1 + ri1".into());
    line(&mut s, "er2 = 1 + Z2 + ry0".into());
    line(&mut s, "er3 = 1 + Z3 + ry1".into());
    line(&mut s, "eqris = er0 * er1 * er2 * er3".into());
    // terminal: inner = Σ_y yr[y]·(eqris·EVB_y + beta0·resid0_y + betaL·residL_y)
    // resid0_y = pp0 · Π_{j: bit_j(y)} w6_{2+j};  residL_y = Π_{j: bit_j(y)} w4_j
    line(&mut s, "inner = 0".into());
    for y in 0..16usize {
        // resid0_y
        let mut r0 = "pp0".to_string();
        for j in 0..4 {
            if (y >> j) & 1 == 1 {
                r0.push_str(&format!(" * w6_{}", 2 + j));
            }
        }
        line(&mut s, format!("r0y{y} = {r0}"));
        // residL_y (empty product ⇒ 1)
        let sel: Vec<String> = (0..4).filter(|&j| (y >> j) & 1 == 1).map(|j| format!("w4_{j}")).collect();
        let rl = if sel.is_empty() { "GEN ** 0".to_string() } else { sel.join(" * ") };
        line(&mut s, format!("rLy{y} = {rl}"));
        line(&mut s, format!("evb{y} = eqris * EVB{y}"));
        line(&mut s, format!("comb{y} = evb{y} + beta0 * r0y{y} + betaL * rLy{y}"));
        line(&mut s, format!("inner = inner + yr[GEN ** {y}] * comb{y}"));
    }
    line(&mut s, "assert inner == tr".into());
    line(&mut s, "return".into());

    // helpers
    s.push_str("\ndef chk(bp, v):\n");
    s.push_str("    cb = bp\n    wb = GEN ** 0\n    recon = 0\n");
    s.push_str("    for b in unroll(0, 128):\n");
    s.push_str("        bit = cb[1]\n        sq = bit * bit\n        assert sq == bit\n");
    s.push_str("        recon = recon + bit * wb\n        cb = cb * GEN\n        wb = wb * GEN\n");
    s.push_str("    assert recon == v\n    return\n");
    s.push_str("\ndef hleaf(r0, r1, r2, r3):\n");
    s.push_str("    iv = StackBuf(2)\n    iv[0] = GEN ** 64\n    iv[1] = 0\n");
    s.push_str("    q0 = StackBuf(2)\n    q0[0] = r0\n    q0[1] = r1\n    c1 = StackBuf(2)\n    blake3(iv, q0, c1)\n");
    s.push_str("    q1 = StackBuf(2)\n    q1[0] = r2\n    q1[1] = r3\n    c2 = StackBuf(2)\n    blake3(c1, q1, c2)\n");
    s.push_str("    return c2[0], c2[1]\n");
    s.push_str("\ndef mstep(n0, n1, s0, s1, bit):\n");
    s.push_str("    nb = StackBuf(2)\n    nb[0] = n0\n    nb[1] = n1\n");
    s.push_str("    sb = StackBuf(2)\n    sb[0] = s0\n    sb[1] = s1\n    pr = StackBuf(2)\n");
    s.push_str("    if bit == 0:\n        blake3(nb, sb, pr)\n    else:\n        blake3(sb, nb, pr)\n");
    s.push_str("    return pr[0], pr[1]\n");
    s
}

// ---- Ligerito core: native driver probe (tiny instance, 1 query/level) ----
//
// Drives flock's actual recursive Ligerito prover + succinct verifier at a tiny
// config with a leanVM-b ProverState challenger (the compress-sponge the zkDSL
// guest replays). With 1 query per level the octopus multi-proof degenerates to a
// single Merkle path, keeping the port tractable. Prints the concrete proof shapes
// the guest port must consume.
#[test]
fn test_recursive_ligerito() {
    use std::collections::BTreeMap;
    use std::time::Instant;
    use leanvm_b::compiler::parse_file_with_replacements;
    use leanvm_b::transcript::ProverState;
    use flare::lincheck::build_eq_table;
    use flare::ntt::AdditiveNttF128;
    use flare::pcs::ligerito::{eval_sk_at_vks, ligero_commit, recursive_prover_with_basis, recursive_verifier_with_basis_succinct};
    use flare::zerocheck::multilinear::eq_eval;

    // The tiny config (1 query/level). The verifier program lives in the readable
    // `.py` file `tests/ligerito_verifier.py`, loaded via placeholder substitution.
    let cfg = LigCfg {
        log_n: 8,
        initial_k: 2,
        log_inv_rates: vec![1, 1],
        recursive_ks: vec![2],
        recursive_log_msg_cols: vec![4],
        initial_log_msg_cols: 6,
        queries: vec![1, 1],
        fold_grinding_bits: vec![0, 0],
        yr_log_n: 4,
    };
    let poly: Vec<F128> = (0..(1usize << cfg.log_n))
        .map(|i| F128::new(0x9E37_79B9u64.wrapping_mul(i as u64 + 1) + 1, 0x1234 ^ (i as u64)))
        .collect();
    let z: Vec<F128> = (0..cfg.log_n).map(|i| F128::new(0xABCD + i as u64, 0x55u64.wrapping_mul(i as u64) + 7)).collect();
    let b = build_eq_table(&z);
    let target: F128 = poly.iter().zip(b.iter()).map(|(&a, &c)| a * c).fold(F128::ZERO, |a, x| a + x);

    let ntt = AdditiveNttF128::standard(cfg.initial_log_msg_cols + cfg.log_inv_rates[0]);
    let wtns = ligero_commit(&poly, cfg.initial_log_msg_cols, cfg.initial_k, cfg.log_inv_rates[0], &ntt);
    let initial_root = wtns.root();

    let label = b"ligtest";
    let mut pch = ProverState::new(label, &[]);
    let proof = recursive_prover_with_basis(&cfg.prover(), poly, b, target, &wtns.mat, &wtns.tree, &mut pch);

    let zc = z.clone();
    let eval_b = move |ris: &[F128], yl: usize| -> Vec<F128> {
        let mut p = ris.to_vec();
        p.resize(ris.len() + yl, F128::ZERO);
        (0..(1usize << yl))
            .map(|y| {
                for j in 0..yl {
                    p[ris.len() + j] = if (y >> j) & 1 == 1 { F128::ONE } else { F128::ZERO };
                }
                eq_eval(&zc, &p)
            })
            .collect()
    };
    let mut vch = ProverState::new(label, &[]);
    assert!(recursive_verifier_with_basis_succinct(&cfg.verifier(), &proof, cfg.log_n, target, &initial_root, eval_b, &mut vch));

    // Mirror confirms inner == t_r and extracts the sampled query values.
    let m = run_mirror(&cfg, &proof, &z, target, label);
    assert_eq!(m.inner, m.tr, "mirror: inner == t_r");
    let v_q0 = m.levels[0].raw[0];
    let v_ql = m.levels[1].raw[0];

    // ---- Load the zkDSL verifier from tests/ligerito_verifier.py, filling the
    // per-proof constants via placeholder substitution (recursion.py convention). ----
    let hbytes = |h: [u8; 32]| {
        let w = |o: usize| u64::from_le_bytes(h[o..o + 8].try_into().unwrap());
        [F128::new(w(0), w(8)), F128::new(w(16), w(24))]
    };
    let ir = hbytes(proof.initial_root);
    let rr = hbytes(proof.recursive_roots[0]);
    let lbl_bytes = b"flock-ligerito-basis-v0";
    let word = |o: usize| {
        let mut buf = [0u8; 16];
        let end = (lbl_bytes.len() - o).min(16);
        buf[..end].copy_from_slice(&lbl_bytes[o..o + end]);
        F128::new(u64::from_le_bytes(buf[..8].try_into().unwrap()), u64::from_le_bytes(buf[8..].try_into().unwrap()))
    };
    let sv6 = eval_sk_at_vks(6);
    let iv6: Vec<F128> = sv6.iter().map(|&v| if v == F128::ZERO { F128::ZERO } else { v.inv() }).collect();
    let sv4 = eval_sk_at_vks(4);
    let iv4: Vec<F128> = sv4.iter().map(|&v| if v == F128::ZERO { F128::ZERO } else { v.inv() }).collect();
    let seed = fs_ref::seed_cv(label, &[]);

    let mut rep: BTreeMap<String, String> = BTreeMap::new();
    let mut put = |k: String, v: F128| {
        rep.insert(format!("{k}_PLACEHOLDER"), u(v).to_string());
    };
    put("SEED0".into(), seed[0]);
    put("SEED1".into(), seed[1]);
    put("TARGET".into(), target);
    put("INITROOT0".into(), ir[0]);
    put("INITROOT1".into(), ir[1]);
    put("RECROOT0".into(), rr[0]);
    put("RECROOT1".into(), rr[1]);
    put("LBLA".into(), word(0));
    put("LBLB".into(), word(16));
    for i in 0..5 {
        put(format!("SV6_{i}"), sv6[i]);
    }
    for i in 0..6 {
        put(format!("IV6_{i}"), iv6[i]);
    }
    for i in 0..3 {
        put(format!("SV4_{i}"), sv4[i]);
    }
    for i in 0..4 {
        put(format!("IV4_{i}"), iv4[i]);
    }
    for i in 0..8 {
        put(format!("Z{i}"), z[i]);
    }

    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/ligerito_verifier.py");
    let ast = parse_file_with_replacements(path, &rep).expect("parse ligerito_verifier.py");
    let mut program = compile(&ast);

    let sc_flat: Vec<F128> = proof.sumcheck_transcript.iter().flat_map(|m| [m.u_0, m.u_2]).collect();
    let path_flat = |p: &[[u8; 32]]| -> Vec<F128> { p.iter().flat_map(|&h| hbytes(h)).collect() };
    program.set_witness("sc", vec![sc_flat]);
    program.set_witness("l0row", vec![proof.initial_proof.opened_rows[0].clone()]);
    program.set_witness("l0path", vec![path_flat(&proof.initial_proof.merkle_proof)]);
    program.set_witness("lastrow", vec![proof.final_proof.opened_rows[0].clone()]);
    program.set_witness("lastpath", vec![path_flat(&proof.final_proof.merkle_proof)]);
    program.set_witness("yr", vec![proof.final_proof.yr.clone()]);
    program.set_witness("vq0", vec![bits_of(v_q0)]);
    program.set_witness("vql", vec![bits_of(v_ql)]);
    let pi = [F128::ZERO, F128::ZERO];
    let t = std::time::Instant::now();
    let (gproof, stats) = prove(&program, pi);
    let t_prove = t.elapsed();
    let t = std::time::Instant::now();
    verify(&program, &pi, &gproof).expect("recursive Ligerito verification");
    let t_verify = t.elapsed();

    let proof_bytes = bincode::serialized_size(&gproof).expect("proof serializes");
    println!("\nRecursive Ligerito verification, in-circuit (config: log_n=8, initial_k=2, 1 query/level)");
    println!("  cycles (VM steps)           : {}", stats.cycles);
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"].iter().zip(&stats.counts) {
        let pow = if c == 0 { "0".to_string() } else { format!("2^{:.2}", (c as f64).log2()) };
        println!("    {name:<6} instructions      : {c:>8}  = {pow}");
    }
    println!("  committed witness size      : 2^{:.3}", (stats.committed as f64).log2());
    println!("  data memory                 : 2^{} padded", stats.log_mem);
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving (incl. witness gen) : {t_prove:?}");
    println!("  verifying                   : {t_verify:?}");
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

/// Emit `compress(cv, [val, tag])` into cv0/cv1 — the absorb/observe primitive
/// (tag 1 = scalar, 2 = byte-word, 3 = length frame, 5 = PoW nonce).
fn emit_absorb(s: &mut String, n: &mut usize, val: &str, tag: u32) {
    let k = *n;
    *n += 1;
    line(s, format!("ac{k} = StackBuf(2)"));
    line(s, format!("ac{k}[0] = {val}"));
    line(s, format!("ac{k}[1] = {tag}"));
    line(s, format!("cc{k} = StackBuf(2)"));
    line(s, format!("cc{k}[0] = cv0"));
    line(s, format!("cc{k}[1] = cv1"));
    line(s, format!("co{k} = StackBuf(2)"));
    line(s, format!("blake3(cc{k}, ac{k}, co{k})"));
    line(s, format!("cv0 = co{k}[0]"));
    line(s, format!("cv1 = co{k}[1]"));
}

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
