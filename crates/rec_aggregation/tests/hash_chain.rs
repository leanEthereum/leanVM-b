//! BLAKE3 hash chain, written in the zkDSL and proven end-to-end.
//!
//! Starting from `h_0 = 0…0` (256 bits), each step is `h_{i+1} = BLAKE3(h_i,
//! h_i)` (the previous value fed as both 256-bit operands). The program mirrors
//! the Fibonacci demo's strategy: a `mul_range` loop *in the exponent* on the
//! outside, an unrolled block of `BLAKE3` steps on the inside, with the chain
//! state carried through a `HeapBuf` (write-once memory). The final `h_N` is
//! published into the public input (`m[0], m[1]`); write-once memory forces the
//! proven result to equal it.
//!
//! `N` and the unroll factor are read from the environment (`LEANVM_HASH_N`,
//! `LEANVM_HASH_UNROLL`) so this doubles as a benchmark — e.g.
//! `LEANVM_HASH_N=10000 LEANVM_HASH_UNROLL=1000 cargo test --release
//! --test hash_chain -- --nocapture`. It prints cycles, per-table sizes, proof
//! size, prove/verify time, and hashes/second, like `src/main.rs`.

use std::time::Instant;

use lean_vm::blake3_flock::warm_setup;
use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::F128;

/// One compression step `c = BLAKE3(a, b)` (the VM's `blake3` builtin): the four
/// input words are laid little-endian into 64 bytes, BLAKE3-hashed, and the
/// 32-byte digest split into two `F128` words. Matches `cpu::blake3_compress`.
fn compress(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(16).zip([a[0], a[1], b[0], b[1]]) {
        slot[..8].copy_from_slice(&w.lo.to_le_bytes());
        slot[8..].copy_from_slice(&w.hi.to_le_bytes());
    }
    let d = blake3::hash(&input);
    let d = d.as_bytes();
    let word = |b: &[u8]| {
        F128::new(
            u64::from_le_bytes(b[..8].try_into().unwrap()),
            u64::from_le_bytes(b[8..16].try_into().unwrap()),
        )
    };
    [word(&d[..16]), word(&d[16..])]
}

/// Build the zkDSL source for an `n`-step chain unrolled `unroll` per outer
/// iteration (`k = n / unroll` iterations). Layout in the heap `buff`: the chain
/// value after `j·unroll` steps sits at cells `2j, 2j+1` (g-powers `g^{2j},
/// g^{2j+1}`). Each outer step loads that pair into a size-2 `StackBuf`, runs
/// `unroll` `BLAKE3`s in the stack — each output pair feeds the next with **no
/// copies** (a self-hash `blake3(h, h, out)` aliases one pair into both input
/// operands) — then writes the result pair two cells along.
fn chain_source(n: usize, unroll: usize) -> String {
    assert!(unroll >= 1 && n.is_multiple_of(unroll), "N must be a positive multiple of UNROLL");
    let k = n / unroll;
    let two_k = 2 * k;

    let mut body = String::new();
    // Block `j`'s boundary pair sits at cells `g^{2j}, g^{2j+1}`; the loop counter
    // `i = gʲ` is the block index (×g each iteration), so the pair base is `b = i·i`.
    // Load the current chain value into a size-2 StackBuf (heap read straight
    // into the two consecutive stack cells).
    body.push_str("        b = i * i\n");
    body.push_str("        h0 = StackBuf(2)\n");
    body.push_str("        h0[0] = buff[b]\n");
    body.push_str("        h0[1] = buff[b * GEN]\n");
    // `unroll` self-hashes; each `blake3` reads its operand stack in place and
    // writes into the next pre-allocated size-2 stack — no copies between steps.
    for s in 1..=unroll {
        body.push_str(&format!("        h{s} = StackBuf(2)\n"));
        body.push_str(&format!("        blake3(h{p}, h{p}, h{s})\n", p = s - 1));
    }
    // Write the block's result back to the next array pair.
    body.push_str(&format!("        buff[b * GEN ** 2] = h{unroll}[0]\n"));
    body.push_str(&format!("        buff[b * GEN ** 3] = h{unroll}[1]\n"));

    format!(
        "def main():\n\
        \x20   buff = HeapBuf({size})\n\
        \x20   buff[1] = 0\n\
        \x20   buff[GEN] = 0\n\
        \x20   for i in mul_range(1, GEN ** {k}):\n\
        {body}\
        \x20   p = 1\n\
        \x20   p[1] = buff[GEN ** {two_k}]\n\
        \x20   p[GEN] = buff[GEN ** {two_k_1}]\n\
        \x20   return\n",
        size = 2 * k + 2,
        two_k_1 = two_k + 1,
    )
}

#[test]
fn blake3_hash_chain() {
    let env = |key: &str, default: usize| {
        std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
    };
    let unroll = env("LEANVM_HASH_UNROLL", 4);
    let n = env("LEANVM_HASH_N", 8);
    assert!(n.is_multiple_of(unroll), "LEANVM_HASH_N must be a multiple of LEANVM_HASH_UNROLL");

    // Reference chain in O(1) memory: a rolling value, no array of intermediates.
    let mut h = [F128::ZERO; 2];
    for _ in 0..n {
        h = compress(h, h);
    }
    let pi = h; // the published final value h_N

    let program = compile(&parse(&chain_source(n, unroll)).expect("parse"));

    // Pay the one-time, circuit-shape-only flock setup (build + hash the BLAKE3
    // R1CS) up front so the timed prove/verify below reflect steady-state,
    // repeated-proving cost rather than the cold start.
    warm_setup(n);

    let t = Instant::now();
    let (proof, stats) = prove(&program, pi);
    let t_prove = t.elapsed();
    let t = Instant::now();
    verify(&program, &pi, &proof).expect("hash-chain proof verifies");
    let t_verify = t.elapsed();

    assert_eq!(stats.counts[5], n, "one BLAKE3 row per chain step");

    println!("\nBLAKE3 hash chain, N = {n}, unroll = {unroll}");
    println!("  cycles (VM steps)           : {}", stats.cycles);
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"].iter().zip(&stats.counts) {
        let pow = if c == 0 {
            "0".to_string()
        } else {
            format!("2^{:.3}", (c as f64).log2())
        };
        println!("    {name:<6} instructions       : {pow}");
    }
    println!("  committed witness size      : 2^{:.3}", (stats.committed as f64).log2());
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving (incl. witness gen) : {t_prove:?}");
    println!("  verifying                   : {t_verify:?}");
    println!(
        "  throughput                  : {:.0} hashes/s",
        n as f64 / t_prove.as_secs_f64()
    );

    // A wrong public input must be rejected.
    let mut bad = pi;
    bad[0] += F128::ONE;
    assert!(verify(&program, &bad, &proof).is_err());
}
