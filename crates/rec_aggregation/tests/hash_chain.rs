//! BLAKE3 hash chain, written in the zkDSL and proven end-to-end.
//!
//! Starting from `h_0 = 0…0` (256 bits), each step is `h_{i+1} = BLAKE3(h_i,
//! h_i)` (the previous value fed as both 256-bit operands). The program mirrors
//! the Fibonacci demo's strategy: a `mul_range` loop *in the exponent* on the
//! outside, an unrolled block of `BLAKE3` steps on the inside, with the chain
//! state carried through a `HeapBuf` (write-once memory). The four 64-bit digest
//! lanes of the final `h_N` are packed into two canonical 128-bit BLAKE3 cells
//! embedded in the F192 public input;
//! write-once memory forces the proven result to equal it.
//!
//! `N` and the unroll factor are read from the environment (`LEANVM_HASH_N`,
//! `LEANVM_HASH_UNROLL`) so this doubles as a benchmark — e.g.
//! `LEANVM_HASH_N=10000 LEANVM_HASH_UNROLL=1000 cargo test --release
//! --test hash_chain -- --nocapture`. It prints cycles, per-table sizes, proof
//! size, prove/verify time, and hashes/second, like `src/main.rs`.

use std::time::Instant;

use lean_compiler::{compile, parse};
use lean_vm::blake3_flock::warm_setup;
use lean_vm::cpu::{prove, verify};
use primitives::{
    field::{F64, F192},
    pretty_integer,
};

/// One compression step `c = BLAKE3(a, b)` (the VM's `blake3` builtin): the eight
/// input words are laid little-endian into 64 bytes, BLAKE3-hashed, and the
/// 32-byte digest split into four `F64` words. Matches `cpu::blake3_compress`.
fn compress(a: [F64; 4], b: [F64; 4]) -> [F64; 4] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(8).zip(a.into_iter().chain(b)) {
        slot.copy_from_slice(&w.0.to_le_bytes());
    }
    let d = blake3::hash(&input);
    let d = d.as_bytes();
    std::array::from_fn(|k| F64(u64::from_le_bytes(d[8 * k..8 * k + 8].try_into().unwrap())))
}

/// Build the zkDSL source for an `n`-step chain unrolled `unroll` per outer
/// iteration (`k = n / unroll` iterations). Layout in the heap `buff`: the chain
/// value after `j·unroll` steps sits at cells `2j, 2j+1`. Each outer step loads
/// that pair into a size-2 `StackBuf`, runs `unroll` `BLAKE3`s in the stack —
/// each output pair feeds the next with **no copies** (a self-hash aliases one
/// pair into both input operands) — then writes the result pair two cells along.
fn chain_source(n: usize, unroll: usize) -> String {
    assert!(
        unroll >= 1 && n.is_multiple_of(unroll),
        "N must be a positive multiple of UNROLL"
    );
    let k = n / unroll;
    let two_k = 2 * k;

    let mut body = String::new();
    // A 256-bit BLAKE3 value occupies two canonical 128-bit cells. Block `j`'s
    // boundary value sits at cells `g^{2j}..g^{2j+1}`; the loop counter `i = gʲ`
    // is the block index (×g each iteration), so the value base is `b = i²`.
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
    // Write the block's result back to the next value (two cells along).
    for w in 0..2 {
        body.push_str(&format!("        buff[b * GEN ** {}] = h{unroll}[{w}]\n", 2 + w));
    }

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
    let env = |key: &str, default: usize| std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default);
    let unroll = env("LEANVM_HASH_UNROLL", 4);
    let n = env("LEANVM_HASH_N", 8);
    assert!(
        n.is_multiple_of(unroll),
        "LEANVM_HASH_N must be a multiple of LEANVM_HASH_UNROLL"
    );

    // Reference chain in O(1) memory: a rolling value, no array of intermediates.
    let mut h = [F64::ZERO; 4];
    for _ in 0..n {
        h = compress(h, h);
    }
    // The two published BLAKE3 cells of h_N (top F192 limb zero).
    let pi = [F192::new(h[0].0, h[1].0, 0), F192::new(h[2].0, h[3].0, 0)];

    let program = compile(&parse(&chain_source(n, unroll)).expect("parse"));

    // Pay the one-time, circuit-shape-only flock setup (build + hash the BLAKE3
    // R1CS) up front so the timed prove/verify below reflect steady-state,
    // repeated-proving cost rather than the cold start.
    warm_setup(n);

    let t = Instant::now();
    let (proof, stats) = prove(&program, pi, lean_vm::pcs::LOG_INV_RATE);
    let t_prove = t.elapsed();
    let t = Instant::now();
    verify(&program, &pi, &proof).expect("hash-chain proof verifies");
    let t_verify = t.elapsed();

    assert_eq!(stats.counts[5], n, "one BLAKE3 row per chain step");

    println!(
        "\nBLAKE3 hash chain, N = {}, unroll = {}",
        pretty_integer(n),
        pretty_integer(unroll)
    );
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"]
        .iter()
        .zip(&stats.counts)
    {
        let pow = if c == 0 {
            "0".to_string()
        } else {
            format!("2^{:.3}", (c as f64).log2())
        };
        println!("    {name:<6} instructions       : {pow}");
    }
    println!(
        "  committed witness size      : 2^{:.3}",
        (stats.committed as f64).log2()
    );
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving (incl. witness gen) : {t_prove:?}");
    println!("  verifying                   : {t_verify:?}");
    let hashes_per_second = (n as f64 / t_prove.as_secs_f64()).round() as u64;
    println!(
        "  throughput                  : {} hashes/s",
        pretty_integer(hashes_per_second)
    );

    // A wrong public input must be rejected.
    let mut bad = pi;
    bad[0] += F192::ONE;
    assert!(verify(&program, &bad, &proof).is_err());
}
