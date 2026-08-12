//! BLAKE2s hash chain, written in the zkDSL and proven end-to-end.
//!
//! Starting from `h_0 = 0…0` (256 bits), each step is `h_{i+1} = BLAKE2s(h_i,
//! h_i)` (the previous value fed as both 256-bit operands). The program mirrors
//! the Fibonacci demo's strategy: a `mul_range` loop *in the exponent* on the
//! outside, an unrolled block of `BLAKE2s` steps on the inside, with the chain
//! state carried through a `HeapBuf` (write-once memory). The four 64-bit digest
//! lanes of the final `h_N` are packed into two canonical 128-bit BLAKE2s cells
//! embedded in the F192 public input;
//! write-once memory forces the proven result to equal it.
//!
//! `N` and the unroll factor are read from the environment (`LEANVM_HASH_N`,
//! `LEANVM_HASH_UNROLL`) so this doubles as a benchmark:
//! `LEANVM_HASH_N=10000 LEANVM_HASH_UNROLL=1000 cargo test --release
//! -p rec_aggregation blake2s_hash_chain -- --nocapture`. It prints cycles,
//! per-table sizes, proof size, prove/verify time, and hashes/second, like
//! `src/main.rs`.

use std::time::Instant;

use lean_compiler::{compile, compile_without_filler, parse};
use lean_vm::blake2s_flock::warm_setup;
use lean_vm::cpu::{prove, verify};
use lean_vm::vmhash::compress;
use primitives::{
    field::{F64, F192},
    pretty_f64, pretty_integer,
};

/// The program's own instruction mix: a build without the fill blocks, executed but not
/// proven. Proving needs them, since a table's height has to be a power of two with no
/// padding rows, but their dummy rows would drown out exactly what these counts are
/// measuring.
fn mix(src: &str, pi: [F192; 2]) -> [usize; lean_vm::cpu::Stats::TABLES.len()] {
    compile_without_filler(&parse(src).expect("parse"))
        .execute(pi)
        .base_counts
}

/// Build the zkDSL source for an `n`-step chain unrolled `unroll` per outer
/// iteration (`k = n / unroll` iterations). Layout in the heap `buff`: the chain
/// value after `j·unroll` steps sits at cells `2j, 2j+1`. Each outer step loads
/// that pair into a size-2 `StackBuf`, runs `unroll` `BLAKE2s`s in the stack —
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
    // A 256-bit BLAKE2s value occupies two canonical 128-bit cells. Block `j`'s
    // boundary value sits at cells `g^{2j}..g^{2j+1}`; the loop counter `i = gʲ`
    // is the block index (×g each iteration), so the value base is `b = i²`.
    // Load the current chain value into a size-2 StackBuf (heap read straight
    // into the two consecutive stack cells).
    body.push_str("        b = i * i\n");
    body.push_str("        h0 = StackBuf(2)\n");
    body.push_str("        h0[0] = buff[b]\n");
    body.push_str("        h0[1] = buff[b * GEN]\n");
    // `unroll` self-hashes; each `blake2s` reads its operand stack in place and
    // writes into the next pre-allocated size-2 stack — no copies between steps.
    for s in 1..=unroll {
        body.push_str(&format!("        h{s} = StackBuf(2)\n"));
        body.push_str(&format!("        blake2s(h{p}, h{p}, h{s})\n", p = s - 1));
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
fn blake2s_hash_chain() {
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
    // The two published BLAKE2s cells of h_N (top F192 limb zero).
    let pi = [F192::new(h[0].0, h[1].0, 0), F192::new(h[2].0, h[3].0, 0)];

    let program = compile(&parse(&chain_source(n, unroll)).expect("parse"));

    // Pay the one-time, circuit-shape-only flock setup (build + hash the BLAKE2s
    // R1CS) up front so the timed prove/verify below reflect steady-state,
    // repeated-proving cost rather than the cold start.
    warm_setup(n);

    let t = Instant::now();
    let (proof, stats) = prove(&program, pi, lean_vm::pcs::LOG_INV_RATE);
    let t_prove = t.elapsed();
    let t = Instant::now();
    verify(&program, &pi, &proof).expect("hash-chain proof verifies");
    let t_verify = t.elapsed();

    assert_eq!(
        mix(&chain_source(n, unroll), pi)[5],
        n,
        "one BLAKE2s row per chain step"
    );

    println!(
        "\nBLAKE2s hash chain, N = {}, unroll = {}",
        pretty_integer(n),
        pretty_integer(unroll)
    );
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE2S", "PACK64X2"]
        .iter()
        .zip(&stats.counts)
    {
        let pow = if c == 0 {
            "0".to_string()
        } else {
            format!("2^{}", pretty_f64((c as f64).log2()))
        };
        println!("    {name:<6} instructions       : {pow}");
    }
    println!(
        "  committed witness size      : 2^{:.3}",
        (stats.committed as f64).log2()
    );
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving                     : {t_prove:?}");
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
