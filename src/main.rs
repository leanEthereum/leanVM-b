//! Demo / benchmark: prove and verify Fibonacci in the exponent over a heap
//! `Array` — an unrolled `range` loop (`buff[g^k] = g^{F(k)}`, the recurrence
//! `buff[i·g²] = buff[i·g] · buff[i]`) — plus an `XOR` checksum over the buffer's
//! tail. The result `g^{F(N)}` is bound as the public input `m[0]`.

use std::time::Instant;

use leanvm_b::compiler::{compile, parse};
use leanvm_b::cpu::{prove, verify};
use leanvm_b::field::{F128, g_pow};

fn main() {
    const FIB_N: usize = 2_000_000;
    let (src, pi) = fibonacci_program(FIB_N);
    let program = compile(&parse(&src).unwrap());

    // println!("SOURCE\n\n{src}\n");
    // println!("COMPILED\n\n{program}\n");

    let t = Instant::now();
    let (proof, stats) = prove(&program, pi);
    let t_prove = t.elapsed();
    let t = Instant::now();
    verify(&program, &pi, &proof).unwrap();
    let t_verify = t.elapsed();

    println!("Fibonacci (in the exponent, i.e. modulo 2^128 - 1), N = {FIB_N}");
    println!("  cycles (VM steps)           : {}", stats.cycles);
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"].iter().zip(&stats.counts) {
        let pow = if c == 0 {
            "0".to_string()
        } else {
            format!("2^{:.3}", (c as f64).log2())
        };
        println!("    {name:<5} instructions        : {pow}");
    }
    println!(
        "  committed witness size      : 2^{:.3}",
        (stats.committed as f64).log2()
    );
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving (incl. witness gen) : {t_prove:?}");
    println!("  verifying                   : {t_verify:?}");
    println!(
        "  throughput                  : {:.0} cycles/s",
        stats.cycles as f64 / t_prove.as_secs_f64()
    );
}

/// Build the demo program: Fibonacci in the exponent over `fib_n` steps (an
/// unrolled `range` loop over a heap `Array`), an `XOR` checksum over the buffer
/// tail, and the result `g^{F(N)}` published into cell `m[0]`. Returns the zkDSL
/// source and the public input `[g^{F(N)}, 0]`.
fn fibonacci_program(fib_n: usize) -> (String, [F128; 2]) {
    const UNROLL: usize = 1000;
    const XORS: usize = 16;
    assert!(
        fib_n >= UNROLL && fib_n.is_multiple_of(UNROLL),
        "fib_n must be a positive multiple of {UNROLL}"
    );
    let k = fib_n / UNROLL; // number of blocks
    assert!(2 * k + 2 >= XORS, "fib_n too small for a {XORS}-cell checksum");

    // Run the recurrence in the field (the same one the VM runs in the exponent)
    // to pin the result g^{F(N)} (the public input) and an XOR (field sum)
    // checksum of the buffer's last `XORS` cells. Record every boundary pair
    // g^{F(jU)}, g^{F(jU+1)} the buffer holds, so the checksum matches.
    let mut cells = Vec::with_capacity(2 * k + 2);
    let (mut a, mut b) = (F128::ONE, g_pow(1)); // g^{F(0)}, g^{F(1)}
    cells.push(a);
    cells.push(b);
    for m in 1..=fib_n {
        let c = a * b;
        a = b;
        b = c; // (a, b) = (g^{F(m)}, g^{F(m+1)})
        if m % UNROLL == 0 {
            cells.push(a);
            cells.push(b);
        }
    }
    let pi = [a, F128::ZERO]; // a = g^{F(N)}: the result, then 0
    let cs = cells[cells.len() - XORS..].iter().fold(F128::ZERO, |acc, &v| acc + v);
    let checksum = ((cs.hi as u128) << 64) | cs.lo as u128;

    // `K` blocks: each reads its boundary pair into locals, runs `UNROLL`
    // Fibonacci `MUL`s in registers, and writes the next pair (4 DEREFs per
    // block). The counter advances by `×g²` (`range(0, 2K, 2)`).
    let mut body = String::from("        f0 = buff[i]\n        f1 = buff[i * GEN]\n");
    for j in 2..=UNROLL + 1 {
        body.push_str(&format!("        f{j} = f{} * f{}\n", j - 2, j - 1));
    }
    body.push_str(&format!("        buff[i * GEN ** 2] = f{UNROLL}\n"));
    body.push_str(&format!("        buff[i * GEN ** 3] = f{}\n", UNROLL + 1));

    // After the loop: XOR-fold the last `XORS` buffer cells into one accumulator
    // and assert it equals the checksum.
    let first = 2 * k + 2 - XORS; // first cell index of the folded tail
    let mut fold = format!("    s0 = buff[GEN ** {first}] + buff[GEN ** {}]\n", first + 1);
    for t in 1..XORS - 1 {
        fold.push_str(&format!("    s{t} = s{} + buff[GEN ** {}]\n", t - 1, first + t + 1));
    }
    fold.push_str(&format!("    assert s{} == {checksum}\n", XORS - 2));

    // Publish the result g^{F(N)} = buff[GEN ** {2K}] into cell m[0]: a pointer
    // whose value is g^0 (`p = 1`) addresses m[0] (`p[1] = m[1·g^0] = m[g^0]`),
    // and write-once forces m[0] to equal the seeded public input pi[0].
    let publish = format!("    p = 1\n    p[1] = buff[GEN ** {}]\n", 2 * k);

    let src = format!(
        "def main():\n\
        \x20   buff = Array({size})\n\
        \x20   buff[1] = 1\n\
        \x20   buff[GEN] = GEN\n\
        \x20   for i in range(0, {hi}, 2):\n\
        {body}\
        {fold}\
        {publish}\
        \x20   return\n",
        size = 2 * k + 2,
        hi = 2 * k,
    );
    (src, pi)
}
