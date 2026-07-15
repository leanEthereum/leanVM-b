//! Fibonacci in the exponent: the demo benchmark (`buff[g^k] = g^{F(k)}`,
//! recurrence `buff[i·g²] = buff[i·g] · buff[i]`).

use std::time::Instant;

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

/// Prove and verify Fibonacci-in-the-exponent over a `HeapBuf` (an unrolled
/// `mul_range` recurrence), binding `g^{F(n)}` as the public input. Prints the
/// benchmark report.
pub fn run_fibonacci(n: usize) {
    let (src, pi) = fibonacci_program(n);
    let program = compile(&parse(&src).unwrap());

    // Warm the flock BLAKE3 R1CS setup once up front (Fibonacci runs no BLAKE3, so
    // this warms the single padding instance). It is a fixed, one-time,
    // program-independent circuit build — not part of proving — so timing prove/
    // verify below reflects steady-state performance.
    lean_vm::blake3_flock::warm_setup(0);

    let t = Instant::now();
    let (proof, stats) = prove(&program, pi);
    let t_prove = t.elapsed();
    let t = Instant::now();
    verify(&program, &pi, &proof).unwrap();
    let t_verify = t.elapsed();

    println!("Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = {n}");
    println!("  cycles (VM steps)           : {}", stats.cycles);
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"]
        .iter()
        .zip(&stats.counts)
    {
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
/// unrolled `mul_range` loop over a `HeapBuf`), with the result `g^{F(N)}`
/// published into cell `m[0]`. Returns the zkDSL source and the public input
/// `[g^{F(N)}, 0]`.
fn fibonacci_program(fib_n: usize) -> (String, [F192; 2]) {
    const UNROLL: usize = 1000;
    assert!(
        fib_n >= UNROLL && fib_n.is_multiple_of(UNROLL),
        "fib_n must be a positive multiple of {UNROLL}"
    );
    let k = fib_n / UNROLL; // number of blocks

    // Run the recurrence in the field (the same one the VM runs in the exponent)
    // to pin the result g^{F(N)}, the public input.
    let (mut a, mut b) = (F64::ONE, g_pow(1)); // g^{F(0)}, g^{F(1)}
    for _ in 1..=fib_n {
        let c = a * b;
        a = b;
        b = c; // (a, b) = (g^{F(m)}, g^{F(m+1)})
    }
    let pi = [F192::from(a), F192::ZERO]; // a = g^{F(N)}: the result, then 0

    // `K` blocks: each reads its boundary pair into locals, runs `UNROLL`
    // Fibonacci `MUL`s in registers, and writes the next pair (4 DEREFs per
    // block). The loop counter `x = gʲ` is the block index (×g each iteration);
    // block `j`'s boundary pair lives at cells `g^{2j}, g^{2j+1}`, so its base is
    // `b = x·x = g^{2j}`.
    let mut body = String::from("        b = x * x\n        f0 = buff[b]\n        f1 = buff[b * GEN]\n");
    for j in 2..=UNROLL + 1 {
        body.push_str(&format!("        f{j} = f{} * f{}\n", j - 2, j - 1));
    }
    body.push_str(&format!("        buff[b * GEN ** 2] = f{UNROLL}\n"));
    body.push_str(&format!("        buff[b * GEN ** 3] = f{}\n", UNROLL + 1));

    // Publish the result g^{F(N)} = buff[GEN ** {2K}] into cell m[0]: a pointer
    // whose value is g^0 (`p = 1`) addresses m[0] (`p[1] = m[1·g^0] = m[g^0]`),
    // and write-once forces m[0] to equal the seeded public input pi[0].
    let publish = format!("    p = 1\n    p[1] = buff[GEN ** {}]\n", 2 * k);

    let src = format!(
        "def main():\n\
        \x20   buff = HeapBuf({size})\n\
        \x20   buff[1] = 1\n\
        \x20   buff[GEN] = GEN\n\
        \x20   for x in mul_range(1, GEN ** {k}):\n\
        {body}\
        {publish}\
        \x20   return\n",
        size = 2 * k + 2,
    );
    (src, pi)
}

#[cfg(test)]
mod tests {
    #[test]
    fn fibonacci() {
        super::run_fibonacci(200_000);
    }
}
