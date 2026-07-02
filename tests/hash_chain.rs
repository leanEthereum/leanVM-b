//! A BLAKE3 hash chain, proven end-to-end.
//!
//! Starting from the 256-bit zero value `h_0 = 0…0`, each step compresses the
//! previous value (fed as both 256-bit operands, so `h_{i+1} = BLAKE3(h_i, h_i)`)
//! into the next. The final value `h_N` is published as the public input — the
//! first two memory words `m[0], m[1]` — and the last chain step writes its
//! output directly into those cells, so write-once memory forces the proven
//! result to equal the announced public input.
//!
//! The BLAKE3 compression is unproven (doc §7.6), so the proof certifies only the
//! memory / state / bytecode bus interactions: that the chain's reads and writes
//! are a consistent memory trace ending in the published cells.

use leanvm_b::cpu::{Op, Program, prove, verify};
use leanvm_b::field::F128;

/// Independent reference for one compression step, mirroring the VM's encoding:
/// the four input words `a0,a1,b0,b1` are laid little-endian (lo then hi) into 64
/// bytes, BLAKE3-hashed, and the 32-byte digest split back into two words.
fn compress(a: [F128; 2], b: [F128; 2]) -> [F128; 2] {
    let mut input = [0u8; 64];
    for (slot, w) in input.chunks_exact_mut(16).zip([a[0], a[1], b[0], b[1]]) {
        slot[..8].copy_from_slice(&w.lo.to_le_bytes());
        slot[8..].copy_from_slice(&w.hi.to_le_bytes());
    }
    let digest = blake3::hash(&input);
    let d = digest.as_bytes();
    let word = |b: &[u8]| {
        F128::new(
            u64::from_le_bytes(b[..8].try_into().unwrap()),
            u64::from_le_bytes(b[8..16].try_into().unwrap()),
        )
    };
    [word(&d[..16]), word(&d[16..])]
}

#[test]
fn blake3_hash_chain() {
    // N steps; N+1 is a power of two so the bytecode is exactly the N steps plus
    // one sentinel slot, with no filler instructions needed.
    const N: usize = 15;
    assert!((N + 1).is_power_of_two());

    // Reference chain: h[0] = 0…0, h[i+1] = BLAKE3(h[i], h[i]).
    let mut h = vec![[F128::ZERO; 2]; N + 1];
    for i in 0..N {
        h[i + 1] = compress(h[i], h[i]);
    }
    let pi = h[N]; // the published final value

    // Memory layout (fp = 0 throughout): h[i] lives in the two consecutive cells
    // (2+2i, 3+2i); h[0]'s cells are never written, so they read as 0 (= 0…0).
    // Step i hashes h[i] into h[i+1]; the final step (i = N-1) writes h[N] into
    // cells (0, 1), the public-input words.
    let cell = |i: usize| (2 + 2 * i) as u32;
    let mut prog: Vec<Op> = (0..N)
        .map(|i| {
            let out = if i + 1 == N { 0 } else { cell(i + 1) };
            Op::Blake3 {
                a: cell(i),
                b: cell(i),
                c: out,
            }
        })
        .collect();
    // Sentinel in the last slot (never executed; the run halts on reaching it).
    prog.push(Op::Xor { a: 0, b: 0, c: 0 });
    assert_eq!(prog.len(), N + 1);

    let main_frame = (2 * N + 2) as u32; // cells 0,1 and 2..=2N+1
    let program = Program::from_bytecode(prog, main_frame);

    // The run writes the final hash into m[0], m[1]; write-once would panic here
    // if our reference chain disagreed with the VM's computation.
    let exec = program.execute(pi);
    assert_eq!(exec.mem[0], pi[0]);
    assert_eq!(exec.mem[1], pi[1]);

    let (proof, stats) = prove(&program, pi);
    assert_eq!(stats.counts[5], N, "one BLAKE3 row per chain step");
    verify(&program, &pi, &proof).expect("hash-chain proof verifies");

    // A wrong public input must be rejected (the bound m[0],m[1] no longer match).
    let mut bad = pi;
    bad[0] += F128::ONE;
    assert!(verify(&program, &bad, &proof).is_err());
}
