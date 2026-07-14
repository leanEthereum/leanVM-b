//! Standalone batch BLAKE3 proving, isolated from the VM.
//!
//! This exercises ONLY the flock "BLAKE3 stuff" over `N` compressions —
//! witness-gen → commit → [`Blake3Setup::prove_validity_stacked`] (zerocheck +
//! lincheck reduction, then the stacked Ligerito open) → verify — with no
//! leanVM execute / bus / constraints around it. Much faster to iterate on
//! than the full xmss benchmark when optimizing the flock reduction / PCS.
//!
//! `Blake3Setup::new` (circuit construction, one-time preprocessing
//! independent of the witness) runs OUTSIDE the timed region, matching how
//! `cpu::prove` warms it off the critical path. The Ligerito configuration is
//! the one leanVM-b commits with, so the numbers are comparable to the
//! `[open]` / `commit` stages of the xmss benchmark.
//!
//! Run (N = number of compressions; the xmss n=820 workload is ~130k = 181 + 158·820):
//! ```text
//!   RAYON_NUM_THREADS=11 FLOCK_N=131072 cargo test --release -p flock --test blake3_batch -- --nocapture
//! ```

use std::time::Instant;

use flock::blake3::{
    Blake3Setup, Compression, K_LOG, generate_witness_with_ab_packed_and_lincheck,
    min_n_blocks_log, pinned_compression,
};
use pcs::{Commitment, LOG_PACKING, PcsParams, ProverState, VerifierState};
use primitives::field::F128T;

/// Tiny deterministic xorshift RNG — no `rand` dep, reproducible inputs.
struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        (x.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 32) as u32
    }
}

/// A Merkle root as two field scalars, exactly as leanVM binds it (the root
/// rides the shared stream before any challenge).
fn root_to_scalars(root: &[u8; 32]) -> [F128T; 2] {
    let w = |o: usize| u64::from_le_bytes(root[o..o + 8].try_into().unwrap());
    [F128T::new(w(0), w(8)), F128T::new(w(16), w(24))]
}

fn scalars_to_root(s: &[F128T]) -> [u8; 32] {
    let mut root = [0u8; 32];
    root[0..8].copy_from_slice(&s[0].c0.to_le_bytes());
    root[8..16].copy_from_slice(&s[0].c1.to_le_bytes());
    root[16..24].copy_from_slice(&s[1].c0.to_le_bytes());
    root[24..32].copy_from_slice(&s[1].c1.to_le_bytes());
    root
}

#[test]
fn blake3_batch_prove_verify() {
    // Number of compressions to prove. Default is quick-but-meaningful; set
    // FLOCK_N=131072 to mirror the xmss n=820 BLAKE3 workload (~2^17).
    let n: usize = std::env::var("FLOCK_N").ok().and_then(|s| s.parse().ok()).unwrap_or(8192);
    assert!(n >= 1, "FLOCK_N must be ≥ 1");
    let n_log = min_n_blocks_log(n);
    // Committed q_pkd log-size; the Secure ladder needs some room.
    let mu = K_LOG + n_log - LOG_PACKING;
    assert!(mu >= 15, "FLOCK_N too small — need ≥ 2^8 compressions (mu ≥ 15)");

    // Deterministic sample compressions (arbitrary messages; the prover does
    // the same work regardless of values). cv/counter/blen/flags are pinned by
    // the circuit's constant rows.
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| {
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            pinned_compression(m)
        })
        .collect();

    // Circuit construction (one-time preprocessing) — OUTSIDE the timed region,
    // like cpu::prove's background warm. Warms the CSC lincheck circuit and the
    // prover scratch.
    let t = Instant::now();
    let setup = Blake3Setup::new(n);
    let setup_ms = t.elapsed().as_secs_f64() * 1e3;

    // The committed stack is q_pkd itself (offset 0, no other columns).
    let t = Instant::now();
    let q_pkd = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log).0;
    let witness_ms = t.elapsed().as_secs_f64() * 1e3;
    assert_eq!(q_pkd.len(), 1 << mu);

    let params = PcsParams {
        m: mu + LOG_PACKING,
        log_inv_rate: pcs::ligerito::LOG_INV_RATE_0,
        log_batch_size: pcs::ligerito::INITIAL_FOLDING_FATOR,
    };

    let mut ps = ProverState::new(b"flock-blake3-batch", &[]);
    let t_prove = Instant::now();
    let t = Instant::now();
    let (commitment, prover_data) = pcs::commit(&q_pkd, &params);
    ps.add_scalars(&pcs::merkle::hash_to_scalars(&commitment.root));
    let commit_ms = t.elapsed().as_secs_f64() * 1e3;

    // Reduction (zerocheck + lincheck) + the one stacked Ligerito open.
    let t = Instant::now();
    let proof =
        setup.prove_validity_stacked(&blocks, &q_pkd, 0, &prover_data, &commitment, &[], &mut ps);
    let open_ms = t.elapsed().as_secs_f64() * 1e3;
    let prove_s = t_prove.elapsed().as_secs_f64();
    let bundle = ps.into_proof();

    // Verify (correctness gate + a verify timing for reference).
    let t = Instant::now();
    let mut vs = VerifierState::new(b"flock-blake3-batch", &bundle, &[]);
    let root = pcs::merkle::scalars_to_hash(&vs.next_scalars(2).expect("root scalars"));
    let commitment_v = Commitment { root, params };
    setup
        .verify_validity_stacked(&commitment_v, 0, &[], &proof, &mut vs)
        .expect("flock BLAKE3 batch proof must verify");
    vs.finish().expect("stream fully consumed");
    let verify_ms = t.elapsed().as_secs_f64() * 1e3;

    println!("\nflock BLAKE3 batch proving, {n} compressions (2^{n_log} slots)");
    println!("  setup (preprocessing, excluded) : {setup_ms:>8.1} ms");
    println!("  witness-gen                     : {witness_ms:>8.1} ms");
    println!("  commit                          : {commit_ms:>8.1} ms");
    println!("  reduction + open                : {open_ms:>8.1} ms");
    println!("  ------------------------------------------");
    println!("  prove TOTAL (witness excluded)  : {:>8.1} ms", prove_s * 1e3);
    println!("  verify                          : {verify_ms:>8.1} ms");
    println!("  throughput                      : {:>10.0} compressions/s", n as f64 / prove_s);
    println!("  (~{:.0} XMSS/s equiv @ 158 compressions/sig)", n as f64 / prove_s / 158.0);
}
