//! Standalone benchmark for the flock BLAKE3 R1CS prover, isolated from the VM.
//!
//! This exercises ONLY the flock "BLAKE3 stuff" — `Blake3Setup::prove_fast`
//! (witness-gen → commit → zerocheck → lincheck → Ligerito open) over `N`
//! compressions, with no leanVM execute / bus / constraints around it. Much
//! faster to iterate on than the full `xmss_vm` test when optimizing the flock
//! reduction / PCS.
//!
//! `Blake3Setup::new` (the R1CS circuit construction, ~hundreds of ms, one-time
//! preprocessing independent of the witness) is built OUTSIDE the timed region,
//! matching how `cpu::prove` warms it off the critical path.
//!
//! Uses the `Secure` Ligerito profile — the same one leanVM-b commits with
//! (`pcs::PROFILE`) — so the numbers are comparable to the `[open]` / `commit`
//! stages of the `xmss_vm` benchmark.
//!
//! Run (N = number of compressions; the xmss n=820 workload is ~130k = `181 + 158·820`):
//! ```text
//!   RAYON_NUM_THREADS=11 FLOCK_N=131072 cargo test --release --test blake3_bench -- --nocapture
//! ```

use std::time::Instant;

use flare::pcs::ligerito::LigeritoProfile;
use flock_prover::r1cs_hashes::blake3::{Blake3Setup, Compression, pinned_compression};

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

#[test]
fn bench_blake3_prove() {
    // Number of compressions to prove. Default is a quick-but-meaningful size;
    // set FLOCK_N=131072 to mirror the xmss n=820 BLAKE3 workload (~2^17).
    let n: usize = std::env::var("FLOCK_N").ok().and_then(|s| s.parse().ok()).unwrap_or(8192);
    assert!(n >= 1, "FLOCK_N must be ≥ 1");

    // Ligerito profile. DEFAULT `secure` matches leanVM-b's `pcs::PROFILE` (120-bit,
    // more queries). The flock repo's `blake3_proof` bench uses `Blake3Setup::new`,
    // which is `fast` (100-bit) — set FLOCK_PROFILE=fast to compare like-for-like.
    let (profile, profile_name) = match std::env::var("FLOCK_PROFILE").as_deref() {
        Ok("fast") => (LigeritoProfile::Fast, "Fast (100-bit)"),
        Ok("slim") => (LigeritoProfile::Slim, "Slim"),
        _ => (LigeritoProfile::Secure, "Secure (120-bit)"),
    };
    // Warm best-of-N proving, to match `cargo bench`/criterion (which reports the
    // best of many warmed iterations) rather than a single cold run. FLOCK_REPS≥3
    // gives a comparable steady-state number.
    let reps: usize = std::env::var("FLOCK_REPS").ok().and_then(|s| s.parse().ok()).unwrap_or(1).max(1);

    // Deterministic sample compressions (arbitrary message; the prover does the
    // same work regardless of the values). cv/counter/blen/flags are pinned by
    // the circuit's constant rows.
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| {
            let m: [u32; 16] = std::array::from_fn(|_| rng.next_u32());
            pinned_compression(m)
        })
        .collect();

    // Circuit construction (one-time preprocessing) — OUTSIDE the timed region,
    // like cpu::prove's background warm. The constructor warms the CSC lincheck
    // circuit + scratch; we also warm the statement digest (which `bind_statement`
    // needs on the first prove) so the timed run reflects steady-state proving —
    // exactly what `blake3_flock::warm_setup` does for the VM path.
    let t_setup = Instant::now();
    let setup = Blake3Setup::with_profile(n, profile);
    let _ = setup.r1cs.statement_digest();
    let setup_ms = t_setup.elapsed().as_secs_f64() * 1e3;

    // Timed proving: best of `reps` warmed iterations (with per-phase breakdown).
    let mut best = f64::INFINITY;
    let mut best_timings = None;
    let mut last = None;
    for _ in 0..reps {
        let mut ch = flare::challenger::FsChallenger::new(b"flock-blake3-bench");
        let t = Instant::now();
        let (proof, commitment, _claim, timings) = setup.prove_fast_timed(&blocks, &mut ch);
        let secs = t.elapsed().as_secs_f64();
        if secs < best {
            best = secs;
            best_timings = Some(timings);
        }
        last = Some((proof, commitment));
    }
    let secs = best;
    let timings = best_timings.expect("≥1 rep");

    // Verify (correctness gate + a verify timing for reference).
    let (proof, commitment) = last.expect("≥1 rep");
    let mut ch_v = flare::challenger::FsChallenger::new(b"flock-blake3-bench");
    let t = Instant::now();
    setup.verify(&commitment, &proof, &mut ch_v).expect("flock BLAKE3 proof must verify");
    let verify = t.elapsed();

    let ms = |s: f64| s * 1e3;
    println!("\nflock BLAKE3 proving ({profile_name}), {n} compressions, best of {reps}");
    println!("  setup (preprocessing, excluded) : {setup_ms:>8.1} ms");
    println!("  witness-gen                     : {:>8.1} ms", ms(timings.witness_s));
    println!("  commit                          : {:>8.1} ms", ms(timings.commit_s));
    println!("  zerocheck                       : {:>8.1} ms", ms(timings.zerocheck_s));
    println!("  lincheck                        : {:>8.1} ms", ms(timings.lincheck_s));
    println!("  open (Ligerito)                 : {:>8.1} ms", ms(timings.open_s));
    println!("  ------------------------------------------");
    println!("  prove TOTAL                     : {:>8.1} ms", ms(secs));
    println!("  verify                          : {:>8.1} ms", ms(verify.as_secs_f64()));
    println!("  throughput                      : {:>10.0} compressions/s", n as f64 / secs);
    println!("  (~{:.0} XMSS/s equiv @ 158 compressions/sig)", n as f64 / secs / 158.0);
}
