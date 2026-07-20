//! Standalone batch BLAKE3 proving, isolated from the VM.
//!
//! This exercises only Flock's BLAKE3 path over `N` compressions: witness
//! generation, F64 commitment, zerocheck + lincheck reduction, the stacked
//! ring-switch/Ligerito opening, and verification. Circuit construction is
//! outside the timed region, matching the VM's warmed-setup convention.
//!
//! Run with the XMSS-sized workload:
//! ```text
//! RAYON_NUM_THREADS=11 FLOCK_N_LOG=17 cargo test --release -p flock --test blake3_batch -- --ignored --nocapture
//! ```

use std::time::Instant;

use fiat_shamir::transcript::{ProverState, VerifierState};
use flock::blake3::{
    Blake3Setup, Compression, K_LOG, ReducedClaims, generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
    pinned_compression,
};
use flock::proof::ZClaim;
use pcs::ligerito::{INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0};
use pcs::ligerito::{commit, configs_for};
use pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use pcs::stack_open::{
    RingSwitchClaim, RingSwitchOpen, RingSwitchVerify, open_batch_mixed_ligerito_stacked,
    verify_opening_batch_mixed_ligerito_stacked,
};
use primitives::multilinear::lagrange_weights_naive;
use primitives::{
    field::{F64, F192},
    pretty_integer,
};

/// Tiny deterministic xorshift RNG: reproducible inputs without another dep.
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

/// Split the two K coefficients of each packed tower element. Flock's fused
/// witness generator uses 128-bit containers; the PCS commits 64 bits/word.
fn flatten_packed(packed: &[F192]) -> Vec<F64> {
    let mut out = Vec::with_capacity(2 * packed.len());
    for value in packed {
        out.push(F64(value.c0));
        out.push(F64(value.c1));
    }
    out
}

/// Adapt one Flock evaluation claim to the 64-bit ring switch. Lincheck
/// captures its 64 slices directly; the fused zerocheck kernel captures two
/// banks around the first suffix coordinate, which are folded here.
fn ring_claim(z: &ZClaim, captured: Option<&[F192]>, qpkd_vars: usize) -> RingSwitchClaim {
    let mut suffix_point = z.point.x_inner_rest.clone();
    suffix_point.extend_from_slice(&z.point.x_outer);
    assert_eq!(suffix_point.len(), qpkd_vars);

    let s_hat_v = captured.and_then(|s| match s.len() {
        PACKING_WIDTH => Some(s.to_vec()),
        n if n == 2 * PACKING_WIDTH && !z.point.x_inner_rest.is_empty() => {
            let c = z.point.x_inner_rest[0];
            Some(
                (0..PACKING_WIDTH)
                    .map(|i| (F192::ONE + c) * s[i] + c * s[i + PACKING_WIDTH])
                    .collect(),
            )
        }
        _ => None,
    });

    RingSwitchClaim {
        prefix_weights: lagrange_weights_naive(LOG_PACKING, z.point.z_skip),
        suffix_point,
        value: z.value,
        s_hat_v,
    }
}

fn prover_ring(reduced: &ReducedClaims, qpkd_vars: usize) -> RingSwitchOpen {
    RingSwitchOpen {
        offset: 0,
        qpkd_vars,
        claims: vec![
            ring_claim(&reduced.ab.claim, reduced.ab.s_hat_v.as_deref(), qpkd_vars),
            ring_claim(&reduced.c.claim, reduced.c.s_hat_v.as_deref(), qpkd_vars),
        ],
    }
}

fn verifier_ring(ab: &ZClaim, c: &ZClaim, qpkd_vars: usize) -> RingSwitchVerify {
    RingSwitchVerify {
        offset: 0,
        qpkd_vars,
        claims: vec![ring_claim(ab, None, qpkd_vars), ring_claim(c, None, qpkd_vars)],
    }
}

#[test]
#[ignore = "manual release benchmark; needs a large-stack worker and substantial memory"]
fn blake3_batch_prove_verify() {
    // The XMSS n=820 workload executes about 2^17 BLAKE3 compressions.
    let requested_n_log: usize = std::env::var("FLOCK_N_LOG")
        .ok()
        .map(|s| s.parse().expect("FLOCK_N_LOG must be an integer"))
        .unwrap_or(13);
    let n = 1usize
        .checked_shl(requested_n_log as u32)
        .expect("FLOCK_N_LOG exceeds the platform usize width");
    let n_log = min_n_blocks_log(n);
    let mu = K_LOG + n_log - LOG_PACKING;
    assert!(
        mu >= 15,
        "FLOCK_N_LOG too small: need a committed witness with mu >= 15"
    );

    let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ n as u64);
    let blocks: Vec<Compression> = (0..n)
        .map(|_| pinned_compression(std::array::from_fn(|_| rng.next_u32())))
        .collect();

    let t = Instant::now();
    let setup = Blake3Setup::new(n);
    let setup_ms = t.elapsed().as_secs_f64() * 1e3;

    let t = Instant::now();
    let (z_packed, a_packed, b_packed, z_lincheck) =
        generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
    let q_pkd = flatten_packed(&z_packed);
    let witness_ms = t.elapsed().as_secs_f64() * 1e3;
    assert_eq!(q_pkd.len(), 1 << mu);

    let (prover_config, verifier_config) = configs_for(mu).expect("Ligerito configuration");
    let mut ps = ProverState::<()>::new(b"flock-blake3-batch", &[]);
    let t_prove = Instant::now();

    let t = Instant::now();
    let (commitment, prover_data) = commit(&q_pkd, INITIAL_FOLDING_FACTOR, LOG_INV_RATE_0);
    ps.add_scalars(&pcs::merkle::hash_to_scalars(&commitment.root));
    let commit_ms = t.elapsed().as_secs_f64() * 1e3;

    let t = Instant::now();
    let reduced = setup.prove_reduction_precomputed(
        &z_packed,
        &a_packed,
        &b_packed,
        &z_lincheck,
        &mut ps,
    );
    drop((z_packed, a_packed, b_packed, z_lincheck));
    let ring = prover_ring(&reduced, mu);
    let opening = open_batch_mixed_ligerito_stacked(ps.sponge_mut(), &q_pkd, &prover_data, &prover_config, &[], &ring);
    let open_ms = t.elapsed().as_secs_f64() * 1e3;
    let prove_s = t_prove.elapsed().as_secs_f64();
    let transcript = ps.into_proof();

    let t = Instant::now();
    let mut vs = VerifierState::<()>::new(b"flock-blake3-batch", &transcript, &[]);
    let root = pcs::merkle::scalars_to_hash(&vs.next_scalars(2).expect("commitment root"));
    let replay = setup.verify_reduction(&mut vs).expect("Flock reduction verifies");
    let ring = verifier_ring(&replay.ab, &replay.c, mu);
    verify_opening_batch_mixed_ligerito_stacked(vs.sponge_mut(), &verifier_config, mu, &root, &[], &ring, &opening)
        .expect("stacked PCS opening verifies");
    vs.finish().expect("transcript fully consumed");
    let verify_ms = t.elapsed().as_secs_f64() * 1e3;

    println!(
        "\nFlock BLAKE3 batch proving, {} compressions (2^{n_log} slots)",
        pretty_integer(n)
    );
    println!("  setup (preprocessing, excluded) : {setup_ms:>8.1} ms");
    println!("  witness-gen                     : {witness_ms:>8.1} ms");
    println!("  commit                          : {commit_ms:>8.1} ms");
    println!("  reduction + open                : {open_ms:>8.1} ms");
    println!("  ------------------------------------------");
    println!("  prove TOTAL (witness excluded)  : {:>8.1} ms", prove_s * 1e3);
    println!("  verify                          : {verify_ms:>8.1} ms");
    let compressions_per_second = (n as f64 / prove_s).round() as u64;
    println!(
        "  throughput                      : {:>14} compressions/s",
        pretty_integer(compressions_per_second)
    );
    println!(
        "  (~{:.1} XMSS/s equivalent at 158 compressions/signature)",
        n as f64 / prove_s / 158.0
    );
}
