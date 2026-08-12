//! The in-VM XMSS aggregation verifier (`guests/xmss_aggregate.py`): `n`
//! signers (fresh keypairs) sign the same message at the same epoch with the
//! `xmss` crate; the VM absorbs `message | tweaks | merkle_bits | public
//! keys` into a protocol-specific runtime-length accumulator while verifying every
//! signature against the bound data, and publishes the final 32-byte state —
//! compared against the natively computed aggregation hash.

use std::collections::BTreeMap;

use lean_compiler::{compile, parse_file_with_replacements};
use lean_vm::cpu::{prove, verify};
use primitives::{
    bench::Plan,
    field::{F64, F192, g_pow},
    pretty_f64, pretty_integer,
};
use xmss::*;

use crate::signers_cache;

fn word(bytes: &[u8]) -> F64 {
    F64(u64::from_le_bytes(bytes[..8].try_into().unwrap()))
}

/// A K-embedded F192 cell for count/digit hints, which are g-powers.
fn cell(w: F64) -> F192 {
    F192::from(w)
}

/// A 16-byte native value in the canonical BLAKE2s subspace of F192: `c0`
/// carries bytes 0..8, `c1` bytes 8..16, and `c2` is zero.
fn val16(b: &[u8]) -> F192 {
    F192::new(word(&b[..8]).0, word(&b[8..16]).0, 0)
}

/// A 16-byte native value as ONE cell.
fn pair(b: &[u8]) -> Vec<F192> {
    vec![val16(b)]
}

/// A 32-byte hash block as two canonical 128-bit BLAKE2s cells.
fn quad(b: &[u8]) -> Vec<F192> {
    vec![val16(&b[..16]), val16(&b[16..32])]
}

/// Protocol-specific streaming binding used only by the runtime-sized XMSS
/// aggregation benchmark. Unlike XMSS/PCS slice hashing, this is not exposed
/// as a general hash construction: a runtime chunk counter cannot be placed in
/// the VM's deliberately compile-time BLAKE2s metadata immediate.
fn aggregate_binding(mut state: [u8; STATE_LEN], data: &[u8]) -> [u8; STATE_LEN] {
    assert!(data.len().is_multiple_of(STATE_LEN));
    for block in data.chunks_exact(STATE_LEN) {
        let mut input = [0u8; 2 * STATE_LEN];
        input[..STATE_LEN].copy_from_slice(&state);
        input[STATE_LEN..].copy_from_slice(block);
        state = primitives::blake2s::hash(&input);
    }
    state
}

/// Aggregate `n` XMSS signatures inside the VM and verify the proof: signs
/// natively with the `xmss` crate, runs the in-VM aggregation verifier
/// (`guests/xmss_aggregate.py`) over all signatures, proves, verifies, and
/// prints the benchmark report.
///
/// Proving runs one discarded warmup pass followed by `plan.repeat` measured
/// passes; see [`primitives::bench`] for why the first pass is not
/// representative and why the cooldown matters.
pub fn run_xmss_aggregation(n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("XMSS aggregation", n, log_inv_rate).entered();

    // Spawn the worker pool before any timed work, so no kernel pays the spawn
    // cost. Opting into the arena is the calling *process's* decision (one region,
    // one proof at a time), so it stays in `main`, not here.
    lean_vm::init_prover_pool();
    let epoch = signers_cache::EPOCH;
    let message: Message = signers_cache::message();
    // Generated once and cached to disk; see `signers_cache`.
    let signers = signers_cache::get_signers(n);

    // The 328-tweak table (tweak index — see the program header). The
    // Merkle parent index is `epoch >> (level+1)` computed in u64 (a u32 shift
    // by 32 at the top level would mask, not zero).
    let mut tweaks: Vec<Tweak> = vec![make_tweak(TWEAK_TYPE_ENCODING, 0, epoch)];
    for i in 0..V {
        for s in 0..CHAIN_LENGTH - 1 {
            tweaks.push(make_tweak(TWEAK_TYPE_CHAIN, (i * CHAIN_LENGTH + s) as u32, epoch));
        }
    }
    tweaks.push(make_tweak(TWEAK_TYPE_WOTS_PK, 0, epoch));
    for l in 0..LOG_LIFETIME {
        let parent_index = ((epoch as u64) >> (l + 1)) as u32;
        tweaks.push(make_tweak(TWEAK_TYPE_MERKLE, (l + 1) as u32, parent_index));
    }
    assert_eq!(tweaks.len(), 328);

    // The natively computed aggregation hash.
    let mut data = Vec::new();
    data.extend_from_slice(&message);
    for t in &tweaks {
        data.extend_from_slice(t);
    }
    for l in 0..LOG_LIFETIME {
        let mut w = [0u8; 16];
        w[0] = ((epoch >> l) & 1) as u8;
        data.extend_from_slice(&w);
    }
    for (pk, _) in &signers {
        data.extend_from_slice(&pk.flatten());
    }
    let num_bytes = data.len();
    assert_eq!(num_bytes, 5792 + 32 * n);
    let mut iv = [0u8; STATE_LEN];
    iv[..8].copy_from_slice(&g_pow(num_bytes).0.to_le_bytes());
    let state = aggregate_binding(iv, &data);
    // The guest publishes the final binding state's two 128-bit cells (32 bytes).
    let want = [val16(&state[..16]), val16(&state[16..32])];

    // The XMSS instance parameters, injected into the program's placeholders;
    // every derived size (tweak-table width, IV byte counts, …) is computed
    // from these by the DSL's compile-time integer arithmetic.
    let replacements = BTreeMap::from([
        ("V_PLACEHOLDER".to_string(), V.to_string()),
        ("W_PLACEHOLDER".to_string(), W.to_string()),
        ("TARGET_SUM_PLACEHOLDER".to_string(), TARGET_SUM.to_string()),
        ("LOG_LIFETIME_PLACEHOLDER".to_string(), LOG_LIFETIME.to_string()),
    ]);
    let mut program = compile(
        &parse_file_with_replacements(
            concat!(env!("CARGO_MANIFEST_DIR"), "/guests/xmss_aggregate.py"),
            &replacements,
        )
        .expect("parse"),
    );
    program.set_witness("n_pks", vec![vec![cell(g_pow(n))]]);
    program.set_witness("msg", vec![quad(&message)]);
    program.set_witness(
        "tweaks",
        tweaks.chunks(2).map(|c| vec![val16(&c[0]), val16(&c[1])]).collect(),
    );
    // Two Merkle epoch bits per block, each one 16-byte cell (bit in the low byte, rest zero).
    program.set_witness(
        "merkle_bits",
        (0..LOG_LIFETIME / 2)
            .map(|u| {
                vec![
                    cell(F64(((epoch >> (2 * u)) & 1) as u64)),
                    cell(F64(((epoch >> (2 * u + 1)) & 1) as u64)),
                ]
            })
            .collect(),
    );
    program.set_witness(
        "pks",
        signers
            .iter()
            .map(|(pk, _)| vec![val16(&pk.merkle_root), val16(&pk.public_param)])
            .collect(),
    );
    // Per-signature streams, signature-major order.
    let (mut rand_s, mut digits_s, mut chain_starts_s, mut sib_s) = (vec![], vec![], vec![], vec![]);
    for (pk, sig) in &signers {
        let wots = &sig.wots_signature;
        let mut rnd = [0u8; STATE_LEN];
        rnd[..RANDOMNESS_LEN].copy_from_slice(&wots.randomness);
        rand_s.push(quad(&rnd));
        let encoding = wots_encode(&message, epoch, &pk.public_param, &wots.randomness).expect("encoding");
        digits_s.extend(encoding.iter().map(|&e| vec![cell(g_pow(e as usize))]));
        chain_starts_s.extend(wots.chain_tips.iter().map(|t| pair(t)));
        sib_s.extend(sig.merkle_proof.iter().map(|s| pair(s)));
    }
    program.set_witness("rand", rand_s);
    program.set_witness("digits", digits_s);
    program.set_witness("chain_starts", chain_starts_s);
    program.set_witness("siblings", sib_s);

    // Pre-build the BLAKE2s R1CS setup (the circuit-construction cost, ~hundreds of
    // ms) OUTSIDE the timed region. It depends only on the compression count (the
    // circuit shape), not the witness, and in a real deployment is built once per
    // shape and reused across every proof — so it is one-time preprocessing (like a
    // proving key), not part of per-proof proving throughput. Warming it here makes
    // the timing below reflect steady-state repeated proving. The compression count
    // is `181 + 145·n`: 181 aggregation-prefix blocks, then per signature
    // one aggregate absorb + 2 encoding + 99 WOTS-chain + 11 WOTS-pubkey +
    // 32 Merkle-parent compressions.
    lean_vm::blake2s_flock::warm_setup(181 + 145 * n);

    // Only the final measured pass of each stage is traced (see `run_recursion`).
    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        prove(&program, want, log_inv_rate)
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        verify(&program, &want, &proof).expect("XMSS aggregation verifies in-VM");
    });

    assert_eq!(stats.base_counts[5], 181 + 145 * n, "BLAKE2s instruction count");
    let bad = [want[0], want[1] + F192::ONE];
    assert!(verify(&program, &bad, &proof).is_err());

    let per = |x: usize| pretty_f64(x as f64 / n as f64);
    drop(trace_span);

    println!("\nXMSS aggregation, {} signatures", pretty_integer(n));
    // The program's own work, then what gets proven: the fill blocks bring each table
    // to a power of two so that none needs padding rows, so the proven total is the sum
    // of those powers.
    let base_cycles: usize = stats.base_counts.iter().sum();
    println!(
        "  cycles (VM steps)           : {} = {}   ({} / XMSS)",
        pretty_integer(base_cycles),
        crate::report::pow(base_cycles),
        per(base_cycles)
    );
    println!(
        "    proven rows               : {} = {}  (filled to powers of two)",
        pretty_integer(stats.cycles),
        crate::report::pow(stats.cycles)
    );
    println!("    details                   : {}", stats.details());
    crate::report::print_proof_size(&proof);
    println!(
        "  proving                     : {} s{}   {} XMSS/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_f64(n as f64 / prove_time.mean()),
        crate::report::peak_gib()
    );
    println!("  verifying                   : {} s", pretty_f64(verify_time.mean()));
}

#[cfg(test)]
mod tests {
    /// Batch size overridable: `LEANVM_XMSS_N=820 cargo test … -- --nocapture`.
    #[test]
    fn aggregate_xmss() {
        let n = std::env::var("LEANVM_XMSS_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);
        super::run_xmss_aggregation(n, lean_vm::pcs::LOG_INV_RATE, primitives::bench::Plan::default());
    }
}
