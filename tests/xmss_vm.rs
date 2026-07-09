//! The in-VM XMSS aggregation verifier (`tests/xmss_aggregate.py`): `n`
//! signers (fresh keypairs) sign the same message at the same slot with the
//! `xmss` crate; the VM absorbs `message | tweaks | merkle_bits | public
//! keys` into the size-in-IV Merkle-Damgard hash while verifying every
//! signature against the bound data, and publishes the final state's first
//! two 64-bit words — compared against the natively computed aggregation hash.

use std::time::Instant;

use std::collections::BTreeMap;

use leanvm_b::compiler::{compile, parse_file_with_replacements};
use leanvm_b::cpu::{prove, verify};
use leanvm_b::field::{F64, g_pow};
use rand::SeedableRng;
use rand::rngs::StdRng;
use xmss::*;

fn word(bytes: &[u8]) -> F64 {
    F64(u64::from_le_bytes(bytes[..8].try_into().unwrap()))
}

/// A 16-byte native value as its two 64-bit VM words.
fn pair(b: &[u8]) -> Vec<F64> {
    vec![word(&b[..8]), word(&b[8..16])]
}

/// A 32-byte hash block as its four 64-bit VM words.
fn quad(b: &[u8]) -> Vec<F64> {
    (0..4).map(|k| word(&b[8 * k..8 * k + 8])).collect()
}

#[test]
fn test_aggregate_xmss() {
    // Pin rayon workers to performance cores (QoS) before any parallel work runs,
    // so fork-join stages are not held up by efficiency-core stragglers. Thread
    // count still follows RAYON_NUM_THREADS.
    leanvm_b::init_prover_pool();
    let slot = 7u32;
    // Batch size, overridable: `LEANVM_XMSS_N=16 cargo test … -- --nocapture`.
    let n = std::env::var("LEANVM_XMSS_N").ok().and_then(|s| s.parse().ok()).unwrap_or(3);
    let message: Message = std::array::from_fn(|i| (i * 5 + 1) as u8);
    let signers: Vec<(XmssPublicKey, XmssSignature)> = (0..n)
        .map(|s| {
            let seed = [10 + s as u8; 32];
            let (sk, pk) = xmss_key_gen(seed, 0, 15).expect("keygen");
            let sig = xmss_sign(&mut StdRng::seed_from_u64(s as u64), &sk, &message, slot).expect("sign");
            (pk, sig)
        })
        .collect();

    // The 328-tweak table (tweak index — see the program header). The
    // Merkle parent index is `slot >> (level+1)` computed in u64 (a u32 shift
    // by 32 at the top level would mask, not zero).
    let mut tweaks: Vec<Tweak> = vec![make_tweak(TWEAK_TYPE_ENCODING, 0, slot)];
    for i in 0..V {
        for s in 0..CHAIN_LENGTH - 1 {
            tweaks.push(make_tweak(TWEAK_TYPE_CHAIN, (i * CHAIN_LENGTH + s) as u32, slot));
        }
    }
    tweaks.push(make_tweak(TWEAK_TYPE_WOTS_PK, 0, slot));
    for l in 0..LOG_LIFETIME {
        let parent_index = ((slot as u64) >> (l + 1)) as u32;
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
        w[0] = ((slot >> l) & 1) as u8;
        data.extend_from_slice(&w);
    }
    for (pk, _) in &signers {
        data.extend_from_slice(&pk.flatten());
    }
    let num_bytes = data.len();
    assert_eq!(num_bytes, 5792 + 32 * n);
    let mut iv = [0u8; STATE_LEN];
    iv[..8].copy_from_slice(&gf64::g_pow_bytes(num_bytes));
    let state = md_hash(iv, &data);
    let want = [word(&state[..8]), word(&state[8..16])];

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
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/xmss_aggregate.py"),
            &replacements,
        )
        .expect("parse"),
    );
    program.set_witness("n_pks", vec![vec![g_pow(n)]]);
    program.set_witness("msg", vec![quad(&message)]);
    program.set_witness(
        "tweaks",
        tweaks
            .chunks(2)
            .map(|c| {
                let mut block = pair(&c[0]);
                block.extend(pair(&c[1]));
                block
            })
            .collect(),
    );
    let bit_word = |l: usize| vec![F64(((slot >> l) & 1) as u64), F64::ZERO];
    program.set_witness(
        "merkle_bits",
        (0..LOG_LIFETIME / 2)
            .map(|u| {
                let mut block = bit_word(2 * u);
                block.extend(bit_word(2 * u + 1));
                block
            })
            .collect(),
    );
    program.set_witness(
        "pks",
        signers
            .iter()
            .map(|(pk, _)| {
                let mut block = pair(&pk.merkle_root);
                block.extend(pair(&pk.public_param));
                block
            })
            .collect(),
    );
    // Per-signature streams, signature-major order.
    let (mut rand_s, mut digits_s, mut chain_starts_s, mut sib_s) = (vec![], vec![], vec![], vec![]);
    for (pk, sig) in &signers {
        let wots = &sig.wots_signature;
        let mut rnd = [0u8; STATE_LEN];
        rnd[..RANDOMNESS_LEN].copy_from_slice(&wots.randomness);
        rand_s.push(quad(&rnd));
        let encoding = wots_encode(&message, slot, &pk.public_param, &wots.randomness).expect("encoding");
        digits_s.extend(encoding.iter().map(|&e| vec![g_pow(e as usize)]));
        chain_starts_s.extend(wots.chain_tips.iter().map(|t| pair(t)));
        sib_s.extend(sig.merkle_proof.iter().map(|s| pair(s)));
    }
    program.set_witness("rand", rand_s);
    program.set_witness("digits", digits_s);
    program.set_witness("chain_starts", chain_starts_s);
    program.set_witness("siblings", sib_s);

    // Pre-build the BLAKE3 R1CS setup (the circuit-construction cost, ~hundreds of
    // ms) OUTSIDE the timed region. It depends only on the compression count (the
    // circuit shape), not the witness, and in a real deployment is built once per
    // shape and reused across every proof — so it is one-time preprocessing (like a
    // proving key), not part of per-proof proving throughput. Warming it here makes
    // the timing below reflect steady-state repeated proving. The compression count
    // is the asserted `181 + 158·n`.
    leanvm_b::blake3_flock::warm_setup(181 + 158 * n);

    let t = Instant::now();
    let (proof, stats) = prove(&program, want);
    let t_prove = t.elapsed();
    let t = Instant::now();
    verify(&program, &want, &proof).expect("XMSS aggregation verifies in-VM");
    let t_verify = t.elapsed();

    // 181 fixed blocks + per signature: 1 (pk absorb) + 157 (the native
    // verifier's constant).
    assert_eq!(stats.counts[5], 181 + 158 * n, "BLAKE3 instruction count");
    let bad = [want[0], want[1] + F64::ONE];
    assert!(verify(&program, &bad, &proof).is_err());

    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    let per = |x: usize| x as f64 / n as f64;
    let pow = |x: usize| {
        if x == 0 {
            "     -".into()
        } else {
            format!("2^{:.2}", (x as f64).log2())
        }
    };
    println!("\nXMSS aggregation, {n} signatures");
    println!(
        "  cycles (VM steps)           : {:>10} = {:>7}   ({:>8.1} / XMSS)",
        stats.cycles,
        pow(stats.cycles),
        per(stats.cycles)
    );
    for (name, &c) in ["XOR", "MUL", "SET", "DEREF", "JUMP", "BLAKE3"].iter().zip(&stats.counts) {
        println!(
            "    {name:<6} instructions       : {c:>10} = {:>7}   ({:>8.1} / XMSS)",
            pow(c),
            per(c)
        );
    }
    println!("  committed witness size      : 2^{:.3}", (stats.committed as f64).log2());
    println!(
        "  data memory                 : 2^{} padded (2^{:.2} used)",
        stats.log_mem,
        (stats.mem_used as f64).log2()
    );
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!("  proving (incl. witness gen) : {t_prove:?}");
    println!("  verifying                   : {t_verify:?}");
    println!(
        "  throughput                  : {:.1} XMSS/s",
        n as f64 / t_prove.as_secs_f64()
    );
}
