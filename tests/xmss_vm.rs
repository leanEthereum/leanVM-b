//! Stage 1 of the in-VM XMSS verifier: the WOTS core (`tests/xmss_wots.py`).
//! A real signature is produced natively with the `xmss` crate; its pieces
//! become the program's witness streams; the VM re-derives the encoding
//! digest, checks the hinted digits (range, target sum in the exponent, and
//! the monomial-subspace reconstruction against the digest), walks the 42
//! chains, hashes the tips, and publishes (Merkle leaf, encoding digest) —
//! compared against the natively computed values.

use leanvm_b::compiler::{compile, parse_file};
use leanvm_b::cpu::{prove, verify};
use leanvm_b::field::{F128, g_pow};
use rand::SeedableRng;
use rand::rngs::StdRng;
use xmss::*;

/// A 16-byte digest/tweak/pp as the F128 word the VM sees (little-endian).
fn word(bytes: &[u8]) -> F128 {
    F128::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
    )
}

/// One 32-byte block as a 2-word witness entry.
fn pair(a: &[u8], b: &[u8]) -> Vec<F128> {
    vec![word(a), word(b)]
}

#[test]
fn wots_core_in_vm() {
    let seed = [42u8; 32];
    let slot = 7u32;
    let message: Message = std::array::from_fn(|i| (i * 5 + 1) as u8);
    let (sk, pk) = xmss_key_gen(seed, 0, 15).expect("keygen");
    let sig = xmss_sign(&mut StdRng::seed_from_u64(1), &sk, &message, slot).expect("sign");
    let pp = pk.public_param;
    let wots = &sig.wots_signature;
    let encoding = wots_encode(&message, slot, &pp, &wots.randomness).expect("encoding");

    // Native values the program must reproduce.
    let leaf = wots.recover_public_key(&message, slot, &pp).expect("recover").hash(&pp, slot);
    let mut enc_data = [0u8; 2 * STATE_LEN];
    enc_data[..MESSAGE_LEN].copy_from_slice(&message);
    enc_data[MESSAGE_LEN..][..RANDOMNESS_LEN].copy_from_slice(&wots.randomness);
    let digest = md_tweak_hash(&pp, TWEAK_TYPE_ENCODING, 0, slot, &enc_data);

    // The witness streams.
    let mut program = compile(
        &parse_file(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/xmss_wots.py")).expect("parse"),
    );
    let tweak_pair = |ty: u8, pos: u32| pair(&make_tweak(ty, pos, slot), &pp);
    program.set_witness("enc_tweak", vec![tweak_pair(TWEAK_TYPE_ENCODING, 0)]);
    program.set_witness("msg", vec![pair(&message[..16], &message[16..])]);
    program.set_witness("rand", vec![pair(&enc_data[MESSAGE_LEN..][..16], &enc_data[MESSAGE_LEN + 16..])]);
    program.set_witness(
        "digits",
        encoding.iter().map(|&e| vec![g_pow(e as usize)]).collect(),
    );
    program.set_witness(
        "sig",
        wots.chain_tips.iter().map(|t| vec![word(t)]).collect(),
    );
    // Per chain, the tweak|pp pair of each executed step (positions e_i..6),
    // in execution order.
    let mut chain_tweaks = Vec::new();
    for (i, &e) in encoding.iter().enumerate() {
        for s in e as usize..CHAIN_LENGTH - 1 {
            let position = (i * CHAIN_LENGTH + s) as u32;
            chain_tweaks.push(tweak_pair(TWEAK_TYPE_CHAIN, position));
        }
    }
    program.set_witness("chain_tweaks", chain_tweaks);
    program.set_witness("pk_tweak", vec![tweak_pair(TWEAK_TYPE_WOTS_PK, 0)]);

    let want = [word(&leaf), word(&digest)];
    let (proof, stats) = prove(&program, want);
    // 3 (encoding) + 100 (chain walks, fixed by the target sum) + 22 (tips).
    assert_eq!(stats.counts[5], 125, "BLAKE3 instruction count");
    verify(&program, &want, &proof).expect("WOTS core verifies in-VM");

    // A wrong public input (a tampered digest) is rejected.
    let bad = [want[0], want[1] + F128::ONE];
    assert!(verify(&program, &bad, &proof).is_err());
}
