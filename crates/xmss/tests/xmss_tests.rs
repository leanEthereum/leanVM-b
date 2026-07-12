use rand::{Rng, SeedableRng, rngs::StdRng};
use xmss::*;

fn test_message() -> Message {
    std::array::from_fn(|i| (i * 3 + 7) as u8)
}

#[test]
fn keygen_sign_verify() {
    let seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message = test_message();

    for slot in [0u32, 1234, u32::MAX] {
        let (sk, pk) = xmss_key_gen(seed, slot.saturating_sub(1), slot.saturating_add(2)).unwrap();
        let sig = xmss_sign(&mut StdRng::seed_from_u64(slot as u64), &sk, &message, slot).unwrap();
        xmss_verify(&pk, &message, &sig, slot).unwrap();
    }
}

#[test]
fn serialize_deserialize_and_size() {
    let seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message = test_message();
    let slot = 110;

    let (sk, pk) = xmss_key_gen(seed, 100, 115).unwrap();
    let sig = xmss_sign(&mut StdRng::seed_from_u64(0), &sk, &message, slot).unwrap();

    let pk_bytes = bincode::serialize(&pk).unwrap();
    assert_eq!(pk_bytes.len(), PUB_KEY_FLAT_SIZE); // 32 bytes
    let pk2: XmssPublicKey = bincode::deserialize(&pk_bytes).unwrap();
    assert_eq!(pk, pk2);

    let sig_bytes = bincode::serialize(&sig).unwrap();
    assert_eq!(sig_bytes.len(), XMSS_SIG_SIZE); // 1208 bytes, below the IPv6 MTU
    let sig2: XmssSignature = bincode::deserialize(&sig_bytes).unwrap();
    assert_eq!(sig, sig2);

    xmss_verify(&pk2, &message, &sig2, slot).unwrap();
}

#[test]
fn deterministic_keygen() {
    let seed = [3u8; 32];
    let (_, pk1) = xmss_key_gen(seed, 50, 60).unwrap();
    let (_, pk2) = xmss_key_gen(seed, 50, 60).unwrap();
    assert_eq!(pk1, pk2);
    // A different range changes the filler/real split, hence the root.
    let (_, pk3) = xmss_key_gen(seed, 50, 61).unwrap();
    assert_ne!(pk1.merkle_root, pk3.merkle_root);
}

#[test]
fn tampered_signatures_rejected() {
    let seed = [9u8; 32];
    let message = test_message();
    let slot = 7;
    let (sk, pk) = xmss_key_gen(seed, 0, 15).unwrap();
    let sig = xmss_sign(&mut StdRng::seed_from_u64(1), &sk, &message, slot).unwrap();
    xmss_verify(&pk, &message, &sig, slot).unwrap();

    // Wrong message.
    let mut bad_message = message;
    bad_message[0] ^= 1;
    assert!(xmss_verify(&pk, &bad_message, &sig, slot).is_err());

    // Wrong slot.
    assert!(xmss_verify(&pk, &message, &sig, slot + 1).is_err());

    // Tampered chain tip.
    let mut bad = sig.clone();
    bad.wots_signature.chain_tips[5][0] ^= 1;
    assert!(xmss_verify(&pk, &message, &bad, slot).is_err());

    // Tampered randomness (either the encoding no longer hits the target sum,
    // or the recovered WOTS key changes; both must fail).
    let mut bad = sig.clone();
    bad.wots_signature.randomness[0] ^= 1;
    assert!(xmss_verify(&pk, &message, &bad, slot).is_err());

    // Tampered Merkle path.
    let mut bad = sig.clone();
    bad.merkle_proof[10][3] ^= 1;
    assert_eq!(
        xmss_verify(&pk, &message, &bad, slot),
        Err(XmssVerifyError::InvalidMerklePath)
    );

    // Signing outside the key's range.
    assert_eq!(
        xmss_sign(&mut StdRng::seed_from_u64(2), &sk, &message, 16),
        Err(XmssSignatureError::SlotOutOfRange)
    );
}

#[test]
#[ignore]
fn encoding_grinding_bits() {
    let n = 200;
    let pp = [0u8; PUBLIC_PARAM_LEN];
    let mut total_iters = 0usize;
    for i in 0..n {
        let mut rng = StdRng::seed_from_u64(i as u64);
        let message: Message = rng.random();
        let (_, _, num_iters) = find_randomness_for_wots_encoding(&message, i as u32, &pp, &mut rng);
        total_iters += num_iters;
    }
    println!("Average grinding bits: {:.1}", (total_iters as f64 / n as f64).log2());
}
