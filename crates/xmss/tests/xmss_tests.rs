use rand::{Rng, SeedableRng, rngs::StdRng};
use xmss::*;

fn test_message() -> Message {
    std::array::from_fn(|i| (i * 3 + 7) as u8)
}

#[test]
fn keygen_sign_verify() {
    let seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message = test_message();

    for epoch in [0u32, 1234, u32::MAX] {
        let (sk, pk) = xmss_key_gen(seed, epoch.saturating_sub(1), epoch.saturating_add(2)).unwrap();
        let sig = xmss_sign(&mut StdRng::seed_from_u64(epoch as u64), &sk, &message, epoch).unwrap();
        xmss_verify(&pk, &message, &sig, epoch).unwrap();
    }
}

#[test]
fn serialize_deserialize_and_size() {
    let seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message = test_message();
    let epoch = 110;

    let (sk, pk) = xmss_key_gen(seed, 100, 115).unwrap();
    let sig = xmss_sign(&mut StdRng::seed_from_u64(0), &sk, &message, epoch).unwrap();

    let public_key_bytes = bincode::serialize(&pk).unwrap();
    assert_eq!(public_key_bytes.len(), PUB_KEY_FLAT_SIZE);
    let decoded_public_key: XmssPublicKey = bincode::deserialize(&public_key_bytes).unwrap();
    assert_eq!(pk, decoded_public_key);

    let signature_bytes = bincode::serialize(&sig).unwrap();
    assert_eq!(signature_bytes.len(), XMSS_SIG_SIZE);
    let decoded_signature: XmssSignature = bincode::deserialize(&signature_bytes).unwrap();
    assert_eq!(sig, decoded_signature);

    xmss_verify(&decoded_public_key, &message, &decoded_signature, epoch).unwrap();
}

#[test]
fn key_range_changes_root() {
    let seed = [3u8; 32];
    let (_, shorter_range) = xmss_key_gen(seed, 50, 60).unwrap();
    let (_, longer_range) = xmss_key_gen(seed, 50, 61).unwrap();
    assert_ne!(shorter_range.merkle_root, longer_range.merkle_root);
}

#[test]
fn tampered_signatures_rejected() {
    let seed = [9u8; 32];
    let message = test_message();
    let epoch = 7;
    let (sk, pk) = xmss_key_gen(seed, 0, 15).unwrap();
    let sig = xmss_sign(&mut StdRng::seed_from_u64(1), &sk, &message, epoch).unwrap();
    xmss_verify(&pk, &message, &sig, epoch).unwrap();

    let mut bad_message = message;
    bad_message[0] ^= 1;
    assert!(xmss_verify(&pk, &bad_message, &sig, epoch).is_err());

    assert!(xmss_verify(&pk, &message, &sig, epoch + 1).is_err());

    let mut bad_chain_tip = sig.clone();
    bad_chain_tip.wots_signature.chain_tips[5][0] ^= 1;
    assert!(xmss_verify(&pk, &message, &bad_chain_tip, epoch).is_err());

    let mut bad_randomness = sig.clone();
    bad_randomness.wots_signature.randomness[0] ^= 1;
    assert!(xmss_verify(&pk, &message, &bad_randomness, epoch).is_err());

    let mut bad_merkle_path = sig.clone();
    bad_merkle_path.merkle_proof[10][3] ^= 1;
    assert_eq!(
        xmss_verify(&pk, &message, &bad_merkle_path, epoch),
        Err(XmssVerifyError::InvalidMerklePath)
    );

    assert_eq!(
        xmss_sign(&mut StdRng::seed_from_u64(2), &sk, &message, 16),
        Err(XmssSignatureError::EpochOutOfRange)
    );
}

/// Detect changes to the encoding predicate through its grinding cost.
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
    let bits = (total_iters as f64 / n as f64).log2();
    println!("Average grinding bits: {bits:.1}");
    assert!((13.5..15.5).contains(&bits), "grinding cost moved: {bits:.2} bits");
}
