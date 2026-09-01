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
        let (sk, pk) = key_gen(seed, epoch.saturating_sub(1), epoch.saturating_add(2)).unwrap();
        let sig = sign(&mut StdRng::seed_from_u64(epoch as u64), &sk, &message, epoch).unwrap();
        verify(&pk, &message, &sig, epoch).unwrap();
    }
}

#[test]
fn serialize_deserialize_and_size() {
    let seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message = test_message();
    let epoch = 110;

    let (sk, pk) = key_gen(seed, 100, 115).unwrap();
    let sig = sign(&mut StdRng::seed_from_u64(0), &sk, &message, epoch).unwrap();

    let public_key_bytes = bincode::serialize(&pk).unwrap();
    assert_eq!(public_key_bytes.len(), PUB_KEY_SIZE);
    let decoded_public_key: XmssPublicKey = bincode::deserialize(&public_key_bytes).unwrap();
    assert_eq!(pk, decoded_public_key);

    let signature_bytes = bincode::serialize(&sig).unwrap();
    assert_eq!(signature_bytes.len(), SIG_SIZE);
    let decoded_signature: XmssSignature = bincode::deserialize(&signature_bytes).unwrap();
    assert_eq!(sig, decoded_signature);

    verify(&decoded_public_key, &message, &decoded_signature, epoch).unwrap();
}

#[test]
fn deterministic_keygen_and_range_separation() {
    let seed = [3u8; 32];
    let (_, pk) = key_gen(seed, 50, 60).unwrap();
    let (_, same_seed_and_range) = key_gen(seed, 50, 60).unwrap();
    assert_eq!(pk, same_seed_and_range);
    // A different range changes the filler/real split, hence the root.
    let (_, longer_range) = key_gen(seed, 50, 61).unwrap();
    assert_ne!(pk.merkle_root, longer_range.merkle_root);
}

/// Pin the wire layout of the tweak: the type byte, both little-endian `u32`
/// fields, and the seven trailing zeros. Literal bytes, so an endianness
/// mistake cannot be mirrored here.
#[test]
fn tweak_layout_is_exact() {
    assert_eq!(
        [
            TWEAK_TYPE_CHAIN,
            TWEAK_TYPE_WOTS_PK,
            TWEAK_TYPE_MERKLE,
            TWEAK_TYPE_ENCODING
        ],
        [0, 1, 2, 3]
    );
    assert_eq!(
        make_tweak(TWEAK_TYPE_MERKLE, 0x0102_0304, 0xa0b0_c0d0),
        [2, 0x04, 0x03, 0x02, 0x01, 0xd0, 0xc0, 0xb0, 0xa0, 0, 0, 0, 0, 0, 0, 0]
    );
}

#[test]
fn tweak_separates_hash_domains() {
    let pp = [7u8; PUBLIC_PARAM_LEN];
    let x = [1u8; DIGEST_LEN];
    let base = tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &x);
    // Different type, position, index, or public parameter: different hash.
    assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_MERKLE, 3, 5, &x));
    assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 4, 5, &x));
    assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 6, &x));
    assert_ne!(base, tweak_hash(&[8u8; PUBLIC_PARAM_LEN], TWEAK_TYPE_CHAIN, 3, 5, &x));
    // Standard BLAKE2s binds the exact payload length.
    let mut extended = [0u8; STATE_LEN];
    extended[..DIGEST_LEN].copy_from_slice(&x);
    assert_ne!(base, tweak_hash(&pp, TWEAK_TYPE_CHAIN, 3, 5, &extended));
}

/// The multi-block WOTS public-key hash is standard BLAKE2s of `tweak | pp |
/// payload`, assembled independently here and streamed in unrelated chunks.
#[test]
fn multi_block_tweak_hash_is_standard_blake2s() {
    let pp = [9u8; PUBLIC_PARAM_LEN];
    let payload = [5u8; V * DIGEST_LEN];
    let mut input = Vec::new();
    input.extend_from_slice(&make_tweak(TWEAK_TYPE_WOTS_PK, 0, 42));
    input.extend_from_slice(&pp);
    input.extend_from_slice(&payload);

    let mut hasher = primitives::hash::Hasher::new();
    for chunk in input.chunks(37) {
        hasher.update(chunk);
    }
    let expected = hasher.finalize();
    assert_eq!(expected, primitives::hash::hash(&input));
    assert_eq!(
        tweak_hash(&pp, TWEAK_TYPE_WOTS_PK, 0, 42, &payload),
        expected[..DIGEST_LEN]
    );
}

#[test]
fn tampered_signatures_rejected() {
    let seed = [9u8; 32];
    let message = test_message();
    let epoch = 7;
    let (sk, pk) = key_gen(seed, 0, 15).unwrap();
    let sig = sign(&mut StdRng::seed_from_u64(1), &sk, &message, epoch).unwrap();
    verify(&pk, &message, &sig, epoch).unwrap();

    let mut bad_message = message;
    bad_message[0] ^= 1;
    assert!(verify(&pk, &bad_message, &sig, epoch).is_err());

    assert!(verify(&pk, &message, &sig, epoch + 1).is_err());

    let mut bad_chain_tip = sig.clone();
    bad_chain_tip.wots_signature.chain_tips[5][0] ^= 1;
    assert!(verify(&pk, &message, &bad_chain_tip, epoch).is_err());

    let mut bad_randomness = sig.clone();
    bad_randomness.wots_signature.randomness[0] ^= 1;
    assert!(verify(&pk, &message, &bad_randomness, epoch).is_err());

    let mut bad_merkle_path = sig.clone();
    bad_merkle_path.merkle_proof[10][3] ^= 1;
    assert_eq!(
        verify(&pk, &message, &bad_merkle_path, epoch),
        Err(XmssVerifyError::InvalidMerklePath)
    );

    assert_eq!(
        sign(&mut StdRng::seed_from_u64(2), &sk, &message, 16),
        Err(XmssSignError::EpochOutOfRange)
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

/// A reloaded secret key must sign exactly as the original does, so that
/// persisting one is a real alternative to regenerating it.
#[test]
fn secret_key_survives_a_round_trip() {
    let seed: [u8; 32] = std::array::from_fn(|i| (i * 11) as u8);
    let (sk, pk) = key_gen(seed, 40, 45).unwrap();
    let reloaded: XmssSecretKey = bincode::deserialize(&bincode::serialize(&sk).unwrap()).unwrap();

    assert_eq!(reloaded.public_key(), pk);
    assert_eq!(reloaded.epoch_range(), 40..=45);
    let message = test_message();
    for epoch in [40, 43, 45] {
        let sig = sign(&mut StdRng::seed_from_u64(epoch), &reloaded, &message, epoch as u32).unwrap();
        verify(&pk, &message, &sig, epoch as u32).unwrap();
    }
    assert_eq!(
        sign(&mut StdRng::seed_from_u64(0), &reloaded, &message, 46),
        Err(XmssSignError::EpochOutOfRange)
    );
}
