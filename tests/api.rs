use leanvm_b::*;

const EPOCHS: [xmss::Epoch; 2] = [7, 9];

const LEAF_RATE: usize = 1;
const ROOT_RATE: usize = 2;

#[test]
fn public_api_end_to_end() {
    setup_prover();
    let rng = &mut rand::rng();

    // 1. Four XMSS signers.
    let mut xmss_input = Vec::new();
    for key in 0..4u8 {
        let (secret_key, pub_key) = xmss::key_gen([key; 32], EPOCHS[0], EPOCHS[1]).expect("a valid epoch range");
        let signs_at: &[xmss::Epoch] = match key {
            // Signing at both epochs is two claims for the one key.
            0 | 1 => &EPOCHS,
            2 => &EPOCHS[..1],
            _ => &EPOCHS[1..],
        };
        for &epoch in signs_at {
            let message = message_at(epoch);
            let signature = xmss::sign(rng, &secret_key, &message, epoch).expect("the epoch is in range");
            xmss_input.push((pub_key.clone(), epoch, message, signature));
        }
    }

    // 2. Two SPHINCS signers, each on its own message: this half of the statement
    //    is `(key, message)` pairs, not one message everyone shared.
    let mut sphincs_input = Vec::new();
    for signer in 0..2u8 {
        let (secret_key, pub_key) = sphincs::key_gen(rng);
        let message = [signer; sphincs::MESSAGE_LEN];
        let signature = sphincs::sign(rng, &secret_key, &message).expect("a signature exists");
        sphincs_input.push((pub_key, message, signature));
    }

    // 3. Two leaves over half the signatures each, then one root over both. The
    //    root covers every signer the leaves did, and costs the same to verify.
    let left = aggregate(&[], xmss_input[..3].to_vec(), sphincs_input[..1].to_vec(), LEAF_RATE).expect("a leaf");
    let right = aggregate(&[], xmss_input[3..].to_vec(), sphincs_input[1..].to_vec(), LEAF_RATE).expect("a leaf");
    let root = aggregate(&[left, right], vec![], vec![], ROOT_RATE).expect("a root");
    assert_eq!(root.n_claims(), xmss_input.len() + sphincs_input.len());

    // 4. Onto the wire, and back to a receiver holding only what it expects.
    let expected: Vec<_> = sphincs_input.iter().map(|(key, message, _)| (*key, *message)).collect();
    let bytes = root.to_bytes();
    let received = AggregateSignature::from_bytes(&bytes).expect("the wire form parses");
    accept(&received, &expected);

    // 5. What the API promises to reject.
    for rate in [MIN_LOG_INV_RATE - 1, MAX_LOG_INV_RATE + 1] {
        assert_eq!(
            aggregate(&[], xmss_input[..1].to_vec(), vec![], rate).err(),
            Some(AggregationError::InvalidRate { log_inv_rate: rate }),
            "a rate outside the accepted range reports, it does not panic"
        );
    }
    assert_eq!(
        aggregate(&[], vec![], vec![], LEAF_RATE).err(),
        Some(AggregationError::Empty),
        "an aggregate needs at least one input"
    );
    assert_eq!(
        received.verify_against(&[(EPOCHS[0], message_at(EPOCHS[0]))]),
        Err(AggregateVerifyError::UnexpectedStatement),
        "an epoch group the caller did not allow is rejected"
    );
    // Parsing rejects rather than panicking, and never accepts trailing bytes.
    let mut trailing = bytes.clone();
    trailing.push(0);
    for bad in [&bytes[..bytes.len() - 1], &trailing[..]] {
        assert_eq!(
            AggregateSignature::from_bytes(bad).err(),
            Some(AggregateVerifyError::MalformedEncoding)
        );
    }
}

/// The receiver's side. `verify_against` pins the XMSS half to the
/// `(epoch, message)` pairs we accept and nothing else, so the SPHINCS pairs are
/// ours to check.
fn accept(sig: &AggregateSignature, expected_sphincs: &[(sphincs::SphincsPublicKey, sphincs::Message)]) {
    let allowed = EPOCHS.map(|epoch| (epoch, message_at(epoch)));
    sig.verify_against(&allowed).expect("the root verifies");
    for signer in sig.sphincs_signers() {
        assert!(expected_sphincs.contains(signer), "an unexpected SPHINCS signer");
    }

    // A claim is not a signer: the two keys that signed at both epochs hold two
    // claims each, so a threshold over distinct keys has to deduplicate.
    let mut keys: Vec<_> = sig.xmss_signers().iter().flat_map(|(_, _, keys)| keys).collect();
    keys.sort();
    keys.dedup();
    assert_eq!(keys.len(), 4);
    assert_eq!(sig.xmss_signers().len(), EPOCHS.len());
    assert_eq!(sig.xmss_signers().iter().map(|(_, _, k)| k.len()).sum::<usize>(), 6);
}

fn message_at(epoch: xmss::Epoch) -> xmss::Message {
    let mut message = [0; xmss::MESSAGE_LEN];
    message[..4].copy_from_slice(&epoch.to_le_bytes());
    message
}
