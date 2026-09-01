//! Aggregate signatures of both schemes, at several epochs, into two leaves,
//! recurse over those, and check the root against the statement we expected.
//!
//! `cargo run --release --example aggregate`

use leanvm_b::{AggregateSignature, aggregate, rand, setup_prover, sphincs, xmss};

/// The rate is per call, and there is no default: leaves here are proved for
/// speed, the root for size.
const LEAF_LOG_INV_RATE: usize = 1;
const ROOT_LOG_INV_RATE: usize = 2;

/// The XMSS epochs signed at. One message per epoch, which is what lets an
/// aggregate group its XMSS signers by epoch.
const EPOCHS: [xmss::Epoch; 2] = [7, 9];

fn xmss_message(epoch: xmss::Epoch) -> xmss::Message {
    let mut message = [0; xmss::MESSAGE_LEN];
    message[..4].copy_from_slice(&epoch.to_le_bytes());
    message
}

fn sphincs_message(signer: usize) -> sphincs::Message {
    let mut message = [0; sphincs::MESSAGE_LEN];
    message[0] = signer as u8;
    message
}

/// Keys 0 and 1 sign at both epochs, 2 and 3 at one each, so a key can hold more
/// than one claim.
fn epochs_signed_by(key: u8) -> &'static [xmss::Epoch] {
    match key {
        0 | 1 => &EPOCHS,
        2 => &EPOCHS[..1],
        _ => &EPOCHS[1..],
    }
}

fn main() {
    setup_prover();
    let rng = &mut rand::rng();

    let mut raw_xmss = Vec::new();
    for key in 0..4u8 {
        let (secret_key, pub_key) = xmss::key_gen([key; 32], EPOCHS[0], EPOCHS[1]).expect("a valid epoch range");
        for &epoch in epochs_signed_by(key) {
            let message = xmss_message(epoch);
            let signature = xmss::sign(rng, &secret_key, &message, epoch).expect("the epoch is in range");
            raw_xmss.push((pub_key.clone(), epoch, message, signature));
        }
    }

    // Every SPHINCS signer carries its own message, so that half of the statement
    // is `(key, message)` pairs rather than one shared message.
    let mut raw_sphincs = Vec::new();
    for signer in 0..3 {
        let (secret_key, pub_key) = sphincs::key_gen(rng);
        let message = sphincs_message(signer);
        let signature = sphincs::sign(rng, &secret_key, &message).expect("a signature exists");
        raw_sphincs.push((pub_key, message, signature));
    }
    let expected_sphincs: Vec<_> = raw_sphincs.iter().map(|(pk, message, _)| (*pk, *message)).collect();

    // Two leaves over disjoint halves, then one root over both: the root's signer
    // lists are the union of what the leaves published, and cost the same to check.
    let (xmss_left, xmss_right) = raw_xmss.split_at(raw_xmss.len() / 2);
    let (sphincs_left, sphincs_right) = raw_sphincs.split_at(1);
    let leaf = |x: &[_], s: &[_]| aggregate(&[], x.to_vec(), s.to_vec(), LEAF_LOG_INV_RATE).expect("a leaf");
    let children = [leaf(xmss_left, sphincs_left), leaf(xmss_right, sphincs_right)];
    let root = aggregate(&children, vec![], vec![], ROOT_LOG_INV_RATE).expect("a root");

    let bytes = root.to_bytes();
    let received = AggregateSignature::from_bytes(&bytes).expect("the wire form parses");
    accept(&received, &expected_sphincs);
    println!("{} bytes on the wire", bytes.len());
}

/// What a receiver does. `verify_against` pins the XMSS half to the
/// `(epoch, message)` pairs we accept; it constrains no SPHINCS message, so we
/// compare those ourselves.
fn accept(sig: &AggregateSignature, expected_sphincs: &[(sphincs::SphincsPublicKey, sphincs::Message)]) {
    let allowed: Vec<_> = EPOCHS.iter().map(|&epoch| (epoch, xmss_message(epoch))).collect();
    sig.verify_against(&allowed).expect("the root verifies");
    for signer in sig.sphincs_signers() {
        assert!(expected_sphincs.contains(signer), "an unexpected SPHINCS signer");
    }

    // A claim is not a signer: a key signing at two epochs holds two claims, so a
    // threshold over distinct keys has to deduplicate.
    let mut keys: Vec<_> = sig.xmss_signers().iter().flat_map(|(_, _, keys)| keys).collect();
    keys.sort();
    keys.dedup();
    println!(
        "verified: {} XMSS claims over {} keys in {} epochs, and {} SPHINCS claims",
        sig.xmss_signers().iter().map(|(_, _, keys)| keys.len()).sum::<usize>(),
        keys.len(),
        sig.xmss_signers().len(),
        sig.sphincs_signers().len(),
    );
}
