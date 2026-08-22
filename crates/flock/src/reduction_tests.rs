//! The Keccak circuit driven through flock's actual reduction: zerocheck then
//! lincheck, prover and verifier, on the shared transcript.
//!
//! The unit tests in `flock::sha3` establish that the circuit is the right
//! circuit (the witness is the permutation, the backward walk transposes the
//! forward one) and that the reduction round-trips and rejects a tampered
//! witness. What is left, and what this file is for, is the transcript itself:
//! a flipped word anywhere in the stream must make the reduction reject. Only
//! the PCS opening is out of scope, being generic in the claims and covered end
//! to end by `sha3_batch`.

use crate::sha3::{Compression, K_LOG, K_SKIP, Sha3Setup, min_n_blocks_log};
use fiat_shamir::transcript::{ProverState, VerifierState};
use primitives::test_rng::Rng;

const LABEL: &[u8] = b"flock-sha3-reduction-test";

fn blocks_for(n: usize, seed: u64) -> Vec<Compression> {
    let mut rng = Rng::new(seed);
    (0..n)
        .map(|_| Compression {
            prev: std::array::from_fn(|_| rng.next_u64()),
            msg: std::array::from_fn(|_| rng.next_u64()),
        })
        .collect::<Vec<Compression>>()
}

fn prove(n: usize) -> (Sha3Setup, fiat_shamir::transcript::Proof) {
    let setup = Sha3Setup::new(n);
    let mut ps = ProverState::new(LABEL, &[]);
    setup.prove_reduction(&blocks_for(n, 0x5A3 ^ n as u64), &mut ps);
    (setup, ps.into_proof())
}

fn verify(setup: &Sha3Setup, transcript: &fiat_shamir::transcript::Proof) -> bool {
    let mut vs = VerifierState::new(LABEL, transcript, &[]);
    setup.verify_reduction(&mut vs).is_ok() && vs.finish().is_ok()
}

/// One flipped transcript word in any region must make the reduction reject.
/// The zerocheck has no terminal check of its own any more: a tampered round
/// message just moves the ĉ it derives, and it is lincheck, which pins â, b̂
/// and ĉ against the same witness vector, that catches it. This test is what
/// stands behind that claim.
#[test]
fn sha3_reduction_rejects_proof_mutations() {
    let n = 8;
    let (setup, transcript) = prove(n);
    assert!(verify(&setup, &transcript), "honest transcript must verify");

    let m = setup.m();
    let ell = 1usize << K_SKIP;
    let n_mlv = m - K_SKIP;
    let zc_len = ell + 2 * n_mlv + 2;
    let lc_rounds = K_LOG - K_SKIP;
    let regions: [(&str, usize); 7] = [
        ("zerocheck round1[0]", 0),
        ("zerocheck round1[last]", ell - 1),
        ("zerocheck round[mid].msg_1", ell + 2 * (n_mlv / 2)),
        ("zerocheck round[mid].msg_inf", ell + 2 * (n_mlv / 2) + 1),
        ("zerocheck final_a", zc_len - 2),
        ("lincheck round[0]", zc_len),
        ("lincheck z_partial[0]", zc_len + 2 * lc_rounds),
    ];
    for (label, word) in regions {
        let mut bad = transcript.clone();
        bad.stream[word].c0 ^= 1;
        assert!(!verify(&setup, &bad), "flipping {label} must make the reduction reject");
    }
    assert_eq!(min_n_blocks_log(n), setup.n_blocks_log());
}
