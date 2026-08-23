//! The SHA-256 circuit driven through flock's actual reduction: zerocheck then
//! lincheck, prover and verifier, on the shared transcript.
//!
//! The unit tests in `flock::hash` establish that the circuit is the right
//! circuit (known-answer vectors, honest witness satisfies, the backward walk
//! transposes the forward one). This establishes that the encoding is *provable* with the
//! machinery as it stands: same zerocheck, same lincheck, `k_log = 15` and
//! `k_skip = 6`. Only the PCS opening is left out, which is generic in the
//! claims and covered end to end by `hash_batch`.

use crate::lincheck::QuirkyPoint;
use crate::hash::{
    Compression, K_LOG, K_SKIP, USEFUL_BITS, WalkLincheckCircuit, generate_witness_with_ab_packed_and_lincheck, iv_64,
    min_n_blocks_log,
};
use crate::zerocheck::{PaddingSpec, ZerocheckClaim};
use fiat_shamir::transcript::{ProverState, VerifierState};
use primitives::test_rng::Rng;

const LABEL: &[u8] = b"flock-sha2-reduction-test";

fn packed_bytes(words: &[u64]) -> &[u8] {
    // SAFETY: u64 has no padding and any bit pattern is a valid u8 sequence.
    unsafe { std::slice::from_raw_parts(words.as_ptr().cast::<u8>(), std::mem::size_of_val(words)) }
}

fn x_ab_of(zc: &ZerocheckClaim, inner_rest_len: usize) -> QuirkyPoint {
    QuirkyPoint {
        z_skip: zc.z,
        x_inner_rest: zc.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zc.mlv_challenges[inner_rest_len..].to_vec(),
    }
}

fn blocks_for(n: usize, seed: u64) -> Vec<Compression> {
    let mut rng = Rng::new(seed);
    (0..n)
        .map(|i| {
            (
                if i == 0 {
                    iv_64()
                } else {
                    std::array::from_fn(|_| rng.next_u32())
                },
                std::array::from_fn(|_| rng.next_u32()),
            )
        })
        .collect()
}

/// Prove. `tamper` may corrupt the packed witness first, in which case the
/// transcript this returns must not verify.
fn prove(n: usize, tamper: Option<usize>) -> (usize, fiat_shamir::transcript::Proof) {
    let n_log = min_n_blocks_log(n);
    let m = K_LOG + n_log;
    let blocks = blocks_for(n, 0xB2_5E_ED ^ n as u64);

    let (mut z, a, b, mut z_lincheck) = generate_witness_with_ab_packed_and_lincheck(&blocks, n_log);
    if let Some(bit) = tamper {
        // Flip one committed witness bit, in both views the prover feeds in.
        z[bit / 64] ^= 1u64 << (bit % 64);
        let (inner, outer) = (bit % (1 << K_LOG), bit >> K_LOG);
        z_lincheck[(outer / 8) * (1 << K_LOG) + inner] ^= 1u8 << (outer % 8);
    }

    let padding = PaddingSpec {
        k_log: K_LOG,
        useful_bits_per_block: USEFUL_BITS,
    };
    let inner_rest_len = K_LOG - K_SKIP;

    let mut ps = ProverState::new(LABEL, &[]);
    let zc = crate::zerocheck::prove_packed_padded(
        packed_bytes(&a),
        packed_bytes(&b),
        packed_bytes(&z), // C = I, so c == z
        m,
        &padding,
        &mut ps,
    );
    let x_ab = x_ab_of(&zc, inner_rest_len);
    let _lc = crate::lincheck::prove_padded_capture_s_hat_v(
        &z_lincheck,
        m,
        K_LOG,
        K_SKIP,
        USEFUL_BITS,
        &WalkLincheckCircuit,
        &x_ab,
        &mut ps,
    );
    (m, ps.into_proof())
}

/// Replay a transcript through the reduction verifier.
fn verify(m: usize, transcript: &fiat_shamir::transcript::Proof) -> bool {
    let inner_rest_len = K_LOG - K_SKIP;
    let mut vs = VerifierState::new(LABEL, transcript, &[]);
    let Ok(zc_v) = crate::zerocheck::verify(m, &mut vs) else {
        return false;
    };
    let x_ab_v = x_ab_of(&zc_v, inner_rest_len);
    let circuit = WalkLincheckCircuit;
    if crate::lincheck::verify(
        m,
        K_LOG,
        K_SKIP,
        &circuit,
        &x_ab_v,
        zc_v.a_eval,
        zc_v.b_eval,
        zc_v.c_eval,
        &mut vs,
    )
    .is_err()
    {
        return false;
    }
    vs.finish().is_ok()
}

/// Prove, then verify.
fn run(n: usize, tamper: Option<usize>) -> bool {
    let (m, transcript) = prove(n, tamper);
    verify(m, &transcript)
}

/// A full SHA-256 compression inside a 2^15 block, proved and verified through
/// the unmodified zerocheck and lincheck. The lincheck verifier here answers via
/// [`flock::hash::bilinear_walk`], so this also exercises the forward walk
/// against the same transcript the backward walk's marginal produced.
#[test]
fn sha2_reduction_roundtrip() {
    for n in [8usize, 16] {
        assert!(run(n, None), "honest SHA-256 reduction must verify at n = {n}");
    }
}

/// A single flipped witness bit must not survive. Picks an input bit, a
/// message bit, a schedule pin, a product bit in the last round and the output
/// region, so every row kind the block contains is represented.
#[test]
fn sha2_reduction_rejects_tampering() {
    // One bit from each region of the block, per `flock::hash`'s layout map:
    // h[0] bit 0; m[5] bit 28; W[29]'s pin; round 63's Ch product and its
    // A_NEW pin; and out[1] bit 12.
    for bit in [0usize, 700, 2_728, 28_540, 28_860, 300] {
        assert!(
            !run(8, Some(bit)),
            "flipping witness bit {bit} must make the reduction reject"
        );
    }
}

/// One flipped transcript word in any region must make the reduction reject.
/// The zerocheck has no terminal check of its own any more: a tampered round
/// message just moves the ĉ it derives, and it is lincheck, which pins â, b̂
/// and ĉ against the same witness vector, that catches it. This test is what
/// stands behind that claim.
#[test]
fn sha2_reduction_rejects_proof_mutations() {
    let n = 8;
    let (m, transcript) = prove(n, None);
    assert!(verify(m, &transcript), "honest transcript must verify");

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
        assert!(!verify(m, &bad), "flipping {label} must make the reduction reject");
    }
}
