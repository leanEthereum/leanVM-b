//! Bridge to the flock BLAKE3 prover ([`flock::blake3`]), single-PCS.
//!
//! `q_pkd` (flock's packed BLAKE3 witness) is committed as a column in leanVM-b's
//! ONE stacked witness (§3.1) — no separate flock commitment. The VM's `BLAKE3`
//! table binds to it by point-eval equality (its value columns and `q_pkd`'s
//! slots are point-evals of the same committed stack), and flock's R1CS validity
//! is discharged by a Ligerito over that same stacked commitment
//! ([`flock::blake3::Blake3Setup::prove_validity_stacked`],
//! which lifts the ring-switch weight into the stack domain).
//!
//! ## The mapping
//!
//! The VM's `BLAKE3(a, b) -> c` is a flock single-block compression with the
//! chaining value fixed to the BLAKE3 IV, counter `0`, block length `64`, flags
//! `CHUNK_START | CHUNK_END | ROOT` (= [`FLAGS`]) — exactly `blake3::hash` of the
//! 64-byte message `a‖b`, matching `cpu::blake3_compress`.
//!
//! ## The layout (after the alignment re-layout, `M_BASE = 640`)
//!
//! Each compression's `2^K_LOG` bits pack into [`PACKED_PER_INSTANCE`]`
//! = 2^(K_LOG-7)` `F128` coordinates; each VM-visible 128-bit word is one whole
//! packed coordinate at a fixed within-instance slot:
//!
//! ```text
//!   c0,c1 = slots 2,3     a0,a1 = slots 5,6     b0,b1 = slots 7,8
//!   cv = slots 0,1 (= IV)    counter‖blen‖flags = slot 9
//! ```
//!
//! cv and slot 9 hold constants baked into the per-block matrices (constant
//! rows), so no claims are needed to pin them.

use primitives::field::F128;
use crate::transcript::{ProverState, VerifierState};
use ::pcs::LOG_PACKING;
use ::pcs::Commitment;
#[cfg(test)]
use ::pcs::ProverData;
use flock::blake3::{
    Blake3Setup, Compression, K_LOG, ReducedClaims, ReductionReplay, blake3_compress,
    generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
};
use flock::verifier::VerifyError;

/// A `ẑ(point) = value` claim on the committed witness `q_pkd`, recovered by the
/// Flock zerocheck + lincheck reduction ([`prove_reduction`] / [`verify_reduction`])
/// and later discharged by the PCS. Re-exported from [`flock::proof`].
pub use flock::proof::ZClaim;

/// flock flags for a single 64-byte root block: `CHUNK_START(1) | CHUNK_END(2) |
/// ROOT(8) = 11` — the configuration under which the compression output equals
/// `blake3::hash` of the 64-byte input. Baked into flock's per-block matrices
/// (constant rows), along with `cv = IV`, `counter = 0` and `block_len = 64`.
pub const FLAGS: u32 = flock::blake3::PINNED_FLAGS;

/// Packed `F128` coordinates per compression instance: `K / 128 = 2^(K_LOG-7)`.
/// Instance `j` occupies packed indices `[j*PACKED_PER_INSTANCE, (j+1)*…)`.
pub const PACKED_PER_INSTANCE: usize = 1 << (K_LOG - LOG_PACKING);

// Within-instance packed-coordinate (slot) indices of the VM-visible words,
// fixed by the aligned flock layout (asserted by `layout_constants` there).
pub const SLOT_C0: usize = 2;
pub const SLOT_C1: usize = 3;
pub const SLOT_A0: usize = 5;
pub const SLOT_A1: usize = 6;
pub const SLOT_B0: usize = 7;
pub const SLOT_B1: usize = 8;

/// The six within-instance value slots in canonical order `[a0,a1,b0,b1,c0,c1]`,
/// matching `tables::BLAKE3_VALUE_COLS`.
pub const SLOTS: [usize; 6] = [SLOT_A0, SLOT_A1, SLOT_B0, SLOT_B1, SLOT_C0, SLOT_C1];


/// Split a 128-bit field element into the four little-endian `u32` words flock's
/// message uses (`lo` → words 0,1; `hi` → words 2,3) — the VM memory byte order.
fn words_of(x: F128) -> [u32; 4] {
    [x.lo as u32, (x.lo >> 32) as u32, x.hi as u32, (x.hi >> 32) as u32]
}

/// Inverse of [`words_of`]: pack four little-endian `u32` words into the `F128`.
pub fn pack_words(w: [u32; 4]) -> F128 {
    F128::new(
        (w[0] as u64) | ((w[1] as u64) << 32),
        (w[2] as u64) | ((w[3] as u64) << 32),
    )
}

/// The flock [`Compression`] for one VM `BLAKE3(a, b)`: message `m = a‖b` under
/// the pinned configuration (`cv = IV`, counter `0`, block length `64`, flags
/// [`FLAGS`] — all enforced by the matrices' constant rows).
pub fn compression(a: [F128; 2], b: [F128; 2]) -> Compression {
    let mut m = [0u32; 16];
    m[0..4].copy_from_slice(&words_of(a[0]));
    m[4..8].copy_from_slice(&words_of(a[1]));
    m[8..12].copy_from_slice(&words_of(b[0]));
    m[12..16].copy_from_slice(&words_of(b[1]));
    flock::blake3::pinned_compression(m)
}

/// The 256-bit digest `c = (c0, c1)` of a compression (= flock's `out_lo` =
/// `blake3::hash(a‖b)`).
pub fn digest(block: &Compression) -> [F128; 2] {
    let st = blake3_compress(&block.0, &block.1, block.2, block.3, block.4);
    [
        pack_words([st[0], st[1], st[2], st[3]]),
        pack_words([st[4], st[5], st[6], st[7]]),
    ]
}

/// flock's `n_blocks_log` for `n` compressions (lincheck floor `≥ 3`). The VM's
/// BLAKE3 table is sized to `2^n_blocks_log` rows so its value columns share
/// `q_pkd`'s instance cube.
pub fn n_blocks_log(n: usize) -> usize {
    min_n_blocks_log(n)
}

/// The variable count (`log2` length) of the committed `q_pkd` column for `n`
/// executed compressions: `K_LOG + n_blocks_log(max(n,1)) - 7`. Always ≥ 1
/// instance — `n = 0` still commits one padding instance (uniform proof shape).
pub fn qpkd_kappa(n: usize) -> usize {
    K_LOG + n_blocks_log(n.max(1)) - LOG_PACKING
}

/// The padding instance: the pinned compression of the all-zero message, i.e.
/// `blake3(0^64)` — what flock's witness generation fills unused slots with.
/// Synthesized as the sole block when a program executes no BLAKE3, so `q_pkd`
/// and the reduction always have ≥ 1 instance.
pub fn padding_compression() -> Compression {
    flock::blake3::padding_block()
}

/// Build the committed `q_pkd` column (flock's packed witness) for `blocks`, padded
/// to `2^n_blocks_log(max(blocks.len(),1))` instances (the unused ones
/// [`padding_compression`] blocks). Deterministic, so it matches what the reduction
/// regenerates. An empty `blocks` yields one padding cube (all instances are padding).
pub fn build_qpkd(blocks: &[Compression]) -> Vec<F128> {
    generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log(blocks.len().max(1))).0
}

/// The digest `(c0, c1)` of [`padding_compression`], i.e. `blake3(0^64)`. It is
/// NONZERO, so the VM pads its BLAKE3 output value columns with this.
pub fn padding_digest() -> [F128; 2] {
    digest(&padding_compression())
}

/// `log2` of the within-instance packed span (`PACKED_PER_INSTANCE = 2^7`): the
/// number of low coords of a `q_pkd` point that carry the slot's bits, and the
/// stride between consecutive instances' same-slot coords in `q_pkd`. A value
/// claim on `q_pkd` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING;

/// Memoized BLAKE3 R1CS [`Blake3Setup`], keyed by the executed-instance count.
/// Building it (the symbolic constraint walk over `2^K_LOG` slots) costs
/// ~hundreds of ms — fixed per circuit shape, independent of `N` or the proof.
/// So we build each shape once and reuse it across `prove`, `verify`, and
/// repeated proofs; the per-setup caches then stay warm, making verification
/// milliseconds rather than rebuilding the circuit each time.
///
/// The cache is bounded ([`SETUP_CACHE_CAP`]): `verify` calls this with the
/// PROVER-ANNOUNCED count, so an attacker cycling distinct counts could otherwise
/// grow it without limit. Past the cap we build an ephemeral (uncached) setup —
/// correct, just not memoized; legit workloads use only a handful of sizes.
const SETUP_CACHE_CAP: usize = 256;

fn setup_cache() -> &'static std::sync::Mutex<std::collections::HashMap<usize, std::sync::Arc<Blake3Setup>>> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<usize, std::sync::Arc<Blake3Setup>>>> =
        std::sync::OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

fn setup_for(n_blocks: usize) -> std::sync::Arc<Blake3Setup> {
    let cache = setup_cache();
    // Fast path: build OUTSIDE the lock so a concurrent builder (e.g. the
    // background warm spawned by `cpu::prove`) doesn't serialize behind us — the
    // ~hundreds-of-ms build must not hold the mutex.
    if let Some(s) = cache.lock().expect("BLAKE3 setup cache poisoned").get(&n_blocks) {
        return std::sync::Arc::clone(s);
    }
    let setup = std::sync::Arc::new(Blake3Setup::new(n_blocks));
    let mut map = cache.lock().expect("BLAKE3 setup cache poisoned");
    // Re-check: another thread may have inserted while we built (harmless — one wins).
    if let Some(s) = map.get(&n_blocks) {
        return std::sync::Arc::clone(s);
    }
    if map.len() < SETUP_CACHE_CAP {
        map.insert(n_blocks, std::sync::Arc::clone(&setup));
    }
    setup
}

/// Pre-build (and cache) the flock BLAKE3 R1CS setup. This is the fixed,
/// circuit-shape-only cost (~hundreds of ms, independent of the witness or the
/// number of proofs): building the `2^K_LOG`-slot R1CS.
///
/// Callers pass the number of EXECUTED `BLAKE3` instructions; it is floored at 1
/// (the padding instance a no-BLAKE3 program still carries), matching
/// `cpu::prove`/`verify`. Call it once up front so a subsequent prove/verify
/// reflects steady-state (repeated-proving) performance — the ~hundreds-of-ms
/// build is a one-time, program-independent cost, not part of proving. Idempotent.
pub fn warm_setup(n_blocks: usize) {
    let _ = setup_for(n_blocks.max(1));
}

/// The flock BLAKE3 circuit-FAMILY digest: a hash of the per-block R1CS
/// matrices and shape parameters ([`family_digest`] on the R1CS), independent
/// of the instance count. The full instance is block-diagonal — the count is
/// announced and absorbed with the other sizes — so a transcript seeded with
/// this digest (via [`crate::cpu::fs_seed`]) binds the whole statement up
/// front. Baked in flock (test-guarded): recomputing it costs ~300 ms of
/// matrix building + hashing, which used to land inside the first `prove`.
pub fn family_digest() -> [u8; 32] {
    flock::blake3::FAMILY_DIGEST
}

/// **Flock reduction only** (prover): run flock's BLAKE3 zerocheck + lincheck
/// over `blocks`, binding to `commitment`, and return the two claims
/// [`ReducedClaims`] on the committed witness `q_pkd` — `ab` (`A∘B`, lincheck)
/// and `c` (`C`, zerocheck) — along with the regenerated packed witness. The
/// sub-proof scalars ride the shared transcript stream (`ps.add_scalar` at the
/// protocol points). Does NOT open the PCS: the caller discharges the returned
/// claims via [`crate::pcs::open`] (as [`crate::cpu`]'s prove does). This is
/// the clean seam the PCS builds on.
pub fn prove_reduction(
    blocks: &[Compression],
    commitment: &Commitment,
    ps: &mut ProverState,
) -> (Vec<F128>, ReducedClaims) {
    setup_for(blocks.len()).prove_reduction(blocks, commitment, ps)
}

/// **Flock reduction only** (verifier): mirror of [`prove_reduction`]. Rebuild the
/// stack commitment from `root`/`mu`, replay the zerocheck + lincheck sub-proofs
/// straight off the shared stream (each scalar bound as it is read), and recover
/// the two `(ab, c)` claims on `q_pkd` for the PCS to discharge — plus the
/// reassembled records and reduction claims ([`ReductionReplay`]).
pub fn verify_reduction(
    n_blocks: usize,
    root: &[u8; 32],
    mu: usize,
    vs: &mut VerifierState,
) -> Result<ReductionReplay, VerifyError> {
    let commitment = crate::pcs::commitment_from_root(*root, mu);
    setup_for(n_blocks).verify_reduction(&commitment, vs)
}

/// The multilinear tail `x_inner_rest ++ x_outer` of a quirky point — the
/// `x_outer_full` the PCS ring-switch front-end consumes.
fn x_outer_full(point: &flock::lincheck::QuirkyPoint) -> Vec<F128> {
    let mut v = point.x_inner_rest.clone();
    v.extend_from_slice(&point.x_outer);
    v
}

/// Package the prover's reduction claims ([`ReducedClaims`]) as a
/// [`crate::pcs::RingSwitchOpen`], so the PCS discharges flock's `(ab, c)`
/// validity in the SAME opening as leanVM's point claims. `offset` is `q_pkd`'s
/// slot in the committed stack; the opener slices `q_pkd` from there.
pub fn ring_switch_open(n_blocks: usize, offset: usize, reduced: &ReducedClaims) -> crate::pcs::RingSwitchOpen {
    let setup = setup_for(n_blocks);
    crate::pcs::RingSwitchOpen {
        offset,
        qpkd_vars: qpkd_kappa(n_blocks),
        x_outers: vec![
            x_outer_full(&reduced.ab.claim.point),
            x_outer_full(&reduced.c.claim.point),
        ],
        s_hat_v: vec![reduced.ab.s_hat_v.clone(), reduced.c.s_hat_v.clone()],
        padding: ::pcs::PaddingSpec {
            k_log: setup.r1cs.k_log,
            useful_bits_per_block: setup.r1cs.useful_bits,
        },
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered `(ab, c)`
/// claims (from [`verify_reduction`]) as a [`crate::pcs::RingSwitchVerify`].
pub fn ring_switch_verify(n_blocks: usize, offset: usize, ab: ZClaim, c: ZClaim) -> crate::pcs::RingSwitchVerify {
    crate::pcs::RingSwitchVerify {
        offset,
        qpkd_vars: qpkd_kappa(n_blocks),
        values: vec![ab.value, c.value],
        z_skips: vec![ab.point.z_skip, c.point.z_skip],
        x_outers: vec![x_outer_full(&ab.point), x_outer_full(&c.point)],
    }
}

// (No write/read_stack_proof: flock's scalar sub-proof rides the shared stream
// via add_scalar/next_scalar at its protocol points, exactly like leanVM's own
// scalars; the one Merkle-bearing Ligerito rides the `openings` hint channel.)

/// Prove `blocks` are valid compressions in two clean phases, discharging the
/// proof against the caller's already-committed `stack` (with `q_pkd` the aligned
/// sub-block at `stack_offset`), reusing its `prover_data`/`commitment`, on the
/// shared transcript `ps`:
/// 1. the Flock reduction ([`prove_reduction`]): zerocheck + lincheck → the
///    `(ab, c)` claims on `q_pkd`;
/// 2. the PCS: one stacked Ligerito discharging those claims together with the
///    caller's `stack_pd` point claims.
#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn prove_validity_stacked(
    blocks: &[Compression],
    stack: &[F128],
    stack_offset: usize,
    prover_data: &ProverData,
    commitment: &Commitment,
    stack_pd: &[(Vec<F128>, F128)],
    ps: &mut ProverState,
) -> ::pcs::ligerito::LigeritoProof {
    setup_for(blocks.len())
        .prove_validity_stacked(blocks, stack, stack_offset, prover_data, commitment, stack_pd, ps)
}

/// Verifier side of [`prove_validity_stacked`], in the same two phases:
/// [`verify_reduction`] (replay zerocheck + lincheck → `(ab, c)` claims), then
/// verify the SINGLE stacked Ligerito against `commitment` on the shared
/// transcript. `stack_pd` are all of leanVM's point claims (bus / constraint /
/// public-input / binding) folded into the same opening.
#[cfg(test)]
pub(crate) fn verify_validity_stacked(
    n_blocks: usize,
    commitment: &Commitment,
    stack_offset: usize,
    stack_pd: &[(Vec<F128>, F128)],
    open: &::pcs::ligerito::LigeritoProof,
    vs: &mut VerifierState,
) -> Result<(), VerifyError> {
    setup_for(n_blocks).verify_validity_stacked(commitment, stack_offset, stack_pd, open, vs)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(lo: u64, hi: u64) -> F128 {
        F128::new(lo, hi)
    }

    fn sample_blocks(n: usize) -> Vec<Compression> {
        (0..n as u64)
            .map(|i| {
                compression(
                    [f(0x11 * (i + 1), 0x22 * (i + 1)), f(0x33 * (i + 1), 0x44 * (i + 1))],
                    [f(0x55 * (i + 1), 0x66 * (i + 1)), f(0x77 * (i + 1), 0x88 * (i + 1))],
                )
            })
            .collect()
    }

    /// `q_pkd`'s aligned packed slots hold the VM's 128-bit words in our field
    /// representation, and the digest matches the `blake3` crate.
    #[test]
    fn qpkd_words_match_layout() {
        let inputs: Vec<([F128; 2], [F128; 2])> = (0..5u64)
            .map(|i| {
                (
                    [f(0x1000 + i, 0x2000 + i), f(0x3000 + i, 0x4000 + i)],
                    [f(0x5000 + i, 0x6000 + i), f(0x7000 + i, 0x8000 + i)],
                )
            })
            .collect();
        let blocks: Vec<Compression> = inputs.iter().map(|&(a, b)| compression(a, b)).collect();
        let q_pkd = build_qpkd(&blocks);
        assert_eq!(q_pkd.len(), 1 << qpkd_kappa(blocks.len()));

        let slot = |j: usize, s: usize| q_pkd[j * PACKED_PER_INSTANCE + s];
        for (j, (&(a, b), blk)) in inputs.iter().zip(&blocks).enumerate() {
            assert_eq!(slot(j, SLOT_A0), a[0]);
            assert_eq!(slot(j, SLOT_A1), a[1]);
            assert_eq!(slot(j, SLOT_B0), b[0]);
            assert_eq!(slot(j, SLOT_B1), b[1]);
            let mut input = [0u8; 64];
            for (s, w) in input.chunks_exact_mut(16).zip([a[0], a[1], b[0], b[1]]) {
                s[..8].copy_from_slice(&w.lo.to_le_bytes());
                s[8..].copy_from_slice(&w.hi.to_le_bytes());
            }
            let h = *blake3::hash(&input).as_bytes();
            let word = |o: usize| {
                F128::new(
                    u64::from_le_bytes(h[o..o + 8].try_into().unwrap()),
                    u64::from_le_bytes(h[o + 8..o + 16].try_into().unwrap()),
                )
            };
            assert_eq!(digest(blk), [word(0), word(16)]);
            assert_eq!(slot(j, SLOT_C0), word(0));
            assert_eq!(slot(j, SLOT_C1), word(16));
        }
        // Constant slots (matrix-pinned): cv = IV in slots 0,1 and the packed
        // counter‖counter_hi‖block_len‖flags word in slot 9.
        let iv = flock::blake3::BLAKE3_IV;
        assert_eq!(slot(0, 0), pack_words([iv[0], iv[1], iv[2], iv[3]]));
        assert_eq!(slot(0, 1), pack_words([iv[4], iv[5], iv[6], iv[7]]));
        assert_eq!(slot(0, 9), pack_words([0, 0, 64, FLAGS]));
    }

    /// flock's validity proof, discharged by a Ligerito over a single committed
    /// stack containing `q_pkd` (plus a dummy column) — proves and verifies on
    /// the shared transcript, and a corrupted `q_pkd` is rejected.
    #[test]
    fn validity_stacked_roundtrip() {
        let blocks = sample_blocks(4);
        let q_pkd = build_qpkd(&blocks);
        let dummy = vec![f(7, 9); 8];
        let cols = vec![q_pkd.clone(), dummy];
        let stacked = crate::witness::stack(&cols);
        let offset = stacked.placements[0].offset;

        // Also fold in one full-stack point claim (exercises the pd path of the
        // single fused opening).
        let pd_point: Vec<F128> = (0..stacked.m).map(|i| f(0x100 + i as u64, 0x7)).collect();
        let pd_value = primitives::multilinear::mle_eval(&stacked.q, &pd_point);
        let stack_pd = vec![(pd_point, pd_value)];

        let mut ps = ProverState::new(b"vstack", &[]);
        let committed = crate::pcs::commit(&mut ps, &stacked.q);
        let proof = prove_validity_stacked(
            &blocks,
            &stacked.q,
            offset,
            &committed.prover_data,
            &committed.commitment,
            &stack_pd,
            &mut ps,
        );
        let bundle = ps.into_proof();

        let mut vs = VerifierState::new(b"vstack", &bundle, &[]);
        let root = crate::pcs::read_commitment(&mut vs).unwrap();
        let commitment = crate::pcs::commitment_from_root(root, stacked.m);
        verify_validity_stacked(blocks.len(), &commitment, offset, &stack_pd, &proof, &mut vs)
            .expect("validity verifies");

        // A mismatched transcript (different domain) diverges the shared sponge,
        // so the validity proof must be rejected.
        let mut vs_bad = VerifierState::new(b"different-domain", &bundle, &[]);
        let root_b = crate::pcs::read_commitment(&mut vs_bad).unwrap();
        let commitment_b = crate::pcs::commitment_from_root(root_b, stacked.m);
        assert!(
            verify_validity_stacked(blocks.len(), &commitment_b, offset, &stack_pd, &proof, &mut vs_bad).is_err(),
            "validity under a mismatched transcript must fail"
        );

        // A tampered pd value must be rejected too.
        let mut bad_pd = stack_pd.clone();
        bad_pd[0].1 += F128::ONE;
        let mut vs_pd = VerifierState::new(b"vstack", &bundle, &[]);
        let root_p = crate::pcs::read_commitment(&mut vs_pd).unwrap();
        let commitment_p = crate::pcs::commitment_from_root(root_p, stacked.m);
        assert!(
            verify_validity_stacked(blocks.len(), &commitment_p, offset, &bad_pd, &proof, &mut vs_pd).is_err(),
            "tampered pd value must fail"
        );
    }

    /// The Flock reduction (zerocheck + lincheck) is a clean, self-contained
    /// unit: run WITHOUT any PCS open, the prover's `(ab, c)` claims on the
    /// committed witness `q_pkd` are exactly what the verifier recovers by
    /// replaying the sub-proofs. This is the seam the PCS builds on.
    #[test]
    fn reduction_roundtrip() {
        let blocks = sample_blocks(4);
        let q_pkd = build_qpkd(&blocks);
        let dummy = vec![f(7, 9); 8];
        let stacked = crate::witness::stack(&[q_pkd.clone(), dummy]);
        let offset = stacked.placements[0].offset;

        // Prover: commit, then run ONLY the reduction (no PCS open).
        let mut ps = ProverState::new(b"reduce", &[]);
        let committed = crate::pcs::commit(&mut ps, &stacked.q);
        let (z_packed, reduced) = prove_reduction(&blocks, &committed.commitment, &mut ps);
        let bundle = ps.into_proof();

        // The reduction regenerates exactly the committed `q_pkd` sub-block.
        assert_eq!(z_packed, q_pkd, "reduction witness must equal committed q_pkd");
        assert_eq!(&stacked.q[offset..offset + z_packed.len()], z_packed.as_slice());

        // Verifier: replay the reduction and recover the claims.
        let mut vs = VerifierState::new(b"reduce", &bundle, &[]);
        let root = crate::pcs::read_commitment(&mut vs).unwrap();
        let replay = verify_reduction(blocks.len(), &root, stacked.m, &mut vs)
            .expect("reduction verifies");

        // Prover and verifier agree on the claims left for the PCS.
        assert_eq!(reduced.ab.claim, replay.ab, "ab claim mismatch");
        assert_eq!(reduced.c.claim, replay.c, "c claim mismatch");

        // A mismatched transcript domain diverges the sponge, so the recovered
        // claims must NOT match the prover's (the reduction is transcript-bound).
        let mut vs_bad = VerifierState::new(b"different", &bundle, &[]);
        let root_b = crate::pcs::read_commitment(&mut vs_bad).unwrap();
        if let Ok(replay_b) = verify_reduction(blocks.len(), &root_b, stacked.m, &mut vs_bad) {
            assert!(
                replay_b.ab != replay.ab || replay_b.c != replay.c,
                "a diverged sponge must not reproduce the prover's claims"
            );
        }
    }
}
