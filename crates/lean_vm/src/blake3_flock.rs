//! Bridge to the flock BLAKE3 prover ([`flock::blake3`]), single-PCS.
//!
//! `q_pkd` (flock's packed BLAKE3 witness, 64 bits per `F64` word) is committed
//! as a column in leanVM-b's ONE stacked `K`-witness (§3.1) — no separate flock
//! commitment. The VM's `BLAKE3` table binds to it by point-eval equality (its
//! value columns and `q_pkd`'s slots are point-evals of the same committed
//! stack), and flock's R1CS validity is discharged by the same stacked Ligerito-K:
//! the reduction's two claims cross from flock's GHASH world into the tower via
//! [`ring_switch_open`] / [`ring_switch_verify`] and join the batch-mixed
//! opening ([`::pcs::stack_open_k`]).
//!
//! ## The mapping
//!
//! The VM's `BLAKE3(a, b) -> c` is a flock single-block compression with the
//! chaining value fixed to the BLAKE3 IV, counter `0`, block length `64`, flags
//! `CHUNK_START | CHUNK_END | ROOT` (= [`FLAGS`]) — exactly `blake3::hash` of the
//! 64-byte message `a‖b`, matching `cpu::blake3_compress`.
//!
//! ## The layout (aligned re-layout, `M_BASE = 640`, 64-bit words)
//!
//! Each compression's `2^K_LOG` bits pack into [`PACKED_PER_INSTANCE`]`
//! = 2^(K_LOG-6)` `F64` words; each VM-visible 64-bit word is one whole packed
//! word at a fixed within-instance slot (bit position / 64):
//!
//! ```text
//!   c0..c3 = slots 4..8      a0..a3 = slots 10..14    b0..b3 = slots 14..18
//!   cv = slots 0..4 (= IV)   counter = slot 18        blen‖flags = slot 19
//! ```
//!
//! cv and the counter / blen‖flags slots hold constants baked into the
//! per-block matrices (constant rows), so no claims are needed to pin them.

use primitives::field::{F64, F128, F128T, ghash_to_tower};
use crate::transcript::{ProverState, VerifierState};
use ::pcs::pack_k::{LOG_PACKING_K, PACKING_WIDTH_K};
use primitives::multilinear::lagrange_weights_naive_t;
use flock::blake3::{
    Blake3Setup, Compression, K_LOG, ReducedClaims, ReductionReplay, blake3_compress,
    generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
};
use flock::verifier::VerifyError;

/// A `ẑ(point) = value` claim on the committed witness `q_pkd`, recovered by the
/// Flock zerocheck + lincheck reduction ([`prove_reduction`] / [`verify_reduction`])
/// and later discharged by the PCS. Re-exported from [`flock::proof`] (GHASH-
/// typed; [`ring_switch_verify`] maps it into the tower).
pub use flock::proof::ZClaim;

/// flock flags for a single 64-byte root block: `CHUNK_START(1) | CHUNK_END(2) |
/// ROOT(8) = 11` — the configuration under which the compression output equals
/// `blake3::hash` of the 64-byte input. Baked into flock's per-block matrices
/// (constant rows), along with `cv = IV`, `counter = 0` and `block_len = 64`.
pub const FLAGS: u32 = flock::blake3::PINNED_FLAGS;

/// Packed `F64` words per compression instance: `K / 64 = 2^(K_LOG-6)`.
/// Instance `j` occupies packed indices `[j*PACKED_PER_INSTANCE, (j+1)*…)`.
pub const PACKED_PER_INSTANCE: usize = 1 << (K_LOG - LOG_PACKING_K);

// Within-instance packed-word (slot) indices of the VM-visible words, fixed by
// the aligned flock layout (bit bases asserted by `layout_constants` there):
// `OUT_LO_BASE = 256` → c words 4..8, `M_BASE = 640` → a words 10..14 and
// b words 14..18.
pub const SLOT_C0: usize = 4;
pub const SLOT_A0: usize = 10;
pub const SLOT_B0: usize = 14;

/// The twelve within-instance value slots in canonical order
/// `[a0..a3, b0..b3, c0..c3]`, matching `tables::BLAKE3_VALUE_COLS`.
pub const SLOTS: [usize; 12] = [
    SLOT_A0,
    SLOT_A0 + 1,
    SLOT_A0 + 2,
    SLOT_A0 + 3,
    SLOT_B0,
    SLOT_B0 + 1,
    SLOT_B0 + 2,
    SLOT_B0 + 3,
    SLOT_C0,
    SLOT_C0 + 1,
    SLOT_C0 + 2,
    SLOT_C0 + 3,
];


/// Split a 64-bit field element into the two little-endian `u32` words flock's
/// message uses — the VM memory byte order.
fn words_of(x: F64) -> [u32; 2] {
    [x.0 as u32, (x.0 >> 32) as u32]
}

/// Inverse of [`words_of`]: pack two little-endian `u32` words into the `F64`.
pub fn pack_words(w: [u32; 2]) -> F64 {
    F64((w[0] as u64) | ((w[1] as u64) << 32))
}

/// The flock [`Compression`] for one VM `BLAKE3(a, b)`: message `m = a‖b` under
/// the pinned configuration (`cv = IV`, counter `0`, block length `64`, flags
/// [`FLAGS`] — all enforced by the matrices' constant rows).
pub fn compression(a: [F64; 4], b: [F64; 4]) -> Compression {
    let mut m = [0u32; 16];
    for (i, &w) in a.iter().enumerate() {
        m[2 * i..2 * i + 2].copy_from_slice(&words_of(w));
    }
    for (i, &w) in b.iter().enumerate() {
        m[8 + 2 * i..8 + 2 * i + 2].copy_from_slice(&words_of(w));
    }
    flock::blake3::pinned_compression(m)
}

/// The 256-bit digest `c = (c0..c3)` of a compression (= flock's `out_lo` =
/// `blake3::hash(a‖b)`).
pub fn digest(block: &Compression) -> [F64; 4] {
    let st = blake3_compress(&block.0, &block.1, block.2, block.3, block.4);
    std::array::from_fn(|k| pack_words([st[2 * k], st[2 * k + 1]]))
}

/// flock's `n_blocks_log` for `n` compressions (lincheck floor `≥ 3`). The VM's
/// BLAKE3 table is sized to `2^n_blocks_log` rows so its value columns share
/// `q_pkd`'s instance cube.
pub fn n_blocks_log(n: usize) -> usize {
    min_n_blocks_log(n)
}

/// The variable count (`log2` length) of the committed `q_pkd` column for `n`
/// executed compressions: `K_LOG + n_blocks_log(max(n,1)) - 6`. Always ≥ 1
/// instance — `n = 0` still commits one padding instance (uniform proof shape).
pub fn qpkd_kappa(n: usize) -> usize {
    K_LOG + n_blocks_log(n.max(1)) - LOG_PACKING_K
}

/// The padding instance: the pinned compression of the all-zero message, i.e.
/// `blake3(0^64)` — what flock's witness generation fills unused slots with.
/// Synthesized as the sole block when a program executes no BLAKE3, so `q_pkd`
/// and the reduction always have ≥ 1 instance.
pub fn padding_compression() -> Compression {
    flock::blake3::padding_block()
}

/// Flatten flock's GHASH-packed witness (128 bits per `F128` word, bit `i` at
/// position `i`) into the committed `F64` packing (64 bits per word): word `j`
/// becomes words `2j` (lo lanes, bits 0..64) and `2j+1` (hi lanes, bits
/// 64..128), which is exactly `pack_witness_k`'s convention on the same bit string.
fn flatten_packed(packed: Vec<F128>) -> Vec<F64> {
    let mut out = Vec::with_capacity(packed.len() * 2);
    for w in packed {
        out.push(F64(w.lo));
        out.push(F64(w.hi));
    }
    out
}

/// Build the committed `q_pkd` column (flock's packed witness) for `blocks`, padded
/// to `2^n_blocks_log(max(blocks.len(),1))` instances (the unused ones
/// [`padding_compression`] blocks). Deterministic, so it matches what the reduction
/// regenerates. An empty `blocks` yields one padding cube (all instances are padding).
pub fn build_qpkd(blocks: &[Compression]) -> Vec<F64> {
    flatten_packed(generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log(blocks.len().max(1))).0)
}

/// The digest `(c0..c3)` of [`padding_compression`], i.e. `blake3(0^64)`. It is
/// NONZERO, so the VM pads its BLAKE3 output value columns with this.
pub fn padding_digest() -> [F64; 4] {
    digest(&padding_compression())
}

/// `log2` of the within-instance packed span (`PACKED_PER_INSTANCE = 2^8`): the
/// number of low coords of a `q_pkd` point that carry the slot's bits, and the
/// stride between consecutive instances' same-slot words in `q_pkd`. A value
/// claim on `q_pkd` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING_K;

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
/// over `blocks` and return the two claims [`ReducedClaims`] on the committed
/// witness `q_pkd` — `ab` (`A∘B`, lincheck) and `c` (`C`, zerocheck) — along
/// with the regenerated packed witness (already flattened to the committed
/// `F64` packing). The sub-proof scalars ride the shared transcript stream
/// (`ps.add_scalar` at the protocol points); flock runs entirely in its GHASH
/// world on the shared sponge, only the claims cross into the tower
/// ([`ring_switch_open`]). Does NOT open the PCS: the caller discharges the
/// returned claims via [`crate::pcs::open`] (as [`crate::cpu`]'s prove does).
/// The statement is already transcript-bound (the fs_seed, the announced
/// sizes, and the commitment root on the stream), so `commitment` is only a
/// symmetry witness that the caller committed first.
pub fn prove_reduction(
    blocks: &[Compression],
    commitment: &::pcs::ligerito_k::CommitmentK,
    ps: &mut ProverState,
) -> (Vec<F64>, ReducedClaims) {
    let _ = commitment;
    let (z_packed, reduced) = setup_for(blocks.len()).prove_reduction(blocks, ps);
    (flatten_packed(z_packed), reduced)
}

/// **Flock reduction only** (verifier): mirror of [`prove_reduction`]. Replay
/// the zerocheck + lincheck sub-proofs straight off the shared stream (each
/// scalar bound as it is read), and recover the two `(ab, c)` claims on `q_pkd`
/// for the PCS to discharge — plus the reassembled reduction claims
/// ([`ReductionReplay`]). `root`/`mu` are symmetry witnesses (the statement is
/// bound via the seed + announced sizes + the root on the stream).
pub fn verify_reduction(
    n_blocks: usize,
    root: &[u8; 32],
    mu: usize,
    vs: &mut VerifierState,
) -> Result<ReductionReplay, VerifyError> {
    let _ = (root, mu);
    setup_for(n_blocks).verify_reduction(vs)
}

/// One flock claim as a tower [`crate::pcs::RingSwitchClaimK`]: the quirky point
/// splits at the packing boundary. Its univariate-skip coordinate `z_skip`
/// covers exactly the `k_skip = LOG_PACKING_K = 6` packed variables, so the
/// packing prefix is the 64 φ8-Lagrange weights at `z_skip`, and the WHOLE
/// multilinear tail `x_inner_rest ++ x_outer` is the suffix point (`q_pkd` has
/// `2^(K_LOG + n_log − 6)` words: one more variable than the old F128 stack, and
/// no coordinate is split off into the prefix). Everything crosses from GHASH to
/// the tower through the field isomorphism `ghash_to_tower`, under which the
/// claim identity `value = Σ_i L_i(z_skip)·ŝ_i(suffix)` transports exactly (the
/// bit-slice MLEs have F2 coefficients, which the isomorphism fixes).
fn ring_claim(z: &ZClaim, s_hat_v128: Option<&[F128]>, qpkd_vars: usize) -> crate::pcs::RingSwitchClaimK {
    // flock's claim is now native tower (F128T): its point, value, and the φ₈
    // weights need no isomorphism. Only `s_hat_v` remains a GHASH capture
    // (prover-side; the verifier passes `None`), so it alone crosses via
    // `ghash_to_tower` below.
    let prefix_weights: Vec<F128T> = lagrange_weights_naive_t(LOG_PACKING_K, z.point.z_skip);
    let mut suffix_point: Vec<F128T> = z.point.x_inner_rest.clone();
    suffix_point.extend_from_slice(&z.point.x_outer);
    // Length invariant: prefix (6) + suffix == K_LOG + n_blocks_log, i.e. the
    // suffix spans exactly the committed q_pkd cube.
    assert_eq!(
        suffix_point.len(),
        qpkd_vars,
        "ring-switch suffix must span the q_pkd cube"
    );
    // Precomputed s_hat_v (prover side): flock's reduction captures the 128
    // bit-slice MLEs w.r.t. its OWN 128-bit packing, whose prefix absorbs
    // z_skip AND the first inner-rest coordinate `c`; the 64-bit packing here
    // keeps `c` in the suffix. The 64-wide values recombine linearly: 64-word
    // `y = 2y' + b` is the b-half of 128-word `y'`, and bit `i` of that half
    // is bit `i + 64b` of the 128-word, so
    //     s64[i] = (1+c)·s128[i] + c·s128[i+64].
    // Exact field arithmetic under the GHASH→tower isomorphism, so the values
    // are bit-identical to the fold the opener would otherwise run (and are
    // hard-checked against the claim in `ring_switch_k::prove`).
    let s_hat_v = s_hat_v128.and_then(|s128| {
        if s128.len() != 2 * PACKING_WIDTH_K || z.point.x_inner_rest.is_empty() {
            return None;
        }
        let c = z.point.x_inner_rest[0];
        let one_plus_c = F128T::ONE + c;
        Some(
            (0..PACKING_WIDTH_K)
                .map(|i| {
                    one_plus_c * ghash_to_tower(s128[i]) + c * ghash_to_tower(s128[i + PACKING_WIDTH_K])
                })
                .collect(),
        )
    });
    crate::pcs::RingSwitchClaimK {
        prefix_weights,
        suffix_point,
        value: z.value,
        s_hat_v,
    }
}

/// Package the prover's reduction claims ([`ReducedClaims`]) as a
/// [`crate::pcs::RingSwitchOpen`], so the PCS discharges flock's `(ab, c)`
/// validity in the SAME opening as leanVM's point claims. `offset` is `q_pkd`'s
/// slot in the committed stack; the opener slices `q_pkd` from there.
pub fn ring_switch_open(n_blocks: usize, offset: usize, reduced: &ReducedClaims) -> crate::pcs::RingSwitchOpen {
    let qpkd_vars = qpkd_kappa(n_blocks);
    crate::pcs::RingSwitchOpen {
        offset,
        qpkd_vars,
        claims: vec![
            ring_claim(&reduced.ab.claim, reduced.ab.s_hat_v.as_deref(), qpkd_vars),
            ring_claim(&reduced.c.claim, reduced.c.s_hat_v.as_deref(), qpkd_vars),
        ],

    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered `(ab, c)`
/// claims (from [`verify_reduction`]) as a [`crate::pcs::RingSwitchVerify`], the
/// same statement data; the transmitted opening travels separately (read off the
/// `openings` hint channel by the caller).
pub fn ring_switch_verify(n_blocks: usize, offset: usize, ab: ZClaim, c: ZClaim) -> crate::pcs::RingSwitchVerify {
    let qpkd_vars = qpkd_kappa(n_blocks);
    crate::pcs::RingSwitchVerify {
        offset,
        qpkd_vars,
        claims: vec![ring_claim(&ab, None, qpkd_vars), ring_claim(&c, None, qpkd_vars)],
    }
}

// (No write/read_stack_proof: flock's scalar sub-proof rides the shared stream
// via add_scalar/next_scalar at its protocol points, exactly like leanVM's own
// scalars; the one Merkle-bearing stacked opening rides the `openings` hint
// channel.)

#[cfg(test)]
mod tests {
    use super::*;

    fn f(x: u64) -> F64 {
        F64(x)
    }

    fn sample_blocks(n: usize) -> Vec<Compression> {
        (0..n as u64)
            .map(|i| {
                compression(
                    [
                        f(0x11 * (i + 1)),
                        f(0x22 * (i + 1)),
                        f(0x33 * (i + 1)),
                        f(0x44 * (i + 1)),
                    ],
                    [
                        f(0x55 * (i + 1)),
                        f(0x66 * (i + 1)),
                        f(0x77 * (i + 1)),
                        f(0x88 * (i + 1)),
                    ],
                )
            })
            .collect()
    }

    /// `q_pkd`'s aligned packed slots hold the VM's 64-bit words in our field
    /// representation, and the digest matches the `blake3` crate.
    #[test]
    fn qpkd_words_match_layout() {
        let inputs: Vec<([F64; 4], [F64; 4])> = (0..5u64)
            .map(|i| {
                (
                    [f(0x1000 + i), f(0x2000 + i), f(0x3000 + i), f(0x4000 + i)],
                    [f(0x5000 + i), f(0x6000 + i), f(0x7000 + i), f(0x8000 + i)],
                )
            })
            .collect();
        let blocks: Vec<Compression> = inputs.iter().map(|&(a, b)| compression(a, b)).collect();
        let q_pkd = build_qpkd(&blocks);
        assert_eq!(q_pkd.len(), 1 << qpkd_kappa(blocks.len()));

        let slot = |j: usize, s: usize| q_pkd[j * PACKED_PER_INSTANCE + s];
        for (j, (&(a, b), blk)) in inputs.iter().zip(&blocks).enumerate() {
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_A0 + k), a[k]);
                assert_eq!(slot(j, SLOT_B0 + k), b[k]);
            }
            let mut input = [0u8; 64];
            for (s, w) in input.chunks_exact_mut(8).zip(a.into_iter().chain(b)) {
                s.copy_from_slice(&w.0.to_le_bytes());
            }
            let h = *blake3::hash(&input).as_bytes();
            let word = |o: usize| F64(u64::from_le_bytes(h[o..o + 8].try_into().unwrap()));
            let d: [F64; 4] = std::array::from_fn(|k| word(8 * k));
            assert_eq!(digest(blk), d);
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_C0 + k), d[k]);
            }
        }
        // Constant slots (matrix-pinned): cv = IV in slots 0..4, the zero
        // counter word in slot 18, and the packed block_len‖flags word in slot 19.
        let iv = flock::blake3::BLAKE3_IV;
        for k in 0..4 {
            assert_eq!(slot(0, k), pack_words([iv[2 * k], iv[2 * k + 1]]));
        }
        assert_eq!(slot(0, 18), pack_words([0, 0]));
        assert_eq!(slot(0, 19), pack_words([64, FLAGS]));
    }

    /// The Flock reduction (zerocheck + lincheck) is a clean, self-contained
    /// unit: run WITHOUT any PCS open, the prover's `(ab, c)` claims on the
    /// committed witness `q_pkd` are exactly what the verifier recovers by
    /// replaying the sub-proofs. This is the seam the PCS builds on.
    #[test]
    fn reduction_roundtrip() {
        let blocks = sample_blocks(4);
        let q_pkd = build_qpkd(&blocks);
        let dummy = vec![f(7); 8];
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

    /// flock's validity claims, discharged by ONE stacked Ligerito-K over a
    /// hand-stacked witness containing `q_pkd` (plus a dummy column) together
    /// with an ordinary point claim: the full prove_reduction → ring-switch →
    /// stack_open seam without the VM pipeline. Proves and verifies on the
    /// shared transcript; a mismatched domain and a tampered point value are
    /// rejected.
    #[test]
    fn validity_stacked_roundtrip() {
        let blocks = sample_blocks(4);
        let q_pkd = build_qpkd(&blocks);
        let dummy: Vec<F64> = (0..8u64).map(|i| f(0x9000 + i)).collect();
        let stacked = crate::witness::stack(&[q_pkd.clone(), dummy.clone()]);
        let offset = stacked.placements[0].offset;

        // One ordinary point claim on the dummy column (exercises the point-claim
        // path of the single fused opening).
        let dummy_pl = stacked.placements[1];
        let low_point: Vec<F128T> = (0..dummy_pl.n_vars)
            .map(|i| F128T::new(0x100 + i as u64, 0x7))
            .collect();
        let pd_value = primitives::multilinear::mle_eval(&dummy, &low_point);
        let points = vec![crate::pcs::SlotClaim::Point {
            offset: dummy_pl.offset,
            low_point: low_point.clone(),
            value: pd_value,
        }];

        let mut ps = ProverState::new(b"vstack", &[]);
        let committed = crate::pcs::commit(&mut ps, &stacked.q);
        let (_z, reduced) = prove_reduction(&blocks, &committed.commitment, &mut ps);
        let ring = ring_switch_open(blocks.len(), offset, &reduced);
        let open = crate::pcs::open(&mut ps, &committed, &stacked.q, &points, &ring);
        ps.hint_opening(open);
        let bundle = ps.into_proof();

        let run = |label: &'static [u8], points: &[crate::pcs::SlotClaim]| -> Result<(), &'static str> {
            let mut vs = VerifierState::new(label, &bundle, &[]);
            let root = crate::pcs::read_commitment(&mut vs).map_err(|_| "root")?;
            let replay = verify_reduction(blocks.len(), &root, stacked.m, &mut vs)
                .map_err(|_| "reduction")?;
            let open = vs.next_opening().map_err(|_| "opening hint")?;
            let ring = ring_switch_verify(blocks.len(), offset, replay.ab, replay.c);
            crate::pcs::verify(&mut vs, points, &ring, open, stacked.m, &root).map_err(|_| "opening")?;
            vs.finish().map_err(|_| "leftover")
        };

        run(b"vstack", &points).expect("validity verifies");

        // A mismatched transcript (different domain) diverges the shared sponge,
        // so the stacked opening must be rejected.
        assert!(
            run(b"different-domain", &points).is_err(),
            "validity under a mismatched transcript must fail"
        );

        // A tampered point value must be rejected too.
        let mut bad_points = points.clone();
        if let crate::pcs::SlotClaim::Point { value, .. } = &mut bad_points[0] {
            *value += F128T::ONE;
        }
        assert!(run(b"vstack", &bad_points).is_err(), "tampered point value must fail");
    }
}
