//! Bridge to the flock SHA-256 prover ([`flock::sha2`]), single-PCS.
//!
//! `q_flock` (flock's packed SHA-256 witness, 64 bits per `F64` word) is committed
//! as a column in leanVM-b's ONE stacked `F64` witness (§sec:stacking), with no separate flock
//! commitment. The VM's `Sha2` table binds to it by point-eval equality (its
//! value columns and `q_flock`'s slots are point-evals of the same committed
//! stack), and flock's R1CS validity is discharged by the same stacked WHIR:
//! the reduction's two tower-field claims pass through
//! [`ring_switch_open`] / [`ring_switch_verify`] and join the batch-mixed
//! opening ([`::pcs::stack_open`]).
//!
//! ## The mapping
//!
//! The VM's `Sha2(a, b, cv) -> c` is one SHA-256 compression `C(cv, a‖b)`. All
//! inputs are witness values in `q_flock`, and memory binds all three. Unlike
//! the BLAKE2s opcode it replaces there is no metadata immediate: the
//! length-prefixed Merkle-Damgard carries no per-block counter or final flag,
//! since the length rode the first block and that block is a compile-time
//! constant ([`primitives::sha2::iv_for_len`]).
//!
//! ## The layout (`H_BASE = 0`, `OUT_BASE = 256`, `M_BASE = 512`, 64-bit words)
//!
//! Each compression's `2^K_LOG` bits pack into `2^(K_LOG-6)` `F64` words (the
//! [`SLOT_STRIDE_LOG`] stride); each VM-visible 64-bit word is one whole packed
//! word at a fixed within-instance slot (bit position / 64):
//!
//! ```text
//!   cv0..cv3 = slots 0..4    c0..c3 = slots 4..8
//!   a0..a3   = slots 8..12   b0..b3 = slots 12..16
//! ```
//!
//! All compression inputs are free witness rows; the VM routes claims on all
//! sixteen aligned words directly to these slots.
//!
//! ## Byte order
//!
//! SHA-256 reads its block and writes its digest big-endian, and the VM carries
//! both as little-endian `F64` lanes. flock's bit layout absorbs the difference
//! (see `flock::sha2`'s "Big-endian, for free"), so a packed slot IS the VM's
//! `u64`; `words_of` and `pack_words` are the same relabeling on this side,
//! written through bytes so the two derivations are obviously the same one.

use crate::transcript::{ProverState, VerifierState};
use ::pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use flock::sha2::{
    Compression, K_LOG, ReductionReplay, Sha2Setup, compress, generate_witness_with_ab_packed_and_lincheck,
    min_n_blocks_log,
};
use flock::verifier::VerifyError;
use primitives::field::{F64, F192};
use zk_alloc::ArenaVec;

/// One side of the Flock reduction's output on the committed witness `q_flock`:
/// the `2^K_SKIP` bit slices at a point, already transmitted and checked by the
/// reduction (`prove_reduction` / [`verify_reduction`]), for the PCS to bind.
/// Re-exported from [`flock::sha2`].
pub use flock::sha2::SliceClaim;

// Within-instance packed-word (slot) indices of the VM-visible words: `H_BASE
// = 0` → cv words 0..4, `OUT_BASE = 256` → c words 4..8, `M_BASE = 512` → a
// words 8..12 and b words 12..16. A slot is a 64-bit packed word, so each is
// its flock bit base over 64, which the asserts below hold it to: move a
// region in `flock::sha2` and this fails to compile rather than silently
// routing a bus claim to the wrong slot.
pub const SLOT_CV0: usize = 0;
pub const SLOT_C0: usize = 4;
pub const SLOT_A0: usize = 8;
pub const SLOT_B0: usize = 12;

const _: () = assert!(SLOT_CV0 * 64 == flock::sha2::H_BASE);
const _: () = assert!(SLOT_C0 * 64 == flock::sha2::OUT_BASE);
const _: () = assert!(SLOT_A0 * 64 == flock::sha2::M_BASE);
const _: () = assert!(SLOT_B0 * 64 == flock::sha2::M_BASE + 8 * flock::sha2::WORD_BITS);
// The sixteen VM-visible words are exactly the first `[0, 1024)` bits, so
// nothing else may be placed there.
const _: () = assert!(SLOT_B0 * 64 + 4 * 64 == flock::sha2::SCHED_BASE);

/// The sixteen within-instance value slots in canonical order
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3]`, matching `tables::SHA2_VALUE_COLS`.
pub const SLOTS: [usize; 16] = [
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
    SLOT_CV0,
    SLOT_CV0 + 1,
    SLOT_CV0 + 2,
    SLOT_CV0 + 3,
];

/// Split a 64-bit VM word into the two SHA-256 words it carries: its eight
/// little-endian bytes are eight bytes of the block (or the digest), read
/// big-endian four at a time.
const fn words_of(x: F64) -> [u32; 2] {
    let b = x.0.to_le_bytes();
    [
        u32::from_be_bytes([b[0], b[1], b[2], b[3]]),
        u32::from_be_bytes([b[4], b[5], b[6], b[7]]),
    ]
}

/// Inverse of [`words_of`].
const fn pack_words(w: [u32; 2]) -> F64 {
    let (lo, hi) = (w[0].to_be_bytes(), w[1].to_be_bytes());
    F64(u64::from_le_bytes([
        lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3],
    ]))
}

/// The chaining value a 64-byte `sha2_eth` starts from, as four VM words: the
/// `Sha2` opcode's default, and what makes one opcode a complete hash of 64
/// bytes.
///
/// Derived from [`primitives::sha2::IV_64`] rather than written out, since a
/// hand-copied 32-byte constant is exactly the kind that looks plausible while
/// being wrong.
pub const IV: [F64; 4] = {
    let h = primitives::sha2::IV_64;
    [
        pack_words([h[0], h[1]]),
        pack_words([h[2], h[3]]),
        pack_words([h[4], h[5]]),
        pack_words([h[6], h[7]]),
    ]
};

/// [`IV`] as the two 192-bit VM memory cells a chaining value occupies
/// (canonical 128-bit chunks, top limbs zero).
pub const IV_CELLS: [F192; 2] = [F192::new(IV[0].0, IV[1].0, 0), F192::new(IV[2].0, IV[3].0, 0)];

/// [`IV_CELLS`] for a message of `msg_bytes` bytes:
/// `C(IV_ETH, len_block(8 · msg_bytes))` as the two cells a guest `SET`s before
/// the first block of that message.
///
/// The compiler folds this at every `sha2(..., msg_bytes = N)` site, which is
/// what keeps a known-length hash at `ceil(N / 64)` compressions: the length
/// block never reaches the VM.
pub const fn iv_cells_for_len(msg_bytes: u64) -> [F192; 2] {
    let h = primitives::sha2::iv_for_len(msg_bytes);
    [
        F192::new(pack_words([h[0], h[1]]).0, pack_words([h[2], h[3]]).0, 0),
        F192::new(pack_words([h[4], h[5]]).0, pack_words([h[6], h[7]]).0, 0),
    ]
}

/// The flock [`Compression`] for one VM instruction.
pub fn compression(a: [F64; 4], b: [F64; 4], cv: [F64; 4]) -> Compression {
    let mut m = [0u32; 16];
    for (i, &w) in a.iter().chain(b.iter()).enumerate() {
        let [lo, hi] = words_of(w);
        m[2 * i] = lo;
        m[2 * i + 1] = hi;
    }
    let mut h = [0u32; 8];
    for (i, &w) in cv.iter().enumerate() {
        let [lo, hi] = words_of(w);
        h[2 * i] = lo;
        h[2 * i + 1] = hi;
    }
    (h, m)
}

/// The 256-bit output chaining value `c = (c0..c3)` of a compression. This is
/// `sha2_eth(a‖b)` exactly when the chaining value is [`IV`].
pub fn digest(block: &Compression) -> [F64; 4] {
    let h = compress(block.0, block.1);
    std::array::from_fn(|k| pack_words([h[2 * k], h[2 * k + 1]]))
}

/// flock's `n_blocks_log` for `n` compressions (lincheck floor `≥ 3`). The VM's
/// `Sha2` table is sized to `2^n_blocks_log` rows so its value columns share
/// `q_flock`'s instance cube.
pub fn n_blocks_log(n: usize) -> usize {
    min_n_blocks_log(n)
}

/// The variable count (`log2` length) of the committed `q_flock` column for `n`
/// executed compressions: `K_LOG + n_blocks_log(max(n,1)) - 6`. Always ≥ 1
/// instance: `n = 0` still commits one padding instance (uniform proof shape).
pub fn qflock_kappa(n: usize) -> usize {
    K_LOG + n_blocks_log(n.max(1)) - LOG_PACKING
}

/// Flock-native reduction buffers emitted in the same fused pass as the
/// committed, flattened `q_flock`. They stay alive across commit, bus, and
/// constraint proving so reduction needs no second witness pass.
pub(crate) struct PreparedReductionWitness {
    n_blocks: usize,
    z_packed: ArenaVec<u64>,
    a_packed: ArenaVec<u64>,
    b_packed: ArenaVec<u64>,
    z_lincheck: ArenaVec<u8>,
}

impl PreparedReductionWitness {
    pub(crate) fn n_blocks(&self) -> usize {
        self.n_blocks
    }

    pub(crate) fn prove(&self, ps: &mut ProverState) -> SliceClaim {
        setup_for(self.n_blocks).prove_reduction_precomputed(
            &self.z_packed,
            &self.a_packed,
            &self.b_packed,
            &self.z_lincheck,
            ps,
        )
    }
}

/// Lift flock's packed witness (64 bits per word, bit `i` at position `i`) into
/// the committed `F64` column: word for word, which is exactly `pack_witness`'s
/// convention on the same bit string.
fn flatten_packed_into(packed: &[u64], out: &mut [F64]) {
    assert_eq!(out.len(), packed.len(), "q_flock's window is the wrong size");
    // In parallel, straight into the committed column's window: at scale this
    // moves hundreds of MB, so an intermediate buffer copied again afterwards is
    // not affordable.
    parallel::fill(out, |i| F64(packed[i]));
}

/// Build the committed `q_flock` column (flock's packed witness) for `blocks`, padded
/// to `2^n_blocks_log(max(blocks.len(),1))` instances (the unused ones flock's own
/// `padding_block`), and retain the Flock-native layouts produced by that same fused pass so
/// reduction does not regenerate them later. Deterministic, so it matches what the
/// reduction regenerates. An empty `blocks` yields one padding cube (all instances are
/// padding).
pub(crate) fn build_qflock_prepared(blocks: &[Compression], q_flock: &mut [F64]) -> PreparedReductionWitness {
    let n_blocks = blocks.len().max(1);
    let (z_packed, a_packed, b_packed, z_lincheck) =
        generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log(n_blocks));
    flatten_packed_into(&z_packed, q_flock);
    PreparedReductionWitness {
        n_blocks,
        z_packed,
        a_packed,
        b_packed,
        z_lincheck,
    }
}

/// `log2` of the within-instance packed span (`2^9` words): the
/// number of low coords of a `q_flock` point that carry the slot's bits, and the
/// stride between consecutive instances' same-slot words in `q_flock`. A value
/// claim on `q_flock` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING;

/// Memoized SHA-256 R1CS [`Sha2Setup`], keyed by its power-of-two shape.
/// Building it (the symbolic constraint walk over `2^K_LOG` slots) costs
/// ~hundreds of ms, fixed per circuit shape, independent of `N` or the proof.
/// So we build each shape once and reuse it across `prove`, `verify`, and
/// repeated proofs; the per-setup caches then stay warm, making verification
/// milliseconds rather than rebuilding the circuit each time.
type SetupCell = std::sync::Arc<std::sync::OnceLock<std::sync::Arc<Sha2Setup>>>;

fn setup_cache() -> &'static std::sync::Mutex<std::collections::HashMap<usize, SetupCell>> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<usize, SetupCell>>> =
        std::sync::OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

fn setup_for(n_blocks: usize) -> std::sync::Arc<Sha2Setup> {
    let shape = n_blocks_log(n_blocks);
    let cell = {
        let mut cache = setup_cache().lock().expect("SHA-256 setup cache poisoned");
        std::sync::Arc::clone(
            cache
                .entry(shape)
                .or_insert_with(|| std::sync::Arc::new(std::sync::OnceLock::new())),
        )
    };
    std::sync::Arc::clone(cell.get_or_init(|| std::sync::Arc::new(Sha2Setup::new(1usize << shape))))
}

/// Pre-build (and cache) the flock SHA-256 R1CS setup. This is the fixed,
/// circuit-shape-only cost (~hundreds of ms, independent of the witness or the
/// number of proofs): building the `2^K_LOG`-slot R1CS.
///
/// Callers pass the number of EXECUTED `Sha2` instructions; it is floored at 1
/// (the padding instance a no-`Sha2` program still carries), matching
/// `cpu::prove`/`verify`. Call it once up front so a subsequent prove/verify
/// reflects steady-state (repeated-proving) performance: the ~hundreds-of-ms
/// build is a one-time, program-independent cost, not part of proving. Idempotent.
pub fn warm_setup(n_blocks: usize) {
    let _ = setup_for(n_blocks.max(1));
}

/// The flock SHA-256 R1CS digest: a hash of the per-block R1CS matrices and
/// shape parameters ([`flock::r1cs::BlockR1cs::r1cs_digest`]), independent
/// of the instance count. The full instance is block-diagonal (the count is
/// announced and absorbed with the other sizes), so a transcript seeded with
/// this digest (via [`crate::cpu::fs_seed`]) binds the whole statement up
/// front. Baked in flock (test-guarded): recomputing it costs a pass over the
/// matrices' 384 MiB bit image, which used to land inside the first `prove`.
pub fn r1cs_digest() -> [u8; 32] {
    flock::sha2::R1CS_DIGEST
}

/// **Flock reduction only** (prover): run flock's SHA-256 zerocheck + lincheck
/// over `blocks` and return the one [`SliceClaim`] on the committed witness
/// `q_flock`, along with the regenerated packed witness (already flattened to
/// the committed `F64` packing). The sub-proof scalars ride the shared
/// transcript stream (`ps.add_scalar` at the protocol points); flock runs
/// natively in the tower field on the shared sponge. Does NOT open the PCS: the
/// caller discharges the returned claim via [`crate::pcs::open`] (as
/// [`crate::cpu`]'s prove does).
#[cfg(test)]
fn prove_reduction(blocks: &[Compression], ps: &mut ProverState) -> (Vec<F64>, SliceClaim) {
    let (z_packed, reduced) = setup_for(blocks.len()).prove_reduction(blocks, ps);
    let mut q_flock = vec![F64::ZERO; z_packed.len()];
    flatten_packed_into(&z_packed, &mut q_flock);
    (q_flock, reduced)
}

/// `q_flock` on its own, for the tests that only need the committed column.
#[cfg(test)]
fn build_qflock(blocks: &[Compression]) -> Vec<F64> {
    let mut q_flock = vec![F64::ZERO; 1 << qflock_kappa(blocks.len())];
    build_qflock_prepared(blocks, &mut q_flock);
    q_flock
}

/// **Flock reduction only** (verifier): mirror of `prove_reduction`. Replay
/// the zerocheck + lincheck sub-proofs straight off the shared stream (each
/// scalar bound as it is read), and recover the one claim on `q_flock`
/// for the PCS to discharge, plus the reassembled reduction claims
/// ([`ReductionReplay`]). The statement is already bound (the seed, the announced
/// sizes, and the commitment root on the stream), so nothing else enters here.
pub fn verify_reduction(n_blocks: usize, vs: &mut VerifierState) -> Result<ReductionReplay, VerifyError> {
    setup_for(n_blocks).verify_reduction(vs)
}

/// One reduction claim as a tower [`crate::pcs::RingSwitchClaim`]: the
/// `2^K_SKIP` bit slices and the suffix point they live at, which is the WHOLE
/// multilinear tail of the quirky point (`q_flock` has `2^(K_LOG + n_log − 6)`
/// words, and the packing prefix is exactly the skipped coordinates, so nothing
/// is split off into it). The family arrives transmitted and checked, by
/// flock's reduction, so there is nothing to tie here.
fn ring_claim(claim: &SliceClaim, qflock_vars: usize) -> crate::pcs::RingSwitchClaim {
    assert_eq!(
        claim.suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );
    assert_eq!(claim.s_hat_v.len(), PACKING_WIDTH);
    crate::pcs::RingSwitchClaim {
        suffix_point: claim.suffix_point.clone(),
        s_hat_v: Some(claim.s_hat_v.clone()),
    }
}

/// Package the prover's reduction claim ([`SliceClaim`]) as a
/// [`crate::pcs::RingSwitchOpen`], so the PCS discharges flock's validity in the
/// same opening as leanVM's point claims. `offset` is `q_flock`'s slot in the
/// committed stack; the opener slices `q_flock` from there.
pub fn ring_switch_open(n_blocks: usize, offset: usize, reduced: &SliceClaim) -> crate::pcs::RingSwitchOpen {
    let qflock_vars = qflock_kappa(n_blocks);
    crate::pcs::RingSwitchOpen {
        offset,
        qflock_vars,
        claims: vec![ring_claim(reduced, qflock_vars)],
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered claim
/// (from [`verify_reduction`]) as a [`crate::pcs::RingSwitchVerify`], the same
/// statement data; the transmitted opening travels separately (read off the
/// `openings` hint channel by the caller).
pub fn ring_switch_verify(n_blocks: usize, offset: usize, claim: &SliceClaim) -> crate::pcs::RingSwitchVerify {
    let qflock_vars = qflock_kappa(n_blocks);
    crate::pcs::RingSwitchVerify {
        offset,
        qflock_vars,
        claims: vec![ring_claim(claim, qflock_vars)],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn setup_cache_is_keyed_by_shape() {
        let one = setup_for(1);
        let eight = setup_for(8);
        let nine = setup_for(9);
        assert!(std::sync::Arc::ptr_eq(&one, &eight));
        assert!(!std::sync::Arc::ptr_eq(&eight, &nine));
    }

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
                    IV,
                )
            })
            .collect()
    }

    /// `words_of` and `pack_words` are the byte relabeling flock's layout
    /// applies on its side, so they must round-trip and must agree with reading
    /// the VM word's bytes as two big-endian SHA-256 words.
    #[test]
    fn word_packing_round_trips() {
        for x in [0u64, 1, u64::MAX, 0x0123_4567_89AB_CDEF] {
            assert_eq!(pack_words(words_of(F64(x))), F64(x));
        }
        assert_eq!(words_of(F64(0x0123_4567_89AB_CDEF)), [0xEFCD_AB89, 0x6745_2301]);
    }

    /// `q_flock`'s aligned packed slots hold the VM's 64-bit words in our field
    /// representation, and the digest matches `primitives::sha2`.
    #[test]
    fn qflock_words_match_layout() {
        let inputs: Vec<([F64; 4], [F64; 4])> = (0..5u64)
            .map(|i| {
                (
                    [f(0x1000 + i), f(0x2000 + i), f(0x3000 + i), f(0x4000 + i)],
                    [f(0x5000 + i), f(0x6000 + i), f(0x7000 + i), f(0x8000 + i)],
                )
            })
            .collect();
        let blocks: Vec<Compression> = inputs.iter().map(|&(a, b)| compression(a, b, IV)).collect();
        let q_flock = build_qflock(&blocks);
        assert_eq!(q_flock.len(), 1 << qflock_kappa(blocks.len()));

        let slot = |j: usize, s: usize| q_flock[j * (1 << SLOT_STRIDE_LOG) + s];
        for (j, (&(a, b), blk)) in inputs.iter().zip(&blocks).enumerate() {
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_A0 + k), a[k]);
                assert_eq!(slot(j, SLOT_B0 + k), b[k]);
            }
            // The opcode over the default chaining value IS `sha2_eth` of the
            // 64 message bytes.
            let mut input = [0u8; 64];
            for (s, w) in input.chunks_exact_mut(8).zip(a.into_iter().chain(b)) {
                s.copy_from_slice(&w.0.to_le_bytes());
            }
            let h = primitives::sha2::hash(&input);
            let word = |o: usize| F64(u64::from_le_bytes(h[o..o + 8].try_into().unwrap()));
            let d: [F64; 4] = std::array::from_fn(|k| word(8 * k));
            assert_eq!(digest(blk), d);
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_C0 + k), d[k]);
            }
        }
        // The chaining-value slots hold the default IV.
        for k in 0..4 {
            assert_eq!(slot(0, SLOT_CV0 + k), IV[k]);
        }
    }

    /// The Flock reduction (zerocheck + lincheck) is a clean, self-contained
    /// unit: run WITHOUT any PCS open, the prover's claim on the
    /// committed witness `q_flock` are exactly what the verifier recovers by
    /// replaying the sub-proofs. This is the seam the PCS builds on.
    #[test]
    fn reduction_roundtrip() {
        let blocks = sample_blocks(4);
        let q_flock = build_qflock(&blocks);
        let dummy = vec![f(7); 8];
        let stacked = crate::witness::stack(&[q_flock.clone(), dummy]);
        let offset = stacked.placements[0].offset;

        // Prover: commit, then run ONLY the reduction (no PCS open).
        let mut ps = ProverState::new(b"reduce", &[]);
        let _committed = crate::pcs::commit(&mut ps, &stacked.q, crate::pcs::LOG_INV_RATE);
        let (z_packed, reduced) = prove_reduction(&blocks, &mut ps);
        let bundle = ps.into_proof();

        // The reduction regenerates exactly the committed `q_flock` sub-block.
        assert_eq!(z_packed, q_flock, "reduction witness must equal committed q_flock");
        assert_eq!(&stacked.q[offset..offset + z_packed.len()], z_packed.as_slice());

        // Verifier: replay the reduction and recover the claims.
        let mut vs = VerifierState::new(b"reduce", &bundle, &[]);
        let _root = crate::pcs::read_commitment(&mut vs).unwrap();
        let replay = verify_reduction(blocks.len(), &mut vs).expect("reduction verifies");

        // Prover and verifier agree on the claim left for the PCS.
        assert_eq!(reduced, replay.claim, "reduction claim mismatch");

        // A mismatched transcript domain diverges the sponge, so the recovered
        // claims must NOT match the prover's (the reduction is transcript-bound).
        let mut vs_bad = VerifierState::new(b"different", &bundle, &[]);
        let _root_b = crate::pcs::read_commitment(&mut vs_bad).unwrap();
        if let Ok(replay_b) = verify_reduction(blocks.len(), &mut vs_bad) {
            assert!(
                replay_b.claim != replay.claim,
                "a diverged sponge must not reproduce the prover's claim"
            );
        }
    }

    /// flock's validity claims, discharged by ONE stacked WHIR over a
    /// hand-stacked witness containing `q_flock` (plus a dummy column) together
    /// with an ordinary point claim: the full prove_reduction → ring-switch →
    /// stack_open seam without the VM pipeline. Proves and verifies on the
    /// shared transcript; a mismatched domain and a tampered point value are
    /// rejected.
    #[test]
    fn validity_stacked_roundtrip() {
        let blocks = sample_blocks(4);
        let q_flock = build_qflock(&blocks);
        let dummy: Vec<F64> = (0..8u64).map(|i| f(0x9000 + i)).collect();
        let stacked = crate::witness::stack(&[q_flock.clone(), dummy.clone()]);
        let offset = stacked.placements[0].offset;

        // One ordinary point claim on the dummy column (exercises the point-claim
        // path of the single fused opening).
        let dummy_pl = stacked.placements[1];
        let low_point: Vec<F192> = (0..dummy_pl.n_vars)
            .map(|i| F192::new(0x100 + i as u64, 0x7, 0x55))
            .collect();
        let pd_value = primitives::multilinear::mle_eval(&dummy, &low_point);
        let points = vec![crate::pcs::SlotClaim::Point {
            offset: dummy_pl.offset,
            low_point: low_point.clone(),
            value: pd_value,
        }];

        let mut ps = ProverState::new(b"vstack", &[]);
        let committed = crate::pcs::commit(&mut ps, &stacked.q, crate::pcs::LOG_INV_RATE);
        let (_z, reduced) = prove_reduction(&blocks, &mut ps);
        let ring = ring_switch_open(blocks.len(), offset, &reduced);
        crate::pcs::open(&mut ps, &committed, &stacked.q, &points, &ring);
        let bundle = ps.into_proof();

        let run = |label: &'static [u8], points: &[crate::pcs::SlotClaim]| -> Result<(), &'static str> {
            let mut vs = VerifierState::new(label, &bundle, &[]);
            let root = crate::pcs::read_commitment(&mut vs).map_err(|_| "root")?;
            let replay = verify_reduction(blocks.len(), &mut vs).map_err(|_| "reduction")?;
            let ring = ring_switch_verify(blocks.len(), offset, &replay.claim);
            crate::pcs::verify(&mut vs, points, &ring, stacked.m, crate::pcs::LOG_INV_RATE, &root)
                .map_err(|_| "opening")?;
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
            *value += F192::ONE;
        }
        assert!(run(b"vstack", &bad_points).is_err(), "tampered point value must fail");
    }
}
