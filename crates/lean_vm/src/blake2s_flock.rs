//! Bridge to the flock BLAKE2s prover ([`flock::blake2s`]), single-PCS.
//!
//! `q_flock` (flock's packed BLAKE2s witness, 64 bits per `F64` word) is committed
//! as a column in leanVM-b's ONE stacked `F64` witness (§sec:stacking), with no separate flock
//! commitment. The VM's `BLAKE2s` table binds to it by point-eval equality (its
//! value columns and `q_flock`'s slots are point-evals of the same committed
//! stack), and flock's R1CS validity is discharged by the same stacked WHIR:
//! the reduction's two tower-field claims pass through
//! [`ring_switch_open`] / [`ring_switch_verify`] and join the batch-mixed
//! opening ([`::pcs::stack_open`]).
//!
//! ## The mapping
//!
//! The VM's `BLAKE2s(a, b, cv, metadata) -> c` is one standard BLAKE2s
//! compression. `metadata` packs `counter:u64 | f0:u32 | f1:u32` in
//! little-endian order. All inputs are witness values in `q_flock`; memory binds
//! `a`, `b`, and `cv`, while the bytecode interaction binds `metadata`.
//!
//! ## The layout (aligned re-layout, `M_BASE = 640`, 64-bit words)
//!
//! Each compression's `2^K_LOG` bits pack into `2^(K_LOG-6)` `F64` words (the
//! [`SLOT_STRIDE_LOG`] stride); each VM-visible 64-bit word is one whole packed
//! word at a fixed within-instance slot (bit position / 64):
//!
//! ```text
//!   c0..c3 = slots 4..8      a0..a3 = slots 10..14    b0..b3 = slots 14..18
//!   cv0..cv3 = slots 0..4    counter = slot 18        f0‖f1 = slot 19
//! ```
//!
//! All compression inputs are free witness rows; the VM routes claims on all
//! eighteen aligned words directly to these slots.

use crate::transcript::{ProverState, VerifierState};
use ::pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use flock::blake2s::{
    Blake2sSetup, Compression, K_LOG, PackedWitnessClaims, ReductionReplay, blake2s_compress,
    generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
};
use flock::verifier::VerifyError;
use primitives::field::{F64, F192};
use primitives::multilinear::lagrange_weights_naive;
use zk_alloc::ArenaVec;

/// A `ẑ(point) = value` claim on the committed witness `q_flock`, recovered by the
/// Flock zerocheck + lincheck reduction (`prove_reduction` / [`verify_reduction`])
/// and later discharged by the PCS. Re-exported from [`flock::proof`].
pub use flock::proof::ZClaim;

/// BLAKE2s's final-block flag `f0`, which RFC 7693 sets to all ones on the last
/// block. A hash-shaped compression is one 64-byte final block, so it is always
/// set there.
pub const FINAL_FLAG: u32 = flock::blake2s::PINNED_F0;
/// The byte counter of the one 64-byte block a hash-shaped compression absorbs.
pub const PINNED_T: u64 = flock::blake2s::PINNED_T;

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

    pub(crate) fn prove(&self, ps: &mut ProverState) -> PackedWitnessClaims {
        setup_for(self.n_blocks).prove_reduction_precomputed(
            &self.z_packed,
            &self.a_packed,
            &self.b_packed,
            &self.z_lincheck,
            ps,
        )
    }
}

// Within-instance packed-word (slot) indices of the VM-visible words, fixed by
// the aligned flock layout (bit bases asserted by `layout_constants` there):
// `CV_BASE = 0` → cv words 0..4, `OUT_LO_BASE = 256` → c words 4..8, `M_BASE
// = 640` → a words 10..14 and b words 14..18, metadata (counter, f0‖f1)
// words 18..20.
pub const SLOT_CV0: usize = 0;
pub const SLOT_C0: usize = 4;
pub const SLOT_A0: usize = 10;
pub const SLOT_B0: usize = 14;
pub const SLOT_METADATA: usize = 18;

/// The eighteen within-instance value slots in canonical order
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]`, matching
/// `tables::BLAKE2S_VALUE_COLS`.
pub const SLOTS: [usize; 18] = [
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
    SLOT_METADATA,
    SLOT_METADATA + 1,
];

/// Split a 64-bit field element into the two little-endian `u32` words flock's
/// message uses (the VM memory byte order).
fn words_of(x: F64) -> [u32; 2] {
    [x.0 as u32, (x.0 >> 32) as u32]
}

/// Inverse of `words_of`: pack two little-endian `u32` words into the `F64`.
fn pack_words(w: [u32; 2]) -> F64 {
    F64((w[0] as u64) | ((w[1] as u64) << 32))
}

/// Pack BLAKE2s's compression metadata as one little-endian 128-bit value in
/// the two low K-lanes of a 192-bit word (top lane zero).
pub const fn metadata(counter: u64, f0: u32, f1: u32) -> F192 {
    F192::new(counter, (f0 as u64) | ((f1 as u64) << 32), 0)
}

/// Unpack `counter:u64 | f0:u32 | f1:u32` from a 192-bit word (the top lane
/// must be zero).
pub const fn unpack_metadata(x: F192) -> (u64, u32, u32) {
    assert!(x.c2 == 0, "BLAKE2s metadata must have a zero top lane");
    (x.c0, x.c1 as u32, (x.c1 >> 32) as u32)
}

/// BLAKE2s-256's initial chaining value as four flock words (the two
/// chaining-value cells' low lanes, in canonical lane order). This is the IV
/// with the parameter block (digest length 32, unkeyed, fanout and depth 1)
/// folded into word 0, which is what makes a 64-byte compression equal
/// `blake2s` of those 64 bytes.
///
/// Derived from [`flock::blake2s::param_iv`] rather than written out: the
/// parameter block touches three bytes of word 0, and a hand-copied constant
/// that XORs only the low byte still looks plausible.
pub const IV: [F64; 4] = {
    const fn w(lo: u32, hi: u32) -> F64 {
        F64((lo as u64) | ((hi as u64) << 32))
    }
    let h = flock::blake2s::param_iv();
    [w(h[0], h[1]), w(h[2], h[3]), w(h[4], h[5]), w(h[6], h[7])]
};

/// The initial chaining value as the two 192-bit VM memory cells a chaining
/// value occupies (canonical 128-bit chunks, top limbs zero).
pub const IV_CELLS: [F192; 2] = [F192::new(IV[0].0, IV[1].0, 0), F192::new(IV[2].0, IV[3].0, 0)];

/// The flock [`Compression`] for one VM instruction.
pub fn compression(a: [F64; 4], b: [F64; 4], cv: [F64; 4], meta: F192) -> Compression {
    let mut m = [0u32; 16];
    for (i, &w) in a.iter().enumerate() {
        m[2 * i..2 * i + 2].copy_from_slice(&words_of(w));
    }
    for (i, &w) in b.iter().enumerate() {
        m[8 + 2 * i..8 + 2 * i + 2].copy_from_slice(&words_of(w));
    }
    let mut cv_words = [0u32; 8];
    for (i, &w) in cv.iter().enumerate() {
        cv_words[2 * i..2 * i + 2].copy_from_slice(&words_of(w));
    }
    let (counter, f0, f1) = unpack_metadata(meta);
    (cv_words, m, counter, f0, f1)
}

/// The 256-bit output chaining value `c = (c0..c3)` of an arbitrary
/// compression. This is `blake2s(a‖b)` only for the parameterized [`IV`] and
/// one-block final metadata (counter 64, `f0` set).
pub fn digest(block: &Compression) -> [F64; 4] {
    let h = blake2s_compress(&block.0, &block.1, block.2, block.3, block.4);
    std::array::from_fn(|k| pack_words([h[2 * k], h[2 * k + 1]]))
}

/// flock's `n_blocks_log` for `n` compressions (lincheck floor `≥ 3`). The VM's
/// BLAKE2s table is sized to `2^n_blocks_log` rows so its value columns share
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

/// Lift flock's packed witness (64 bits per word, bit `i` at position `i`) into
/// the committed `F64` column: word for word, which is exactly `pack_witness`'s
/// convention on the same bit string.
fn flatten_packed_into(packed: &[u64], out: &mut [F64]) {
    assert_eq!(out.len(), packed.len(), "q_flock's window is the wrong size");
    // In parallel, straight into the committed column's window: at scale this
    // moves 270 MB, so an intermediate buffer copied again afterwards is not
    // affordable.
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

/// `log2` of the within-instance packed span (`2^8` words): the
/// number of low coords of a `q_flock` point that carry the slot's bits, and the
/// stride between consecutive instances' same-slot words in `q_flock`. A value
/// claim on `q_flock` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING;

/// Memoized BLAKE2s R1CS [`Blake2sSetup`], keyed by its power-of-two shape.
/// Building it (the symbolic constraint walk over `2^K_LOG` slots) costs
/// ~hundreds of ms, fixed per circuit shape, independent of `N` or the proof.
/// So we build each shape once and reuse it across `prove`, `verify`, and
/// repeated proofs; the per-setup caches then stay warm, making verification
/// milliseconds rather than rebuilding the circuit each time.
type SetupCell = std::sync::Arc<std::sync::OnceLock<std::sync::Arc<Blake2sSetup>>>;

fn setup_cache() -> &'static std::sync::Mutex<std::collections::HashMap<usize, SetupCell>> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<usize, SetupCell>>> =
        std::sync::OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

fn setup_for(n_blocks: usize) -> std::sync::Arc<Blake2sSetup> {
    let shape = n_blocks_log(n_blocks);
    let cell = {
        let mut cache = setup_cache().lock().expect("BLAKE2s setup cache poisoned");
        std::sync::Arc::clone(
            cache
                .entry(shape)
                .or_insert_with(|| std::sync::Arc::new(std::sync::OnceLock::new())),
        )
    };
    std::sync::Arc::clone(cell.get_or_init(|| std::sync::Arc::new(Blake2sSetup::new(1usize << shape))))
}

/// Pre-build (and cache) the flock BLAKE2s R1CS setup. This is the fixed,
/// circuit-shape-only cost (~hundreds of ms, independent of the witness or the
/// number of proofs): building the `2^K_LOG`-slot R1CS.
///
/// Callers pass the number of EXECUTED `BLAKE2s` instructions; it is floored at 1
/// (the padding instance a no-BLAKE2s program still carries), matching
/// `cpu::prove`/`verify`. Call it once up front so a subsequent prove/verify
/// reflects steady-state (repeated-proving) performance: the ~hundreds-of-ms
/// build is a one-time, program-independent cost, not part of proving. Idempotent.
pub fn warm_setup(n_blocks: usize) {
    let _ = setup_for(n_blocks.max(1));
}

/// The flock BLAKE2s circuit-FAMILY digest: a hash of the per-block R1CS
/// matrices and shape parameters ([`family_digest`] on the R1CS), independent
/// of the instance count. The full instance is block-diagonal (the count is
/// announced and absorbed with the other sizes), so a transcript seeded with
/// this digest (via [`crate::cpu::fs_seed`]) binds the whole statement up
/// front. Baked in flock (test-guarded): recomputing it costs ~300 ms of
/// matrix building + hashing, which used to land inside the first `prove`.
pub fn family_digest() -> [u8; 32] {
    flock::blake2s::FAMILY_DIGEST
}

/// **Flock reduction only** (prover): run flock's BLAKE2s zerocheck + lincheck
/// over `blocks` and return the two [`PackedWitnessClaims`] on the committed
/// witness `q_flock`, `ab` (`A∘B`, lincheck) and `c` (`C`, zerocheck), along
/// with the regenerated packed witness (already flattened to the committed
/// `F64` packing). The sub-proof scalars ride the shared transcript stream
/// (`ps.add_scalar` at the protocol points); flock runs natively in the tower
/// field on the shared sponge. Does NOT open the PCS: the caller discharges the
/// returned claims via [`crate::pcs::open`] (as [`crate::cpu`]'s prove does).
#[cfg(test)]
fn prove_reduction(blocks: &[Compression], ps: &mut ProverState) -> (Vec<F64>, PackedWitnessClaims) {
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
/// scalar bound as it is read), and recover the two `(ab, c)` claims on `q_flock`
/// for the PCS to discharge, plus the reassembled reduction claims
/// ([`ReductionReplay`]). The statement is already bound (the seed, the announced
/// sizes, and the commitment root on the stream), so nothing else enters here.
pub fn verify_reduction(n_blocks: usize, vs: &mut VerifierState) -> Result<ReductionReplay, VerifyError> {
    setup_for(n_blocks).verify_reduction(vs)
}

/// One flock claim as a tower [`crate::pcs::RingSwitchClaim`]: the quirky point
/// splits at the packing boundary. Its univariate-skip coordinate `z_skip`
/// covers exactly the `k_skip = LOG_PACKING = 6` packed variables, so the
/// packing prefix is the 64 φ8-Lagrange weights at `z_skip`, and the WHOLE
/// multilinear tail `x_inner_rest ++ x_outer` is the suffix point (`q_flock` has
/// `2^(K_LOG + n_log − 6)` words, and no coordinate is split off into the
/// prefix).
fn ring_claim(z: &ZClaim, captured: Option<&[F192]>, qflock_vars: usize) -> crate::pcs::RingSwitchClaim {
    let prefix_weights: Vec<F192> = lagrange_weights_naive(LOG_PACKING, z.point.z_skip);
    let mut suffix_point: Vec<F192> = z.point.x_inner_rest.clone();
    suffix_point.extend_from_slice(&z.point.x_outer);
    // Length invariant: prefix (6) + suffix == K_LOG + n_blocks_log, i.e. the
    // suffix spans exactly the committed q_flock cube.
    assert_eq!(
        suffix_point.len(),
        qflock_vars,
        "ring-switch suffix must span the q_flock cube"
    );
    // Precomputed s_hat_v (prover side): flock's reduction captures the 128
    // bit-slice MLEs w.r.t. its OWN 128-bit packing, whose prefix absorbs
    // z_skip AND the first inner-rest coordinate `c`; the 64-bit packing here
    // keeps `c` in the suffix. The 64-wide values recombine linearly: 64-word
    // `y = 2y' + b` is the b-half of 128-word `y'`, and bit `i` of that half
    // is bit `i + 64b` of the 128-word, so
    //     s64[i] = (1+c)·s128[i] + c·s128[i+64].
    // Lincheck already captures the 64 slices expected by the K ring switch.
    // Zerocheck's fused kernel captures two 64-slice banks around the first
    // suffix coordinate; fold that coordinate here without rescanning q_flock.
    let s_hat_v = captured.and_then(|s| match s.len() {
        PACKING_WIDTH => Some(s.to_vec()),
        n if n == 2 * PACKING_WIDTH && !z.point.x_inner_rest.is_empty() => {
            let c = z.point.x_inner_rest[0];
            Some(
                (0..PACKING_WIDTH)
                    .map(|i| (F192::ONE + c) * s[i] + c * s[i + PACKING_WIDTH])
                    .collect(),
            )
        }
        _ => None,
    });
    crate::pcs::RingSwitchClaim {
        prefix_weights,
        suffix_point,
        value: z.value,
        s_hat_v,
    }
}

/// Package the prover's reduction claims ([`PackedWitnessClaims`]) as a
/// [`crate::pcs::RingSwitchOpen`], so the PCS discharges flock's `(ab, c)`
/// validity in the same opening as leanVM's point claims. `offset` is `q_flock`'s
/// slot in the committed stack; the opener slices `q_flock` from there.
pub fn ring_switch_open(n_blocks: usize, offset: usize, reduced: &PackedWitnessClaims) -> crate::pcs::RingSwitchOpen {
    let qflock_vars = qflock_kappa(n_blocks);
    crate::pcs::RingSwitchOpen {
        offset,
        qflock_vars,
        prebound: 1,
        claims: vec![
            ring_claim(&reduced.ab.claim, reduced.ab.s_hat_v.as_deref(), qflock_vars),
            ring_claim(&reduced.c.claim, reduced.c.s_hat_v.as_deref(), qflock_vars),
        ],
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered `(ab, c)`
/// claims (from [`verify_reduction`]) as a [`crate::pcs::RingSwitchVerify`], the
/// same statement data; the transmitted opening travels separately (read off the
/// `openings` hint channel by the caller).
pub fn ring_switch_verify(
    n_blocks: usize,
    offset: usize,
    ab: ZClaim,
    c: ZClaim,
    ab_s_hat_v: &[F192],
) -> crate::pcs::RingSwitchVerify {
    let qflock_vars = qflock_kappa(n_blocks);
    crate::pcs::RingSwitchVerify {
        offset,
        qflock_vars,
        reconstructed: vec![ab_s_hat_v.to_vec()],
        claims: vec![ring_claim(&ab, None, qflock_vars), ring_claim(&c, None, qflock_vars)],
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
                    metadata(PINNED_T, FINAL_FLAG, 0),
                )
            })
            .collect()
    }

    /// `q_flock`'s aligned packed slots hold the VM's 64-bit words in our field
    /// representation, and the digest matches the `blake2s` crate.
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
        let blocks: Vec<Compression> = inputs
            .iter()
            .map(|&(a, b)| compression(a, b, IV, metadata(PINNED_T, FINAL_FLAG, 0)))
            .collect();
        let q_flock = build_qflock(&blocks);
        assert_eq!(q_flock.len(), 1 << qflock_kappa(blocks.len()));

        let slot = |j: usize, s: usize| q_flock[j * (1 << SLOT_STRIDE_LOG) + s];
        for (j, (&(a, b), blk)) in inputs.iter().zip(&blocks).enumerate() {
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_A0 + k), a[k]);
                assert_eq!(slot(j, SLOT_B0 + k), b[k]);
            }
            let mut input = [0u8; 64];
            for (s, w) in input.chunks_exact_mut(8).zip(a.into_iter().chain(b)) {
                s.copy_from_slice(&w.0.to_le_bytes());
            }
            let h = primitives::blake2s::hash(&input);
            let word = |o: usize| F64(u64::from_le_bytes(h[o..o + 8].try_into().unwrap()));
            let d: [F64; 4] = std::array::from_fn(|k| word(8 * k));
            assert_eq!(digest(blk), d);
            for k in 0..4 {
                assert_eq!(slot(j, SLOT_C0 + k), d[k]);
            }
        }
        // Input slots for this one-block hash: the parameterized initial chaining
        // value in slots 0..4, the byte counter in slot 18, and the packed
        // f0‖f1 flag word in slot 19.
        let iv = flock::blake2s::param_iv();
        for k in 0..4 {
            assert_eq!(slot(0, k), pack_words([iv[2 * k], iv[2 * k + 1]]));
        }
        assert_eq!(slot(0, 18), pack_words([PINNED_T as u32, 0]));
        assert_eq!(slot(0, 19), pack_words([FINAL_FLAG, 0]));
    }

    /// The Flock reduction (zerocheck + lincheck) is a clean, self-contained
    /// unit: run WITHOUT any PCS open, the prover's `(ab, c)` claims on the
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

        // Prover and verifier agree on the claims left for the PCS.
        assert_eq!(reduced.ab.claim, replay.ab, "ab claim mismatch");
        assert_eq!(reduced.c.claim, replay.c, "c claim mismatch");

        // A mismatched transcript domain diverges the sponge, so the recovered
        // claims must NOT match the prover's (the reduction is transcript-bound).
        let mut vs_bad = VerifierState::new(b"different", &bundle, &[]);
        let _root_b = crate::pcs::read_commitment(&mut vs_bad).unwrap();
        if let Ok(replay_b) = verify_reduction(blocks.len(), &mut vs_bad) {
            assert!(
                replay_b.ab != replay.ab || replay_b.c != replay.c,
                "a diverged sponge must not reproduce the prover's claims"
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
            let ring = ring_switch_verify(blocks.len(), offset, replay.ab, replay.c, &replay.lc_claim.s_hat_v);
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
