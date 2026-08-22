//! Bridge to the flock Keccak prover ([`flock::sha3`]), single-PCS.
//!
//! `q_flock` (flock's packed Keccak witness, 64 bits per `F64` word) is committed
//! as a column in leanVM-b's ONE stacked `F64` witness (§sec:stacking), with no separate flock
//! commitment. The VM's `Keccak` table binds to it by point-eval equality (its
//! value columns and `q_flock`'s slots are point-evals of the same committed
//! stack), and flock's R1CS validity is discharged by the same stacked WHIR:
//! the reduction's two tower-field claims pass through
//! [`ring_switch_open`] / [`ring_switch_verify`] and join the batch-mixed
//! opening ([`::pcs::stack_open`]).
//!
//! ## The mapping
//!
//! The VM's `Keccak(st_in) -> st_out` is one Keccak-f[1600] permutation. Both
//! states are 25 lanes of 64 bits, which the VM carries as thirteen 128-bit
//! cells with the thirteenth cell's high lane forced to zero. All fifty-two
//! words are witness values in `q_flock`, and memory binds every one of them:
//! this opcode has no bytecode-borne immediate at all, a permutation having no
//! counter and no flags.
//!
//! ## The layout (64-bit words, one Keccak lane per word)
//!
//! Each permutation's `2^K_LOG` bits pack into `2^(K_LOG-6)` `F64` words (the
//! [`SLOT_STRIDE_LOG`] stride); each VM-visible 64-bit word is one whole packed
//! word at a fixed within-instance slot (bit position / 64):
//!
//! ```text
//!   input  lanes 0..25 = slots  0..25,  slot 25 = zero pad
//!   output lanes 0..25 = slots 26..51,  slot 51 = zero pad
//! ```
//!
//! The pad slots are empty rows in the R1CS, so it forces them to zero, and the
//! bus in turn forces the VM cell's high lane to zero. All permutation inputs
//! are free witness rows; the VM routes claims on all fifty-two aligned words
//! directly to these slots.

use crate::transcript::{ProverState, VerifierState};
use ::pcs::pack::{LOG_PACKING, PACKING_WIDTH};
use flock::sha3::{
    Compression, K_LOG, ReductionReplay, STATE_LANES, Sha3Setup, generate_witness_with_ab_packed_and_lincheck,
    min_n_blocks_log, permute,
};

/// Flock words one state region occupies: the 25 lanes plus the alignment pad.
/// Re-exported so the VM table can size its value columns from it.
pub use flock::sha3::STATE_WORDS;
use flock::verifier::VerifyError;
use primitives::field::{F64, F192};
use primitives::stream::Stream;
use zk_alloc::ArenaVec;

/// One side of the Flock reduction's output on the committed witness `q_flock`:
/// the `2^K_SKIP` bit slices at a point, already transmitted and checked by the
/// reduction (`prove_reduction` / [`verify_reduction`]), for the PCS to bind.
/// Re-exported from [`flock::sha3`].
pub use flock::sha3::SliceClaim;

/// VM cells one state occupies: thirteen 128-bit cells hold the 25 lanes plus
/// the zero pad.
pub const STATE_CELLS: usize = STATE_WORDS / 2;
/// Cells of the input state the opcode addresses independently, holding lanes
/// `0..8`: the message half of a 64-byte hash.
pub const IN_CELLS: usize = 4;
/// Cells of the input state the opcode reads from one base, holding lanes
/// `8..26`: the constant pad of a 64-byte hash.
pub const REST_CELLS: usize = STATE_CELLS - IN_CELLS;

/// The nine `rest` cells of SHA3-256's 64-byte pad: `0x06` at message byte 64
/// (lane 8's low byte) and `0x80` at byte 135 (lane 16's high byte), the rest
/// zero. A cell the VM never writes reads as zero, so only two of the nine
/// carry an instruction.
pub const PAD64_REST: [F192; REST_CELLS] = {
    let mut cells = [F192::new(0, 0, 0); REST_CELLS];
    // lane 8 is cell 4's low lane, the first `rest` cell.
    cells[0] = F192::new(primitives::sha3::DOMAIN as u64, 0, 0);
    // lane 16 is cell 8's low lane, the fifth `rest` cell.
    cells[4] = F192::new(0x80u64 << 56, 0, 0);
    cells
};

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

// Within-instance packed-word (slot) indices of the VM-visible words, which
// are the flock layout's own word indices: the input region is words
// `0..STATE_WORDS` and the output region the `STATE_WORDS` after it.
pub const SLOT_IN0: usize = flock::sha3::W_IN;
pub const SLOT_OUT0: usize = flock::sha3::W_OUT;

/// The fifty-two within-instance value slots in canonical order, the input
/// state's words then the output state's, matching `tables::KECCAK_VALUE_COLS`.
/// Word `2c + l` is lane `l` of cell `c`, and the last word of each region is
/// the zero pad.
pub const SLOTS: [usize; 2 * STATE_WORDS] = {
    let mut slots = [0usize; 2 * STATE_WORDS];
    let mut i = 0;
    while i < STATE_WORDS {
        slots[i] = SLOT_IN0 + i;
        slots[STATE_WORDS + i] = SLOT_OUT0 + i;
        i += 1;
    }
    slots
};

/// The flock [`Compression`] (the 25-lane input state) for one VM instruction,
/// read from the thirteen cells of the state buffer. The thirteenth cell's high
/// lane is the layout's zero pad and is not part of the state; the R1CS forces
/// it to zero, so a nonzero one cannot verify.
pub fn compression(cells: &[F192; STATE_CELLS]) -> Compression {
    std::array::from_fn(|i| if i % 2 == 0 { cells[i / 2].c0 } else { cells[i / 2].c1 })
}

/// The permuted state, which is what the VM writes to the output cells.
pub fn permuted(block: &Compression) -> Compression {
    let mut out = *block;
    permute(&mut out);
    out
}

/// The output state as the thirteen 192-bit VM memory cells it occupies
/// (canonical 128-bit chunks, top limbs zero, the last cell's high lane the
/// layout's zero pad).
pub fn out_cells(state: &Compression) -> [F192; STATE_CELLS] {
    std::array::from_fn(|c| {
        let lo = state[2 * c];
        let hi = if 2 * c + 1 < STATE_LANES { state[2 * c + 1] } else { 0 };
        F192::new(lo, hi, 0)
    })
}

/// flock's `n_blocks_log` for `n` permutations (lincheck floor `≥ 3`). The VM's
/// Keccak table is sized to `2^n_blocks_log` rows so its value columns share
/// `q_flock`'s instance cube.
pub fn n_blocks_log(n: usize) -> usize {
    min_n_blocks_log(n)
}

/// The variable count (`log2` length) of the committed `q_flock` column for `n`
/// executed permutations: `K_LOG + n_blocks_log(max(n,1)) - 6`. Always ≥ 1
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
    // moves hundreds of MB, so an intermediate buffer copied again afterwards is not
    // affordable. Nothing reads the window until the commitment encodes it, by
    // which time a column this size is long evicted, so it publishes streamed.
    // SAFETY: `F64` is `repr(transparent)` over `u64`, so the two slices are the
    // same bytes.
    let words: &mut [u64] = unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len()) };
    parallel::chunks_mut_zip(words, packed, 1 << 14, |_, dst, src| Stream::new().copy(dst, src));
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

/// `log2` of the within-instance packed span (`2^10` words): the
/// number of low coords of a `q_flock` point that carry the slot's bits, and the
/// stride between consecutive instances' same-slot words in `q_flock`. A value
/// claim on `q_flock` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING;

/// Memoized Keccak R1CS [`Sha3Setup`], keyed by its power-of-two shape.
/// Building it (the symbolic constraint walk over `2^K_LOG` slots) costs
/// ~hundreds of ms, fixed per circuit shape, independent of `N` or the proof.
/// So we build each shape once and reuse it across `prove`, `verify`, and
/// repeated proofs; the per-setup caches then stay warm, making verification
/// milliseconds rather than rebuilding the circuit each time.
type SetupCell = std::sync::Arc<std::sync::OnceLock<std::sync::Arc<Sha3Setup>>>;

fn setup_cache() -> &'static std::sync::Mutex<std::collections::HashMap<usize, SetupCell>> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<usize, SetupCell>>> =
        std::sync::OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

fn setup_for(n_blocks: usize) -> std::sync::Arc<Sha3Setup> {
    let shape = n_blocks_log(n_blocks);
    let cell = {
        let mut cache = setup_cache().lock().expect("Keccak setup cache poisoned");
        std::sync::Arc::clone(
            cache
                .entry(shape)
                .or_insert_with(|| std::sync::Arc::new(std::sync::OnceLock::new())),
        )
    };
    std::sync::Arc::clone(cell.get_or_init(|| std::sync::Arc::new(Sha3Setup::new(1usize << shape))))
}

/// Pre-build (and cache) the flock Keccak R1CS setup. This is the fixed,
/// circuit-shape-only cost (~hundreds of ms, independent of the witness or the
/// number of proofs): building the `2^K_LOG`-slot R1CS.
///
/// Callers pass the number of EXECUTED `Keccak` instructions; it is floored at 1
/// (the padding instance a no-Keccak program still carries), matching
/// `cpu::prove`/`verify`. Call it once up front so a subsequent prove/verify
/// reflects steady-state (repeated-proving) performance: the ~hundreds-of-ms
/// build is a one-time, program-independent cost, not part of proving. Idempotent.
pub fn warm_setup(n_blocks: usize) {
    let _ = setup_for(n_blocks.max(1));
}

/// **Flock reduction only** (prover): run flock's Keccak zerocheck + lincheck
/// over `blocks` and return the one [`SliceClaim`] on the committed witness
/// `q_flock`, along with the regenerated packed witness (already flattened to
/// the committed `F64` packing). The sub-proof scalars ride the shared
/// transcript stream (`ps.add_scalar` at the protocol points); flock runs
/// natively in the tower field on the shared transcript. Does NOT open the PCS: the
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
/// multilinear tail of the quirky point (`q_flock` has `2^(K_LOG + n_log - 6)`
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

    /// `n` distinct input states, as the VM would present them: thirteen cells
    /// with a zero pad in the thirteenth cell's high lane.
    fn sample_blocks(n: usize) -> Vec<Compression> {
        (0..n as u64)
            .map(|i| {
                let cells: [F192; STATE_CELLS] = std::array::from_fn(|c| {
                    let hi = if 2 * c + 1 < STATE_LANES {
                        0x1111_1111 * (c as u64 + 1) ^ i
                    } else {
                        0
                    };
                    F192::new(0x0101_0101 * (c as u64 + 1) ^ (i << 8), hi, 0)
                });
                compression(&cells)
            })
            .collect()
    }

    /// A state buffer's thirteen cells and the 25 lanes are the same words, and
    /// the thirteenth cell's high lane is the pad.
    #[test]
    fn cells_and_lanes_are_the_same_words() {
        let block = sample_blocks(1)[0];
        let cells = out_cells(&block);
        assert_eq!(compression(&cells), block);
        assert_eq!(
            cells[STATE_CELLS - 1].c1,
            0,
            "the thirteenth cell's high lane is the pad"
        );
    }

    /// `q_flock`'s aligned packed slots hold the VM's 64-bit words in our field
    /// representation, input state then permuted output, and the permutation is
    /// the one `primitives::sha3` computes.
    #[test]
    fn qflock_words_match_layout() {
        let blocks = sample_blocks(5);
        let q_flock = build_qflock(&blocks);
        assert_eq!(q_flock.len(), 1 << qflock_kappa(blocks.len()));

        let slot = |j: usize, s: usize| q_flock[j * (1 << SLOT_STRIDE_LOG) + s];
        for (j, block) in blocks.iter().enumerate() {
            let out = permuted(block);
            for lane in 0..STATE_LANES {
                assert_eq!(slot(j, SLOT_IN0 + lane), f(block[lane]), "instance {j}, in lane {lane}");
                assert_eq!(slot(j, SLOT_OUT0 + lane), f(out[lane]), "instance {j}, out lane {lane}");
            }
            // The two alignment pads, which the R1CS forces to zero.
            assert_eq!(slot(j, SLOT_IN0 + STATE_LANES), F64::ZERO);
            assert_eq!(slot(j, SLOT_OUT0 + STATE_LANES), F64::ZERO);
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
        let _committed = crate::pcs::commit(&mut ps, &stacked.q, stacked.shape, crate::pcs::LOG_INV_RATE);
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

        // A mismatched transcript domain diverges the state, so the recovered
        // claims must NOT match the prover's (the reduction is transcript-bound).
        let mut vs_bad = VerifierState::new(b"different", &bundle, &[]);
        let _root_b = crate::pcs::read_commitment(&mut vs_bad).unwrap();
        if let Ok(replay_b) = verify_reduction(blocks.len(), &mut vs_bad) {
            assert!(
                replay_b.claim != replay.claim,
                "a diverged transcript must not reproduce the prover's claim"
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
        let committed = crate::pcs::commit(&mut ps, &stacked.q, stacked.shape, crate::pcs::LOG_INV_RATE);
        let (_z, reduced) = prove_reduction(&blocks, &mut ps);
        let ring = ring_switch_open(blocks.len(), offset, &reduced);
        crate::pcs::open(&mut ps, &committed, &stacked.q, &points, &ring);
        let bundle = ps.into_proof();

        let run = |label: &'static [u8], points: &[crate::pcs::SlotClaim]| -> Result<(), &'static str> {
            let mut vs = VerifierState::new(label, &bundle, &[]);
            let root = crate::pcs::read_commitment(&mut vs).map_err(|_| "root")?;
            let replay = verify_reduction(blocks.len(), &mut vs).map_err(|_| "reduction")?;
            let ring = ring_switch_verify(blocks.len(), offset, &replay.claim);
            crate::pcs::verify(&mut vs, points, &ring, stacked.shape, crate::pcs::LOG_INV_RATE, &root)
                .map_err(|_| "opening")?;
            vs.finish().map_err(|_| "leftover")
        };

        run(b"vstack", &points).expect("validity verifies");

        // A mismatched transcript (different domain) diverges the shared state,
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
