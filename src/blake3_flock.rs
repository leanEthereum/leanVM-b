//! Bridge to the vendored flock BLAKE3 prover (`flock_prover`), single-PCS.
//!
//! `q_pkd` (flock's packed BLAKE3 witness) is committed as a column in leanVM-b's
//! ONE stacked witness (§3.1) — no separate flock commitment. The VM's `BLAKE3`
//! table binds to it by point-eval equality (its value columns and `q_pkd`'s
//! slots are point-evals of the same committed stack), and flock's R1CS validity
//! is discharged by a Ligerito over that same stacked commitment
//! ([`flock_prover::r1cs_hashes::blake3::Blake3Setup::prove_validity_stacked`],
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
//!   cv = slots 0,1 (= IV)    counter‖blen‖flags = slot 9 (pinned constants)
//! ```

use crate::field::F128;
use crate::transcript::{ProverState, VerifierState};
use flare::pcs::LOG_PACKING;
use flock_prover::pcs::{Commitment, ProverData};
use flock_prover::r1cs_hashes::blake3::{
    BLAKE3_IV, Blake3Setup, Blake3StackProof, Compression, K_LOG, ReducedClaims, blake3_compress,
    generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
};
use flock_prover::verifier::VerifyError;

/// A `ẑ(point) = value` claim on the committed witness `q_pkd`, recovered by the
/// Flock zerocheck + lincheck reduction ([`prove_reduction`] / [`verify_reduction`])
/// and later discharged by the PCS. Re-exported from `flock_prover`.
pub use flock_prover::proof::ZClaim;

/// flock flags for a single 64-byte root block: `CHUNK_START(1) | CHUNK_END(2) |
/// ROOT(8) = 11` — the configuration under which the compression output equals
/// `blake3::hash` of the 64-byte input.
pub const FLAGS: u32 = (1 << 0) | (1 << 1) | (1 << 3);

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

/// Within-instance slots pinned to PUBLIC constants: `cv` (slots 0,1 = the IV)
/// and the packed `counter‖counter_hi‖block_len‖flags` word (slot 9). Pinning
/// them makes the proven compression a real BLAKE3-of-64-bytes.
pub const PIN_SLOTS: [usize; 3] = [0, 1, 9];

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

/// The flock [`Compression`] for one VM `BLAKE3(a, b)`: `cv = IV`, message
/// `m = a‖b`, counter `0`, block length `64`, flags [`FLAGS`].
pub fn compression(a: [F128; 2], b: [F128; 2]) -> Compression {
    let mut m = [0u32; 16];
    m[0..4].copy_from_slice(&words_of(a[0]));
    m[4..8].copy_from_slice(&words_of(a[1]));
    m[8..12].copy_from_slice(&words_of(b[0]));
    m[12..16].copy_from_slice(&words_of(b[1]));
    (BLAKE3_IV, m, 0, 64, FLAGS)
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
/// compressions: `K_LOG + n_blocks_log - 7`, or `0` (a size-1 dummy) when `n=0`.
pub fn qpkd_kappa(n: usize) -> usize {
    if n == 0 { 0 } else { K_LOG + n_blocks_log(n) - LOG_PACKING }
}

/// Build the committed `q_pkd` column (flock's packed witness) for `blocks`.
/// Deterministic, so it matches what `prove_validity_stacked` regenerates.
pub fn build_qpkd(blocks: &[Compression]) -> Vec<F128> {
    generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log(blocks.len())).0
}

/// The output `(c0, c1)` of flock's padding compression — the all-zero input
/// `([0;8],[0;16],0,0,0)` that fills padding instances (const-wire pin). Its
/// output is NONZERO, so the VM pads its BLAKE3 output value columns with this.
pub fn padding_digest() -> [F128; 2] {
    digest(&([0u32; 8], [0u32; 16], 0, 0, 0))
}

/// The PUBLIC constants the [`PIN_SLOTS`] hold on a real instance, in PIN_SLOTS
/// order: `cv[0..4]`, `cv[4..8]` (the IV), and `(counter_lo=0, counter_hi=0,
/// block_len=64, flags=11)` packed. Padding instances hold 0.
pub fn pin_constants() -> [F128; 3] {
    [
        pack_words([BLAKE3_IV[0], BLAKE3_IV[1], BLAKE3_IV[2], BLAKE3_IV[3]]),
        pack_words([BLAKE3_IV[4], BLAKE3_IV[5], BLAKE3_IV[6], BLAKE3_IV[7]]),
        pack_words([0, 0, 64, FLAGS]),
    ]
}

/// `log2` of the within-instance packed span (`PACKED_PER_INSTANCE = 2^7`): the
/// number of low coords in a [`slot_point`] that carry the slot's bits, and the
/// stride between consecutive instances' same-slot coords in `q_pkd`. A value
/// claim on `q_pkd` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING;

/// The `q_pkd`-column MLE point selecting within-instance `slot` over the
/// instance cube `rho`: the low 7 coords are `slot`'s bits (LSB-first), the high
/// `n_log` coords are `rho`.
pub fn slot_point(slot: usize, rho: &[F128]) -> Vec<F128> {
    let mut p: Vec<F128> = (0..SLOT_STRIDE_LOG)
        .map(|b| if (slot >> b) & 1 == 1 { F128::ONE } else { F128::ZERO })
        .collect();
    p.extend_from_slice(rho);
    p
}

/// Prove `blocks` are valid compressions, discharging the proof against the
/// caller's already-committed `stack` (with `q_pkd` the aligned sub-block at
/// `stack_offset`), reusing its `prover_data`/`commitment`. On the shared
/// transcript `ps`.
/// Memoized BLAKE3 R1CS [`Blake3Setup`], keyed by the executed-instance count.
/// Building it (the symbolic constraint walk over `2^K_LOG` slots) and its
/// statement digest cost ~hundreds of ms — fixed per circuit shape, independent
/// of `N` or the proof. So we build each shape once and reuse it across `prove`,
/// `verify`, and repeated proofs; the per-setup digest/CSC caches then stay warm,
/// making verification milliseconds rather than rebuilding the circuit each time.
///
/// The cache is bounded ([`SETUP_CACHE_CAP`]): `verify` calls this with the
/// PROVER-ANNOUNCED count, so an attacker cycling distinct counts could otherwise
/// grow it without limit. Past the cap we build an ephemeral (uncached) setup —
/// correct, just not memoized; legit workloads use only a handful of sizes.
const SETUP_CACHE_CAP: usize = 256;

fn setup_for(n_blocks: usize) -> std::sync::Arc<Blake3Setup> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<usize, std::sync::Arc<Blake3Setup>>>> =
        std::sync::OnceLock::new();
    let cache = CACHE.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    let mut map = cache.lock().expect("BLAKE3 setup cache poisoned");
    if let Some(s) = map.get(&n_blocks) {
        return std::sync::Arc::clone(s);
    }
    let setup = std::sync::Arc::new(Blake3Setup::new(n_blocks));
    if map.len() < SETUP_CACHE_CAP {
        map.insert(n_blocks, std::sync::Arc::clone(&setup));
    }
    setup
}

/// Pre-build (and cache) the flock BLAKE3 R1CS setup for `n_blocks` compressions,
/// warming BOTH the circuit and the statement-digest caches. This is the fixed,
/// circuit-shape-only cost (~hundreds of ms, independent of the witness or the
/// number of proofs): building the `2^K_LOG`-slot R1CS and hashing it.
///
/// Call it once up front for a given BLAKE3 instance count to take it off the
/// critical path, so a subsequent [`crate::cpu::prove`]/[`crate::cpu::verify`]
/// reflects steady-state (repeated-proving) performance. `n_blocks` is the number
/// of executed `BLAKE3` instructions (the BLAKE3 table's row count). Idempotent.
pub fn warm_setup(n_blocks: usize) {
    if n_blocks == 0 {
        return;
    }
    let setup = setup_for(n_blocks);
    let _ = setup.r1cs.statement_digest(); // warm the digest cache too
}

/// **Flock reduction only** (prover): run flock's BLAKE3 zerocheck + lincheck
/// over `blocks`, binding to `commitment`, and return the two claims
/// [`ReducedClaims`] on the committed witness `q_pkd` — `ab` (`A∘B`, lincheck)
/// and `c` (`C`, zerocheck) — along with the regenerated packed witness and the
/// transmitted zerocheck / lincheck sub-proofs. Does NOT open the PCS: the
/// caller discharges the returned claims (see [`prove_validity_stacked`]). This
/// is the clean seam the PCS builds on.
pub fn prove_reduction(
    blocks: &[Compression],
    commitment: &Commitment,
    ps: &mut ProverState,
) -> (
    Vec<F128>,
    flock_prover::zerocheck::ZerocheckProof,
    flock_prover::lincheck::LincheckProof,
    ReducedClaims,
) {
    setup_for(blocks.len()).prove_reduction(blocks, commitment, ps)
}

/// **Flock reduction only** (verifier): mirror of [`prove_reduction`]. Rebuild the
/// stack commitment from `root`/`mu`, replay the `zerocheck` + `lincheck`
/// sub-proofs (binding to it), and recover the two `(ab, c)` claims on `q_pkd`
/// for the PCS to discharge. In a full proof these sub-proofs live in
/// [`Blake3StackProof`] (`proof.zerocheck` / `proof.lincheck`).
pub fn verify_reduction(
    n_blocks: usize,
    root: &[u8; 32],
    mu: usize,
    zerocheck: &flock_prover::zerocheck::ZerocheckProof,
    lincheck: &flock_prover::lincheck::LincheckProof,
    vs: &mut VerifierState,
) -> Result<(ZClaim, ZClaim), VerifyError> {
    let commitment = crate::pcs::commitment_from_root(*root, mu);
    setup_for(n_blocks).verify_reduction(&commitment, zerocheck, lincheck, vs)
}

/// The multilinear tail `x_inner_rest ++ x_outer` of a quirky point — the
/// `x_outer_full` the PCS ring-switch front-end consumes.
fn x_outer_full(point: &flock_prover::lincheck::QuirkyPoint) -> Vec<F128> {
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
        padding: flock_prover::zerocheck::PaddingSpec {
            k_log: setup.r1cs.k_log,
            useful_bits_per_block: setup.r1cs.useful_bits,
        },
    }
}

/// Verifier counterpart of [`ring_switch_open`]: package the recovered `(ab, c)`
/// claims (from [`verify_reduction`]) plus the transmitted opening as a
/// [`crate::pcs::RingSwitchVerify`].
pub fn ring_switch_verify<'a>(
    n_blocks: usize,
    offset: usize,
    ab: ZClaim,
    c: ZClaim,
    open: &'a crate::pcs::BatchOpeningProofLigerito,
) -> crate::pcs::RingSwitchVerify<'a> {
    crate::pcs::RingSwitchVerify {
        offset,
        qpkd_vars: qpkd_kappa(n_blocks),
        values: vec![ab.value, c.value],
        z_skips: vec![ab.point.z_skip, c.point.z_skip],
        x_outers: vec![x_outer_full(&ab.point), x_outer_full(&c.point)],
        open,
    }
}

/// Carry flock's BLAKE3 sub-proof on leanVM's [`crate::transcript::Proof`]
/// channels — no dedicated field. The scalar reduction (`zerocheck`, `lincheck`,
/// and the opening's `ring_switches`) is serialized onto the `stream` as pure
/// transport ([`ProverState::hint_bytes`]: NOT re-absorbed — the verifier's
/// reduction/opening replay is the sole binder), and the one Merkle-bearing
/// Ligerito rides the `openings` hint channel like every other PCS opening.
/// Mirrored by [`read_stack_proof`].
pub fn write_stack_proof(
    ps: &mut ProverState,
    zerocheck: flock_prover::zerocheck::ZerocheckProof,
    lincheck: flock_prover::lincheck::LincheckProof,
    open: crate::pcs::BatchOpeningProofLigerito,
) {
    let crate::pcs::BatchOpeningProofLigerito { ring_switches, ligerito } = open;
    let bytes = bincode::serialize(&(zerocheck, lincheck, ring_switches))
        .expect("flock BLAKE3 sub-proof serializes");
    ps.hint_bytes(&bytes);
    ps.hint_opening(ligerito);
}

/// Verifier side of [`write_stack_proof`]: read flock's scalar reduction back off
/// the `stream` (raw — not re-absorbed) and its Ligerito off the `openings`
/// channel, reassembling `(zerocheck, lincheck, open)` for [`verify_reduction`]
/// and [`ring_switch_verify`].
#[allow(clippy::type_complexity)]
pub fn read_stack_proof(
    vs: &mut VerifierState,
) -> Result<
    (
        flock_prover::zerocheck::ZerocheckProof,
        flock_prover::lincheck::LincheckProof,
        crate::pcs::BatchOpeningProofLigerito,
    ),
    crate::transcript::Error,
> {
    let bytes = vs.next_hint_bytes()?;
    let (zerocheck, lincheck, ring_switches): (
        flock_prover::zerocheck::ZerocheckProof,
        flock_prover::lincheck::LincheckProof,
        Vec<flare::pcs::RingSwitchProof>,
    ) = bincode::deserialize(&bytes).map_err(|_| crate::transcript::Error::MissingHint)?;
    let ligerito = vs.next_opening()?.clone();
    Ok((zerocheck, lincheck, crate::pcs::BatchOpeningProofLigerito { ring_switches, ligerito }))
}

/// Prove `blocks` are valid compressions in two clean phases, discharging the
/// proof against the caller's already-committed `stack` (with `q_pkd` the aligned
/// sub-block at `stack_offset`), reusing its `prover_data`/`commitment`, on the
/// shared transcript `ps`:
/// 1. the Flock reduction ([`prove_reduction`]): zerocheck + lincheck → the
///    `(ab, c)` claims on `q_pkd`;
/// 2. the PCS: one stacked Ligerito discharging those claims together with the
///    caller's `stack_pd` point claims.
#[allow(clippy::too_many_arguments)]
pub fn prove_validity_stacked(
    blocks: &[Compression],
    stack: &[F128],
    stack_offset: usize,
    prover_data: &ProverData,
    commitment: &Commitment,
    stack_pd: &[(Vec<F128>, F128)],
    ps: &mut ProverState,
) -> Blake3StackProof {
    setup_for(blocks.len())
        .prove_validity_stacked(blocks, stack, stack_offset, prover_data, commitment, stack_pd, ps)
}

/// Verifier side of [`prove_validity_stacked`], in the same two phases:
/// [`verify_reduction`] (replay zerocheck + lincheck → `(ab, c)` claims), then
/// verify the SINGLE stacked Ligerito against `commitment` on the shared
/// transcript. `stack_pd` are all of leanVM's point claims (bus / constraint /
/// public-input / binding / pinning) folded into the same opening.
pub fn verify_validity_stacked(
    n_blocks: usize,
    commitment: &Commitment,
    stack_offset: usize,
    stack_pd: &[(Vec<F128>, F128)],
    proof: &Blake3StackProof,
    vs: &mut VerifierState,
) -> Result<(), VerifyError> {
    setup_for(n_blocks).verify_validity_stacked(commitment, stack_offset, stack_pd, proof, vs)
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
        // Pinned slots: cv = IV on real instances.
        let pin = pin_constants();
        assert_eq!(slot(0, PIN_SLOTS[0]), pin[0]);
        assert_eq!(slot(0, PIN_SLOTS[1]), pin[1]);
        assert_eq!(slot(0, PIN_SLOTS[2]), pin[2]);
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
        let pd_value = crate::multilinear::mle_eval(&stacked.q, &pd_point);
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
        let (z_packed, zc, lc, reduced) =
            prove_reduction(&blocks, &committed.commitment, &mut ps);
        let bundle = ps.into_proof();

        // The reduction regenerates exactly the committed `q_pkd` sub-block.
        assert_eq!(z_packed, q_pkd, "reduction witness must equal committed q_pkd");
        assert_eq!(&stacked.q[offset..offset + z_packed.len()], z_packed.as_slice());

        // Verifier: replay the reduction and recover the claims.
        let mut vs = VerifierState::new(b"reduce", &bundle, &[]);
        let root = crate::pcs::read_commitment(&mut vs).unwrap();
        let (ab, c) = verify_reduction(blocks.len(), &root, stacked.m, &zc, &lc, &mut vs)
            .expect("reduction verifies");

        // Prover and verifier agree on the claims left for the PCS.
        assert_eq!(reduced.ab.claim, ab, "ab claim mismatch");
        assert_eq!(reduced.c.claim, c, "c claim mismatch");

        // A mismatched transcript domain diverges the sponge, so the recovered
        // claims must NOT match the prover's (the reduction is transcript-bound).
        let mut vs_bad = VerifierState::new(b"different", &bundle, &[]);
        let root_b = crate::pcs::read_commitment(&mut vs_bad).unwrap();
        if let Ok((ab_b, c_b)) = verify_reduction(blocks.len(), &root_b, stacked.m, &zc, &lc, &mut vs_bad) {
            assert!(
                ab_b != ab || c_b != c,
                "a diverged sponge must not reproduce the prover's claims"
            );
        }
    }
}
