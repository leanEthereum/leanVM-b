//! Bridge to the vendored flock BLAKE3 prover (`flock_prover`), single-PCS.
//!
//! `q_pkd` (flock's packed BLAKE3 witness, 64 bits per `F64` word) is committed
//! as a column in leanVM-b's ONE stacked `K`-witness (§3.1) — no separate flock
//! commitment. The VM's `BLAKE3` table binds to it by point-eval equality (its
//! value columns and `q_pkd`'s slots are point-evals of the same committed
//! stack), and flock's R1CS validity is discharged by the same stacked Ligerito:
//! the reduction's two claims cross from flock's GHASH world into the tower via
//! [`ring_switch_open`] / [`ring_switch_verify`] and join the batch-mixed
//! opening ([`flare::pcs::stack_open_k`]).
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

use crate::field::{F64, F128T};
use crate::transcript::{ProverState, VerifierState};
use flare::field::{F128, ghash_to_tower};
use flare::pcs::pack_k::{LOG_PACKING_K, PACKING_WIDTH_K};
use flare::zerocheck::multilinear::lagrange_weights_naive;
use flock_prover::r1cs_hashes::blake3::{
    BLAKE3_IV, Blake3Setup, Compression, K_LOG, ReducedClaims, blake3_compress,
    generate_witness_with_ab_packed_and_lincheck, min_n_blocks_log,
};
use flock_prover::verifier::VerifyError;

/// A `ẑ(point) = value` claim on the committed witness `q_pkd`, recovered by the
/// Flock zerocheck + lincheck reduction ([`prove_reduction`] / [`verify_reduction`])
/// and later discharged by the PCS. Re-exported from `flock_prover` (GHASH-typed;
/// [`ring_switch_verify`] maps it into the tower).
pub use flock_prover::proof::ZClaim;

/// flock flags for a single 64-byte root block: `CHUNK_START(1) | CHUNK_END(2) |
/// ROOT(8) = 11` — the configuration under which the compression output equals
/// `blake3::hash` of the 64-byte input.
pub const FLAGS: u32 = (1 << 0) | (1 << 1) | (1 << 3);

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

/// Within-instance slots pinned to PUBLIC constants: `cv` (slots 0..4 = the IV,
/// two u32 words each), the counter word (slot 18: `counter_lo‖counter_hi = 0`),
/// and the packed `block_len‖flags` word (slot 19). Pinning them makes the
/// proven compression a real BLAKE3-of-64-bytes.
pub const PIN_SLOTS: [usize; 6] = [0, 1, 2, 3, 18, 19];

/// Split a 64-bit field element into the two little-endian `u32` words flock's
/// message uses — the VM memory byte order.
fn words_of(x: F64) -> [u32; 2] {
    [x.0 as u32, (x.0 >> 32) as u32]
}

/// Inverse of [`words_of`]: pack two little-endian `u32` words into the `F64`.
pub fn pack_words(w: [u32; 2]) -> F64 {
    F64((w[0] as u64) | ((w[1] as u64) << 32))
}

/// The flock [`Compression`] for one VM `BLAKE3(a, b)`: `cv = IV`, message
/// `m = a‖b`, counter `0`, block length `64`, flags [`FLAGS`].
pub fn compression(a: [F64; 4], b: [F64; 4]) -> Compression {
    let mut m = [0u32; 16];
    for (i, &w) in a.iter().enumerate() {
        m[2 * i..2 * i + 2].copy_from_slice(&words_of(w));
    }
    for (i, &w) in b.iter().enumerate() {
        m[8 + 2 * i..8 + 2 * i + 2].copy_from_slice(&words_of(w));
    }
    (BLAKE3_IV, m, 0, 64, FLAGS)
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

/// The all-zero compression `([0;8],[0;16],0,0,0)` — the padding instance flock's
/// witness generation fills unused slots with. Synthesized as the sole block when
/// a program executes no BLAKE3, so `q_pkd` and the reduction always have ≥ 1
/// instance.
pub fn padding_compression() -> Compression {
    ([0u32; 8], [0u32; 16], 0, 0, 0)
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
/// to `2^n_blocks_log(max(blocks.len(),1))` instances (the unused ones all-zero
/// padding). Deterministic, so it matches what the reduction regenerates. An empty
/// `blocks` yields one padding cube (all instances are padding).
pub fn build_qpkd(blocks: &[Compression]) -> Vec<F64> {
    flatten_packed(generate_witness_with_ab_packed_and_lincheck(blocks, n_blocks_log(blocks.len().max(1))).0)
}

/// The output `(c0..c3)` of flock's padding compression — the all-zero input
/// `([0;8],[0;16],0,0,0)` that fills padding instances (const-wire pin). Its
/// output is NONZERO, so the VM pads its BLAKE3 output value columns with this.
pub fn padding_digest() -> [F64; 4] {
    digest(&padding_compression())
}

/// The PUBLIC constants the [`PIN_SLOTS`] hold on a real instance, in PIN_SLOTS
/// order: the IV's four 64-bit words, the zero counter word, and
/// `block_len=64 ‖ flags=11`. Padding instances hold 0.
pub fn pin_constants() -> [F64; 6] {
    [
        pack_words([BLAKE3_IV[0], BLAKE3_IV[1]]),
        pack_words([BLAKE3_IV[2], BLAKE3_IV[3]]),
        pack_words([BLAKE3_IV[4], BLAKE3_IV[5]]),
        pack_words([BLAKE3_IV[6], BLAKE3_IV[7]]),
        pack_words([0, 0]),
        pack_words([64, FLAGS]),
    ]
}

/// `log2` of the within-instance packed span (`PACKED_PER_INSTANCE = 2^8`): the
/// number of low coords in a [`slot_point`] that carry the slot's bits, and the
/// stride between consecutive instances' same-slot words in `q_pkd`. A value
/// claim on `q_pkd` is thus a boolean-selector (strided) claim with this stride.
pub const SLOT_STRIDE_LOG: usize = K_LOG - LOG_PACKING_K;

/// The `q_pkd`-column MLE point selecting within-instance `slot` over the
/// instance cube `rho`: the low 8 coords are `slot`'s bits (LSB-first), the high
/// `n_log` coords are `rho`.
pub fn slot_point(slot: usize, rho: &[F128T]) -> Vec<F128T> {
    let mut p: Vec<F128T> = (0..SLOT_STRIDE_LOG)
        .map(|b| if (slot >> b) & 1 == 1 { F128T::ONE } else { F128T::ZERO })
        .collect();
    p.extend_from_slice(rho);
    p
}

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

/// Pre-build (and cache) the flock BLAKE3 R1CS setup, warming BOTH the circuit and
/// the statement-digest caches. This is the fixed, circuit-shape-only cost
/// (~hundreds of ms, independent of the witness or the number of proofs): building
/// the `2^K_LOG`-slot R1CS and hashing it.
///
/// Callers pass the number of EXECUTED `BLAKE3` instructions; it is floored at 1
/// (the padding instance a no-BLAKE3 program still carries), matching
/// `cpu::prove`/`verify`. Call it once up front so a subsequent prove/verify
/// reflects steady-state (repeated-proving) performance — the ~hundreds-of-ms
/// build is a one-time, program-independent cost, not part of proving. Idempotent.
pub fn warm_setup(n_blocks: usize) {
    let setup = setup_for(n_blocks.max(1));
    let _ = setup.r1cs.statement_digest(); // warm the digest cache too
}

/// **Flock reduction only** (prover): run flock's BLAKE3 zerocheck + lincheck
/// over `blocks`, binding to the stack commitment (`root`/`mu`, see
/// [`crate::pcs::commitment_from_root`]), and return the two claims
/// [`ReducedClaims`] on the committed witness `q_pkd` — `ab` (`A∘B`, lincheck)
/// and `c` (`C`, zerocheck) — along with the regenerated packed witness (already
/// flattened to the committed `F64` packing) and the transmitted zerocheck /
/// lincheck sub-proofs. Does NOT open the PCS: the caller packages the returned
/// claims for the stacked opening ([`ring_switch_open`]). flock runs entirely in
/// its GHASH world on the shared sponge `ps` (the [`flare::challenger::Challenger`]
/// impl); only the claims cross into the tower.
pub fn prove_reduction(
    blocks: &[Compression],
    root: &[u8; 32],
    mu: usize,
    ps: &mut ProverState,
) -> (
    Vec<F64>,
    flock_prover::zerocheck::ZerocheckProof,
    flock_prover::lincheck::LincheckProof,
    ReducedClaims,
) {
    let commitment = crate::pcs::commitment_from_root(*root, mu);
    let (z_packed, zc, lc, reduced) = setup_for(blocks.len()).prove_reduction(blocks, &commitment, ps);
    (flatten_packed(z_packed), zc, lc, reduced)
}

/// **Flock reduction only** (verifier): mirror of [`prove_reduction`]. Rebuild the
/// stack commitment from `root`/`mu`, replay the `zerocheck` + `lincheck`
/// sub-proofs (binding to it), and recover the two `(ab, c)` claims on `q_pkd`
/// for the PCS to discharge. In a full proof these sub-proofs ride the shared
/// channels ([`read_stack_proof`]).
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
    let prefix_weights: Vec<F128T> = lagrange_weights_naive(LOG_PACKING_K, z.point.z_skip)
        .into_iter()
        .map(ghash_to_tower)
        .collect();
    let mut suffix_point: Vec<F128T> = z.point.x_inner_rest.iter().copied().map(ghash_to_tower).collect();
    suffix_point.extend(z.point.x_outer.iter().copied().map(ghash_to_tower));
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
        let c = ghash_to_tower(z.point.x_inner_rest[0]);
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
        value: ghash_to_tower(z.value),
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
/// same statement data; the transmitted opening travels separately
/// ([`read_stack_proof`]).
pub fn ring_switch_verify(n_blocks: usize, offset: usize, ab: ZClaim, c: ZClaim) -> crate::pcs::RingSwitchVerify {
    let qpkd_vars = qpkd_kappa(n_blocks);
    crate::pcs::RingSwitchVerify {
        offset,
        qpkd_vars,
        claims: vec![ring_claim(&ab, None, qpkd_vars), ring_claim(&c, None, qpkd_vars)],
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
    open: crate::pcs::BatchOpeningProofK,
) {
    let crate::pcs::BatchOpeningProofK { ring_switches, ligerito } = open;
    let bytes = bincode::serialize(&(zerocheck, lincheck, ring_switches)).expect("flock BLAKE3 sub-proof serializes");
    ps.hint_bytes(&bytes);
    ps.hint_opening(ligerito);
}

/// Verifier side of [`write_stack_proof`]: read flock's scalar reduction back off
/// the `stream` (raw — not re-absorbed) and its Ligerito off the `openings`
/// channel, reassembling `(zerocheck, lincheck, open)` for [`verify_reduction`]
/// and [`crate::pcs::verify`].
#[allow(clippy::type_complexity)]
pub fn read_stack_proof(
    vs: &mut VerifierState,
) -> Result<
    (
        flock_prover::zerocheck::ZerocheckProof,
        flock_prover::lincheck::LincheckProof,
        crate::pcs::BatchOpeningProofK,
    ),
    crate::transcript::Error,
> {
    let bytes = vs.next_hint_bytes()?;
    let (zerocheck, lincheck, ring_switches): (
        flock_prover::zerocheck::ZerocheckProof,
        flock_prover::lincheck::LincheckProof,
        Vec<flare::pcs::ring_switch_k::RingSwitchProofK>,
    ) = bincode::deserialize(&bytes).map_err(|_| crate::transcript::Error::MissingHint)?;
    let ligerito = vs.next_opening()?.clone();
    Ok((zerocheck, lincheck, crate::pcs::BatchOpeningProofK { ring_switches, ligerito }))
}

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
        // Pinned slots on a real instance: the IV words, the zero counter, and
        // blen‖flags, exactly `pin_constants`.
        let pin = pin_constants();
        for (k, &ps) in PIN_SLOTS.iter().enumerate() {
            assert_eq!(slot(0, ps), pin[k]);
        }
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
        let (z_packed, zc, lc, reduced) =
            prove_reduction(&blocks, &committed.commitment.root, committed.mu, &mut ps);
        let bundle = ps.into_proof();

        // The reduction regenerates exactly the committed `q_pkd` sub-block.
        assert_eq!(z_packed, q_pkd, "reduction witness must equal committed q_pkd");
        assert_eq!(&stacked.q[offset..offset + z_packed.len()], z_packed.as_slice());

        // Verifier: replay the reduction and recover the claims.
        let mut vs = VerifierState::new(b"reduce", &bundle, &[]);
        let root = crate::pcs::read_commitment(&mut vs).unwrap();
        let (ab, c) =
            verify_reduction(blocks.len(), &root, stacked.m, &zc, &lc, &mut vs).expect("reduction verifies");

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
        let pd_value = crate::multilinear::mle_eval(&dummy, &low_point);
        let points = vec![crate::pcs::SlotClaim::Point {
            offset: dummy_pl.offset,
            low_point: low_point.clone(),
            value: pd_value,
        }];

        let mut ps = ProverState::new(b"vstack", &[]);
        let committed = crate::pcs::commit(&mut ps, &stacked.q);
        let (_z, zc, lc, reduced) = prove_reduction(&blocks, &committed.commitment.root, committed.mu, &mut ps);
        let ring = ring_switch_open(blocks.len(), offset, &reduced);
        let open = crate::pcs::open(&mut ps, &committed, &stacked.q, &points, &ring);
        write_stack_proof(&mut ps, zc, lc, open);
        let bundle = ps.into_proof();

        let run = |label: &'static [u8], points: &[crate::pcs::SlotClaim]| -> Result<(), &'static str> {
            let mut vs = VerifierState::new(label, &bundle, &[]);
            let root = crate::pcs::read_commitment(&mut vs).map_err(|_| "root")?;
            let (zc, lc, open) = read_stack_proof(&mut vs).map_err(|_| "stack proof")?;
            let (ab, c) = verify_reduction(blocks.len(), &root, stacked.m, &zc, &lc, &mut vs)
                .map_err(|_| "reduction")?;
            let ring = ring_switch_verify(blocks.len(), offset, ab, c);
            crate::pcs::verify(&mut vs, points, &ring, &open, stacked.m, &root).map_err(|_| "opening")?;
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
