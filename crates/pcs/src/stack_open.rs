// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::whir::commit`]), and one WHIR run discharges
//!
//! - **point claims** ([`StackClaim`]): plain multilinear evaluations of
//!   aligned sub-slices of the stack (a `Point` claim's weight is
//!   `eq(low_point, .)` supported on `[offset, offset + 2^|low_point|)`; a
//!   `Strided` claim freezes the low `stride_log` in-block coords to `slot`'s
//!   bits, so its weight is nonzero only at `offset + slot + j * 2^stride_log`),
//! - **ring-switched claims** ([`RingSwitchOpen`]): bit-MLE evaluation claims
//!   on the packed sub-block `q_flock = stack[offset .. offset + 2^qflock_vars]`,
//!   reduced per claim by [`super::ring_switch::prove_prepare`] and the
//!   deferred finish path to an inner-product
//!   claim `<q_flock, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind`.
//!
//! All claims are gamma-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::whir::recursive_prover_with_basis`]. The verifier replays
//! the ring-switch reductions succinctly ([`super::ring_switch::verify_prepare`]
//! and [`super::ring_switch::verify_finish`], with no dense `rs_eq_ind`) and drives
//! [`super::whir::recursive_verifier_with_basis_succinct`] with a
//! terminal evaluator that reconstructs `MLE(b_stack)` once, at the final fold
//! point, using closed-form eq / stride selectors and
//! [`super::ring_switch::eval_rs_eq`].
//!
//! ## Transcript order (identical on both sides)
//!
//! label -> per ring-switched claim ([`super::ring_switch`]'s own label +
//! `s_hat_v_i` observed + shared linear map sampled) -> per point claim (label +
//! value observed) -> gamma (ONE challenge for both families) -> WHIR, with
//! domain-separated labels for every phase.
//!
//! ## The combined weight
//!
//! With `sel = offset >> qflock_vars` the selector coords of the q_flock slice,
//! the lifted weight at a full-stack point `x = (x_lo, x_hi)` (split at
//! `qflock_vars`, LSB-first) is
//!
//! ```text
//! b(x) = eq(sel, x_hi) * sum_i gamma^i * MLE(rs_eq_ind_i)(x_lo)
//!      + sum_j gamma^(n_rs + j) * eq(claim_j, x)
//! ```
//!
//! which is exactly what the dense `b_stack` scatter produces (each claim's
//! weight lives on its aligned slice, so scattering the low-dimensional eq /
//! rs_eq_ind tensor at the slice offset IS multiplying by the boolean
//! selector eq).
//!
//! Both families take DISJOINT power ranges of ONE challenge, as the table
//! sumcheck's eta ranges do, so every claim carries a distinct power (the
//! batching step of `thm:rbr`).

use crate::merkle::Hash;
use fiat_shamir::transcript::{Receiver, Transmitter};
use primitives::field::{F64, F192, powers};
use primitives::multilinear::eq_eval;

use super::pack::PACKING_WIDTH;
use super::ring_switch;
use super::whir::{ProverConfig, VerifierConfig};
use super::whir::{ProverData, recursive_prover_with_basis, recursive_verifier_with_basis_succinct};

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// An owning point claim folded into the stacked mixed opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaim {
    /// `eq(low_point, .)` on the aligned slice
    /// `[offset, offset + 2^|low_point|)`; `offset` must be a multiple of
    /// `2^|low_point|`.
    Point {
        offset: usize,
        low_point: Vec<F192>,
        value: F192,
    },
    /// A boolean-selector claim on a packed column: the low `stride_log`
    /// in-block coords are frozen to `slot`'s bits (so the weight is nonzero
    /// only at `offset + slot + j * 2^stride_log`) and `point` is the high
    /// part. Equivalent to a `Point` with `low_point = slot_bits ++ point`,
    /// folded in `O(2^|point|)` instead of `O(2^(stride_log + |point|))`.
    /// `offset` must be a multiple of `2^(stride_log + |point|)` and
    /// `slot < 2^stride_log`.
    Strided {
        offset: usize,
        slot: usize,
        stride_log: usize,
        point: Vec<F192>,
        value: F192,
    },
}

impl StackClaim {
    #[inline]
    pub fn value(&self) -> F192 {
        match self {
            StackClaim::Point { value, .. } | StackClaim::Strided { value, .. } => *value,
        }
    }
}

/// The tie of a ring-switched claim to one combined value:
/// `value == sum_i prefix_weights[i] * s_hat_v[i]`, with [`PACKING_WIDTH`] = 64
/// weights (the eq tensor of the 6 prefix coords for a plain point claim, phi_8
/// Lagrange weights for a univariate-skip claim).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchTie {
    pub prefix_weights: Vec<F192>,
    pub value: F192,
}

/// One ring-switched claim on the q_flock sub-block, about the 64 bit-slice MLEs
/// of q_flock at `suffix_point` (see [`super::ring_switch`]), which has
/// `qflock_vars` coords.
///
/// Ring switching binds every slice; `tie` additionally pins them to a single
/// value the caller holds. It is `None` for flock's AB claim, whose slices are
/// lincheck's residual vector, bound by the terminal identity upstream. A
/// tie-less claim must be `prebound`: fresh slices with no tie would be
/// unconstrained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub tie: Option<RingSwitchTie>,
    pub suffix_point: Vec<F192>,
    /// Prover-side optional precomputed `s_hat_v` (the 64 bit-slice MLE
    /// values at `suffix_point`, e.g. captured inside flock's reduction).
    /// When present, [`super::ring_switch::prove_prepare`] skips its
    /// `fold_1b_rows` recomputation; the values are checked against the
    /// claim (`claim_check`) and the transcript is identical either way.
    /// Verifier-side bundles leave it `None`.
    pub s_hat_v: Option<Vec<F192>>,
}

/// Prover-side bundle of the ring-switched claims discharged in the same
/// stacked opening as the [`StackClaim`]s. Each claim may carry its
/// precomputed `s_hat_v`.
#[derive(Clone, Debug)]
pub struct RingSwitchOpen {
    /// q_flock's offset inside the committed stack; must be a multiple of
    /// `2^qflock_vars` (an aligned slice).
    pub offset: usize,
    /// log2 of q_flock's length in F64 words; the opener slices
    /// `q_flock = stack[offset .. offset + 2^qflock_vars]` (no separate copy).
    pub qflock_vars: usize,
    /// Number of leading claims whose `s_hat_v` was already absorbed earlier
    /// in this transcript. They are not absorbed a second time before the
    /// shared map challenges.
    pub prebound: usize,
    pub claims: Vec<RingSwitchClaim>,
}

/// Verifier counterpart of [`RingSwitchOpen`]: identical statement data
/// (the Merkle openings ride the transcript's phase list).
#[derive(Clone, Debug)]
pub struct RingSwitchVerify {
    /// q_flock's offset inside the committed stack.
    pub offset: usize,
    /// log2 of q_flock's length in F64 words.
    pub qflock_vars: usize,
    /// Leading ring-switch messages reconstructed from earlier stream data,
    /// where an upstream identity already bound them, so they are used without
    /// being re-sent and their claims carry no `tie`.
    pub reconstructed: Vec<Vec<F192>>,
    pub claims: Vec<RingSwitchClaim>,
}

// ---------------------------------------------------------------------------
// Shared claim folding / evaluation
// ---------------------------------------------------------------------------

/// The b_stack range a claim's weight is supported on. Every range is an
/// aligned dyadic interval (the offset asserts below), so two of them are
/// nested or disjoint and never partially overlap. `Strided` reports its whole
/// block rather than the strided positions inside it, which is conservative in
/// the direction that matters: it only ever makes a later claim accumulate.
fn claim_range(claim: &StackClaim) -> (usize, usize) {
    match claim {
        StackClaim::Point { offset, low_point, .. } => (*offset, *offset + (1usize << low_point.len())),
        StackClaim::Strided {
            offset,
            stride_log,
            point,
            ..
        } => (*offset, *offset + (1usize << (stride_log + point.len()))),
    }
}

/// Per-claim "this claim may WRITE its range instead of accumulating into it",
/// plus the ranges those writes cover. A `Point` claim qualifies when nothing
/// written earlier (the q_flock block, which `combine_deferred_into` fills, or
/// an earlier claim) lands anywhere in its range: claims are folded in list
/// order, so its slice is still untouched when its turn comes, and in char 2
/// writing where a zero would have been is bit-identical.
///
/// The returned ranges are pairwise disjoint, so the caller only has to zero
/// the gaps between them.
fn claim_write_plan(claims: &[StackClaim], qflock: (usize, usize)) -> (Vec<bool>, Vec<(usize, usize)>) {
    let mut touched = vec![qflock];
    let mut written = vec![qflock];
    let mut write_first = Vec::with_capacity(claims.len());
    for claim in claims {
        let range = claim_range(claim);
        let free = touched.iter().all(|&(s, e)| range.1 <= s || e <= range.0);
        let first = free && matches!(claim, StackClaim::Point { .. });
        if first {
            written.push(range);
        }
        touched.push(range);
        write_first.push(first);
    }
    (write_first, written)
}

/// Fold the gamma-weighted point claims into the stack weight `b_stack` and
/// running `target` (pure: the caller has already observed the claim values
/// and sampled `gammas` in transcript order). A `Point` builds eq over ONLY
/// its aligned slice, a `Strided` scatters the eq of its high coords at the
/// slot's stride. Every claim but the first one on a range scatters with `+=`,
/// so overlapping slices accumulate correctly; the OUTER loop therefore stays
/// serial (several bus claims can land on one column region), and parallelism
/// lives inside each claim: the gamma-seeded eq build (parallel above its level
/// floor) and the strided scatter. Small slices stay fully serial (with many
/// tiny point claims, pool dispatch would cost more than the fold itself). The
/// gamma seeding and the serial/parallel splits are exact-field/order-preserving,
/// so `b_stack`'s bytes (and hence the proof) are unchanged relative to the
/// build-then-multiply form.
///
/// `write_first` comes from [`claim_write_plan`]: where it is set, the claim's
/// slice is uninitialized and the eq table is written straight into it by
/// [`super::whir::build_eq_table_ext_seeded`]; elsewhere
/// [`super::whir::add_eq_table_ext_seeded`] accumulates, expanding its last
/// coordinate straight into `b_stack` so the table's largest level is never
/// staged in scratch.
fn fold_stacked_point_claims(
    b_stack: &mut [F192],
    target: &mut F192,
    claims: &[StackClaim],
    gammas: &[F192],
    write_first: &[bool],
) {
    // One reusable eq scratch: half the largest accumulating Point claim (the
    // seeded add expands the last coordinate straight into `b_stack`, and a
    // write-first Point needs no scratch at all), or the whole eq table of the
    // largest Strided claim. A fresh multi-MB allocation per claim would pay the
    // first-touch page faults anew.
    let scratch_len = claims
        .iter()
        .zip(write_first)
        .map(|(c, &first)| match c {
            StackClaim::Point { .. } if first => 0,
            StackClaim::Point { low_point, .. } => 1usize << low_point.len().saturating_sub(1),
            StackClaim::Strided { point, .. } => 1usize << point.len(),
        })
        .max()
        .unwrap_or(0);
    let mut scratch = zk_alloc::alloc_uninit(scratch_len);
    for ((claim, g), &first) in claims.iter().zip(gammas.iter()).zip(write_first) {
        let g = *g;
        match claim {
            StackClaim::Point {
                offset,
                low_point,
                value,
            } => {
                let len = 1usize << low_point.len();
                assert!(
                    offset % len == 0,
                    "StackClaim::Point: offset must be 2^|low_point|-aligned"
                );
                let dst = &mut b_stack[*offset..*offset + len];
                if first {
                    super::whir::build_eq_table_ext_seeded(low_point, g, dst);
                } else {
                    super::whir::add_eq_table_ext_seeded(low_point, g, &mut scratch, dst);
                }
                *target += g * *value;
            }
            StackClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                value,
            } => {
                // Sparse: eq over the instance `point` (2^|point| entries),
                // scattered at stride 2^stride_log from the slot's position.
                // Identical b_stack contribution to the dense Point with
                // low_point = slot_bits ++ point, at ~2^stride_log x less work.
                let stride = 1usize << stride_log;
                let block = 1usize << (stride_log + point.len());
                assert!(*slot < stride, "StackClaim::Strided: slot must fit the stride");
                assert!(
                    offset % block == 0,
                    "StackClaim::Strided: offset must be 2^(stride_log + |point|)-aligned"
                );
                let base = *offset + *slot;
                let len = 1usize << point.len();
                super::whir::build_eq_table_ext_seeded(point, g, &mut scratch[..len]);
                // SAFETY: the build above initialized exactly this prefix.
                let eq = unsafe { std::slice::from_raw_parts(scratch.as_ptr().cast::<F192>(), len) };
                for (j, &ej) in eq.iter().enumerate() {
                    b_stack[base + j * stride] += ej;
                }
                *target += g * *value;
            }
        }
    }
}

/// The claim's weight `eq(full claim point, x)` at an arbitrary point `x` of
/// the full stack cube. A `Point`'s full point is `[low_point, sel_bits]`, a
/// `Strided`'s is `[slot_bits, point, sel_bits]`; neither is materialized.
fn stack_claim_eq_at(claim: &StackClaim, x: &[F192]) -> F192 {
    match claim {
        StackClaim::Point { offset, low_point, .. } => {
            let n = low_point.len();
            let mut e = eq_eval(low_point, &x[..n]);
            let sel = offset >> n;
            for (k, &xi) in x[n..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
        StackClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            ..
        } => {
            let mut e = F192::ONE;
            for (k, &xi) in x[..*stride_log].iter().enumerate() {
                e *= if (slot >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            let block_vars = stride_log + point.len();
            e *= eq_eval(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` slice
/// evaluation AND the ring-switched q_flock claims (`ring`) in ONE WHIR
/// run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (the caller retains it; it is not stored
/// in [`ProverData`]); `config.initial_k` / `config.log_inv_rates[0]` must
/// match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the WHIR prover).
pub fn open_batch_mixed_whir_stacked(
    ps: &mut impl Transmitter,
    stack: &[F64],
    prover_data: &ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) {
    let qflock_len = 1usize << ring.qflock_vars;
    assert!(
        ring.offset.is_multiple_of(qflock_len),
        "q_flock offset must be 2^qflock_vars-aligned"
    );
    assert!(
        ring.offset + qflock_len <= stack.len(),
        "q_flock slice must fit inside the stack"
    );
    assert!(
        !ring.claims.is_empty(),
        "stacked PCS opening carries at least one ring-switched claim"
    );
    // Optional phase timing, answering to the same env var as the WHIR
    // prover/commit tracing (one env lookup per open, no work when unset).
    let trace = std::env::var_os("WHIR_TRACE").is_some();
    let mut t = std::time::Instant::now();
    let mark = |label: &str, t: &mut std::time::Instant| {
        if trace {
            eprintln!("[stack-open-k] {label}: {:7.2} ms", t.elapsed().as_secs_f64() * 1e3);
        }
        *t = std::time::Instant::now();
    };

    assert!(ring.prebound <= ring.claims.len());
    // 1. Ring-switch reduction: prepare every claim's s_hat_v, sending all but
    //    the leading pre-bound claims, then sample one shared linear map.
    let qflock = &stack[ring.offset..ring.offset + qflock_len];
    let mut rs_states = Vec::with_capacity(ring.claims.len());
    for (i, claim) in ring.claims.iter().enumerate() {
        assert_eq!(
            claim.suffix_point.len(),
            ring.qflock_vars,
            "ring-switch suffix point must have qflock_vars coords"
        );
        assert!(
            claim.tie.is_some() || i < ring.prebound,
            "a tie-less ring-switch claim must have its slices already bound"
        );
        let state = ring_switch::prove_prepare(
            qflock,
            claim.tie.as_ref().map(|t| (t.prefix_weights.as_slice(), t.value)),
            &claim.suffix_point,
            claim.s_hat_v.as_deref(),
            i < ring.prebound,
            ps,
        );
        rs_states.push(state);
    }
    let map_challenges = ring_switch::sample_map_challenges(ps);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);

    // 2. Point-claim values, then the ONE batching challenge both families take
    //    disjoint power ranges of.
    for claim in point_claims {
        ps.observe_scalar(claim.value());
    }
    let gammas = powers(ps.sample(), ring.claims.len() + point_claims.len());
    let (gammas_rs, gammas_pd) = gammas.split_at(ring.claims.len());

    let rs_outputs: Vec<_> = rs_states
        .into_iter()
        .zip(gammas_rs.iter().copied())
        .map(|(state, gamma)| ring_switch::prove_finish_deferred(state, &coordinate_weights, gamma))
        .collect();
    mark("ring-switch proves", &mut t);

    // 3. Combined target and lifted stack weight b_stack: the gamma-weighted
    //    rs_eq_ind sum scattered at the q_flock slice, plus the point-claim
    //    eq tensors scattered at their offsets.
    let mut target = rs_outputs
        .iter()
        .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim);
    // Parallel first-touch wins for the tower stack: its many scattered point
    // claims otherwise fault pages one claim at a time. A scatter that lands on
    // slots an earlier one already touched has to accumulate, so those slots
    // start at zero; a range whose first writer covers all of it does not, and
    // zeroing it would be stores thrown away. `combine_deferred_into` writes the
    // whole q_flock block, and `claim_write_plan` finds the point claims that
    // likewise write a whole untouched range.
    //
    // SAFETY: every slot is written before it is read: the fill covers every gap
    // between the written ranges, `combine_deferred_into` writes the q_flock
    // block, and each `write_first` claim writes its whole slice before any
    // later claim can accumulate into it.
    let (write_first, mut written) = claim_write_plan(point_claims, (ring.offset, ring.offset + qflock_len));
    let mut b_stack = unsafe { zk_alloc::ArenaVec::<F192>::uninitialized(stack.len()) };
    {
        const ZERO_CHUNK: usize = 1 << 16;
        written.sort_unstable();
        let mut cursor = 0usize;
        let zero = |part: &mut [F192]| parallel::chunks_mut(part, ZERO_CHUNK, |_, c| c.fill(F192::ZERO));
        for (start, end) in written {
            if start > cursor {
                zero(&mut b_stack[cursor..start]);
            }
            cursor = cursor.max(end);
        }
        zero(&mut b_stack[cursor..]);
        mark("b_stack zero fill", &mut t);
        let block = &mut b_stack[ring.offset..ring.offset + qflock_len];
        ring_switch::combine_deferred_into(&rs_outputs, block);
        mark("rs_eq_ind scatter", &mut t);
    }
    fold_stacked_point_claims(&mut b_stack, &mut target, point_claims, gammas_pd, &write_first);
    mark("point-claim folds", &mut t);

    // 4. One WHIR over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    recursive_prover_with_basis(
        config,
        stack,
        b_stack,
        target,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        ps,
    )
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verifier mirror of [`open_batch_mixed_whir_stacked`]: replay the
/// ring-switch reductions succinctly, recompute the combined target, then
/// drive the succinct WHIR verifier with one terminal evaluation of the
/// lifted weight. `log_n` is the committed stack's log size in F64 words and
/// `root` the L0 commitment root ([`super::whir::Commitment::root`]).
pub fn verify_opening_batch_mixed_whir_stacked(
    vs: &mut impl Receiver,
    config: &VerifierConfig,
    log_n: usize,
    root: &Hash,
    point_claims: &[StackClaim],
    ring: &RingSwitchVerify,
) -> bool {
    let n_rs = ring.claims.len();
    let qflock_vars = ring.qflock_vars;
    // Caller (statement) invariants: panic on misuse, like the extension-field layer.
    assert!(qflock_vars <= log_n);
    assert!(
        ring.offset.is_multiple_of(1usize << qflock_vars),
        "q_flock offset must be 2^qflock_vars-aligned"
    );
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    for claim in &ring.claims {
        if let Some(tie) = &claim.tie {
            assert_eq!(tie.prefix_weights.len(), PACKING_WIDTH);
        }
        assert_eq!(claim.suffix_point.len(), qflock_vars);
    }
    if ring.reconstructed.len() > n_rs || ring.reconstructed.iter().any(|s| s.len() != PACKING_WIDTH) {
        return false;
    }

    // 1. Ring-switch verify: each reconstructed leading vector was already bound
    //    upstream, so only the remaining ones are read off the stream, against
    //    the tie that pins them. Then sample one shared map.
    let mut rs_proofs = ring.reconstructed.clone();
    for claim in ring.claims.iter().skip(ring.reconstructed.len()) {
        let Some(tie) = &claim.tie else { return false };
        let Ok(s_hat_v) = ring_switch::verify_prepare(tie.value, &tie.prefix_weights, vs) else {
            return false;
        };
        rs_proofs.push(s_hat_v);
    }
    let map_challenges = ring_switch::sample_map_challenges(vs);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);

    // 2. Point-claim values, then the one batching challenge, then fold both
    //    families into the target over disjoint power ranges.
    for claim in point_claims {
        vs.observe_scalar(claim.value());
    }
    let gammas = powers(vs.sample(), n_rs + point_claims.len());
    let (gammas_rs, gammas_pd) = gammas.split_at(n_rs);

    let mut target = F192::ZERO;
    for (s_hat_v, g) in rs_proofs.iter().zip(gammas_rs.iter()) {
        target += *g * ring_switch::verify_finish(s_hat_v, &coordinate_weights);
    }
    for (claim, g) in point_claims.iter().zip(gammas_pd.iter()) {
        target += *g * claim.value();
    }

    // 3. Evaluate the lifted weight once, at the terminal sumcheck point.
    let sel = ring.offset >> qflock_vars;
    let eval_b_at = |x: &[F192]| -> F192 {
        let (x_lo, x_hi) = x.split_at(qflock_vars);
        let mut sel_eq = F192::ONE;
        for (k, &xi) in x_hi.iter().enumerate() {
            sel_eq *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
        }
        let mut rs_part = F192::ZERO;
        for (claim, g) in ring.claims.iter().zip(gammas_rs.iter()) {
            rs_part += *g * ring_switch::eval_rs_eq(&claim.suffix_point, x_lo, &coordinate_weights);
        }
        let mut acc = rs_part * sel_eq;
        for (claim, g) in point_claims.iter().zip(gammas_pd.iter()) {
            acc += *g * stack_claim_eq_at(claim, x);
        }
        acc
    };

    recursive_verifier_with_basis_succinct(config, log_n, target, root, eval_b_at, vs)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pack::{LOG_PACKING, pack_witness};
    use crate::ring_switch::{claim_check, fold_1b_rows};
    use crate::whir::{build_eq_table_ext, commit, default_config, inner_product_base_ext};
    use crate::whir_config::test_configs_for;
    use primitives::test_rng::Rng;

    const DOMAIN: &[u8] = b"stack-open-test";

    struct Instance {
        vc: VerifierConfig,
        log_n: usize,
        root: Hash,
        point_claims: Vec<StackClaim>,
        ring: RingSwitchOpen,
        fs: fiat_shamir::transcript::Proof,
    }

    /// Synthetic stack of 2^14 F64 words: three aligned 2^12-word columns
    /// plus a q_flock region (a random bit-witness packed by pack) at the
    /// top slice, padded with random filler. Pool: one point claim per
    /// column at a random E point, one strided claim into q_flock, one
    /// ring-switched claim with plain eq prefix weights.
    ///
    /// q_flock is kept SMALL (2^8 words) so the succinct verifier's residual
    /// cube sits entirely above the q_flock coords (the production regime:
    /// shared tensor prefix folded once, y coords all selector-indicator,
    /// nonempty E-valued selector prefix from ris); the crossing regime is
    /// exercised by `stacked_open_residual_crosses_qflock`.
    fn build_instance(seed: u64) -> Instance {
        let log_n = 14usize;
        let col_vars = 12usize;
        let col_len = 1usize << col_vars;
        let qflock_vars = 8usize;
        let qflock_offset = 3 * col_len;
        let mut rng = Rng::new(seed);

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(rng.next_u64())).collect();
        let bits = rng.bits(1usize << (qflock_vars + LOG_PACKING));
        stack.extend(pack_witness(&bits, qflock_vars + LOG_PACKING));
        while stack.len() < 1 << log_n {
            stack.push(F64(rng.next_u64()));
        }
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaim> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point = rng.ext_vec(col_vars);
                let eq = build_eq_table_ext(&low_point);
                let value = inner_product_base_ext(&stack[offset..offset + col_len], &eq);
                StackClaim::Point {
                    offset,
                    low_point,
                    value,
                }
            })
            .collect();

        // One strided claim into the q_flock region: freeze the low 3 in-block
        // coords to slot 5, eq over the remaining coords of the slice.
        {
            let stride_log = 3usize;
            let slot = 5usize;
            let point = rng.ext_vec(qflock_vars - stride_log);
            let eq = build_eq_table_ext(&point);
            let mut value = F192::ZERO;
            for (j, &ej) in eq.iter().enumerate() {
                value += ej.mul_base(stack[qflock_offset + slot + (j << stride_log)]);
            }
            point_claims.push(StackClaim::Strided {
                offset: qflock_offset,
                slot,
                stride_log,
                point,
                value,
            });
        }

        // One ring-switched claim on q_flock (plain eq prefix weights).
        let qflock = &stack[qflock_offset..qflock_offset + (1 << qflock_vars)];
        let r_prefix = rng.ext_vec(LOG_PACKING);
        let prefix_weights = build_eq_table_ext(&r_prefix);
        let suffix_point = rng.ext_vec(qflock_vars);
        let s_hat_v = fold_1b_rows(qflock, &build_eq_table_ext(&suffix_point));
        let value = claim_check(&prefix_weights, &s_hat_v);
        let ring = RingSwitchOpen {
            offset: qflock_offset,
            qflock_vars,
            prebound: 0,
            claims: vec![RingSwitchClaim {
                tie: Some(RingSwitchTie { prefix_weights, value }),
                suffix_point,
                // Exercise the fold path (no precompute).
                s_hat_v: None,
            }],
        };

        let (pc, vc) = test_configs_for(log_n);
        // Pin the intended residual regime: the residual cube must sit
        // entirely above the q_flock coords, with at least one selector coord
        // covered by ris (the E-valued sel prefix) and the rest by y bits.
        let yr_log_n = log_n - pc.initial_k - pc.level_ks.iter().sum::<usize>();
        assert!(
            qflock_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_flock (yr_log_n = {yr_log_n})"
        );
        let (cm, pd) = commit(&stack, pc.initial_k, pc.log_inv_rates[0]);
        let mut ps = fiat_shamir::transcript::ProverState::new(DOMAIN, &[]);
        open_batch_mixed_whir_stacked(&mut ps, &stack, &pd, &pc, &point_claims, &ring);

        Instance {
            vc,
            log_n,
            root: cm.root,
            point_claims,
            ring,
            fs: ps.into_proof(),
        }
    }

    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaim],
        ring_claims: &[RingSwitchClaim],
        fs: &fiat_shamir::transcript::Proof,
    ) -> bool {
        let ring = RingSwitchVerify {
            offset: inst.ring.offset,
            qflock_vars: inst.ring.qflock_vars,
            reconstructed: Vec::new(),
            claims: ring_claims.to_vec(),
        };
        let mut vs = fiat_shamir::transcript::VerifierState::new(DOMAIN, fs, &[]);
        verify_opening_batch_mixed_whir_stacked(&mut vs, &inst.vc, inst.log_n, &inst.root, point_claims, &ring)
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
        let inst = build_instance(1);
        assert!(
            verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &inst.fs),
            "honest stacked opening rejected"
        );

        // Wrong point-claim value (dense column claim).
        let mut bad_points = inst.point_claims.clone();
        if let StackClaim::Point { value, .. } = &mut bad_points[0] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring.claims, &inst.fs),
            "tampered Point value accepted"
        );

        // Wrong strided-claim value.
        let mut bad_points = inst.point_claims.clone();
        if let StackClaim::Strided { value, .. } = &mut bad_points[3] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring.claims, &inst.fs),
            "tampered Strided value accepted"
        );

        // Wrong ring-switched claim value: rejected by the claim check.
        let mut bad_ring = inst.ring.claims.clone();
        bad_ring[0].tie.as_mut().unwrap().value += F192::ONE;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.fs),
            "tampered ring-switch value accepted"
        );

        // Every scalar the opening sends rides the stream: the leading 64 are
        // the transmitted s_hat_v (caught by the claim check), the rest are
        // WHIR's. Tampering any of them must be rejected.
        for idx in [17usize, inst.fs.stream.len() - 1] {
            let mut bad_fs = inst.fs.clone();
            bad_fs.stream[idx] += F192::ONE;
            assert!(
                !verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &bad_fs),
                "tampered stream word {idx} accepted"
            );
        }

        // Shape tamper: a truncated stream must return false, not panic.
        let mut short_fs = inst.fs.clone();
        short_fs.stream.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &short_fs),
            "short stream accepted"
        );
    }

    #[test]
    fn stacked_open_proof_is_deterministic() {
        let a = build_instance(2);
        let b = build_instance(2);
        assert_eq!(a.fs, b.fs, "same inputs must yield identical proofs");
        let bytes_a = bincode::serialize(&a.fs).unwrap();
        let bytes_b = bincode::serialize(&b.fs).unwrap();
        assert_eq!(bytes_a, bytes_b, "proof bytes must be deterministic");
    }

    /// Residual cube crossing INTO the q_flock slice (case split = n_ris in the
    /// verifier closure): q_flock occupies half a 2^14 stack (qflock_vars = 13),
    /// and the fallback config's residual cube (yr_log_n = 3) is wider than
    /// the single selector coordinate, so some q_flock coords are covered by
    /// binary y bits and the tensor finish runs with a nonempty suffix.
    #[test]
    fn stacked_open_residual_crosses_qflock() {
        let log_n = 14usize;
        let qflock_vars = 13usize;
        let qflock_offset = 1usize << 13;
        let mut rng = Rng::new(3);

        let mut stack: Vec<F64> = (0..1usize << 13).map(|_| F64(rng.next_u64())).collect();
        let bits = rng.bits(1usize << (qflock_vars + LOG_PACKING));
        stack.extend(pack_witness(&bits, qflock_vars + LOG_PACKING));
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim on the low column.
        let low_point = rng.ext_vec(12);
        let eq = build_eq_table_ext(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaim::Point {
            offset: 0,
            low_point,
            value,
        }];

        // One ring-switched claim on the wide q_flock.
        let qflock = &stack[qflock_offset..];
        let r_prefix = rng.ext_vec(LOG_PACKING);
        let prefix_weights = build_eq_table_ext(&r_prefix);
        let suffix_point = rng.ext_vec(qflock_vars);
        let s_hat_v = fold_1b_rows(qflock, &build_eq_table_ext(&suffix_point));
        let rs_value = claim_check(&prefix_weights, &s_hat_v);
        let claims = vec![RingSwitchClaim {
            tie: Some(RingSwitchTie {
                prefix_weights,
                value: rs_value,
            }),
            suffix_point,
            // Exercise the precomputed path (transcript must be identical).
            s_hat_v: Some(s_hat_v.clone()),
        }];

        // Fixed fallback config so the residual cube size is known: the
        // crossing regime needs qflock_vars > log_n - yr_log_n.
        let pc = default_config(log_n, 5, 1).unwrap();
        let vc = pc.clone();
        let yr_log_n = log_n - pc.initial_k - pc.level_ks.iter().sum::<usize>();
        assert!(
            qflock_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let (cm, pd) = commit(&stack, pc.initial_k, pc.log_inv_rates[0]);
        let ring = RingSwitchOpen {
            offset: qflock_offset,
            qflock_vars,
            prebound: 0,
            claims,
        };
        let mut ps = fiat_shamir::transcript::ProverState::new(DOMAIN, &[]);
        open_batch_mixed_whir_stacked(&mut ps, &stack, &pd, &pc, &point_claims, &ring);
        let fs = ps.into_proof();

        let ring_v = RingSwitchVerify {
            offset: qflock_offset,
            qflock_vars,
            reconstructed: Vec::new(),
            claims: ring.claims.clone(),
        };
        let mut vs = fiat_shamir::transcript::VerifierState::new(DOMAIN, &fs, &[]);
        assert!(
            verify_opening_batch_mixed_whir_stacked(&mut vs, &vc, log_n, &cm.root, &point_claims, &ring_v),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip its value.
        let mut bad_ring = ring_v;
        bad_ring.claims[0].tie.as_mut().unwrap().value += F192::ONE;
        let mut vs = fiat_shamir::transcript::VerifierState::new(DOMAIN, &fs, &[]);
        assert!(
            !verify_opening_batch_mixed_whir_stacked(&mut vs, &vc, log_n, &cm.root, &point_claims, &bad_ring),
            "tampered crossing-regime ring value accepted"
        );
    }
}
