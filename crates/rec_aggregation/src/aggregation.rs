//! Recursive XMSS aggregation: one bytecode (`guests/aggregate.py`) for every
//! node of an aggregation tree.
//!
//! A node verifies `n_raw` XMSS signatures and `n_children` sub-proofs **of this
//! same bytecode**, all against one shared `(message, epoch)`, and publishes the
//! sorted deduplicated union of their signer sets. Coverage is what carries the
//! security claim: a write-once slot per declared signer, written once by each
//! raw signature and each child key, plus a final count, so every declared
//! signer is backed by a real signature or a verified child.
//!
//! The bytecode is compiled to a fixed point on its own size
//! ([`unified_guest`]): the recursion placeholders depend on the inner bytecode
//! size, and here the inner bytecode is this one. Its digest does not need a
//! fixed point, riding the statement instead of the code.
//!
//! Three fixed polynomials (the stacked bytecode and flock's `A0`/`B0`) are too
//! big to evaluate in-circuit, so each node exports one deferred claim on each
//! and batches its children's carried claims with the fresh ones its
//! verifications raise (`doc/leanvm/main.tex` §Deferred evaluation claims). Only
//! the root's are discharged natively, by [`AggregateSignature::verify`].
//!
//! The transcript trace of a real `cpu::verify` run
//! (`transcript::trace_start`/`trace_take`) keeps the native and guest verifiers
//! synchronized: `gen_verify` walks it structurally, while `cpu::layout`
//! supplies every compile-time shape.

use std::collections::BTreeMap;
use std::ops::Range;

use lean_compiler::{compile, parse_with_replacements};
use lean_vm::cpu::{Program, prove, verify};
use lean_vm::leaf::{Block, Coord};
use lean_vm::transcript::{Sponge, TraceOp, trace_start, trace_take};
use primitives::field::{F64, F192, G, g_pow};
use primitives::multilinear::mle_eval;
use xmss::{XmssPublicKey, XmssSignature};

/// Why the guest reads every `q_flock` slot claim's instance point off `rho`: a
/// virtual value column is referenced only by its own table's bus blocks, which
/// the table sumcheck settles, so no framework block can raise one at `zeta`.
const VALCOL_FRAMEWORK: &str = "a framework block must not reference a virtual value column";
const RECURSION_AGG_LABEL: &[u8] = b"leanvm-b/recursion-aggregation/v1";
const RECURSION_STATEMENT_LABEL: &[u8] = b"leanvm-b/recursive-statement/v1";
const EPOCH_LABEL: &[u8] = b"leanvm-b/aggregation-epoch/v1";
const PUBKEYS_LABEL: &[u8] = b"leanvm-b/aggregation-pubkeys/v1";

/// The recursion arity, and the cap on `n_keys + n_dup` (exclusive: the guest
/// proves `log(n_total) < MAX_KEYS`).
///
/// `MAX_KEYS` is what the coverage indices' runtime range check needs to stay
/// below `2^MIN_LOG_MEM`, so that the bound means the same thing at every
/// announced memory size. The guest discharges that by range-checking
/// `n_total` against this constant with a COMPILE-TIME bound, so raising
/// `MAX_KEYS` past `2^MIN_LOG_MEM` fails the build rather than quietly
/// weakening the index bound. leanVM caps its signer sets at the same place.
pub const MAX_CHILDREN: usize = 16;
pub const MAX_KEYS: usize = 1 << 16;

// The guest bakes a bytecode claim's width from `N_TUPLE_BITS` while `bytecode_vars`
// reads it off the stacked table, which is `N_BYTECODE_SELECTORS` wide. Two constants
// that happen to agree: were they to drift, a leaf's claim point would be one length in
// the guest and another in the statement, and nothing else would notice.
const _: () = assert!(lean_vm::leaf::N_TUPLE_BITS == lean_vm::leaf::N_BYTECODE_SELECTORS);
// The epoch digest absorbs the tweak table and the Merkle bits two cells per
// compression, the guest as `N_TWEAKS / 2` then `LOG_LIFETIME / 2` blocks and this file
// as one `chunks_exact(2)` over their concatenation. Odd counts would silently drop a
// cell here and misalign the blocks there.
const _: () = assert!((2 + xmss::V * (xmss::CHAIN_LENGTH - 1) + xmss::LOG_LIFETIME).is_multiple_of(2));
const _: () = assert!(xmss::LOG_LIFETIME.is_multiple_of(2));

/// A count as the guest carries it: in the exponent, `g^n`.
fn count(n: usize) -> F192 {
    F192::new(g_pow(n).0, 0, 0)
}

/// A field element as the decimal `u128` literal the zkDSL parser accepts.
fn u(f: F192) -> u128 {
    assert_eq!(f.c2, 0, "u128 DSL literal cannot encode the top F192 limb");
    (f.c0 as u128) | ((f.c1 as u128) << 64)
}

fn f192_literal(f: F192) -> String {
    format!("f192({},{},{})", f.c0, f.c1, f.c2)
}

/// Pack the sponge's four K lanes as two canonical 128-bit VM cells.
fn pack_state(s: [F64; 4]) -> [F192; 2] {
    [F192::new(s[0].0, s[1].0, 0), F192::new(s[2].0, s[3].0, 0)]
}

/// Pack a 32-byte Merkle node as the same canonical 128+128 cell pair used by
/// the VM's sole BLAKE2s representation.
fn pack_hash_state(hash: &[u8; 32]) -> [F192; 2] {
    let w = |o: usize| u64::from_le_bytes(hash[o..o + 8].try_into().unwrap());
    [F192::new(w(0), w(8), 0), F192::new(w(16), w(24), 0)]
}

/// Native mirror of the guest's default `blake2s(state, block, out)` over two
/// 128-bit cells each: the four `F64` lanes of a two-cell buffer are
/// `[w0.c0, w0.c1, w1.c0, w1.c1]`, and the output packs back the same way.
fn compress2(state: [F192; 2], block: [F192; 2]) -> [F192; 2] {
    let lanes = |c: [F192; 2]| [F64(c[0].c0), F64(c[0].c1), F64(c[1].c0), F64(c[1].c1)];
    let out = lean_vm::vmhash::compress(lanes(state), lanes(block));
    [F192::new(out[0].0, out[1].0, 0), F192::new(out[2].0, out[3].0, 0)]
}

/// A domain-separated two-cell IV, so the guest's two plain BLAKE2s chains
/// cannot be confused with each other or with a sponge state.
fn chain_iv(label: &[u8]) -> [F192; 2] {
    pack_state(Sponge::new(label, &[]).state())
}

/// A 16-byte native value as one canonical 128-bit cell.
fn val16(b: &[u8]) -> F192 {
    let w = |o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
    F192::new(w(0), w(8), 0)
}

/// A public key as the two cells the guest hashes and `verify_sig` reads:
/// the Merkle root then the public parameter.
fn key_cells(pk: &XmssPublicKey) -> [F192; 2] {
    [val16(&pk.merkle_root), val16(&pk.public_param)]
}

/// The 328-entry tweak table at `epoch`, in the order `verify_sig` indexes it:
/// encoding, then `V` chains of `CHAIN_LENGTH - 1` steps, then the WOTS-PK
/// tweak, then one per Merkle level. The Merkle parent index is `epoch >>
/// (level+1)` in `u64` (a `u32` shift by 32 at the top level would mask, not
/// zero).
fn tweak_table(epoch: u32) -> Vec<xmss::Tweak> {
    use xmss::*;
    let mut tweaks = vec![make_tweak(TWEAK_TYPE_ENCODING, 0, epoch)];
    for i in 0..V {
        for s in 0..CHAIN_LENGTH - 1 {
            tweaks.push(make_tweak(TWEAK_TYPE_CHAIN, (i * CHAIN_LENGTH + s) as u32, epoch));
        }
    }
    tweaks.push(make_tweak(TWEAK_TYPE_WOTS_PK, 0, epoch));
    for l in 0..LOG_LIFETIME {
        let parent_index = ((epoch as u64) >> (l + 1)) as u32;
        tweaks.push(make_tweak(TWEAK_TYPE_MERKLE, (l + 1) as u32, parent_index));
    }
    tweaks
}

/// The Merkle direction bits at `epoch`, one 1-cell word per level.
fn merkle_bit_cells(epoch: u32) -> Vec<F192> {
    (0..xmss::LOG_LIFETIME)
        .map(|l| F192::new(((epoch >> l) & 1) as u64, 0, 0))
        .collect()
}

/// The epoch's whole contribution to the statement: the tweak table and the
/// Merkle bits, chained through BLAKE2s exactly as the guest absorbs them, two
/// cells per compression. Nothing derives a tweak in-circuit; the guest hints
/// both tables and checks this digest.
fn epoch_hash(epoch: u32) -> [F192; 2] {
    let mut cells: Vec<F192> = tweak_table(epoch).iter().map(|t| val16(t)).collect();
    cells.extend(merkle_bit_cells(epoch));
    let mut state = chain_iv(EPOCH_LABEL);
    for block in cells.chunks_exact(2) {
        state = compress2(state, [block[0], block[1]]);
    }
    state
}

/// The signer-set digest: one compression per key, in list order.
fn pubkeys_hash(keys: &[XmssPublicKey]) -> [F192; 2] {
    let mut state = chain_iv(PUBKEYS_LABEL);
    for pk in keys {
        state = compress2(state, key_cells(pk));
    }
    state
}

/// The claims on the three fixed polynomials that a node defers rather than
/// evaluating in-circuit: one point and value on the stacked bytecode, one point
/// and two values on flock's `A0`/`B0` (`doc/leanvm/main.tex` §Deferred
/// evaluation claims).
///
/// Only the points are transmitted; the values are derived from them on receipt,
/// so a prover that lies about a value changes the statement its proof has to
/// satisfy rather than the claim anyone checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeferredClaim {
    bytecode_point: Vec<F192>,
    bytecode_value: F192,
    matrix_point: Vec<F192>,
    matrix_a_value: F192,
    matrix_b_value: F192,
}

impl DeferredClaim {
    /// What a leaf defers: the all-zeros point on each polynomial, where the
    /// value is just the table's first entry.
    fn leaf() -> Self {
        Self::recompute(
            vec![F192::ZERO; bytecode_vars()],
            vec![F192::ZERO; 2 * flock::blake2s::K_LOG],
        )
        .expect("the all-zeros point has the right shape")
    }

    /// Evaluate the three fixed polynomials at `bytecode_point` / `matrix_point`.
    fn recompute(bytecode_point: Vec<F192>, matrix_point: Vec<F192>) -> Result<Self, VerifyError> {
        let klog = flock::blake2s::K_LOG;
        if bytecode_point.len() != bytecode_vars() || matrix_point.len() != 2 * klog {
            return Err(VerifyError::MalformedClaim);
        }
        // Every leaf defers the all-zeros point, where each polynomial is just
        // its table's first entry. Worth special-casing: the general path is two
        // full passes, one over 2^23 bytecode entries and one over 89M matrix
        // nonzeros, and a leaf is the aggregate people verify most.
        if bytecode_point.iter().chain(&matrix_point).all(|x| *x == F192::ZERO) {
            let (ma, mb) = flock::blake2s::matrices();
            let first = |m: &flock::r1cs::SparseBinaryMatrix| {
                if m.rows[0].contains(&0) { F192::ONE } else { F192::ZERO }
            };
            return Ok(Self {
                bytecode_point,
                bytecode_value: F192::from(stacked_bytecode()[0]),
                matrix_point,
                matrix_a_value: first(ma),
                matrix_b_value: first(mb),
            });
        }
        let bytecode_value = mle_eval(stacked_bytecode(), &bytecode_point);
        let eq_r = pcs::whir::build_eq_table_ext(&matrix_point[..klog]);
        let eq_c = pcs::whir::build_eq_table_ext(&matrix_point[klog..]);
        let (matrix_a_value, matrix_b_value) = flock::blake2s::bilinear_walk_pair(&eq_r, &eq_c);
        Ok(Self {
            bytecode_point,
            bytecode_value,
            matrix_point,
            matrix_a_value,
            matrix_b_value,
        })
    }

    /// The cells the statement digest absorbs, in the guest's `defer_stmt` order.
    fn cells(&self) -> Vec<F192> {
        let mut cells = self.bytecode_point.clone();
        cells.push(self.bytecode_value);
        cells.extend_from_slice(&self.matrix_point);
        cells.push(self.matrix_a_value);
        cells.push(self.matrix_b_value);
        cells
    }
}

/// A node's public statement, hashed to the two words the VM publishes. The
/// guest's `statement_digest` computes exactly this, both for itself and when it
/// rebuilds a child's, which is what forces a whole tree onto one bytecode,
/// one message and one epoch.
fn statement_digest(
    n_keys: usize,
    pubkeys_hash: [F192; 2],
    message: &xmss::Message,
    epoch_hash: [F192; 2],
    defer: &DeferredClaim,
) -> [F192; 2] {
    let fs_seed = lean_vm::cpu::fs_seed(unified_guest());
    let mut sponge = Sponge::new(RECURSION_STATEMENT_LABEL, &[]);
    sponge.observe(fs_seed[0]);
    sponge.observe(fs_seed[1]);
    sponge.observe(count(n_keys));
    sponge.observe(pubkeys_hash[0]);
    sponge.observe(pubkeys_hash[1]);
    sponge.observe(val16(&message[..16]));
    sponge.observe(val16(&message[16..]));
    sponge.observe(epoch_hash[0]);
    sponge.observe(epoch_hash[1]);
    for c in defer.cells() {
        sponge.observe(c);
    }
    pack_state(sponge.state())
}

/// The deferred-claim data the guest binds to the outer public input: the outer
/// verifier checks each claim natively (`doc/leanvm/main.tex` §Deferred evaluation claims;
/// n_rec = 1 forwards fresh claims without batching).
struct DeferredSubproof {
    public_input: [F192; 2],
    bytecode_row_point: Vec<F192>,
    bytecode_selector_point: Vec<F192>,
    bytecode_value: F192,
    matrix_a_coefficient: F192,
    skip_point: F192,
    zerocheck_row_point: Vec<F192>,
    lincheck_round_point: Vec<F192>,
    lincheck_terminal_values: Vec<F192>,
    matrix_claim: F192,
}

/// An aggregate signature: a proof that every key in `public_keys` signed
/// `message` at `epoch`.
///
/// The signer set is strictly sorted and deduplicated, and it is the union of
/// everything the aggregate covers, whether by a raw signature or through a
/// child aggregate. [`Self::verify`] is the only acceptance path.
#[derive(Clone, Debug)]
pub struct AggregateSignature {
    pub message: xmss::Message,
    pub epoch: u32,
    /// Strictly sorted, deduplicated, non-empty, at most [`MAX_KEYS`] long.
    pub public_keys: Vec<XmssPublicKey>,
    /// What this aggregate defers to whoever discharges it: its parent, in
    /// circuit, or [`Self::verify`], natively.
    defer: DeferredClaim,
    proof: lean_vm::cpu::Proof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The signer set is empty, unsorted, holds a duplicate, or is too long.
    MalformedSignerSet,
    /// A deferred claim's point has the wrong number of coordinates.
    MalformedClaim,
    /// The aggregate is for a different message or epoch than the caller expected.
    UnexpectedStatement,
    Proof(lean_vm::cpu::Error),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateError {
    /// A child disagrees with the node on the message or the epoch.
    InconsistentChildren,
    /// A child aggregate does not verify.
    InvalidChild(VerifyError),
    /// Nothing to aggregate: no raw signatures and no children.
    Empty,
    /// More than [`MAX_CHILDREN`] children, or more than [`MAX_KEYS`] signers
    /// once the duplicate slots are counted.
    TooLarge,
    /// A child's committed witness falls outside the opening arms the guest was
    /// compiled with. Small aggregates are padded up to the floor, so this means
    /// a child too big: more signatures than one node can hold.
    ChildOutOfRange { log_committed: usize },
}

/// Everything but the signer set, which a receiver may already hold.
type WireCore = (xmss::Message, u32, Vec<F192>, Vec<F192>, lean_vm::cpu::Proof);

/// Reject a signer set that the coverage argument does not cover: strict sorting
/// is what makes "every declared key signed" mean `public_keys.len()` distinct
/// signers rather than one signer counted many times.
fn check_signer_set(keys: &[XmssPublicKey]) -> Result<(), VerifyError> {
    if keys.is_empty() || keys.len() >= MAX_KEYS || !keys.windows(2).all(|w| w[0] < w[1]) {
        return Err(VerifyError::MalformedSignerSet);
    }
    Ok(())
}

impl AggregateSignature {
    /// This aggregate's own public statement, as the VM publishes it.
    fn public_input(&self) -> [F192; 2] {
        statement_digest(
            self.public_keys.len(),
            pubkeys_hash(&self.public_keys),
            &self.message,
            epoch_hash(self.epoch),
            &self.defer,
        )
    }

    /// The wire format: the shared statement, the signer set, the two deferred
    /// points, and the VM proof. The claim *values* are not transmitted;
    /// [`Self::from_bytes`] recomputes them, so there is nothing to lie about.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(&(&self.public_keys, self.core())).expect("an aggregate serializes")
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let (public_keys, core): (Vec<XmssPublicKey>, WireCore) = bincode::deserialize(bytes).ok()?;
        Self::from_parts(public_keys, core)
    }

    /// Without the signer set, for a receiver that already knows it. A set other
    /// than the one aggregated fails verification.
    pub fn to_bytes_without_pubkeys(&self) -> Vec<u8> {
        bincode::serialize(&self.core()).expect("an aggregate serializes")
    }

    pub fn from_bytes_without_pubkeys(bytes: &[u8], public_keys: Vec<XmssPublicKey>) -> Option<Self> {
        Self::from_parts(public_keys, bincode::deserialize(bytes).ok()?)
    }

    fn core(&self) -> WireCore {
        (
            self.message,
            self.epoch,
            self.defer.bytecode_point.clone(),
            self.defer.matrix_point.clone(),
            self.proof.clone(),
        )
    }

    fn from_parts(public_keys: Vec<XmssPublicKey>, core: WireCore) -> Option<Self> {
        let (message, epoch, bytecode_point, matrix_point, proof) = core;
        Some(Self {
            message,
            epoch,
            public_keys,
            defer: DeferredClaim::recompute(bytecode_point, matrix_point).ok()?,
            proof,
        })
    }

    /// Verify the aggregate against the message and epoch the caller expects.
    ///
    /// Prefer this to [`Self::verify`]. The prover supplies `message` and
    /// `epoch` along with everything else, so a bare `verify` establishes only
    /// that these signers signed *this object's* statement: an aggregate over
    /// the same keys from a different epoch, or over a different message,
    /// verifies just as well. Anything that reads `public_keys` as attestation
    /// of a particular statement has to pin that statement here.
    pub fn verify_against(&self, message: &xmss::Message, epoch: u32) -> Result<(), VerifyError> {
        if &self.message != message || self.epoch != epoch {
            return Err(VerifyError::UnexpectedStatement);
        }
        self.verify()
    }

    /// Verify the aggregate's internal consistency: the signer set is well
    /// formed, the three deferred fixed-polynomial claims hold at their
    /// transmitted points, and the VM proof satisfies the statement built from
    /// all of it.
    ///
    /// This says "every key in `public_keys` signed `self.message` at
    /// `self.epoch`", with `self.message` and `self.epoch` chosen by whoever
    /// produced the aggregate. Use [`Self::verify_against`] unless the caller
    /// has already pinned those two some other way.
    pub fn verify(&self) -> Result<(), VerifyError> {
        check_signer_set(&self.public_keys)?;
        // Recomputing the values is what binds them: a claim carrying anything
        // else yields a different statement, which the proof cannot satisfy.
        let defer = DeferredClaim::recompute(self.defer.bytecode_point.clone(), self.defer.matrix_point.clone())?;
        if defer != self.defer {
            return Err(VerifyError::MalformedClaim);
        }
        verify(unified_guest(), &self.public_input(), &self.proof).map_err(VerifyError::Proof)?;
        Ok(())
    }
}

/// The stacked bytecode polynomial of the aggregation guest: the one fixed
/// table every node's bytecode claims are about. Cached, because verification
/// evaluates it and building it walks the whole program.
fn stacked_bytecode() -> &'static [F64] {
    static TABLE: std::sync::OnceLock<Vec<F64>> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| lean_vm::cpu::layout::bytecode_table(&unified_guest().prog))
}

/// The slots of the stacked bytecode that are not structurally zero.
///
/// Nine encoding columns sit inside sixteen stacking slots, so nearly half the
/// table is zero and contributes nothing to any round of the batching sumcheck.
/// Read off the table rather than from the column count, so an all-zero column
/// at the edge only ever shrinks the window.
fn bytecode_window() -> Range<usize> {
    static WINDOW: std::sync::OnceLock<Range<usize>> = std::sync::OnceLock::new();
    WINDOW
        .get_or_init(|| {
            let table = stacked_bytecode();
            let kbc = bytecode_vars() - lean_vm::leaf::N_BYTECODE_SELECTORS;
            let live = |s: usize| table[s << kbc..(s + 1) << kbc].iter().any(|v| *v != F64::ZERO);
            let slots = 1 << lean_vm::leaf::N_BYTECODE_SELECTORS;
            let start = (0..slots).find(|&s| live(s)).expect("the bytecode is not all zero");
            let end = (0..slots).rfind(|&s| live(s)).expect("the bytecode is not all zero") + 1;
            start..end
        })
        .clone()
}

/// One round message against a K-valued table: `bt` is the bytecode itself, so
/// the products are base-by-extension.
fn round_msg_base(bt: &[F64], wt: &[F192]) -> (F192, F192) {
    let half = bt.len() / 2;
    let term = |i: usize| {
        let (u0, u1) = (bt[2 * i], bt[2 * i + 1]);
        let (m0, m1) = (wt[2 * i], wt[2 * i + 1]);
        (m1.mul_base(u1), (m0 + m1).mul_base(u0 + u1))
    };
    if half >= PAR_MIN {
        parallel::fold_reduce(
            half,
            || (F192::ZERO, F192::ZERO),
            |acc: &mut (F192, F192), i| {
                let (x, y) = term(i);
                acc.0 += x;
                acc.1 += y;
            },
            |a: (F192, F192), b: (F192, F192)| (a.0 + b.0, a.1 + b.1),
        )
    } else {
        (0..half).fold((F192::ZERO, F192::ZERO), |acc, i| {
            let (x, y) = term(i);
            (acc.0 + x, acc.1 + y)
        })
    }
}

/// The first fold of a K-valued table, which is where it becomes extension-valued.
fn fold_lsb_base(bt: &[F64], r: F192) -> Vec<F192> {
    parallel::map_collect(bt.len() / 2, |i| {
        let (a, b) = (bt[2 * i], bt[2 * i + 1]);
        F192::from(a) + r.mul_base(a + b)
    })
}

/// `Σ_t γ_t · eq(points[t], (r_row, ·))` over the stacking slots, once the row
/// variables are bound. A closed form, so the row rounds never have to carry the
/// slot half of a `2^kbcv` weight table.
fn slot_weights(points: &[Vec<F192>], gammas: &[F192], r_row: &[F192], kbc: usize) -> Vec<F192> {
    let slots = lean_vm::leaf::N_BYTECODE_SELECTORS;
    let mut out = vec![F192::ZERO; 1 << slots];
    for (p, &g) in points.iter().zip(gammas) {
        let row: F192 = (0..kbc).fold(g, |acc, k| acc * (F192::ONE + p[k] + r_row[k]));
        for (s, w) in out.iter_mut().enumerate() {
            let e = (0..slots).fold(row, |acc, b| {
                let c = p[kbc + b];
                acc * if (s >> b) & 1 == 1 { c } else { F192::ONE + c }
            });
            *w += e;
        }
    }
    out
}

/// Variables of a bytecode claim's point: the log row count plus the stacking
/// selectors.
fn bytecode_vars() -> usize {
    stacked_bytecode().len().trailing_zeros() as usize
}

/// Below this a parallel dispatch costs more than the loop it replaces.
const PAR_MIN: usize = 1 << 16;

fn fold_lsb(t: &mut Vec<F192>, r: F192) {
    let half = t.len() / 2;
    if half >= PAR_MIN {
        // Out of place: folding in place reads `t[2i]` while another task writes
        // `t[i]`, and the ranges overlap.
        let src: &[F192] = t;
        let folded = parallel::map_collect(half, |i| {
            let (a, b) = (src[2 * i], src[2 * i + 1]);
            a + r * (a + b)
        });
        *t = folded;
        return;
    }
    for i in 0..half {
        t[i] = t[2 * i] + r * (t[2 * i] + t[2 * i + 1]);
    }
    t.truncate(half);
}

/// Compressed product-sumcheck round message over γ-weighted table pairs:
/// (g1, g∞) with g0 recovered from the running claim.
fn round_msg(pairs: &[(&[F192], &[F192], F192)]) -> (F192, F192) {
    let (mut g1, mut gi) = (F192::ZERO, F192::ZERO);
    for &(u, m, gamma) in pairs {
        let half = u.len() / 2;
        let term = |i: usize| {
            let (u0, u1) = (u[2 * i], u[2 * i + 1]);
            let (m0, m1) = (m[2 * i], m[2 * i + 1]);
            (u1 * m1, (u0 + u1) * (m0 + m1))
        };
        let (a1, ai) = if half >= PAR_MIN {
            parallel::fold_reduce(
                half,
                || (F192::ZERO, F192::ZERO),
                |acc: &mut (F192, F192), i| {
                    let (x, y) = term(i);
                    acc.0 += x;
                    acc.1 += y;
                },
                |a: (F192, F192), b: (F192, F192)| (a.0 + b.0, a.1 + b.1),
            )
        } else {
            (0..half).fold((F192::ZERO, F192::ZERO), |acc, i| {
                let (x, y) = term(i);
                (acc.0 + x, acc.1 + y)
            })
        };
        g1 += gamma * a1;
        gi += gamma * ai;
    }
    (g1, gi)
}

/// One round of a batching sumcheck, in the transcript order the guest mirrors
/// word for word: observe `(g1, g_inf)`, squeeze the fold challenge, record
/// both, and advance the running claim through the compressed round polynomial.
/// Returns the challenge, which the caller folds its tables with.
fn absorb_round(
    h: &mut Sponge,
    msgs: &mut Vec<F192>,
    points: &mut Vec<F192>,
    run: &mut F192,
    (g1, gi): (F192, F192),
) -> F192 {
    h.observe(g1);
    h.observe(gi);
    let r = h.sample();
    msgs.extend([g1, gi]);
    points.push(r);
    let g0 = *run + g1;
    let c1 = g0 + g1 + gi;
    *run = (gi * r + c1) * r + g0;
    r
}

/// `Σ_t γ_t · eq(points[t], ·)`, over the `active` window of `2^vars` entries.
///
/// Each point splits in half; the halves' eq tables are small and serial, and
/// the full table is their outer product, one fused multiply-add per entry,
/// parallel over the high index. Materializing a `2^vars` eq table per claim and
/// summing them is the same arithmetic done twice, serially.
fn weighted_eq_table(points: &[Vec<F192>], gammas: &[F192], vars: usize, active: Range<usize>) -> Vec<F192> {
    let lo_vars = vars / 2;
    let lo_len = 1usize << lo_vars;
    debug_assert!(active.start.is_multiple_of(lo_len) && active.end.is_multiple_of(lo_len));
    // `build_eq_table_ext` is LSB-first, so the low variables index the low bits
    // and entry `hi * lo_len + lo` is `eq_lo[lo] * eq_hi[hi]`.
    let halves: Vec<(Vec<F192>, Vec<F192>)> = points
        .iter()
        .zip(gammas)
        .map(|(p, &g)| {
            let lo = pcs::whir::build_eq_table_ext(&p[..lo_vars]);
            let mut hi = pcs::whir::build_eq_table_ext(&p[lo_vars..]);
            hi.iter_mut().for_each(|h| *h *= g);
            (lo, hi)
        })
        .collect();
    let mut out = vec![F192::ZERO; active.len()];
    let first = active.start / lo_len;
    parallel::chunks_mut(&mut out, lo_len, |h, chunk| {
        for (lo, hi) in &halves {
            let scale = hi[first + h];
            for (o, &l) in chunk.iter_mut().zip(lo) {
                *o += scale * l;
            }
        }
    });
    out
}

/// The BLAKE2s R1CS matrices in CSR form with 16-bit column indices.
///
/// The matrices are fixed, so this is preprocessing paid once per process, and
/// the contractions below are bound by the index array rather than by their
/// arithmetic: `Vec<Vec<usize>>` is 8 bytes per nonzero across `K` separate
/// allocations, this is 2 (columns are below `2^K_LOG`) in one run.
struct Csr {
    starts: Vec<u32>,
    cols: Vec<u16>,
}

impl Csr {
    fn of(m: &flock::r1cs::SparseBinaryMatrix) -> Self {
        assert!(m.num_cols <= 1 << 16, "a column index must fit in u16");
        let mut starts = Vec::with_capacity(m.rows.len() + 1);
        let mut cols = Vec::with_capacity(m.rows.iter().map(Vec::len).sum());
        for row in &m.rows {
            starts.push(cols.len() as u32);
            cols.extend(row.iter().map(|&j| j as u16));
        }
        starts.push(cols.len() as u32);
        Self { starts, cols }
    }

    fn row(&self, i: usize) -> &[u16] {
        &self.cols[self.starts[i] as usize..self.starts[i + 1] as usize]
    }

    fn n_rows(&self) -> usize {
        self.starts.len() - 1
    }
}

fn matrices_csr() -> &'static (Csr, Csr) {
    static CSR: std::sync::OnceLock<(Csr, Csr)> = std::sync::OnceLock::new();
    CSR.get_or_init(|| {
        let (a, b) = flock::blake2s::matrices();
        (Csr::of(a), Csr::of(b))
    })
}

/// Contract every claim's column weights against one matrix: `out[i * n + t]`
/// sums claim `t`'s weight over row `i`'s nonzeros.
///
/// One pass over the nonzeros for ALL claims rather than one pass each, since
/// the index array is tens of millions of entries and dwarfs the arithmetic.
/// `wflat` is interleaved by claim for the same reason: a nonzero then costs one
/// random fetch of `n` adjacent weights instead of `n` fetches into `n` separate
/// tables, each its own cache miss.
fn contract_cols(m: &Csr, wflat: &[F192], n: usize) -> Vec<F192> {
    let mut out = vec![F192::ZERO; m.n_rows() * n];
    parallel::chunks_mut(&mut out, n, |i, acc| {
        for &j in m.row(i) {
            for (a, w) in acc.iter_mut().zip(&wflat[j as usize * n..][..n]) {
                *a += *w;
            }
        }
    });
    out
}

/// Contract one matrix along its rows at the point phase one fixed: a scatter,
/// so each worker accumulates into its own column vector and the dispatcher
/// adds them.
fn contract_rows(m: &Csr, n_cols: usize, eq_rstar: &[F192]) -> Vec<F192> {
    parallel::fold_reduce(
        m.n_rows(),
        || vec![F192::ZERO; n_cols],
        |acc, i| {
            let e = eq_rstar[i];
            for &j in m.row(i) {
                acc[j as usize] += e;
            }
        },
        |mut a, b| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        },
    )
}

/// Mirror the guest's `aggregate_claims` transcript and prove the two batching
/// sumchecks: dense for the bytecode, two-phase sparse for the matrices.
///
/// Each child brings two claims per fixed polynomial: the one it deferred
/// (`carried`) and the fresh one its verification raised (`subs`). They differ
/// only in the weight they enter with. A fresh matrix claim carries flock's
/// zerocheck/lincheck structure; a carried one is a plain point, so its weight
/// is an eq table on each side. Returns the guest hints and the single claim
/// per polynomial they reduce to.
fn aggregate_deferred_claims(subs: &[DeferredSubproof], carried: &[DeferredClaim]) -> (SubHints, DeferredClaim) {
    let nsub = subs.len();
    assert_eq!(nsub, carried.len(), "one carried claim per child");
    let kbcv = bytecode_vars();
    let klog = flock::blake2s::K_LOG;

    // ---- the aggregation transcript (mirrors the guest exactly) ----
    let mut h = Sponge::new(RECURSION_AGG_LABEL, &[]);
    h.observe(count(nsub));
    for (d, c) in subs.iter().zip(carried) {
        h.observe(d.public_input[0]);
        h.observe(d.public_input[1]);
        for &v in &d.bytecode_row_point {
            h.observe(v);
        }
        for &v in &d.bytecode_selector_point {
            h.observe(v);
        }
        h.observe(d.bytecode_value);
        h.observe(d.matrix_a_coefficient);
        h.observe(d.skip_point);
        for &v in &d.zerocheck_row_point {
            h.observe(v);
        }
        for &v in &d.lincheck_round_point {
            h.observe(v);
        }
        for &v in &d.lincheck_terminal_values {
            h.observe(v);
        }
        h.observe(d.matrix_claim);
        for v in c.cells() {
            h.observe(v);
        }
    }

    // ---- bytecode batching sumcheck (dense, 2^kbcv; fresh then carried per child) ----
    let _span = tracing::info_span!("Bytecode batch", vars = kbcv).entered();
    let gbc: Vec<F192> = (0..2 * nsub).map(|_| h.sample()).collect();
    let points: Vec<Vec<F192>> = subs
        .iter()
        .zip(carried)
        .flat_map(|(d, c)| {
            [
                d.bytecode_row_point
                    .iter()
                    .chain(&d.bytecode_selector_point)
                    .copied()
                    .collect::<Vec<_>>(),
                c.bytecode_point.clone(),
            ]
        })
        .collect();
    let values: Vec<F192> = subs
        .iter()
        .zip(carried)
        .flat_map(|(d, c)| [d.bytecode_value, c.bytecode_value])
        .collect();
    let mut brun: F192 = (0..2 * nsub).map(|t| gbc[t] * values[t]).fold(F192::ZERO, |a, x| a + x);
    let mut bscr = Vec::new();
    let mut r_bc = Vec::new();
    // The row variables, over the populated slot window only: the rest of the
    // stacked table is structurally zero and contributes nothing to any round
    // message, and folding LSB-first pairs entries within a slot, so the window's
    // blocks stay aligned all the way down.
    let n_slots = 1 << lean_vm::leaf::N_BYTECODE_SELECTORS;
    let slot_window = bytecode_window();
    let kbc = kbcv - lean_vm::leaf::N_BYTECODE_SELECTORS;
    let mut wt = weighted_eq_table(
        &points,
        &gbc,
        kbcv,
        (slot_window.start << kbc)..(slot_window.end << kbc),
    );
    // Round zero runs against the K-valued table itself: the bytecode never needs
    // to exist as `2^kbcv` extension elements (three times the memory traffic),
    // and base-by-extension is cheaper than extension-by-extension. Every later
    // round is extension-valued anyway.
    let bc = &stacked_bytecode()[(slot_window.start << kbc)..(slot_window.end << kbc)];
    let mut bt = {
        let msg = round_msg_base(bc, &wt);
        let r = absorb_round(&mut h, &mut bscr, &mut r_bc, &mut brun, msg);
        let folded = fold_lsb_base(bc, r);
        fold_lsb(&mut wt, r);
        folded
    };
    for _ in 1..kbc {
        let msg = round_msg(&[(&bt, &wt, F192::ONE)]);
        let r = absorb_round(&mut h, &mut bscr, &mut r_bc, &mut brun, msg);
        fold_lsb(&mut bt, r);
        fold_lsb(&mut wt, r);
    }
    // The slot variables. The window has folded to one entry per populated slot;
    // put those back among the zeros. The weights come from a closed form rather
    // than from having carried a `2^kbcv` table through the rows.
    let mut bt_slots = vec![F192::ZERO; n_slots];
    bt_slots[slot_window.clone()].copy_from_slice(&bt);
    let wt_slots = slot_weights(&points, &gbc, &r_bc, kbc);
    let (mut bt, mut wt) = (bt_slots, wt_slots);
    for _ in 0..lean_vm::leaf::N_BYTECODE_SELECTORS {
        let msg = round_msg(&[(&bt, &wt, F192::ONE)]);
        let r = absorb_round(&mut h, &mut bscr, &mut r_bc, &mut brun, msg);
        fold_lsb(&mut bt, r);
        fold_lsb(&mut wt, r);
    }
    let v_bc = bt[0];
    assert_eq!(brun, v_bc * wt[0], "bytecode sumcheck terminal");

    drop(_span);
    let _span = tracing::info_span!("Matrix batch").entered();
    // ---- matrix batching sumcheck (two-phase sparse) ----
    // One group per claim: the row weights, the column weights, and the
    // coefficient each matrix enters with. Downstream is shape-blind.
    let mut us: Vec<Vec<F192>> = Vec::with_capacity(2 * nsub);
    let mut ws: Vec<Vec<F192>> = Vec::with_capacity(2 * nsub);
    let mut ga: Vec<F192> = Vec::with_capacity(2 * nsub);
    let mut gb: Vec<F192> = Vec::with_capacity(2 * nsub);
    let mut mrun = F192::ZERO;
    for (d, c) in subs.iter().zip(carried) {
        let (gf, cga, cgb) = (h.sample(), h.sample(), h.sample());
        us.push(flock::lincheck::build_quirky_eq_table(
            d.skip_point,
            &d.zerocheck_row_point,
            6,
        ));
        ws.push(
            (0..1usize << klog)
                .map(|col| {
                    let mut w = d.lincheck_terminal_values[col & 63];
                    for (j, &rj) in d.lincheck_round_point.iter().enumerate() {
                        let bit = (col >> (klog - 1 - j)) & 1;
                        w *= if bit == 1 { rj } else { F192::ONE + rj };
                    }
                    w
                })
                .collect(),
        );
        ga.push(gf * d.matrix_a_coefficient);
        gb.push(gf);
        us.push(pcs::whir::build_eq_table_ext(&c.matrix_point[..klog]));
        ws.push(pcs::whir::build_eq_table_ext(&c.matrix_point[klog..]));
        ga.push(cga);
        gb.push(cgb);
        mrun += gf * d.matrix_claim + cga * c.matrix_a_value + cgb * c.matrix_b_value;
    }
    let (ma, mb) = matrices_csr();
    let (n_claims, n_rows) = (ws.len(), ma.n_rows());
    assert_eq!(n_rows, mb.n_rows(), "the two matrices share their row space");
    let mut wflat = vec![F192::ZERO; (1 << klog) * n_claims];
    for (t, w) in ws.iter().enumerate() {
        for (j, &v) in w.iter().enumerate() {
            wflat[j * n_claims + t] = v;
        }
    }
    let _cols = tracing::info_span!("Contract columns").entered();
    let (ca, cb) = (contract_cols(ma, &wflat, n_claims), contract_cols(mb, &wflat, n_claims));
    drop(_cols);
    // Back to one table per claim, A before B, which is the order `ga`/`gb` index.
    let mut ms: Vec<Vec<F192>> = Vec::with_capacity(2 * n_claims);
    for t in 0..n_claims {
        ms.push((0..n_rows).map(|i| ca[i * n_claims + t]).collect());
        ms.push((0..n_rows).map(|i| cb[i * n_claims + t]).collect());
    }
    // sanity: every claim really is the bilinear form over the matrices.
    #[cfg(debug_assertions)]
    for t in 0..2 * nsub {
        let form = |m: &[F192]| {
            m.iter()
                .zip(&us[t])
                .map(|(&m, &u)| m * u)
                .fold(F192::ZERO, |a, x| a + x)
        };
        let (fa, fb) = (form(&ms[2 * t]), form(&ms[2 * t + 1]));
        if t % 2 == 0 {
            let d = &subs[t / 2];
            assert_eq!(
                d.matrix_a_coefficient * fa + fb,
                d.matrix_claim,
                "fresh matrix claim, child {}",
                t / 2
            );
        } else {
            let c = &carried[t / 2];
            assert_eq!((fa, fb), (c.matrix_a_value, c.matrix_b_value), "carried matrix claim");
        }
    }
    let mut mscr = Vec::new();
    let mut r_row = Vec::new();
    let _rounds = tracing::info_span!("Row rounds").entered();
    for _ in 0..klog {
        let pairs: Vec<(&[F192], &[F192], F192)> = (0..2 * nsub)
            .flat_map(|t| {
                [
                    (&us[t][..], &ms[2 * t][..], ga[t]),
                    (&us[t][..], &ms[2 * t + 1][..], gb[t]),
                ]
            })
            .collect();
        let msg = round_msg(&pairs);
        let r = absorb_round(&mut h, &mut mscr, &mut r_row, &mut mrun, msg);
        for u in us.iter_mut() {
            fold_lsb(u, r);
        }
        for m in ms.iter_mut() {
            fold_lsb(m, r);
        }
    }
    drop(_rounds);
    let eq_rstar = pcs::whir::build_eq_table_ext(&r_row);
    let _rows = tracing::info_span!("Contract rows").entered();
    let mut acol = contract_rows(ma, 1 << klog, &eq_rstar);
    let mut bcol = contract_rows(mb, 1 << klog, &eq_rstar);
    drop(_rows);
    let mut wa = vec![F192::ZERO; 1 << klog];
    let mut wb = vec![F192::ZERO; 1 << klog];
    for t in 0..2 * nsub {
        let (sa, sb) = (ga[t] * us[t][0], gb[t] * us[t][0]);
        for j in 0..1 << klog {
            wa[j] += sa * ws[t][j];
            wb[j] += sb * ws[t][j];
        }
    }
    let mut r_col = Vec::new();
    for _ in 0..klog {
        let pairs: Vec<(&[F192], &[F192], F192)> = vec![(&acol, &wa, F192::ONE), (&bcol, &wb, F192::ONE)];
        let msg = round_msg(&pairs);
        let r = absorb_round(&mut h, &mut mscr, &mut r_col, &mut mrun, msg);
        for tb in [&mut acol, &mut bcol, &mut wa, &mut wb] {
            fold_lsb(tb, r);
        }
    }
    let (v_a, v_b) = (acol[0], bcol[0]);
    assert_eq!(mrun, v_a * wa[0] + v_b * wb[0], "matrix sumcheck terminal");
    // The guest reaches the same two weights by a succinct formula rather than by
    // folding these tables, and nothing else compares the two: the aggregation
    // layer has no third implementation the way `cpu::verify` does. So this runs
    // unconditionally (it is O(n) against a 2^28 sumcheck), and it compares the
    // weights COMPONENT-WISE. Checking only the combination `v_a·wa + v_b·wb`
    // would let two correlated errors through.
    {
        let eqr = pcs::whir::build_eq_table_ext(&r_row[..6]);
        let eqc = pcs::whir::build_eq_table_ext(&r_col[..6]);
        let (mut wam, mut wbm) = (F192::ZERO, F192::ZERO);
        for (t, (d, c)) in subs.iter().zip(carried).enumerate() {
            let lam = primitives::multilinear::lagrange_weights_naive(6, d.skip_point);
            let mut urow: F192 = (0..64).map(|i| lam[i] * eqr[i]).fold(F192::ZERO, |a, x| a + x);
            for (k, &z) in d.zerocheck_row_point.iter().enumerate() {
                urow *= F192::ONE + z + r_row[6 + k];
            }
            let mut wcol: F192 = (0..64)
                .map(|i| d.lincheck_terminal_values[i] * eqc[i])
                .fold(F192::ZERO, |a, x| a + x);
            for (j, &rj) in d.lincheck_round_point.iter().enumerate() {
                wcol *= F192::ONE + rj + r_col[klog - 1 - j];
            }
            let fresh = urow * wcol;
            let mut plain = F192::ONE;
            for (k, &p) in c.matrix_point.iter().enumerate() {
                let r = if k < klog { r_row[k] } else { r_col[k - klog] };
                plain *= F192::ONE + p + r;
            }
            wam += ga[2 * t] * fresh + ga[2 * t + 1] * plain;
            wbm += gb[2 * t] * fresh + gb[2 * t + 1] * plain;
        }
        assert_eq!(wa[0], wam, "guest row-weight formula for A0");
        assert_eq!(wb[0], wbm, "guest row-weight formula for B0");
    }

    drop(_span);
    let hints = vec![
        ("bc_sumcheck_msgs".to_string(), bscr),
        ("mat_sumcheck_msgs".to_string(), mscr),
        ("bc_star_hint".to_string(), vec![v_bc]),
        ("mat_stars_hint".to_string(), vec![v_a, v_b]),
    ];
    (
        hints,
        DeferredClaim {
            bytecode_point: r_bc,
            bytecode_value: v_bc,
            matrix_point: r_row.iter().chain(&r_col).copied().collect(),
            matrix_a_value: v_a,
            matrix_b_value: v_b,
        },
    )
}

/// The verifier-side WHIR config for one committed size and rate, plus the
/// query packing derived from it. The hint builder needs it for the real
/// opening and the placeholder map for every candidate size, so it lives here:
/// a candidate whose shape differed from the real one would compile a guest
/// that cannot open the proof it is handed.
struct WhirShape {
    config: pcs::whir::VerifierConfig,
    levels: pcs::whir::LevelShapes,
    /// Merkle tree depth per level.
    depth: Vec<usize>,
    /// Query positions carried by one squeezed F192 word, per level.
    per_squeeze: Vec<usize>,
}

fn whir_shape(mu: usize, log_inv_rate: usize) -> WhirShape {
    let config = pcs::whir::WhirSecurityConfig::derive_config_with_log_inv_rate(mu + pcs::LOG_PACKING, log_inv_rate)
        .and_then(|s| s.to_prover_verifier_configs())
        .expect("stacked whir config")
        .1;
    let levels = config.level_shapes(mu);
    let depth: Vec<usize> = levels.block_len.iter().map(|b| b.trailing_zeros() as usize).collect();
    let per_squeeze = depth.iter().map(|&d| 192 / d).collect();
    WhirShape {
        config,
        levels,
        depth,
        per_squeeze,
    }
}

/// The BLAKE2s table's virtual value columns, in `blake2s_flock::SLOTS` order.
fn blake2s_value_columns() -> Vec<usize> {
    let base = lean_vm::cpu::schema().base[5];
    lean_vm::tables::BLAKE2S_VALUE_COLS.iter().map(|&c| base + c).collect()
}

/// One entry of the guest's claim pool.
enum ClaimSite {
    /// A framework bus block reads a committed column at this kappa.
    Framework { column: usize, kappa: usize },
    /// A committed column of `table`; `is_virtual` marks the q_flock-backed value
    /// columns, whose claim is a strided slot rather than a plain column.
    TableColumn {
        table: usize,
        column: usize,
        is_virtual: bool,
    },
    /// One of the three PI memory limbs (MEM_LO, MEM_HI, MEM_TOP).
    MemoryLimb { column: usize },
}

/// The guest's `COORD_KIND_*` code for a coordinate (`guests/aggregate.py`),
/// shared by its `COORD_TYPE` and `TERM_TYPE` arrays.
fn coord_kind(c: &Coord) -> usize {
    match c {
        Coord::Const(_) => 0,
        Coord::Col(_) => 1,
        Coord::GCol(..) => 2,
        Coord::Index => 3,
        Coord::Public(_) => 4,
        Coord::Prod(..) => 5,
        Coord::Sum(..) => 6,
    }
}

/// The `K` scalar a coordinate carries beside its columns: the constant itself,
/// or the `g^k` a `GCol`/`Prod` scales by. Zero for every other kind.
fn coord_scale(c: &Coord) -> F192 {
    match c {
        Coord::Const(v) => F192::new(v.0, 0, 0),
        Coord::GCol(_, k) | Coord::Prod(_, _, k) => F192::new(g_pow(*k as usize).0, 0, 0),
        _ => F192::ZERO,
    }
}

/// Flatten one table-block coordinate into the guest's term arrays, in local
/// column indices. A [`Coord::Sum`]'s children are its terms; every other kind is
/// one term. `Index`/`Public` never reach a table block.
fn push_coord_terms(
    c: &Coord,
    base: usize,
    ty: &mut Vec<usize>,
    val: &mut Vec<u128>,
    col_a: &mut Vec<usize>,
    col_b: &mut Vec<usize>,
) {
    let (a, b) = match c {
        Coord::Const(_) => (0, 0),
        Coord::Col(i) | Coord::GCol(i, _) => (*i - base, 0),
        Coord::Prod(i, j, _) => (*i - base, *j - base),
        Coord::Sum(cs) => {
            for c in cs {
                push_coord_terms(c, base, ty, val, col_a, col_b);
            }
            return;
        }
        Coord::Index | Coord::Public(_) => unreachable!("a table's bus block carries no virtual coordinate"),
    };
    ty.push(coord_kind(c));
    val.push(u(coord_scale(c)));
    col_a.push(a);
    col_b.push(b);
}

/// Visit the claim pool in the exact order the guest indexes it: the framework
/// bus claims (deduped by `(column, kappa)`, as `leaf.rs` pools them), then every
/// table's committed columns, then the PI memory triple. Both the per-sub hints
/// and the placeholder map descriptors are built from this one walk, so the two
/// stay index-aligned by construction rather than by two matching count asserts.
fn walk_claims(l: &lean_vm::cpu::Layout, kbc: usize, mut visit: impl FnMut(ClaimSite)) {
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let valcols = blake2s_value_columns();
    // Only the framework blocks raise claims: a table's coords are settled inside
    // the table sumcheck.
    let is_framework: Vec<bool> = lean_vm::cpu::block_kappa_sources(kbc)
        .into_iter()
        .map(|(src, _)| src < 2)
        .collect();
    let mut seen: std::collections::HashSet<(usize, usize)> = Default::default();
    let mut bi = 0usize;
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            let framework = is_framework[bi];
            bi += 1;
            if !framework {
                continue;
            }
            for c in &blk.coords {
                if let Coord::Col(i) | Coord::GCol(i, _) = c {
                    if !seen.insert((*i, blk.kappa)) {
                        continue; // deduped: pooled once at its first occurrence
                    }
                    assert!(!valcols.contains(i), "{VALCOL_FRAMEWORK}");
                    visit(ClaimSite::Framework {
                        column: *i,
                        kappa: blk.kappa,
                    });
                }
            }
        }
    }
    let sch = lean_vm::cpu::schema();
    for (t, table) in lean_vm::tables::tables().iter().enumerate() {
        for c in 0..table.n_committed_columns() {
            let column = sch.base[t] + c;
            visit(ClaimSite::TableColumn {
                table: t,
                column,
                is_virtual: l.placements[column].is_virtual(),
            });
        }
    }
    for &column in &[lean_vm::cpu::MEM_LO, lean_vm::cpu::MEM_HI, lean_vm::cpu::MEM_TOP] {
        visit(ClaimSite::MemoryLimb { column });
    }
}

/// Config + hints for the recursion guest (`guests/aggregate.py`), built
/// from the REAL `cpu::layout` of the inner program and the transcript trace of
/// a real `cpu::verify` run (zero hand-mirroring drift).
fn gen_verify(
    program: &Program,
    pi: [F192; 2],
    summary: &lean_vm::cpu::VerifySummary,
    ops: &[TraceOp],
) -> Result<(SubHints, DeferredSubproof), AggregateError> {
    let raw = &summary.raw.stream;
    let l = lean_vm::cpu::layout(
        &program.prog,
        raw[0].c0 as usize,
        std::array::from_fn(|i| raw[1 + i].c0 as usize),
        pi,
    );
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let lays: Vec<lean_vm::leaf::Layout> = sides.iter().map(|b| lean_vm::leaf::layout(b)).collect();
    let smu: Vec<usize> = lays.iter().map(|x| x.mu).collect();
    // Fixed capacities: every buffer/stride placeholder is a global cap so
    // the placeholder map is SHAPE-INDEPENDENT (the definition of generic).
    assert!(*smu.iter().max().unwrap() <= MU_CAP && raw.len() <= STREAM_CAP);
    // The guest holds one opening arm per candidate committed size, so a child
    // outside that window has no arm to dispatch to. `min_log_committed` keeps
    // every aggregate above the low end, leaving only the ceiling reachable.
    if !(MU_MIN..=MU_MAX).contains(&l.m) {
        return Err(AggregateError::ChildOutOfRange { log_committed: l.m });
    }

    // ---- typed extraction: proof structs + the verifier's summary ----
    // Drift check: replaying the recorded trace from the seed must reproduce
    // every challenge and grind the native run produced.
    let fs_seed = lean_vm::cpu::fs_seed(program);
    let seed = Sponge::new(b"leanvm-b", &[fs_seed[0], fs_seed[1], pi[0], pi[1]]);
    seed.clone().replay(ops);

    // Grinding digests are the only trace-borne data (they are functions of
    // sponge states): fold grinds carry bits > 0 and query-phase grinds carry
    // bits = 0.
    let pows: Vec<(F192, u32, F64)> = ops
        .iter()
        .filter_map(|op| match op {
            TraceOp::Pow { nonce, bits, digest } => Some((*nonce, *bits, *digest)),
            _ => None,
        })
        .collect();
    // Bus: the bytecode claims carry the push/pull ζ_lo points and sb.
    let kbc = summary.bytecode_claims[0].point.len() - lean_vm::leaf::N_BYTECODE_SELECTORS;
    let zeta: Vec<F192> = summary.bytecode_claims[0].point[..kbc].to_vec();
    let sb: Vec<F192> = summary.bytecode_claims[0].point[kbc..].to_vec();

    let taus = l.taus;
    // Flock replay data, all named struct fields.
    let lcrounds = flock::blake2s::K_LOG - 6;
    let zcf = [summary.zc_claim.a_eval, summary.zc_claim.b_eval];
    let zc_z = summary.zc_claim.z;
    let zrho = summary.zc_claim.mlv_challenges.clone();
    let lc_alpha = summary.lc_claim.alpha;
    let lc_beta = summary.lc_claim.beta;
    let lrr = summary.lc_claim.r_rounds.clone();

    // ---- the stacked opening: config + the opening summary ----
    let stack = whir_shape(l.m, summary.log_inv_rate);
    let (vcfg, shapes) = (&stack.config, &stack.levels);
    let nlev = shapes.levels;
    let klvl = &shapes.ks;
    let fgb = |lvl: usize| vcfg.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;

    // flock's reduction ends at `flock_stream_end`, where the WHIR opening's own
    // scalars start: its last 64 scalars are lincheck's `z_partial` (which the
    // summary already carries as `s_hat_v`), immediately preceded by the
    // `(e0, e1, e_inf)` triples of the `lcrounds` lincheck rounds.
    let ns = summary.flock_stream_end;
    let lcr: Vec<F192> = raw[ns - 64 - 3 * lcrounds..ns - 64].to_vec();
    let lcz: Vec<F192> = summary.lc_claim.s_hat_v.clone();

    // matpart = the deferred weighted matrix evaluation: the lincheck running
    // claim minus (= plus, char 2) the const-pin contribution.
    let mut lrun = lc_alpha * zcf[0] + zcf[1] + lc_beta;
    for i in 0..lcrounds {
        let (e0, e1, ei, rv) = (lcr[3 * i], lcr[3 * i + 1], lcr[3 * i + 2], lrr[i]);
        let c1q = e0 + e1 + ei;
        lrun = (ei * rv + c1q) * rv + e0;
    }
    let mut pinw = lc_beta;
    for (j, &rv) in lrr.iter().enumerate() {
        let bit = (flock::blake2s::Z_CONST_POS >> (flock::blake2s::K_LOG - 1 - j)) & 1;
        pinw *= if bit == 1 { rv } else { F192::ONE + rv };
    }
    pinw *= lcz[flock::blake2s::Z_CONST_POS % 64];
    let matpart = lrun + pinw;

    // Grind sanity: in transcript order, per level, the fold grinds (bits > 0
    // per the config schedule) then ONE query-phase
    // grind. The nonces themselves ride the shared stream now (raw words);
    // the trace is only cross-checked here.
    let qbits: Vec<u32> = (0..nlev).map(|lvl| vcfg.grinding_bits[lvl] as u32).collect();
    let mut grinds = pows.iter();
    for lvl in 0..nlev {
        for j in 0..klvl[lvl] {
            let bits = (fgb(lvl) - j as i64).max(0) as u32;
            if bits > 0 {
                let &(_, b2, _) = grinds.next().expect("fold grind recorded");
                assert_eq!(b2, bits);
            }
        }
        let &(_, b2, _) = grinds.next().expect("query grind recorded");
        assert_eq!(b2, qbits[lvl], "level {lvl} query grind bits");
    }
    assert!(grinds.next().is_none(), "every grind consumed");

    // ---- hints ----
    // The program's whole share of a bytecode leaf: ONE value, the stacked
    // polynomial at (ζ_lo, α⃗), the slot coordinates of the claim's own point being
    // the fingerprint challenges (§sec:e2e-bc).
    let bytecode_value = summary.bytecode_claims[0].value;
    let bcv = vec![bytecode_value];

    // ---- per-sub HINT data (the placeholder map is built once, elsewhere) ----
    // Per side, the packing order read straight off `leaf::layout`'s offsets:
    // sort_order[side_base + rank] = g^{side-local index of the rank-r block}.
    // The guest only perm-checks it and derives offsets; any aligned tiling is
    // sound, so this canonical order just has to match the committed leaf.
    let mut sort_order: Vec<F192> = Vec::new();
    let mut gbase = 0usize;
    for (s, blocks) in sides.iter().enumerate() {
        let mut order: Vec<usize> = (0..blocks.len()).collect();
        order.sort_by_key(|&i| lays[s].offsets[i]);
        for &i in &order {
            sort_order.push(F192::new(g_pow(gbase + i).0, 0, 0)); // g^{global block index}
        }
        gbase += blocks.len();
    }
    // The stacked commitment uses witness::placements_of: committed columns
    // sorted by descending kappa, then by their native column index. Transport
    // compact committed-column indices; the guest certifies the permutation,
    // ordering, and accumulated offsets before using them as claim selectors.
    let col_sources = lean_vm::cpu::col_kappa_sources(kbc);
    let committed_globals: Vec<usize> = col_sources
        .iter()
        .enumerate()
        .filter_map(|(i, source)| source.map(|_| i))
        .collect();
    let mut compact_col = vec![usize::MAX; col_sources.len()];
    for (compact, &global) in committed_globals.iter().enumerate() {
        compact_col[global] = compact;
    }
    let mut col_order = committed_globals.clone();
    col_order.sort_by_key(|&global| l.placements[global].offset);
    let col_sort_order: Vec<F192> = col_order
        .iter()
        .map(|&global| F192::new(g_pow(compact_col[global]).0, 0, 0))
        .collect();
    let log_mem = raw[0].c0 as usize;

    // ---- Phase E2 hints (the stacked WHIR opening) ----
    let lenris: usize = klvl.iter().sum();
    // The verifier already authenticated every queried row and expanded the
    // pruned phases into one full path per query, in level order. The guest
    // re-hashes exactly that: a leaf is its `F64` words (one per interleaved K
    // value at level 0, three per `E` value deeper), then a walk up the path.
    let (mut lrows_flat, mut lpaths_flat): (Vec<F192>, Vec<F192>) = (Vec::new(), Vec::new());
    for opening in &summary.raw.merkle_openings {
        lrows_flat.extend(opening.leaf_data.iter().map(|x| F192::new(x.0, 0, 0)));
        for h in &opening.path {
            lpaths_flat.extend_from_slice(&pack_hash_state(h));
        }
    }
    // claim descriptors, in exact clv order.
    let mut nover_v = Vec::new();
    walk_claims(&l, program.prog.len().trailing_zeros() as usize, |site| {
        // Per claim, `nvt` is the full low span; when it exceeds `lenris` the point
        // overlaps the residual y region by `nover` coords. Stack selectors are not
        // emitted: the guest derives them from the certified committed-column offsets.
        let nvt = match site {
            ClaimSite::Framework { kappa, .. } => kappa,
            ClaimSite::TableColumn { table, is_virtual, .. } => {
                if is_virtual {
                    lean_vm::blake2s_flock::SLOT_STRIDE_LOG + taus[table]
                } else {
                    taus[table]
                }
            }
            // The three PI memory lanes share one point [r_m, 0, 0, ...]; the coords
            // beyond `lenris` are const zero, so they fold into the y pattern instead
            // of a runtime overlap factor.
            ClaimSite::MemoryLimb { column } => l.placements[column].n_vars.min(lenris),
        };
        nover_v.push(nvt.saturating_sub(lenris));
    });

    // The ring-switch weight's own residual overlap: the q_flock claim spans
    // `qflockv` coordinates, and a BLAKE2s-dominated inner proof pushes that past
    // the fold rounds. Same quantity as the q_flock point claim's `nover`, but
    // the guest pins it independently, in the rs block.
    let qflockv = lean_vm::blake2s_flock::SLOT_STRIDE_LOG + taus[5];
    let rs_nover = qflockv.saturating_sub(lenris);

    let deferred = DeferredSubproof {
        public_input: pi,
        bytecode_row_point: zeta,
        bytecode_selector_point: sb.clone(),
        bytecode_value,
        matrix_a_coefficient: lc_alpha,
        skip_point: zc_z,
        zerocheck_row_point: zrho[..lcrounds].to_vec(),
        lincheck_round_point: lrr.clone(),
        lincheck_terminal_values: lcz.clone(),
        matrix_claim: matpart,
    };

    let hints = vec![
        ("stream".to_string(), {
            // The guest replays the WHIR opening off the same stream the native
            // verifier reads: every transmitted scalar (sumcheck messages, level
            // roots, OOD claims, grind nonces, `yr`) is already there in protocol
            // order, so there is nothing to reassemble. The guest's `open_stacked`
            // picks it up at `msg_cursor = cursor`, which sits where the flock
            // reduction stopped; the ring-switch messages are struct-observed and
            // still do not advance that cursor.
            let mut v = raw.clone();
            assert!(v.len() <= STREAM_CAP, "stream {} exceeds cap {STREAM_CAP}", v.len());
            v.resize(STREAM_CAP, F192::ZERO);
            v
        }),
        ("bytecode_val".to_string(), bcv),
        ("matpart".to_string(), vec![matpart]),
        ("merkle_leaf_rows".to_string(), lrows_flat),
        ("merkle_paths".to_string(), lpaths_flat),
        // per-claim overlap count, for the exact length pin: nover = the
        // amount by which the claim's total vars exceed the fold rounds.
        (
            "claim_nover".to_string(),
            nover_v.iter().map(|&n| F192::new(g_pow(n).0, 0, 0)).collect(),
        ),
        // the pi claim's low dimension is min(log_mem, lenris); certify it as
        // a min (<= both, == one) so pi is pinned like every other claim.
        (
            "pi_cplen".to_string(),
            vec![F192::new(g_pow(log_mem.min(lenris)).0, 0, 0)],
        ),
        // the table sumcheck's round count: max_t tau_t, certified in-guest as a
        // maximum (one of the taus, and dominating them all).
        (
            "zc_tau_max".to_string(),
            vec![F192::new(g_pow(*taus.iter().max().unwrap()).0, 0, 0)],
        ),
        ("rs_nover".to_string(), vec![F192::new(g_pow(rs_nover).0, 0, 0)]),
        ("col_sort_order".to_string(), col_sort_order),
        ("sort_order".to_string(), sort_order),
    ];
    Ok((hints, deferred))
}

/// The guest's stacked-size dispatch range: one `match_range` opening arm per
/// candidate `mu` in `MU_MIN..=MU_MAX` (mirrored by the soundness test's
/// residual-log cap).
const MU_MIN: usize = 22;
const MU_MAX: usize = 28;

/// The guest's baked buffer caps, which `placeholder_map` compiles in and
/// `gen_verify` admits against: one definition, so a hinted shape can never
/// outgrow the buffer the guest was compiled with.
const MU_CAP: usize = 40;
const STREAM_CAP: usize = 8192;

/// Verify an inner proof with the transcript tracer on, which is what keeps the
/// native and guest verifiers synchronized (`gen_verify` walks the recorded ops).
fn traced_verify(
    program: &Program,
    pi: &[F192; 2],
    proof: &lean_vm::cpu::Proof,
) -> Result<(lean_vm::cpu::VerifySummary, Vec<TraceOp>), VerifyError> {
    trace_start();
    let summary = verify(program, pi, proof);
    // Take the trace before propagating: a failed child verification would
    // otherwise leave the thread-local recorder on, and every later sponge
    // operation in the process would append to it.
    let ops = trace_take();
    Ok((summary.map_err(VerifyError::Proof)?, ops))
}

/// One entry per named hint stream, for a single sub-proof.
type SubHints = Vec<(String, Vec<F192>)>;

/// One `hint_witness` stream: a name and its entries, in the order the guest
/// pops them.
#[derive(Default)]
pub(crate) struct Hints(Vec<(String, Vec<Vec<F192>>)>);

impl Hints {
    fn push(&mut self, name: &str, entry: Vec<F192>) {
        match self.0.iter_mut().find(|(n, _)| n == name) {
            Some((_, entries)) => entries.push(entry),
            None => self.0.push((name.to_string(), vec![entry])),
        }
    }

    /// The entries of one stream, for the adversarial test to corrupt.
    #[cfg(test)]
    fn entries(&mut self, name: &str) -> &mut Vec<Vec<F192>> {
        &mut self
            .0
            .iter_mut()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("no hint stream `{name}`"))
            .1
    }

    fn install(self, guest: &mut Program) {
        for (name, entries) in self.0 {
            guest.set_witness(name, entries);
        }
    }
}

/// The signer index each write in the guest's coverage walk targets, in walk
/// order: the raw signatures first, then each child's key list.
///
/// A key first seen takes its slot in the declared set; one seen again takes a
/// fresh duplicate slot past it, so the walk hits every one of the
/// `n_keys + n_dup` slots exactly once. That bijection, enforced in-circuit by
/// write-once memory plus the final count, is what makes every declared key
/// covered by a real signature or a verified child.
struct Coverage {
    keys: Vec<XmssPublicKey>,
    duplicates: Vec<XmssPublicKey>,
    raw_indices: Vec<usize>,
    child_indices: Vec<Vec<usize>>,
}

fn take_slot(
    keys: &[XmssPublicKey],
    claimed: &mut [bool],
    duplicates: &mut Vec<XmssPublicKey>,
    pk: &XmssPublicKey,
) -> usize {
    let pos = keys.binary_search(pk).expect("every covered key is in the union");
    if claimed[pos] {
        duplicates.push(pk.clone());
        keys.len() + duplicates.len() - 1
    } else {
        claimed[pos] = true;
        pos
    }
}

fn plan_coverage(raw: &[XmssPublicKey], children: &[&[XmssPublicKey]]) -> Result<Coverage, AggregateError> {
    let mut keys: Vec<XmssPublicKey> = raw.to_vec();
    for c in children {
        keys.extend_from_slice(c);
    }
    keys.sort();
    keys.dedup();
    if keys.is_empty() {
        return Err(AggregateError::Empty);
    }
    let mut claimed = vec![false; keys.len()];
    let mut duplicates = Vec::new();
    let raw_indices: Vec<usize> = raw
        .iter()
        .map(|pk| take_slot(&keys, &mut claimed, &mut duplicates, pk))
        .collect();
    let child_indices: Vec<Vec<usize>> = children
        .iter()
        .map(|c| {
            c.iter()
                .map(|pk| take_slot(&keys, &mut claimed, &mut duplicates, pk))
                .collect()
        })
        .collect();
    if keys.len() + duplicates.len() >= MAX_KEYS {
        return Err(AggregateError::TooLarge);
    }
    Ok(Coverage {
        keys,
        duplicates,
        raw_indices,
        child_indices,
    })
}

/// One signature's witness: the WOTS randomness, the encoding digits (in the
/// exponent), the chain tips they start from, and the Merkle siblings.
fn push_signature_hints(
    hints: &mut Hints,
    pk: &XmssPublicKey,
    sig: &XmssSignature,
    message: &xmss::Message,
    epoch: u32,
) {
    let wots = &sig.wots_signature;
    let mut randomness = [0u8; xmss::STATE_LEN];
    randomness[..xmss::RANDOMNESS_LEN].copy_from_slice(&wots.randomness);
    hints.push("rand", vec![val16(&randomness[..16]), val16(&randomness[16..])]);
    let encoding =
        xmss::wots_encode(message, epoch, &pk.public_param, &wots.randomness).expect("a verified signature encodes");
    for &e in &encoding {
        hints.push("digits", vec![count(e as usize)]);
    }
    for tip in &wots.chain_tips {
        hints.push("chain_starts", vec![val16(tip)]);
    }
    for sibling in &sig.merkle_proof {
        hints.push("siblings", vec![val16(sibling)]);
    }
}

/// Aggregate raw XMSS signatures and previously aggregated signatures into one
/// proof, over the union of their signer sets, all against the same
/// `(message, epoch)`.
///
/// Children and raw signatures mix freely: no children is a leaf, no raw
/// signatures is a pure recursion step, and one child plus a few signatures
/// tops up an existing aggregate. One proving job at a time per process.
pub fn aggregate(
    children: &[AggregateSignature],
    raw: Vec<(XmssPublicKey, XmssSignature)>,
    message: xmss::Message,
    epoch: u32,
    log_inv_rate: usize,
) -> Result<AggregateSignature, AggregateError> {
    aggregate_with_stats(children, raw, message, epoch, log_inv_rate).map(|(sig, _)| sig)
}

/// [`aggregate`], keeping the prover statistics the benchmark reports.
pub(crate) fn aggregate_with_stats(
    children: &[AggregateSignature],
    raw: Vec<(XmssPublicKey, XmssSignature)>,
    message: xmss::Message,
    epoch: u32,
    log_inv_rate: usize,
) -> Result<(AggregateSignature, lean_vm::cpu::Stats), AggregateError> {
    aggregate_tampered(children, raw, message, epoch, log_inv_rate, |_| {})
}

/// [`aggregate`], with a hook to corrupt the witness before proving.
///
/// The coverage argument and the claim batching are enforced entirely by guest
/// asserts over prover advice, so the only way to test them is to lie in a hint
/// and require the guest to notice. That is what `tamper` is for
/// (`aggregate_hints_bind`); with an empty hook this is the production path.
pub(crate) fn aggregate_tampered(
    children: &[AggregateSignature],
    raw: Vec<(XmssPublicKey, XmssSignature)>,
    message: xmss::Message,
    epoch: u32,
    log_inv_rate: usize,
    tamper: impl FnOnce(&mut Hints),
) -> Result<(AggregateSignature, lean_vm::cpu::Stats), AggregateError> {
    if children.len() > MAX_CHILDREN {
        return Err(AggregateError::TooLarge);
    }
    if children.iter().any(|c| c.message != message || c.epoch != epoch) {
        return Err(AggregateError::InconsistentChildren);
    }
    let guest = unified_guest();
    let mut raw = raw;
    raw.sort_by(|(a, _), (b, _)| a.cmp(b));
    raw.dedup_by(|(a, _), (b, _)| a == b);

    // Verifying a child here is not a courtesy: `gen_verify` derives the guest's
    // whole witness for it from the trace of a real verification. Its deferred
    // claim is deliberately NOT recomputed, which would cost a full pass over
    // each fixed polynomial per child: the batching sumcheck below already
    // forces every batched value to be the true evaluation, and the root
    // discharges the one claim they reduce to.
    let mut verified = Vec::with_capacity(children.len());
    let _span = tracing::info_span!("Verify children").entered();
    for child in children {
        check_signer_set(&child.public_keys).map_err(AggregateError::InvalidChild)?;
        let pi = child.public_input();
        let (summary, ops) = traced_verify(guest, &pi, &child.proof).map_err(AggregateError::InvalidChild)?;
        verified.push((pi, summary, ops));
    }

    drop(_span);

    let _span = tracing::info_span!("Build witness").entered();
    let raw_keys: Vec<XmssPublicKey> = raw.iter().map(|(pk, _)| pk.clone()).collect();
    let child_keys: Vec<&[XmssPublicKey]> = children.iter().map(|c| c.public_keys.as_slice()).collect();
    let cover = plan_coverage(&raw_keys, &child_keys)?;
    let (n_keys, n_dup) = (cover.keys.len(), cover.duplicates.len());

    let mut hints = Hints::default();
    hints.push(
        "meta",
        vec![count(n_keys), count(n_dup), count(raw.len()), count(children.len())],
    );
    let fs_seed = lean_vm::cpu::fs_seed(guest);
    hints.push("fs_seed", vec![fs_seed[0], fs_seed[1]]);
    hints.push("message", vec![val16(&message[..16]), val16(&message[16..])]);
    let tweaks = tweak_table(epoch);
    for pair in tweaks.chunks_exact(2) {
        hints.push("tweaks", vec![val16(&pair[0]), val16(&pair[1])]);
    }
    for pair in merkle_bit_cells(epoch).chunks_exact(2) {
        hints.push("merkle_bits", vec![pair[0], pair[1]]);
    }
    for pk in &cover.keys {
        hints.push("pubkeys", key_cells(pk).to_vec());
    }
    for pk in &cover.duplicates {
        hints.push("dup_pubkeys", key_cells(pk).to_vec());
    }
    for (&idx, (pk, sig)) in cover.raw_indices.iter().zip(&raw) {
        hints.push("raw_index", vec![count(idx)]);
        push_signature_hints(&mut hints, pk, sig, &message, epoch);
    }

    let mut subs = Vec::with_capacity(children.len());
    let mut carried = Vec::with_capacity(children.len());
    for (i, child) in children.iter().enumerate() {
        hints.push("child_n_keys", vec![count(child.public_keys.len())]);
        for &idx in &cover.child_indices[i] {
            hints.push("child_index", vec![count(idx)]);
        }
        hints.push("child_defer", child.defer.cells());
        let (pi, summary, ops) = &verified[i];
        let (sub_hints, defer) = gen_verify(guest, *pi, summary, ops)?;
        for (name, entry) in sub_hints {
            hints.push(&name, entry);
        }
        subs.push(defer);
        carried.push(child.defer.clone());
    }

    drop(_span);

    let defer = if children.is_empty() {
        let leaf = DeferredClaim::leaf();
        hints.push(
            "leaf_defer",
            vec![leaf.bytecode_value, leaf.matrix_a_value, leaf.matrix_b_value],
        );
        leaf
    } else {
        let _span = tracing::info_span!("Batch deferred claims").entered();
        let (agg_hints, reduced) = aggregate_deferred_claims(&subs, &carried);
        for (name, entry) in agg_hints {
            hints.push(&name, entry);
        }
        reduced
    };

    let public_input = statement_digest(n_keys, pubkeys_hash(&cover.keys), &message, epoch_hash(epoch), &defer);
    let mut program = guest.clone();
    // Every aggregate is a potential child, and the guest has no opening arm below
    // `2^MU_MIN`. A run smaller than that (a leaf of a few dozen signatures) grows
    // its SET table until it clears the floor.
    program.min_log_committed = MU_MIN;
    tamper(&mut hints);
    hints.install(&mut program);
    let (proof, stats) = prove(&program, public_input, log_inv_rate);
    Ok((
        AggregateSignature {
            message,
            epoch,
            public_keys: cover.keys,
            defer,
            proof,
        },
        stats,
    ))
}

struct OpeningShape {
    n_levels: usize,
    yr_level: usize,
    yr_log_len: usize,
    folds: Vec<usize>,
    log_message_columns: Vec<usize>,
    queries: Vec<usize>,
    tree_depths: Vec<usize>,
    positions_per_squeeze: Vec<usize>,
    squeezes: Vec<usize>,
    interleaving: Vec<usize>,
    query_grinding_bits: Vec<usize>,
    fold_grinding_bits: Vec<usize>,
    row_offsets: Vec<usize>,
    path_offsets: Vec<usize>,
    positions_offsets: Vec<usize>,
    vanish_offsets: Vec<usize>,
    fold_offsets: Vec<usize>,
    residual_fold_offsets: Vec<usize>,
    vanish_values: Vec<F192>,
    vanish_inverses: Vec<F192>,
    ood_samples: Vec<usize>,
}

/// The recursion program's placeholder map (the SHAPE-INDEPENDENT constants the
/// generic guest is compiled from), built from the inner program's STRUCTURE and
/// bytecode SIZE alone — no proof. Dummy layout sizes are fine: `rep` reads only the
/// size-independent block/coord structure and `kbc = log2(bytecode)`, so the guest
/// can be compiled BEFORE any inner proof exists. Because the map is a function of
/// the inner bytecode size alone, one compiled guest serves every shape.
fn placeholder_map(kbc: usize) -> BTreeMap<String, String> {
    // Any valid sizes drive the layout — rep depends only on structure + kbc,
    // and the layout reads a program's length, never its instructions, so a
    // stand-in of the right size is what lets the map exist before the bytecode
    // it describes does.
    let stand_in = vec![lean_vm::cpu::Op::Xor { a: 0, b: 0, c: 0 }; 1 << kbc];
    let l = lean_vm::cpu::layout(
        &stand_in,
        20,
        [1usize << 10; lean_vm::tables::N_TABLES],
        [F192::ZERO, F192::ZERO],
    );
    let sides: [&[Block]; 3] = [&l.push, &l.pull, &l.count];
    let lcrounds = flock::blake2s::K_LOG - 6;

    // ---- flattened block/coord descriptors (structural) ----
    let (mut sblk, mut bc0, mut bcn) = (vec![0usize], vec![], vec![]);
    let (mut ct, mut cval) = (vec![], vec![]);
    let (mut nclaims, mut nbcv, mut nblocks) = (0usize, 0usize, 0usize);
    // Claim dedup (mirrors leaf.rs): per coord, fresh = first (group, col,
    // kappa) occurrence gets the next pool slot; duplicates point at it.
    let mut slot_of: std::collections::HashMap<(usize, usize), usize> = Default::default();
    let (mut coord_fresh, mut coord_slot) = (vec![], vec![]);
    // A TABLE block's coordinates, flattened into terms: the guest rebuilds each as
    // `Σ_terms`, so a derived value (an XOR/MUL result, a DEREF store, a JUMP
    // successor) costs terms rather than columns. A framework coordinate has none:
    // it decomposes into pooled claims instead.
    let (mut coord_toff, mut coord_tcount) = (vec![], vec![]);
    let (mut term_type, mut term_const) = (vec![], vec![]);
    let (mut term_col_a, mut term_col_b) = (vec![], vec![]);
    // A table's blocks raise no claim any more: the table sumcheck settles them
    //, so only the framework blocks stream column values.
    let sch_pm = lean_vm::cpu::schema();
    let owner_pm: Vec<Option<usize>> = lean_vm::cpu::block_kappa_sources(kbc)
        .into_iter()
        .map(|(src, _)| src.checked_sub(2))
        .collect();
    for blocks in sides.iter() {
        for blk in blocks.iter() {
            bc0.push(ct.len());
            bcn.push(blk.coords.len());
            let owner = owner_pm[nblocks];
            nblocks += 1;
            for c in &blk.coords {
                // One COORD_FRESH/COORD_CLAIM_SLOT entry PER coord (the guest
                // indexes them by global coord offset); only a framework block's
                // Col/GCol raises a claim.
                let (mut fresh, mut slot) = (0usize, 0usize);
                if let (Coord::Col(i) | Coord::GCol(i, _), None) = (c, owner) {
                    let key = (*i, blk.kappa);
                    if let Some(&known) = slot_of.get(&key) {
                        slot = known;
                    } else {
                        slot_of.insert(key, nclaims);
                        fresh = 1;
                        slot = nclaims;
                        nclaims += 1;
                    }
                }
                coord_fresh.push(fresh);
                coord_slot.push(slot);
                // A table's coord becomes terms; a framework one has none, having
                // decomposed into the pooled claim above.
                let toff = term_type.len();
                if let Some(t) = owner {
                    push_coord_terms(
                        c,
                        sch_pm.base[t],
                        &mut term_type,
                        &mut term_const,
                        &mut term_col_a,
                        &mut term_col_b,
                    );
                }
                coord_toff.push(toff);
                coord_tcount.push(term_type.len() - toff);
                nbcv += usize::from(matches!(c, Coord::Public(_)));
                ct.push(coord_kind(c) as u128);
                cval.push(u(coord_scale(c)));
            }
        }
        sblk.push(nblocks);
    }
    let evtot: usize = lean_vm::tables::tables().iter().map(|t| t.n_committed_columns()).sum();
    let ncl = nclaims + evtot + 3; // bus + constraint + the three PI memory-limb claims

    // ---- claim descriptor buffer ids (structural) ----
    let valcols = blake2s_value_columns();
    let col_sources_pm = lean_vm::cpu::col_kappa_sources(kbc);
    let mut compact_col_pm = vec![usize::MAX; col_sources_pm.len()];
    let mut n_committed = 0usize;
    for (global, source) in col_sources_pm.iter().enumerate() {
        if source.is_some() {
            compact_col_pm[global] = n_committed;
            n_committed += 1;
        }
    }
    let qflock_compact = compact_col_pm[lean_vm::cpu::QFLOCK];
    assert_ne!(qflock_compact, usize::MAX, "QFLOCK must be committed");
    let (mut cpbuf, mut cpcol, mut cpqslot): (Vec<usize>, Vec<usize>, Vec<usize>) = (vec![], vec![], vec![]);
    // `cpbuf` codes are the guest's POINT_BUF_*: 0 zeta, 1 rho, 2 pi, 3 qflock-rho.
    walk_claims(&l, kbc, |site| match site {
        ClaimSite::Framework { column, .. } => {
            let compact = compact_col_pm[column];
            assert_ne!(compact, usize::MAX, "framework claim must target a committed column");
            cpbuf.push(0);
            cpcol.push(compact);
            cpqslot.push(0);
        }
        ClaimSite::TableColumn { column, is_virtual, .. } => {
            cpbuf.push(if is_virtual { 3 } else { 1 });
            cpcol.push(if is_virtual {
                qflock_compact
            } else {
                compact_col_pm[column]
            });
            cpqslot.push(if is_virtual {
                lean_vm::blake2s_flock::SLOTS[valcols.iter().position(|&v| v == column).unwrap()]
            } else {
                0
            });
        }
        ClaimSite::MemoryLimb { column } => {
            cpbuf.push(2);
            cpcol.push(compact_col_pm[column]);
            cpqslot.push(0);
        }
    });
    assert_eq!(cpbuf.len(), ncl, "descriptor count == pool size");
    assert_eq!(cpcol.len(), ncl, "every descriptor has a committed-column target");
    assert_eq!(cpqslot.len(), ncl, "every descriptor has a fixed QFLOCK slot");

    // ---- the placeholder map ----
    let ints = |v: &[usize]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let us = |v: &[u128]| format!("[{}]", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "));
    let flds = |v: &[F192]| {
        format!(
            "[{}]",
            v.iter().map(|&x| f192_literal(x)).collect::<Vec<_>>().join(", ")
        )
    };
    let mut rep = BTreeMap::new();
    let mut ps = |k: &str, v: String| {
        rep.insert(format!("{k}_PLACEHOLDER"), v);
    };
    ps("STREAM_CAP", STREAM_CAP.to_string());
    ps("MIN_LOG_MEM", lean_vm::cpu::MIN_LOG_MEM.to_string());
    ps("INV_GEN", u(F192::new(G.inv().0, 0, 0)).to_string());
    // The table sumcheck sends its round polynomial WHOLE, at {0, 1, g, g^2}, so
    // it interpolates a cubic: one baked inverse denominator per node.
    {
        let q = primitives::multilinear::quad_nodes();
        for i in 0..4 {
            let den = (0..4).filter(|&j| j != i).fold(F192::ONE, |acc, j| acc * (q[i] + q[j]));
            ps(&format!("LAG4_INV_{i}"), f192_literal(den.inv()));
        }
    }
    ps("MU_CAP", MU_CAP.to_string());
    ps("NO_TABLE", l.taus.len().to_string());
    ps("GKR_ROUNDS_CAP", (MU_CAP * (MU_CAP + 1) / 2 + MU_CAP + 2).to_string());
    ps("GKR_POINTS_CAP", ((MU_CAP + 1) * MU_CAP).to_string());
    ps("SIDE_BLOCK_START", ints(&sblk));
    ps("N_BLOCKS", nblocks.to_string());
    let bks = lean_vm::cpu::block_kappa_sources(kbc);
    // Push and pull emit bus blocks in matched pairs, so their baked kappa-source
    // segments are identical; the guest computes only push's side total and
    // aliases pull's mu to push's on this basis.
    assert_eq!(
        bks[sblk[0]..sblk[1]],
        bks[sblk[1]..sblk[2]],
        "push/pull kappa sources must match"
    );
    ps(
        "BLOCK_KAPPA_SRC",
        ints(&bks.iter().map(|&(s, _)| s).collect::<Vec<_>>()),
    );
    ps(
        "BLOCK_KAPPA_ADJ",
        ints(&bks.iter().map(|&(_, a)| a).collect::<Vec<_>>()),
    );
    ps(
        "BLOCK_TABLE",
        ints(
            &bks.iter()
                .map(|&(s, _)| if s >= 2 { s - 2 } else { l.taus.len() })
                .collect::<Vec<_>>(),
        ),
    );
    let mut block_side = Vec::new();
    for (s, blocks) in sides.iter().enumerate() {
        block_side.extend(std::iter::repeat_n(s, blocks.len()));
    }
    ps("BLOCK_SIDE", ints(&block_side));
    ps("BLOCK_COORD_OFF", ints(&bc0));
    ps("BLOCK_COORD_COUNT", ints(&bcn));
    ps("COORD_TYPE", us(&ct));
    ps("COORD_CONST", us(&cval));
    ps("COORD_FRESH", ints(&coord_fresh));
    ps("COORD_CLAIM_SLOT", ints(&coord_slot));
    ps("COORD_TERM_OFF", ints(&coord_toff));
    ps("COORD_TERM_COUNT", ints(&coord_tcount));
    ps("TERM_TYPE", ints(&term_type));
    ps("TERM_CONST", us(&term_const));
    ps("TERM_COL_A", ints(&term_col_a));
    ps("TERM_COL_B", ints(&term_col_b));
    ps("N_BUS_CLAIMS", nclaims.to_string());
    let idxc: Vec<u128> = (0..34)
        .map(|i| {
            let mut g2k = F192::new(G.0, 0, 0);
            for _ in 0..i {
                g2k = g2k * g2k;
            }
            u(F192::ONE + g2k)
        })
        .collect();
    ps("INDEX_MLE_FACTORS", us(&idxc));
    ps("N_CLAIMS", ncl.to_string());
    ps("N_TABLES", l.taus.len().to_string());
    // The table sumcheck's eta layout, from the native verifier's own numbers:
    // a disjoint range of identities per table, then THREE powers shared by every
    // table, one per bus side. Sharing is what lets the target be derived from the
    // three leaf claims instead of trusted (lean_vm::cpu::eta_form_base).
    let n_id: Vec<usize> = lean_vm::tables::tables().iter().map(|t| t.n_constraints()).collect();
    let form_base = lean_vm::cpu::eta_form_base();
    ps(
        "ETA_OFFSET",
        ints(&lean_vm::constraints::eta_offsets(n_id.iter().copied())),
    );
    ps("ETA_FORM_BASE", form_base.to_string());
    ps("N_ETA_POWS", (form_base + 3).to_string());
    let committed: Vec<usize> = lean_vm::tables::tables()
        .iter()
        .map(|t| t.n_committed_columns())
        .collect();
    ps("N_TABLE_COLS", ints(&committed));
    ps("TABLE_COLS_CAP", (committed.iter().max().unwrap() + 1).to_string());
    let fixed_challenges: Vec<F192> = flock::zerocheck::univariate_skip_optimized::small_challenges()
        .into_iter()
        .chain(flock::zerocheck::univariate_skip_optimized::medium_challenges())
        .collect();
    ps("FIXED_CHALLENGES", flds(&fixed_challenges));
    // Flock univariate skip: 6 skipped variables, then the fixed inner rounds.
    ps("K_SKIP", "6".to_string());
    ps("N_FIXED_CHALLENGE_ROUNDS", fixed_challenges.len().to_string());
    let phi: Vec<F192> = primitives::field::PHI_8_TABLE_192[..128].to_vec();
    ps("PHI8_NODES", flds(&phi));
    // Tower F192 = F64[Y]/(Y^3+Y+1), Y = new(0,1,0). Y_TOWER embeds Y for
    // AIR lane reassembly; Y_INV helps derive the top PI-memory limb.
    let y_tower = F192::new(0, 1, 0);
    ps("Y_TOWER", u(y_tower).to_string());
    ps("Y_INV", f192_literal(y_tower.inv()));
    // Coordinate basis e_i of F192 over F2 (spans the whole field): the 64
    // binary basis vectors in each of the three tower limbs. The guest uses
    // these vectors to reconstruct a word from its 192 coordinate bits.
    let coord_basis: Vec<F192> = (0..192)
        .map(|i| match i / 64 {
            0 => F192::new(1u64 << i, 0, 0),
            1 => F192::new(0, 1u64 << (i - 64), 0),
            2 => F192::new(0, 0, 1u64 << (i - 128)),
            _ => unreachable!(),
        })
        .collect();
    ps("COORD_BASIS", flds(&coord_basis));
    let inv_den = |nodes: &[F192], node: F192, skip: F192| {
        let mut d = F192::ONE;
        for &s in nodes {
            if s != skip {
                d *= node + s;
            }
        }
        d.inv()
    };
    let ilam: Vec<F192> = (0..64)
        .map(|i| inv_den(&phi[64..128], phi[64 + i], phi[64 + i]))
        .collect();
    let icmb: Vec<F192> = (0..64)
        .map(|i| inv_den(&phi[..128], phi[64 + i], phi[64 + i]))
        .collect();
    let isdom: Vec<F192> = (0..64).map(|i| inv_den(&phi[..64], phi[i], phi[i])).collect();
    ps("LAGRANGE_INV_LAMBDA", flds(&ilam));
    ps("LAGRANGE_INV_COMBINED", flds(&icmb));
    ps("LAGRANGE_INV_S", flds(&isdom));
    ps("LINCHECK_ROUNDS", lcrounds.to_string());
    ps("PIN_COLUMN", flock::blake2s::Z_CONST_POS.to_string());
    ps("K_LOG", flock::blake2s::K_LOG.to_string());
    // The q_flock Strided-claim slot stride is K_LOG - LOG_PACKING (= 8), so the
    // qflock point-claim slot must use THIS, not LOG2_FIELD_BITS.
    ps("SLOT_STRIDE_LOG", lean_vm::blake2s_flock::SLOT_STRIDE_LOG.to_string());

    // ---- LIG candidate tables (fixed [minm, maxm] range; open_stacked config) ----
    let oshape = |m: usize, log_inv_rate: usize| {
        let shape = whir_shape(m, log_inv_rate);
        let (vc, sh) = (&shape.config, &shape.levels);
        let (cn, cr) = (sh.levels, vc.level_steps);
        // The final message sits at the LAST level. The guest fills level_roots slot 0
        // with the commitment root and every later slot from that level's root read,
        // then checks each query's Merkle walk with a write-once store into its slot.
        // A slot no read had filled would turn that check into a write, so this
        // relation is what keeps the query phase binding.
        assert_eq!(cr, cn - 1, "the yr level must be the last one");
        let (ck, cl, cyr) = (sh.ks.clone(), sh.log_msg_cols.clone(), sh.yr_log_n);
        let cq = vc.queries.clone();
        let (cd, cp) = (&shape.depth, &shape.per_squeeze);
        let cs: Vec<usize> = (0..cn).map(|i| cq[i].div_ceil(cp[i])).collect();
        let cni: Vec<usize> = ck.iter().map(|&k| 1usize << k).collect();
        let cqb: Vec<usize> = (0..cn).map(|lvl| vc.grinding_bits[lvl]).collect();
        assert!(
            cni.iter().enumerate().all(|(lv, &n)| {
                let (bytes, whole_blocks) = if lv == 0 {
                    (8 * n, n % 8 == 0)
                } else {
                    (24 * n, (3 * n) % 8 == 0)
                };
                bytes <= 1024 && whole_blocks
            }),
            "recursive WHIR guest supports whole-block Merkle rows of at most one 1024-byte BLAKE2s chunk"
        );
        let cfgb = |lvl: usize| vc.fold_grinding_bits.get(lvl).copied().unwrap_or(0) as i64;
        let mut cfb: Vec<usize> = Vec::new();
        for (lvl, &k) in ck.iter().enumerate().take(cn) {
            for j in 0..k {
                cfb.push((cfgb(lvl) - j as i64).max(0) as usize);
            }
        }
        let psum = |f: &dyn Fn(usize) -> usize| -> Vec<usize> {
            let mut o = Vec::with_capacity(cn);
            let mut acc = 0;
            for lv in 0..cn {
                o.push(acc);
                acc += f(lv);
            }
            o
        };
        let c_rowoff = psum(&|lv| cq[lv] * cni[lv] * if lv == 0 { 1 } else { 3 });
        let c_pathoff = psum(&|lv| cq[lv] * cd[lv] * 2);
        let c_qpoff = psum(&|lv| cs[lv] * cp[lv]);
        let c_svkoff = psum(&|lv| cl[lv] + 1);
        let c_foldbase = psum(&|lv| ck[lv]);
        let c_risstart: Vec<usize> = (0..cn).map(|k| c_foldbase[k] + ck[k]).collect();
        let mut c_svk = Vec::new();
        let mut c_ivk = Vec::new();
        for &cl_lv in cl.iter().take(cn) {
            for &v in &pcs::whir::eval_sk_at_vks(cl_lv) {
                c_svk.push(F192::new(v.0, 0, 0));
                c_ivk.push(if v == F64::ZERO {
                    F192::ZERO
                } else {
                    F192::new(v.inv().0, 0, 0)
                });
            }
        }
        OpeningShape {
            n_levels: cn,
            yr_level: cr,
            yr_log_len: cyr,
            folds: ck,
            log_message_columns: cl,
            queries: cq,
            tree_depths: cd.clone(),
            positions_per_squeeze: cp.clone(),
            squeezes: cs,
            interleaving: cni,
            query_grinding_bits: cqb,
            fold_grinding_bits: cfb,
            row_offsets: c_rowoff,
            path_offsets: c_pathoff,
            positions_offsets: c_qpoff,
            vanish_offsets: c_svkoff,
            fold_offsets: c_foldbase,
            residual_fold_offsets: c_risstart,
            vanish_values: c_svk,
            vanish_inverses: c_ivk,
            ood_samples: vc.ood_samples.clone(),
        }
    };
    let (minm, maxm) = (MU_MIN, MU_MAX);
    let rates = pcs::whir::MIN_LOG_INV_RATE..=pcs::whir::MAX_LOG_INV_RATE;
    let cands: Vec<_> = rates
        .clone()
        .flat_map(|r| (minm..=maxm).map(move |m| oshape(m, r)))
        .collect();
    let maxlev = cands.iter().map(|c| c.n_levels).max().unwrap();
    let maxfolds = cands.iter().map(|c| c.fold_grinding_bits.len()).max().unwrap();
    let maxsvk = cands.iter().map(|c| c.vanish_values.len()).max().unwrap();
    let maxood = cands.iter().flat_map(|c| &c.ood_samples).copied().max().unwrap_or(0);
    ps("LIG_MAX_LEVELS", maxlev.to_string());
    ps("LIG_MAX_TOTAL_FOLDS", maxfolds.to_string());
    ps("LIG_MAX_VANISH_LEN", maxsvk.to_string());
    ps("LIG_MAX_OOD_SAMPLES", maxood.to_string());
    ps("LIG_MIN_LOG_SIZE", minm.to_string());
    let cks: Vec<(usize, usize)> = lean_vm::cpu::col_kappa_sources(kbc).into_iter().flatten().collect();
    ps("N_COMMITTED_COLS", cks.len().to_string());
    ps("COL_KAPPA_SRC", ints(&cks.iter().map(|&(s, _)| s).collect::<Vec<_>>()));
    ps("COL_KAPPA_ADJ", ints(&cks.iter().map(|&(_, a)| a).collect::<Vec<_>>()));
    ps("PCS_MIN_MU", lean_vm::pcs::MIN_MU.to_string());
    ps(
        "LIG_LOG_MSG_COLS_CAP",
        cands
            .iter()
            .map(|c| *c.log_message_columns.iter().max().unwrap())
            .max()
            .unwrap()
            .to_string(),
    );
    ps(
        "YR_LOG_CAP",
        cands.iter().map(|c| c.yr_log_len).max().unwrap().to_string(),
    );
    {
        let pad = |v: &[usize], stride: usize| -> Vec<usize> {
            let mut o = v.to_vec();
            o.resize(stride, 0);
            o
        };
        let flat = |f: &dyn Fn(&OpeningShape) -> Vec<usize>, stride: usize| -> Vec<usize> {
            cands.iter().flat_map(|c| pad(&f(c), stride)).collect()
        };
        let scal = |f: &dyn Fn(&OpeningShape) -> usize| -> Vec<usize> { cands.iter().map(f).collect() };
        ps("LIG_N_LEVELS", ints(&scal(&|c| c.n_levels)));
        ps("LIG_YR_LEVEL", ints(&scal(&|c| c.yr_level)));
        ps("LIG_YR_LOG_LEN", ints(&scal(&|c| c.yr_log_len)));
        ps("LIG_YR_LEN", ints(&scal(&|c| 1usize << c.yr_log_len)));
        ps("LIG_TOTAL_FOLDS", ints(&scal(&|c| c.folds.iter().sum())));
        ps("LIG_MAX_QUERIES", ints(&scal(&|c| *c.queries.iter().max().unwrap())));
        ps("LIG_MAX_SQUEEZES", ints(&scal(&|c| *c.squeezes.iter().max().unwrap())));
        ps(
            "LIG_MAX_INTERLEAVE",
            ints(&scal(&|c| *c.interleaving.iter().max().unwrap())),
        );
        // StackBuf cap for the packed leaf row AND the raw-limb `lanes` scratch
        // that shares it (`open_stacked`). Level 0 packs 2 base-field lanes per
        // cell (n/2 cells). Deeper levels first load 3 raw tower limbs per word
        // into `lanes` (3n cells), then pack them into the 3n/2-cell leaf row,
        // so `lanes` (3n) is the binding size there. Sizing the deeper term at
        // 3n/2 happened to hold only while L0's n/2 dominated (small folds);
        // it under-provisions once a deeper interleave exceeds L0's.
        let packed_cells = |c: &Vec<usize>| -> usize {
            c.iter()
                .enumerate()
                .map(|(lv, &n)| if lv == 0 { n / 2 } else { 3 * n })
                .max()
                .unwrap()
        };
        ps(
            "LIG_PACKED_ROW_CAP",
            cands
                .iter()
                .map(|c| packed_cells(&c.interleaving))
                .max()
                .unwrap()
                .to_string(),
        );
        ps(
            "LIG_POSITIONS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.squeezes[level] * c.positions_per_squeeze[level])
                    .sum()
            })),
        );
        ps(
            "LIG_ROWS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.queries[level] * c.interleaving[level] * if level == 0 { 1 } else { 3 })
                    .sum()
            })),
        );
        ps(
            "LIG_PATHS_LEN",
            ints(&scal(&|c| {
                (0..c.n_levels)
                    .map(|level| c.queries[level] * c.tree_depths[level] * 2)
                    .sum()
            })),
        );
        ps(
            "LIG_QUERY_GRIND_BITS",
            ints(&flat(&|c| c.query_grinding_bits.clone(), maxlev)),
        );
        ps(
            "LIG_OOD_SAMPLES",
            ints(
                &cands
                    .iter()
                    .flat_map(|shape| pad(&shape.ood_samples, maxlev))
                    .collect::<Vec<_>>(),
            ),
        );
        ps("LIG_QUERIES", ints(&flat(&|c| c.queries.clone(), maxlev)));
        ps("LIG_FOLDS", ints(&flat(&|c| c.folds.clone(), maxlev)));
        ps("LIG_INTERLEAVE", ints(&flat(&|c| c.interleaving.clone(), maxlev)));
        ps(
            "LIG_LEAF_PAIRS",
            ints(&flat(
                &|c| {
                    c.interleaving
                        .iter()
                        .enumerate()
                        .map(|(lv, &n)| if lv == 0 { n / 4 } else { 3 * n / 4 })
                        .collect()
                },
                maxlev,
            )),
        );
        // 64-byte BLAKE2s blocks per leaf row: level 0's committed rows are
        // base-field F64 (8 bytes/lane); deeper levels are native F192
        // (24 bytes/word, received as three embedded K limbs each). Rows are
        // whole blocks only (asserted at candidate construction).
        ps(
            "LIG_LEAF_BLOCKS",
            ints(&flat(
                &|c| {
                    c.interleaving
                        .iter()
                        .enumerate()
                        .map(|(lv, &n)| if lv == 0 { n / 8 } else { 3 * n / 8 })
                        .collect()
                },
                maxlev,
            )),
        );
        ps("LIG_TREE_DEPTH", ints(&flat(&|c| c.tree_depths.clone(), maxlev)));
        ps("LIG_SQUEEZES", ints(&flat(&|c| c.squeezes.clone(), maxlev)));
        ps(
            "LIG_POSITIONS_OFF",
            ints(&flat(&|c| c.positions_offsets.clone(), maxlev)),
        );
        ps(
            "LIG_LOG_MSG_COLS",
            ints(&flat(&|c| c.log_message_columns.clone(), maxlev)),
        );
        ps(
            "LIG_RESIDUAL_FOLD_OFF",
            ints(&flat(&|c| c.residual_fold_offsets.clone(), maxlev)),
        );
        ps(
            "LIG_RESIDUAL_PREFIX_LEN",
            ints(&flat(
                &|c| {
                    c.log_message_columns
                        .iter()
                        .map(|&columns| columns - c.yr_log_len)
                        .collect()
                },
                maxlev,
            )),
        );
        ps("LIG_FOLDS_OFF", ints(&flat(&|c| c.fold_offsets.clone(), maxlev)));
        ps("LIG_ROWS_OFF", ints(&flat(&|c| c.row_offsets.clone(), maxlev)));
        ps("LIG_PATHS_OFF", ints(&flat(&|c| c.path_offsets.clone(), maxlev)));
        ps("LIG_VANISH_OFF", ints(&flat(&|c| c.vanish_offsets.clone(), maxlev)));
        ps(
            "LIG_FOLD_GRIND_BITS",
            ints(&flat(&|c| c.fold_grinding_bits.clone(), maxfolds)),
        );
        let mut svk2 = Vec::new();
        let mut ivk2 = Vec::new();
        for c in &cands {
            let mut s = c.vanish_values.clone();
            let mut iv = c.vanish_inverses.clone();
            s.resize(maxsvk, F192::ZERO);
            iv.resize(maxsvk, F192::ZERO);
            svk2.extend(s);
            ivk2.extend(iv);
        }
        ps("LIG_VANISH_VALS", flds(&svk2));
        ps("LIG_VANISH_INVS", flds(&ivk2));
    }
    let n_log_sizes = maxm - minm + 1;
    let n_rates = pcs::whir::MAX_LOG_INV_RATE - pcs::whir::MIN_LOG_INV_RATE + 1;
    ps("LIG_N_LOG_SIZES", n_log_sizes.to_string());
    ps("LIG_N_RATES", n_rates.to_string());
    ps("LIG_N_CANDIDATES", (n_log_sizes * n_rates).to_string());
    ps("LIG_MIN_SHIFT_INV", u(F192::new(g_pow(minm).inv().0, 0, 0)).to_string());
    ps("CLAIM_POINT_BUF", ints(&cpbuf));
    ps("CLAIM_COMMITTED_COL", ints(&cpcol));
    let slot_stride_log = lean_vm::blake2s_flock::SLOT_STRIDE_LOG;
    let cpqbits: Vec<usize> = cpqslot
        .iter()
        .flat_map(|&slot| (0..slot_stride_log).map(move |k| (slot >> k) & 1))
        .collect();
    ps("CLAIM_QFLOCK_SLOT_BITS", ints(&cpqbits));
    ps("QFLOCK_COMMITTED_COL", qflock_compact.to_string());
    ps("QFLOCK_VARS_CAP", (33 + slot_stride_log).to_string());
    ps("BYTECODE_LOG", kbc.to_string());
    // The stacked bytecode: nbcv/2 encoding columns per side, aligned with the bus
    // tuple, so their slots span the fingerprint's own bits. The defer region is
    // 2*kbc points + sel bits + 2 reduced + alpha + z_skip + 2*lcrounds rounds
    // + 64 z_partial + 1 matpart.
    let bc_cols = nbcv / 2;
    let log2_bc_cols = lean_vm::leaf::N_TUPLE_BITS;
    ps("BYTECODE_COLS", bc_cols.to_string());
    ps("LOG2_BYTECODE_COLS", log2_bc_cols.to_string());
    ps("DEFER_SIZE", (kbc + log2_bc_cols + 2 * lcrounds + 68).to_string());
    ps("BYTECODE_VARS", (kbc + log2_bc_cols).to_string());
    let label_state = pack_state(Sponge::new(b"leanvm-b", &[]).state());
    ps("TRANSCRIPT_SEED_0", u(label_state[0]).to_string());
    ps("TRANSCRIPT_SEED_1", u(label_state[1]).to_string());
    let agg_state = pack_state(Sponge::new(RECURSION_AGG_LABEL, &[]).state());
    ps("AGG_SEED_0", u(agg_state[0]).to_string());
    ps("AGG_SEED_1", u(agg_state[1]).to_string());
    let statement_state = pack_state(Sponge::new(RECURSION_STATEMENT_LABEL, &[]).state());
    ps("STATEMENT_SEED_0", u(statement_state[0]).to_string());
    ps("STATEMENT_SEED_1", u(statement_state[1]).to_string());
    let epoch_iv = chain_iv(EPOCH_LABEL);
    ps("EPOCH_IV_0", u(epoch_iv[0]).to_string());
    ps("EPOCH_IV_1", u(epoch_iv[1]).to_string());
    let pk_iv = chain_iv(PUBKEYS_LABEL);
    ps("PK_IV_0", u(pk_iv[0]).to_string());
    ps("PK_IV_1", u(pk_iv[1]).to_string());

    // The XMSS instance, from which the guest derives every table width by
    // compile-time integer arithmetic.
    ps("V", xmss::V.to_string());
    ps("W", xmss::W.to_string());
    ps("TARGET_SUM", xmss::TARGET_SUM.to_string());
    ps("LOG_LIFETIME", xmss::LOG_LIFETIME.to_string());
    ps("MAX_KEYS", MAX_KEYS.to_string());
    ps("MAX_CHILDREN", MAX_CHILDREN.to_string());
    rep
}

/// The aggregation bytecode, compiled to a fixed point on its own size.
///
/// The recursion placeholders are a function of the inner bytecode's log size,
/// and here the inner bytecode is this one, so the size has to agree with
/// itself. Its *digest* needs no such loop: it rides the statement rather than
/// the code. The guess converges in one or two rounds because the map's only
/// size-dependent part is a handful of unrolled sumcheck rounds.
pub fn unified_guest() -> &'static Program {
    static GUEST: std::sync::OnceLock<Program> = std::sync::OnceLock::new();
    GUEST.get_or_init(|| {
        let mut guess = 20;
        for _ in 0..8 {
            let guest = compile_guest(guess);
            let actual = guest.prog.len().trailing_zeros() as usize;
            if actual == guess {
                return guest;
            }
            guess = actual;
        }
        panic!("the aggregation bytecode's self-referential compile did not converge");
    })
}

fn compile_guest(kbc: usize) -> Program {
    let replacements = placeholder_map(kbc);
    // `DBG_PLACEHOLDERS=path`: dump the baked guest constants, to read alongside
    // a `DBG_PROF_DUMP` profile (the guest's shape is entirely in these).
    if let Ok(path) = std::env::var("DBG_PLACEHOLDERS") {
        let dump: String = replacements.iter().map(|(k, v)| format!("{k} = {v}\n")).collect();
        std::fs::write(&path, dump).expect("write DBG_PLACEHOLDERS");
    }
    let guest = compile(
        &parse_with_replacements(include_str!("../guests/aggregate.py"), &replacements)
            .expect("the repository aggregation guest must parse"),
    );
    // `DBG_DISASM=path`: dump the guest's disassembly, to read alongside a
    // `DBG_PROF_DUMP` per-pc profile. Function boundaries lead the dump, so the
    // pc a failed guest check reports can be resolved to a source function
    // without re-deriving the layout by hand.
    if let Ok(path) = std::env::var("DBG_DISASM") {
        let mut ranges: Vec<_> = guest.fn_ranges.iter().collect();
        ranges.sort_by_key(|(_, entry, _)| *entry);
        let mut dump = String::new();
        for (name, entry, len) in ranges {
            dump += &format!("# fn {entry:>7}..{:<7} {name}\n", entry + len);
        }
        dump += &lean_compiler::disassemble(&guest.prog);
        std::fs::write(&path, dump).expect("write DBG_DISASM");
    }
    guest
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::signers_cache::{EPOCH, get_signers, message};

    /// Small enough that the leaf's committed witness needs padding up to the
    /// floor, which is the case the fill has to handle.
    const LEAF: usize = 6;

    /// The smallest possible aggregate. A single signature is far below the
    /// committed floor, so this is the case where the fill has to do the most
    /// work, and where a growth schedule that only approaches the floor
    /// geometrically runs out of rounds.
    #[test]
    fn aggregate_one_signer() {
        lean_vm::init_prover_pool();
        let agg = aggregate(&[], get_signers(1), message(), EPOCH, lean_vm::pcs::LOG_INV_RATE).expect("aggregates");
        agg.verify().expect("verifies");
        agg.verify_against(&message(), EPOCH)
            .expect("verifies against its statement");
        assert_eq!(
            agg.verify_against(&message(), EPOCH + 1),
            Err(VerifyError::UnexpectedStatement)
        );
    }

    /// A leaf: raw signatures only, no children. Exercises the whole node
    /// machinery except recursion, so it is the fast check that the statement,
    /// the epoch binding, the signer-set digest and the coverage argument agree
    /// between the guest and this file.
    #[test]
    fn aggregate_leaf() {
        lean_vm::init_prover_pool();
        let raw = get_signers(3);
        let agg = aggregate(&[], raw, message(), EPOCH, lean_vm::pcs::LOG_INV_RATE).expect("leaf aggregates");
        agg.verify().expect("leaf verifies");
        assert_eq!(agg.public_keys.len(), 3);
    }

    /// Two leaves into one node: the real recursion step. The node rebuilds each
    /// child's statement from indices into its own signer table, verifies both
    /// proofs in-circuit, and batches four bytecode claims and six matrix claims
    /// into the one pair it defers.
    ///
    /// The two leaves are deliberately different sizes, so one is padded up to the
    /// committed floor and the other reaches it on its own: the node then
    /// dispatches a different opening arm per child.
    #[test]
    fn aggregate_two_to_one() {
        lean_vm::init_prover_pool();
        let rate = lean_vm::pcs::LOG_INV_RATE;
        let signers = get_signers(LEAF + 60);
        let left = aggregate(&[], signers[..LEAF].to_vec(), message(), EPOCH, rate).expect("left leaf");
        let right = aggregate(&[], signers[LEAF..].to_vec(), message(), EPOCH, rate).expect("right leaf");
        let node = aggregate(&[left, right], vec![], message(), EPOCH, rate).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(node.public_keys.len(), LEAF + 60);
    }

    /// Overlapping committees, which is the case recursion exists for: the two
    /// leaves share signers, so the union is smaller than the sum and the
    /// repeats land in duplicate coverage slots.
    #[test]
    fn aggregate_overlapping_signers() {
        lean_vm::init_prover_pool();
        let rate = lean_vm::pcs::LOG_INV_RATE;
        // 25 + 25 signers sharing 10, so ten repeats take duplicate slots.
        let signers = get_signers(40);
        let left = aggregate(&[], signers[..25].to_vec(), message(), EPOCH, rate).expect("left leaf");
        let right = aggregate(&[], signers[15..].to_vec(), message(), EPOCH, rate).expect("right leaf");
        let node = aggregate(&[left, right], vec![], message(), EPOCH, rate).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(node.public_keys.len(), 40, "the union, not the sum");
        assert!(node.public_keys.windows(2).all(|w| w[0] < w[1]));
    }

    /// A node of nodes, plus raw signatures joining at the top: proofs whose
    /// children are themselves recursive, so the root batches claims that were
    /// already batched once. Slow enough to keep out of the default run.
    #[test]
    #[ignore]
    fn aggregate_three_levels() {
        lean_vm::init_prover_pool();
        let rate = lean_vm::pcs::LOG_INV_RATE;
        let signers = get_signers(4 * LEAF + 2);
        let leaf = |k: usize| {
            aggregate(&[], signers[k * LEAF..(k + 1) * LEAF].to_vec(), message(), EPOCH, rate).expect("leaf")
        };
        let left = aggregate(&[leaf(0), leaf(1)], vec![], message(), EPOCH, rate).expect("left node");
        let right = aggregate(&[leaf(2), leaf(3)], vec![], message(), EPOCH, rate).expect("right node");
        let extra = signers[4 * LEAF..].to_vec();
        let root = aggregate(&[left, right], extra, message(), EPOCH, rate).expect("root aggregates");
        root.verify().expect("root verifies");
        assert_eq!(root.public_keys.len(), 4 * LEAF + 2);
    }

    /// The statement binds everything an aggregate claims. Each tamper below
    /// changes one field of an honest node and must stop it verifying; the
    /// signer set and the deferred points are the interesting ones, being the
    /// only parts a receiver reads rather than derives.
    #[test]
    #[ignore]
    fn aggregate_statement_binds() {
        lean_vm::init_prover_pool();
        let rate = lean_vm::pcs::LOG_INV_RATE;
        let signers = get_signers(2 * LEAF);
        let left = aggregate(&[], signers[..LEAF].to_vec(), message(), EPOCH, rate).expect("left leaf");
        let right = aggregate(&[], signers[LEAF..].to_vec(), message(), EPOCH, rate).expect("right leaf");
        let node = aggregate(&[left, right], vec![], message(), EPOCH, rate).expect("node");
        node.verify().expect("the honest node verifies");

        assert_eq!(
            AggregateSignature::from_bytes(&node.to_bytes())
                .expect("round trip")
                .to_bytes(),
            node.to_bytes(),
            "the wire format round-trips, recomputed claim values included"
        );
        let without =
            AggregateSignature::from_bytes_without_pubkeys(&node.to_bytes_without_pubkeys(), node.public_keys.clone())
                .expect("round trip");
        without.verify().expect("a caller-supplied signer set verifies");

        let tampered = |f: &dyn Fn(&mut AggregateSignature)| {
            let mut bad = node.clone();
            f(&mut bad);
            assert!(bad.verify().is_err(), "a tampered aggregate must not verify");
        };
        tampered(&|s| s.public_keys[0] = s.public_keys[1].clone()); // duplicate: unsorted
        tampered(&|s| {
            s.public_keys.swap(0, 1);
        });
        tampered(&|s| {
            s.public_keys.pop();
        });
        tampered(&|s| s.epoch += 1);
        tampered(&|s| s.message[0] ^= 1);
        tampered(&|s| s.defer.bytecode_point[0] += F192::ONE);
        tampered(&|s| s.defer.matrix_point[0] += F192::ONE);
        // A signer set the aggregate never covered, of the right length.
        tampered(&|s| s.public_keys[0] = get_signers(2 * LEAF + 1)[2 * LEAF].0.clone());
    }

    /// The all-zeros fast path in `DeferredClaim::recompute` must agree with the
    /// two full passes it replaces, or every leaf would verify against the wrong
    /// statement.
    #[test]
    fn leaf_claim_matches_the_general_path() {
        let klog = flock::blake2s::K_LOG;
        let leaf = DeferredClaim::leaf();
        let general = {
            let bytecode_value = mle_eval(stacked_bytecode(), &leaf.bytecode_point);
            let eq_r = pcs::whir::build_eq_table_ext(&leaf.matrix_point[..klog]);
            let eq_c = pcs::whir::build_eq_table_ext(&leaf.matrix_point[klog..]);
            let (a, b) = flock::blake2s::bilinear_walk_pair(&eq_r, &eq_c);
            (bytecode_value, a, b)
        };
        assert_eq!((leaf.bytecode_value, leaf.matrix_a_value, leaf.matrix_b_value), general);
    }

    /// A named corruption of one hint stream.
    type Tamper<'a> = (&'a str, &'a dyn Fn(&mut Hints));

    /// The witness binds. Everything the coverage argument and the claim
    /// batching rest on is a guest assert over prover advice, so the only way to
    /// test them is to lie in a hint and require the guest to notice. Each
    /// tamper below must stop the aggregate existing or stop it verifying.
    ///
    /// This is the descendant of the deleted `recursion_soundness_binds`, and it
    /// is the test that covers the coverage bijection, the runtime-bounded index
    /// range check, and the new `rs_nover` and carried-claim hints.
    #[test]
    #[ignore]
    fn aggregate_hints_bind() {
        lean_vm::init_prover_pool();
        let rate = lean_vm::pcs::LOG_INV_RATE;
        let signers = get_signers(2 * LEAF);
        let (msg, ep) = (message(), EPOCH);

        let rejects = |children: &[AggregateSignature],
                       raw: Vec<(XmssPublicKey, XmssSignature)>,
                       what: &str,
                       tamper: &dyn Fn(&mut Hints)| {
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                aggregate_tampered(children, raw, msg, ep, rate, |h| tamper(h)).map(|(sig, _)| sig.verify().is_ok())
            }));
            assert!(!matches!(outcome, Ok(Ok(true))), "tampering {what} must be rejected");
        };

        // ---- a leaf: coverage, the signer table, and the leaf's own claim ----
        let raw = signers[..LEAF].to_vec();
        aggregate(&[], raw.clone(), msg, ep, rate).expect("the honest leaf aggregates");
        let leaf_cases: &[Tamper] = &[
            // Two signatures covering one slot: write-once sees two different
            // counter values at one address.
            ("raw_index (duplicate slot)", &|h: &mut Hints| {
                let e = h.entries("raw_index");
                e[1] = e[0].clone();
            }),
            // An index past the declared set, which only the runtime-bounded
            // range check stops.
            ("raw_index (out of range)", &|h: &mut Hints| {
                h.entries("raw_index")[0] = vec![count(LEAF)];
            }),
            ("meta (n_keys inflated)", &|h: &mut Hints| {
                h.entries("meta")[0][0] = count(LEAF + 1);
            }),
            ("meta (n_raw understated)", &|h: &mut Hints| {
                h.entries("meta")[0][2] = count(LEAF - 1);
            }),
            ("meta (a spurious duplicate slot)", &|h: &mut Hints| {
                h.entries("meta")[0][1] = count(1);
            }),
            ("pubkeys (a key nobody signed for)", &|h: &mut Hints| {
                h.entries("pubkeys")[0][0] += F192::ONE;
            }),
            ("fs_seed", &|h: &mut Hints| {
                h.entries("fs_seed")[0][0] += F192::ONE;
            }),
            ("leaf_defer", &|h: &mut Hints| {
                h.entries("leaf_defer")[0][0] += F192::ONE;
            }),
            ("tweaks (an epoch the verifier did not ask for)", &|h: &mut Hints| {
                h.entries("tweaks")[0][0] += F192::ONE;
            }),
        ];
        for (what, tamper) in leaf_cases {
            rejects(&[], raw.clone(), what, *tamper);
        }

        // ---- a node: the child statements, the batching, and rs_nover ----
        let left = aggregate(&[], signers[..LEAF].to_vec(), msg, ep, rate).expect("left leaf");
        let right = aggregate(&[], signers[LEAF..].to_vec(), msg, ep, rate).expect("right leaf");
        let children = vec![left, right];
        aggregate(&children, vec![], msg, ep, rate).expect("the honest node aggregates");
        let node_cases: &[Tamper] = &[
            ("child_index (duplicate slot)", &|h: &mut Hints| {
                let e = h.entries("child_index");
                e[1] = e[0].clone();
            }),
            ("child_index (out of range)", &|h: &mut Hints| {
                h.entries("child_index")[0] = vec![count(2 * LEAF)];
            }),
            ("child_n_keys", &|h: &mut Hints| {
                h.entries("child_n_keys")[0][0] = count(LEAF - 1);
            }),
            ("child_defer (a forged carried claim)", &|h: &mut Hints| {
                h.entries("child_defer")[0][0] += F192::ONE;
            }),
            ("bc_star_hint", &|h: &mut Hints| {
                h.entries("bc_star_hint")[0][0] += F192::ONE;
            }),
            ("mat_stars_hint", &|h: &mut Hints| {
                h.entries("mat_stars_hint")[0][0] += F192::ONE;
            }),
            ("rs_nover", &|h: &mut Hints| {
                h.entries("rs_nover")[0][0] *= F192::from(primitives::field::G);
            }),
        ];
        for (what, tamper) in node_cases {
            rejects(&children, vec![], what, *tamper);
        }
    }

    /// A signature that does not match its public key cannot be aggregated: the
    /// guest's Merkle-root equality fails during witness generation, which is
    /// how a failed guest assert surfaces.
    #[test]
    #[ignore]
    fn aggregate_rejects_a_bad_signature() {
        lean_vm::init_prover_pool();
        let mut raw = get_signers(3);
        raw[1].1.wots_signature.chain_tips[0][0] ^= 1;
        let built = std::panic::catch_unwind(|| {
            aggregate(&[], raw, message(), EPOCH, lean_vm::pcs::LOG_INV_RATE).map(|s| s.verify().is_ok())
        });
        assert!(
            !matches!(built, Ok(Ok(true))),
            "a forged signature must not produce a verifying aggregate"
        );
    }
}
