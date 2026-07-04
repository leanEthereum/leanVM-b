//! The bus: a single shared channel balanced by a grand product (§4.2–§4.4).
//!
//! Each interaction wires a table's columns into width-`m` tuples and flushes
//! them in a direction (`push`/`pull`). The bus balances when the pushed and
//! pulled tuples form the same multiset, proven by two GKR product passes over
//! the leaf vectors `γ − π_α(σ)` (one per side). Each pass reduces to a single
//! leaf claim `Ṽ₀(ζ)`, which we decompose — block by block, coordinate by
//! coordinate — into evaluation claims on the committed columns (settled against
//! the witness commitment by `crate::pcs`).
//!
//! Coordinates are field elements: a public constant, a committed column, the
//! `g`-multiple of a committed column (the free increment `g·x`), or the index
//! column `g^z` (§5.3). There is no materialization.

use crate::PAR_THRESHOLD;
use crate::field::{F128, G, index_mle};
use crate::gkr;
use crate::multilinear::{eq_eval, mle_eval};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::Column;
use rayon::prelude::*;

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, the seed count `1`).
    Const(F128),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The free increment `g · col[z]` (a virtual column, §1).
    GCol(usize),
    /// The index column `g^z` (§5.3): MLE `∏_k(1+ζ_k(1+g^{2^k}))`, free.
    Index,
    /// A public column (the bytecode program, §8): not committed; both parties
    /// form its MLE directly, so it raises no claim.
    Public(Vec<F128>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. `real` is the
/// number of meaningful rows; the remaining `2^kappa - real` are padding rows,
/// every column zero but the read counts (which are `g^0 = 1`, §e2e-pad). A
/// padding row's tuple is therefore a fixed default the verifier divides out of
/// the bus product (\S sec:gp).
#[derive(Clone, Debug)]
pub struct Block {
    pub kappa: usize,
    pub coords: Vec<Coord>,
    pub real: usize,
}

/// Placement of each block in the stacked leaf vector (input order).
#[derive(Clone, Debug)]
pub struct Layout {
    pub mu: usize,
    pub offsets: Vec<usize>,
}

/// An evaluation claim on a committed column, settled against the witness.
/// Reconstructed identically by prover and verifier (its value rides the
/// transcript stream), so it is not itself part of the proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F128>,
    pub value: F128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Unbalanced,
    /// A read count is zero, so a read self-cancels on the bus (the count product
    /// has a zero factor). See `Coord::GCol` and §sec:memchan.
    ZeroCount,
    Gkr(gkr::GkrError),
    Decomposition {
        side: &'static str,
    },
    /// The bus grinding nonce (before the multiset challenge γ) failed its PoW.
    PowFailed,
}

/// Proof-of-work bits to grind before the multiset challenge γ, so the bus
/// grand-product phase clears [`crate::SECURITY_BITS`]. Two Schwartz–Zippel
/// failure events share this randomness; union-bound over them:
///
/// - the push/pull **balance** `push_root · d_pull = pull_root · d_push` — one
///   identity in γ whose difference has degree `max(push factors, pull
///   factors)` (the larger of the two sides; within a side the default-padding
///   factors are a single high-multiplicity root, so it is `max` not sum);
/// - the **count** channel `count_root ≠ 0` — a *separate* grand product of
///   `count factors`.
///
/// So `N = max(2^push_mu, 2^pull_mu) + 2^count_mu`, and a false phase passes a
/// random challenge with probability ≤ `N / 2^128`, i.e. `128 − log2(N)` bits.
/// Grinding adds that many bits back (the prover must redo the PoW to re-roll
/// γ), so we grind the deficit up to the target.
///
/// The fingerprint challenge α needs no grind: forging a fingerprint collision
/// (its `~N·w / 2^128` error) requires a fresh commitment to re-roll α, whose
/// `≥ 2^MIN_MU` Merkle-hash cost already exceeds the target for every witness
/// size we admit (`MIN_MU = 15`).
fn grand_product_grinding_bits(push: &Layout, pull: &Layout, count: &Layout) -> u32 {
    let n = (1usize << push.mu).max(1usize << pull.mu) + (1usize << count.mu);
    let ceil_log2_n = crate::log2_ceil_usize(n) as u32;
    (crate::SECURITY_BITS + ceil_log2_n).saturating_sub(128)
}

/// Stack blocks largest-first at aligned offsets; `μ = ⌈log2 Σ 2^{κ_b}⌉`.
pub fn layout(blocks: &[Block]) -> Layout {
    let n = blocks.len();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| blocks[b].kappa.cmp(&blocks[a].kappa).then(a.cmp(&b)));
    let mut offsets = vec![0usize; n];
    let mut off = 0usize;
    for &i in &order {
        offsets[i] = off;
        off += 1 << blocks[i].kappa;
    }
    let mu = crate::log2_ceil_usize(off.max(1));
    Layout { mu, offsets }
}

/// A non-constant coordinate as `(source, coefficient)`: its contribution to a
/// leaf is `coeff · source(z)`. `GCol` folds the `g` factor into the coefficient.
enum Term<'a> {
    Col(usize, F128),
    Index(F128),
    Public(&'a [F128], F128),
}

/// Build one side's leaf vector: block `b` row `z` holds `γ − Σ_i α^i c_i(z)`,
/// padded to `2^μ` with the identity `1`.
///
/// The `α`-power chain and the constant coordinates are row-invariant, so they
/// are folded once per block into `const_part`; the per-row loop then costs one
/// multiply-add per *non-constant* coordinate (no per-row `α` chain, no per-row
/// handling of separators / seed counts).
pub fn build_leaves(blocks: &[Block], lay: &Layout, cols: &[Column], alpha: F128, gamma: F128) -> Vec<F128> {
    let mut leaves = vec![F128::ONE; 1usize << lay.mu];
    // Precompute the index column g^z so the `Index` coordinate is an O(1) lookup
    // instead of an O(log z) power.
    let maxk = blocks.iter().map(|b| b.kappa).max().unwrap_or(0);
    let gpow = crate::field::g_powers(1usize << maxk);
    for (b, blk) in blocks.iter().enumerate() {
        let mut const_part = gamma;
        let mut terms: Vec<Term> = Vec::with_capacity(blk.coords.len());
        let mut alpha_pow = F128::ONE;
        for c in &blk.coords {
            match c {
                Coord::Const(v) => const_part += alpha_pow * *v,
                Coord::Col(i) => terms.push(Term::Col(*i, alpha_pow)),
                Coord::GCol(i) => terms.push(Term::Col(*i, alpha_pow * G)),
                Coord::Index => terms.push(Term::Index(alpha_pow)),
                Coord::Public(vals) => terms.push(Term::Public(vals, alpha_pow)),
            }
            alpha_pow *= alpha;
        }
        let row = |z: usize| -> F128 {
            let mut acc = const_part;
            for t in &terms {
                acc += match t {
                    Term::Col(i, c) => *c * cols[*i][z],
                    Term::Index(c) => *c * gpow[z],
                    Term::Public(vals, c) => *c * vals[z],
                };
            }
            acc
        };
        let off = lay.offsets[b];
        let rows = 1usize << blk.kappa;
        let dst = &mut leaves[off..off + rows];
        if rows >= PAR_THRESHOLD {
            dst.par_iter_mut().enumerate().for_each(|(z, slot)| *slot = row(z));
        } else {
            for (z, slot) in dst.iter_mut().enumerate() {
                *slot = row(z);
            }
        }
    }
    leaves
}

/// Recompute `Ṽ₀(ζ)` from the block structure, taking each committed column's
/// value at `ζ_lo` from `col_val` (in block/coord order). The prover passes a
/// closure reading the real columns; the verifier one replaying PCS-certified
/// values.
pub fn decompose_formula<F: FnMut(usize, &[F128]) -> F128>(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F128],
    alpha: F128,
    gamma: F128,
    mut col_val: F,
) -> F128 {
    assert_eq!(zeta.len(), lay.mu);
    let mut acc = F128::ZERO;
    let mut sel_sum = F128::ZERO;
    for (b, blk) in blocks.iter().enumerate() {
        let kappa = blk.kappa;
        let zeta_lo = &zeta[..kappa];
        let zeta_hi = &zeta[kappa..];
        let sel = lay.offsets[b] >> kappa;
        let sel_bits: Vec<F128> = (0..(lay.mu - kappa))
            .map(|k| F128::new(((sel >> k) & 1) as u64, 0))
            .collect();
        let eq_hi = eq_eval(&sel_bits, zeta_hi);
        sel_sum += eq_hi;

        let mut inner = F128::ZERO;
        let mut alpha_pow = F128::ONE;
        for c in &blk.coords {
            let coord_val = match c {
                Coord::Const(v) => *v,
                Coord::Index => index_mle(zeta_lo),
                Coord::Col(i) => col_val(*i, zeta_lo),
                Coord::GCol(i) => G * col_val(*i, zeta_lo),
                Coord::Public(vals) => mle_eval(vals, zeta_lo),
            };
            inner += alpha_pow * coord_val;
            alpha_pow *= alpha;
        }
        acc += eq_hi * (gamma + inner);
    }
    acc + (F128::ONE + sel_sum)
}

/// The number of committed coordinates (`Col`/`GCol`) in a side — i.e. how many
/// claim values flow through the transcript for it.
fn n_committed(blocks: &[Block]) -> usize {
    blocks
        .iter()
        .flat_map(|b| &b.coords)
        .filter(|c| matches!(c, Coord::Col(_) | Coord::GCol(_)))
        .count()
}

/// Prover-side decomposition: reads the real columns, writing each committed
/// value into the stream and recording the matching claim (block/coord order).
fn decompose_prove(
    blocks: &[Block],
    lay: &Layout,
    cols: &[Column],
    zeta: &[F128],
    alpha: F128,
    gamma: F128,
    ps: &mut ProverState,
) -> Vec<ColumnClaim> {
    let mut claims = Vec::new();
    decompose_formula(blocks, lay, zeta, alpha, gamma, |col, zeta_lo| {
        let v = mle_eval(&cols[col], zeta_lo);
        ps.add_scalar(v);
        claims.push(ColumnClaim {
            col,
            point: zeta_lo.to_vec(),
            value: v,
        });
        v
    });
    claims
}

/// Verifier-side decomposition: reads the committed values from the stream,
/// recomputes `Ṽ₀(ζ)`, and records the matching claims.
fn decompose_verify(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F128],
    alpha: F128,
    gamma: F128,
    vs: &mut VerifierState,
) -> Result<(F128, Vec<ColumnClaim>), Error> {
    let vals = vs.next_scalars(n_committed(blocks)).map_err(|_| Error::Truncated)?;
    let mut vals_iter = vals.iter().copied();
    let mut claims = Vec::new();
    let value = decompose_formula(blocks, lay, zeta, alpha, gamma, |col, zeta_lo| {
        let v = vals_iter.next().expect("n_committed counts every col_val call");
        claims.push(ColumnClaim {
            col,
            point: zeta_lo.to_vec(),
            value: v,
        });
        v
    });
    Ok((value, claims))
}

/// `base^e` by repeated squaring.
fn fpow(base: F128, mut e: usize) -> F128 {
    let (mut r, mut b) = (F128::ONE, base);
    while e > 0 {
        if e & 1 == 1 {
            r *= b;
        }
        b *= b;
        e >>= 1;
    }
    r
}

/// `π_α` of a block's padding-row tuple, where every column is zero but the read
/// counts (value `1`): `Col(i) -> pad[i]`, `GCol(i) -> g·pad[i]`. Only blocks with
/// padding rows are queried, and those carry only `Const`/`Col`/`GCol`.
fn default_fingerprint(block: &Block, pad: &[F128], alpha: F128) -> F128 {
    let mut fingerprint = F128::ZERO;
    let mut alpha_pow = F128::ONE;
    for c in &block.coords {
        let coord_val = match c {
            Coord::Const(v) => *v,
            Coord::Col(i) => pad[*i],
            Coord::GCol(i) => G * pad[*i],
            Coord::Index | Coord::Public(_) => F128::ZERO,
        };
        fingerprint += alpha_pow * coord_val;
        alpha_pow *= alpha;
    }
    fingerprint
}

/// The default-padding surplus on one side: `∏_b (γ − π_α(default_b))^{2^{κ_b} −
/// real_b}`. The default rows do not self-cancel (nonzero counts, §e2e-pad), so
/// the verifier divides this out before comparing the two sides (§sec:gp).
fn default_surplus(blocks: &[Block], pad: &[F128], alpha: F128, gamma: F128) -> F128 {
    let mut acc = F128::ONE;
    for b in blocks {
        let delta = (1usize << b.kappa) - b.real;
        if delta != 0 {
            acc *= fpow(gamma + default_fingerprint(b, pad, alpha), delta);
        }
    }
    acc
}

/// Prove the bus balances, writing the proof into `ps`; returns the per-column
/// claims to open (§4.4).
pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    cols: &[Column],
    ps: &mut ProverState,
) -> Vec<ColumnClaim> {
    // No shape observe: the block structure is public and reconstructed by the
    // verifier from the (bound) announced sizes + program, and `alpha`/`gamma` only
    // need to follow the witness commitment (which they do) for the grand product
    // to be sound. So sample the fingerprint challenge directly. Then grind
    // before γ to lift the grand product to [`BUS_TARGET_BITS`] (see
    // [`bus_grind_bits`]).
    let alpha = ps.sample();
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let count_lay = layout(count);
    ps.grind(grand_product_grinding_bits(&push_lay, &pull_lay, &count_lay));
    let gamma = ps.sample();
    // The three leaf vectors are independent (transcript-free), so build them
    // concurrently. The count channel's leaf is the read count itself, so its
    // root is the product of all counts (a single `Col`, `γ=0`, `α=1`; §sec:memchan).
    let (push_leaves, (pull_leaves, count_leaves)) = rayon::join(
        || build_leaves(push, &push_lay, cols, alpha, gamma),
        || {
            rayon::join(
                || build_leaves(pull, &pull_lay, cols, alpha, gamma),
                || build_leaves(count, &count_lay, cols, F128::ONE, F128::ZERO),
            )
        },
    );
    let (_, push_claim) = gkr::prove_product(push_leaves, ps);
    let (_, pull_claim) = gkr::prove_product(pull_leaves, ps);
    let (_, count_claim) = gkr::prove_product(count_leaves, ps);

    let mut claims = decompose_prove(push, &push_lay, cols, &push_claim.point, alpha, gamma, ps);
    claims.extend(decompose_prove(
        pull,
        &pull_lay,
        cols,
        &pull_claim.point,
        alpha,
        gamma,
        ps,
    ));
    claims.extend(decompose_prove(
        count,
        &count_lay,
        cols,
        &count_claim.point,
        F128::ONE,
        F128::ZERO,
        ps,
    ));
    claims
}

/// Verify the bus balances, reading the proof from `vs` — oracle-free (the
/// prover's committed values arrive on the stream and are certified by `pcs`).
/// Returns the reconstructed per-column claims for the caller to open.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    pad: &[F128],
    vs: &mut VerifierState,
) -> Result<Vec<ColumnClaim>, Error> {
    // Mirror `prove_balance`: no shape observe (see there); check the pre-γ
    // grinding nonce before sampling γ.
    let alpha = vs.sample();
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let count_lay = layout(count);
    vs.grind_check(grand_product_grinding_bits(&push_lay, &pull_lay, &count_lay)).map_err(|e| match e {
        crate::transcript::Error::PowFailed => Error::PowFailed,
        _ => Error::Truncated,
    })?;
    let gamma = vs.sample();
    let (push_root, cp) = gkr::verify_product(push_lay.mu, vs).map_err(Error::Gkr)?;
    let (pull_root, cq) = gkr::verify_product(pull_lay.mu, vs).map_err(Error::Gkr)?;
    let (count_root, cc) = gkr::verify_product(count_lay.mu, vs).map_err(Error::Gkr)?;
    // Every read count is nonzero iff this product is (§sec:memchan); a zero
    // would let a read self-cancel and free its value from memory.
    if count_root == F128::ZERO {
        return Err(Error::ZeroCount);
    }
    // The two sides differ by the default-padding surplus (§sec:gp); divide each
    // out (cross-multiplied) before comparing.
    let d_push = default_surplus(push, pad, alpha, gamma);
    let d_pull = default_surplus(pull, pad, alpha, gamma);
    if push_root * d_pull != pull_root * d_push {
        return Err(Error::Unbalanced);
    }

    let (vp, mut claims) = decompose_verify(push, &push_lay, &cp.point, alpha, gamma, vs)?;
    if vp != cp.value {
        return Err(Error::Decomposition { side: "push" });
    }
    let (vq, claims_q) = decompose_verify(pull, &pull_lay, &cq.point, alpha, gamma, vs)?;
    if vq != cq.value {
        return Err(Error::Decomposition { side: "pull" });
    }
    claims.extend(claims_q);
    let (vc, claims_c) = decompose_verify(count, &count_lay, &cc.point, F128::ONE, F128::ZERO, vs)?;
    if vc != cc.value {
        return Err(Error::Decomposition { side: "count" });
    }
    claims.extend(claims_c);
    Ok(claims)
}
