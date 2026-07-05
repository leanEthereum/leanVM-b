//! The bus: a single shared channel balanced by a grand product (§4.2–§4.4). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by two GKR passes over the leaf vectors `γ − π_α(σ)`. Each pass
//! reduces to a leaf claim `Ṽ₀(ζ)`, decomposed into evaluation claims on the
//! committed columns. Tuple coordinates `σ_i` are `K`-valued (column entries,
//! g-powers, separators); the fingerprint challenges `α, γ` are `E`-valued, so a
//! leaf accumulates via the mixed `mul_base` product (2 PMULL per coordinate).

use crate::PAR_THRESHOLD;
use crate::field::{F64, F128T, g_pow, index_mle};
use crate::gkr;
use crate::multilinear::{eq_eval, mle_eval};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::Column;
use rayon::prelude::*;

/// One tuple coordinate as a function of the block's row `z`.
#[derive(Clone, Debug)]
pub enum Coord {
    /// A public constant (domain separator, opcode, the seed count `1`).
    Const(F64),
    /// A committed column, value `col[z]`.
    Col(usize),
    /// The free increment `g^k · col[z]` (a virtual column, §1): `k = 1` for the
    /// count/state steps, `k ∈ {1,2,3}` for BLAKE3's consecutive-word successors.
    GCol(usize, u32),
    /// The index column `g^z` (§5.3), free via the factored MLE.
    Index,
    /// A public column (the bytecode program, §8): not committed; both parties form
    /// its MLE directly, so it raises no claim.
    Public(Vec<F64>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. `real` is the
/// number of meaningful rows; the rest are padding (every column zero but the read
/// counts, which are `1`), a fixed default the verifier divides out (§e2e-pad).
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
/// Reconstructed identically by both sides (its value rides the stream).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F128T>,
    pub value: F128T,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Unbalanced,
    /// A read count is zero, so a read self-cancels on the bus (§sec:memchan).
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
/// random challenge with probability ≤ `N / 2^128` (γ is sampled from `E`), i.e.
/// `128 − log2(N)` bits. Grinding adds that many bits back (the prover must redo
/// the PoW to re-roll γ), so we grind the deficit up to the target.
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

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// the mixed product `coeff · source(z)` with `source(z) ∈ K`, `coeff ∈ E`.
/// `GCol` folds the `g^k` factor into the coefficient.
enum Term<'a> {
    Col(usize, F128T),
    Index(F128T),
    Public(&'a [F64], F128T),
}

/// Build one side's leaf vector: block `b` row `z` holds `γ − Σ_i α^i c_i(z)`,
/// padded to `2^μ` with the identity `1`. The row-invariant `α`-power chain and
/// constant coordinates are folded once per block into `const_part`.
pub fn build_leaves(blocks: &[Block], lay: &Layout, cols: &[Column], alpha: F128T, gamma: F128T) -> Vec<F128T> {
    let mut leaves = vec![F128T::ONE; 1usize << lay.mu];
    let maxk = blocks.iter().map(|b| b.kappa).max().unwrap_or(0);
    let gpow = crate::field::g_powers(1usize << maxk);
    for (b, blk) in blocks.iter().enumerate() {
        let mut const_part = gamma;
        let mut terms: Vec<Term> = Vec::with_capacity(blk.coords.len());
        let mut alpha_pow = F128T::ONE;
        for c in &blk.coords {
            match c {
                Coord::Const(v) => const_part += alpha_pow.mul_base(*v),
                Coord::Col(i) => terms.push(Term::Col(*i, alpha_pow)),
                Coord::GCol(i, k) => terms.push(Term::Col(*i, alpha_pow.mul_base(g_pow(*k as usize)))),
                Coord::Index => terms.push(Term::Index(alpha_pow)),
                Coord::Public(vals) => terms.push(Term::Public(vals, alpha_pow)),
            }
            alpha_pow *= alpha;
        }
        let row = |z: usize| -> F128T {
            let mut acc = const_part;
            for t in &terms {
                acc += match t {
                    Term::Col(i, c) => c.mul_base(cols[*i][z]),
                    Term::Index(c) => c.mul_base(gpow[z]),
                    Term::Public(vals, c) => c.mul_base(vals[z]),
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

/// Recompute `Ṽ₀(ζ)` from the block structure, taking each committed column's value
/// at `ζ_lo` from `col_val` (block/coord order): the prover reads the real columns,
/// the verifier replays PCS-certified values.
pub fn decompose_formula<F: FnMut(usize, &[F128T]) -> F128T>(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F128T],
    alpha: F128T,
    gamma: F128T,
    mut col_val: F,
) -> F128T {
    assert_eq!(zeta.len(), lay.mu);
    let mut acc = F128T::ZERO;
    let mut sel_sum = F128T::ZERO;
    for (b, blk) in blocks.iter().enumerate() {
        let kappa = blk.kappa;
        let zeta_lo = &zeta[..kappa];
        let zeta_hi = &zeta[kappa..];
        let sel = lay.offsets[b] >> kappa;
        let sel_bits: Vec<F128T> = (0..(lay.mu - kappa))
            .map(|k| F128T::new(((sel >> k) & 1) as u64, 0))
            .collect();
        let eq_hi = eq_eval(&sel_bits, zeta_hi);
        sel_sum += eq_hi;

        let mut inner = F128T::ZERO;
        let mut alpha_pow = F128T::ONE;
        for c in &blk.coords {
            let coord_val = match c {
                Coord::Const(v) => F128T::from(*v),
                Coord::Index => index_mle(zeta_lo),
                Coord::Col(i) => col_val(*i, zeta_lo),
                Coord::GCol(i, k) => col_val(*i, zeta_lo).mul_base(g_pow(*k as usize)),
                Coord::Public(vals) => mle_eval(vals, zeta_lo),
            };
            inner += alpha_pow * coord_val;
            alpha_pow *= alpha;
        }
        acc += eq_hi * (gamma + inner);
    }
    // The padding rows (identity `1`) contribute the leftover mass `1 - Σ_b sel_b`.
    acc + (F128T::ONE + sel_sum)
}

/// The number of committed coordinates (`Col`/`GCol`) in a side — how many claim
/// values flow through the transcript for it.
fn n_committed(blocks: &[Block]) -> usize {
    blocks
        .iter()
        .flat_map(|b| &b.coords)
        .filter(|c| matches!(c, Coord::Col(_) | Coord::GCol(..)))
        .count()
}

/// Prover-side decomposition: reads the real columns, writing each committed value
/// onto the stream and recording the matching claim (block/coord order).
///
/// The column MLE evaluations run in a parallel first pass: within one
/// `decompose_formula` call no challenge is sampled between claims (`zeta`,
/// `alpha`, `gamma` are fixed arguments and each claim's point is
/// `zeta[..kappa]` of its block), so the values are independent of the
/// transcript and only their `add_scalar` ORDER matters. The second pass
/// replays them through the transcript in the original block/coord order,
/// keeping the stream byte-identical to the serial form.
fn decompose_prove(
    blocks: &[Block],
    lay: &Layout,
    cols: &[Column],
    zeta: &[F128T],
    alpha: F128T,
    gamma: F128T,
    ps: &mut ProverState,
) -> Vec<ColumnClaim> {
    // Pass 1: enumerate the committed coords exactly as `decompose_formula`
    // visits them (blocks in order, coords in order, Col/GCol only; the same
    // filter as `n_committed`), then evaluate all column MLEs in parallel.
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c {
                jobs.push((*i, blk.kappa));
            }
        }
    }
    let vals: Vec<F128T> = jobs
        .par_iter()
        .map(|&(col, kappa)| mle_eval(&cols[col], &zeta[..kappa]))
        .collect();

    // Pass 2: replay in the original order.
    let mut vals_iter = vals.iter().copied();
    let mut claims = Vec::new();
    decompose_formula(blocks, lay, zeta, alpha, gamma, |col, zeta_lo| {
        let v = vals_iter
            .next()
            .expect("job enumeration matches decompose_formula's col_val order");
        debug_assert_eq!(v, mle_eval(&cols[col], zeta_lo), "job/coord order drift");
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
    zeta: &[F128T],
    alpha: F128T,
    gamma: F128T,
    vs: &mut VerifierState,
) -> Result<(F128T, Vec<ColumnClaim>), Error> {
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
fn fpow(base: F128T, mut e: usize) -> F128T {
    let (mut r, mut b) = (F128T::ONE, base);
    while e > 0 {
        if e & 1 == 1 {
            r *= b;
        }
        b *= b;
        e >>= 1;
    }
    r
}

/// `π_α` of a block's padding-row tuple (every column zero but the read counts,
/// value `1`). Only padded blocks are queried, and those carry only `Const`/`Col`/`GCol`.
fn default_fingerprint(block: &Block, pad: &[F64], alpha: F128T) -> F128T {
    let mut fingerprint = F128T::ZERO;
    let mut alpha_pow = F128T::ONE;
    for c in &block.coords {
        let coord_val = match c {
            Coord::Const(v) => *v,
            Coord::Col(i) => pad[*i],
            Coord::GCol(i, k) => g_pow(*k as usize) * pad[*i],
            Coord::Index | Coord::Public(_) => F64::ZERO,
        };
        fingerprint += alpha_pow.mul_base(coord_val);
        alpha_pow *= alpha;
    }
    fingerprint
}

/// The default-padding surplus on one side: `∏_b (γ − π_α(default_b))^{2^{κ_b} −
/// real_b}`. The verifier divides it out before comparing the two sides (§sec:gp).
fn default_surplus(blocks: &[Block], pad: &[F64], alpha: F128T, gamma: F128T) -> F128T {
    let mut acc = F128T::ONE;
    for b in blocks {
        let delta = (1usize << b.kappa) - b.real;
        if delta != 0 {
            acc *= fpow(gamma + default_fingerprint(b, pad, alpha), delta);
        }
    }
    acc
}

/// Prove the bus balances; returns the per-column claims to open (§4.4). `alpha`/
/// `gamma` follow the witness commitment (the only ordering the grand product
/// needs), and the block structure is public, so no shape is observed.
pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    cols: &[Column],
    ps: &mut ProverState,
) -> Vec<ColumnClaim> {
    let alpha = ps.sample();
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let count_lay = layout(count);
    // Grind before γ to lift the grand product to `SECURITY_BITS` ([`grand_product_grinding_bits`]).
    ps.grind(grand_product_grinding_bits(&push_lay, &pull_lay, &count_lay));
    let gamma = ps.sample();
    // Independent leaf vectors; build concurrently. The count channel's leaf is the
    // count itself (a single `Col`, `γ=0`, `α=1`), so its root is the product of all counts.
    let prof = std::env::var("LEANVM_PROFILE").is_ok();
    let t0 = std::time::Instant::now();
    let (push_leaves, (pull_leaves, count_leaves)) = rayon::join(
        || build_leaves(push, &push_lay, cols, alpha, gamma),
        || {
            rayon::join(
                || build_leaves(pull, &pull_lay, cols, alpha, gamma),
                || build_leaves(count, &count_lay, cols, F128T::ONE, F128T::ZERO),
            )
        },
    );
    if prof {
        eprintln!("[bus]   leaves    : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    let t0 = std::time::Instant::now();
    let (_, push_claim) = gkr::prove_product(push_leaves, ps);
    let (_, pull_claim) = gkr::prove_product(pull_leaves, ps);
    let (_, count_claim) = gkr::prove_product(count_leaves, ps);
    if prof {
        eprintln!("[bus]   gkr       : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    let t0 = std::time::Instant::now();

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
        F128T::ONE,
        F128T::ZERO,
        ps,
    ));
    if prof {
        eprintln!("[bus]   decompose : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    claims
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    pad: &[F64],
    vs: &mut VerifierState,
) -> Result<Vec<ColumnClaim>, Error> {
    // Check the pre-γ grinding nonce before sampling γ (mirror of prove_balance).
    let alpha = vs.sample();
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let count_lay = layout(count);
    vs.grind_check(grand_product_grinding_bits(&push_lay, &pull_lay, &count_lay))
        .map_err(|e| match e {
            crate::transcript::Error::PowFailed => Error::PowFailed,
            _ => Error::Truncated,
        })?;
    let gamma = vs.sample();
    let (push_root, cp) = gkr::verify_product(push_lay.mu, vs).map_err(Error::Gkr)?;
    let (pull_root, cq) = gkr::verify_product(pull_lay.mu, vs).map_err(Error::Gkr)?;
    let (count_root, cc) = gkr::verify_product(count_lay.mu, vs).map_err(Error::Gkr)?;
    // Every read count is nonzero iff this product is (§sec:memchan); a zero would
    // let a read self-cancel and free its value from memory.
    if count_root == F128T::ZERO {
        return Err(Error::ZeroCount);
    }
    // The two sides differ by the default-padding surplus; divide each out
    // (cross-multiplied) before comparing.
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
    let (vc, claims_c) = decompose_verify(count, &count_lay, &cc.point, F128T::ONE, F128T::ZERO, vs)?;
    if vc != cc.value {
        return Err(Error::Decomposition { side: "count" });
    }
    claims.extend(claims_c);
    Ok(claims)
}
