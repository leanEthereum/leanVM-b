//! The state bus, balanced by a grand product (§4.2–§4.4). Each instruction
//! wires `(pc, fp)` and its successor into tuples; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by two GKR passes over the leaf vectors `γ − π_α(σ)`. Each pass
//! reduces to a leaf claim `Ṽ₀(ζ)`, decomposed into evaluation claims on the
//! committed columns. Tuple coordinates `σ_i` are `K`-valued (column entries,
//! g-powers, separators); the fingerprint challenges `α, γ` are `E`-valued, so a
//! leaf accumulates via the mixed `mul_base` product (2 PMULL per coordinate).

use crate::PAR_THRESHOLD;
use crate::gkr;
use crate::transcript::{ProverState, VerifierState};
use crate::witness::Column;
use primitives::field::{F64, F192, F192BaseUnreduced, g_pow, index_mle};
use primitives::multilinear::{eq_eval, mle_eval};
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
    /// First row of the aligned source slice. Ordinary whole-column claims use 0.
    pub start: usize,
    pub point: Vec<F192>,
    pub value: F192,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Unbalanced,
    Gkr(gkr::GkrError),
    Decomposition { side: &'static str },
}

/// Check that the state grand product fits the native field's soundness budget.
fn assert_grinding_unnecessary(push: &Layout, pull: &Layout) {
    assert_eq!(
        push.mu, pull.mu,
        "push/pull bus blocks are paired, so their layouts match"
    );
    assert!(
        crate::SECURITY_BITS + (push.mu as u32) < 192,
        "bus layout exceeds the unground F192 soundness budget"
    );
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
    Col(usize, F192),
    Index(F192),
    Public(&'a [F64], F192),
}

/// Build one side's leaf vector: block `b` row `z` holds `γ − Σ_i α^i c_i(z)`,
/// padded to `2^μ` with the identity `1`. The row-invariant `α`-power chain and
/// constant coordinates are folded once per block into `const_part`.
pub fn build_leaves(blocks: &[Block], lay: &Layout, cols: &[Column], alpha: F192, gamma: F192) -> Vec<F192> {
    let mut leaves = vec![F192::ONE; 1usize << lay.mu];
    let maxk = blocks.iter().map(|b| b.kappa).max().unwrap_or(0);
    let gpow = primitives::field::g_powers(1usize << maxk);
    for (b, blk) in blocks.iter().enumerate() {
        let mut const_part = gamma;
        let mut terms: Vec<Term> = Vec::with_capacity(blk.coords.len());
        let mut alpha_pow = F192::ONE;
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
        let row = |z: usize| -> F192 {
            // The α-weighted coordinate sum defers its reductions: each mixed
            // product contributes its three raw limb products (3 PMULL, no
            // reduction tail), one combined reduction per row at the end —
            // bit-identical to summing reduced `mul_base` terms.
            let mut acc = F192BaseUnreduced::ZERO;
            for t in &terms {
                acc ^= match t {
                    Term::Col(i, c) => c.mul_base_unreduced(cols[*i][z]),
                    Term::Index(c) => c.mul_base_unreduced(gpow[z]),
                    Term::Public(vals, c) => c.mul_base_unreduced(vals[z]),
                };
            }
            const_part + acc.reduce()
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
pub fn decompose_formula<F: FnMut(usize, &[F192]) -> F192>(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F192],
    alpha: F192,
    gamma: F192,
    mut col_val: F,
) -> F192 {
    assert_eq!(zeta.len(), lay.mu);
    let mut acc = F192::ZERO;
    let mut sel_sum = F192::ZERO;
    for (b, blk) in blocks.iter().enumerate() {
        let kappa = blk.kappa;
        let zeta_lo = &zeta[..kappa];
        let zeta_hi = &zeta[kappa..];
        let sel = lay.offsets[b] >> kappa;
        let sel_bits: Vec<F192> = (0..(lay.mu - kappa))
            .map(|k| F192::new(((sel >> k) & 1) as u64, 0, 0))
            .collect();
        let eq_hi = eq_eval(&sel_bits, zeta_hi);
        sel_sum += eq_hi;

        let mut inner = F192::ZERO;
        let mut alpha_pow = F192::ONE;
        for c in &blk.coords {
            let coord_val = match c {
                Coord::Const(v) => F192::from(*v),
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
    acc + (F192::ONE + sel_sum)
}

/// Look up an already-recorded claim on `(col, point)`. Push and pull share
/// their GKR point, so a column read by both sides (or by two same-κ blocks of
/// one side) is streamed and opened ONCE; later occurrences reuse the value.
fn known_claim(claims: &[ColumnClaim], col: usize, point: &[F192]) -> Option<F192> {
    claims
        .iter()
        .find(|c| c.col == col && c.point == point)
        .map(|c| c.value)
}

/// Prover-side decomposition: reads the real columns, writing each FRESH
/// committed value onto the stream and recording the matching claim
/// (block/coord order); duplicates reuse the recorded value.
///
/// The fresh column MLE evaluations run in a parallel first pass: within one
/// `decompose_formula` call no challenge is sampled between claims (`zeta`,
/// `alpha`, `gamma` are fixed arguments and each claim's point is
/// `zeta[..kappa]` of its block), so the values are independent of the
/// transcript and only their `add_scalar` ORDER matters. The second pass
/// replays them through the transcript in the original block/coord order,
/// keeping the stream byte-identical to the serial form.
#[allow(clippy::too_many_arguments)] // the shared dedup context is the 8th
fn decompose_prove(
    blocks: &[Block],
    lay: &Layout,
    cols: &[Column],
    zeta: &[F192],
    alpha: F192,
    gamma: F192,
    claims: &mut Vec<ColumnClaim>,
    ps: &mut ProverState,
) {
    // Pass 1: enumerate the FRESH committed coords exactly as `decompose_formula`
    // visits them (blocks in order, coords in order, Col/GCol only, first
    // occurrence per `(col, point)` — the same dedup as `known_claim`), then
    // evaluate the column MLEs in parallel.
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c {
                let fresh = known_claim(claims, *i, &zeta[..blk.kappa]).is_none() && !jobs.contains(&(*i, blk.kappa));
                if fresh {
                    jobs.push((*i, blk.kappa));
                }
            }
        }
    }
    let vals: Vec<F192> = jobs
        .par_iter()
        .map(|&(col, kappa)| mle_eval(&cols[col], &zeta[..kappa]))
        .collect();

    // Pass 2: replay in the original order; duplicates reuse the recorded claim.
    let mut fresh_iter = jobs.iter().zip(vals.iter());
    decompose_formula(blocks, lay, zeta, alpha, gamma, |col, zeta_lo| {
        if let Some(v) = known_claim(claims, col, zeta_lo) {
            return v;
        }
        let (&(jc, jk), &v) = fresh_iter
            .next()
            .expect("job enumeration matches decompose_formula's col_val order");
        debug_assert_eq!((jc, jk), (col, zeta_lo.len()), "job/coord order drift");
        debug_assert_eq!(v, mle_eval(&cols[col], zeta_lo), "job/coord order drift");
        ps.add_scalar(v);
        claims.push(ColumnClaim {
            col,
            start: 0,
            point: zeta_lo.to_vec(),
            value: v,
        });
        v
    });
}

/// Verifier-side decomposition: reads each FRESH committed value from the
/// stream (duplicates reuse the recorded claim), recomputes `Ṽ₀(ζ)`, and
/// records the fresh claims. A pre-pass mirrors the formula's block/coord scan
/// so the stream reads stay sequential.
fn decompose_verify(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F192],
    alpha: F192,
    gamma: F192,
    claims: &mut Vec<ColumnClaim>,
    vs: &mut VerifierState,
) -> Result<F192, Error> {
    for blk in blocks {
        let zeta_lo = &zeta[..blk.kappa];
        for c in &blk.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c
                && known_claim(claims, *i, zeta_lo).is_none()
            {
                let v = vs.next_scalar().map_err(|_| Error::Truncated)?;
                claims.push(ColumnClaim {
                    col: *i,
                    start: 0,
                    point: zeta_lo.to_vec(),
                    value: v,
                });
            }
        }
    }
    let value = decompose_formula(blocks, lay, zeta, alpha, gamma, |col, zeta_lo| {
        known_claim(claims, col, zeta_lo).expect("the pre-pass recorded every coordinate")
    });
    Ok(value)
}

/// `base^e` by repeated squaring.
fn fpow(base: F192, mut e: usize) -> F192 {
    let (mut r, mut b) = (F192::ONE, base);
    while e > 0 {
        if e & 1 == 1 {
            r *= b;
        }
        b *= b;
        e >>= 1;
    }
    r
}

/// `π_α` of a block's padding-row tuple. Only padded state blocks are
/// queried, and those carry only `Const`/`Col`/`GCol` coordinates.
fn default_fingerprint(block: &Block, pad: &[F64], alpha: F192) -> F192 {
    let mut fingerprint = F192::ZERO;
    let mut alpha_pow = F192::ONE;
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
fn default_surplus(blocks: &[Block], pad: &[F64], alpha: F192, gamma: F192) -> F192 {
    let mut acc = F192::ONE;
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
pub fn prove_balance(push: &[Block], pull: &[Block], cols: &[Column], ps: &mut ProverState) -> Vec<ColumnClaim> {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    assert_grinding_unnecessary(&push_lay, &pull_lay);
    let alpha = ps.sample();
    let gamma = ps.sample();
    let prof = std::env::var("LEANVM_PROFILE").is_ok();
    let t0 = std::time::Instant::now();
    let (push_leaves, pull_leaves) = rayon::join(
        || build_leaves(push, &push_lay, cols, alpha, gamma),
        || build_leaves(pull, &pull_lay, cols, alpha, gamma),
    );
    if prof {
        eprintln!("[bus]   leaves    : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    let t0 = std::time::Instant::now();
    let bus_gkr = gkr::prove_product_pair([push_leaves, pull_leaves], ps);
    if prof {
        eprintln!("[bus]   gkr       : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    let t0 = std::time::Instant::now();

    let mut claims: Vec<ColumnClaim> = Vec::new();
    decompose_prove(push, &push_lay, cols, &bus_gkr.point, alpha, gamma, &mut claims, ps);
    decompose_prove(pull, &pull_lay, cols, &bus_gkr.point, alpha, gamma, &mut claims, ps);
    if prof {
        eprintln!("[bus]   decompose : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }

    claims
}

pub struct BusVerify {
    pub claims: Vec<ColumnClaim>,
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
pub fn verify_balance(push: &[Block], pull: &[Block], pad: &[F64], vs: &mut VerifierState) -> Result<BusVerify, Error> {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    assert_grinding_unnecessary(&push_lay, &pull_lay);
    let alpha = vs.sample();
    let gamma = vs.sample();
    let bus_gkr = gkr::verify_product_pair(push_lay.mu, vs).map_err(Error::Gkr)?;
    let [push_root, pull_root] = bus_gkr.roots;
    // The two sides differ by the default-padding surplus; divide each out
    // (cross-multiplied) before comparing.
    let d_push = default_surplus(push, pad, alpha, gamma);
    let d_pull = default_surplus(pull, pad, alpha, gamma);
    if push_root * d_pull != pull_root * d_push {
        return Err(Error::Unbalanced);
    }

    let mut claims: Vec<ColumnClaim> = Vec::new();
    let vp = decompose_verify(push, &push_lay, &bus_gkr.point, alpha, gamma, &mut claims, vs)?;
    if vp != bus_gkr.values[0] {
        return Err(Error::Decomposition { side: "push" });
    }
    let vq = decompose_verify(pull, &pull_lay, &bus_gkr.point, alpha, gamma, &mut claims, vs)?;
    if vq != bus_gkr.values[1] {
        return Err(Error::Decomposition { side: "pull" });
    }
    Ok(BusVerify { claims })
}
