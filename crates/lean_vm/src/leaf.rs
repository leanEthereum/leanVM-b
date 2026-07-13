//! The bus: a single shared channel balanced by a grand product (§4.2–§4.4). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset, proven by two GKR passes over the leaf vectors `γ − π_α(σ)`. Each pass
//! reduces to a leaf claim `Ṽ₀(ζ)`, decomposed into evaluation claims on the
//! committed columns. Tuple coordinates `σ_i` are `K`-valued (column entries,
//! g-powers, separators); the fingerprint challenges `α, γ` are `E`-valued, so a
//! leaf accumulates via the mixed `mul_base` product (2 PMULL per coordinate).

use crate::PAR_THRESHOLD;
use primitives::field::{F64, F128T, F128TBaseUnreduced, g_pow, index_mle};
use crate::gkr;
use primitives::multilinear::{eq_eval, mle_eval};
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
/// `128 − log2(N)` bits.
/// Two structural facts collapse this. The push and pull sides emit their bus
/// blocks in matched pairs — every [`FlushBuilder`] call appends one block to
/// each side with equal `κ`, and the three framework blocks (boundary, memory,
/// bytecode) are paired the same way — so the two sides have identical
/// `κ`-multisets and `push_mu == pull_mu`. And each count column is the count
/// coordinate of exactly one bytecode/memory flush while the state flush
/// carries none, so the count side sums strictly fewer `2^κ` than push and
/// `count_mu ≤ push_mu`. Hence `N = 2^push_mu + 2^count_mu` with
/// `count_mu ≤ push_mu`, so `⌈log2 N⌉ = push_mu + 1` exactly and the grind is
/// simply `SECURITY_BITS + push_mu + 1 − 128`. Grinding adds that deficit back
/// (the prover must redo the PoW to re-roll γ).
///
/// The fingerprint challenge α is sampled AFTER the grind, so re-rolling it
/// also costs the PoW (besides the older argument that a fresh commitment to
/// re-roll α already costs `≥ 2^MIN_MU` Merkle hashes, above the target for
/// every admitted witness size).
fn grand_product_grinding_bits(push: &Layout, pull: &Layout, count: &Layout) -> u32 {
    assert_eq!(push.mu, pull.mu, "push/pull bus blocks are paired, so their layouts match");
    assert!(count.mu <= push.mu, "count sums fewer bus messages than push");
    (crate::SECURITY_BITS + push.mu as u32 + 1).saturating_sub(128)
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
    let gpow = primitives::field::g_powers(1usize << maxk);
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
            // The α-weighted coordinate sum defers its reductions: each mixed
            // product contributes its two raw lane products (2 PMULL, no
            // reduction tail), one pair reduction per row at the end —
            // bit-identical to summing reduced `mul_base` terms.
            let mut acc = F128TBaseUnreduced::ZERO;
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

/// Look up an already-recorded claim on `(col, point)`. Push and pull share
/// their GKR point, so a column read by both sides (or by two same-κ blocks of
/// one side) is streamed and opened ONCE; later occurrences reuse the value.
fn known_claim(claims: &[ColumnClaim], col: usize, point: &[F128T]) -> Option<F128T> {
    claims.iter().find(|c| c.col == col && c.point == point).map(|c| c.value)
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
    zeta: &[F128T],
    alpha: F128T,
    gamma: F128T,
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
                let fresh = known_claim(claims, *i, &zeta[..blk.kappa]).is_none()
                    && !jobs.contains(&(*i, blk.kappa));
                if fresh {
                    jobs.push((*i, blk.kappa));
                }
            }
        }
    }
    let vals: Vec<F128T> = jobs
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
    zeta: &[F128T],
    alpha: F128T,
    gamma: F128T,
    claims: &mut Vec<ColumnClaim>,
    vs: &mut VerifierState,
) -> Result<F128T, Error> {
    for blk in blocks {
        let zeta_lo = &zeta[..blk.kappa];
        for c in &blk.coords {
            if let Coord::Col(i) | Coord::GCol(i, _) = c
                && known_claim(claims, *i, zeta_lo).is_none() {
                    let v = vs.next_scalar().map_err(|_| Error::Truncated)?;
                    claims.push(ColumnClaim {
                        col: *i,
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

/// One reduced claim on the bytecode polynomial. The six public encoding
/// columns (op, o1, o2, o3, fpc, ffp) stacked along three selector bits form
/// ONE multilinear polynomial B̃ in `κ_bc + 3` variables; after the
/// decompositions both parties absorb the six per-column evaluations (push and
/// pull share the GKR point ζ, so the columns are evaluated once), sample
/// three selector challenges `s`, and reduce the six values to
/// `B̃(ζ_lo, s) = Σ_c eq(s, c)·v_c`. Natively the claim is
/// true by construction (the verifier evaluated the columns itself); a
/// recursive verifier defers exactly this one claim to its public input.
#[derive(Clone, Debug)]
pub struct BytecodeClaim {
    /// `ζ_side_lo ++ s` — a point in `κ_bc + 3` variables.
    pub point: Vec<F128T>,
    /// `B̃(point)`.
    pub value: F128T,
}

/// The public (bytecode) coordinate evaluations of a side at its GKR point,
/// block/coord order, with the bytecode block's `κ`.
pub fn public_evals(blocks: &[Block], zeta: &[F128T]) -> (usize, Vec<F128T>) {
    let mut kappa = 0;
    let mut out = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Public(vals) = c {
                kappa = blk.kappa;
                out.push(mle_eval(vals, &zeta[..blk.kappa]));
            }
        }
    }
    (kappa, out)
}

/// The stacked bytecode polynomial as a dense table: the six public encoding
/// columns along three selector bits (`B̃`'s evaluations on the cube). This is
/// the polynomial [`BytecodeClaim`]s are claims about; the outermost native
/// verifier evaluates it here.
pub fn stacked_bytecode_table(blocks: &[Block]) -> Vec<F64> {
    let mut kbc = 0;
    let mut cols: Vec<&Vec<F64>> = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Public(vals) = c {
                kbc = blk.kappa;
                cols.push(vals);
            }
        }
    }
    let mut table = vec![F64::ZERO; 8 << kbc];
    for (c_idx, vals) in cols.iter().enumerate() {
        assert_eq!(vals.len(), 1 << kbc);
        table[(c_idx << kbc)..((c_idx + 1) << kbc)].copy_from_slice(vals);
    }
    table
}

/// `Σ_c eq(s, c)·v_c`: one side's public-column evaluations reduced to the
/// stacked-polynomial value at selector point `s`.
pub fn stacked_bytecode_value(evals: &[F128T], s: &[F128T; 3]) -> F128T {
    let mut acc = F128T::ZERO;
    for (c, &v) in evals.iter().enumerate() {
        let mut e = F128T::ONE;
        for (t, &st) in s.iter().enumerate() {
            e *= if (c >> t) & 1 == 1 { st } else { F128T::ONE + st };
        }
        acc += e * v;
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
) -> (Vec<ColumnClaim>, Vec<BytecodeClaim>) {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    // Grind FIRST, so the PoW covers both bus challenges α and γ
    // ([`grand_product_grinding_bits`]): re-rolling either means redoing it.
    ps.grind(grand_product_grinding_bits(&push_lay, &pull_lay, &count_lay));
    let alpha = ps.sample();
    // Pad the count tree to the pair's depth with identity leaves (the product,
    // blocks, and offsets are unchanged; `build_leaves` fills the cube with `1`
    // and the decompose accounts the padding mass), so all THREE trees share
    // one RLC-batched GKR — and one point ζ.
    count_lay.mu = push_lay.mu;
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
    // All three trees run as ONE RLC-batched GKR (equal μ: push/pull match
    // block-for-block, count is padded), so every claim lands on ONE point ζ.
    let bus_gkr = gkr::prove_product_triple([push_leaves, pull_leaves, count_leaves], ps);
    if prof {
        eprintln!("[bus]   gkr       : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    let t0 = std::time::Instant::now();

    // One shared claim list: push/pull duplicates (same column, same shared
    // point) are streamed and opened once. The count side has its own weights,
    // so its claims stay distinct only where the columns differ.
    let mut claims: Vec<ColumnClaim> = Vec::new();
    decompose_prove(push, &push_lay, cols, &bus_gkr.point, alpha, gamma, &mut claims, ps);
    decompose_prove(pull, &pull_lay, cols, &bus_gkr.point, alpha, gamma, &mut claims, ps);
    decompose_prove(count, &count_lay, cols, &bus_gkr.point, F128T::ONE, F128T::ZERO, &mut claims, ps);
    if prof {
        eprintln!("[bus]   decompose : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }

    // Bytecode = ONE polynomial, and push/pull now share the point ζ, so the
    // six public columns are opened ONCE: bind the evaluations, sample the
    // selector challenges, emit the single reduced claim.
    let (kbc, pv) = public_evals(push, &bus_gkr.point);
    for &v in &pv {
        ps.observe_scalar(v);
    }
    let s = [ps.sample(), ps.sample(), ps.sample()];
    let bytecode_claims = vec![BytecodeClaim {
        point: [&bus_gkr.point[..kbc], &s[..]].concat(),
        value: stacked_bytecode_value(&pv, &s),
    }];
    (claims, bytecode_claims)
}

/// What [`verify_balance`] establishes: the per-column claims to open, the
/// reduced bytecode claim (a one-element vec in practice: push and pull share
/// ζ), and the count-channel root (nonzero; recursion
/// guests prove that via a hinted inverse).
pub struct BusVerify {
    pub claims: Vec<ColumnClaim>,
    pub bytecode_claims: Vec<BytecodeClaim>,
    pub count_root: F128T,
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    pad: &[F64],
    vs: &mut VerifierState,
) -> Result<BusVerify, Error> {
    // Check the grinding nonce FIRST: the PoW covers both bus challenges
    // α and γ (mirror of prove_balance).
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    vs.grind_check(grand_product_grinding_bits(&push_lay, &pull_lay, &count_lay)).map_err(|e| match e {
        crate::transcript::Error::PowFailed => Error::PowFailed,
        _ => Error::Truncated,
    })?;
    let alpha = vs.sample();
    // The count tree is padded to the pair's depth (identity leaves), so all
    // three verify as ONE RLC-batched GKR at ONE shared point.
    count_lay.mu = push_lay.mu;
    let gamma = vs.sample();
    let bus_gkr = gkr::verify_product_triple(push_lay.mu, vs).map_err(Error::Gkr)?;
    let [push_root, pull_root, count_root] = bus_gkr.roots;
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

    let mut claims: Vec<ColumnClaim> = Vec::new();
    let vp = decompose_verify(push, &push_lay, &bus_gkr.point, alpha, gamma, &mut claims, vs)?;
    if vp != bus_gkr.values[0] {
        return Err(Error::Decomposition { side: "push" });
    }
    let vq = decompose_verify(pull, &pull_lay, &bus_gkr.point, alpha, gamma, &mut claims, vs)?;
    if vq != bus_gkr.values[1] {
        return Err(Error::Decomposition { side: "pull" });
    }
    let vc = decompose_verify(count, &count_lay, &bus_gkr.point, F128T::ONE, F128T::ZERO, &mut claims, vs)?;
    if vc != bus_gkr.values[2] {
        return Err(Error::Decomposition { side: "count" });
    }

    // Bytecode = ONE polynomial (mirror of `prove_balance`); the shared push/
    // pull point means one set of public-column evaluations and ONE reduced
    // claim on the stacked bytecode multilinear.
    let (kbc, pv) = public_evals(push, &bus_gkr.point);
    for &v in &pv {
        vs.observe_scalar(v);
    }
    let s = [vs.sample(), vs.sample(), vs.sample()];
    let bytecode_claims = vec![BytecodeClaim {
        point: [&bus_gkr.point[..kbc], &s[..]].concat(),
        value: stacked_bytecode_value(&pv, &s),
    }];
    Ok(BusVerify {
        claims,
        bytecode_claims,
        count_root,
    })
}
