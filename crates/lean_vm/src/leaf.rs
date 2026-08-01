//! The bus: a single shared channel balanced by a grand product (§4.2–§4.4). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
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
    pub point: Vec<F192>,
    pub value: F192,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Unbalanced,
    /// A read count is zero, so a read self-cancels on the bus (§sec:memchan).
    ZeroCount,
    Gkr(gkr::GkrError),
}

/// Conservative sum of the degree bounds for every random-challenge failure in
/// the bus argument. A side contains at most `2^mu` leaf factors; multiplying by
/// the other side's padding surplus can double that count. Each factor has total
/// `(alpha, gamma)` degree at most the tuple width. The second term covers all
/// radix-four GKR batching and sumcheck challenges.
fn soundness_degree_bound(mu: usize, tuple_width: usize) -> u128 {
    assert!(mu < u128::BITS as usize, "bus layout is too large to bound");
    let fingerprint = 2u128 * tuple_width as u128 * (1u128 << mu);
    let gkr = 8u128 * (mu as u128 + 1).pow(2);
    fingerprint + gkr
}

fn soundness_bits(mu: usize, tuple_width: usize) -> u32 {
    let degree = soundness_degree_bound(mu, tuple_width);
    192u32.saturating_sub(u128::BITS - degree.leading_zeros())
}

/// Check that the 192-bit challenge field supplies the target bus soundness.
/// Push and pull have the same logical height, and the count product is checked
/// by the same GKR rather than by a separate root-at-random test.
fn assert_grinding_unnecessary(
    push_blocks: &[Block],
    pull_blocks: &[Block],
    push: &Layout,
    pull: &Layout,
    count: &Layout,
) {
    assert_eq!(
        push.mu, pull.mu,
        "push/pull bus blocks are paired, so their layouts match"
    );
    assert!(count.mu <= push.mu, "count sums fewer bus messages than push");
    let tuple_width = push_blocks
        .iter()
        .chain(pull_blocks)
        .map(|block| block.coords.len())
        .max()
        .unwrap_or(0);
    assert!(
        soundness_bits(push.mu, tuple_width) >= crate::SECURITY_BITS,
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

/// One table's bus contribution on one side, as a linear form over that table's
/// committed columns: `Σ_c coeffs[c]·col_c(z) + constant`. Every coefficient is a
/// public function of `α`, `γ` and the block selectors at `ζ`, because a table's
/// bus blocks carry only `Const`/`Col`/`GCol` coordinates. The batched zerocheck
/// sums this against `eq(ζ[..τ], ·)` instead of opening each column at `ζ`, which
/// is why those per-column claims no longer reach the PCS.
#[derive(Clone, Debug)]
pub struct BusForm {
    pub coeffs: Vec<F192>,
    pub constant: F192,
}

impl BusForm {
    fn new(n_cols: usize) -> Self {
        Self {
            coeffs: vec![F192::ZERO; n_cols],
            constant: F192::ZERO,
        }
    }

    /// `Σ_c coeffs[c]·evals[c] + constant`: the form at one row, or at a point when
    /// `evals` are column evaluations there.
    pub fn eval(&self, evals: &[F192]) -> F192 {
        self.coeffs
            .iter()
            .zip(evals)
            .fold(self.constant, |acc, (&w, &v)| acc + w * v)
    }
}

/// Walk one side's blocks. A block owned by table `t` (with column base `base`)
/// accumulates into `forms[t]`; the framework blocks are decomposed into per-column
/// claims as before, `fresh` supplying values not already in `claims`. Returns the
/// framework blocks' contribution to `Ṽ₀(ζ)` plus the padding mass, so the caller
/// can settle the side once the zerocheck has proven the tables' forms.
fn decompose_formula<F: FnMut(usize, &[F192]) -> Result<F192, Error>>(
    blocks: &[Block],
    lay: &Layout,
    zeta: &[F192],
    alpha: F192,
    gamma: F192,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    mut fresh: F,
) -> Result<F192, Error> {
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

        // A table's block becomes a linear form the zerocheck will sum; only the
        // framework blocks (boundary, memory, bytecode) still open columns at ζ.
        if let Some((t, base)) = owners[b] {
            let form = &mut forms[t];
            form.constant += eq_hi * gamma;
            let mut alpha_pow = F192::ONE;
            for c in &blk.coords {
                match c {
                    Coord::Const(v) => form.constant += eq_hi * alpha_pow.mul_base(*v),
                    Coord::Col(i) => form.coeffs[*i - base] += eq_hi * alpha_pow,
                    Coord::GCol(i, k) => form.coeffs[*i - base] += eq_hi * alpha_pow.mul_base(g_pow(*k as usize)),
                    Coord::Index | Coord::Public(_) => {
                        unreachable!("a table's bus block carries no virtual coordinate")
                    }
                }
                alpha_pow *= alpha;
            }
            continue;
        }

        let mut inner = F192::ZERO;
        let mut alpha_pow = F192::ONE;
        for c in &blk.coords {
            let coord_val = match c {
                Coord::Const(v) => F192::from(*v),
                Coord::Index => index_mle(zeta_lo),
                Coord::Col(i) => {
                    if let Some(v) = known_claim(claims, *i, zeta_lo) {
                        v
                    } else {
                        let v = fresh(*i, zeta_lo)?;
                        claims.push(ColumnClaim {
                            col: *i,
                            point: zeta_lo.to_vec(),
                            value: v,
                        });
                        v
                    }
                }
                Coord::GCol(i, k) => {
                    let v = if let Some(v) = known_claim(claims, *i, zeta_lo) {
                        v
                    } else {
                        let v = fresh(*i, zeta_lo)?;
                        claims.push(ColumnClaim {
                            col: *i,
                            point: zeta_lo.to_vec(),
                            value: v,
                        });
                        v
                    };
                    v.mul_base(g_pow(*k as usize))
                }
                Coord::Public(vals) => mle_eval(vals, zeta_lo),
            };
            inner += alpha_pow * coord_val;
            alpha_pow *= alpha;
        }
        acc += eq_hi * (gamma + inner);
    }
    // The padding rows (identity `1`) contribute the leftover mass `1 - Σ_b sel_b`.
    Ok(acc + (F192::ONE + sel_sum))
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
#[allow(clippy::too_many_arguments)] // the shared dedup + form context
fn decompose_prove(
    blocks: &[Block],
    lay: &Layout,
    cols: &[Column],
    zeta: &[F192],
    alpha: F192,
    gamma: F192,
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    ps: &mut ProverState,
) -> F192 {
    // Pass 1: enumerate the FRESH committed coords exactly as `decompose_formula`
    // visits them (blocks in order, coords in order, Col/GCol only, first
    // occurrence per `(col, point)` — the same dedup as `known_claim`), then
    // evaluate the column MLEs in parallel.
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    for (b, blk) in blocks.iter().enumerate() {
        if owners[b].is_some() {
            continue;
        }
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
    decompose_formula(
        blocks,
        lay,
        zeta,
        alpha,
        gamma,
        owners,
        forms,
        claims,
        |col, zeta_lo| {
            let (&(jc, jk), &v) = fresh_iter
                .next()
                .expect("job enumeration matches decompose_formula's col_val order");
            debug_assert_eq!((jc, jk), (col, zeta_lo.len()), "job/coord order drift");
            debug_assert_eq!(v, mle_eval(&cols[col], zeta_lo), "job/coord order drift");
            ps.add_scalar(v);
            Ok(v)
        },
    )
    .expect("prover decomposition is infallible")
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
    owners: &[Option<(usize, usize)>],
    forms: &mut [BusForm],
    claims: &mut Vec<ColumnClaim>,
    vs: &mut VerifierState,
) -> Result<F192, Error> {
    decompose_formula(blocks, lay, zeta, alpha, gamma, owners, forms, claims, |_, _| {
        vs.next_scalar().map_err(|_| Error::Truncated)
    })
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

/// `π_α` of a block's padding-row tuple (every column zero but the read counts,
/// value `1`). Only padded blocks are queried, and those carry only `Const`/`Col`/`GCol`.
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

/// One reduced claim on the bytecode polynomial. The nine public encoding
/// columns (opcode plus eight operand/immediate slots), padded to sixteen slots
/// along four selector bits, form one multilinear polynomial B̃ in `κ_bc + 4`
/// variables. After decomposition both parties absorb the nine column
/// evaluations (push and pull share the GKR point ζ), sample four selector
/// challenges `s`, and reduce them to
/// `B̃(ζ_lo, s) = Σ_c eq(s, c)·v_c`. Natively the claim is
/// true by construction (the verifier evaluated the columns itself); a
/// recursive verifier defers exactly this one claim to its public input.
#[derive(Clone, Debug)]
pub struct BytecodeClaim {
    /// `ζ_side_lo ++ s` — a point in `κ_bc + 4` variables.
    pub point: Vec<F192>,
    /// `B̃(point)`.
    pub value: F192,
}

/// The public (bytecode) coordinate evaluations of a side at its GKR point,
/// block/coord order, with the bytecode block's `κ`.
pub fn public_evals(blocks: &[Block], zeta: &[F192]) -> (usize, Vec<F192>) {
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

/// The stacked bytecode polynomial as a dense table: nine public encoding
/// columns padded to sixteen selector slots. This is the polynomial
/// [`BytecodeClaim`]s are claims about; the outermost verifier evaluates it.
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
    assert!(cols.len() <= 1 << N_BYTECODE_SELECTORS);
    let mut table = vec![F64::ZERO; 1 << (N_BYTECODE_SELECTORS + kbc)];
    for (c_idx, vals) in cols.iter().enumerate() {
        assert_eq!(vals.len(), 1 << kbc);
        table[(c_idx << kbc)..((c_idx + 1) << kbc)].copy_from_slice(vals);
    }
    table
}

/// `Σ_c eq(s, c)·v_c`: one side's public-column evaluations reduced to the
/// Selector bits of the stacked bytecode polynomial: the public encoding
/// columns (opcode + eight operand/immediate slots = nine) stack along
/// `2^N_BYTECODE_SELECTORS` slots.
pub const N_BYTECODE_SELECTORS: usize = 4;

/// stacked-polynomial value at selector point `s`.
pub fn stacked_bytecode_value(evals: &[F192], s: &[F192]) -> F192 {
    debug_assert_eq!(s.len(), N_BYTECODE_SELECTORS);
    let mut acc = F192::ZERO;
    for (c, &v) in evals.iter().enumerate() {
        let mut e = F192::ONE;
        for (t, &st) in s.iter().enumerate() {
            e *= if (c >> t) & 1 == 1 { st } else { F192::ONE + st };
        }
        acc += e * v;
    }
    acc
}

/// Prove the bus balances; returns the per-column claims to open (§4.4). `alpha`/
/// `gamma` follow the witness commitment (the only ordering the grand product
/// needs), and the block structure is public, so no shape is observed.
/// Everything the bus hands on: the framework blocks' column claims, the reduced
/// bytecode claim, the shared GKR point (the batched zerocheck's eq point), and
/// per side the tables' linear forms plus what each is claimed to sum to.
pub struct BusProof {
    pub claims: Vec<ColumnClaim>,
    pub bytecode_claims: Vec<BytecodeClaim>,
    /// The GKR point ζ: the zerocheck reuses it, so no fresh point is sampled.
    pub point: Vec<F192>,
    /// `forms[side][table]`, in `[push, pull, count]` order.
    pub forms: [Vec<BusForm>; 3],
    /// `sigmas[side][table]`: each form's eq-weighted sum over its table's rows.
    /// Prover-side only. NOTHING here travels: the batch's target is the caller's
    /// derived `Σ_s η^·totals[s]`, and the shares serve only to build each round's
    /// waiting line, which rides inside the round polynomial.
    pub sigmas: [Vec<F192>; 3],
}

pub fn prove_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    cols: &[Column],
    owners: &[Vec<Option<(usize, usize)>>; 3],
    tables: &[(usize, usize)],
    ps: &mut ProverState,
) -> BusProof {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    assert_grinding_unnecessary(push, pull, &push_lay, &pull_lay, &count_lay);
    let alpha = ps.sample();
    // The GKR treats the count tree as identity-padded to the pair's depth, but
    // its prover keeps that all-one suffix implicit. Retain the smaller layout
    // for leaf construction and the full logical layout for decomposition.
    let count_build_lay = count_lay.clone();
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
                || build_leaves(count, &count_build_lay, cols, F192::ONE, F192::ZERO),
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

    // Framework blocks keep their per-column claims (deduped: push/pull share ζ);
    // every table block becomes a linear form for the zerocheck instead.
    let mut claims: Vec<ColumnClaim> = Vec::new();
    let sides: [(&[Block], &Layout, F192, F192); 3] = [
        (push, &push_lay, alpha, gamma),
        (pull, &pull_lay, alpha, gamma),
        (count, &count_lay, F192::ONE, F192::ZERO),
    ];
    // Each table's columns at ζ[..τ], computed once and shared by the three sides
    // (a form is linear in them). Nothing here travels, neither the evaluations nor
    // any total: the verifier derives each side's table share as `Ṽ₀(ζ)` less the
    // framework decomposition ([`verify_balance`]) and the batch settles it. A
    // transmitted total would appear in exactly one check, which it could always be
    // solved to satisfy, and would settle nothing.
    let table_evals = tables_at(cols, tables, &bus_gkr.point);
    let mut forms = std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n)).collect::<Vec<_>>());
    let mut sigmas: [Vec<F192>; 3] = std::array::from_fn(|_| Vec::new());
    for (s, &(blocks, lay, a, g)) in sides.iter().enumerate() {
        let framework = decompose_prove(
            blocks,
            lay,
            cols,
            &bus_gkr.point,
            a,
            g,
            &owners[s],
            &mut forms[s],
            &mut claims,
            ps,
        );
        sigmas[s] = forms[s].iter().zip(&table_evals).map(|(f, e)| f.eval(e)).collect();
        // Completeness only: the verifier derives this identity rather than checking
        // it, so a mismatch here is a prover bug, not a rejection path.
        debug_assert_eq!(
            sigmas[s].iter().fold(framework, |acc, &b| acc + b),
            bus_gkr.values[s],
            "side {s} must decompose into its leaf value"
        );
    }
    if prof {
        eprintln!("[bus]   decompose : {:>7.2} ms", t0.elapsed().as_secs_f64() * 1e3);
    }

    // Bytecode = ONE polynomial, and push/pull now share the point ζ, so the
    // nine public columns are opened ONCE: bind the evaluations, sample the
    // selector challenges, emit the single reduced claim.
    let (kbc, pv) = public_evals(push, &bus_gkr.point);
    for &v in &pv {
        ps.observe_scalar(v);
    }
    let s: Vec<F192> = (0..N_BYTECODE_SELECTORS).map(|_| ps.sample()).collect();
    let bytecode_claims = vec![BytecodeClaim {
        point: [&bus_gkr.point[..kbc], &s[..]].concat(),
        value: stacked_bytecode_value(&pv, &s),
    }];
    BusProof {
        claims,
        bytecode_claims,
        point: bus_gkr.point,
        forms,
        sigmas,
    }
}

/// Every table's committed columns at `ζ[..τ_t]`: one `eq` table per table, then an
/// inner product per column. `tables[t] = (base, n_cols)` in the global schema.
fn tables_at(cols: &[Column], tables: &[(usize, usize)], zeta: &[F192]) -> Vec<Vec<F192>> {
    tables
        .iter()
        .map(|&(base, n_cols)| {
            let tau = crate::log2_strict_usize(cols[base].len());
            (0..n_cols)
                .into_par_iter()
                .map(|c| mle_eval(&cols[base + c], &zeta[..tau]))
                .collect()
        })
        .collect()
}

/// What [`verify_balance`] establishes: the per-column claims to open, the
/// reduced bytecode claim (a one-element vec in practice: push and pull share
/// ζ), and the count-channel root (nonzero; recursion
/// guests prove that via a hinted inverse).
pub struct BusVerify {
    pub claims: Vec<ColumnClaim>,
    pub bytecode_claims: Vec<BytecodeClaim>,
    pub count_root: F192,
    /// The GKR point ζ, reused as the batched zerocheck's eq point.
    pub point: Vec<F192>,
    /// `forms[side][table]`, for the zerocheck to settle.
    pub forms: [Vec<BusForm>; 3],
    /// Per side, what the tables' blocks owe its leaf claim: `Ṽ₀(ζ)` less the
    /// framework blocks' decomposition. Derived here, pinned by the batch's target.
    pub totals: [F192; 3],
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    pad: &[F64],
    owners: &[Vec<Option<(usize, usize)>>; 3],
    tables: &[(usize, usize)],
    vs: &mut VerifierState,
) -> Result<BusVerify, Error> {
    let push_lay = layout(push);
    let pull_lay = layout(pull);
    let mut count_lay = layout(count);
    assert_grinding_unnecessary(push, pull, &push_lay, &pull_lay, &count_lay);
    let alpha = vs.sample();
    // The count tree is padded to the pair's depth (identity leaves), so all
    // three verify as ONE RLC-batched GKR at ONE shared point.
    count_lay.mu = push_lay.mu;
    let gamma = vs.sample();
    let bus_gkr = gkr::verify_product_triple(push_lay.mu, vs).map_err(Error::Gkr)?;
    let [push_root, pull_root, count_root] = bus_gkr.roots;
    // Every read count is nonzero iff this product is (§sec:memchan); a zero would
    // let a read self-cancel and free its value from memory.
    if count_root == F192::ZERO {
        return Err(Error::ZeroCount);
    }
    // The two sides differ by the default-padding surplus; divide each out
    // (cross-multiplied) before comparing.
    let d_push = default_surplus(push, pad, alpha, gamma);
    let d_pull = default_surplus(pull, pad, alpha, gamma);
    if push_root * d_pull != pull_root * d_push {
        return Err(Error::Unbalanced);
    }

    // Framework blocks decompose as before; the tables' blocks become linear forms.
    // Each side's table share is DERIVED from `framework + Ṽ₀(ζ)` rather than checked
    // here, the batch's target being what pins it, so no table column is opened at ζ.
    let mut claims: Vec<ColumnClaim> = Vec::new();
    let mut forms = std::array::from_fn(|_| tables.iter().map(|&(_, n)| BusForm::new(n)).collect::<Vec<_>>());
    let sides: [(&[Block], &Layout, F192, F192); 3] = [
        (push, &push_lay, alpha, gamma),
        (pull, &pull_lay, alpha, gamma),
        (count, &count_lay, F192::ONE, F192::ZERO),
    ];
    let mut totals = [F192::ZERO; 3];
    for (s, &(blocks, lay, a, g)) in sides.iter().enumerate() {
        let framework = decompose_verify(
            blocks,
            lay,
            &bus_gkr.point,
            a,
            g,
            &owners[s],
            &mut forms[s],
            &mut claims,
            vs,
        )?;
        // What the tables owe this side: DERIVED, never read. A transmitted total
        // would be a free variable in its own check and would settle nothing; the
        // caller instead pins these against the batch's target.
        totals[s] = framework + bus_gkr.values[s];
    }

    // Bytecode = ONE polynomial (mirror of `prove_balance`); the shared push/
    // pull point means one set of public-column evaluations and ONE reduced
    // claim on the stacked bytecode multilinear.
    let (kbc, pv) = public_evals(push, &bus_gkr.point);
    for &v in &pv {
        vs.observe_scalar(v);
    }
    let s: Vec<F192> = (0..N_BYTECODE_SELECTORS).map(|_| vs.sample()).collect();
    let bytecode_claims = vec![BytecodeClaim {
        point: [&bus_gkr.point[..kbc], &s[..]].concat(),
        value: stacked_bytecode_value(&pv, &s),
    }];
    Ok(BusVerify {
        claims,
        bytecode_claims,
        count_root,
        point: bus_gkr.point,
        forms,
        totals,
    })
}

#[cfg(test)]
mod tests {
    use super::soundness_bits;

    #[test]
    fn bus_soundness_accounts_for_tuple_width() {
        assert!(soundness_bits(38, 12) >= crate::SECURITY_BITS);
        assert!(soundness_bits(59, 12) >= crate::SECURITY_BITS);
        assert!(soundness_bits(60, 12) < crate::SECURITY_BITS);
        assert!(soundness_bits(58, 16) < soundness_bits(58, 1));
    }
}
