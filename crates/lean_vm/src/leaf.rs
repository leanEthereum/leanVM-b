//! The bus: a single shared channel balanced by a grand product (§4.2–§4.4). Each
//! interaction wires a table's columns into width-`m` tuples and flushes them in a
//! direction; the bus balances when pushed and pulled tuples form the same
//! multiset. Push, pull, and count rows are each concatenated without internal
//! padding, padded once at the end, and checked by one batched product GKR. A
//! short quadratic sumcheck reduces the three terminal linear functionals to
//! ordinary evaluations of the committed columns.

use crate::gkr;
use crate::PAR_THRESHOLD;
use primitives::field::{mul_by_x, F128, G};
use primitives::multilinear::{fold_low_inplace, lagrange_eval, mle_eval, tri_nodes};
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
    /// The index column `g^z` (§5.3), free via the factored MLE.
    Index,
    /// A public column (the bytecode program, §8): not committed; both parties form
    /// its MLE directly, so it raises no claim.
    Public(Vec<F128>),
}

/// A flushing rule: `2^kappa` rows, each a tuple of coordinates. `real` is the
/// number of meaningful rows. Logical column padding still exists for the AIR
/// and PCS, but the grand-product leaf vector includes only these real rows.
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
    pub point: Vec<F128>,
    pub value: F128,
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
    ReductionRound {
        round: usize,
    },
    AssistFinal,
    /// The bus grinding nonce (before the multiset challenge γ) failed its PoW.
    PowFailed,
}

/// Proof-of-work bits to grind before the multiset challenge γ, so the bus
/// grand-product phase clears [`crate::SECURITY_BITS`]. The dominant
/// Schwartz–Zippel event is the push/pull fingerprint identity, whose degree
/// is at most `2^push_mu`. The same transcript also contains:
///
/// - the batched product-GKR degree-two sumchecks and combiners;
/// - a degree-two challenge batching the three terminal functionals;
/// - the new degree-two reduction sumcheck.
///
/// Push and pull have the same depth, while `count_mu ≤ push_mu`. Reserving
/// `push_mu + 2` bits gives ample union-bound slack for these lower-degree
/// checks. Grinding adds any deficit beyond the field's 128 bits.
///
/// The fingerprint challenge α is sampled AFTER the grind, so re-rolling it
/// also costs the PoW (besides the older argument that a fresh commitment to
/// re-roll α already costs `≥ 2^MIN_MU` Merkle hashes, above the target for
/// every admitted witness size).
fn grand_product_grinding_bits(push: &Layout, pull: &Layout, count: &Layout) -> u32 {
    assert_eq!(push.mu, pull.mu, "push/pull bus blocks are paired, so their layouts match");
    assert!(count.mu <= push.mu, "count sums fewer bus messages than push");
    // Keep one extra bit of slack for the tight-layout batching challenge and
    // reduction sumcheck.
    (crate::SECURITY_BITS + push.mu as u32 + 2).saturating_sub(128)
}

/// Concatenate every block's real rows in their canonical declaration order,
/// then pad once at the end.
pub fn layout(blocks: &[Block]) -> Layout {
    let mut offsets = Vec::with_capacity(blocks.len());
    let mut off = 0usize;
    for block in blocks {
        offsets.push(off);
        off += block.real;
    }
    let mu = crate::log2_ceil_usize(off.max(1));
    Layout { mu, offsets }
}

/// A non-constant coordinate as `(source, coefficient)`: its leaf contribution is
/// `coeff · source(z)`. `GCol` folds the `g` factor into the coefficient.
enum Term<'a> {
    Col(usize, F128),
    Index(F128),
    Public(&'a [F128], F128),
}

/// Build one side's leaf vector: block `b` row `z` holds `γ − Σ_i α^i c_i(z)`,
/// padded to `2^μ` with the identity `1`. The row-invariant `α`-power chain and
/// constant coordinates are folded once per block into `const_part`.
pub fn build_leaves(blocks: &[Block], lay: &Layout, cols: &[Column], alpha: F128, gamma: F128) -> Vec<F128> {
    let mut leaves = vec![F128::ONE; 1usize << lay.mu];
    let maxk = blocks.iter().map(|b| b.kappa).max().unwrap_or(0);
    let gpow = primitives::field::g_powers(1usize << maxk);
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
        let rows = blk.real;
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

#[derive(Clone)]
enum ReductionSource {
    One,
    Index { row_nu: usize },
    Column { group: usize },
    Public { group: usize },
}

#[derive(Clone)]
struct ProductTerm {
    source: ReductionSource,
    coefficient: F128,
}

#[derive(Clone)]
struct ReductionProduct {
    target_offset: usize,
    height: usize,
    row_nu: usize,
    terms: Vec<ProductTerm>,
}

#[derive(Clone)]
struct ColumnGroup {
    col: usize,
    kappa: usize,
    row_nu: usize,
}

struct PublicGroup<'a> {
    values: &'a [F128],
    kappa: usize,
    row_nu: usize,
}

struct ReductionPlan<'a> {
    products: Vec<ReductionProduct>,
    columns: Vec<ColumnGroup>,
    public: Vec<PublicGroup<'a>>,
    nu: usize,
}

struct ReductionWork {
    column: Vec<F128>,
    weight: Vec<F128>,
}

fn column_group(groups: &mut Vec<ColumnGroup>, col: usize, kappa: usize, row_nu: usize) -> usize {
    if let Some(group) =
        groups.iter().position(|group| group.col == col && group.kappa == kappa && group.row_nu == row_nu)
    {
        group
    } else {
        groups.push(ColumnGroup {
            col,
            kappa,
            row_nu,
        });
        groups.len() - 1
    }
}

#[allow(clippy::too_many_arguments)]
fn append_block_terms(
    block: &Block,
    side_weight: F128,
    alpha: F128,
    gamma: F128,
    columns: &mut Vec<ColumnGroup>,
    public_cursor: &mut usize,
    public: &[PublicGroup<'_>],
    terms: &mut Vec<ProductTerm>,
) {
    let row_nu = crate::log2_ceil_usize(block.real.max(1));
    let mut constant = gamma + F128::ONE;
    let mut alpha_power = F128::ONE;
    for coord in &block.coords {
        match coord {
            Coord::Const(value) => constant += alpha_power * *value,
            Coord::Index => terms.push(ProductTerm {
                source: ReductionSource::Index { row_nu },
                coefficient: side_weight * alpha_power,
            }),
            Coord::Col(col) | Coord::GCol(col) => {
                let group = column_group(columns, *col, block.kappa, row_nu);
                terms.push(ProductTerm {
                    source: ReductionSource::Column { group },
                    coefficient: side_weight
                        * alpha_power
                        * if matches!(coord, Coord::GCol(_)) { G } else { F128::ONE },
                });
            }
            Coord::Public(values) => {
                let group = *public_cursor;
                let known = &public[group];
                assert_eq!(known.kappa, block.kappa);
                assert_eq!(known.row_nu, row_nu);
                assert_eq!(known.values, values);
                terms.push(ProductTerm {
                    source: ReductionSource::Public { group },
                    coefficient: side_weight * alpha_power,
                });
                *public_cursor += 1;
            }
        }
        alpha_power *= alpha;
    }
    terms.push(ProductTerm {
        source: ReductionSource::One,
        coefficient: side_weight * constant,
    });
}

fn reduction_plan<'a>(
    push: &'a [Block],
    pull: &'a [Block],
    count: &'a [Block],
    layouts: [&Layout; 3],
    alpha: F128,
    gamma: F128,
    eta: F128,
) -> ReductionPlan<'a> {
    assert_eq!(push.len(), pull.len());
    let public: Vec<PublicGroup<'_>> = push
        .iter()
        .flat_map(|block| {
            let row_nu = crate::log2_ceil_usize(block.real.max(1));
            block.coords.iter().filter_map(move |coord| match coord {
                Coord::Public(values) => Some(PublicGroup {
                    values,
                    kappa: block.kappa,
                    row_nu,
                }),
                _ => None,
            })
        })
        .collect();
    let mut columns = Vec::new();
    for blocks in [push, pull, count] {
        for block in blocks {
            let row_nu = crate::log2_ceil_usize(block.real.max(1));
            for coord in &block.coords {
                if let Coord::Col(col) | Coord::GCol(col) = coord {
                    column_group(&mut columns, *col, block.kappa, row_nu);
                }
            }
        }
    }
    let mut products = Vec::with_capacity(push.len() + count.len());
    let (mut push_public, mut pull_public) = (0usize, 0usize);

    for block_index in 0..push.len() {
        assert_eq!(layouts[0].offsets[block_index], layouts[1].offsets[block_index]);
        assert_eq!(push[block_index].real, pull[block_index].real);
        let mut terms = Vec::new();
        append_block_terms(
            &push[block_index],
            F128::ONE,
            alpha,
            gamma,
            &mut columns,
            &mut push_public,
            &public,
            &mut terms,
        );
        append_block_terms(
            &pull[block_index],
            eta,
            alpha,
            gamma,
            &mut columns,
            &mut pull_public,
            &public,
            &mut terms,
        );
        products.push(ReductionProduct {
            target_offset: layouts[0].offsets[block_index],
            height: push[block_index].real,
            row_nu: crate::log2_ceil_usize(push[block_index].real.max(1)),
            terms,
        });
    }
    assert_eq!(push_public, public.len());
    assert_eq!(pull_public, public.len());

    let mut count_public = 0usize;
    for (block_index, block) in count.iter().enumerate() {
        let mut terms = Vec::new();
        append_block_terms(
            block,
            eta * eta,
            F128::ONE,
            F128::ZERO,
            &mut columns,
            &mut count_public,
            &[],
            &mut terms,
        );
        products.push(ReductionProduct {
            target_offset: layouts[2].offsets[block_index],
            height: block.real,
            row_nu: crate::log2_ceil_usize(block.real.max(1)),
            terms,
        });
    }
    assert_eq!(count_public, 0);
    let nu = products.iter().map(|product| product.row_nu).max().unwrap_or(0);
    ReductionPlan {
        products,
        columns,
        public,
        nu,
    }
}

fn product_round_message(column: &[F128], weight: &[F128]) -> [F128; 3] {
    let half = column.len() / 2;
    (0..half).fold([F128::ZERO; 3], |mut acc, row| {
        let (c0, c1) = (column[2 * row], column[2 * row + 1]);
        let (w0, w1) = (weight[2 * row], weight[2 * row + 1]);
        let cg = c0 + mul_by_x(c0 + c1);
        let wg = w0 + mul_by_x(w0 + w1);
        acc[0] += c0 * w0;
        acc[1] += c1 * w1;
        acc[2] += cg * wg;
        acc
    })
}

fn source_value(
    source: &ReductionSource,
    row: usize,
    plan: &ReductionPlan<'_>,
    cols: &[Column],
) -> F128 {
    match *source {
        ReductionSource::One => F128::ONE,
        ReductionSource::Index { .. } => primitives::field::g_pow(row),
        ReductionSource::Column { group } => cols[plan.columns[group].col][row],
        ReductionSource::Public { group } => plan.public[group].values[row],
    }
}

fn index_eval(point: &[F128]) -> F128 {
    let mut power = G;
    point.iter().fold(F128::ONE, |acc, &coordinate| {
        let next = acc * (F128::ONE + coordinate + power * coordinate);
        power *= power;
        next
    })
}

fn endpoint_bits(value: usize, len: usize) -> Vec<F128> {
    (0..len)
        .map(|bit| F128::new(((value >> bit) & 1) as u64, 0))
        .collect()
}

fn assist_eval_query(
    row_point: &[F128],
    index_point: &[F128],
    interval_bits: &[(Vec<F128>, Vec<F128>)],
    coefficients: &[F128],
    prefix: &[F128],
    round: usize,
    node: F128,
) -> F128 {
    let start_len = interval_bits[0].0.len();
    interval_bits
        .iter()
        .zip(coefficients)
        .fold(F128::ZERO, |acc, ((start_bits, length_bits), &coefficient)| {
            let mut start = start_bits.clone();
            let mut length = length_bits.clone();
            for (coordinate, &value) in prefix.iter().enumerate() {
                if coordinate < start_len {
                    start[coordinate] = value;
                } else {
                    length[coordinate - start_len] = value;
                }
            }
            if round < start_len {
                start[round] = node;
            } else {
                length[round - start_len] = node;
            }
            let bit = if round < start_len {
                start_bits[round]
            } else {
                length_bits[round - start_len]
            };
            let prefix_equality = prefix.iter().enumerate().fold(
                F128::ONE,
                |weight, (coordinate, &challenge)| {
                    let parameter_bit = if coordinate < start_len {
                        start_bits[coordinate]
                    } else {
                        length_bits[coordinate - start_len]
                    };
                    weight * (F128::ONE + challenge + parameter_bit)
                },
            );
            acc + coefficient
                * prefix_equality
                * (F128::ONE + node + bit)
                * ::pcs::jagged::indicator_eval_with_start_length_points(
                    row_point,
                    index_point,
                    &start,
                    &length,
                )
        })
}

fn prove_overlap_assist(
    products: &[ReductionProduct],
    coefficients: &[F128],
    row_point: &[F128],
    index_point: &[F128],
    mut claim: F128,
    ps: &mut ProverState,
) {
    let start_len = index_point.len();
    let length_len = products.iter().map(|product| product.row_nu).max().unwrap() + 1;
    let interval_bits: Vec<_> = products
        .iter()
        .map(|product| {
            (
                endpoint_bits(product.target_offset, start_len),
                endpoint_bits(product.height, length_len),
            )
        })
        .collect();
    let mut prefix = Vec::with_capacity(start_len + length_len);
    let nodes = tri_nodes();
    for round in 0..start_len + length_len {
        let at_zero =
            assist_eval_query(row_point, index_point, &interval_bits, coefficients, &prefix, round, F128::ZERO);
        let at_generator = assist_eval_query(row_point, index_point, &interval_bits, coefficients, &prefix, round, G);
        ps.add_scalars(&[at_zero, at_generator]);
        let challenge = ps.sample();
        let at_one = claim + at_zero;
        claim = lagrange_eval(&nodes, &[at_zero, at_one, at_generator], challenge);
        prefix.push(challenge);
    }
    let batch_weight = interval_bits
        .iter()
        .zip(coefficients)
        .fold(F128::ZERO, |acc, ((start, length), &coefficient)| {
            let point = start.iter().chain(length);
            acc + coefficient
                * point
                    .zip(&prefix)
                    .fold(F128::ONE, |weight, (&bit, &coordinate)| {
                        weight * (F128::ONE + bit + coordinate)
                    })
        });
    let overlap = ::pcs::jagged::indicator_eval_with_start_length_points(
        row_point,
        index_point,
        &prefix[..start_len],
        &prefix[start_len..],
    );
    assert_eq!(claim, overlap * batch_weight);
}

fn verify_overlap_assist(
    products: &[ReductionProduct],
    coefficients: &[F128],
    row_point: &[F128],
    index_point: &[F128],
    mut claim: F128,
    vs: &mut VerifierState,
) -> Result<(), Error> {
    let start_len = index_point.len();
    let length_len = products.iter().map(|product| product.row_nu).max().unwrap() + 1;
    let nodes = tri_nodes();
    let mut point = Vec::with_capacity(start_len + length_len);
    for _round in 0..start_len + length_len {
        let message = vs.next_scalars(2).map_err(|_| Error::Truncated)?;
        let at_one = claim + message[0];
        let challenge = vs.sample();
        claim = lagrange_eval(&nodes, &[message[0], at_one, message[1]], challenge);
        point.push(challenge);
    }
    let mut batch_weight = F128::ZERO;
    for (product, &coefficient) in products.iter().zip(coefficients) {
        let start = product.target_offset;
        let length = product.height;
        let mut equality = F128::ONE;
        for (coordinate, &challenge) in point.iter().enumerate() {
            let bit = if coordinate < start_len {
                (start >> coordinate) & 1
            } else {
                (length >> (coordinate - start_len)) & 1
            };
            equality *= F128::ONE + F128::new(bit as u64, 0) + challenge;
        }
        batch_weight += coefficient * equality;
    }
    let overlap = ::pcs::jagged::indicator_eval_with_start_length_points(
        row_point,
        index_point,
        &point[..start_len],
        &point[start_len..],
    );
    if claim != overlap * batch_weight {
        return Err(Error::AssistFinal);
    }
    Ok(())
}

struct ReductionResult {
    claims: Vec<ColumnClaim>,
    public_point: Vec<F128>,
    public_values: Vec<F128>,
}

#[allow(clippy::too_many_arguments)]
fn prove_tight_reduction(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    layouts: [&Layout; 3],
    gkr_values: [F128; 3],
    target_point: &[F128],
    alpha: F128,
    gamma: F128,
    cols: &[Column],
    ps: &mut ProverState,
) -> ReductionResult {
    let eta = ps.sample();
    let plan = reduction_plan(push, pull, count, layouts, alpha, gamma, eta);
    let target_eq = primitives::multilinear::build_eq(target_point);

    let mut work: Vec<ReductionWork> = plan
        .products
        .clone()
        .into_par_iter()
        .map(|product| {
            let local_n = 1usize << product.row_nu;
            let column = (0..local_n)
                .map(|row| {
                    product.terms.iter().fold(F128::ZERO, |acc, term| {
                        acc + term.coefficient * source_value(&term.source, row, &plan, cols)
                    })
                })
                .collect();
            let mut weight = vec![F128::ZERO; local_n];
            for row in 0..product.height {
                weight[row] = target_eq[product.target_offset + row];
            }
            ReductionWork { column, weight }
        })
        .collect();

    let mut claim =
        gkr_values[0] + F128::ONE + eta * (gkr_values[1] + F128::ONE) + eta * eta * (gkr_values[2] + F128::ONE);
    let nodes = tri_nodes();
    let mut rho = Vec::with_capacity(plan.nu);
    for _ in 0..plan.nu {
        let msg = work
            .par_iter()
            .map(|entry| {
                if entry.column.len() == 1 {
                    let value = entry.column[0] * entry.weight[0];
                    [value, F128::ZERO, (F128::ONE + G) * value]
                } else {
                    product_round_message(&entry.column, &entry.weight)
                }
            })
            .reduce(
                || [F128::ZERO; 3],
                |a, b| [a[0] + b[0], a[1] + b[1], a[2] + b[2]],
            );
        assert_eq!(msg[0] + msg[1], claim);
        ps.add_scalars(&msg);
        let challenge = ps.sample();
        claim = lagrange_eval(&nodes, &msg, challenge);
        rho.push(challenge);
        work.par_iter_mut().for_each(|entry| {
            if entry.column.len() == 1 {
                entry.weight[0] *= F128::ONE + challenge;
            } else {
                fold_low_inplace(&mut entry.column, challenge);
                fold_low_inplace(&mut entry.weight, challenge);
            }
        });
    }

    let mut column_values = Vec::with_capacity(plan.columns.len());
    let mut claims = Vec::with_capacity(plan.columns.len());
    for group in &plan.columns {
        let mut point = rho[..group.row_nu].to_vec();
        point.resize(group.kappa, F128::ZERO);
        let value = mle_eval(&cols[group.col][..1usize << group.kappa], &point);
        ps.add_scalar(value);
        column_values.push(value);
        claims.push(ColumnClaim {
            col: group.col,
            point,
            value,
        });
    }

    let mut public_values = Vec::with_capacity(plan.public.len());
    for group in &plan.public {
        let mut point = rho[..group.row_nu].to_vec();
        point.resize(group.kappa, F128::ZERO);
        let value = mle_eval(group.values, &point);
        ps.observe_scalar(value);
        public_values.push(value);
    }

    let product_values: Vec<F128> = plan
        .products
        .iter()
        .map(|product| {
            product.terms.iter().fold(F128::ZERO, |acc, term| {
                let source = match term.source {
                    ReductionSource::One => F128::ONE,
                    ReductionSource::Index { row_nu } => index_eval(&rho[..row_nu]),
                    ReductionSource::Column { group } => column_values[group],
                    ReductionSource::Public { group } => public_values[group],
                };
                acc + term.coefficient * source
            })
        })
        .collect();
    prove_overlap_assist(&plan.products, &product_values, &rho, target_point, claim, ps);

    let public_point = plan
        .public
        .first()
        .map(|group| {
            let mut point = rho[..group.row_nu].to_vec();
            point.resize(group.kappa, F128::ZERO);
            point
        })
        .unwrap_or_default();
    ReductionResult {
        claims,
        public_point,
        public_values,
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_tight_reduction(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    layouts: [&Layout; 3],
    gkr_values: [F128; 3],
    target_point: &[F128],
    alpha: F128,
    gamma: F128,
    vs: &mut VerifierState,
) -> Result<ReductionResult, Error> {
    let eta = vs.sample();
    let plan = reduction_plan(push, pull, count, layouts, alpha, gamma, eta);
    let mut claim =
        gkr_values[0] + F128::ONE + eta * (gkr_values[1] + F128::ONE) + eta * eta * (gkr_values[2] + F128::ONE);

    let nodes = tri_nodes();
    let mut rho = Vec::with_capacity(plan.nu);
    for round in 0..plan.nu {
        let msg = vs.next_scalars(3).map_err(|_| Error::Truncated)?;
        if msg[0] + msg[1] != claim {
            return Err(Error::ReductionRound { round });
        }
        let challenge = vs.sample();
        claim = lagrange_eval(&nodes, &msg, challenge);
        rho.push(challenge);
    }

    let mut column_values = Vec::with_capacity(plan.columns.len());
    let mut claims = Vec::with_capacity(plan.columns.len());
    for group in &plan.columns {
        let value = vs.next_scalar().map_err(|_| Error::Truncated)?;
        let mut point = rho[..group.row_nu].to_vec();
        point.resize(group.kappa, F128::ZERO);
        column_values.push(value);
        claims.push(ColumnClaim {
            col: group.col,
            point,
            value,
        });
    }

    let mut public_values = Vec::with_capacity(plan.public.len());
    for group in &plan.public {
        let mut point = rho[..group.row_nu].to_vec();
        point.resize(group.kappa, F128::ZERO);
        let value = mle_eval(group.values, &point);
        vs.observe_scalar(value);
        public_values.push(value);
    }

    let product_values: Vec<F128> = plan
        .products
        .iter()
        .map(|product| {
            product.terms.iter().fold(F128::ZERO, |acc, term| {
                let source = match term.source {
                    ReductionSource::One => F128::ONE,
                    ReductionSource::Index { row_nu } => index_eval(&rho[..row_nu]),
                    ReductionSource::Column { group } => column_values[group],
                    ReductionSource::Public { group } => public_values[group],
                };
                acc + term.coefficient * source
            })
        })
        .collect();
    verify_overlap_assist(&plan.products, &product_values, &rho, target_point, claim, vs)?;

    let public_point = plan
        .public
        .first()
        .map(|group| {
            let mut point = rho[..group.row_nu].to_vec();
            point.resize(group.kappa, F128::ZERO);
            point
        })
        .unwrap_or_default();
    Ok(ReductionResult {
        claims,
        public_point,
        public_values,
    })
}

/// One reduced claim on the bytecode polynomial. The eight public encoding
/// columns (opcode plus seven operand/immediate slots), stacked along three selector bits, form
/// ONE multilinear polynomial B̃ in `κ_bc + 3` variables; after the
/// reduction both parties absorb the eight per-column evaluations (push and
/// pull share the row point, so the columns are evaluated once), sample
/// three selector challenges `s`, and reduce the eight values to
/// `B̃(ζ_lo, s) = Σ_c eq(s, c)·v_c`. Natively the claim is
/// true by construction (the verifier evaluated the columns itself); a
/// recursive verifier defers exactly this one claim to its public input.
#[derive(Clone, Debug)]
pub struct BytecodeClaim {
    /// `ζ_side_lo ++ s` — a point in `κ_bc + 3` variables.
    pub point: Vec<F128>,
    /// `B̃(point)`.
    pub value: F128,
}

/// The public (bytecode) coordinate evaluations of a side at a row point,
/// block/coord order, with the bytecode block's `κ`.
pub fn public_evals(blocks: &[Block], point: &[F128]) -> (usize, Vec<F128>) {
    let mut kappa = 0;
    let mut out = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Public(vals) = c {
                kappa = blk.kappa;
                out.push(mle_eval(vals, &point[..blk.kappa]));
            }
        }
    }
    (kappa, out)
}

/// The stacked bytecode polynomial as a dense table: the eight public encoding
/// columns along three selector bits (`B̃`'s evaluations on the cube). This is
/// the polynomial [`BytecodeClaim`]s are claims about; the outermost native
/// verifier evaluates it here.
pub fn stacked_bytecode_table(blocks: &[Block]) -> Vec<F128> {
    let mut kbc = 0;
    let mut cols: Vec<&Vec<F128>> = Vec::new();
    for blk in blocks {
        for c in &blk.coords {
            if let Coord::Public(vals) = c {
                kbc = blk.kappa;
                cols.push(vals);
            }
        }
    }
    let mut table = vec![F128::ZERO; 8 << kbc];
    for (c_idx, vals) in cols.iter().enumerate() {
        assert_eq!(vals.len(), 1 << kbc);
        table[(c_idx << kbc)..((c_idx + 1) << kbc)].copy_from_slice(vals);
    }
    table
}

/// `Σ_c eq(s, c)·v_c`: one side's public-column evaluations reduced to the
/// stacked-polynomial value at selector point `s`.
pub fn stacked_bytecode_value(evals: &[F128], s: &[F128; 3]) -> F128 {
    let mut acc = F128::ZERO;
    for (c, &v) in evals.iter().enumerate() {
        let mut e = F128::ONE;
        for (t, &st) in s.iter().enumerate() {
            e *= if (c >> t) & 1 == 1 { st } else { F128::ONE + st };
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
    // blocks, and offsets are unchanged; `build_leaves` fills the cube with
    // `1`), so all THREE trees share one RLC-batched GKR and one point ζ.
    count_lay.mu = push_lay.mu;
    let gamma = ps.sample();
    // Independent leaf vectors; build concurrently. The count channel's leaf is the
    // count itself (a single `Col`, `γ=0`, `α=1`), so its root is the product of all counts.
    let (push_leaves, (pull_leaves, count_leaves)) = rayon::join(
        || build_leaves(push, &push_lay, cols, alpha, gamma),
        || {
            rayon::join(
                || build_leaves(pull, &pull_lay, cols, alpha, gamma),
                || build_leaves(count, &count_lay, cols, F128::ONE, F128::ZERO),
            )
        },
    );
    // All three trees run as ONE RLC-batched GKR (equal μ: push/pull match
    // block-for-block, count is padded), so every claim lands on ONE point ζ.
    let bus_gkr = gkr::prove_product_triple([push_leaves, pull_leaves, count_leaves], ps);

    // Batch the three complete leaf claims and reduce them to ordinary source
    // evaluations. Constants, indices, and public bytecode participate in the
    // same reduction, so no interval mass is evaluated separately.
    let reduction = prove_tight_reduction(
        push,
        pull,
        count,
        [&push_lay, &pull_lay, &count_lay],
        bus_gkr.values,
        &bus_gkr.point,
        alpha,
        gamma,
        cols,
        ps,
    );

    // The eight public source evaluations were already absorbed before the
    // overlap assist. Reduce them to one deferred bytecode claim.
    let s = [ps.sample(), ps.sample(), ps.sample()];
    let bytecode_claims = vec![BytecodeClaim {
        point: [&reduction.public_point[..], &s[..]].concat(),
        value: stacked_bytecode_value(&reduction.public_values, &s),
    }];
    (reduction.claims, bytecode_claims)
}

/// What [`verify_balance`] establishes: the per-column claims to open, the
/// reduced bytecode claim (a one-element vec in practice: push and pull share
/// ζ), and the count-channel root (nonzero; recursion
/// guests prove that via a hinted inverse).
pub struct BusVerify {
    pub claims: Vec<ColumnClaim>,
    pub bytecode_claims: Vec<BytecodeClaim>,
    pub count_root: F128,
}

/// Verify the bus balances, oracle-free (the prover's committed values arrive on
/// the stream and are certified by `pcs`). Returns the per-column claims to open.
pub fn verify_balance(
    push: &[Block],
    pull: &[Block],
    count: &[Block],
    _pad: &[F128],
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
    if count_root == F128::ZERO {
        return Err(Error::ZeroCount);
    }
    if push_root != pull_root {
        return Err(Error::Unbalanced);
    }

    let reduction = verify_tight_reduction(
        push,
        pull,
        count,
        [&push_lay, &pull_lay, &count_lay],
        bus_gkr.values,
        &bus_gkr.point,
        alpha,
        gamma,
        vs,
    )?;

    let s = [vs.sample(), vs.sample(), vs.sample()];
    let bytecode_claims = vec![BytecodeClaim {
        point: [&reduction.public_point[..], &s[..]].concat(),
        value: stacked_bytecode_value(&reduction.public_values, &s),
    }];
    Ok(BusVerify {
        claims: reduction.claims,
        bytecode_claims,
        count_root,
    })
}
