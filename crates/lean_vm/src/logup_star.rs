//! logup* indexed lookups for the VM's memory and public bytecode tables.

use std::collections::HashMap;

use crate::frac_gkr;
use crate::leaf::{ColumnClaim, Coord};
use crate::transcript::{ProverState, VerifierState};
use crate::witness::{self, Column, Placement};
use primitives::field::{F64, F192, g_pow, index_mle};
use primitives::multilinear::{eq_table, mle_eval};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Family {
    Memory,
    Bytecode,
}

#[derive(Clone, Debug)]
pub struct AccessBlock {
    /// The access site this dyadic slice belongs to.
    pub site: usize,
    /// Variables in this aligned dyadic source slice.
    pub kappa: usize,
    /// First row in the source table column.
    pub start: usize,
    pub index: Coord,
    /// Memory: three limbs. Bytecode: opcode plus five operand/flag slots.
    pub values: Vec<Coord>,
}

#[derive(Clone, Debug)]
pub struct AccessSite {
    /// Instruction-table index supplying this access.
    pub table: usize,
    /// Log-size of the padded source table.
    pub kappa: usize,
    /// Number of real source rows included in the lookup.
    pub real: usize,
    pub index: Coord,
    /// Memory: three limbs. Bytecode: opcode plus five operand/flag slots.
    pub values: Vec<Coord>,
}

#[derive(Clone, Debug)]
pub struct AccessLayout {
    pub family: Family,
    pub sites: Vec<AccessSite>,
    pub blocks: Vec<AccessBlock>,
    pub offsets: Vec<usize>,
    pub mu: usize,
}

impl AccessLayout {
    pub fn new(family: Family, sites: Vec<AccessSite>) -> Self {
        let mut blocks = Vec::new();
        for (site, access) in sites.iter().enumerate() {
            for (start, kappa) in dyadic_prefix(access.real) {
                blocks.push(AccessBlock {
                    site,
                    kappa,
                    start,
                    index: access.index.clone(),
                    values: access.values.clone(),
                });
            }
        }
        let mut order: Vec<usize> = (0..blocks.len()).collect();
        order.sort_by(|&a, &b| blocks[b].kappa.cmp(&blocks[a].kappa).then(a.cmp(&b)));
        let mut offsets = vec![0; blocks.len()];
        let mut off = 0usize;
        for i in order {
            offsets[i] = off;
            off += 1 << blocks[i].kappa;
        }
        let mu = crate::log2_ceil_usize(off.max(1));
        Self {
            family,
            sites,
            blocks,
            offsets,
            mu,
        }
    }

    /// Materialize the virtual access stack for the prover. The unused tail is
    /// the valid lookup `(g^0, table[0])`.
    pub fn materialize(&self, cols: &[Column], table_len: usize) -> Materialized {
        let len = 1usize << self.mu;
        let mut indices = vec![F192::ONE; len];
        let mut targets = vec![0usize; len];
        let reverse: HashMap<F64, usize> = primitives::field::g_powers(table_len)
            .into_iter()
            .enumerate()
            .map(|(i, x)| (x, i))
            .collect();

        for (b, block) in self.blocks.iter().enumerate() {
            let offset = self.offsets[b];
            for z in 0..1usize << block.kappa {
                let row = block.start + z;
                let i = coord_row(&block.index, cols, row);
                indices[offset + z] = F192::from(i);
                targets[offset + z] = *reverse.get(&i).expect("lookup index must address its table");
            }
        }
        Materialized { indices, targets }
    }

    pub fn virtual_eval_prove(
        &self,
        cols: &[Column],
        point: &[F192],
        dummy: F192,
        ps: &mut ProverState,
    ) -> (F192, Vec<ColumnClaim>) {
        let expected = virtual_index_formula(self, point, dummy, |coord, start, p| {
            coord_eval_local(coord, cols, start, p)
        });
        let mut claims = Vec::new();
        let checked = virtual_index_formula(self, point, dummy, |coord, start, p| match coord {
            Coord::Col(col) | Coord::GCol(col, _) => {
                let v = mle_eval(&cols[*col][start..start + (1 << p.len())], p);
                ps.add_scalar(v);
                claims.push(ColumnClaim {
                    col: *col,
                    start,
                    point: p.to_vec(),
                    value: v,
                });
                match coord {
                    Coord::GCol(_, k) => v.mul_base(g_pow(*k as usize)),
                    _ => v,
                }
            }
            _ => coord_eval_local(coord, cols, start, p),
        });
        debug_assert_eq!(expected, checked);
        (expected, claims)
    }

    pub fn virtual_eval_verify(
        &self,
        point: &[F192],
        dummy: F192,
        vs: &mut VerifierState,
    ) -> Result<(F192, Vec<ColumnClaim>), Error> {
        let mut opened = Vec::new();
        for block in &self.blocks {
            for coord in std::slice::from_ref(&block.index) {
                if matches!(coord, Coord::Col(_) | Coord::GCol(_, _)) {
                    opened.push(vs.next_scalar().map_err(|_| Error::Truncated)?);
                }
            }
        }
        let mut opened = opened.into_iter();
        let mut claims = Vec::new();
        let result = virtual_index_formula(self, point, dummy, |coord, start, p| match coord {
            Coord::Col(col) | Coord::GCol(col, _) => {
                let v = opened.next().expect("one pre-read value per committed coordinate");
                claims.push(ColumnClaim {
                    col: *col,
                    start,
                    point: p.to_vec(),
                    value: v,
                });
                match coord {
                    Coord::GCol(_, k) => v.mul_base(g_pow(*k as usize)),
                    _ => v,
                }
            }
            Coord::Const(v) => F192::from(*v),
            _ => panic!("unsupported lookup coordinate"),
        });
        debug_assert!(opened.next().is_none());
        Ok((result, claims))
    }

    /// Build the transparent numerator that batches one real-prefix value
    /// evaluation per access site. The site values must already be transcript
    /// bound; `gammas` are sampled afterward.
    pub fn batch_values(&self, table_points: &[Vec<F192>], site_values: &[F192], gammas: &[F192]) -> BatchedValues {
        assert_eq!(site_values.len(), self.sites.len());
        assert_eq!(gammas.len(), self.sites.len());
        let mut weights = vec![F192::ZERO; 1usize << self.mu];
        let mut claim = F192::ZERO;
        let eqs: Vec<Vec<F192>> = table_points.iter().map(|point| eq_table(point)).collect();
        for (site, access) in self.sites.iter().enumerate() {
            assert_eq!(table_points[access.table].len(), access.kappa);
            assert!(access.real <= 1usize << access.kappa);
            let gamma = gammas[site];
            claim += gamma * site_values[site];
            for (block, &offset) in self.blocks.iter().zip(&self.offsets) {
                if block.site != site {
                    continue;
                }
                let src = &eqs[access.table][block.start..block.start + (1usize << block.kappa)];
                for (dst, &weight) in weights[offset..offset + src.len()].iter_mut().zip(src) {
                    *dst += gamma * weight;
                }
            }
        }
        BatchedValues { weights, claim }
    }
}

/// Decompose `[0, real)` into aligned dyadic slices.
pub fn dyadic_prefix(mut real: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut start = 0usize;
    while real != 0 {
        let kappa = real.ilog2() as usize;
        let len = 1usize << kappa;
        out.push((start, kappa));
        start += len;
        real -= len;
    }
    out
}

pub struct Materialized {
    pub indices: Vec<F192>,
    pub targets: Vec<usize>,
}

impl Materialized {
    pub fn pushforward(&self, weights: &[F192], table_len: usize) -> Vec<F192> {
        assert_eq!(weights.len(), self.targets.len());
        let mut result = vec![F192::ZERO; table_len];
        for (&target, &weight) in self.targets.iter().zip(weights) {
            result[target] += weight;
        }
        result
    }
}

pub struct BatchedValues {
    pub weights: Vec<F192>,
    pub claim: F192,
}

#[derive(Clone, Debug)]
pub struct PushforwardLayout {
    pub placements: Vec<Placement>,
    pub mu: usize,
    pub mem_vars: usize,
    pub bytecode_vars: usize,
}

impl PushforwardLayout {
    pub fn new(mem_vars: usize, bytecode_vars: usize) -> Self {
        let kappas = vec![Some(mem_vars); 3]
            .into_iter()
            .chain(vec![Some(bytecode_vars); 3])
            .collect::<Vec<_>>();
        let (placements, mu) = witness::placements_of(&kappas);
        Self {
            placements,
            mu,
            mem_vars,
            bytecode_vars,
        }
    }

    fn base(&self, family: Family) -> usize {
        match family {
            Family::Memory => 0,
            Family::Bytecode => 3,
        }
    }
}

pub struct PushforwardWitness {
    pub layout: PushforwardLayout,
    pub cols: Vec<Column>,
    pub q: Vec<F64>,
}

impl PushforwardWitness {
    pub fn new(memory: &[F192], bytecode: &[F192]) -> Self {
        let layout = PushforwardLayout::new(memory.len().ilog2() as usize, bytecode.len().ilog2() as usize);
        let mut cols = Vec::with_capacity(6);
        for values in [memory, bytecode] {
            cols.push(values.iter().map(|v| F64(v.c0)).collect());
            cols.push(values.iter().map(|v| F64(v.c1)).collect());
            cols.push(values.iter().map(|v| F64(v.c2)).collect());
        }
        let q = witness::stack_q(&cols, &layout.placements, layout.mu);
        Self { layout, cols, q }
    }

    pub fn claim_prove(
        &self,
        family: Family,
        point: &[F192],
        full: F192,
        ps: &mut ProverState,
    ) -> Vec<crate::pcs::SlotClaim> {
        let base = self.layout.base(family);
        let lo = mle_eval(&self.cols[base], point);
        let hi = mle_eval(&self.cols[base + 1], point);
        ps.add_scalars(&[lo, hi]);
        let claims = push_claims(&self.layout, family, point, full, lo, hi);
        let top = mle_eval(&self.cols[base + 2], point);
        debug_assert_eq!(
            full,
            lo + F192::Y * hi + F192::Y * F192::Y * top,
            "pushforward limb decomposition"
        );
        claims
    }
}

pub fn push_claim_verify(
    layout: &PushforwardLayout,
    family: Family,
    point: &[F192],
    full: F192,
    vs: &mut VerifierState,
) -> Result<Vec<crate::pcs::SlotClaim>, Error> {
    let lo = vs.next_scalar().map_err(|_| Error::Truncated)?;
    let hi = vs.next_scalar().map_err(|_| Error::Truncated)?;
    Ok(push_claims(layout, family, point, full, lo, hi))
}

fn push_claims(
    layout: &PushforwardLayout,
    family: Family,
    point: &[F192],
    full: F192,
    lo: F192,
    hi: F192,
) -> Vec<crate::pcs::SlotClaim> {
    let top = (full + lo + F192::Y * hi) * (F192::Y * F192::Y).inv();
    let base = layout.base(family);
    [lo, hi, top]
        .into_iter()
        .enumerate()
        .map(|(i, value)| crate::pcs::SlotClaim::Point {
            offset: layout.placements[base + i].offset,
            low_point: point.to_vec(),
            value,
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Fraction(frac_gkr::Error),
    RootMismatch,
    NumeratorMismatch,
    AccessIndexMismatch,
    TableIndexMismatch,
    TableMismatch,
}

impl From<frac_gkr::Error> for Error {
    fn from(value: frac_gkr::Error) -> Self {
        Self::Fraction(value)
    }
}

pub struct ProveOutput {
    pub main_claims: Vec<ColumnClaim>,
    pub push_claims: Vec<crate::pcs::SlotClaim>,
    pub bytecode_table_claim: Option<(Vec<F192>, F192)>,
}

pub fn prove_lookup(
    family: Family,
    layout: &AccessLayout,
    materialized: &Materialized,
    batched: &BatchedValues,
    table: Vec<F192>,
    pushforward: &[F192],
    push_witness: &PushforwardWitness,
    theta: F192,
    index_dummy: F192,
    cols: &[Column],
    ps: &mut ProverState,
) -> ProveOutput {
    let c = ps.sample();
    let left_num = batched.weights.clone();
    let left_den = materialized.indices.iter().map(|&i| c + i).collect();
    let right_den = (0..table.len()).map(|j| c + F192::from(g_pow(j))).collect();
    let left = frac_gkr::Circuit::new(left_num, left_den);
    let right = frac_gkr::Circuit::new(pushforward.to_vec(), right_den);
    let (ln, ld) = left.root();
    let (rn, rd) = right.root();
    debug_assert_eq!(ln * rd, rn * ld);
    ps.add_scalars(&[ln, ld, rn, rd]);
    let left_out = left.prove(ps);
    let right_out = right.prove(ps);

    debug_assert_eq!(left_out.num, mle_eval_ext(&batched.weights, &left_out.point));
    let index_eval = c + left_out.den;
    let (opened_index, mut main_claims) = layout.virtual_eval_prove(cols, &left_out.point, index_dummy, ps);
    debug_assert_eq!(opened_index, index_eval);

    debug_assert_eq!(right_out.den, c + index_mle(&right_out.point));
    let mut push_claims = push_witness.claim_prove(family, &right_out.point, right_out.num, ps);

    let ip = frac_gkr::prove_inner_product(table.clone(), pushforward.to_vec(), batched.claim, ps);
    let bytecode_table_claim = match family {
        Family::Memory => {
            let lo = mle_eval(&cols[crate::cpu::MEM_LO], &ip.point);
            let hi = mle_eval(&cols[crate::cpu::MEM_HI], &ip.point);
            let top = mle_eval(&cols[crate::cpu::MEM_TOP], &ip.point);
            ps.add_scalars(&[lo, hi, top]);
            debug_assert_eq!(ip.num, lo + theta * hi + theta * theta * top);
            for (col, value) in [
                (crate::cpu::MEM_LO, lo),
                (crate::cpu::MEM_HI, hi),
                (crate::cpu::MEM_TOP, top),
            ] {
                main_claims.push(ColumnClaim {
                    col,
                    start: 0,
                    point: ip.point.clone(),
                    value,
                });
            }
            None
        }
        Family::Bytecode => Some((ip.point.clone(), ip.num)),
    };
    push_claims.extend(push_witness.claim_prove(family, &ip.point, ip.den, ps));
    debug_assert_eq!(index_eval, c + left_out.den);
    ProveOutput {
        main_claims,
        push_claims,
        bytecode_table_claim,
    }
}

pub fn verify_lookup(
    family: Family,
    layout: &AccessLayout,
    batched: &BatchedValues,
    table: &[F192],
    table_vars: usize,
    push_layout: &PushforwardLayout,
    theta: F192,
    index_dummy: F192,
    vs: &mut VerifierState,
) -> Result<ProveOutput, Error> {
    let c = vs.sample();
    let roots = vs.next_scalars(4).map_err(|_| Error::Truncated)?;
    if roots[0] * roots[3] != roots[2] * roots[1] {
        return Err(Error::RootMismatch);
    }
    let left = frac_gkr::verify(layout.mu, roots[0], roots[1], vs)?;
    let right = frac_gkr::verify(table_vars, roots[2], roots[3], vs)?;
    if left.num != mle_eval_ext(&batched.weights, &left.point) {
        return Err(Error::NumeratorMismatch);
    }
    let expected_index = c + left.den;
    let (index, mut main_claims) = layout.virtual_eval_verify(&left.point, index_dummy, vs)?;
    if index != expected_index {
        return Err(Error::AccessIndexMismatch);
    }
    if right.den != c + index_mle(&right.point) {
        return Err(Error::TableIndexMismatch);
    }
    let mut push_claims = push_claim_verify(push_layout, family, &right.point, right.num, vs)?;

    let ip = frac_gkr::verify_inner_product(table_vars, batched.claim, vs)?;
    let bytecode_table_claim = match family {
        Family::Memory => {
            let lo = vs.next_scalar().map_err(|_| Error::Truncated)?;
            let hi = vs.next_scalar().map_err(|_| Error::Truncated)?;
            let top = vs.next_scalar().map_err(|_| Error::Truncated)?;
            if ip.num != lo + theta * hi + theta * theta * top {
                return Err(Error::TableMismatch);
            }
            for (col, value) in [
                (crate::cpu::MEM_LO, lo),
                (crate::cpu::MEM_HI, hi),
                (crate::cpu::MEM_TOP, top),
            ] {
                main_claims.push(ColumnClaim {
                    col,
                    start: 0,
                    point: ip.point.clone(),
                    value,
                });
            }
            None
        }
        Family::Bytecode => {
            let expected = mle_eval_ext(table, &ip.point);
            if expected != ip.num {
                return Err(Error::TableMismatch);
            }
            Some((ip.point.clone(), ip.num))
        }
    };
    push_claims.extend(push_claim_verify(push_layout, family, &ip.point, ip.den, vs)?);
    Ok(ProveOutput {
        main_claims,
        push_claims,
        bytecode_table_claim,
    })
}

pub fn mle_eval_ext(table: &[F192], point: &[F192]) -> F192 {
    assert_eq!(table.len(), 1 << point.len());
    let mut values = table.to_vec();
    for &r in point {
        let half = values.len() / 2;
        for i in 0..half {
            values[i] = primitives::multilinear::interp(values[2 * i], values[2 * i + 1], r);
        }
        values.truncate(half);
    }
    values[0]
}

fn virtual_index_formula<F>(layout: &AccessLayout, point: &[F192], dummy: F192, mut eval: F) -> F192
where
    F: FnMut(&Coord, usize, &[F192]) -> F192,
{
    assert_eq!(point.len(), layout.mu);
    let mut acc = F192::ZERO;
    let mut selector_sum = F192::ZERO;
    for (b, block) in layout.blocks.iter().enumerate() {
        let low = &point[..block.kappa];
        let selector = layout.offsets[b] >> block.kappa;
        let weight = selector_weight(selector, &point[block.kappa..]);
        selector_sum += weight;
        let block_value = eval(&block.index, block.start, low);
        acc += weight * block_value;
    }
    acc + (F192::ONE + selector_sum) * dummy
}

fn coord_eval_local(coord: &Coord, cols: &[Column], start: usize, point: &[F192]) -> F192 {
    match coord {
        Coord::Const(v) => F192::from(*v),
        Coord::Col(col) => mle_eval(&cols[*col][start..start + (1 << point.len())], point),
        Coord::GCol(col, k) => {
            mle_eval(&cols[*col][start..start + (1 << point.len())], point).mul_base(g_pow(*k as usize))
        }
        _ => panic!("unsupported lookup coordinate"),
    }
}

fn coord_row(coord: &Coord, cols: &[Column], row: usize) -> F64 {
    match coord {
        Coord::Const(v) => *v,
        Coord::Col(col) => cols[*col][row],
        Coord::GCol(col, k) => cols[*col][row] * g_pow(*k as usize),
        _ => panic!("unsupported lookup coordinate"),
    }
}

fn selector_weight(selector: usize, point: &[F192]) -> F192 {
    point.iter().enumerate().fold(F192::ONE, |acc, (k, &x)| {
        acc * if (selector >> k) & 1 == 1 { x } else { F192::ONE + x }
    })
}

/// Sum of the multilinear equality weights for Boolean rows in `[0, real)`.
pub fn real_prefix_weight(point: &[F192], real: usize) -> F192 {
    dyadic_prefix(real).into_iter().fold(F192::ZERO, |acc, (start, kappa)| {
        acc + selector_weight(start >> kappa, &point[kappa..])
    })
}

pub fn bytecode_table(program: &[[F64; 6]], theta: F192) -> Vec<F192> {
    program
        .iter()
        .map(|row| {
            let mut acc = F192::ZERO;
            let mut power = F192::ONE;
            for &value in row {
                acc += power.mul_base(value);
                power *= theta;
            }
            acc
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dyadic_prefix_is_aligned_and_exact() {
        assert_eq!(dyadic_prefix(0), vec![]);
        assert_eq!(dyadic_prefix(13), vec![(0, 3), (8, 2), (12, 0)]);
        for real in 0..128 {
            let chunks = dyadic_prefix(real);
            assert_eq!(chunks.iter().map(|(_, k)| 1usize << k).sum::<usize>(), real);
            assert!(chunks.iter().all(|(start, k)| start.is_multiple_of(1usize << k)));
        }
    }

    #[test]
    fn stacked_access_pushforward_satisfies_duality() {
        let table: Vec<F192> = (0..8).map(|j| F192::from(F64(100 + j as u64))).collect();
        let targets = [2usize, 1, 2, 5, 0, 5];
        let mut cols = vec![vec![F64::ZERO; 8]; 4];
        for (row, &target) in targets.iter().enumerate() {
            cols[0][row] = g_pow(target);
            cols[1][row] = F64(table[target].c0);
        }
        let values = vec![Coord::Col(1), Coord::Col(2), Coord::Col(3)];
        let layout = AccessLayout::new(
            Family::Memory,
            vec![AccessSite {
                table: 0,
                kappa: 3,
                real: 6,
                index: Coord::Col(0),
                values,
            }],
        );
        let materialized = layout.materialize(&cols, table.len());
        let point = vec![F192::new(3, 4, 5), F192::new(6, 7, 8), F192::new(9, 10, 11)];
        let site_value = mle_eval(&cols[1], &point);
        let batched = layout.batch_values(std::slice::from_ref(&point), &[site_value], &[F192::ONE]);
        let pushforward = materialized.pushforward(&batched.weights, table.len());
        let lhs = batched.claim;
        let rhs = table
            .iter()
            .zip(&pushforward)
            .fold(F192::ZERO, |acc, (&t, &y)| acc + t * y);
        assert_eq!(lhs, rhs);
    }
}
