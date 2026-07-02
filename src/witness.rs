//! Field-valued columns stacked into one committed witness (§3.1).
//!
//! A column is a vector of `2^κ` field elements. The columns are laid end to
//! end, largest first at aligned offsets, into one multilinear `q` of length
//! `2^m`; an evaluation claim on column `i` at `ζ` is the claim `q̂(ζ, sel_i) = c`
//! on the stack, where `sel_i` is the high-bit selector of the column's offset.

use crate::field::F128;

/// A committed column: `2^κ` field elements.
pub type Column = Vec<F128>;

/// Where a column sits in the stacked witness. A **virtual** placement
/// ([`Placement::VIRTUAL`]) marks a column that is NOT committed (it has data on
/// the prover for the bus, but its evaluation claims are settled against some
/// other committed column — e.g. the BLAKE3 value columns route to `q_pkd`).
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    pub n_vars: usize,
    pub offset: usize,
}

impl Placement {
    /// A column that is not committed in the stack (see the type docs).
    pub const VIRTUAL: Placement = Placement { n_vars: usize::MAX, offset: 0 };

    /// Whether this column is uncommitted (occupies no stack space).
    pub fn is_virtual(&self) -> bool {
        self.n_vars == usize::MAX
    }

    /// The high-bit selector of the column's offset (`offset / 2^{n_vars}`).
    pub fn sel(&self) -> usize {
        self.offset >> self.n_vars
    }
}

/// The stacked witness and the per-column placements (in input order).
pub struct Stacked {
    /// `log2` of the witness length.
    pub m: usize,
    /// The stacked witness `q`, length `2^m`.
    pub q: Vec<F128>,
    pub placements: Vec<Placement>,
}

impl Stacked {
    /// The PCS evaluation point for a claim on column `c` at `point` (length
    /// `κ_c`): the within-column coordinates followed by the column's selector
    /// bits, total length `m` (LSB-first).
    pub fn pcs_point(&self, c: usize, point: &[F128]) -> Vec<F128> {
        let placement = self.placements[c];
        debug_assert_eq!(point.len(), placement.n_vars);
        let mut pcs_point = point.to_vec();
        let sel = placement.sel();
        for k in 0..(self.m - placement.n_vars) {
            pcs_point.push(F128::new(((sel >> k) & 1) as u64, 0));
        }
        pcs_point
    }
}

/// Compute the per-column placements (offset + n_vars) and stack length `2^m`
/// from the columns' log-sizes alone (`kappas`), largest-first at aligned
/// offsets, padded to `m ≥ 2` (the PCS minimum). A `None` kappa marks a
/// **virtual** (uncommitted) column: it gets [`Placement::VIRTUAL`] and occupies
/// no stack space. Depends only on the columns' lengths, not their values, so the
/// verifier can reconstruct it.
pub fn placements_of(kappas: &[Option<usize>]) -> (Vec<Placement>, usize) {
    let n = kappas.len();
    let mut order: Vec<usize> = (0..n).filter(|&i| kappas[i].is_some()).collect();
    order.sort_by(|&a, &b| kappas[b].unwrap().cmp(&kappas[a].unwrap()).then(a.cmp(&b)));

    let mut placements = vec![Placement::VIRTUAL; n];
    let mut off = 0usize;
    for &i in &order {
        let k = kappas[i].unwrap();
        placements[i] = Placement { n_vars: k, offset: off };
        off += 1 << k;
    }
    let m = crate::log2_ceil_usize(off.max(1)).max(2);
    (placements, m)
}

/// Copy the committed columns into one multilinear `q` of length `2^m` at their
/// placed offsets (zero elsewhere). Virtual columns are skipped.
pub fn stack_q(cols: &[Column], placements: &[Placement], m: usize) -> Vec<F128> {
    let mut q = vec![F128::ZERO; 1 << m];
    for (i, placement) in placements.iter().enumerate() {
        if placement.is_virtual() {
            continue;
        }
        let offset = placement.offset;
        q[offset..offset + (1 << placement.n_vars)].copy_from_slice(&cols[i]);
    }
    q
}

/// Stack columns largest-first at aligned offsets, zero-padded to `2^m`
/// (`m ≥ 2`, the PCS minimum).
pub fn stack(cols: &[Column]) -> Stacked {
    let kappas: Vec<Option<usize>> = cols
        .iter()
        .map(|c| {
            assert!(!c.is_empty(), "column must be non-empty");
            Some(crate::log2_strict_usize(c.len()))
        })
        .collect();
    let (placements, m) = placements_of(&kappas);
    let q = stack_q(cols, &placements, m);
    Stacked { m, q, placements }
}
