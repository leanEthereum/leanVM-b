//! `K`-valued columns stacked into one committed witness (§3.1): columns laid
//! end to end, largest first at aligned offsets, into one multilinear `q` over
//! `F64`. An evaluation claim on column `i` at `ζ ∈ E` becomes the claim
//! `q̂(ζ, sel_i) = c` on the stack, where `sel_i` is the high-bit selector of
//! the column's offset.

use primitives::field::F64;

/// A logical prover column: `2^κ` `K`-elements. Its placement determines
/// whether it is committed or retained only as a virtual AIR/logup* witness.
pub type Column = Vec<F64>;

/// Where a column sits in the stacked witness. A [`Placement::VIRTUAL`] column is
/// NOT committed: its evaluations are discharged by logup*, or against another
/// committed column (BLAKE3 value columns route to `q_pkd`).
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    pub n_vars: usize,
    pub offset: usize,
}

impl Placement {
    pub const VIRTUAL: Placement = Placement {
        n_vars: usize::MAX,
        offset: 0,
    };

    pub fn is_virtual(&self) -> bool {
        self.n_vars == usize::MAX
    }

    /// The high-bit selector of the column's offset (`offset / 2^{n_vars}`).
    pub fn sel(&self) -> usize {
        self.offset >> self.n_vars
    }
}

/// The stacked witness and the per-column placements (in input order).
#[cfg(test)]
pub(crate) struct Stacked {
    pub m: usize,
    pub q: Vec<F64>,
    pub placements: Vec<Placement>,
}

/// Per-column placements (offset + n_vars) and stack length `2^m` from the columns'
/// log-sizes alone, largest-first at aligned offsets. A `None` kappa marks a virtual
/// (uncommitted) column. Depends only on lengths, so the verifier can reconstruct it.
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
    // Floor at the PCS minimum (Ligerito's level ladder needs room); tiny
    // witnesses zero-pad up. Both sides derive this identically from the kappas.
    let m = crate::log2_ceil_usize(off.max(1)).max(crate::pcs::MIN_MU);
    (placements, m)
}

/// Copy the committed columns into one multilinear `q` of length `2^m` at their
/// placed offsets (zero elsewhere). Virtual columns are skipped. Large columns
/// (e.g. `q_pkd`, ~1 GB at scale) copy in parallel — the `2^m` stack is
/// memory-bandwidth bound, so a single-threaded `memcpy` leaves most of the
/// machine idle.
pub fn stack_q(cols: &[Column], placements: &[Placement], m: usize) -> Vec<F64> {
    use rayon::prelude::*;
    // `alloc_zeroed`-backed for the all-zero pad tail; only the copied ranges are
    // touched. (F64 is all-zero bytes at ZERO, so the pad needs no explicit write.)
    let mut q = vec![F64::ZERO; 1 << m];
    // Copy chunk width: big enough that per-chunk `copy_from_slice` amortizes rayon
    // dispatch, small enough to spread the largest column across cores.
    const COPY_CHUNK: usize = 1 << 16;
    for (i, placement) in placements.iter().enumerate() {
        if placement.is_virtual() {
            continue;
        }
        let offset = placement.offset;
        let dst = &mut q[offset..offset + (1 << placement.n_vars)];
        let src = &cols[i];
        if src.len() >= crate::PAR_THRESHOLD {
            dst.par_chunks_mut(COPY_CHUNK)
                .zip(src.par_chunks(COPY_CHUNK))
                .for_each(|(d, s)| d.copy_from_slice(s));
        } else {
            dst.copy_from_slice(src);
        }
    }
    q
}

/// Stack columns largest-first at aligned offsets, zero-padded to `2^m`.
#[cfg(test)]
pub(crate) fn stack(cols: &[Column]) -> Stacked {
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
