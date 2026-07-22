//! Field-valued columns packed into the dense representation of a Jagged PCS.
//! Only each column's real prefix is committed; columns are concatenated without
//! alignment gaps and the Jagged indicator maps their padded MLE claims back to
//! this dense vector.

use primitives::field::F128;

/// A committed column: `2^κ` field elements.
pub type Column = Vec<F128>;

/// Where a column sits in the stacked witness. A [`Placement::VIRTUAL`] column is
/// NOT committed: it carries data for the bus, but its evaluation claims settle
/// against some other committed column (e.g. the BLAKE3 value columns route to `q_pkd`).
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    /// Number of variables in the logical, zero-padded column MLE.
    pub n_vars: usize,
    /// Start of the real prefix in the dense committed vector.
    pub offset: usize,
    /// Number of real entries committed for this column (not necessarily a
    /// power of two and possibly zero).
    pub height: usize,
}

impl Placement {
    pub const VIRTUAL: Placement = Placement {
        n_vars: usize::MAX,
        offset: 0,
        height: 0,
    };

    pub fn is_virtual(&self) -> bool {
        self.n_vars == usize::MAX
    }
}

/// The stacked witness and the per-column placements (in input order).
#[cfg(test)]
pub(crate) struct Stacked {
    pub m: usize,
    pub q: Vec<F128>,
    pub placements: Vec<Placement>,
}

/// Per-column Jagged placements and dense commitment length `2^m`.
///
/// `heights[i]` is the real prefix length (at most `2^kappas[i]`). A `None`
/// kappa marks a virtual column. `first`, when present, anchors one power-of-two
/// column at offset zero; leanVM uses this for flock's `q_pkd`, whose existing
/// ring-switch weight can then be lifted unchanged while every ordinary column
/// uses the Jagged adapter.
pub fn placements_of(
    kappas: &[Option<usize>],
    heights: &[usize],
    first: Option<usize>,
) -> (Vec<Placement>, usize) {
    let n = kappas.len();
    assert_eq!(heights.len(), n);
    let mut order: Vec<usize> = first.into_iter().collect();
    order.extend((0..n).filter(|&i| kappas[i].is_some() && Some(i) != first));

    let mut placements = vec![Placement::VIRTUAL; n];
    let mut off = 0usize;
    for &i in &order {
        let k = kappas[i].unwrap();
        assert!(heights[i] <= 1usize << k, "column height exceeds its padded MLE");
        placements[i] = Placement {
            n_vars: k,
            offset: off,
            height: heights[i],
        };
        off += heights[i];
    }
    // Floor at the PCS minimum (Ligerito's level ladder needs room); tiny witnesses
    // zero-pad up. Both sides derive this identically from the kappas.
    let m = crate::log2_ceil_usize(off.max(1)).max(crate::pcs::MIN_MU);
    (placements, m)
}

/// Copy the real column prefixes into the Jagged dense vector `q` of length
/// `2^m` (zero in the final PCS pad). Virtual columns are skipped. Large columns
/// (e.g. `q_pkd`, ~1 GB at scale) copy in parallel — the `2^m` stack is
/// memory-bandwidth bound, so a single-threaded `memcpy` leaves most of the
/// machine idle.
pub fn stack_q(cols: &[Column], placements: &[Placement], m: usize) -> Vec<F128> {
    use rayon::prelude::*;
    // `alloc_zeroed`-backed for the all-zero pad tail; only the copied ranges are
    // touched. (F128 is all-zero bytes at ZERO, so the pad needs no explicit write.)
    let mut q = vec![F128::ZERO; 1 << m];
    // Copy chunk width: big enough that per-chunk `copy_from_slice` amortizes rayon
    // dispatch, small enough to spread the largest column across cores.
    const COPY_CHUNK: usize = 1 << 16;
    for (i, placement) in placements.iter().enumerate() {
        if placement.is_virtual() {
            continue;
        }
        let offset = placement.offset;
        let dst = &mut q[offset..offset + placement.height];
        let src = &cols[i][..placement.height];
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
    let heights: Vec<usize> = cols.iter().map(Vec::len).collect();
    let (placements, m) = placements_of(&kappas, &heights, None);
    let q = stack_q(cols, &placements, m);
    Stacked { m, q, placements }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jagged_layout_is_tight_and_anchors_requested_column() {
        let kappas = vec![Some(2), Some(3), None, Some(1)];
        let heights = vec![3, 5, 0, 2];
        let (placements, m) = placements_of(&kappas, &heights, Some(1));

        assert_eq!(m, crate::pcs::MIN_MU);
        assert_eq!(placements[1].offset, 0);
        assert_eq!(placements[0].offset, 5);
        assert_eq!(placements[3].offset, 8);
        assert!(placements[2].is_virtual());

        let cols = vec![
            vec![
                F128::new(10, 0),
                F128::new(11, 0),
                F128::new(12, 0),
                F128::new(99, 0),
            ],
            (20..28).map(|x| F128::new(x, 0)).collect(),
            vec![F128::new(77, 0)],
            vec![F128::new(30, 0), F128::new(31, 0)],
        ];
        let q = stack_q(&cols, &placements, m);
        assert_eq!(&q[..5], &cols[1][..5]);
        assert_eq!(&q[5..8], &cols[0][..3]);
        assert_eq!(&q[8..10], &cols[3][..2]);
        assert!(q[10..].iter().all(|&x| x == F128::ZERO));
    }
}
