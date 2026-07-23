//! Field-valued columns packed into the dense representation of a Jagged PCS.
//! Only each column's real prefix is committed. Compatible equal-height columns
//! are interleaved row-major; other blocks are concatenated without alignment
//! gaps. The Jagged indicator maps padded column-MLE claims to this dense vector.

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
    /// Log2 number of equal-height columns interleaved row-major in this
    /// Jagged block. Zero is the ordinary one-column layout.
    pub block_width_log: usize,
    /// This column's low-bit selector inside its block.
    pub slot: usize,
}

impl Placement {
    pub const VIRTUAL: Placement = Placement {
        n_vars: usize::MAX,
        offset: 0,
        height: 0,
        block_width_log: 0,
        slot: 0,
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

    let blocks: Vec<Vec<usize>> = order.into_iter().map(|i| vec![i]).collect();
    placements_of_blocks(kappas, heights, &blocks)
}

/// Place explicit power-of-two, equal-height column blocks row-major. The
/// blocks must cover every committed column exactly once; virtual columns are
/// omitted. A width-`2^c` block occupies one tight Jagged interval of length
/// `2^c * height`, and column `slot` lives at `offset + slot + row * 2^c`.
pub fn placements_of_blocks(
    kappas: &[Option<usize>],
    heights: &[usize],
    blocks: &[Vec<usize>],
) -> (Vec<Placement>, usize) {
    let n = kappas.len();
    assert_eq!(heights.len(), n);
    let mut placements = vec![Placement::VIRTUAL; n];
    let mut seen = vec![false; n];
    let mut off = 0usize;
    for block in blocks {
        assert!(!block.is_empty() && block.len().is_power_of_two(), "Jagged block width must be a nonzero power of two");
        let width_log = block.len().trailing_zeros() as usize;
        let first = block[0];
        let k = kappas[first].expect("Jagged blocks cannot contain virtual columns");
        let height = heights[first];
        assert!(height <= 1usize << k, "column height exceeds its padded MLE");
        for (slot, &i) in block.iter().enumerate() {
            assert!(i < n && !seen[i], "Jagged blocks must cover columns exactly once");
            assert_eq!(kappas[i], Some(k), "Jagged block columns must have equal padded height");
            assert_eq!(heights[i], height, "Jagged block columns must have equal real height");
            seen[i] = true;
            placements[i] = Placement {
                n_vars: k,
                offset: off,
                height,
                block_width_log: width_log,
                slot,
            };
        }
        off += height * block.len();
    }
    assert!(kappas.iter().enumerate().all(|(i, k)| k.is_some() == seen[i]), "Jagged blocks must cover every committed column");
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
        // A row-major block is written once, by slot zero. Writing complete
        // rows gives the CPU contiguous stores (and lets rayon split disjoint
        // chunks); walking one physical column at a time would be a strided,
        // cache-hostile transpose.
        if placement.slot != 0 {
            continue;
        }
        let width = 1usize << placement.block_width_log;
        let src = &cols[i][..placement.height];
        if width == 1 && src.len() >= crate::PAR_THRESHOLD {
            let dst = &mut q[placement.offset..placement.offset + placement.height];
            dst.par_chunks_mut(COPY_CHUNK)
                .zip(src.par_chunks(COPY_CHUNK))
                .for_each(|(d, s)| d.copy_from_slice(s));
        } else if width == 1 {
            q[placement.offset..placement.offset + placement.height].copy_from_slice(src);
        } else {
            let mut block_cols = vec![usize::MAX; width];
            for (j, other) in placements.iter().enumerate() {
                if !other.is_virtual()
                    && other.offset == placement.offset
                    && other.block_width_log == placement.block_width_log
                {
                    block_cols[other.slot] = j;
                }
            }
            assert!(block_cols.iter().all(|&j| j != usize::MAX), "incomplete row-major Jagged block");
            let dst = &mut q[placement.offset..placement.offset + placement.height * width];
            let write_row = |row: usize, out: &mut [F128]| {
                for (slot, &col) in block_cols.iter().enumerate() {
                    out[slot] = cols[col][row];
                }
            };
            if dst.len() >= crate::PAR_THRESHOLD {
                dst.par_chunks_mut(width).enumerate().for_each(|(row, out)| write_row(row, out));
            } else {
                for (row, out) in dst.chunks_mut(width).enumerate() {
                    write_row(row, out);
                }
            }
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

    #[test]
    fn row_major_block_is_one_multilinear_claim() {
        let kappas = vec![Some(2), Some(2)];
        let heights = vec![3, 3];
        let (placements, m) = placements_of_blocks(&kappas, &heights, &[vec![0, 1]]);
        let cols = vec![
            vec![F128::new(2, 0), F128::new(3, 0), F128::new(5, 0), F128::ZERO],
            vec![F128::new(7, 0), F128::new(11, 0), F128::new(13, 0), F128::ZERO],
        ];
        let q = stack_q(&cols, &placements, m);
        assert_eq!(&q[..6], &[cols[0][0], cols[1][0], cols[0][1], cols[1][1], cols[0][2], cols[1][2]]);

        let z_col = F128::new(17, 0);
        let row_point = [F128::new(19, 0), F128::new(23, 0)];
        let mut block_point = vec![z_col];
        block_point.extend(row_point);
        let block_eq = primitives::multilinear::build_eq(&block_point);
        let block_eval = q[..6].iter().zip(&block_eq).fold(F128::ZERO, |acc, (&v, &e)| acc + v * e);

        let row_eq = primitives::multilinear::build_eq(&row_point);
        let eval0 = cols[0].iter().zip(&row_eq).fold(F128::ZERO, |acc, (&v, &e)| acc + v * e);
        let eval1 = cols[1].iter().zip(&row_eq).fold(F128::ZERO, |acc, (&v, &e)| acc + v * e);
        assert_eq!(block_eval, (F128::ONE + z_col) * eval0 + z_col * eval1);
    }
}
