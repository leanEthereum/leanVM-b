//! `K`-valued columns packed into the dense representation of a Jagged PCS.
//! Only each column's real prefix is committed, over `F64`. Compatible
//! equal-height columns are interleaved row-major; other blocks are
//! concatenated without alignment gaps. The Jagged indicator
//! ([`::pcs::jagged`]) maps a padded column-MLE claim at `ζ ∈ E` to a weighted
//! claim on this dense vector.

use primitives::field::F64;

/// A committed column: its real entries are `K`-elements. The logical MLE is
/// this prefix zero-padded to `2^κ`.
pub type Column = Vec<F64>;

/// Where a column sits in the dense Jagged witness. A [`Placement::VIRTUAL`]
/// column is NOT committed: it carries data for the bus, but its evaluation
/// claims settle against some other committed column (e.g. the BLAKE3 value
/// columns route to `q_pkd`).
#[derive(Clone, Copy, Debug)]
pub struct Placement {
    /// Number of variables in the logical, zero-padded column MLE.
    pub n_vars: usize,
    /// Start of the real prefix in the dense committed vector.
    pub offset: usize,
    /// Number of real entries committed for this column (not necessarily a
    /// power of two, and possibly zero).
    pub height: usize,
    /// Log2 of the number of equal-height columns interleaved row-major in
    /// this Jagged block. Zero is the ordinary one-column layout.
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
    pub q: Vec<F64>,
    pub placements: Vec<Placement>,
}

/// Per-column Jagged placements and dense commitment length `2^m`.
///
/// `heights[i]` is the real prefix length (at most `2^kappas[i]`). A `None`
/// kappa marks a virtual column. `first`, when present, anchors one
/// power-of-two column at offset zero; leanVM uses this for flock's `q_pkd`,
/// whose existing ring-switch weight is then lifted unchanged while every
/// ordinary column goes through the Jagged adapter.
///
/// Depends only on the announced sizes, so the verifier reconstructs it.
pub fn placements_of(kappas: &[Option<usize>], heights: &[usize], first: Option<usize>) -> (Vec<Placement>, usize) {
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
    let mut logical_m = 0usize;
    for block in blocks {
        assert!(
            !block.is_empty() && block.len().is_power_of_two(),
            "Jagged block width must be a nonzero power of two"
        );
        let width_log = block.len().trailing_zeros() as usize;
        let first = block[0];
        let k = kappas[first].expect("Jagged blocks cannot contain virtual columns");
        logical_m = logical_m.max(k + width_log);
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
    assert!(
        kappas.iter().enumerate().all(|(i, k)| k.is_some() == seen[i]),
        "Jagged blocks must cover every committed column"
    );
    // The dense cube must both hold the packed area and have enough coordinates
    // to embed every block's selector + logical row point. Floor additionally
    // at the PCS minimum required by Ligerito's level ladder.
    let m = crate::log2_ceil_usize(off.max(1))
        .max(logical_m)
        .max(crate::pcs::MIN_MU);
    (placements, m)
}

/// Copy the real column prefixes into the Jagged dense vector `q` of length
/// `2^m` (zero in the final PCS pad). Virtual columns are skipped. Large
/// columns (e.g. `q_pkd`, ~1 GB at scale) copy in parallel — the `2^m` stack
/// is memory-bandwidth bound, so a single-threaded `memcpy` leaves most of the
/// machine idle.
///
/// What is committed is the column OFFSET BY ITS PAD VALUE, `P_c + pad[c]`. The
/// logical column is `P_c` below its real height and the constant `pad[c]` at and
/// above it, so the offset column vanishes on the padding and is still supported
/// exactly on `[0, height)`; and since the MLE of a constant is that constant, a
/// logical evaluation is the committed one plus `pad[c]`. That turns the padding
/// correction into a single field addition and removes the prefix indicator the
/// verifier would otherwise evaluate per claim (`cpu::slot_claims`). Columns with
/// `pad[c] == 0`, which is all but the read counts and the two finalize-count
/// columns, keep the plain `memcpy` path.
pub fn stack_q(cols: &[Column], placements: &[Placement], pads: &[F64], m: usize) -> Vec<F64> {
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
        // A row-major block is written once, by slot zero. Writing complete
        // rows gives the CPU contiguous stores (and lets rayon split disjoint
        // chunks); walking one physical column at a time would be a strided,
        // cache-hostile transpose.
        if placement.slot != 0 {
            continue;
        }
        let width = 1usize << placement.block_width_log;
        let src = &cols[i][..placement.height];
        let pad = pads[i];
        if width == 1 && pad != F64::ZERO {
            let dst = &mut q[placement.offset..placement.offset + placement.height];
            if dst.len() >= crate::PAR_THRESHOLD {
                dst.par_iter_mut().zip(src.par_iter()).for_each(|(d, s)| *d = *s + pad);
            } else {
                for (d, s) in dst.iter_mut().zip(src) {
                    *d = *s + pad;
                }
            }
        } else if width == 1 && src.len() >= crate::PAR_THRESHOLD {
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
            assert!(
                block_cols.iter().all(|&j| j != usize::MAX),
                "incomplete row-major Jagged block"
            );
            let dst = &mut q[placement.offset..placement.offset + placement.height * width];
            let write_row = |row: usize, out: &mut [F64]| {
                for (slot, &col) in block_cols.iter().enumerate() {
                    out[slot] = cols[col][row] + pads[col];
                }
            };
            if dst.len() >= crate::PAR_THRESHOLD {
                dst.par_chunks_mut(width)
                    .enumerate()
                    .for_each(|(row, out)| write_row(row, out));
            } else {
                for (row, out) in dst.chunks_mut(width).enumerate() {
                    write_row(row, out);
                }
            }
        }
    }
    q
}

/// Stack columns tightly in the Jagged layout, zero-padded to `2^m`.
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
    let q = stack_q(cols, &placements, &vec![F64::ZERO; cols.len()], m);
    Stacked { m, q, placements }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::F192;

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
            vec![F64(10), F64(11), F64(12), F64(99)],
            (20..28).map(F64).collect(),
            vec![F64(77)],
            vec![F64(30), F64(31)],
        ];
        let q = stack_q(&cols, &placements, &vec![F64::ZERO; cols.len()], m);
        assert_eq!(&q[..5], &cols[1][..5]);
        assert_eq!(&q[5..8], &cols[0][..3]);
        assert_eq!(&q[8..10], &cols[3][..2]);
        assert!(q[10..].iter().all(|&x| x == F64::ZERO));
    }

    /// A width-two row-major block must read back as the single multilinear
    /// `(1 + z)·col0(row) + z·col1(row)` over the shared row point.
    #[test]
    fn row_major_block_is_one_multilinear_claim() {
        let kappas = vec![Some(2), Some(2)];
        let heights = vec![3, 3];
        let (placements, m) = placements_of_blocks(&kappas, &heights, &[vec![0, 1]]);
        let cols = vec![
            vec![F64(2), F64(3), F64(5), F64::ZERO],
            vec![F64(7), F64(11), F64(13), F64::ZERO],
        ];
        let q = stack_q(&cols, &placements, &vec![F64::ZERO; cols.len()], m);
        assert_eq!(
            &q[..6],
            &[cols[0][0], cols[1][0], cols[0][1], cols[1][1], cols[0][2], cols[1][2]]
        );

        let z_col = F192::new(17, 0, 0);
        let row_point = [F192::new(19, 0, 0), F192::new(23, 0, 0)];
        let mut block_point = vec![z_col];
        block_point.extend(row_point);
        let block_eval = primitives::multilinear::mle_eval(&q[..8], &block_point);

        let eval0 = primitives::multilinear::mle_eval(&cols[0], &row_point);
        let eval1 = primitives::multilinear::mle_eval(&cols[1], &row_point);
        assert_eq!(block_eval, (F192::ONE + z_col) * eval0 + z_col * eval1);
    }
}
