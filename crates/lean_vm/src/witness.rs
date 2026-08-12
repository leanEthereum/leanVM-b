//! `K`-valued columns stacked into one committed witness (§sec:stacking): columns laid
//! end to end, largest first at aligned offsets, into one multilinear `q` over
//! `F64`. An evaluation claim on column `i` at `ζ ∈ E` becomes the claim
//! `q̂(ζ, sel_i) = c` on the stack, where `sel_i` is the high-bit selector of
//! the column's offset.

use primitives::field::F64;
use zk_alloc::ArenaVec;

/// A committed column: `2^κ` `K`-elements.
pub type Column = Vec<F64>;

/// Where a column sits in the stacked witness. A [`Placement::VIRTUAL`] column is
/// NOT committed: it carries data for the bus, but its evaluation claims settle
/// against some other committed column (e.g. the BLAKE2s value columns route to `q_flock`).
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
}

/// The stacked witness and the per-column placements (in input order).
#[cfg(test)]
pub(crate) struct Stacked {
    pub m: usize,
    pub q: ArenaVec<F64>,
    pub placements: Vec<Placement>,
}

/// Lay `2^kappa`-sized items end to end, largest first at aligned offsets and ties
/// broken by index, returning the per-item offset and `⌈log2 Σ 2^kappa⌉`. A `None`
/// kappa takes no space and its offset is meaningless. Depends only on the sizes, so
/// the verifier reconstructs the same tiling.
pub(crate) fn stack_offsets(kappas: &[Option<usize>]) -> (Vec<usize>, usize) {
    let n = kappas.len();
    let mut order: Vec<usize> = (0..n).filter(|&i| kappas[i].is_some()).collect();
    order.sort_by(|&a, &b| kappas[b].unwrap().cmp(&kappas[a].unwrap()).then(a.cmp(&b)));

    let mut offsets = vec![0usize; n];
    let mut off = 0usize;
    for &i in &order {
        offsets[i] = off;
        off += 1 << kappas[i].unwrap();
    }
    (offsets, crate::log2_ceil_usize(off.max(1)))
}

/// Per-column placements (offset + n_vars) and stack length `2^m` from the columns'
/// log-sizes alone, largest-first at aligned offsets. A `None` kappa marks a virtual
/// (uncommitted) column. Depends only on lengths, so the verifier can reconstruct it.
pub fn placements_of(kappas: &[Option<usize>]) -> (Vec<Placement>, usize) {
    let (offsets, mu) = stack_offsets(kappas);
    let placements = kappas
        .iter()
        .zip(&offsets)
        .map(|(k, &offset)| match *k {
            Some(n_vars) => Placement { n_vars, offset },
            None => Placement::VIRTUAL,
        })
        .collect();
    // Floor at the PCS minimum (WHIR's level ladder needs room); tiny
    // witnesses zero-pad up. Both sides derive this identically from the kappas.
    (placements, mu.max(crate::pcs::MIN_MU))
}

/// Chunk width for the bulk writes below: big enough to amortize the dispatch,
/// small enough to spread one column across cores.
const FILL_CHUNK: usize = 1 << 16;

/// The uninitialized stacked witness, `2^m` slots. Arena-backed: `q` is born and
/// dies inside one `cpu::prove` phase.
///
/// # Safety
/// Every slot must be written before it is read. [`split_stack`] hands out one
/// window per committed column and zeroes the pad tail, which together cover the
/// whole allocation, so the obligation reduces to each column's fill writing its
/// own window.
pub unsafe fn alloc_stack(m: usize) -> ArenaVec<F64> {
    // SAFETY: forwarded to the caller by the contract above.
    unsafe { ArenaVec::<F64>::uninitialized(1 << m) }
}

/// Carve the stack into one mutable window per committed column, in column order,
/// and zero the pad tail past the last one. A virtual column gets an empty window:
/// it is not in the stack, so its values need storage of their own.
///
/// Writing each column into its final place is what lets the whole witness be
/// written once. Copying columns in afterwards would move the entire stack a
/// second time (a gigabyte at scale) for nothing, and allocating the stack zeroed
/// would memset all `2^m` slots only for the columns to overwrite them.
///
/// Safe despite [`alloc_stack`]'s uninitialized allocation: [`placements_of`]
/// tiles the columns from offset 0, checked here, so consecutive `split_at_mut`
/// hands out disjoint windows covering `[0, placed)` and this zeroes the rest.
pub fn split_stack<'a>(q: &'a mut [F64], placements: &[Placement]) -> Vec<&'a mut [F64]> {
    let mut order: Vec<usize> = (0..placements.len()).filter(|&i| !placements[i].is_virtual()).collect();
    order.sort_unstable_by_key(|&i| placements[i].offset);

    let mut windows: Vec<&mut [F64]> = Vec::with_capacity(placements.len());
    windows.resize_with(placements.len(), || &mut []);
    let mut rest = q;
    let mut placed = 0usize;
    for &i in &order {
        assert_eq!(
            placements[i].offset, placed,
            "the stacked columns must tile from 0 with no gap"
        );
        let (window, tail) = rest.split_at_mut(1 << placements[i].n_vars);
        windows[i] = window;
        rest = tail;
        placed += 1 << placements[i].n_vars;
    }
    parallel::chunks_mut(rest, FILL_CHUNK, |_, pad| pad.fill(F64::ZERO));
    windows
}

/// Stack the columns for a test: build the placements from their lengths, then
/// copy each into its window.
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
    // SAFETY: `split_stack` covers the whole allocation, and every window is
    // copied into below.
    let mut q = unsafe { alloc_stack(m) };
    for (w, c) in split_stack(&mut q, &placements).into_iter().zip(cols) {
        w.copy_from_slice(c);
    }
    Stacked { m, q, placements }
}
