//! `lagrange_weights` divides by ONE denominator rather than one per node, because every
//! barycentric denominator over an aligned window of the φ₈ table is the same field element:
//! φ₈ is F2-linear on its index, so `nodes[a] + nodes[b] = φ₈(a ^ b)` (a coset's offset cancels)
//! and `b ↦ a ^ b` only permutes the window. Should `PHI_8_BASIS` ever stop being the image of a
//! basis, the identity dies silently and every flock skip round is quietly wrong, so it is pinned
//! here against the per-node computation it replaced.
use primitives::field::{F192, PHI_8_TABLE_192 as PHI_8_TABLE};
use primitives::multilinear::{lagrange_eval, window_denominator};

/// The pre-change denominator: `∏_{k≠i} (nodes[i] + nodes[k])`, inverted, one per node.
fn per_node(nodes: &[F192], i: usize) -> F192 {
    let mut denominator = F192::ONE;
    for k in 0..nodes.len() {
        if k != i {
            denominator *= nodes[i] + nodes[k];
        }
    }
    denominator.inv()
}

#[test]
fn one_denominator_per_window_size() {
    for log_size in 1..=8 {
        let size = 1usize << log_size;
        let shared = window_denominator(size);
        for base in (0..PHI_8_TABLE.len()).step_by(size) {
            let nodes = &PHI_8_TABLE[base..base + size];
            for i in 0..size {
                assert_eq!(per_node(nodes, i), shared, "size {size}, base {base}, node {i}");
            }
        }
    }
}

/// The weights are assembled from that one denominator, so interpolating at a node must still
/// return that node's value, on a coset as well as on the prefix.
#[test]
fn interpolation_recovers_node_values() {
    for (base, size) in [(0usize, 64usize), (64, 64), (0, 128), (192, 64)] {
        let nodes = &PHI_8_TABLE[base..base + size];
        let values: Vec<F192> = (0..size)
            .map(|i| F192::new((i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15), i as u64, 0))
            .collect();
        for i in 0..size {
            assert_eq!(
                lagrange_eval(nodes, &values, nodes[i]),
                values[i],
                "base {base}, size {size}, node {i}"
            );
        }
    }
}
