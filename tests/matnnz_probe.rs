//! Scratch probe: BLAKE3 R1CS per-block matrix shapes + nnz + the cost of the
//! "standard" (walk-every-nonzero) evaluation the lincheck verifier performs.
use std::time::Instant;

#[test]
fn matnnz() {
    let (a, b) = flock_prover::r1cs_hashes::blake3::build_matrices();
    let nnz = |m: &flare::r1cs::SparseBinaryMatrix| m.rows.iter().map(|r| r.len()).sum::<usize>();
    let (na, nb) = (nnz(&a), nnz(&b));
    println!("A_0: {}x{}  nnz={}  ({:.1} avg/row)", a.num_rows, a.num_cols, na, na as f64 / a.num_rows as f64);
    println!("B_0: {}x{}  nnz={}  ({:.1} avg/row)", b.num_rows, b.num_cols, nb, nb as f64 / b.num_rows as f64);

    // The verifier-side evaluation: build the eq table (2^14 MULs), then
    // comb[c] = alpha*(eq^T A)[c] + (eq^T B)[c] — one XOR per nonzero.
    use flare::field::F128;
    use flare::lincheck::build_eq_table;
    let point: Vec<F128> = (0..14).map(|i| F128::new(0xABC + i as u64, 31 * i as u64 + 5)).collect();
    let alpha = F128::new(0x1234, 0x9999);
    let t = Instant::now();
    let eq = build_eq_table(&point);
    let t_eq = t.elapsed();
    let t = Instant::now();
    let mut comb = vec![F128::ZERO; a.num_cols];
    for (i, row) in a.rows.iter().enumerate() {
        for &c in row {
            comb[c] += eq[i];
        }
    }
    for v in comb.iter_mut() {
        *v *= alpha;
    }
    for (i, row) in b.rows.iter().enumerate() {
        for &c in row {
            comb[c] += eq[i];
        }
    }
    let t_fold = t.elapsed();
    println!("eq table (2^14): {t_eq:?}   fold over {} nnz: {t_fold:?}", na + nb);
    println!("comb[0] = {:?}", comb[0]); // keep it alive
}
