//! Probe: the deferred-claim batching sumcheck for the fixed BLAKE3 R1CS
//! matrices — the leanVM "bytecode evaluation claims" trick applied to the
//! lincheck's matrix evaluations (the one step of `cpu::verify` that is
//! infeasible to replay in-circuit: ~21M nonzeros, §matnnz_probe).
//!
//! Each in-circuit lincheck verification defers two claims `Ã₀(r) = v_a`,
//! `B̃₀(r) = v_b` (28-variable multilinears, same point). An aggregation node
//! collects `t` such claims per matrix (forwarded + fresh, à la
//! minimal_zkVM.tex §"Bytecode evaluation claims"), RLC-batches them with γ's,
//! and runs ONE sumcheck over
//!
//!   P(x) = A(x)·W_A(x) + B(x)·W_B(x),   W_M(x) = Σ_t γ_{M,t}·eq(r_t, x)
//!
//! reducing everything to single claims Ã₀(r*), B̃₀(r*) forwarded outward; the
//! outermost (native) verifier evaluates them directly (~21 ms, one nnz pass).
//!
//! The PROVER exploits sparsity so no dense 2^28 table ever exists:
//!   phase 1 (bind 14 row vars): per claim, contract the matrix over columns
//!     once — `m_t[i] = Σ_{j∈row i} eq(r_t^col, j)` — an XOR-only nnz pass
//!     (boolean entries); then 14 dense product-sumcheck rounds over 2^14
//!     tables (u_t = eq(r_t^row,·) vs m_t), folding both per round.
//!   phase 2 (bind 14 col vars): contract each matrix over rows at the bound
//!     row point — `Mcol[j] = Σ_{i: (i,j)∈nnz} eq(r*_row, i)` — one XOR-only
//!     nnz pass per matrix; collapse each W to a single dense 2^14 col table;
//!     14 standard dense rounds.
//! Total: (t+1) XOR-only passes over each matrix's nonzeros + O(t·2^14) muls.
use std::time::Instant;

use flare::field::F128;
use flare::lincheck::build_eq_table;
use flare::r1cs::SparseBinaryMatrix;

fn rnd(seed: u64, i: u64) -> F128 {
    F128::new(
        seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(i.wrapping_mul(0xD134_2543_DE82_EF95)) | 1,
        i.wrapping_mul(seed | 7).wrapping_add(0xABCD),
    )
}

/// Direct ("standard") evaluation of the boolean-matrix MLE at (r_row, r_col):
/// one XOR-only pass over the nonzeros with two eq tables.
fn eval_direct(m: &SparseBinaryMatrix, r_row: &[F128], r_col: &[F128]) -> F128 {
    let eq_r = build_eq_table(r_row);
    let eq_c = build_eq_table(r_col);
    let mut acc = F128::ZERO;
    for (i, row) in m.rows.iter().enumerate() {
        let mut s = F128::ZERO;
        for &j in row {
            s += eq_c[j];
        }
        acc += eq_r[i] * s;
    }
    acc
}

/// `m_t[i] = Σ_{j ∈ row i} eq_col[j]` — the per-claim column contraction.
fn contract_cols(m: &SparseBinaryMatrix, eq_col: &[F128]) -> Vec<F128> {
    m.rows
        .iter()
        .map(|row| {
            let mut s = F128::ZERO;
            for &j in row {
                s += eq_col[j];
            }
            s
        })
        .collect()
}

/// `Mcol[j] = Σ_{i : (i,j) ∈ nnz} eq_row[i]` — the row contraction.
fn contract_rows(m: &SparseBinaryMatrix, eq_row: &[F128]) -> Vec<F128> {
    let mut out = vec![F128::ZERO; m.num_cols];
    for (i, row) in m.rows.iter().enumerate() {
        let e = eq_row[i];
        for &j in row {
            out[j] += e;
        }
    }
    out
}

/// One product-sumcheck round over paired tables (u·m summed), binding the LSB.
/// Returns (g0, g1, ginf) contributions; caller folds tables with the challenge.
fn round_msg(pairs: &[(&[F128], &[F128], F128)]) -> (F128, F128, F128) {
    let (mut g0, mut g1, mut gi) = (F128::ZERO, F128::ZERO, F128::ZERO);
    for &(u, m, gamma) in pairs {
        let (mut a0, mut a1, mut ai) = (F128::ZERO, F128::ZERO, F128::ZERO);
        for i in 0..u.len() / 2 {
            a0 += u[2 * i] * m[2 * i];
            a1 += u[2 * i + 1] * m[2 * i + 1];
            ai += (u[2 * i] + u[2 * i + 1]) * (m[2 * i] + m[2 * i + 1]);
        }
        g0 += gamma * a0;
        g1 += gamma * a1;
        gi += gamma * ai;
    }
    (g0, g1, gi)
}

fn fold_lsb(t: &mut Vec<F128>, r: F128) {
    let half = t.len() / 2;
    for i in 0..half {
        t[i] = t[2 * i] + r * (t[2 * i] + t[2 * i + 1]);
    }
    t.truncate(half);
}

fn eq_point(a: &[F128], b: &[F128]) -> F128 {
    a.iter().zip(b).fold(F128::ONE, |acc, (&x, &y)| acc * (F128::ONE + x + y))
}

#[test]
fn matclaim_batch_sumcheck() {
    let (a, b) = flock_prover::r1cs_hashes::blake3::build_matrices();
    let nnz = |m: &SparseBinaryMatrix| m.rows.iter().map(|r| r.len()).sum::<usize>();
    println!("A nnz={}  B nnz={}", nnz(&a), nnz(&b));
    let kl = 14usize; // log rows = log cols

    for t in [2usize, 4, 8] {
        println!("== t = {t} claims per matrix ==");
        // Claim points (r_row, r_col) + claimed values (computed directly, as the
        // in-circuit linchecks would assert them).
        let points: Vec<(Vec<F128>, Vec<F128>)> = (0..t)
            .map(|k| {
                (
                    (0..kl).map(|v| rnd(3 + k as u64, v as u64)).collect(),
                    (0..kl).map(|v| rnd(77 + k as u64, v as u64)).collect(),
                )
            })
            .collect();
        let tt = Instant::now();
        let va: Vec<F128> = points.iter().map(|(rr, rc)| eval_direct(&a, rr, rc)).collect();
        let vb: Vec<F128> = points.iter().map(|(rr, rc)| eval_direct(&b, rr, rc)).collect();
        println!("  [setup] direct evals for reference claims: {:?}", tt.elapsed());
        let ga: Vec<F128> = (0..t).map(|k| rnd(500, k as u64)).collect();
        let gb: Vec<F128> = (0..t).map(|k| rnd(600, k as u64)).collect();

        // ---- Prover ----
        let t_total = Instant::now();
        // Phase 1 setup: per-claim eq tables + column contractions (nnz passes).
        let tt = Instant::now();
        let mut us: Vec<Vec<F128>> = points.iter().map(|(rr, _)| build_eq_table(rr)).collect();
        let mut ms: Vec<Vec<F128>> = Vec::new();
        for (_, rc) in &points {
            let eq_c = build_eq_table(rc);
            ms.push(contract_cols(&a, &eq_c));
            ms.push(contract_cols(&b, &eq_c));
        }
        let t_contract_cols = tt.elapsed();

        let mut running: F128 = (0..t).map(|k| ga[k] * va[k] + gb[k] * vb[k]).fold(F128::ZERO, |x, y| x + y);
        let mut transcript_r: Vec<F128> = Vec::new();

        // Phase 1: 14 row rounds.
        let tt = Instant::now();
        for rd in 0..kl {
            let pairs: Vec<(&[F128], &[F128], F128)> = (0..t)
                .flat_map(|k| [(&us[k][..], &ms[2 * k][..], ga[k]), (&us[k][..], &ms[2 * k + 1][..], gb[k])])
                .collect();
            let (g0, g1, gi) = round_msg(&pairs);
            assert_eq!(g0 + g1, running, "row round {rd} sum consistency");
            let r = rnd(900, rd as u64);
            let c1 = g0 + g1 + gi;
            running = gi * r * r + c1 * r + g0;
            transcript_r.push(r);
            for u in us.iter_mut() {
                fold_lsb(u, r);
            }
            for m in ms.iter_mut() {
                fold_lsb(m, r);
            }
        }
        let t_rows = tt.elapsed();
        let r_row_star = transcript_r.clone();

        // Phase 2 setup: row contractions at r*_row (one nnz pass per matrix) +
        // collapse each W to a single dense column table.
        let tt = Instant::now();
        let eq_rstar = build_eq_table(&r_row_star);
        let acol = contract_rows(&a, &eq_rstar);
        let bcol = contract_rows(&b, &eq_rstar);
        let mut wa = vec![F128::ZERO; 1 << kl];
        let mut wb = vec![F128::ZERO; 1 << kl];
        for (k, (rr, rc)) in points.iter().enumerate() {
            let sa = ga[k] * eq_point(rr, &r_row_star);
            let sb = gb[k] * eq_point(rr, &r_row_star);
            let eq_c = build_eq_table(rc);
            for j in 0..1 << kl {
                wa[j] += sa * eq_c[j];
                wb[j] += sb * eq_c[j];
            }
        }
        let t_contract_rows = tt.elapsed();

        // Sanity: phase-2 start matches the running claim.
        let s2: F128 = (0..1 << kl).map(|j| acol[j] * wa[j] + bcol[j] * wb[j]).fold(F128::ZERO, |x, y| x + y);
        assert_eq!(s2, running, "phase boundary consistency");

        // Phase 2: 14 col rounds (γ already inside the W tables).
        let tt = Instant::now();
        let (mut acol, mut bcol, mut wa, mut wb) = (acol, bcol, wa, wb);
        let mut r_col_star: Vec<F128> = Vec::new();
        for rd in 0..kl {
            let pairs: Vec<(&[F128], &[F128], F128)> = vec![(&acol[..], &wa[..], F128::ONE), (&bcol[..], &wb[..], F128::ONE)];
            let (g0, g1, gi) = round_msg(&pairs);
            assert_eq!(g0 + g1, running, "col round {rd} sum consistency");
            let r = rnd(901, rd as u64);
            let c1 = g0 + g1 + gi;
            running = gi * r * r + c1 * r + g0;
            r_col_star.push(r);
            for tb in [&mut acol, &mut bcol, &mut wa, &mut wb] {
                fold_lsb(tb, r);
            }
        }
        let t_cols = tt.elapsed();
        let t_prover = t_total.elapsed();

        // ---- Terminal check (what the outermost native verifier does) ----
        // The prover's final table entries are the two deferred claims.
        let (a_star, b_star) = (acol[0], bcol[0]);
        let wa_star: F128 = (0..t)
            .map(|k| ga[k] * eq_point(&points[k].0, &r_row_star) * eq_point(&points[k].1, &r_col_star))
            .fold(F128::ZERO, |x, y| x + y);
        let wb_star: F128 = (0..t)
            .map(|k| gb[k] * eq_point(&points[k].0, &r_row_star) * eq_point(&points[k].1, &r_col_star))
            .fold(F128::ZERO, |x, y| x + y);
        assert_eq!(running, a_star * wa_star + b_star * wb_star, "terminal identity");
        // And the deferred claims are true statements about the fixed matrices:
        assert_eq!(a_star, eval_direct(&a, &r_row_star, &r_col_star), "deferred A claim");
        assert_eq!(b_star, eval_direct(&b, &r_row_star, &r_col_star), "deferred B claim");

        println!("  [prover] col contractions (t x 2 nnz passes): {t_contract_cols:?}");
        println!("  [prover] 14 row rounds (dense 2^14, {t}x2 pairs): {t_rows:?}");
        println!("  [prover] row contractions + W collapse:        {t_contract_rows:?}");
        println!("  [prover] 14 col rounds:                        {t_cols:?}");
        println!("  [prover] TOTAL:                                {t_prover:?}");
        println!("  terminal + deferred claims verified");
    }
}
