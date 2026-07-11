//! Probe: the ring-switch tensor computations as LINEARIZED polynomials.
//!
//! Claim: any eq-weighted bit-sum is a trace form, `Σ_i w_i·bit_i(y) = L_w(y)`
//! with `L_w(y) = Σ_k c_k·y^{2^k}`, `c_k = Σ_i w_i·δ_i^{2^k}`, where {δ_i} is
//! the trace-dual basis of the polynomial basis. Consequences:
//!   (1) sumcheck_claim = ⟨transpose(s_hat_v), w⟩ = Σ_j B_j·L_w(s_hat_v[j]);
//!   (2) eval_rs_eq(z, q, w) = Σ_k c_k·Π_j (z_j^{2^k} + 1 + q_j)
//!       (the rank-1 subset expansion of Π_j(z_j⊗1 + 1⊗(1+q_j)) telescopes).
//! In-circuit, squaring is ONE mul, so both drop from ~10^5-10^6 cycles to
//! ~10^4: the tensor deferral would become unnecessary.

use leanvm_b::field::F128;

fn tr(x: F128) -> F128 {
    // absolute trace to F2 (as a 0/1 field element): Σ_{k<128} x^{2^k}.
    let mut acc = F128::ZERO;
    let mut p = x;
    for _ in 0..128 {
        acc += p;
        p *= p;
    }
    acc
}

fn basis(j: usize) -> F128 {
    if j < 64 { F128::new(1u64 << j, 0) } else { F128::new(0, 1u64 << (j - 64)) }
}

/// The trace-dual basis {δ_i}: Tr(δ_i·B_j) = [i == j].
fn dual_basis() -> Vec<F128> {
    // Gram matrix G[i][j] = Tr(B_i·B_j) over F2, rows as u128 bitmasks.
    let mut g: Vec<u128> = vec![0; 128];
    for (i, row) in g.iter_mut().enumerate() {
        for j in 0..128 {
            if tr(basis(i) * basis(j)) == F128::ONE {
                *row |= 1u128 << j;
            }
        }
    }
    // Invert G over F2 (Gauss-Jordan), identity alongside.
    let mut inv: Vec<u128> = (0..128).map(|i| 1u128 << i).collect();
    for col in 0..128 {
        let piv = (col..128).find(|&r| (g[r] >> col) & 1 == 1).expect("Gram invertible");
        g.swap(col, piv);
        inv.swap(col, piv);
        for r in 0..128 {
            if r != col && (g[r] >> col) & 1 == 1 {
                g[r] ^= g[col];
                inv[r] ^= inv[col];
            }
        }
    }
    // δ_i = Σ_j Ginv[i][j]·B_j.
    (0..128)
        .map(|i| {
            let mut d = F128::ZERO;
            for j in 0..128 {
                if (inv[i] >> j) & 1 == 1 {
                    d += basis(j);
                }
            }
            d
        })
        .collect()
}

fn bit(y: F128, i: usize) -> u64 {
    if i < 64 { (y.lo >> i) & 1 } else { (y.hi >> (i - 64)) & 1 }
}

struct Rng(u64);
impl Rng {
    fn f128(&mut self) -> F128 {
        let mut n = || {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        };
        F128::new(n(), n())
    }
}

#[test]
fn linearized_tensor_identities() {
    let delta = dual_basis();
    let mut rng = Rng(0xC0FFEE);

    // (0) the trace form recovers bits: bit_i(y) == Tr(δ_i·y).
    for _ in 0..4 {
        let y = rng.f128();
        for (i, &d) in delta.iter().enumerate() {
            assert_eq!(tr(d * y), F128::new(bit(y, i), 0), "dual basis bit {i}");
        }
    }

    // random instance shaped like the real one (qpkd_vars = 10, 7 r'' coords).
    let z: Vec<F128> = (0..10).map(|_| rng.f128()).collect();
    let q: Vec<F128> = (0..10).map(|_| rng.f128()).collect();
    let rdp: Vec<F128> = (0..7).map(|_| rng.f128()).collect();
    let w = flare::zerocheck::univariate_skip::build_eq(&rdp);

    // c_k = Σ_i w_i·δ_i^{2^k}.
    let mut c = vec![F128::ZERO; 128];
    for i in 0..128 {
        let mut p = delta[i];
        for ck in c.iter_mut() {
            *ck += w[i] * p;
            p *= p;
        }
    }

    // (1) the transposed inner product as Σ_j B_j·L_w(y_j).
    let shv: Vec<F128> = (0..128).map(|_| rng.f128()).collect();
    let shu = flare::pcs::ring_switch::tensor_algebra_transpose(&shv);
    let want = flare::pcs::ring_switch::inner_product(&shu, &w);
    let mut got = F128::ZERO;
    for (j, &y) in shv.iter().enumerate() {
        let mut lw = F128::ZERO;
        let mut p = y;
        for &ck in &c {
            lw += ck * p;
            p *= p;
        }
        got += basis(j) * lw;
    }
    assert_eq!(got, want, "transpose identity");

    // (2) eval_rs_eq as the telescoped product formula.
    let want = flare::pcs::ring_switch::eval_rs_eq(&z, &q, &w);
    let mut zp: Vec<F128> = z.clone(); // z_j^{2^k}, squared in place per k
    let mut got = F128::ZERO;
    for &ck in &c {
        let mut prod = F128::ONE;
        for (j, zpj) in zp.iter_mut().enumerate() {
            prod *= *zpj + F128::ONE + q[j];
            *zpj *= *zpj;
        }
        got += ck * prod;
    }
    assert_eq!(got, want, "eval_rs_eq product formula");
    eprintln!("linearized tensor identities hold");
}
