//! Fractional-addition GKR used by logup*.
//!
//! Leaves represent fractions `num / den`. Adjacent fractions are added as
//! `(n0*d1 + n1*d0) / (d0*d1)`. The GKR reduces the two root claims to the
//! numerator and denominator leaf multilinears at one shared point.

use crate::transcript::{ProverState, VerifierState};
use primitives::field::{F192, G};
use primitives::multilinear::{eq_table, interp, lagrange_eval, tri_nodes};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Truncated,
    Sumcheck { layer: usize, round: usize },
    Layer { layer: usize },
}

#[derive(Clone, Debug)]
pub struct Output {
    pub point: Vec<F192>,
    pub num: F192,
    pub den: F192,
}

pub struct Circuit {
    nums: Vec<Vec<F192>>,
    dens: Vec<Vec<F192>>,
}

impl Circuit {
    pub fn new(num: Vec<F192>, den: Vec<F192>) -> Self {
        assert_eq!(num.len(), den.len());
        assert!(num.len().is_power_of_two());
        let mut nums = vec![num];
        let mut dens = vec![den];
        while nums.last().unwrap().len() > 1 {
            let n = nums.last().unwrap();
            let d = dens.last().unwrap();
            let mut nn = Vec::with_capacity(n.len() / 2);
            let mut dd = Vec::with_capacity(d.len() / 2);
            for i in 0..n.len() / 2 {
                nn.push(n[2 * i] * d[2 * i + 1] + n[2 * i + 1] * d[2 * i]);
                dd.push(d[2 * i] * d[2 * i + 1]);
            }
            nums.push(nn);
            dens.push(dd);
        }
        Self { nums, dens }
    }

    pub fn n_vars(&self) -> usize {
        self.nums.len() - 1
    }

    pub fn root(&self) -> (F192, F192) {
        let last = self.n_vars();
        (self.nums[last][0], self.dens[last][0])
    }

    /// Prove from roots that the caller has already transmitted and bound.
    pub fn prove(self, ps: &mut ProverState) -> Output {
        let mu = self.n_vars();
        let (mut num_claim, mut den_claim) = self.root();
        let mut point = Vec::new();
        let nodes = tri_nodes();
        let mut lambda = ps.sample();

        for layer in (1..=mu).rev() {
            let k = mu - layer;
            let below_n = &self.nums[layer - 1];
            let below_d = &self.dens[layer - 1];
            let width = 1usize << k;
            let mut n0: Vec<F192> = (0..width).map(|i| below_n[2 * i]).collect();
            let mut n1: Vec<F192> = (0..width).map(|i| below_n[2 * i + 1]).collect();
            let mut d0: Vec<F192> = (0..width).map(|i| below_d[2 * i]).collect();
            let mut d1: Vec<F192> = (0..width).map(|i| below_d[2 * i + 1]).collect();
            let mut eq_suffix = if k == 0 { Vec::new() } else { eq_table(&point[1..]) };
            let mut rho = Vec::with_capacity(k);

            for _round in 0..k {
                let half = n0.len() / 2;
                let mut msg = [F192::ZERO; 3];
                for i in 0..half {
                    let eq = eq_suffix[i];
                    for (node_i, &t) in nodes.iter().enumerate() {
                        let a0 = interp(n0[2 * i], n0[2 * i + 1], t);
                        let a1 = interp(n1[2 * i], n1[2 * i + 1], t);
                        let b0 = interp(d0[2 * i], d0[2 * i + 1], t);
                        let b1 = interp(d1[2 * i], d1[2 * i + 1], t);
                        msg[node_i] += eq * (a0 * b1 + a1 * b0 + lambda * b0 * b1);
                    }
                }
                ps.add_scalars(&msg);
                let challenge = ps.sample();
                rho.push(challenge);
                fold(&mut n0, challenge);
                fold(&mut n1, challenge);
                fold(&mut d0, challenge);
                fold(&mut d1, challenge);
                shrink_eq(&mut eq_suffix);
            }

            ps.add_scalars(&[n0[0], n1[0], d0[0], d1[0]]);
            let child = ps.sample();
            num_claim = interp(n0[0], n1[0], child);
            den_claim = interp(d0[0], d1[0], child);
            lambda = ps.sample();
            point.clear();
            point.push(child);
            point.extend_from_slice(&rho);
        }

        Output {
            point,
            num: num_claim,
            den: den_claim,
        }
    }
}

pub fn verify(mu: usize, mut num_claim: F192, mut den_claim: F192, vs: &mut VerifierState) -> Result<Output, Error> {
    let nodes = tri_nodes();
    let mut point = Vec::new();
    let mut lambda = vs.sample();

    for layer in (1..=mu).rev() {
        let k = mu - layer;
        let mut claim = num_claim + lambda * den_claim;
        let mut rho = Vec::with_capacity(k);
        let mut eq_acc = F192::ONE;
        for round in 0..k {
            let msg = vs.next_scalars(3).map_err(|_| Error::Truncated)?;
            let rj = point[round];
            if eq_acc * ((F192::ONE + rj) * msg[0] + rj * msg[1]) != claim {
                return Err(Error::Sumcheck { layer, round });
            }
            let challenge = vs.sample();
            rho.push(challenge);
            eq_acc *= F192::ONE + rj + challenge;
            claim = eq_acc * lagrange_eval(&nodes, &msg, challenge);
        }
        let evals = vs.next_scalars(4).map_err(|_| Error::Truncated)?;
        let gate = evals[0] * evals[3] + evals[1] * evals[2] + lambda * evals[2] * evals[3];
        if claim != eq_acc * gate {
            return Err(Error::Layer { layer });
        }
        let child = vs.sample();
        num_claim = interp(evals[0], evals[1], child);
        den_claim = interp(evals[2], evals[3], child);
        lambda = vs.sample();
        point.clear();
        point.push(child);
        point.extend_from_slice(&rho);
    }

    Ok(Output {
        point,
        num: num_claim,
        den: den_claim,
    })
}

fn fold(values: &mut Vec<F192>, challenge: F192) {
    let half = values.len() / 2;
    for i in 0..half {
        values[i] = interp(values[2 * i], values[2 * i + 1], challenge);
    }
    values.truncate(half);
}

fn shrink_eq(eq: &mut Vec<F192>) {
    let half = eq.len() / 2;
    for i in 0..half {
        eq[i] = eq[2 * i] + eq[2 * i + 1];
    }
    eq.truncate(half);
}

/// Sumcheck for `<left, right> = claim`, returning both evaluations at one point.
pub fn prove_inner_product(mut left: Vec<F192>, mut right: Vec<F192>, claim: F192, ps: &mut ProverState) -> Output {
    assert_eq!(left.len(), right.len());
    assert!(left.len().is_power_of_two());
    debug_assert_eq!(
        left.iter().zip(&right).fold(F192::ZERO, |acc, (&a, &b)| acc + a * b),
        claim
    );
    let rounds = left.len().ilog2() as usize;
    let nodes = [F192::ZERO, F192::ONE, F192::from(G)];
    let mut point = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let half = left.len() / 2;
        let mut msg = [F192::ZERO; 3];
        for i in 0..half {
            for (j, &t) in nodes.iter().enumerate() {
                msg[j] += interp(left[2 * i], left[2 * i + 1], t) * interp(right[2 * i], right[2 * i + 1], t);
            }
        }
        ps.add_scalars(&msg);
        let r = ps.sample();
        point.push(r);
        fold(&mut left, r);
        fold(&mut right, r);
    }
    ps.add_scalars(&[left[0], right[0]]);
    Output {
        point,
        num: left[0],
        den: right[0],
    }
}

pub fn verify_inner_product(rounds: usize, mut claim: F192, vs: &mut VerifierState) -> Result<Output, Error> {
    let nodes = tri_nodes();
    let mut point = Vec::with_capacity(rounds);
    for round in 0..rounds {
        let msg = vs.next_scalars(3).map_err(|_| Error::Truncated)?;
        if msg[0] + msg[1] != claim {
            return Err(Error::Sumcheck { layer: 0, round });
        }
        let r = vs.sample();
        point.push(r);
        claim = lagrange_eval(&nodes, &msg, r);
    }
    let evals = vs.next_scalars(2).map_err(|_| Error::Truncated)?;
    if evals[0] * evals[1] != claim {
        return Err(Error::Layer { layer: 0 });
    }
    Ok(Output {
        point,
        num: evals[0],
        den: evals[1],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fraction_and_inner_product_roundtrip() {
        let nums: Vec<F192> = (0..16).map(|i| F192::new(i + 1, i * 3, 0)).collect();
        let dens: Vec<F192> = (0..16).map(|i| F192::new(i + 17, 1, i)).collect();
        let circuit = Circuit::new(nums, dens);
        let roots = circuit.root();

        let left: Vec<F192> = (0..8).map(|i| F192::new(i + 2, i + 5, 1)).collect();
        let right: Vec<F192> = (0..8).map(|i| F192::new(i + 11, 2 * i, 3)).collect();
        let inner = left.iter().zip(&right).fold(F192::ZERO, |acc, (&a, &b)| acc + a * b);

        let mut ps = ProverState::new(b"frac-gkr-test", &[]);
        ps.add_scalars(&[roots.0, roots.1]);
        let expected_fraction = circuit.prove(&mut ps);
        let expected_inner = prove_inner_product(left, right, inner, &mut ps);
        let proof = ps.into_proof();

        let mut vs = VerifierState::new(b"frac-gkr-test", &proof, &[]);
        let sent = vs.next_scalars(2).unwrap();
        let fraction = verify(4, sent[0], sent[1], &mut vs).unwrap();
        let product = verify_inner_product(3, inner, &mut vs).unwrap();
        vs.finish().unwrap();

        assert_eq!(fraction.point, expected_fraction.point);
        assert_eq!(
            (fraction.num, fraction.den),
            (expected_fraction.num, expected_fraction.den)
        );
        assert_eq!(product.point, expected_inner.point);
        assert_eq!((product.num, product.den), (expected_inner.num, expected_inner.den));
    }
}
