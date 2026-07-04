//! Integration coverage for the >128-bit field F192 = GF((2^64)^3), through
//! the same `flare` re-export path the VM uses. The deep suite
//! (NEON-vs-reference on 10k random inputs, independent Python-generated
//! vectors, Frobenius/gcd irreducibility proofs of both moduli) lives in
//! `vendor/flock-core/src/field/gf2_64x3.rs` and runs with `cargo test`
//! inside `vendor/flock-core`; this file keeps the main-workspace
//! `cargo testall` honest about the essentials.

use flare::field::{F128, F192, F192Unreduced};
use rand::Rng;

fn rand_f192(rng: &mut impl Rng) -> F192 {
    F192::new(rng.random(), rng.random(), rng.random())
}

#[test]
fn f192_field_behaviour() {
    let mut rng = rand::rng();
    for _ in 0..500 {
        let (a, b, c) = (rand_f192(&mut rng), rand_f192(&mut rng), rand_f192(&mut rng));
        // ring axioms + agreement with the portable reference
        assert_eq!(a * b, flare::field::gf2_64x3::software::mul(a, b));
        assert_eq!(a * b, b * a);
        assert_eq!((a * b) * c, a * (b * c));
        assert_eq!(a * (b + c), a * b + a * c);
        assert_eq!(a.square(), a * a);
        if !a.is_zero() {
            assert_eq!(a * a.inv(), F192::ONE);
        }
    }
    // y^3 = y + 1 (the defining relation)
    assert_eq!(F192::Y * F192::Y * F192::Y, F192::Y + F192::ONE);
}

#[test]
fn deferred_reduction_matches_reduced_sums() {
    let mut rng = rand::rng();

    let mut acc192 = F192Unreduced::ZERO;
    let mut want192 = F192::ZERO;
    for _ in 0..256 {
        let (a, b) = (rand_f192(&mut rng), rand_f192(&mut rng));
        acc192 ^= a.mul_unreduced(b);
        want192 += a * b;
    }
    assert_eq!(acc192.reduce(), want192);
}

/// The F128 fast-squaring path added alongside the new fields.
#[test]
fn f128_square_matches_mul() {
    let mut rng = rand::rng();
    for _ in 0..500 {
        let a = F128::new(rng.random(), rng.random());
        assert_eq!(a.square(), a * a);
        if !a.is_zero() {
            assert_eq!(a * a.inv(), F128::ONE);
        }
    }
}
