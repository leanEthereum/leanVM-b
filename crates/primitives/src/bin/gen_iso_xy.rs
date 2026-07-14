//! Regenerate the GHASH <-> tower isomorphism matrices for the binius64 tower
//! `F128T` (`y^2 = x*y + 1`), to replace the Artin-Schreier matrices in
//! `iso_f128.rs`.
//!
//! `X` (the K-generator's image in GHASH) is tower-independent, so we extract it
//! from the *existing* iso via `tower_to_ghash(x)`. We then solve `Y^2 = X*Y + 1`
//! for the binius root, rebuild `psi(x^i y^j) = X^i Y^j`, invert it by F2 Gaussian
//! elimination, and verify the result is a field homomorphism both ways over 100k
//! random inputs before printing the arrays. Arch-independent output.
//!
//! Run: `cargo run --release -p primitives --bin gen_iso_xy > /tmp/iso_xy.txt`

use primitives::field::gf2_64::F64;
use primitives::field::iso_f128::tower_to_ghash;
use primitives::field::{F128, F128T};

fn u(a: F128) -> u128 {
    ((a.hi as u128) << 64) | a.lo as u128
}
fn f(v: u128) -> F128 {
    F128::new(v as u64, (v >> 64) as u64)
}
fn gadd(a: F128, b: F128) -> F128 {
    F128::new(a.lo ^ b.lo, a.hi ^ b.hi)
}

/// Solve, over F2, `XOR_{k: y_k=1} cols[k] = rhs` for the 128-bit vector `y`.
/// Each row carries `(image, preimage)` with the invariant `image = XOR of
/// cols[k] over set bits of preimage`, preserved through elimination.
fn solve(cols: &[u128; 128], rhs: u128) -> Option<u128> {
    let mut rows: Vec<(u128, u128)> = (0..128).map(|k| (cols[k], 1u128 << k)).collect();
    let mut piv: Vec<(u128, u128)> = Vec::new();
    for bit in (0..128).rev() {
        if let Some(pos) = rows.iter().position(|&(img, _)| (img >> bit) & 1 == 1) {
            let lead = rows.swap_remove(pos);
            for r in rows.iter_mut() {
                if (r.0 >> bit) & 1 == 1 {
                    r.0 ^= lead.0;
                    r.1 ^= lead.1;
                }
            }
            piv.push(lead);
        }
    }
    let mut r = rhs;
    let mut y = 0u128;
    for &(img, pre) in &piv {
        let bit = 127 - img.leading_zeros();
        if (r >> bit) & 1 == 1 {
            r ^= img;
            y ^= pre;
        }
    }
    (r == 0).then_some(y)
}

fn main() {
    // X = image of the K-generator x in GHASH (tower-independent).
    let x = tower_to_ghash(F128T::new(F64::G.0, 0));

    // Sanity: X satisfies x^64 + x^4 + x^3 + x + 1 = 0 in GHASH.
    let pow = |a: F128, n: u32| (0..n).fold(F128::ONE, |acc, _| acc * a);
    let kpoly = gadd(gadd(gadd(gadd(pow(x, 64), pow(x, 4)), pow(x, 3)), x), F128::ONE);
    assert_eq!(kpoly, F128::ZERO, "X does not satisfy the K minimal polynomial");

    // Solve Y^2 + X*Y = 1 (binius relation). L(Y) = Y^2 + X*Y is F2-linear.
    let mut lcols = [0u128; 128];
    for (k, c) in lcols.iter_mut().enumerate() {
        let e = f(1u128 << k);
        *c = u(gadd(e * e, x * e));
    }
    let y = f(solve(&lcols, u(F128::ONE)).expect("no root of y^2 + x*y + 1"));
    assert_eq!(y * y, gadd(x * y, F128::ONE), "Y is not a root of y^2 + x*y + 1");

    // psi columns: tower basis x^i y^j -> X^i Y^j in GHASH.
    let mut xpow = [F128::ONE; 64];
    for i in 1..64 {
        xpow[i] = xpow[i - 1] * x;
    }
    let mut cols = [0u128; 128];
    for i in 0..64 {
        cols[i] = u(xpow[i]);
        cols[64 + i] = u(xpow[i] * y);
    }

    let t2g: Vec<(u64, u64)> = cols.iter().map(|&c| (c as u64, (c >> 64) as u64)).collect();
    let g2t: Vec<(u64, u64)> = (0..128)
        .map(|j| {
            let v = solve(&cols, 1u128 << j).expect("psi not invertible");
            (v as u64, (v >> 64) as u64)
        })
        .collect();

    // Homomorphism verification using the freshly built matrices.
    let t2g_map = |a: F128T| -> F128 {
        let mut acc = 0u128;
        for k in 0..128 {
            let bit = if k < 64 { (a.c0 >> k) & 1 } else { (a.c1 >> (k - 64)) & 1 };
            if bit == 1 {
                acc ^= cols[k];
            }
        }
        f(acc)
    };
    let g2t_map = |a: F128| -> F128T {
        let (mut c0, mut c1) = (0u64, 0u64);
        for k in 0..128 {
            let bit = if k < 64 { (a.lo >> k) & 1 } else { (a.hi >> (k - 64)) & 1 };
            if bit == 1 {
                c0 ^= g2t[k].0;
                c1 ^= g2t[k].1;
            }
        }
        F128T::new(c0, c1)
    };

    let mut s = 0x1234_5678u64;
    let mut rnd = || {
        s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        s
    };
    for _ in 0..100_000 {
        let (a, b) = (F128T::new(rnd(), rnd()), F128T::new(rnd(), rnd()));
        assert_eq!(t2g_map(a * b), t2g_map(a) * t2g_map(b), "psi not multiplicative");
        assert_eq!(g2t_map(t2g_map(a)), a, "phi.psi != id");
        let (g, h) = (F128::new(rnd(), rnd()), F128::new(rnd(), rnd()));
        assert_eq!(g2t_map(g * h), g2t_map(g) * g2t_map(h), "phi not multiplicative");
        assert_eq!(t2g_map(g2t_map(g)), g, "psi.phi != id");
    }
    eprintln!("verification ok: 100k random multiplicativity + round-trip checks passed");

    let emit = |name: &str, m: &[(u64, u64)]| {
        println!("pub(crate) const {name}: [(u64, u64); 128] = [");
        for &(a, b) in m {
            println!("    (0x{a:016x}, 0x{b:016x}),");
        }
        println!("];");
    };
    emit("GHASH_TO_TOWER", &g2t);
    println!();
    emit("TOWER_TO_GHASH", &t2g);
}
