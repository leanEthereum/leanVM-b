//! Generate the tower (`F128T`) φ₈ basis as the iso-image of the GHASH basis.
//!
//! φ₈: GF(2⁸) → GF(2¹²⁸) is a GF(2)-linear field embedding fixed by the image
//! of the AES generator (a root of x⁸+x⁴+x³+x+1). The GHASH basis lives in
//! `primitives::field::phi8`; applying the field isomorphism `ghash_to_tower`
//! to each basis vector yields a *valid tower embedding* (an isomorphism carries
//! roots of the AES polynomial to roots), and it is the canonical choice: every
//! downstream φ₈-derived value (flock's skip claim, the PCS ring-switch weights)
//! becomes exactly the iso-image of today's value, so the migration is
//! output-preserving on the PCS-facing side.
//!
//! Run: `cargo run --release -p primitives --bin gen_phi8_tower`
//! Prints the 8 `F128T` basis literals and checks the homomorphism exhaustively.

use primitives::field::{F8, F128T, ghash_to_tower, phi8};

/// Build the 256-entry table from an 8-vector basis (GF(2)-linear span).
fn build_table(basis: &[F128T; 8]) -> [F128T; 256] {
    let mut table = [F128T::ZERO; 256];
    for value in 1usize..256 {
        let mut image = F128T::ZERO;
        for (bit, b) in basis.iter().enumerate() {
            if value & (1 << bit) != 0 {
                image = F128T::new(image.c0 ^ b.c0, image.c1 ^ b.c1);
            }
        }
        table[value] = image;
    }
    table
}

fn main() {
    // Tower basis = ghash_to_tower(ghash basis). ghash basis[k] = phi8(2^k).
    let mut basis = [F128T::ZERO; 8];
    for (k, slot) in basis.iter_mut().enumerate() {
        *slot = ghash_to_tower(phi8(F8(1u8 << k)));
    }

    let table = build_table(&basis);

    // Sanity: table[2^k] == basis[k], table[1] == ONE, table[0] == ZERO.
    assert_eq!(table[1], F128T::ONE, "phi8(1) must be ONE");
    for k in 0..8 {
        assert_eq!(table[1usize << k], basis[k], "basis/table mismatch at k={k}");
    }

    // Exhaustive homomorphism: φ(a·b)=φ(a)·φ(b) and φ(a+b)=φ(a)+φ(b).
    for a in 0u16..256 {
        for b in 0u16..256 {
            let fa = F8(a as u8);
            let fb = F8(b as u8);
            let lhs_mul = table[(fa * fb).0 as usize];
            let rhs_mul = table[fa.0 as usize] * table[fb.0 as usize];
            assert_eq!(lhs_mul, rhs_mul, "MUL homomorphism fails at a={a}, b={b}");
            let lhs_add = table[(fa + fb).0 as usize];
            let rhs_add = F128T::new(
                table[fa.0 as usize].c0 ^ table[fb.0 as usize].c0,
                table[fa.0 as usize].c1 ^ table[fb.0 as usize].c1,
            );
            assert_eq!(lhs_add, rhs_add, "ADD homomorphism fails at a={a}, b={b}");
        }
    }

    // The GF(2⁸) subfield of F128T lives inside F64, so every image should have
    // c1 == 0. (If this fails, my tower-subfield reasoning is wrong.)
    let all_in_f64 = basis.iter().all(|b| b.c1 == 0);

    println!("// φ₈ tower basis (iso-image of GHASH basis). Homomorphism: OK (exhaustive).");
    println!("// images land in F64 (c1==0): {all_in_f64}");
    println!("const PHI_8_BASIS_TOWER: [F128T; 8] = [");
    for b in &basis {
        println!("    F128T::new(0x{:016x}, 0x{:016x}),", b.c0, b.c1);
    }
    println!("];");
}
