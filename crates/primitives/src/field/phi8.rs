// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright 2025 The Binius Developers
// Copyright 2025 Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The eight `PHI_8_BASIS` values come from binius64's `PHI_8` table
// (https://github.com/binius-zk/binius64, `crates/field/src/ghash.rs`).

//! φ₈: GF(2⁸) → GF(2¹²⁸)-GHASH subfield embedding.
//!
//! The embedding is GF(2)-linear, so the 256-entry [`PHI_8_TABLE`] is generated
//! at compile time from the images of the eight polynomial-basis vectors. The
//! basis images were extracted from binius64's `crates/field/src/ghash.rs` and
//! are checked here against the homomorphism property
//! `phi8(a*b) = phi8(a)*phi8(b)`.

use super::{F8, F128};

const PHI_8_BASIS: [F128; 8] = [
    F128::new(0x0000_0000_0000_0001, 0x0000_0000_0000_0000),
    F128::new(0x6b83_3048_3c2e_9849, 0x0dcb_3646_40a2_22fe),
    F128::new(0x7573_da4a_5f77_10ed, 0x3d5b_d35c_9464_6a24),
    F128::new(0x41a1_2db1_f974_f3ac, 0x6d58_c4e1_81f9_199f),
    F128::new(0x5e2f_716f_4ede_412f, 0xa72e_c177_64d7_ced5),
    F128::new(0x5cb1_0fba_bcf0_0118, 0x4d52_354a_3a3d_8c86),
    F128::new(0x95ed_1f57_f363_2d4d, 0x553e_92e8_bc0a_e9a7),
    F128::new(0x5126_25b1_f09f_a87e, 0x9325_2331_bf04_2b11),
];

const fn build_phi8_table() -> [F128; 256] {
    let mut table = [F128::ZERO; 256];
    let mut value = 1;
    while value < table.len() {
        let mut image = F128::ZERO;
        let mut bit = 0;
        while bit < PHI_8_BASIS.len() {
            if value & (1 << bit) != 0 {
                image.lo ^= PHI_8_BASIS[bit].lo;
                image.hi ^= PHI_8_BASIS[bit].hi;
            }
            bit += 1;
        }
        table[value] = image;
        value += 1;
    }
    table
}

pub static PHI_8_TABLE: [F128; 256] = build_phi8_table();

#[inline]
pub fn phi8(a: F8) -> F128 {
    PHI_8_TABLE[a.0 as usize]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_images_map_correctly() {
        assert_eq!(phi8(F8::ZERO), F128::ZERO);
        assert_eq!(phi8(F8::ONE), F128::ONE);
        assert_eq!(phi8(F8(2)), F128::new(0x6b83_3048_3c2e_9849, 0x0dcb_3646_40a2_22fe));
    }

    #[test]
    fn homomorphism_full() {
        // Exhaustive check: φ(a·b) = φ(a)·φ(b) and φ(a+b) = φ(a)+φ(b)
        // for all 65536 ordered pairs in F_8.
        for a in 0u8..=255 {
            for b in 0u8..=255 {
                let fa = F8(a);
                let fb = F8(b);
                let lhs_mul = phi8(fa * fb);
                let rhs_mul = phi8(fa) * phi8(fb);
                assert_eq!(lhs_mul, rhs_mul, "mul mismatch at a={a}, b={b}");

                let lhs_add = phi8(fa + fb);
                let rhs_add = phi8(fa) + phi8(fb);
                assert_eq!(lhs_add, rhs_add, "add mismatch at a={a}, b={b}");
            }
        }
    }
}
