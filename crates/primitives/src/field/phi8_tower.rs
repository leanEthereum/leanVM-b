// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
// Copyright 2025 The Binius Developers / Irreducible, Inc.
// Modifications copyright 2026 Succinct Labs, Benedikt Bunz, William Wang.
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! `φ₈: GF(2⁸) → F64`, embedded in either supported extension field.
//!
//! `im(φ₈) ⊂ F64`, hence all extension limbs above `c0` are zero. The eight basis images are generated
//! by `gen_phi8_tower`; the homomorphism is checked exhaustively below.

use super::{F8, F128T, F192};

/// φ₈(2ᵏ) for k ∈ [0,8): the images of the GF(2⁸) polynomial basis. All in
/// `F64` (c1 == 0). See module docs for provenance.
const PHI_8_BASIS: [F128T; 8] = [
    F128T::new(0x0000000000000001, 0x0000000000000000),
    F128T::new(0x033ce8beddc8a656, 0x0000000000000000),
    F128T::new(0x512620375ed2a108, 0x0000000000000000),
    F128T::new(0x0c9e636090aafc01, 0x0000000000000000),
    F128T::new(0xba4f3cd82801769c, 0x0000000000000000),
    F128T::new(0xba26e7904adb4a47, 0x0000000000000000),
    F128T::new(0x467698598926dc01, 0x0000000000000000),
    F128T::new(0x4418ae808b28bdd0, 0x0000000000000000),
];

const fn build_phi8_table() -> [F128T; 256] {
    let mut table = [F128T::ZERO; 256];
    let mut value = 1;
    while value < table.len() {
        let mut c0 = 0u64;
        let mut bit = 0;
        while bit < PHI_8_BASIS.len() {
            if value & (1 << bit) != 0 {
                c0 ^= PHI_8_BASIS[bit].c0;
                // c1 is 0 for every basis vector, so the image stays in F64.
            }
            bit += 1;
        }
        table[value] = F128T::new(c0, 0);
        value += 1;
    }
    table
}

pub static PHI_8_TABLE: [F128T; 256] = build_phi8_table();

const fn build_phi8_table_192() -> [F192; 256] {
    let mut table = [F192::ZERO; 256];
    let mut value = 0;
    while value < table.len() {
        table[value] = F192::new(PHI_8_TABLE[value].c0, 0, 0);
        value += 1;
    }
    table
}

/// The same unique GF(2^8) subfield embedded in F192. It lies in the common
/// F64 base, so both higher extension coordinates are zero.
pub static PHI_8_TABLE_192: [F192; 256] = build_phi8_table_192();

#[inline]
pub fn phi8(a: F8) -> F128T {
    PHI_8_TABLE[a.0 as usize]
}

#[inline]
pub fn phi8_192(a: F8) -> F192 {
    PHI_8_TABLE_192[a.0 as usize]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_images() {
        assert_eq!(phi8(F8::ZERO), F128T::ZERO);
        assert_eq!(phi8(F8::ONE), F128T::ONE);
        assert_eq!(phi8(F8(2)), PHI_8_BASIS[1]);
    }

    #[test]
    fn images_live_in_f64() {
        // The GF(2⁸) subfield of F128T lies in F64, so c1 == 0 everywhere.
        for v in 0u16..256 {
            assert_eq!(phi8(F8(v as u8)).c1, 0, "phi8({v}) escaped F64");
        }
    }

    #[test]
    fn homomorphism_full() {
        // Exhaustive: φ(a·b)=φ(a)·φ(b) and φ(a+b)=φ(a)+φ(b) over all 65536 pairs.
        for a in 0u16..256 {
            for b in 0u16..256 {
                let fa = F8(a as u8);
                let fb = F8(b as u8);
                assert_eq!(phi8(fa * fb), phi8(fa) * phi8(fb), "mul at a={a}, b={b}");
                assert_eq!(phi8(fa + fb), phi8(fa) + phi8(fb), "add at a={a}, b={b}");
            }
        }
    }
}
