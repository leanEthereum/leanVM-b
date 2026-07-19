//! The ISA and the `DEREF` store modes.

use primitives::field::F64;

#[derive(Clone, Copy, Debug)]
pub enum Op {
    Xor {
        a: u32,
        b: u32,
        c: u32,
    },
    Mul {
        a: u32,
        b: u32,
        c: u32,
    },
    /// Extension-field addition on three consecutive base-field words:
    /// `mem[c..c+3] = mem[a..a+3] + mem[b..b+3]` in F2^192.
    AddExt {
        a: u32,
        b: u32,
        c: u32,
    },
    /// Extension-field multiplication on three consecutive base-field words:
    /// `mem[c..c+3] = mem[a..a+3] * mem[b..b+3]` in F2^192.
    MulExt {
        a: u32,
        b: u32,
        c: u32,
    },
    Set {
        o: u32,
        /// The 64-bit base-field immediate stored into `mem[fp·o]`.
        k: F64,
    },
    Deref {
        alpha: u32,
        beta: u32,
        gamma: u32,
        mode: DerefMode,
    },
    Jump {
        oc: u32,
        od: u32,
        of: u32,
    },
    /// `BLAKE3`: compress the two 256-bit operands at the four-word runs
    /// `a..a+4` and `b..b+4`, writing the digest to `c..c+4`.
    Blake3 {
        a: u32,
        b: u32,
        c: u32,
    },
}

/// The source `DEREF` stores at `mem[loc_α·β]` (§1): a local cell, the return
/// address `pc+γ`, or the frame pointer. Encoded as two boolean flags `(f_pc,
/// f_fp)` — `Cell=(0,0)`, `Pc=(1,0)`, `Fp=(0,1)` — keeping the store constraint degree 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerefMode {
    Cell,
    Pc,
    Fp,
}

impl DerefMode {
    pub(crate) fn f_pc(self) -> F64 {
        if self == DerefMode::Pc { F64::ONE } else { F64::ZERO }
    }
    pub(crate) fn f_fp(self) -> F64 {
        if self == DerefMode::Fp { F64::ONE } else { F64::ZERO }
    }
}
