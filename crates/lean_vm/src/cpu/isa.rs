//! The ISA: the six opcodes and the `DEREF` store modes.

use primitives::field::F128;

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
    Set {
        o: u32,
        k: F128,
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
    /// `BLAKE3` (§7.6): compresses the four 64-byte input words `ins` (the two
    /// 256-bit operands `ins[0]‖ins[1]` and `ins[2]‖ins[3]`) and writes the
    /// 32-byte digest to the two consecutive words `out`, `out+1`. Each input
    /// word is addressed independently (`fp+ins[i]`) — no forced contiguity, so
    /// the caller need not assemble its operands into adjacent cells. The
    /// compression relation is proven by flock.
    Blake3 {
        ins: [u32; 4],
        out: u32,
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
    pub(crate) fn f_pc(self) -> F128 {
        if self == DerefMode::Pc { F128::ONE } else { F128::ZERO }
    }
    pub(crate) fn f_fp(self) -> F128 {
        if self == DerefMode::Fp { F128::ONE } else { F128::ZERO }
    }
}
