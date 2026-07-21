//! The ISA and the `DEREF` store modes.

use primitives::field::{F64, F128T};

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
        /// The immediate stored into `mem[fp·o]`. A full 128-bit machine word
        /// (`E = F128T`); K-valued constants (addresses, small ints) ride the
        /// low lane with `c1 = 0`.
        k: F128T,
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
    /// Read two K-valued (64-bit) cells and pack them canonically into one
    /// 128-bit cell: `c = (a.c0, b.c0)`. The memory bus reads the sources as
    /// `(lo, 0)`, so executing this instruction also proves both source
    /// words lie in K = F64.
    Pack64x2 {
        a: u32,
        b: u32,
        c: u32,
    },
    /// `BLAKE3` (§7.6): compresses the 64-byte input `ins[0]‖ins[1]‖ins[2]‖ins[3]`
    /// (each `ins[i]` names a 128-bit chunk in ONE 128-bit memory word `fp+ins[i]`)
    /// and writes the 32-byte digest to the TWO consecutive words `out, out+1`.
    /// Each input chunk is addressed independently — no forced contiguity, so the
    /// caller need not assemble its operands into adjacent cells. The compression
    /// relation is proven by flock.
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
    pub(crate) fn f_pc(self) -> F64 {
        if self == DerefMode::Pc { F64::ONE } else { F64::ZERO }
    }
    pub(crate) fn f_fp(self) -> F64 {
        if self == DerefMode::Fp { F64::ONE } else { F64::ZERO }
    }
}
