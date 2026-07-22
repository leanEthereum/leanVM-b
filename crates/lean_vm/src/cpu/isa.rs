//! The ISA and the `DEREF` store modes.

use primitives::field::{F64, F192};

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
        /// The immediate stored into `mem[fp·o]`. A full 192-bit machine word
        /// (`E = F192`); K-valued constants (addresses, small ints) ride the
        /// low lane with `c1 = c2 = 0`.
        k: F192,
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
    /// 128-bit cell: `c = (a.c0, b.c0, 0)`. The memory bus reads the sources as
    /// `(lo, 0, 0)`, so executing this instruction also proves both source
    /// words lie in K = F64.
    Pack64x2 {
        a: u32,
        b: u32,
        c: u32,
    },
    /// `BLAKE3` (§7.6): one standard BLAKE3 compression. The four 16-byte
    /// message chunks `ins` (each a canonical 128-bit chunk in ONE 192-bit cell,
    /// top limb zero) form the 64-byte block; the digest lands in the TWO
    /// consecutive cells `out, out+1`. Each message chunk is addressed
    /// independently — no forced contiguity, so the caller need not assemble
    /// its operands into adjacent cells. The compression relation is proven by
    /// flock.
    Blake3 {
        ins: [u32; 4],
        /// Base of two consecutive cells holding the 256-bit chaining value
        /// (canonical 128-bit chunks, top limbs zero).
        cv: u32,
        out: u32,
        /// `counter:u64 | block_len:u32 | flags:u32`, little-endian, in the two
        /// low K-lanes of a 192-bit immediate (top lane always zero).
        metadata: F192,
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
