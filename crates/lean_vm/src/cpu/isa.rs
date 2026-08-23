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
    /// `Keccak`: one sponge step, `permute(prev ^ (msg || 0...0))`. Absorbing a
    /// 136-byte rate block and permuting is ONE instruction, which is what makes
    /// hashing a long message affordable: the XOR is free over GF(2), so the
    /// circuit does it.
    ///
    /// The rate block is 17 lanes carried as nine 128-bit cells, split so that a
    /// 64-byte hash pays for none of it:
    ///
    /// - `ins` addresses the four cells holding lanes 0..8 INDEPENDENTLY, with
    ///   no forced contiguity, so a caller hashing `(a, b)` need not copy its
    ///   operands anywhere.
    /// - `rest` is the base of the five consecutive cells holding lanes 8..18.
    ///   For SHA3-256 of 64 bytes those are the constant `pad10*1`, so a scope
    ///   builds them once and every hash in it shares them.
    ///
    /// `prev` is the base of the thirteen consecutive cells holding the running
    /// state, all zero to start a hash, which costs nothing: a cell the VM never
    /// writes reads as zero. The result lands in the thirteen consecutive cells
    /// based at `out`. Each region's last high lane is the layout's zero pad,
    /// which the R1CS forces to zero.
    ///
    /// There is no immediate: a permutation has no byte counter and no
    /// finalization flag. The relation is proven by flock.
    Keccak {
        ins: [u32; 4],
        rest: u32,
        prev: u32,
        out: u32,
    },
}

/// The source `DEREF` stores at `mem[loc_α·β]`: a local cell, the return
/// address `g²·pc`, or the frame pointer. Encoded as two boolean flags `(f_pc,
/// f_fp)`: `Cell=(0,0)`, `Pc=(1,0)`, `Fp=(0,1)`, keeping the store constraint degree 2.
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
