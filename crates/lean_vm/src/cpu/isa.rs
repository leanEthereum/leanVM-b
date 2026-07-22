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
    /// `BLAKE3` (§7.6): compresses a 64-byte message block and writes the
    /// 32-byte digest to the two consecutive words `out`, `out+1`. The two CV
    /// words and the first two message words are addressed independently. The
    /// last two message words occupy the consecutive cells `ins[2]`,
    /// `ins[2]+1`, preserving six bytecode offset slots while making keyed
    /// hashing cheap when the key halves come from unrelated cells.
    Blake3 {
        /// First two message-word offsets, then the base of the consecutive
        /// second message half.
        ins: [u32; 3],
        /// Independently addressed 128-bit halves of the chaining value/key.
        cv: [u32; 2],
        out: u32,
        /// `counter:u64 | block_len:u32 | flags:u32`, little-endian.
        metadata: F128,
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
