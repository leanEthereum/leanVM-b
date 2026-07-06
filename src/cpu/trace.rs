//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].

use super::DerefMode;
use crate::field::F128;

pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    pub(crate) aa: u32,
    pub(crate) ab: u32,
    pub(crate) ac: u32,
    pub(crate) ra: F128,
    pub(crate) rb: F128,
    pub(crate) rc: F128,
    pub(crate) bytecode_read: F128,
}
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) o: u32,
    pub(crate) a: u32,
    pub(crate) k: F128,
    pub(crate) r: F128,
    pub(crate) bytecode_read: F128,
}
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) alpha: u32,
    pub(crate) beta: u32,
    pub(crate) gamma: u32,
    pub(crate) mode: DerefMode,
    pub(crate) a1: u32,
    pub(crate) p: F128,
    pub(crate) a2: usize,
    pub(crate) a3: u32,
    pub(crate) v2: F128, // mem[a2], the store target
    pub(crate) v3: F128, // mem[a3], the local cell
    pub(crate) r1: F128,
    pub(crate) r2: F128,
    pub(crate) r3: F128,
    pub(crate) bytecode_read: F128,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) npc: F128,
    pub(crate) nfp: F128,
    pub(crate) oc: u32,
    pub(crate) od: u32,
    pub(crate) of: u32,
    pub(crate) ac: u32,
    pub(crate) ad: u32,
    pub(crate) af: u32,
    pub(crate) c: F128,
    pub(crate) d: F128,
    pub(crate) f: F128,
    pub(crate) w: F128, // inverse hint (is-nonzero witness): c⁻¹ when c ≠ 0, else 0
    pub(crate) b: F128, // taken indicator b = [c ≠ 0]
    pub(crate) rc: F128,
    pub(crate) rd: F128,
    pub(crate) rf: F128,
    pub(crate) bytecode_read: F128,
}

/// `BLAKE3` row: the four independent input-word addresses `aa0, aa1, ab0, ab1`
/// and the output base `ac` (spanning two words), the six word values (four
/// inputs, two outputs `c`), and the six per-word memory access counts.
pub(crate) struct Brow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) aa0: u32,
    pub(crate) aa1: u32,
    pub(crate) ab0: u32,
    pub(crate) ab1: u32,
    pub(crate) ac: u32,
    pub(crate) va0: F128,
    pub(crate) va1: F128,
    pub(crate) vb0: F128,
    pub(crate) vb1: F128,
    pub(crate) vc0: F128,
    pub(crate) vc1: F128,
    pub(crate) ra0: F128,
    pub(crate) ra1: F128,
    pub(crate) rb0: F128,
    pub(crate) rb1: F128,
    pub(crate) rc0: F128,
    pub(crate) rc1: F128,
    pub(crate) bytecode_read: F128,
}

pub(crate) struct Trace {
    pub(crate) xor: Vec<Xrow>,
    pub(crate) mul: Vec<Xrow>,
    pub(crate) set: Vec<Srow>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Jrow>,
    pub(crate) blake3: Vec<Brow>,
    pub(crate) mem_count: Vec<F128>, // per-cell running access count g^{count}; final = g^{A[i]}
    pub(crate) bytecode_count: Vec<F128>, // per-pc running execution count g^{count}; final = g^{A[pc]}
}
