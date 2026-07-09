//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].

use super::DerefMode;
use crate::field::F64;

pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    pub(crate) aa: u32,
    pub(crate) ab: u32,
    pub(crate) ac: u32,
    pub(crate) ra: F64,
    pub(crate) rb: F64,
    pub(crate) rc: F64,
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) o: u32,
    pub(crate) a: u32,
    pub(crate) k: F64,
    pub(crate) r: F64,
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) alpha: u32,
    pub(crate) beta: u32,
    pub(crate) gamma: u32,
    pub(crate) mode: DerefMode,
    pub(crate) a1: u32,
    pub(crate) p: F64,
    pub(crate) a2: usize,
    pub(crate) a3: u32,
    pub(crate) v2: F64, // mem[a2], the store target
    pub(crate) v3: F64, // mem[a3], the local cell
    pub(crate) r1: F64,
    pub(crate) r2: F64,
    pub(crate) r3: F64,
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) npc: F64,
    pub(crate) nfp: F64,
    pub(crate) oc: u32,
    pub(crate) od: u32,
    pub(crate) of: u32,
    pub(crate) ac: u32,
    pub(crate) ad: u32,
    pub(crate) af: u32,
    pub(crate) c: F64,
    pub(crate) d: F64,
    pub(crate) f: F64,
    pub(crate) w: F64, // inverse hint (is-nonzero witness): c⁻¹ when c ≠ 0, else 0
    pub(crate) b: F64, // taken indicator b = [c ≠ 0]
    pub(crate) rc: F64,
    pub(crate) rd: F64,
    pub(crate) rf: F64,
    pub(crate) bytecode_read: F64,
}

/// `BLAKE3` row: the four independent input-chunk base addresses `aa0, aa1,
/// ab0, ab1` (each spanning two consecutive words) and the output base `ac`
/// (spanning four words), the twelve word values (four inputs `a` at
/// `aa0, aa0+1, aa1, aa1+1`, four inputs `b` likewise, four outputs `c`), and
/// the twelve per-word memory access counts.
pub(crate) struct Brow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) aa0: u32,
    pub(crate) aa1: u32,
    pub(crate) ab0: u32,
    pub(crate) ab1: u32,
    pub(crate) ac: u32,
    pub(crate) va: [F64; 4],
    pub(crate) vb: [F64; 4],
    pub(crate) vc: [F64; 4],
    pub(crate) ra: [F64; 4],
    pub(crate) rb: [F64; 4],
    pub(crate) rc: [F64; 4],
    pub(crate) bytecode_read: F64,
}

pub(crate) struct Trace {
    pub(crate) xor: Vec<Xrow>,
    pub(crate) mul: Vec<Xrow>,
    pub(crate) set: Vec<Srow>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Jrow>,
    pub(crate) blake3: Vec<Brow>,
    pub(crate) mem_count: Vec<F64>, // per-cell running access count g^{count}; final = g^{A[i]}
    pub(crate) bytecode_count: Vec<F64>, // per-pc running execution count g^{count}; final = g^{A[pc]}
}
