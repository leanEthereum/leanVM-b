//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].

use super::DerefMode;
use primitives::field::{F64, F128T};

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
    pub(crate) k: F128T, // the stored immediate, a 128-bit machine word
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
    pub(crate) p: F128T, // mem[a1], the pointer word (a K-valued address, read as a full word)
    pub(crate) a2: usize,
    pub(crate) a3: u32,
    pub(crate) v2: F128T, // mem[a2], the store target
    pub(crate) v3: F128T, // mem[a3], the local cell
    pub(crate) r1: F64,
    pub(crate) r2: F64,
    pub(crate) r3: F64,
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) npc: F64, // next pc — a K-valued address
    pub(crate) nfp: F64, // next fp — a K-valued address
    pub(crate) oc: u32,
    pub(crate) od: u32,
    pub(crate) of: u32,
    pub(crate) ac: u32,
    pub(crate) ad: u32,
    pub(crate) af: u32,
    pub(crate) c: F128T, // condition, an arbitrary 128-bit word
    pub(crate) d: F128T, // destination word (a K-valued code address, read as a full word)
    pub(crate) f: F128T, // new frame word (a K-valued frame pointer, read as a full word)
    pub(crate) w: F128T, // inverse hint (is-nonzero witness): c⁻¹ when c ≠ 0, else 0
    pub(crate) b: F64,   // taken indicator b = [c ≠ 0]
    pub(crate) rc: F64,
    pub(crate) rd: F64,
    pub(crate) rf: F64,
    pub(crate) bytecode_read: F64,
}

/// `BLAKE3` row: the four independent input-chunk addresses `aa0, aa1, ab0, ab1`
/// (each a single 128-bit cell) and the output base `ac` (spanning two cells),
/// the twelve flock words (four inputs `a`, four inputs `b`, four outputs `c` —
/// two 64-bit lanes per 128-bit cell), and the six per-cell memory access counts.
pub(crate) struct Brow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) aa0: u32,
    pub(crate) aa1: u32,
    pub(crate) ab0: u32,
    pub(crate) ab1: u32,
    pub(crate) ac: u32,
    pub(crate) va: [F64; 4], // a's four flock words = cells (aa0, aa1), lanes (lo, hi)
    pub(crate) vb: [F64; 4], // b's four flock words = cells (ab0, ab1)
    pub(crate) vc: [F64; 4], // c's four flock words = cells (ac, ac+1)
    pub(crate) ra: [F64; 2], // per-cell counts for the two a input cells
    pub(crate) rb: [F64; 2], // … the two b input cells
    pub(crate) rc: [F64; 2], // … the two c output cells
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
