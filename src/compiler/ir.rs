//! Lowered intermediate instructions and hints, between the AST and final assembly.

use super::*;

pub(crate) type Off = u32;

/// A `SET` immediate: a field constant, or a function entry address resolved
/// once entry program counters are fixed.
#[derive(Clone, Debug)]
pub(crate) enum KVal {
    Const(F128),
    Entry(String),
    /// The halt sentinel pc `g^{B-1}` (last bytecode slot), fixed once the
    /// padded bytecode size `B` is known. `main` jumps here to terminate.
    EndSentinel,
    /// An intra-function jump target: the `i`-th instruction of the function
    /// this `SET` belongs to, resolved to `g^{entry + i}` once entry pcs are
    /// fixed. Emitted with a placeholder by the `if`/`else` lowering and
    /// backpatched ([`FnLower::patch_local`]).
    Local(u32),
}

#[derive(Clone, Debug)]
pub(crate) struct LInstr {
    pub(crate) op: LOp,
    /// Prover hints applied (in order) *before* this instruction during witness
    /// generation.
    pub(crate) hints: Vec<Hint>,
}

/// A `JUMP` target: read from a frame cell, or an immediate code address.
#[derive(Clone, Debug)]
pub(crate) enum JumpDest {
    Indirect(Off),
    Direct(KVal),
}

#[derive(Clone, Debug)]
pub(crate) enum LOp {
    Set {
        o: Off,
        k: KVal,
    },
    Xor {
        a: Off,
        b: Off,
        c: Off,
    },
    Mul {
        a: Off,
        b: Off,
        c: Off,
    },
    Deref {
        alpha: Off,
        beta: Off,
        gamma: Off,
        mode: DerefMode,
    },
    Jump {
        oc: Off,
        of: Off,
        /// The jump target: a cell (`m[fp·g^od]`) or an immediate code address
        /// (a resolved `KVal`, avoiding a `SET` of a constant target).
        dest: JumpDest,
    },
    /// `BLAKE3`: the four input words `ins` are addressed independently (`fp+ins[i]`);
    /// the 32-bit output `c = (c, c+1)` occupies two CONSECUTIVE frame cells.
    Blake3 {
        ins: [Off; 4],
        c: Off,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum Hint {
    /// `m[fp·g^ptr] = g^{fresh base}` — a fresh, disjoint frame for `callee`.
    AllocFrame { ptr: Off, callee: String },
    /// `AllocFrame` sized to the **largest** of several callees — a shared frame
    /// for a dispatched call (all `callees` share the arg/return layout; only
    /// their local count, hence frame size, differs). See [`FnLower::lower_dispatched_call`].
    AllocFrameMax { ptr: Off, callees: Vec<String> },
    /// `m[fp·g^ptr] = g^{fresh base}` — a fresh, disjoint heap region of `size`
    /// cells (a `HeapBuf(size)`), addressed by g-power offsets from the pointer.
    AllocBuffer { ptr: Off, size: u32 },
    /// `AllocBuffer` with a *runtime* size in the exponent: the cell count is
    /// the g-power exponent of `m[fp·g^size]` (a `HeapBuf(size_expr)`).
    AllocBufferDyn { ptr: Off, size: Off },
    /// Pop stream `name`'s next entry (`len` values) into the frame cells
    /// `m[fp·g^{base+k}]`, `k < len`.
    WitnessStack { name: String, base: Off, len: u32 },
    /// Pop stream `name`'s next entry (`len` values) into the heap cells
    /// `m[p·g^{lo+k}]`, `k < len`, where `p = m[fp·g^ptr]`.
    WitnessHeap { name: String, ptr: Off, lo: u32, len: u32 },
}

pub(crate) struct Lowered {
    pub(crate) name: String,
    pub(crate) code: Vec<LInstr>,
    pub(crate) frame_size: u32,
}

/// A resolved 2-cell `blake3` operand: a frame (stack) run used in place, or a
/// heap slice — the buffer pointer's cell plus the first g-power offset —
/// which must be bridged through the stack (`BLAKE3` addresses only frame
/// cells).
pub(crate) enum B3Operand {
    Stack(Off),
    Heap { ptr: Off, lo: u32 },
}
