//! Lowered intermediate instructions and hints, between the AST and final assembly.

use super::*;

pub(crate) type Off = u32;

/// A `SET` immediate: a field constant, or a function entry address resolved
/// once entry program counters are fixed.
#[derive(Clone, Debug)]
pub(crate) enum KVal {
    /// A 192-bit machine-word constant. Source literals fill only c0/c1, while
    /// compiler-generated constants may use the full field.
    Const(F192),
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
        od: Off,
        of: Off,
    },
    /// `BLAKE2s`: the four 128-bit input chunks `ins` are addressed independently,
    /// one frame cell each. The 32-byte output occupies the two consecutive
    /// 128-bit cells `c, c+1`.
    Blake2s {
        ins: [Off; 4],
        cv: Off,
        c: Off,
        metadata: F192,
    },
}

/// A prover hint attached to an instruction. Most are already the runtime's own
/// [`RHint`] and pass straight through; the allocation ones are compiler-side,
/// since their size is only known once every function's frame is laid out.
#[derive(Clone, Debug)]
pub(crate) enum Hint {
    /// `m[fp·g^ptr] = g^{fresh base}`: a fresh, disjoint frame for `callee`.
    AllocFrame { ptr: Off, callee: String },
    /// `AllocFrame` sized to the **largest** of several callees, a shared frame
    /// for a dispatched call (all `callees` share the arg/return layout; only
    /// their local count, hence frame size, differs). See [`FnLower::lower_dispatched_call`].
    AllocFrameMax { ptr: Off, callees: Vec<String> },
    /// `m[fp·g^ptr] = g^{fresh base}`: a fresh, disjoint heap region of `size`
    /// cells (a `HeapBuf(size)`), addressed by g-power offsets from the pointer.
    AllocBuffer { ptr: Off, size: u32 },
    /// `AllocBuffer` with a *runtime* size in the exponent: the cell count is
    /// the g-power exponent of `m[fp·g^size]` (a `HeapBuf(size_expr)`).
    AllocBufferDyn { ptr: Off, size: Off },
    /// A hint that needs nothing from the layout: witness fills, computed
    /// advice, debug prints.
    Resolved(RHint),
}

pub(crate) struct Lowered {
    pub(crate) name: String,
    pub(crate) code: Vec<LInstr>,
    pub(crate) frame_size: u32,
    /// One past the last frame cell the CALLER touches: `2 + n_args +
    /// n_ret_cells` (retpc/retfp, the arguments, then the flattened return
    /// area). Cells below it cross the frame boundary (the caller writes the
    /// arguments and reads the returns), so a write to one of them is
    /// observable outside this function even when no instruction here reads it.
    /// Everything at or above it is a local temporary.
    pub(crate) abi_end: u32,
    /// Where the fill blocks start, so CSE can leave them alone: their operands are
    /// offsets into the frames the interpreter gives them, not this function's
    /// ([`crate::cse::cse`]). `code.len()` when there are none.
    pub(crate) filler_start: usize,
    /// Frame runs whose address escaped through `addr(sb)`, as `(base, len)`.
    /// Writes and reads through the resulting pointer are `DEREF`s that name no
    /// frame cell CSE can see, so these runs are excluded from it
    /// ([`crate::cse::cse`]).
    pub(crate) opaque_runs: Vec<(Off, u32)>,
    /// The fill blocks this function carries, with `code`-relative pcs; only `main` has
    /// any ([`crate::lower::FnLower::lower_filler_blocks`]).
    pub(crate) filler: Vec<lean_vm::cpu::filler::Block>,
}

/// A resolved run of consecutive cells ([`crate::lower::FnLower::cell_run`]): a
/// frame (stack) run, used in place, or a heap slice (the buffer pointer's cell
/// plus the first g-power offset), which a `blake2s` operand must bridge through
/// the stack since `BLAKE2s` addresses only frame cells.
pub(crate) enum CellRun {
    Stack { base: Off, len: u32 },
    Heap { ptr: Off, lo: u32, len: u32 },
}

impl CellRun {
    pub(crate) fn cells(&self) -> u32 {
        match *self {
            CellRun::Stack { len, .. } | CellRun::Heap { len, .. } => len,
        }
    }
}
