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
    /// The poison pc `g^-1`, which lies outside the committed bytecode cube
    /// `{g^0, …, g^{B-1}}`. A failed `assert a != b` jumps here; since the
    /// bytecode channel seeds only the cube, a read at `g^-1` has no matching
    /// push and the bus cannot balance, so no valid proof continues past it.
    Poison,
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
    /// Computed advice for `ceil_log2`: read the `nbits` bits already in the
    /// buffer `m[fp·g^bits_ptr]`, reconstruct their integer value, and write
    /// `g^max(ceil_log2(value), floor)` into `m[fp·g^dst]`. Nondeterministic
    /// (prover-side); the emitting code re-verifies the result in-circuit.
    CeilLog2 { bits_ptr: Off, dst: Off, nbits: u32, floor: u32 },
    /// Computed advice: write the `nbits` bits of the value in `m[fp+value]`
    /// into the buffer `m[fp·g^bits_ptr]` (bit `j` at offset `j`). The emitting
    /// code re-checks booleanity + reconstruction in-circuit.
    Decompose { value: Off, bits_ptr: Off, nbits: u32 },
    /// Computed advice: write the `nbits` bits of `Σ_{i<count} 2^{κ_i}` into the
    /// buffer `m[fp·g^bits_ptr]`, where `g^{κ_i} = m[(m[fp·g^kappa_ptr])·g^{start+i}]`
    /// (each `κ_i` recovered as a small g-power). The emitting code re-checks it.
    DecomposeSum { kappa_ptr: Off, start: u32, count: u32, bits_ptr: Off, nbits: u32 },
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
