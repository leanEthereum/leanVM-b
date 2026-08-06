//! Lowering: each function AST is compiled to a sequence of intermediate
//! [`LOp`] instructions (fp-relative offsets, backpatched jump targets).

use super::*;
use crate::filler::FillerOp;
use lean_vm::cpu::filler::Block;

/// [`FnLower::specialized_body`]'s pieces: runtime param names, runtime args,
/// the `Const`-substituted body, and the callee's return arity.
type SpecializedBody = (Vec<String>, Vec<Expr>, Vec<Stmt>, usize);

/// A value equal to `pointer(base)·g^exp`, or the pure constant `g^exp` when
/// `base` is `None`. Heap-address arithmetic (`ptr·gᵏ`, and constant g-power
/// cursors such as a tweak-table index) is tracked symbolically so a later
/// access folds the whole offset into `DEREF`'s `β` immediate rather than
/// emitting a `SET`+`MUL` per step. A cursor read only as an index thus costs
/// nothing; one used as a value is materialized on demand ([`FnLower::materialize`]).
#[derive(Clone, Copy, Debug)]
struct GAddr {
    base: Option<Off>,
    exp: u128,
}

/// `a·b` in the [`GAddr`] representation: exponents add, and at most one factor
/// may carry a runtime base (two pointers can't be multiplied symbolically).
fn gmul(a: GAddr, b: GAddr) -> Option<GAddr> {
    let base = match (a.base, b.base) {
        (None, x) | (x, None) => x,
        (Some(_), Some(_)) => return None,
    };
    Some(GAddr {
        base,
        exp: a.exp.checked_add(b.exp)?,
    })
}

/// Cap on a `β`-folded exponent: the operand g-power table is sized to the
/// largest immediate, so beyond this a huge constant index falls back to a
/// materialized pointer instead of inflating that table. Tied to the smallest
/// admissible memory, like [`FnLower::try_gpow_index`]'s own cap.
const FOLD_MAX: u128 = 1 << lean_vm::cpu::MIN_LOG_MEM;

/// `b^k` for a compile-time exponent (small, so plain repeated multiplication).
fn field_pow(b: F64, k: u32) -> F64 {
    let mut acc = F64::ONE;
    for _ in 0..k {
        acc *= b;
    }
    acc
}

/// A deferred stack-cell store: the cell is a copy of another cell, or a zero.
/// Recorded instead of emitting the `MUL`/`SET`, and forwarded to the source at
/// each use ([`FnLower::word_src`], [`FnLower::chunk_src`]), so `BLAKE3`,
/// which addresses its four two-word input chunks independently, reads them in
/// place without assembling copies.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Alias {
    Cell(Off),
    /// A compile-time constant: forwarded at its uses to the pooled cell
    /// holding that value (`const_cell`), so a constant stored into a
    /// `blake3` operand cell (the `obs`/`squeeze` tag words, padding
    /// halves) costs ONE `SET` per distinct value per function, not one
    /// per store. A zero constant routes through the zero pool.
    Const(F64),
}

/// How an inlined `@inline` tail-return value binds into the caller
/// ([`FnLower::inline_stack_ret`]): a `StackBuf` hands over its cell run and a
/// folded g-address hands over its symbolic pointer, both aliased at zero
/// copies (so `cvb = obs(cvb, x)` and a fused `fs, x, cur = fs_next(fs, cur)`
/// stay free); a scalar was already copied into its dst cell.
#[derive(Clone, Copy)]
enum RetBind {
    Stack(Off, u32),
    Gaddr(GAddr),
    Scalar,
}

/// What a name is bound to, i.e. which of [`Scope`]'s maps holds it. The kinds
/// are mutually exclusive, so binding one clears the others ([`FnLower::rebind`]).
enum Binding {
    Scalar(Off),
    Stack(Off, u32),
    Gaddr(GAddr),
    FConst(F64),
}

/// Everything a runtime branch may not have executed: the name bindings, plus
/// the lazily materialized cells whose `SET` sits wherever it was first needed.
/// [`FnLower::scoped`] saves one of these and restores it at the join, so a
/// cell written on one path is never trusted on another.
#[derive(Clone, Default)]
struct Scope {
    vars: HashMap<String, Off>,
    /// `StackBuf` bindings: name → (base offset, size). The `size` cells
    /// `base..base+size` are consecutive frame cells (so a size-4 one, or a
    /// 4-cell slice of a larger one, is a direct `blake3` operand). Kept
    /// separate from `vars` since a stack value is a run of cells, not a
    /// single scalar.
    stacks: HashMap<String, (Off, u32)>,
    /// Names bound to integer literals (`x = 10`), usable in compile-time
    /// index positions: stack indexes and slice bounds. Cleared on rebind to
    /// anything else. (Index arithmetic is integer arithmetic: `x + 2` in a
    /// slice bound is 12, not the field XOR the same syntax means elsewhere.)
    consts: HashMap<String, u32>,
    /// Variables bound to a symbolic g-address ([`GAddr`]): index cursors and
    /// shifted pointers, kept virtual so their offsets fold into `DEREF`'s `β`.
    gaddrs: HashMap<String, GAddr>,
    /// Variables bound to a compile-time *field* constant that isn't a g-power
    /// (e.g. a running weight `CHAIN_LENGTH^i`). Kept virtual: folded through
    /// constant field arithmetic and materialized (one `SET`) only when used.
    fconsts: HashMap<String, F64>,
    /// The cell holding this function's own `fp`, materialized lazily
    /// ([`FnLower::self_fp`]): local (`if`/`else`) jumps reload the frame
    /// pointer on the taken branch.
    self_fp_off: Option<Off>,
    /// Range-check product-target cells: bound `k` → the frame cell holding
    /// `g^{k-1}`, set lazily once and shared by every check of that bound.
    bounds: HashMap<u64, Off>,
    /// Constant cells: field value (as bits) → the frame cell holding it, SET
    /// lazily once per distinct constant ([`FnLower::const_cell`]). Cells are
    /// write-once and read-many, so one `SET` serves every use in scope.
    const_cells: HashMap<u64, Off>,
    /// Fully constant three-word extension runs, pooled for extension
    /// instructions just like scalar constants. Without this, every use of a
    /// literal such as `[1, 0, 0]` is assembled with three MUL-by-one copies.
    ext_const_runs: HashMap<[u64; 3], Off>,
    /// Fully constant 128-bit BLAKE3 chunks. BLAKE3 addresses each two-word
    /// chunk by one base offset, so independently pooled scalar constants are
    /// not sufficient to forward a pair without copies.
    chunk_const_runs: HashMap<[u64; 2], Off>,
    /// A cached frame cell holding `0` (for forwarded zero words), set lazily.
    zero_off: Option<Off>,
    /// Four consecutive frame cells holding the standard BLAKE3 IV, emitted
    /// lazily at the first dominating default-IV compression in this
    /// control-flow scope.
    blake3_iv: Option<Off>,
}

struct FnLower<'a> {
    scope: Scope,
    next: Off,
    n_args: u32,
    /// Source-level return shapes for this function. Their physical cell widths
    /// determine the reserved return area immediately after the arguments.
    return_shapes: Vec<ReturnShape>,
    is_main: bool,
    code: Vec<LInstr>,
    one_off: Option<Off>,
    /// Declared size of each `HeapBuf`, keyed by its pointer cell. Shifted
    /// aliases resolve to the same base cell through their gaddr, so a
    /// compile-time index checks against the ORIGINAL buffer's bound.
    heap_sizes: HashMap<Off, u128>,
    /// While inlining an `@inline` call ([`Self::try_inline`]), the destination
    /// cells its tail `return` binds into instead of emitting a return jump.
    /// `None` outside an inlined body.
    inline_ret: Option<Vec<Off>>,
    /// Set by an inlined tail `return`, one [`RetBind`] per returned value,
    /// telling the caller's `let`/tuple how to bind each (alias a `StackBuf` run
    /// or a folded g-address, or take the scalar dst cell). `None` outside an
    /// inlined return.
    inline_stack_ret: Option<Vec<RetBind>>,
    /// Deferred stack-cell copies/zeros ([`Alias`]), forwarded at use.
    alias: HashMap<Off, Alias>,
    /// Where the fill blocks begin in `code`, once emitted.
    filler_start: Option<usize>,
    /// Hints queued to attach to the next emitted instruction.
    pending: Vec<Hint>,
    /// Active `@inline` expansion stack. Nested inline helpers are allowed,
    /// but direct or indirect recursion would otherwise recurse forever in
    /// the compiler.
    inline_calls: Vec<String>,
    /// Set by [`lower_func`] just before lowering a statement that sits in tail
    /// position; consumed by the next [`Self::stmt`] call, so nested lowering
    /// never inherits it.
    tail_call: bool,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
    /// Name of the function being lowered. Only used to attribute a lowered
    /// `for` loop to its source site under `DBG_LOOPS` (the profile prints bare
    /// `__loopN` names, which are otherwise opaque).
    fn_name: String,
    /// The program's function definitions by name, for `Const`-parameter
    /// specialization at call sites ([`Self::specialize`]).
    defs: &'a HashMap<String, Func>,
    /// Top-level constant arrays, resolved at compile time: `NAME[i]` yields the
    /// element (a field value or an index), `len(NAME)` its length.
    const_arrays: &'a HashMap<String, Vec<F64>>,
}

impl FnLower<'_> {
    fn fresh(&mut self) -> Off {
        let o = self.next;
        self.next += 1;
        o
    }

    fn emit(&mut self, op: LOp) {
        let hints = std::mem::take(&mut self.pending);
        self.code.push(LInstr { op, hints });
    }

    /// Bind `name` to `b`, dropping whatever the other three maps held for it:
    /// they are consulted independently, so a stale binding of another kind
    /// would shadow this one. `consts` is deliberately NOT touched, since a
    /// name can keep its compile-time index role across such a rebind; callers
    /// that must drop it do so themselves.
    fn rebind(&mut self, name: &str, b: Binding) {
        self.scope.vars.remove(name);
        self.scope.stacks.remove(name);
        self.scope.gaddrs.remove(name);
        self.scope.fconsts.remove(name);
        match b {
            Binding::Scalar(o) => {
                self.scope.vars.insert(name.to_string(), o);
            }
            Binding::Stack(base, size) => {
                self.scope.stacks.insert(name.to_string(), (base, size));
            }
            Binding::Gaddr(ga) => {
                self.scope.gaddrs.insert(name.to_string(), ga);
            }
            Binding::FConst(c) => {
                self.scope.fconsts.insert(name.to_string(), c);
            }
        }
    }

    /// Bind each of `names` to the join cell holding its value, after a `match`
    /// dispatch: whichever arm ran wrote them, so they are plain scalars now.
    fn bind_join(&mut self, names: &[String], cells: &[Off]) {
        for (name, &cell) in names.iter().zip(cells) {
            self.scope.consts.remove(name);
            self.rebind(name, Binding::Scalar(cell));
        }
    }

    /// A frame cell holding `1` (always-taken `JUMP` condition), set lazily once.
    fn one(&mut self) -> Off {
        if let Some(o) = self.one_off {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set {
            o,
            k: KVal::Const(F64::ONE),
        });
        self.one_off = Some(o);
        o
    }

    /// A frame cell holding the constant `v`, SET lazily once per distinct
    /// constant and shared by every read of it in scope (`1` shares
    /// [`Self::one`]'s cell; `main` alone had ~57k duplicated constant `SET`s
    /// before pooling). Branch-local like the other lazy cells: a cache entry
    /// made inside an `if`/`match` arm reverts at the join.
    fn const_cell(&mut self, v: F64) -> Off {
        if v == F64::ONE {
            return self.one();
        }
        let key = v.0;
        if let Some(&o) = self.scope.const_cells.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set { o, k: KVal::Const(v) });
        self.scope.const_cells.insert(key, o);
        o
    }

    /// Three consecutive cells holding one compile-time extension constant.
    /// Extension instructions address a run by its base, so scalar constant
    /// pooling is insufficient when the three independently pooled cells are
    /// not adjacent.
    fn ext_const_run(&mut self, values: [F64; 3]) -> Off {
        let key = [values[0].0, values[1].0, values[2].0];
        if let Some(&o) = self.scope.ext_const_runs.get(&key) {
            return o;
        }
        let o = self.alloc_stack(3);
        for (k, value) in values.into_iter().enumerate() {
            self.emit(LOp::Set {
                o: o + k as u32,
                k: KVal::Const(value),
            });
        }
        self.scope.ext_const_runs.insert(key, o);
        o
    }

    /// Two consecutive cells holding a compile-time BLAKE3 chunk.
    fn chunk_const_run(&mut self, values: [F64; 2]) -> Off {
        let key = [values[0].0, values[1].0];
        if let Some(&o) = self.scope.chunk_const_runs.get(&key) {
            return o;
        }
        let o = self.alloc_stack(2);
        for (k, value) in values.into_iter().enumerate() {
            self.emit(LOp::Set {
                o: o + k as u32,
                k: KVal::Const(value),
            });
        }
        self.scope.chunk_const_runs.insert(key, o);
        o
    }

    /// Four consecutive words holding the standard BLAKE3 IV.
    fn default_blake3_cv(&mut self) -> Off {
        if let Some(o) = self.scope.blake3_iv {
            return o;
        }
        let o = self.alloc_stack(4);
        for (k, value) in lean_vm::blake3_flock::IV.into_iter().enumerate() {
            self.emit(LOp::Set {
                o: o + k as u32,
                k: KVal::Const(value),
            });
            self.scope.const_cells.insert(value.0, o + k as u32);
        }
        self.scope.blake3_iv = Some(o);
        o
    }

    /// A frame cell holding `0`, set lazily once: the source for forwarded zero
    /// words (a `BLAKE3` padding half).
    fn zero(&mut self) -> Off {
        if let Some(o) = self.scope.zero_off {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set {
            o,
            k: KVal::Const(F64::ZERO),
        });
        self.scope.zero_off = Some(o);
        o
    }

    /// A stack store `sa[k] = val` whose value is a plain copy or a zero, which we
    /// defer as an [`Alias`] (forwarded at use) instead of emitting.
    fn copy_alias(&self, val: &Expr) -> Option<Alias> {
        match val {
            // A live var / stack cell aliases to that cell directly (no new
            // material); anything else that is a compile-time constant defers
            // to the pooled const cell.
            Expr::Var(v) if self.scope.vars.contains_key(v) => self.scope.vars.get(v).map(|&c| Alias::Cell(c)),
            // A scalar assignment is also allowed to retain the value as the
            // symbolic address `cell·g^0`. That representation is still the
            // exact same cell, so it can be forwarded just like an ordinary
            // scalar variable. This matters for the first round of a hash chain:
            // its input has not yet been rebound to a digest cell.
            Expr::Var(v) => match self.scope.gaddrs.get(v) {
                Some(GAddr {
                    base: Some(cell),
                    exp: 0,
                }) => Some(Alias::Cell(*cell)),
                _ => self.try_field_const(val).map(Alias::Const),
            },
            Expr::Index(arr, idx) if self.stack_of(arr).is_some() => {
                let (base, _) = self.stack_of(arr)?;
                Some(Alias::Cell(base + self.try_const_index(idx)?))
            }
            _ => self.try_field_const(val).map(Alias::Const),
        }
    }

    /// Terminate `main`: jump to the halt sentinel `g^{B-1}` with `fp = g^0`.
    /// The cell holding `1` doubles as the (nonzero) jump condition and the new
    /// frame pointer `g^0`; the dest cell holds `g^{B-1}` (doc §sec:e2e, final state).
    fn halt(&mut self) {
        let one = self.one();
        let dest = self.fresh();
        self.emit(LOp::Set {
            o: dest,
            k: KVal::EndSentinel,
        });
        self.emit(LOp::Jump {
            oc: one,
            od: dest,
            of: one,
        });
    }

    /// Emit the fill blocks: per table and per size in `lean_vm::cpu::filler::SIZES`,
    /// that many dummy instructions of the table's opcode, then a `JUMP` back to the
    /// block's own first instruction, in the same frame.
    ///
    /// So a block is a cycle, and nothing jumps into one. They sit past `main`'s halt,
    /// unreachable from any program code, and the interpreter enters them itself once the
    /// program has stopped: the state tuples a traversal pushes are the ones it pulls, so
    /// the cycle balances on its own for any number of traversals, whatever else the run
    /// did (`lean_vm::cpu::filler`).
    ///
    /// The closing jump is always taken, its destination being a g-power and so nonzero,
    /// and it reads that destination and its frame from cells the interpreter writes. A
    /// traversal therefore costs the block's rows plus that one jump, and nothing else:
    /// nothing here counts, tests, or allocates.
    ///
    /// A dummy uses one scratch cell as each of its operands, so the value it writes
    /// there is the value already there, which write-once memory permits however many
    /// traversals run: a block costs one cell for its dummies whatever its size. CSE
    /// leaves the copies alone (a cell written more than once is not a candidate) and
    /// there is no dead-code pass.
    fn lower_filler_blocks(&mut self) -> Vec<Block> {
        use lean_vm::cpu::filler::{SIZES, frame as fr};

        // A block runs in a frame the interpreter carves out, so the cells it reads are at
        // fixed offsets in *that* frame rather than allocated from this function's
        // counter, and nothing here touches `main`'s frame at all.
        self.filler_start = Some(self.code.len());
        let mut blocks = Vec::new();
        for (table, op) in crate::filler::TABLES {
            for size in SIZES {
                blocks.push(Block {
                    pc: self.code.len() as u32,
                    size: size as u32,
                    table,
                });
                for _ in 0..size {
                    self.emit(match op {
                        FillerOp::Xor => LOp::Xor {
                            a: fr::SCRATCH,
                            b: fr::SCRATCH,
                            c: fr::SCRATCH,
                        },
                        FillerOp::Mul => LOp::Mul {
                            a: fr::SCRATCH,
                            b: fr::SCRATCH,
                            c: fr::SCRATCH,
                        },
                        FillerOp::Set => LOp::Set {
                            o: fr::SCRATCH,
                            k: KVal::Const(F64::ZERO),
                        },
                        FillerOp::AddExt => LOp::AddExt {
                            a: fr::SCRATCH,
                            b: fr::SCRATCH,
                            c: fr::SCRATCH,
                        },
                        FillerOp::MulExt => LOp::MulExt {
                            a: fr::SCRATCH,
                            b: fr::SCRATCH,
                            c: fr::SCRATCH,
                        },
                        FillerOp::DerefExt => LOp::DerefExt {
                            alpha: fr::PTR,
                            beta: 0,
                            gamma: fr::SCRATCH,
                        },
                        FillerOp::Deref => LOp::Deref {
                            alpha: fr::PTR,
                            beta: 0,
                            gamma: fr::SCRATCH,
                            mode: DerefMode::Cell,
                        },
                        // Its condition is a cell nothing ever writes, so it reads as
                        // zero: the dummy is not taken and falls through to the next
                        // instruction of the block instead of closing the cycle early.
                        FillerOp::Jump => LOp::Jump {
                            oc: fr::ZERO,
                            od: fr::ZERO,
                            of: fr::ZERO,
                        },
                        FillerOp::Blake3 => LOp::Blake3 {
                            ins: [fr::MSG, fr::MSG + 2, fr::MSG + 4, fr::MSG + 6],
                            cv: fr::SCRATCH,
                            out: fr::DIGEST,
                            metadata: [F64::ZERO; 2],
                        },
                    });
                }
                // Back to the top, closing the cycle. For the `JUMP` table this is one
                // more row of its own, which is why the solver decomposes that table over
                // `size + 1`.
                self.emit(LOp::Jump {
                    oc: fr::DEST,
                    od: fr::DEST,
                    of: fr::NEXT_FP,
                });
            }
        }
        blocks
    }

    /// `dst = src` (no MOV: multiply by `1`).
    fn copy(&mut self, src: Off, dst: Off) {
        let one = self.one();
        self.emit(LOp::Mul { a: src, b: one, c: dst });
    }

    /// A frame cell holding this function's own `fp` (the g-power element),
    /// materialized lazily once: a taken `JUMP` reloads the frame pointer
    /// from a cell, so local (`if`/`else`) jumps must name it. The ISA has no
    /// fp-read, so bounce it through a fresh 1-cell heap buffer: a
    /// `DEREF`-fp writes it there, a `DEREF`-cell copies it back (2 cycles,
    /// once per function that branches). In `main`, `fp = g^0 = 1`, which is
    /// the [`Self::one`] cell.
    fn self_fp(&mut self) -> Off {
        if self.is_main {
            return self.one();
        }
        if let Some(o) = self.scope.self_fp_off {
            return o;
        }
        let q = self.fresh();
        self.pending.push(Hint::AllocBuffer { ptr: q, size: 1 });
        self.emit(LOp::Deref {
            alpha: q,
            beta: 0,
            gamma: 0,
            mode: DerefMode::Fp,
        }); // m[q] := fp
        let o = self.fresh();
        self.emit(LOp::Deref {
            alpha: q,
            beta: 0,
            gamma: o,
            mode: DerefMode::Cell,
        }); // m[fp·g^o] := m[q]
        self.scope.self_fp_off = Some(o);
        o
    }

    /// Backpatch a [`KVal::Local`] `SET` (emitted with a placeholder) to name
    /// the instruction at index `target` of this function's code.
    fn patch_local(&mut self, set_idx: usize, target: usize) {
        match &mut self.code[set_idx].op {
            LOp::Set { k: KVal::Local(t), .. } => *t = target as u32,
            other => unreachable!("patch_local on {other:?}"),
        }
    }

    /// Run `f` with branch-local scope: bindings AND the lazily cached cells
    /// (`one`, `self_fp`, range-check bounds, default BLAKE3 IV) revert
    /// afterwards, since a cell whose `SET` sits inside a conditionally-executed
    /// region must not be trusted outside it.
    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        let branch_start = self.next;
        let saved_aliases = self.alias.clone();
        let saved = self.scope.clone();
        f(self);
        // A deferred store into a buffer declared outside the branch must be
        // materialized on that path before the branch-local aliases are dropped.
        let branch_outputs: Vec<Off> = self
            .alias
            .iter()
            .filter_map(|(&dst, alias)| (dst < branch_start && saved_aliases.get(&dst) != Some(alias)).then_some(dst))
            .collect();
        for dst in branch_outputs {
            let src = self.word_src(dst);
            self.alias.remove(&dst);
            self.copy(src, dst);
        }
        // A hint pending at the end of a branch (e.g. a trailing
        // `hint_witness`) must not attach to whatever instruction follows the
        // join, which would fire it unconditionally. Absorb it with a no-op.
        if !self.pending.is_empty() {
            let o = self.fresh();
            self.emit(LOp::Set {
                o,
                k: KVal::Const(F64::ZERO),
            });
        }
        self.scope = saved;
        self.alias = saved_aliases;
    }

    /// Lower a branch body with branch-local scope ([`Self::scoped`]).
    fn branch(&mut self, body: &[Stmt]) {
        self.scoped(|s| {
            for st in body {
                s.stmt(st);
            }
        });
    }

    /// `match log(x)`: two jumps through a trampoline table (doc §ISA
    /// programming / Match statements). leanVM's switch jumps to the affine
    /// `pc = a + b·x`; in the exponent the dispatch is multiplicative:
    /// `d = g^T · x²` lands on slot `j` of the table at bytecode base `T`,
    /// which is `n` consecutive two-instruction slots, slot `j` being `SET c =
    /// g^{block_j}; JUMP c`. The case blocks sit anywhere, unaligned; only
    /// the fixed-size slots are consecutive. The slots are two instructions
    /// rather than one because a `JUMP` reads its target from a *cell*: a
    /// one-instruction slot would need its cell pre-`SET`, i.e. `n` `SET`s
    /// executed before every dispatch. Folding the `SET` into the slot puts
    /// it on the taken path only, and the doubled slot stride is absorbed as
    /// `x²` (one extra `MUL`). Cost ≈ 7 cycles, independent of `n`.
    ///
    /// Soundness: nothing here bounds `x`, so a scrutinee outside `[0, n)`
    /// dispatches to an arbitrary pc, so hinted values must be range-checked
    /// first (as in leanVM).
    fn lower_match(&mut self, x: &Expr, cases: &[Vec<Stmt>]) {
        let xo = self.expr(x);
        self.lower_match_dispatch(xo, cases.len(), |s, j| s.branch(&cases[j]));
    }

    /// `names = match_range(log(x), …)`: the same dispatch as
    /// [`Self::lower_match`], with generated arms: arm `j` evaluates its
    /// expression (the lambda body at `i = j`) and copies the results into
    /// cells shared by every arm (write-once: exactly one arm executes);
    /// `names` bind to those cells at the join.
    fn lower_match_range(&mut self, names: &[String], x: &Expr, arms: &[Expr]) {
        for arm in arms {
            if let Expr::Call(f, _) = arm
                && self
                    .defs
                    .get(f)
                    .is_some_and(|d| !d.inline && d.return_shapes.iter().any(|s| matches!(s, ReturnShape::StackBuf(_))))
            {
                panic!("a normal function's StackBuf return cannot cross a match_range join; bind it with `let`");
            }
        }
        // Fusion: when every arm is a direct call to the same function with
        // identical runtime args (differing only in `Const` args, the usual
        // `lambda k: f(a, b, k)`), set up one shared callee frame and dispatch
        // straight to the specialization's entry, which returns to the join.
        // Collapses each arm from a full call to a two-instruction trampoline
        // slot; see [`Self::lower_dispatched_call`].
        if arms.iter().all(|a| matches!(a, Expr::Call(..))) {
            let specialized: Vec<(String, Vec<Expr>, Vec<bool>)> = arms
                .iter()
                .map(|a| {
                    let Expr::Call(f, cargs) = a else { unreachable!() };
                    self.specialize(f, cargs)
                })
                .collect();
            let rt0 = &specialized[0].1;
            if specialized[0].2.iter().all(|x| !x)
                && specialized
                    .iter()
                    .all(|(_, rt, ext)| ext.iter().all(|x| !x) && rt == rt0)
            {
                let callees: Vec<String> = specialized.iter().map(|(c, _, _)| c.clone()).collect();
                let rt_args = rt0.clone();
                self.lower_dispatched_call(names, x, &callees, &rt_args);
                return;
            }
            // Not uniform: fall through (the specializations queued above are
            // re-requested idempotently by `call_into`).
        }
        let xo = self.expr(x);
        let rcells: Vec<Off> = names.iter().map(|_| self.fresh()).collect();
        self.lower_match_dispatch(xo, arms.len(), |s, j| {
            s.scoped(|s| {
                if let [rcell] = rcells.as_slice() {
                    s.expr_into(&arms[j], *rcell);
                } else {
                    let Expr::Call(f, cargs) = &arms[j] else {
                        panic!(
                            "a multi-target match_range arm must be a function call, got `{:?}`",
                            arms[j]
                        );
                    };
                    s.inline_stack_ret = None;
                    s.call_into(f, cargs, &rcells);
                    // An @inline arm's aliased returns materialize into the
                    // shared join cells (a real call wrote them directly).
                    if let Some(binds) = s.inline_stack_ret.take() {
                        for (b, &rc) in binds.iter().zip(&rcells) {
                            match *b {
                                RetBind::Gaddr(ga) => {
                                    let c = s.materialize(ga);
                                    s.copy(c, rc);
                                }
                                RetBind::Stack(base, size) => {
                                    assert_eq!(size, 1, "a multi-cell StackBuf return cannot cross a match_range join");
                                    s.copy(base, rc);
                                }
                                RetBind::Scalar => {}
                            }
                        }
                    }
                }
            });
        });
        self.bind_join(names, &rcells);
    }

    /// `names = match_range(log(x), …, lambda k: f(args, k))` fused: the arms all
    /// call one of `callees` (specializations sharing the arg/return layout) with
    /// the same runtime `args`, so build the callee frame **once** and let the
    /// dispatch jump straight into the selected entry, which returns to the join.
    /// Each taken arm is then just the trampoline's `SET entry; JUMP`: no
    /// per-arm frame setup, call, or return jump.
    fn lower_dispatched_call(&mut self, names: &[String], x: &Expr, callees: &[String], rt_args: &[Expr]) {
        let n_args = rt_args.len() as u32;
        let rcells: Vec<Off> = names.iter().map(|_| self.fresh()).collect();

        // Shared callee frame: args, retfp, and retpc = the join (so the callee
        // returns straight past the dispatch). Evaluated once.
        let arg_offs: Vec<Off> = rt_args.iter().map(|a| self.expr(a)).collect();
        let xo = self.expr(x);
        let one = self.one();
        let sfp = self.self_fp();

        let nfp = self.fresh();
        self.pending.push(Hint::AllocFrameMax {
            ptr: nfp,
            callees: callees.to_vec(),
        });
        let mut i = 0;
        while i < arg_offs.len() {
            if i + 2 < arg_offs.len() && arg_offs[i + 1] == arg_offs[i] + 1 && arg_offs[i + 2] == arg_offs[i] + 2 {
                self.emit(LOp::DerefExt {
                    alpha: nfp,
                    beta: 2 + i as u32,
                    gamma: arg_offs[i],
                });
                i += 3;
            } else if i + 1 < arg_offs.len() && arg_offs[i + 1] == arg_offs[i] + 1 {
                self.emit(LOp::Deref128 {
                    alpha: nfp,
                    beta: 2 + i as u32,
                    gamma: arg_offs[i],
                });
                i += 2;
            } else {
                self.emit(LOp::Deref {
                    alpha: nfp,
                    beta: 2 + i as u32,
                    gamma: arg_offs[i],
                    mode: DerefMode::Cell,
                });
                i += 1;
            }
        }
        self.emit(LOp::Deref {
            alpha: nfp,
            beta: 1,
            gamma: 0,
            mode: DerefMode::Fp,
        }); // retfp
        let join_cell = self.fresh();
        let join_set = self.code.len();
        self.emit(LOp::Set {
            o: join_cell,
            k: KVal::Local(0),
        }); // patched: the join pc
        self.emit(LOp::Deref {
            alpha: nfp,
            beta: 0,
            gamma: join_cell,
            mode: DerefMode::Cell,
        }); // retpc = join

        let kset = self.emit_dispatch(xo, one, sfp);

        // Trampoline: slot j enters `callees[j]` with fp = nfp; the callee's own
        // `return` jumps to retpc (the join) in the caller frame.
        self.patch_local(kset, self.code.len());
        self.emit_slots(callees.len(), one, nfp, |j| KVal::Entry(callees[j].clone()));

        // Join: read the return values (written by whichever callee ran).
        self.patch_local(join_set, self.code.len());
        let mut i = 0;
        while i < rcells.len() {
            if i + 2 < rcells.len() && rcells[i + 1] == rcells[i] + 1 && rcells[i + 2] == rcells[i] + 2 {
                self.emit(LOp::DerefExt {
                    alpha: nfp,
                    beta: 2 + n_args + i as u32,
                    gamma: rcells[i],
                });
                i += 3;
            } else if i + 1 < rcells.len() && rcells[i + 1] == rcells[i] + 1 {
                self.emit(LOp::Deref128 {
                    alpha: nfp,
                    beta: 2 + n_args + i as u32,
                    gamma: rcells[i],
                });
                i += 2;
            } else {
                self.emit(LOp::Deref {
                    alpha: nfp,
                    beta: 2 + n_args + i as u32,
                    gamma: rcells[i],
                    mode: DerefMode::Cell,
                });
                i += 1;
            }
        }

        self.bind_join(names, &rcells);
    }

    /// The two-jump dispatch itself: `d = g^T · x²` names slot `x` of the
    /// two-instruction trampoline table at bytecode base `T`. Returns the index
    /// of the `SET` holding `T`, for the caller to patch once the table's
    /// position is known.
    fn emit_dispatch(&mut self, xo: Off, one: Off, of: Off) -> usize {
        let kcell = self.fresh();
        let kset = self.code.len();
        self.emit(LOp::Set {
            o: kcell,
            k: KVal::Local(0),
        }); // patched: table base T
        let x2 = self.fresh();
        self.emit(LOp::Mul { a: xo, b: xo, c: x2 });
        let d = self.fresh();
        self.emit(LOp::Mul { a: kcell, b: x2, c: d });
        self.emit(LOp::Jump { oc: one, od: d, of });
        kset
    }

    /// The `n` trampoline slots themselves, each `SET c = k(j); JUMP c`.
    /// Returns each slot's `SET` index (a [`KVal::Local`] target still needs
    /// patching to the block it selects).
    fn emit_slots(&mut self, n: usize, one: Off, of: Off, k: impl Fn(usize) -> KVal) -> Vec<usize> {
        let mut slots = Vec::new();
        for j in 0..n {
            let c = self.fresh();
            slots.push(self.code.len());
            self.emit(LOp::Set { o: c, k: k(j) });
            self.emit(LOp::Jump { oc: one, od: c, of });
        }
        slots
    }

    /// The trampoline dispatch shared by `match` and `match_range`: jump to
    /// `d = g^T · x²` (slot `j` of the two-instruction table at bytecode base
    /// `T`), then to `body(j)`'s code; every non-final body exits to the
    /// join. `body` lowers arm `j`, with its own branch-local scope.
    fn lower_match_dispatch(&mut self, xo: Off, n: usize, mut body: impl FnMut(&mut Self, usize)) {
        // Hoisted on purpose: these SETs must dominate the join.
        let sfp = self.self_fp();
        let one = self.one();
        let join = self.fresh();
        let jset = self.code.len();
        self.emit(LOp::Set {
            o: join,
            k: KVal::Local(0),
        }); // patched: the join
        // Slot j (two instructions) sits at T + 2j.
        let kset = self.emit_dispatch(xo, one, sfp);
        // The trampoline table.
        self.patch_local(kset, self.code.len());
        let slots = self.emit_slots(n, one, sfp, |_| KVal::Local(0)); // patched: its block
        // The arm blocks, each exiting to the join (the last falls through).
        for (j, &slot) in slots.iter().enumerate() {
            self.patch_local(slot, self.code.len());
            body(self, j);
            if j + 1 != n {
                self.emit(LOp::Jump {
                    oc: one,
                    od: join,
                    of: sfp,
                });
            }
        }
        self.patch_local(jset, self.code.len());
    }

    /// `if` / `else`: one `XOR` and one conditional `JUMP` (taken ⇔ the
    /// sides differ). The taken jump goes to whichever block the test
    /// *doesn't* fall into, so no negation gadget is needed: for `==` the
    /// fall-through is `then`, for `!=` it is `else`. Local jumps keep the
    /// frame via [`Self::self_fp`]; targets are backpatched
    /// [`KVal::Local`]s. Costs 3 cycles, +2 (`SET` + `JUMP`) when a non-empty
    /// second block must be skipped over, + the amortized `one`/`self_fp`
    /// materialization.
    fn lower_if(&mut self, eq: bool, lhs: &Expr, rhs: &Expr, then: &[Stmt], els: &[Stmt]) {
        // Compile-time condition (both sides compile-time integers, e.g. after
        // `Const`-argument substitution): fold to the taken branch, emitting no
        // test or jump. Lets `@inline` arms bake per-case control flow. The
        // taken branch is straight-line code (like an unroll iteration), so its
        // bindings persist, unlike a runtime branch, whose bindings are
        // branch-local (a runtime branch may not execute).
        if let (Some(a), Some(b)) = (self.try_const_index(lhs), self.try_const_index(rhs)) {
            for st in if (a == b) == eq { then } else { els } {
                self.stmt(st);
            }
            return;
        }
        // `x != 0` needs no XOR: the cell itself is the JUMP's nonzero test.
        let x = if self.try_lit(rhs) == Some(0) {
            self.expr(lhs)
        } else if self.try_lit(lhs) == Some(0) {
            self.expr(rhs)
        } else {
            let (la, lb) = (self.expr(lhs), self.expr(rhs));
            let x = self.fresh();
            self.emit(LOp::Xor { a: la, b: lb, c: x }); // x = lhs + rhs: nonzero ⇔ !=
            x
        };
        // Hoisted on purpose: these SETs must dominate the join.
        let sfp = self.self_fp();
        let one = self.one();
        let (a_block, b_block) = if eq { (then, els) } else { (els, then) };
        let bdest = self.fresh();
        let bset = self.code.len();
        self.emit(LOp::Set {
            o: bdest,
            k: KVal::Local(0),
        }); // patched: start of B
        self.emit(LOp::Jump {
            oc: x,
            od: bdest,
            of: sfp,
        });
        self.branch(a_block);
        if b_block.is_empty() {
            self.patch_local(bset, self.code.len());
        } else {
            let edest = self.fresh();
            let eset = self.code.len();
            self.emit(LOp::Set {
                o: edest,
                k: KVal::Local(0),
            }); // patched: the join
            self.emit(LOp::Jump {
                oc: one,
                od: edest,
                of: sfp,
            });
            self.patch_local(bset, self.code.len());
            self.branch(b_block);
            self.patch_local(eset, self.code.len());
        }
    }

    /// `assert a != b`: one `XOR` and one conditional `JUMP` on `a + b`. When
    /// the sides differ (`a + b ≠ 0`) the jump is taken to the continuation, so
    /// execution proceeds; when they are equal it falls through to a `SET` +
    /// unconditional `JUMP` to the poison pc `g^-1` ([`KVal::Poison`]), which
    /// lies outside the committed bytecode cube, so the bytecode bus cannot
    /// balance a read there, so no valid proof continues. Same `JUMP`-nonzero
    /// primitive as [`Self::lower_if`], no prover hint (unlike `(a-b)·inv == 1`).
    /// A compile-time-equal pair is a hard compile error.
    fn lower_assert_ne(&mut self, a: &Expr, b: &Expr) {
        // Compile-time literals (e.g. after `Const`-arg substitution): a
        // trivially-true pair emits nothing, an equal pair is a hard error.
        // Restricted to plain literals so a field value is never confused with a
        // g-power index (unlike stack-index folding).
        if let (Expr::Lit(x), Expr::Lit(y)) = (a, b) {
            assert!(x != y, "assert a != b: sides are the compile-time-equal literal {x}");
            return;
        }
        let (la, lb) = (self.expr(a), self.expr(b));
        let x = self.fresh();
        self.emit(LOp::Xor { a: la, b: lb, c: x }); // x = a + b: nonzero ⇔ a != b
        let sfp = self.self_fp();
        let one = self.one();
        // a != b: skip the poison and continue at the join (patched below).
        let cont = self.fresh();
        let cset = self.code.len();
        self.emit(LOp::Set {
            o: cont,
            k: KVal::Local(0),
        });
        self.emit(LOp::Jump {
            oc: x,
            od: cont,
            of: sfp,
        });
        // a == b: fall through to the poison jump (g^-1, an unreachable pc).
        let pd = self.fresh();
        self.emit(LOp::Set { o: pd, k: KVal::Poison });
        self.emit(LOp::Jump {
            oc: one,
            od: pd,
            of: sfp,
        });
        self.patch_local(cset, self.code.len());
    }

    /// The frame cell holding `g^{k-1}`, the range-check product target, set
    /// lazily once per distinct bound `k` and shared by that bound's checks.
    fn bound_cell(&mut self, k: u64) -> Off {
        if let Some(&o) = self.scope.bounds.get(&k) {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set {
            o,
            k: KVal::Const(g_pow_u128((k - 1) as u128)),
        });
        self.scope.bounds.insert(k, o);
        o
    }

    /// `hint_witness(dest, "name")`: resolve `dest` to a run of cells and
    /// queue the witness-fill hint (no instructions: the values are written
    /// by the runner before the next instruction executes, unconstrained).
    /// `dest`: a whole `StackBuf`, a `StackBuf` slice, a `HeapBuf` slice with
    /// compile-time bounds, or a runtime-start heap slice `buf[i:i + k]`.
    fn lower_hint_witness(&mut self, dest: &Expr, name: &str) {
        let name = name.to_string();
        let hint = match dest {
            Expr::Var(_) => {
                let (base, len) = self
                    .stack_of(dest)
                    .expect("hint_witness dest must be a StackBuf or a StackBuf/HeapBuf slice");
                RHint::WitnessStack { name, base, len }
            }
            Expr::Slice(arr, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                (Some(lo), Some(hi)) => {
                    assert!(lo < hi, "empty hint_witness slice {lo}:{hi}");
                    if let Some((base, size)) = self.stack_of(arr) {
                        assert!(hi <= size, "slice {lo}:{hi} out of bounds (StackBuf size {size})");
                        RHint::WitnessStack {
                            name,
                            base: base + lo,
                            len: hi - lo,
                        }
                    } else {
                        let len = hi - lo;
                        self.check_heap_bound(arr, lo as u128, len as u128);
                        let (ptr, lo) = self.heap_base(arr, lo as u128);
                        RHint::WitnessHeap { name, ptr, lo, len }
                    }
                }
                _ => {
                    assert!(
                        self.stack_of(arr).is_none(),
                        "a StackBuf slice needs compile-time bounds (frame offsets are baked into the bytecode)"
                    );
                    let k = plus_k(lo, hi).unwrap_or_else(|| {
                        panic!("a runtime hint_witness slice must be `buf[i:i + k]`, got `{lo:?}:{hi:?}`")
                    });
                    let len = u32::try_from(k).expect("hint_witness slice length overflows u32");
                    assert!(len > 0, "empty hint_witness slice");
                    let (ptr, lo) = self.heap_addr(arr, lo);
                    RHint::WitnessHeap { name, ptr, lo, len }
                }
            },
            other => panic!("hint_witness dest must be a StackBuf or a slice, got `{other:?}`"),
        };
        self.pending.push(Hint::Resolved(hint));
    }

    /// `assert log x < log GEN ** k`: the 3-cycle range check *in the
    /// exponent* (leanVM's DEREF trick, see
    /// `doc/body/10-isa-programming.tex` §sec:prog-range-checks, transported to g-powers). With `x = g^e`:
    ///
    /// 1. `DEREF` through `x`: the dereferenced address `x·g^0` must be one of
    ///    the memory's `2^h` addresses `{g^0, …, g^{2^h-1}}` (doc §Memory), so
    ///    the bus itself proves `x = g^e` with `e < 2^h`;
    /// 2. `MUL x·y` into the write-once cell holding `g^{k-1}`: asserts
    ///    `x·y = g^{k-1}`. The complement `y = g^{k-1-e}` needs no hint: the
    ///    result cell is already written, so the runner back-solves the one
    ///    unknown operand (leanVM's ADD deduction, multiplicatively);
    /// 3. `DEREF` through `y`: proves `y = g^f` with `f < 2^h`.
    ///
    /// Then `e + f ≡ k-1 (mod 2^64-1)` with `e, f < 2^h`, and since a negative
    /// `k-1-e` wraps to `≈ 2^64 ≫ 2^h`, this forces `e ≤ k-1`, for ANY memory
    /// size the prover announces, provided `k ≤ 2^MIN_LOG_MEM`. The two `DEREF`
    /// target cells are unconstrained touches (only the address matters),
    /// back-filled at the end of execution; the constant cell is one amortized
    /// `SET` per distinct bound.
    fn lower_assert_lt(&mut self, e: &Expr, k: u64) {
        assert!(k >= 1, "range-check bound GEN ** 0 names the empty set");
        assert!(
            k <= 1 << lean_vm::cpu::MIN_LOG_MEM,
            "range-check bound GEN ** {k} exceeds 2^{} (the minimum memory size)",
            lean_vm::cpu::MIN_LOG_MEM,
        );
        let x = self.expr(e);
        let kcell = self.bound_cell(k);
        let y = self.fresh(); // the complement g^{k-1-e}, back-solved by the MUL
        let t1 = self.fresh(); // DEREF targets: unconstrained touch cells
        let t2 = self.fresh();
        self.emit(LOp::Deref {
            alpha: x,
            beta: 0,
            gamma: t1,
            mode: DerefMode::Cell,
        });
        self.emit(LOp::Mul { a: x, b: y, c: kcell });
        self.emit(LOp::Deref {
            alpha: y,
            beta: 0,
            gamma: t2,
            mode: DerefMode::Cell,
        });
    }

    fn expr(&mut self, e: &Expr) -> Off {
        match e {
            Expr::Lit(n) => self.const_cell(lit_field(*n)),
            Expr::Gen => self.const_cell(g_pow(1)),
            Expr::GPow(k) => self.const_cell(g_pow_u128(*k)),
            Expr::GenPow(e) => {
                let k = self.gpow_exp(e);
                self.const_cell(g_pow_u128(k))
            }
            Expr::Pow(b, e) => self.pow_expr(b, e),
            Expr::Var(v) => {
                if self.scope.stacks.contains_key(v) {
                    panic!("StackBuf `{v}` used as a scalar; index it (`{v}[k]`) or pass it to blake3");
                }
                if let Some(&ga) = self.scope.gaddrs.get(v) {
                    return self.materialize(ga);
                }
                if let Some(&c) = self.scope.fconsts.get(v) {
                    return self.const_cell(c);
                }
                *self
                    .scope
                    .vars
                    .get(v)
                    .unwrap_or_else(|| panic!("unbound variable `{v}`"))
            }
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    return self.expr(x);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                let o = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: o });
                o
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    return self.expr(x);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                let o = self.fresh();
                self.emit(LOp::Mul { a: la, b: lb, c: o });
                o
            }
            Expr::FieldDiv(a, b) => {
                // q = a / b via the MUL write-once back-solve: emit `a = q * b`
                // with the quotient `q` the unset operand. Witness-gen fills
                // q = a·b⁻¹, and the MUL constraint pins q·b == a (so b == 0 is
                // rejected unless a == 0). One MUL, no hint. The dividend cell
                // `a` must already be written, which `self.expr(a)` guarantees.
                let (la, lb) = (self.expr(a), self.expr(b));
                let q = self.fresh();
                self.emit(LOp::Mul { a: q, b: lb, c: la });
                q
            }
            Expr::Call(f, _) if f == "f192" => {
                self.const_cell(self.try_field_const(e).expect("f192 needs three literal u64 limbs"))
            }
            Expr::Call(f, args) if f == "hint_log2_ceil" => {
                // Computed advice: the prover fills g^log2_ceil (base-2 ceil-log) of the value in
                // `bits` (a `nbits`-bit buffer), floored at `floor`. Returned
                // UNCONSTRAINED, so the caller (log2_ceil) re-verifies it. Same
                // "prover computes, circuit checks" pattern as `/`.
                assert_eq!(args.len(), 3, "hint_log2_ceil(bits, nbits, floor)");
                let bits_ptr = self.expr(&args[0]);
                let nbits = self.const_index(&args[1]);
                let floor = self.const_index(&args[2]);
                let dst = self.fresh();
                self.pending.push(Hint::Resolved(RHint::Log2Ceil {
                    bits_ptr,
                    dst,
                    nbits,
                    floor,
                }));
                dst
            }
            Expr::Call(f, args) => {
                if let Some(n) = self.const_len(e) {
                    self.const_cell(F64(n as u64))
                } else {
                    let d = self.call(f, args, 1)[0];
                    self.take_inline_ret_cell(d)
                }
            }
            Expr::HeapBuf(n) => {
                let arr = self.fresh();
                self.heap_sizes.insert(arr, *n as u128);
                // Allocate before the next instruction reads the pointer.
                self.pending.push(Hint::AllocBuffer {
                    ptr: arr,
                    size: *n as u32,
                });
                arr
            }
            Expr::HeapBufDyn(e) => {
                // Evaluate the size first (its cell must be written when the
                // alloc hint fires), then allocate before the pointer is read.
                let size = self.expr(e);
                let arr = self.fresh();
                self.pending.push(Hint::AllocBufferDyn { ptr: arr, size });
                arr
            }
            Expr::StackBuf(_) => {
                panic!("StackBuf(n) must be bound to a name: `x = StackBuf(n)`")
            }
            Expr::Index(arr, idx) => {
                // Constant-array element `NAME[i]`: a compile-time field value.
                if let Some(elem) = self.const_array_elem(e) {
                    return self.const_cell(elem);
                }
                // Stack read `sa[k]`: the frame cell `base + k` directly (no deref),
                // forwarded through any deferred copy/zero alias.
                if let Some((base, size)) = self.stack_of(arr) {
                    let k = self.const_index(idx);
                    assert!(k < size, "stack index {k} out of bounds (size {size})");
                    return self.word_src(base + k);
                }
                // Heap read: bind dst := m[arr·idx] (the array cell, written earlier).
                let (base, beta) = self.heap_addr(arr, idx);
                let dst = self.fresh();
                self.emit(LOp::Deref {
                    alpha: base,
                    beta,
                    gamma: dst,
                    mode: DerefMode::Cell,
                });
                dst
            }
            Expr::Sub(..) | Expr::Div(..) | Expr::Mod(..) => {
                panic!(
                    "`-`, `//`, `%` are compile-time only (field subtraction is `+`); use them in an index, a bound, or a `Const` argument, got `{e:?}`"
                )
            }
            Expr::Slice(..) => panic!("a slice is not a scalar; it is only a blake3 operand"),
            Expr::ListLit(..) => panic!(
                "a list literal must be bound to a name: `x = [a, b]` (inlining {:?})",
                self.inline_calls
            ),
        }
    }

    /// Allocate `n` *consecutive* fresh frame cells (a stack run), returning the
    /// base. Nothing else may `fresh()` between them, so they stay adjacent.
    fn alloc_stack(&mut self, n: u32) -> Off {
        let base = self.next;
        self.next += n;
        base
    }

    /// Materialize an inline list literal as a consecutive stack run. This is
    /// the unnamed equivalent of `tmp = [a, b, ...]`, used for StackBuf
    /// arguments such as `mul_192(a, [1, 0, 0], out)`.
    fn materialize_list(&mut self, es: &[Expr]) -> (Off, u32) {
        let size = es.len() as u32;
        let base = self.alloc_stack(size);
        for (k, el) in es.iter().enumerate() {
            let dst = base + k as u32;
            if let Some(a) = self.copy_alias(el) {
                self.alias.insert(dst, a);
            } else {
                self.alias.remove(&dst);
                self.expr_into(el, dst);
            }
        }
        (base, size)
    }

    /// If `e` names a `StackBuf` variable, its `(base, size)`.
    fn stack_of(&self, e: &Expr) -> Option<(Off, u32)> {
        match e {
            Expr::Var(v) => self.scope.stacks.get(v).copied(),
            _ => None,
        }
    }

    /// A compile-time integer index: a literal, a name bound to a literal,
    /// or `+`/`*`/`//`/`%` of those (evaluated as *integer* arithmetic: this is
    /// index space, not the field). `None` when the expression is a runtime
    /// value (which a heap slice start may be; see [`Self::blake3_operand`]).
    fn try_const_index(&self, idx: &Expr) -> Option<u32> {
        match idx {
            // A literal that fits is an index; a ≥ 2^32 literal is a field value,
            // not an index (`None`, and callers that require an index error).
            Expr::Lit(k) => u32::try_from(*k).ok(),
            Expr::Var(v) => self.scope.consts.get(v).copied(),
            // Overflow (or a negative `-`) means the expression is not a valid
            // index, so decline (`None`) rather than panic: this evaluator also
            // probes `Let` bindings speculatively, where `A * B` may be a
            // perfectly fine *field* expression whose integer product overflows.
            Expr::Add(a, b) => self.try_const_index(a)?.checked_add(self.try_const_index(b)?),
            Expr::Sub(a, b) => self.try_const_index(a)?.checked_sub(self.try_const_index(b)?),
            Expr::Mul(a, b) => self.try_const_index(a)?.checked_mul(self.try_const_index(b)?),
            Expr::Div(a, b) => {
                let d = self.try_const_index(b)?;
                assert!(d != 0, "compile-time division by zero");
                Some(self.try_const_index(a)? / d)
            }
            Expr::Mod(a, b) => {
                let d = self.try_const_index(b)?;
                assert!(d != 0, "compile-time modulo by zero");
                Some(self.try_const_index(a)? % d)
            }
            // A constant-array element `NAME[i]` or `len(NAME)` used as an index /
            // bound / `unroll` count. An element too large for an index declines
            // (it is a field value; this evaluator also probes speculatively).
            Expr::Index(..) => self
                .const_array_elem(idx)
                .map(|e| e.0)
                .and_then(|e| u32::try_from(e).ok()),
            Expr::Call(..) => self.const_len(idx).map(|n| n as u32),
            // Integer power `b ** e` (both compile-time), e.g. `2 ** c` for a bit
            // test. Overflow declines (see the Add/Sub/Mul comment above).
            Expr::Pow(b, e) => self.try_const_index(b)?.checked_pow(self.try_const_index(e)?),
            _ => None,
        }
    }

    /// A stack index or compile-time slice bound: [`Self::try_const_index`],
    /// required to succeed.
    fn const_index(&self, idx: &Expr) -> u32 {
        self.try_const_index(idx).unwrap_or_else(|| {
            // An oversized literal is an index-shaped mistake, not a runtime
            // value, so diagnose it precisely (`sa[2^32]` must not wrap to `sa[0]`).
            if let Expr::Lit(k) = idx {
                panic!("stack index {k} does not fit in u32");
            }
            panic!("a StackBuf index must be a compile-time integer, got `{idx:?}`")
        })
    }

    /// The exponent of `GEN ** e`: a compile-time integer, required to succeed.
    fn gpow_exp(&self, e: &Expr) -> u128 {
        self.try_const_index(e)
            .unwrap_or_else(|| panic!("`GEN ** e` needs a compile-time integer exponent, got `{e:?}`")) as u128
    }

    /// `base ** e` (non-`GEN` base, compile-time exponent `e`): a fully-constant
    /// base folds to one `SET`; a runtime base is raised by square-and-multiply.
    fn pow_expr(&mut self, b: &Expr, e: &Expr) -> Off {
        let k = self
            .try_const_index(e)
            .unwrap_or_else(|| panic!("`**` exponent must be a compile-time integer, got `{e:?}`"));
        // Fully constant: evaluate in the field and emit a single `SET`.
        if let Some(bc) = self.try_field_const(b) {
            return self.const_cell(field_pow(bc, k));
        }
        if k == 0 {
            let o = self.fresh();
            self.emit(LOp::Set {
                o,
                k: KVal::Const(F64::ONE),
            });
            return o;
        }
        // Runtime base: square-and-multiply over the compile-time exponent bits.
        let base = self.expr(b);
        let hi = 31 - k.leading_zeros(); // top set bit (k >= 1)
        let mut acc = base;
        for bit in (0..hi).rev() {
            let sq = self.fresh();
            self.emit(LOp::Mul { a: acc, b: acc, c: sq });
            acc = sq;
            if (k >> bit) & 1 == 1 {
                let m = self.fresh();
                self.emit(LOp::Mul { a: acc, b: base, c: m });
                acc = m;
            }
        }
        acc
    }

    /// If `e` is `NAME[i]` for a top-level constant array `NAME` with a
    /// compile-time index `i`, its element (a raw `u128`).
    fn const_array_elem(&self, e: &Expr) -> Option<F64> {
        if let Expr::Index(arr, idx) = e
            && let Expr::Var(v) = arr.as_ref()
            && let Some(a) = self.const_arrays.get(v)
        {
            let i = self.try_const_index(idx)? as usize;
            return Some(
                *a.get(i)
                    .unwrap_or_else(|| panic!("const array `{v}` index {i} out of bounds (len {})", a.len())),
            );
        }
        None
    }

    /// If `e` is `len(NAME)` for a top-level constant array `NAME`, its length.
    fn const_len(&self, e: &Expr) -> Option<usize> {
        if let Expr::Call(f, args) = e
            && f == "len"
            && args.len() == 1
            && let Expr::Var(v) = &args[0]
        {
            return self.const_arrays.get(v).map(|a| a.len());
        }
        None
    }

    /// The surviving operand of `a + b` when the other is a compile-time zero,
    /// which contributes nothing and (being a constant) has no side effect to
    /// preserve. So `x + 0` lowers to just `x`: no cell, no XOR. Kills the
    /// `acc = 0; acc = acc + t` accumulator seed and similar.
    fn add_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F64::ZERO) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F64::ZERO)).then_some(a)
    }

    /// The surviving operand of `a * b` when the other is a compile-time one, a
    /// no-op multiply. Kills the `acc = GEN ** 0` (= 1) accumulator seed's first
    /// `1 * f` in every product loop.
    fn mul_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F64::ONE) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F64::ONE)).then_some(a)
    }

    /// The field value of `e` when it is a trivial compile-time constant (a
    /// literal, a literal-bound name, or `GEN ** 0`), for the `x*1`/`x+0`
    /// arithmetic identities and the `== 0` test of [`Self::lower_if`].
    fn try_lit(&self, e: &Expr) -> Option<u64> {
        match e {
            Expr::Lit(n) => u64::try_from(*n).ok(),
            Expr::Var(v) => self.scope.consts.get(v).map(|&n| n as u64),
            Expr::GPow(0) => Some(1),
            _ => None,
        }
    }

    /// The compile-time g-power exponent of a heap-index expression, when it
    /// has one: `1` (= `g^0`), `GEN`, `GEN ** k`, power-of-two literals
    /// (`g = x`, so the literal `2^j` IS `g^j`), names bound to such
    /// literals, and products of those (exponents add). `None` for runtime
    /// values, and for exponents ≥ 2^MIN_LOG_MEM, which must not become a
    /// `DEREF` `beta` immediate (`beta` is capped by the smallest admissible
    /// memory size; the fallback MUL path handles any element).
    fn try_gpow_index(&self, idx: &Expr) -> Option<u32> {
        let cap = |k: u32| (k < (1u32 << lean_vm::cpu::MIN_LOG_MEM)).then_some(k);
        let pow2 = |n: u128| (n.is_power_of_two() && n < (1 << 64)).then(|| n.trailing_zeros());
        match idx {
            Expr::Lit(n) => pow2(*n).and_then(cap),
            Expr::Var(v) => pow2(*self.scope.consts.get(v)? as u128).and_then(cap),
            Expr::Gen => Some(1),
            Expr::GPow(k) => cap(u32::try_from(*k).ok()?),
            Expr::GenPow(e) => cap(self.try_const_index(e)?),
            Expr::Mul(a, b) => cap(self.try_gpow_index(a)?.checked_add(self.try_gpow_index(b)?)?),
            _ => None,
        }
    }

    /// Resolve a `blake3` operand — a size-4 `StackBuf` name, a 4-cell
    /// `StackBuf` slice, or a 4-cell `HeapBuf` slice. Stack operands are used in
    /// place; heap operands must be
    /// bridged through the stack, since `BLAKE3` addresses only frame cells (see
    /// [`Self::blake3_input`]).
    fn blake3_operand(&mut self, e: &Expr) -> B3Operand {
        match e {
            Expr::Var(_) => {
                let (base, size) = self
                    .stack_of(e)
                    .expect("a bare blake3 operand must be a StackBuf; slice a HeapBuf: `buf[lo:lo + 4]`");
                assert!(
                    size == 4,
                    "a whole-StackBuf blake3 operand must have size 4; slice a larger one: `buf[lo:lo + 4]`"
                );
                B3Operand::Stack(base)
            }
            Expr::Slice(arr, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                // Compile-time bounds: integer cell indexes `lo..lo+4` (frame
                // offsets for a stack, g-power exponents for the heap).
                (Some(lo), Some(hi)) => {
                    assert!(hi == lo + 4, "a blake3 slice must span exactly 4 cells, got {lo}:{hi}");
                    if let Some((base, size)) = self.stack_of(arr) {
                        assert!(hi <= size, "slice {lo}:{hi} out of bounds (StackBuf size {size})");
                        B3Operand::Stack(base + lo)
                    } else {
                        // A heap slice: fold `arr`'s shift and `lo` into the
                        // pointer offset, checking the 4-cell span.
                        self.check_heap_bound(arr, lo as u128, 4);
                        let (ptr, lo) = self.heap_base(arr, lo as u128);
                        B3Operand::Heap { ptr, lo }
                    }
                }
                // Runtime start (heap only): `buf[i:i + 4]` with a runtime
                // g-power index `i` names the cells `buf·i·g^k`, k < 4. The
                // `hi` bound cannot be evaluated, only shape-checked: it must
                // be syntactically `lo + 4`. One MUL folds `i` into the
                // pointer; the four-cell bridge is then offsets 0..4 off it.
                _ => {
                    assert!(
                        self.stack_of(arr).is_none(),
                        "a StackBuf slice needs compile-time bounds (frame offsets are baked into the bytecode)"
                    );
                    assert!(
                        plus_k(lo, hi) == Some(4),
                        "a runtime blake3 slice must have the shape `buf[i:i + 4]`, got `{lo:?}:{hi:?}`"
                    );
                    let (ptr, lo) = self.heap_addr(arr, lo);
                    B3Operand::Heap { ptr, lo }
                }
            },
            other => {
                panic!("a blake3 operand must be a StackBuf, a StackBuf slice, or a HeapBuf slice, got `{other:?}`")
            }
        }
    }

    /// Materialize one two-word BLAKE3 chunk only when its expressions cannot be
    /// forwarded as an adjacent pair. This is what lets an inline four-word list
    /// such as `[x[0], x[1], 0, 0]` name the two real chunks directly, without
    /// reserving a throwaway four-cell `StackBuf` in every call frame.
    fn blake3_chunk_exprs(&mut self, values: &[Expr]) -> Off {
        assert_eq!(values.len(), 2, "a BLAKE3 chunk has two 64-bit words");
        let aliases = [self.copy_alias(&values[0]), self.copy_alias(&values[1])];
        match aliases {
            [Some(Alias::Cell(a)), Some(Alias::Cell(b))] if b == a + 1 => self.chunk_src(a),
            [Some(Alias::Const(a)), Some(Alias::Const(b))] => self.chunk_const_run([a, b]),
            _ => {
                let base = self.alloc_stack(2);
                for (k, value) in values.iter().enumerate() {
                    let dst = base + k as u32;
                    if let Some(alias) = aliases[k] {
                        self.alias.insert(dst, alias);
                    } else {
                        self.expr_into(value, dst);
                    }
                }
                self.chunk_src(base)
            }
        }
    }

    /// A `blake3` operand as two independently addressed 128-bit chunks. Stack
    /// chunks and inline four-word lists forward through adjacent aliases without
    /// copies. A heap slice is bridged into a fresh stack run with two
    /// `DEREF_128` rows. The `β` immediates fold in the heap offsets. The heap
    /// cells must already be written.
    fn blake3_input(&mut self, e: &Expr) -> [Off; 2] {
        if let Expr::ListLit(values) = e {
            assert_eq!(values.len(), 4, "an inline BLAKE3 input list must contain four words");
            let lo = self.blake3_chunk_exprs(&values[..2]);
            let hi = self.blake3_chunk_exprs(&values[2..]);
            return [lo, hi];
        }
        match self.blake3_operand(e) {
            B3Operand::Stack(o) => [self.chunk_src(o), self.chunk_src(o + 2)],
            B3Operand::Heap { ptr, lo } => {
                let t = self.alloc_stack(4);
                self.emit(LOp::Deref128 {
                    alpha: ptr,
                    beta: lo,
                    gamma: t,
                });
                self.emit(LOp::Deref128 {
                    alpha: ptr,
                    beta: lo + 2,
                    gamma: t + 2,
                });
                [t, t + 2]
            }
        }
    }

    /// Resolve a chaining value to one contiguous four-word run.
    fn blake3_cv(&mut self, e: &Expr) -> Off {
        let chunks = self.blake3_input(e);
        if chunks[1] == chunks[0] + 2 {
            return chunks[0];
        }
        let cv = self.alloc_stack(4);
        for k in 0..2 {
            self.copy(chunks[0] + k, cv + k);
            self.copy(chunks[1] + k, cv + 2 + k);
        }
        cv
    }

    /// Ensure deferred stack aliases in a run are physically materialized: VM
    /// instructions that consume a run address cannot follow compiler aliases.
    fn materialize_run(&mut self, base: Off, len: u32) {
        for k in 0..len {
            let cell = base + k;
            if self.alias.contains_key(&cell) {
                let src = self.word_src(cell);
                self.alias.remove(&cell);
                self.copy(src, cell);
            }
        }
    }

    /// Resolve a three-word extension operand and, when its high two limbs are
    /// statically zero, also return the cell containing its embedded base-field
    /// value. Keeping that fact here lets multiplication use three `MUL_64`
    /// rows instead of paying for a general `MUL_192` row.
    fn ext_operand_with_base(&mut self, e: &Expr) -> (Off, Option<Off>) {
        let base = match e {
            Expr::Var(_) => {
                let (base, size) = self
                    .stack_of(e)
                    .unwrap_or_else(|| panic!("extension operand `{e:?}` must be a StackBuf value or slice"));
                assert_eq!(size, 3, "a whole extension operand must be StackBuf(3)");
                base
            }
            Expr::Slice(arr, lo, hi) => {
                let (base, size) = self.stack_of(arr).expect("extension slices must come from a StackBuf");
                let (lo, hi) = (self.const_index(lo), self.const_index(hi));
                assert_eq!(hi, lo + 3, "an extension slice must span exactly 3 words");
                assert!(hi <= size, "extension slice out of bounds (StackBuf size {size})");
                base + lo
            }
            other => panic!("extension operands must be StackBuf values or slices, got `{other:?}`"),
        };
        let aliased_base = matches!(self.alias.get(&(base + 1)), Some(Alias::Const(v)) if v.is_zero())
            && matches!(self.alias.get(&(base + 2)), Some(Alias::Const(v)) if v.is_zero());
        let constant_base = self
            .scope
            .ext_const_runs
            .iter()
            .any(|(value, &run)| run == base && value[1] == 0 && value[2] == 0);
        let scalar = if aliased_base {
            Some(self.word_src(base))
        } else if constant_base {
            Some(base)
        } else {
            None
        };
        (self.ext_src(base), scalar)
    }

    /// Resolve an arbitrary extension operand when no subfield information is
    /// needed by the caller.
    fn ext_operand(&mut self, e: &Expr) -> Off {
        self.ext_operand_with_base(e).0
    }

    /// Follow a deferred three-cell alias when it already names one contiguous
    /// extension run. Extension instructions consume only the run's FP-relative
    /// base, so forwarding the base is equivalent to materializing three copies.
    /// Mixed/scattered aliases still need their own concrete run.
    fn ext_src(&mut self, o: Off) -> Off {
        match (
            self.alias.get(&o).copied(),
            self.alias.get(&(o + 1)).copied(),
            self.alias.get(&(o + 2)).copied(),
        ) {
            (None, None, None) => o,
            (Some(Alias::Cell(s0)), Some(Alias::Cell(s1)), Some(Alias::Cell(s2))) if s1 == s0 + 1 && s2 == s0 + 2 => {
                self.ext_src(s0)
            }
            (Some(Alias::Const(a)), Some(Alias::Const(b)), Some(Alias::Const(c))) => self.ext_const_run([a, b, c]),
            _ => {
                self.materialize_run(o, 3);
                o
            }
        }
    }

    /// The base of the two-cell chunk holding the values of stack cells `o`,
    /// `o+1`, following recorded copy / zero aliases to their real source when
    /// the pair stays CONTIGUOUS there (so `BLAKE3` reads the source cells
    /// directly and the assembling copies are never emitted): a pair aliasing
    /// adjacent cells `(s, s+1)` forwards to `s`, an all-zero pair to the
    /// shared zero pair. A pair that does not forward as a unit (mixed or
    /// non-adjacent sources) is materialized into its own cells instead.
    fn chunk_src(&mut self, o: Off) -> Off {
        match (self.alias.get(&o).copied(), self.alias.get(&(o + 1)).copied()) {
            (None, None) => o,
            (Some(Alias::Cell(s0)), Some(Alias::Cell(s1))) if s1 == s0 + 1 => self.chunk_src(s0),
            (Some(Alias::Const(a)), Some(Alias::Const(b))) => self.chunk_const_run([a, b]),
            _ => {
                for k in [o, o + 1] {
                    if self.alias.contains_key(&k) {
                        let src = self.word_src(k);
                        self.alias.remove(&k);
                        self.copy(src, k);
                    }
                }
                o
            }
        }
    }

    /// The cell holding the value of stack cell `o`, following a recorded copy /
    /// zero alias to its real source. Returns `o` when it holds a genuine value.
    fn word_src(&mut self, o: Off) -> Off {
        match self.alias.get(&o).copied() {
            Some(Alias::Cell(s)) => self.word_src(s),
            Some(Alias::Const(v)) if v.is_zero() => self.zero(),
            Some(Alias::Const(v)) => self.const_cell(v),
            None => o,
        }
    }

    /// Evaluate `e` writing its value straight into cell `dst`, with no temporary +
    /// copy for the common cases (a heap read DEREFs directly into `dst`; a
    /// constant / arithmetic emits into `dst`). Falls back to `expr` + `copy` for
    /// vars, calls, and stack reads.
    fn expr_into(&mut self, e: &Expr, dst: Off) {
        // A constant-array element is a compile-time value, not a heap read.
        if let Some(elem) = self.const_array_elem(e) {
            self.emit(LOp::Set {
                o: dst,
                k: KVal::Const(elem),
            });
            return;
        }
        match e {
            // Heap read straight into dst (a stack read falls through to the copy).
            Expr::Index(arr, idx) if self.stack_of(arr).is_none() => {
                let (base, beta) = self.heap_addr(arr, idx);
                self.emit(LOp::Deref {
                    alpha: base,
                    beta,
                    gamma: dst,
                    mode: DerefMode::Cell,
                });
            }
            Expr::Lit(n) => {
                self.emit(LOp::Set {
                    o: dst,
                    k: KVal::Const(lit_field(*n)),
                });
            }
            Expr::Gen => self.emit(LOp::Set {
                o: dst,
                k: KVal::Const(g_pow(1)),
            }),
            Expr::GPow(k) => self.emit(LOp::Set {
                o: dst,
                k: KVal::Const(g_pow_u128(*k)),
            }),
            Expr::GenPow(e) => self.emit(LOp::Set {
                o: dst,
                k: KVal::Const(g_pow_u128(self.gpow_exp(e))),
            }),
            Expr::Pow(b, e) => {
                let v = self.pow_expr(b, e);
                self.copy(v, dst);
            }
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Xor { a: la, b: lb, c: dst });
                }
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Mul { a: la, b: lb, c: dst });
                }
            }
            // A call writes its single return value straight into `dst` (an
            // aliased inline return materializes, then copies into `dst`).
            Expr::Call(f, args) => {
                self.inline_stack_ret = None;
                self.call_into(f, args, &[dst]);
                let v = self.take_inline_ret_cell(dst);
                if v != dst {
                    self.copy(v, dst);
                }
            }
            _ => {
                let v = self.expr(e);
                self.copy(v, dst);
            }
        }
    }

    /// Resolve a heap access `arr[idx]` to a `DEREF`-ready pair: a cell
    /// holding a pointer `p` and a compile-time exponent `beta`, the accessed
    /// cell being `m[p·g^beta]` (heap addressing in the exponent: cell `g^k`
    /// of the buffer sits at `arr·g^k`). The fallback of [`Self::heap_addr`],
    /// which has already folded away a wholly constant index: here a constant
    /// g-power *factor* still goes into the `beta` immediate, so only the
    /// runtime factor costs a pointer `MUL`.
    fn array_ptr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        // `buf[r * GEN ** k]` (either factor order, either side): beta takes
        // every constant factor, the pointer MUL only the runtime ones.
        let (arr_rt, ka) = self.split_gpow(arr);
        let (idx_rt, ki) = self.split_gpow(idx);
        if let Some(beta) = ka.checked_add(ki).filter(|k| *k <= FOLD_MAX) {
            match (arr_rt, idx_rt) {
                (Some(a), Some(i)) => {
                    let (la, li) = (self.expr(&a), self.expr(&i));
                    let ptr = self.fresh();
                    self.emit(LOp::Mul { a: la, b: li, c: ptr });
                    return (ptr, beta as u32);
                }
                // One side is wholly constant: it is entirely beta's, and the
                // other side is already the pointer cell.
                (Some(r), None) | (None, Some(r)) => return (self.expr(&r), beta as u32),
                // Both constant: the address is a fixed g-power, which still
                // needs a cell to be dereferenced through.
                (None, None) => {}
            }
        }
        let (la, li) = (self.expr(arr), self.expr(idx));
        let ptr = self.fresh();
        self.emit(LOp::Mul { a: la, b: li, c: ptr });
        (ptr, 0)
    }

    /// Split a product into its runtime factors and the exponent carried by its
    /// compile-time `g`-power factors: `chain · x³ · GEN ** 3` gives
    /// `(chain · x³, 3)`. `None` when every factor is constant.
    ///
    /// [`Self::gaddr_of`] cannot do this: it gives up entirely on a product of
    /// two runtime bases, which is exactly the shape of an extension-strided
    /// index, so the constant factor ended up materialized by a `SET` and
    /// multiplied in by a `MUL` instead of riding a `DEREF`'s `β` immediate.
    fn split_gpow(&self, e: &Expr) -> (Option<Expr>, u128) {
        if let Expr::Mul(a, b) = e {
            let (ra, ka) = self.split_gpow(a);
            let (rb, kb) = self.split_gpow(b);
            let Some(exp) = ka.checked_add(kb) else {
                return (Some(e.clone()), 0);
            };
            return match (ra, rb) {
                (Some(x), Some(y)) => (Some(Expr::Mul(Box::new(x), Box::new(y))), exp),
                (Some(x), None) | (None, Some(x)) => (Some(x), exp),
                (None, None) => (None, exp),
            };
        }
        match self.gaddr_of(e) {
            Some(GAddr { base: None, exp }) => (None, exp),
            // `gaddr_of` does not read a power-of-two literal as a g-power, and
            // `g = x` makes it one.
            _ => match self.try_gpow_index(e) {
                Some(k) => (None, k as u128),
                None => (Some(e.clone()), 0),
            },
        }
    }

    /// The symbolic g-address of `e`, when it is one: a constant g-power
    /// (`1 = g⁰`, `GEN`, `GEN ** k`), a tracked cursor/shifted pointer, or a
    /// plain scalar var as its own base (`base·g⁰`). Products of these combine
    /// via [`gmul`]. `None` for anything with a runtime, non-g-power value.
    fn gaddr_of(&self, e: &Expr) -> Option<GAddr> {
        match e {
            Expr::Lit(1) => Some(GAddr { base: None, exp: 0 }),
            Expr::Gen => Some(GAddr { base: None, exp: 1 }),
            Expr::GPow(k) => Some(GAddr { base: None, exp: *k }),
            Expr::GenPow(e) => Some(GAddr {
                base: None,
                exp: self.try_const_index(e)? as u128,
            }),
            Expr::Var(v) => self
                .scope
                .gaddrs
                .get(v)
                .copied()
                .or_else(|| self.scope.vars.get(v).map(|&c| GAddr { base: Some(c), exp: 0 })),
            Expr::Mul(a, b) => gmul(self.gaddr_of(a)?, self.gaddr_of(b)?),
            _ => None,
        }
    }

    /// `e` as a compile-time *field* constant, when it is one: a literal, `GEN`,
    /// `GEN ** k`, a var bound to a field constant (or a constant g-power), or
    /// `+`/`*` of those evaluated in the field (XOR / `K`-mul). `None` for a
    /// runtime value, a literal exceeding the 64-bit word, or a compile-time
    /// *integer* op (`//`/`%` are index-only).
    fn try_field_const(&self, e: &Expr) -> Option<F64> {
        match e {
            // A source value literal fills one F64 word.
            Expr::Lit(n) => Some(lit_field(*n)),
            Expr::Gen => Some(g_pow(1)),
            Expr::GPow(k) => Some(g_pow_u128(*k)),
            Expr::GenPow(e) => Some(g_pow_u128(self.try_const_index(e)? as u128)),
            Expr::Var(v) => self
                .scope
                .fconsts
                .get(v)
                .copied()
                .or_else(|| match self.scope.gaddrs.get(v) {
                    Some(GAddr { base: None, exp }) => Some(g_pow_u128(*exp)),
                    _ => None,
                }),
            Expr::Add(a, b) => Some(self.try_field_const(a)? + self.try_field_const(b)?),
            Expr::Mul(a, b) => Some(self.try_field_const(a)? * self.try_field_const(b)?),
            // A constant-array element `NAME[i]` as a field value, or `len(NAME)`.
            Expr::Index(..) => self.const_array_elem(e),
            Expr::Call(..) => self.const_len(e).map(|n| F64(n as u64)),
            // `b ** e` as a field constant (constant base, compile-time exponent).
            Expr::Pow(b, e) => Some(field_pow(self.try_field_const(b)?, self.try_const_index(e)?)),
            _ => None,
        }
    }

    /// Realize a [`GAddr`] into a frame cell holding its value: a constant is one
    /// `SET`; a base with no shift is already that cell; a shifted base is a
    /// `SET`+`MUL`.
    fn materialize(&mut self, ga: GAddr) -> Off {
        match ga {
            GAddr { base: Some(c), exp: 0 } => c,
            GAddr { base, exp } => {
                let k = self.fresh();
                self.emit(LOp::Set {
                    o: k,
                    k: KVal::Const(g_pow_u128(exp)),
                });
                let Some(c) = base else { return k };
                let o = self.fresh();
                self.emit(LOp::Mul { a: c, b: k, c: o });
                o
            }
        }
    }

    /// Compile-time bounds check: when `arr` resolves to a sized `HeapBuf`
    /// (directly or through shifted aliases) and the whole index is the
    /// compile-time exponent `exp`, reject `exp + span > size`. Runtime
    /// indices are not checked (their value is not known here).
    fn check_heap_bound(&self, arr: &Expr, extra: u128, span: u128) {
        let Some(ga) = self.gaddr_of(arr) else { return };
        let (Some(base), Some(exp)) = (ga.base, ga.exp.checked_add(extra)) else {
            return;
        };
        let Some(&size) = self.heap_sizes.get(&base) else {
            return;
        };
        if exp + span > size {
            let name = self
                .scope
                .vars
                .iter()
                .find(|(_, c)| **c == base)
                .map(|(n, _)| n.as_str())
                .unwrap_or("?");
            if span == 1 {
                panic!("heap index {exp} out of bounds for `{name}` (HeapBuf size {size})");
            }
            panic!(
                "heap slice {exp}:{} out of bounds for `{name}` (HeapBuf size {size})",
                exp + span
            );
        }
    }

    /// Address `arr·g^extra` as `(base_cell, β)`, folding `arr`'s symbolic shift
    /// and the constant `extra` into `β`. Falls back to a materialized pointer
    /// (`β = 0`) when there is no runtime base or the offset exceeds [`FOLD_MAX`].
    fn heap_base(&mut self, arr: &Expr, extra: u128) -> (Off, u32) {
        self.check_heap_bound(arr, extra, 1);
        if let Some(ga) = self.gaddr_of(arr)
            && let (Some(base), Some(exp)) = (ga.base, ga.exp.checked_add(extra))
            && exp <= FOLD_MAX
        {
            return (base, exp as u32);
        }
        // `arr` is not a recognized g-address (typically a product of two
        // runtime bases), but its constant factors and `extra` still belong in
        // `β` rather than in a `SET` and a `MUL`.
        let (runtime, peeled) = self.split_gpow(arr);
        if let Some(r) = runtime
            && let Some(exp) = peeled.checked_add(extra)
            && exp <= FOLD_MAX
        {
            return (self.expr(&r), exp as u32);
        }
        let a = self.expr(arr);
        if extra == 0 {
            return (a, 0);
        }
        let k = self.fresh();
        self.emit(LOp::Set {
            o: k,
            k: KVal::Const(g_pow_u128(extra)),
        });
        let ptr = self.fresh();
        self.emit(LOp::Mul { a, b: k, c: ptr });
        (ptr, 0)
    }

    /// Address `arr[idx]` as `(base_cell, β)`. A constant g-power `idx` folds
    /// into `β` ([`Self::heap_base`]); a runtime index materializes the pointer.
    fn heap_addr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        // A compile-time index that is a plain field constant but NOT a
        // g-power (`buf[0]`, `buf[2]`, an integer unroll var) can never name
        // a heap cell (cell k lives at `buf · g^k`) and would deref a wild
        // address at proving time. Reject it here, where the source is known.
        if self.gaddr_of(idx).is_none()
            && let Some(c) = self.try_field_const(idx)
        {
            panic!(
                "heap index `{arr:?}[{idx:?}]` folds to the field constant {:#x}, not a g-power while inlining {:?}: heap cell k is addressed as `buf[GEN ** k]` (did an integer index leak in from a StackBuf conversion?)",
                c.0, self.inline_calls,
            );
        }
        match self.gaddr_of(idx) {
            Some(GAddr { base: None, exp }) => return self.heap_base(arr, exp),
            // A runtime-base index carrying a constant g-power shift
            // (`buf[cursor * GEN ** k]`): fold the whole constant part (the
            // index's shift plus `arr`'s own symbolic shift) into `β`, and
            // emit ONE pointer multiply instead of materializing g^k.
            Some(GAddr { base: Some(ib), exp }) => {
                if let Some(ga) = self.gaddr_of(arr)
                    && let (Some(ab), Some(total)) = (ga.base, ga.exp.checked_add(exp))
                    && total <= FOLD_MAX
                {
                    let ptr = self.fresh();
                    self.emit(LOp::Mul { a: ab, b: ib, c: ptr });
                    return (ptr, total as u32);
                }
            }
            None => {}
        }
        // Fall back to the constant-g-power-factor fold (a runtime index still
        // materializes the pointer `MUL`, with any constant factor in `β`).
        self.array_ptr(arr, idx)
    }

    /// Consume the [`RetBind`] a single-value inlined tail return recorded,
    /// for a call in EXPRESSION position (embedded in arithmetic, a store
    /// RHS, a single-target match arm): there is no name to alias-bind, so an
    /// aliased return materializes into a plain cell (free for a var / an
    /// exp-0 g-address; one `MUL` for a shifted pointer). `dst` is the call's
    /// destination cell, already written by a real call or a plain-scalar
    /// return, so it is the fallback.
    fn take_inline_ret_cell(&mut self, dst: Off) -> Off {
        match self.inline_stack_ret.take().and_then(|b| b.into_iter().next()) {
            Some(RetBind::Gaddr(ga)) => self.materialize(ga),
            Some(RetBind::Stack(base, size)) => {
                assert_eq!(
                    size, 1,
                    "a multi-cell StackBuf return needs a `let` binding, not an expression use (inline stack: {:?})",
                    self.inline_calls,
                );
                base
            }
            _ => dst,
        }
    }

    /// Lower a call; returns one caller offset per source-level return value.
    /// A real-call StackBuf return is flattened into consecutive ABI cells and
    /// copied into a fresh consecutive run in the caller. `inline_stack_ret`
    /// describes those logical bindings to the surrounding let/tuple lowering.
    fn call(&mut self, callee: &str, args: &[Expr], n_ret: usize) -> Vec<Off> {
        assert!(
            callee != "blake3",
            "blake3 is a statement: `blake3(a, b, out)` writes the digest into the 4-cell stack run `out`"
        );
        self.inline_stack_ret = None;
        if self.defs.get(callee).is_some_and(|d| d.inline) {
            let dsts: Vec<Off> = (0..n_ret).map(|_| self.fresh()).collect();
            self.call_into(callee, args, &dsts);
            return dsts;
        }

        let shapes = self
            .defs
            .get(callee)
            .map(|d| d.return_shapes.clone())
            .unwrap_or_else(|| vec![ReturnShape::Scalar; n_ret]);
        assert_eq!(
            shapes.len(),
            n_ret,
            "`{callee}` returns {} values, call binds {n_ret}",
            shapes.len()
        );
        let mut logical = Vec::with_capacity(n_ret);
        let mut physical = Vec::new();
        let mut binds = Vec::with_capacity(n_ret);
        for shape in shapes {
            match shape {
                ReturnShape::Scalar => {
                    let dst = self.fresh();
                    logical.push(dst);
                    physical.push(dst);
                    binds.push(RetBind::Scalar);
                }
                ReturnShape::StackBuf(size) => {
                    assert!(size > 0, "a returned StackBuf must not be empty");
                    let base = self.alloc_stack(size);
                    logical.push(base);
                    physical.extend(base..base + size);
                    binds.push(RetBind::Stack(base, size));
                }
            }
        }
        self.lower_call(callee, args, physical.len(), None, Some(&physical), false);
        self.inline_stack_ret = Some(binds);
        logical
    }

    /// Evaluate `callee(args)` into `dsts`, inlining the callee when it is
    /// `@inline` ([`Self::try_inline`]), else a real call.
    fn call_into(&mut self, callee: &str, args: &[Expr], dsts: &[Off]) {
        assert!(callee != "blake3", "blake3 is a statement, not a value-returning call");
        if !self.try_inline(callee, args, dsts) {
            if let Some(def) = self.defs.get(callee) {
                assert_eq!(
                    def.return_shapes.len(),
                    dsts.len(),
                    "`{callee}` returns {} values, call binds {}",
                    def.return_shapes.len(),
                    dsts.len()
                );
                assert!(
                    def.return_shapes.iter().all(|s| *s == ReturnShape::Scalar),
                    "a normal function's multi-cell StackBuf return needs a `let` binding"
                );
            }
            self.lower_call(callee, args, dsts.len(), None, Some(dsts), false);
        }
    }

    /// The value a `Const` parameter takes, as the literal that substitutes for
    /// it: a `GEN ** k` argument stays a g-power, everything else must fold to a
    /// compile-time integer (a bound name, a const-array element `DEPTH[lvl]`,
    /// `len(...)`, index arithmetic over other `Const` params). `None` when it
    /// does not fold.
    fn const_arg(&self, a: &Expr) -> Option<Expr> {
        Some(match a {
            Expr::Lit(n) => Expr::Lit(*n),
            Expr::Gen => Expr::GPow(1),
            Expr::GPow(k) => Expr::GPow(*k),
            other => Expr::Lit(self.try_const_index(other)? as u128),
        })
    }

    /// The runtime params, runtime args, and `Const`-substituted body of a call
    /// to a user function: the ingredients for inlining. `None` for a builtin or
    /// unknown callee, an arity mismatch, or an unresolved `Const` argument.
    fn specialized_body(&self, callee: &str, args: &[Expr]) -> Option<SpecializedBody> {
        let def = self.defs.get(callee)?;
        if args.len() != def.params.len() {
            return None;
        }
        let mut body = def.body.clone();
        let (mut rt_params, mut rt_args) = (Vec::new(), Vec::new());
        for ((p, &is_const), a) in def.params.iter().zip(&def.const_params).zip(args) {
            if !is_const {
                rt_params.push(p.clone());
                rt_args.push(a.clone());
                continue;
            }
            let c = self.const_arg(a)?;
            body = subst_stmts(&body, p, &c);
        }
        Some((rt_params, rt_args, body, def.n_ret))
    }

    /// Inline an `@inline` `callee(args)` into the current frame, binding its
    /// return values straight into `dsts`: no frame setup, no argument/return
    /// plumbing, no call/return jumps. Returns `false` for a non-`@inline`
    /// callee (the caller emits a real call). Panics if an `@inline` function
    /// isn't inlinable ([`body_inlinable`]) or its `Const` args don't resolve.
    fn try_inline(&mut self, callee: &str, args: &[Expr], dsts: &[Off]) -> bool {
        if !self.defs.get(callee).is_some_and(|d| d.inline) {
            return false;
        }
        let (params, rt_args, body, n_ret) = self
            .specialized_body(callee, args)
            .unwrap_or_else(|| panic!("`@inline {callee}`: bad arity or unresolved Const argument"));
        assert_eq!(
            n_ret,
            dsts.len(),
            "`@inline {callee}` returns {n_ret} values, call binds {}",
            dsts.len()
        );
        assert!(
            body_inlinable(&body, self.defs),
            "`@inline {callee}` must be a single tail `return` with only builtin or @inline calls, and no loop/match"
        );
        assert!(
            !self.inline_calls.iter().any(|f| f == callee),
            "recursive @inline expansion is not supported: {} -> {callee}",
            self.inline_calls.join(" -> ")
        );
        // Bind the params from the caller-scope arguments (symbolically where we
        // can, so a shifted-pointer arg keeps folding into `β`; a `StackBuf` arg
        // aliases its cell run), then lower the body in a fresh variable
        // environment, since a function sees only its params. The frame, `one`,
        // `self_fp`, and range-check bounds stay the caller's: the inlined code
        // runs in the caller's frame, so they fit.
        enum Bind {
            Stack(Off, u32),
            Addr(GAddr),
            Cell(Off),
        }
        let mut binds: Vec<(String, Bind)> = Vec::new();
        for (p, a) in params.iter().zip(&rt_args) {
            let b = if let Some((base, size)) = self.stack_of(a) {
                Bind::Stack(base, size)
            } else if let Expr::ListLit(es) = a {
                let (base, size) = self.materialize_list(es);
                Bind::Stack(base, size)
            } else if let Some(ga) = self.gaddr_of(a) {
                Bind::Addr(ga)
            } else if let Expr::Call(f, cargs) = a
                && self.defs.contains_key(f)
            {
                // A StackBuf-returning helper can feed another helper directly
                // (`eadd(emul(a, b), c)`). Evaluate it once and pass the
                // returned run by alias, just as a named intermediate would.
                self.inline_stack_ret = None;
                let cell = self.call(f, cargs, 1)[0];
                match self.inline_stack_ret.take().and_then(|v| v.into_iter().next()) {
                    Some(RetBind::Stack(base, size)) => Bind::Stack(base, size),
                    Some(RetBind::Gaddr(ga)) => Bind::Addr(ga),
                    _ => Bind::Cell(cell),
                }
            } else if let (Some(r), k) = self.split_gpow(a)
                && k > 0
            {
                // A runtime product times a constant g-power (`chain · x³ · g³`)
                // is no `GAddr`, since `gmul` gives up on two runtime bases. Bind
                // the runtime part as the base and the constant as the shift
                // anyway, so it still reaches a callee `DEREF`'s `β` immediate
                // instead of being materialized here by a `SET` and a `MUL`.
                Bind::Addr(GAddr {
                    base: Some(self.expr(&r)),
                    exp: k,
                })
            } else {
                Bind::Cell(self.expr(a))
            };
            binds.push((p.clone(), b));
        }
        // Only the name bindings reset: the inlined body runs in the caller's
        // frame, so the caller's `one`, `self_fp`, constant and bound cells all
        // still name valid cells and stay live.
        let saved = (
            std::mem::take(&mut self.scope.vars),
            std::mem::take(&mut self.scope.stacks),
            std::mem::take(&mut self.scope.consts),
            std::mem::take(&mut self.scope.gaddrs),
            std::mem::take(&mut self.scope.fconsts),
        );
        for (p, b) in binds {
            match b {
                Bind::Stack(base, size) => {
                    self.scope.stacks.insert(p, (base, size));
                }
                Bind::Addr(ga) => {
                    self.scope.gaddrs.insert(p, ga);
                }
                Bind::Cell(cell) => {
                    self.scope.vars.insert(p, cell);
                }
            }
        }
        let saved_ret = self.inline_ret.replace(dsts.to_vec());
        self.inline_calls.push(callee.to_string());
        for s in &body {
            self.stmt(s);
        }
        let popped = self.inline_calls.pop();
        debug_assert_eq!(popped.as_deref(), Some(callee));
        self.inline_ret = saved_ret;
        (
            self.scope.vars,
            self.scope.stacks,
            self.scope.consts,
            self.scope.gaddrs,
            self.scope.fconsts,
        ) = saved;
        true
    }

    /// If `callee` declares `Const` parameters, monomorphize: the constant
    /// arguments (literals, `GEN ** k`, or literal-bound names) substitute
    /// into a copy of the callee — queued once per distinct constant tuple,
    /// named `callee__L5_G3`-style — and only the runtime arguments remain.
    fn specialize(&mut self, callee: &str, args: &[Expr]) -> (String, Vec<Expr>, Vec<bool>) {
        // Generated runtime-loop helpers live in `queue`, not the source
        // definition map. Clone the metadata so their Ext captures use the
        // same flattened call ABI on both the entry and recursive calls.
        let Some(def) = self
            .defs
            .get(callee)
            .cloned()
            .or_else(|| self.queue.iter().find(|f| f.name == callee).cloned())
        else {
            return (callee.to_string(), args.to_vec(), vec![false; args.len()]);
        };
        if !def.const_params.contains(&true) {
            return (callee.to_string(), args.to_vec(), def.ext_params.clone());
        }
        assert_eq!(args.len(), def.params.len(), "call to `{callee}`: wrong arity");
        let mut tag = String::new();
        let (mut rt_params, mut rt_args, mut rt_ext, mut substs) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        for (((p, &is_const), &is_ext), a) in def.params.iter().zip(&def.const_params).zip(&def.ext_params).zip(args) {
            if !is_const {
                rt_params.push(p.clone());
                rt_args.push(a.clone());
                rt_ext.push(is_ext);
                continue;
            }
            let c = self.const_arg(a).unwrap_or_else(|| {
                panic!(
                    "argument for Const parameter `{p}` of `{callee}` must be a compile-time \
                     constant, got `{a:?}`"
                )
            });
            tag.push_str(&match &c {
                Expr::Lit(n) => format!("_L{n}"),
                Expr::GPow(k) => format!("_G{k}"),
                _ => unreachable!(),
            });
            substs.push((p.clone(), c));
        }
        let name = format!("{callee}_{tag}");
        if !self.queue.iter().any(|f| f.name == name) {
            assert!(
                self.queue.len() < 10_000,
                "Const specialization explosion (recursive constants?)"
            );
            let mut body = def.body.clone();
            for (p, c) in &substs {
                body = subst_stmts(&body, p, c);
            }
            let const_params = vec![false; rt_params.len()];
            self.queue.push(Func {
                name: name.clone(),
                params: rt_params,
                const_params,
                ext_params: rt_ext.clone(),
                n_ret: def.n_ret,
                return_shapes: def.return_shapes.clone(),
                body,
                inline: false,
            });
        }
        (name, rt_args, rt_ext)
    }

    /// Lower a call. Return values land in `dsts_in` when given (write-once, so
    /// distinct arms of a `match_range` may share the same cells), else in fresh
    /// cells, sparing the caller a temp-then-copy.
    fn lower_call(
        &mut self,
        callee: &str,
        args: &[Expr],
        n_ret: usize,
        cond: Option<Off>,
        dsts_in: Option<&[Off]>,
        tail: bool,
    ) -> Vec<Off> {
        let (callee, args, ext_params) = self.specialize(callee, args);
        let (callee, args) = (callee.as_str(), args.as_slice());
        let mut arg_offs = Vec::new();
        for (arg, &is_ext) in args.iter().zip(&ext_params) {
            if is_ext {
                let stack = if let Some(run) = self.stack_of(arg) {
                    Some(run)
                } else if let Expr::ListLit(es) = arg {
                    Some(self.materialize_list(es))
                } else if let Expr::Call(f, cargs) = arg
                    && self.defs.contains_key(f)
                {
                    self.inline_stack_ret = None;
                    let _ = self.call(f, cargs, 1);
                    match self.inline_stack_ret.take().and_then(|v| v.into_iter().next()) {
                        Some(RetBind::Stack(base, size)) => Some((base, size)),
                        _ => None,
                    }
                } else {
                    None
                };
                let (base, len) = stack.unwrap_or_else(|| panic!("Ext argument to `{callee}` must be a StackBuf(3)"));
                assert_eq!(len, 3, "Ext argument to `{callee}` must be a StackBuf(3)");
                // Initialized StackBufs are commonly represented as deferred
                // aliases. A real-call ABI must pass their values, not the
                // unwritten alias destination cells.
                arg_offs.extend((0..3).map(|k| self.word_src(base + k)));
            } else {
                arg_offs.push(self.expr(arg));
            }
        }
        let nfp = self.fresh();
        let entry = self.fresh();
        // Resolve the jump condition up front: `self.one()` may emit a `SET`, and
        // nothing may sit between the retpc `DEREF` and the `JUMP` (the `g²·pc`
        // return target assumes the `JUMP` is exactly one instruction later).
        let oc = cond.unwrap_or_else(|| self.one());
        self.emit(LOp::Set {
            o: entry,
            k: KVal::Entry(callee.to_string()),
        });

        // The frame-pointer hint fires before the first DEREF that reads `nfp`.
        self.pending.push(Hint::AllocFrame {
            ptr: nfp,
            callee: callee.to_string(),
        });
        // Transfer an adjacent three-word source run with the packed memory
        // relation. This covers both Ext arguments and contiguous prefixes of
        // wider physical values.
        let mut i = 0;
        while i < arg_offs.len() {
            if i + 2 < arg_offs.len() && arg_offs[i + 1] == arg_offs[i] + 1 && arg_offs[i + 2] == arg_offs[i] + 2 {
                self.emit(LOp::DerefExt {
                    alpha: nfp,
                    beta: 2 + i as u32,
                    gamma: arg_offs[i],
                });
                i += 3;
            } else if i + 1 < arg_offs.len() && arg_offs[i + 1] == arg_offs[i] + 1 {
                self.emit(LOp::Deref128 {
                    alpha: nfp,
                    beta: 2 + i as u32,
                    gamma: arg_offs[i],
                });
                i += 2;
            } else {
                self.emit(LOp::Deref {
                    alpha: nfp,
                    beta: 2 + i as u32,
                    gamma: arg_offs[i],
                    mode: DerefMode::Cell,
                });
                i += 1;
            }
        }
        if tail {
            // Tail call: hand the callee OUR return target, so it returns to our
            // caller and we are never resumed. Cells 0/1 of this frame already
            // hold that target (written by whoever called us).
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 1,
                gamma: 1,
                mode: DerefMode::Cell,
            }); // retfp := our retfp
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 0,
                gamma: 0,
                mode: DerefMode::Cell,
            }); // retpc := our retpc
        } else {
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 1,
                gamma: 0,
                mode: DerefMode::Fp,
            }); // retfp
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 0,
                gamma: 0,
                mode: DerefMode::Pc,
            }); // retpc = g²·pc
        }
        self.emit(LOp::Jump { oc, od: entry, of: nfp });

        let n_args = arg_offs.len() as u32;
        let dsts: Vec<Off> = match dsts_in {
            Some(d) => d.to_vec(),
            None => (0..n_ret).map(|_| self.fresh()).collect(),
        };
        // Return cells have the same flattened ABI. Pack any consecutive
        // caller destination triple into one DEREF_EXT; this covers StackBuf(3)
        // returns and three-word prefixes without changing logical return
        // shapes or requiring a new calling convention.
        let mut i = 0;
        while i < dsts.len() {
            if i + 2 < dsts.len() && dsts[i + 1] == dsts[i] + 1 && dsts[i + 2] == dsts[i] + 2 {
                self.emit(LOp::DerefExt {
                    alpha: nfp,
                    beta: 2 + n_args + i as u32,
                    gamma: dsts[i],
                });
                i += 3;
            } else if i + 1 < dsts.len() && dsts[i + 1] == dsts[i] + 1 {
                self.emit(LOp::Deref128 {
                    alpha: nfp,
                    beta: 2 + n_args + i as u32,
                    gamma: dsts[i],
                });
                i += 2;
            } else {
                self.emit(LOp::Deref {
                    alpha: nfp,
                    beta: 2 + n_args + i as u32,
                    gamma: dsts[i],
                    mode: DerefMode::Cell,
                });
                i += 1;
            }
        }
        dsts
    }

    fn stmt(&mut self, s: &Stmt) {
        let tail = std::mem::take(&mut self.tail_call);
        match s {
            Stmt::Let(name, e) => match e {
                // `x = StackBuf(n)`: bind a run of `n` consecutive frame cells.
                Expr::StackBuf(n) => {
                    let base = self.alloc_stack(*n as u32);
                    self.scope.consts.remove(name);
                    self.rebind(name, Binding::Stack(base, *n as u32));
                }
                // `x = [a, b, …]`: an initialized StackBuf. Allocate the run and
                // write each element in place (each write is the stack-store
                // path, so copies/constants defer as aliases). Elements are
                // lowered before `name` rebinds, so they may read its old
                // binding (`fs = [fs[1], fs[0]]`).
                Expr::ListLit(es) => {
                    let base = self.alloc_stack(es.len() as u32);
                    for (k, el) in es.iter().enumerate() {
                        let dst = base + k as u32;
                        if let Some(a) = self.copy_alias(el) {
                            self.alias.insert(dst, a);
                        } else {
                            self.alias.remove(&dst);
                            self.expr_into(el, dst);
                        }
                    }
                    self.scope.consts.remove(name);
                    self.rebind(name, Binding::Stack(base, es.len() as u32));
                }
                // `x = other_stackbuf`: a compile-time alias of the same cell
                // run (zero instructions), the chaining-state idiom `st = sn`
                // of an MD loop.
                Expr::Var(v) if self.scope.stacks.contains_key(v) => {
                    let (base, size) = self.scope.stacks[v];
                    self.scope.consts.remove(name);
                    self.rebind(name, Binding::Stack(base, size));
                }
                _ => {
                    // NOTE: `name`'s old binding stays visible while the RHS is
                    // lowered (the MD-chain idiom `cvb = obs(cvb, x)` reads it);
                    // each terminal path below unbinds/rebinds afterwards.
                    // A compile-time integer binding (a literal, or an expression
                    // that folds: `FOLDBASE[lvl] + j`, `n // 2`, `len(A) - 1`) is
                    // usable as a compile-time index / bound / exponent, and that
                    // role survives the value binding chosen below.
                    let k_idx = self.try_const_index(e);
                    match k_idx {
                        Some(k) => {
                            self.scope.consts.insert(name.clone(), k);
                        }
                        None => {
                            self.scope.consts.remove(name);
                        }
                    }
                    // A symbolic g-address (a constant g-power or a shifted
                    // pointer) or a compile-time field constant stays virtual:
                    // no instruction here, folded / materialized only on demand.
                    if let Some(ga) = self.gaddr_of(e) {
                        self.rebind(name, Binding::Gaddr(ga));
                    } else if let Some(c) = self.try_field_const(e) {
                        self.rebind(name, Binding::FConst(c));
                    } else if let Some(k) = k_idx {
                        // Integer-only fold (`//`, `-`, `%` of constants): a
                        // compile-time value too, and as a scalar it is the field
                        // element with those 128 bits, materialized on demand.
                        self.rebind(name, Binding::FConst(lit_field(k as u128)));
                    } else if let Expr::Call(cf, cargs) = e
                        && self.defs.contains_key(cf)
                    {
                        // A bare `name = call(...)` of a user function: bind per
                        // the inlined return's RetBind, aliasing its StackBuf run
                        // or folded g-address at zero copies (the `cvb = obs(...)`
                        // / advanced-cursor idiom), else (a plain scalar, or a
                        // real call) bind the dst cell. Embedded calls do NOT
                        // take this path: `expr` materializes theirs
                        // ([`Self::take_inline_ret_cell`]).
                        self.inline_stack_ret = None;
                        let o = self.call(cf, cargs, 1)[0];
                        let b = match self.inline_stack_ret.take().and_then(|b| b.into_iter().next()) {
                            Some(RetBind::Stack(base, size)) => Binding::Stack(base, size),
                            Some(RetBind::Gaddr(ga)) => Binding::Gaddr(ga),
                            _ => Binding::Scalar(o),
                        };
                        self.rebind(name, b);
                    } else {
                        let o = self.expr(e);
                        self.rebind(name, Binding::Scalar(o));
                    }
                }
            },
            Stmt::LetTuple(names, f, args) => {
                let dsts = self.call(f, args, names.len());
                // Each returned value binds per its RetBind (alias a StackBuf run
                // or folded g-address, else take the scalar dst cell); a real call
                // leaves the field None, so every name binds its scalar dst.
                let binds = self.inline_stack_ret.take();
                for (i, (n, d)) in names.iter().zip(&dsts).enumerate() {
                    let b = match binds.as_ref().and_then(|b| b.get(i).copied()) {
                        Some(RetBind::Stack(base, size)) => Binding::Stack(base, size),
                        Some(RetBind::Gaddr(ga)) => Binding::Gaddr(ga),
                        _ => Binding::Scalar(*d),
                    };
                    self.scope.consts.remove(n);
                    self.rebind(n, b);
                }
            }
            Stmt::AssertEq(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let t = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: t });
                self.emit(LOp::Set {
                    o: t,
                    k: KVal::Const(F64::ZERO),
                });
            }
            Stmt::AssertNe(a, b) => self.lower_assert_ne(a, b),
            Stmt::AssertLt(e, k) => self.lower_assert_lt(e, *k),
            Stmt::HintWitness { dest, name } => self.lower_hint_witness(dest, name),
            Stmt::Print { label, value } => {
                // Prover-side debug print: evaluate the value into a cell, hang
                // a Print hint on a no-op anchor so it fires exactly here (and
                // only on this path), at witness generation. No constraints.
                let cell = self.expr(value);
                self.pending.push(Hint::Resolved(RHint::Print {
                    label: label.clone(),
                    cell,
                }));
                let o = self.fresh();
                self.emit(LOp::Set {
                    o,
                    k: KVal::Const(F64::ZERO),
                });
            }
            Stmt::If {
                eq,
                lhs,
                rhs,
                then,
                els,
            } => self.lower_if(*eq, lhs, rhs, then, els),
            Stmt::Match { x, cases } => self.lower_match(x, cases),
            Stmt::LetMatchRange { names, x, arms } => self.lower_match_range(names, x, arms),
            Stmt::Call(f, args) => {
                if !self.lower_builtin(f, args) {
                    self.call(f, args, 0);
                }
            }
            Stmt::Store(arr, idx, val) => {
                // Stack write `sa[k] = val`: place `val` straight into cell `base+k`.
                if let Some((base, size)) = self.stack_of(arr) {
                    let k = self.const_index(idx);
                    assert!(k < size, "stack store index {k} out of bounds (size {size})");
                    let dst = base + k;
                    // A plain copy / zero is deferred as an alias and forwarded at
                    // its uses (write-once, so the source cell keeps its value):
                    // the assembling `MUL`/`SET` is never emitted.
                    if let Some(a) = self.copy_alias(val) {
                        self.alias.insert(dst, a);
                    } else {
                        self.alias.remove(&dst);
                        self.expr_into(val, dst);
                    }
                } else {
                    // Heap store `arr[idx] = val`: assert m[arr·idx] == val (write-once).
                    let v = self.expr(val);
                    let (base, beta) = self.heap_addr(arr, idx);
                    self.emit(LOp::Deref {
                        alpha: base,
                        beta,
                        gamma: v,
                        mode: DerefMode::Cell,
                    });
                }
            }
            Stmt::Return(es) => self.lower_return(es),
            Stmt::CallIfNe(lhs, rhs, callee, args) => {
                // A conditional call: the frame setup runs either way, and the
                // `JUMP`'s nonzero test decides whether the callee is entered,
                // so the not-taken path continues straight after it. In tail
                // position the callee inherits THIS frame's `retpc`/`retfp`, so
                // a `mul_range` loop builds no unwind chain: only the final
                // iteration returns, straight to the loop's original caller.
                let (la, lb) = (self.expr(lhs), self.expr(rhs));
                let x = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: x }); // x = lhs + rhs; x != 0 ⇔ lhs != rhs
                self.lower_call(callee, args, 0, Some(x), None, tail);
            }
            Stmt::For { var, lo, hi, body } => self.lower_for(var, *lo, hi, body),
            // Compile-time unrolling: emit the body per integer, the counter
            // substituted as its literal. Every copy executes (this is
            // straight-line code, not a branch), so bindings simply rebind (a
            // fresh binding per iteration) and lazy caches persist.
            Stmt::Unroll { var, lo, hi, body } => {
                let bound = |s: &Self, e: &Expr| {
                    s.try_const_index(e)
                        .unwrap_or_else(|| panic!("unroll bounds must be compile-time integers, got `{e:?}`"))
                };
                let (lo, hi) = (bound(self, lo), bound(self, hi));
                assert!(lo <= hi, "unroll(a, b) needs a <= b, got ({lo}, {hi})");
                for j in lo..hi {
                    for s in subst_stmts(body, var, &Expr::Lit(j as u128)) {
                        self.stmt(&s);
                    }
                }
            }
        }
    }

    /// The statement-position builtins, `true` if `f` was one of them (else the
    /// caller emits an ordinary call). The `hint_*` ones queue prover-side
    /// advice, re-checked in-circuit by their caller: `hint_decompose_bits`
    /// writes a value's bits into a buffer, `hint_decompose_bits_exponent` the
    /// bits of `n` where the value is `g^n` (a bounded dlog at witness
    /// generation). The `*_192` ones are the extension-field instructions.
    fn lower_builtin(&mut self, f: &str, args: &[Expr]) -> bool {
        match f {
            "hint_decompose_bits" | "hint_decompose_bits_exponent" => {
                assert_eq!(args.len(), 3, "{f}(bits, value, nbits)");
                let bits_ptr = self.expr(&args[0]);
                let value = self.expr(&args[1]);
                let nbits = self.const_index(&args[2]);
                self.pending.push(Hint::Resolved(if f == "hint_decompose_bits" {
                    RHint::BitDecompose { value, bits_ptr, nbits }
                } else {
                    RHint::BitDecomposeExp { value, bits_ptr, nbits }
                }));
            }
            "blake3" => self.lower_blake3(args),
            "xor_192" | "mul_192" | "div_192" => {
                assert_eq!(args.len(), 3, "{f}(a, b, out) takes three extension buffers");
                let (a, a_base) = self.ext_operand_with_base(&args[0]);
                let (b, b_base) = self.ext_operand_with_base(&args[1]);
                let c = self.ext_operand(&args[2]);
                match f {
                    "xor_192" => self.emit(LOp::AddExt { a, b, c }),
                    // One extension row beats decomposing into base rows on every
                    // axis: a squaring is 3 MUL + 1 XOR (48 committed cells, 20 bus
                    // flushes, 4 cycles) against one MUL_EXT row (27, 11, 1), and a
                    // base-scalar product is 3 MUL (36, 15, 3) against one
                    // MUL_EXT_BASE row. `a == b` needs no special case: the row reads
                    // the run twice, at two access counts, and squares it.
                    "mul_192" => match (a_base, b_base) {
                        // The scalar mode reads its first operand's run for the bus
                        // but multiplies by lane 0 alone, so the scalar must name a
                        // run whose upper lanes are the zeros it ignores.
                        (Some(scalar), _) if a != b => self.emit(LOp::MulExtBase { a: scalar, b, c }),
                        (_, Some(scalar)) if a != b => self.emit(LOp::MulExtBase { a: scalar, b: a, c }),
                        _ => self.emit(LOp::MulExt { a, b, c }),
                    },
                    // c = a / b is constrained by c * b = a; the VM's write-once
                    // deduction fills c when it is unset.
                    _ => self.emit(LOp::MulExt { a: c, b, c: a }),
                }
            }
            "mul_192_base" => {
                assert_eq!(
                    args.len(),
                    3,
                    "mul_192_base(a, b, out) takes a scalar and two extension buffers"
                );
                let a = self.expr(&args[0]);
                let b = self.ext_operand(&args[1]);
                let c = self.ext_operand(&args[2]);
                // Keep the explicit keyword as the dedicated ISA operation:
                // recursion's coverage guest deliberately exercises every
                // variant, while implicit `[x, 0, 0] * value` expressions are
                // free to use the cheaper base decomposition.
                self.emit(LOp::MulExtBase { a, b, c });
            }
            "deref_192" => {
                assert_eq!(
                    args.len(),
                    2,
                    "deref_192(ptr, value) takes a heap pointer and StackBuf(3)"
                );
                let (alpha, beta) = self.heap_addr(&args[0], &Expr::Lit(1));
                let gamma = self.ext_operand(&args[1]);
                self.emit(LOp::DerefExt { alpha, beta, gamma });
            }
            _ => return false,
        }
        true
    }

    /// `blake3(a, b, out)`: the digest of the two 256-bit operands lands in the
    /// existing 2-cell run `out` (write-once: if `out` was already written, this
    /// asserts the digest equals it). A heap `out` slice takes the digest via a
    /// fresh stack pair and two `DEREF`s after the hash, the store direction
    /// being the same instruction as the load (write-once fills the unset side).
    /// Keyword arguments set the compile-time metadata.
    fn lower_blake3(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        assert_eq!(first_kw, 3, "blake3 takes three positional arguments: (a, b, out)");
        assert!(
            args[first_kw..]
                .iter()
                .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)),
            "keyword arguments must follow the three positional blake3 arguments"
        );
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in &args[first_kw..] {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            assert!(
                kwargs.insert(key, &value[0]).is_none(),
                "duplicate blake3 keyword `{key}`"
            );
        }
        let allowed = [
            "cv",
            "counter",
            "chunk",
            "block_len",
            "flags",
            "step",
            "end",
            "root",
            "parent",
        ];
        assert!(kwargs.keys().all(|k| allowed.contains(k)), "unknown blake3 keyword");
        let customized = kwargs
            .keys()
            .any(|k| matches!(*k, "counter" | "chunk" | "flags" | "step" | "end" | "root" | "parent"));
        assert!(
            !kwargs.contains_key("cv") || customized,
            "blake3 with cv= requires step=, flags=, or another structured metadata keyword"
        );

        let a = self.blake3_input(&args[0]);
        let b = self.blake3_input(&args[1]);
        let (c, heap_out) = match self.blake3_operand(&args[2]) {
            B3Operand::Stack(o) => (o, None),
            B3Operand::Heap { ptr, lo } => (self.alloc_stack(4), Some((ptr, lo))),
        };
        self.materialize_run(c, 4);
        let cv = if let Some(value) = kwargs.get("cv") {
            self.blake3_cv(value)
        } else {
            self.default_blake3_cv()
        };
        let const_kw = |this: &Self, name: &str, default: u128| -> u128 {
            kwargs.get(name).map(|e| this.const_index(e) as u128).unwrap_or(default)
        };
        assert!(
            !(kwargs.contains_key("counter") && kwargs.contains_key("chunk")),
            "use either counter= or chunk=, not both"
        );
        let counter = if kwargs.contains_key("chunk") {
            const_kw(self, "chunk", 0)
        } else {
            const_kw(self, "counter", 0)
        };
        assert!(counter <= u64::MAX as u128, "BLAKE3 counter does not fit in u64");
        let block_len = const_kw(self, "block_len", 64);
        assert!(block_len <= 64, "BLAKE3 block_len must be at most 64");
        let step = kwargs.get("step").map(|e| self.const_index(e));
        if let Some(step) = step {
            assert!(step < 16, "BLAKE3 step must be in 0..16");
        }
        let mut flags = if kwargs.contains_key("flags") {
            const_kw(self, "flags", 0)
        } else if customized {
            if step == Some(0) { 1 } else { 0 }
        } else {
            lean_vm::blake3_flock::FLAGS as u128
        };
        if const_kw(self, "end", 0) != 0 {
            flags |= 1 << 1;
        }
        if const_kw(self, "parent", 0) != 0 {
            flags |= 1 << 2;
        }
        if const_kw(self, "root", 0) != 0 {
            flags |= 1 << 3;
        }
        assert!(flags <= u32::MAX as u128, "BLAKE3 flags do not fit in u32");
        let metadata = [F64(counter as u64), F64(block_len as u64 | (flags as u64) << 32)];
        // Each operand is two 128-bit chunks of two base words each; the opcode
        // addresses the four chunk bases independently (`blake3_input` forwards
        // the real chunk sources where it can). The digest occupies the four
        // consecutive output words based at `c`.
        self.emit(LOp::Blake3 {
            ins: [a[0], a[1], b[0], b[1]],
            cv,
            out: c,
            metadata,
        });
        // A heap `out` takes the digest through two `DEREF_128` rows; the store
        // direction is the same instruction as the load, so write-once fills
        // whichever side is unset.
        if let Some((ptr, lo)) = heap_out {
            for k in 0..2 {
                self.emit(LOp::Deref128 {
                    alpha: ptr,
                    beta: lo + 2 * k,
                    gamma: c + 2 * k,
                });
            }
        }
    }

    fn lower_return(&mut self, exprs: &[Expr]) {
        // Inlined (`@inline`): bind the return values into the caller's cells
        // and fall through: this is the body's tail return, so no jump is needed.
        if let Some(dsts) = self.inline_ret.clone() {
            // Each returned value is bound into the caller independently, exactly
            // as a `let name = <that expr>` would: a `StackBuf` or a folded
            // g-address hands over its run/pointer (alias, not copies: allocated
            // in the caller's frame, so it outlives the inline scope), a scalar is
            // copied into its dst cell. The per-slot record lets the caller's
            // `let`/tuple pick the right binding, so a fused
            // `fs, x, cur = fs_next(fs, cur)` returns a StackBuf, a scalar, and an
            // advanced cursor together.
            let mut binds = Vec::with_capacity(dsts.len());
            for (e, &d) in exprs.iter().zip(&dsts) {
                binds.push(if let Some((base, size)) = self.stack_of(e) {
                    RetBind::Stack(base, size)
                } else if let Some(ga) = self.gaddr_of(e) {
                    RetBind::Gaddr(ga)
                } else if let Expr::Call(f, args) = e
                    && self.defs.contains_key(f)
                {
                    // Tail-returning a StackBuf helper is the expression form
                    // of `tmp = helper(...); return tmp`; preserve the run.
                    self.inline_stack_ret = None;
                    let cell = self.call(f, args, 1)[0];
                    match self.inline_stack_ret.take().and_then(|v| v.into_iter().next()) {
                        Some(RetBind::Stack(base, size)) => RetBind::Stack(base, size),
                        Some(RetBind::Gaddr(ga)) => RetBind::Gaddr(ga),
                        _ => {
                            self.copy(cell, d);
                            RetBind::Scalar
                        }
                    }
                } else {
                    self.expr_into(e, d);
                    RetBind::Scalar
                });
            }
            self.inline_stack_ret = Some(binds);
            return;
        }
        if self.is_main {
            return; // a `return` in main is a no-op; main halts via the trailing sentinel jump (lower_func).
        }
        let ret_base = 2 + self.n_args;
        assert_eq!(
            exprs.len(),
            self.return_shapes.len(),
            "function returns {} values here, but its ABI declares {}",
            exprs.len(),
            self.return_shapes.len()
        );
        // Flatten logical returns into physical source words first. Plain
        // scalar expressions still lower directly into their ABI cell; stack
        // aliases expose their source offsets so adjacent triples can cross the
        // boundary with DEREF_EXT.
        enum ReturnWord {
            Expr(Expr),
            Cell(Off),
        }
        let mut words = Vec::new();
        for (e, shape) in exprs.iter().zip(self.return_shapes.clone()) {
            match shape {
                ReturnShape::Scalar => match self.copy_alias(e) {
                    Some(Alias::Cell(src)) => words.push(ReturnWord::Cell(self.word_src(src))),
                    _ => words.push(ReturnWord::Expr(e.clone())),
                },
                ReturnShape::StackBuf(size) => {
                    let (base, actual) = self
                        .stack_of(e)
                        .unwrap_or_else(|| panic!("expected a StackBuf({size}) return, got `{e:?}`"));
                    assert_eq!(actual, size, "returned StackBuf has size {actual}, expected {size}");
                    for k in 0..size {
                        words.push(ReturnWord::Cell(self.word_src(base + k)));
                    }
                }
            }
        }

        let is_run = |i: usize, words: &[ReturnWord]| {
            matches!(
                words.get(i..i + 3),
                Some([ReturnWord::Cell(a), ReturnWord::Cell(b), ReturnWord::Cell(c)])
                    if *b == *a + 1 && *c == *a + 2
            )
        };
        let mut probe = 0;
        let mut runs = 0;
        while probe < words.len() {
            if is_run(probe, &words) {
                runs += 1;
                probe += 3;
            } else {
                probe += 1;
            }
        }
        // Reading this function's own FP costs two rows. Therefore one packed
        // triple merely breaks even with three MUL-by-one copies; use the
        // packed return path when FP is already live or when at least two runs
        // amortize that setup.
        let pack_runs = self.scope.self_fp_off.is_some() || runs >= 2;
        let mut i = 0;
        while i < words.len() {
            if pack_runs && is_run(i, &words) {
                let ReturnWord::Cell(src) = words[i] else {
                    unreachable!()
                };
                let sfp = self.self_fp();
                self.emit(LOp::DerefExt {
                    alpha: sfp,
                    beta: ret_base + i as u32,
                    gamma: src,
                });
                i += 3;
                continue;
            }
            match &words[i] {
                ReturnWord::Expr(e) => self.expr_into(e, ret_base + i as u32),
                ReturnWord::Cell(src) => self.copy(*src, ret_base + i as u32),
            }
            i += 1;
        }
        let one = self.one();
        self.emit(LOp::Jump { oc: one, od: 0, of: 1 });
    }

    /// `for i in mul_range(GEN**lo, GEN**hi)` → a single tail-recursive helper, with the
    /// exit test folded into the recursion's condition (no separate branch, no
    /// is-zero gadget):
    /// ```text
    /// loop(i):
    ///     <body>
    ///     j = i·g
    ///     if j != g^hi: loop(j)   // JUMP's nonzero test on (j − g^hi)
    ///     return
    /// caller: if lo != hi: loop(g^lo)   // resolved at compile time
    /// ```
    /// Free variables of the body that are bound in the enclosing scope are
    /// captured by value as extra helper parameters (e.g. a `HeapBuf` pointer
    /// threaded through the loop).
    fn lower_for(&mut self, var: &str, lo: u64, hi: &ForBound, body: &[Stmt]) {
        let id = *self.loop_ctr;
        *self.loop_ctr += 1;
        let loop_name = format!("__loop{id}");
        if std::env::var("DBG_LOOPS").is_ok() {
            let bound = match hi {
                ForBound::Const(h) => format!("g^{lo}..g^{h}"),
                ForBound::Runtime(e) => format!("g^{lo}..{e:?}"),
            };
            eprintln!("DBG_LOOPS {loop_name} in {} for {var} in {bound}", self.fn_name);
        }
        // A runtime stop bound is evaluated once here and threaded through the
        // helper as an extra leading parameter (the exit test compares the
        // advanced counter against it each iteration).
        let bound_var = format!("__bound{id}");
        let (exit, entry_bound): (Expr, Expr) = match hi {
            ForBound::Const(hi) => (Expr::GPow(*hi as u128), Expr::GPow(*hi as u128)),
            ForBound::Runtime(e) => (Expr::Var(bound_var.clone()), e.clone()),
        };

        // Determine captures: referenced − locally-bound − the counter, kept if
        // they exist in the enclosing scope (deterministic order).
        let mut referenced = Vec::new();
        let mut bound = std::collections::HashSet::new();
        bound.insert(var.to_string());
        for s in body {
            free_vars_stmt(s, &mut referenced, &mut bound);
        }
        let mut captures = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for r in &referenced {
            if bound.contains(r) {
                continue;
            }
            if let Some(&(_, size)) = self.scope.stacks.get(r) {
                // Extension values are exactly three physical cells and have a
                // first-class call ABI, so a generated loop helper can thread
                // them across recursive iterations just like an explicit
                // `Ext` parameter. Larger scratch StackBufs remain frame-local.
                assert_eq!(
                    size, 3,
                    "StackBuf `{r}` (size {size}) cannot be captured into a `for` loop; \
                     only three-cell extension values may be captured"
                );
                if seen.insert(r.clone()) {
                    captures.push(r.clone());
                }
                continue;
            }
            if (self.scope.vars.contains_key(r) || self.scope.gaddrs.contains_key(r)) && seen.insert(r.clone()) {
                captures.push(r.clone());
            }
        }

        // The helper takes the counter, the runtime bound (if any), then the
        // captures. `cap_args` builds an argument list (a leading expression,
        // the bound, then the captures by name).
        let runtime = matches!(hi, ForBound::Runtime(_));
        let mut params = vec![var.to_string()];
        if runtime {
            params.push(bound_var.clone());
        }
        params.extend(captures.iter().cloned());
        let cap_args = |first: Expr, bound: Expr| {
            let mut a = vec![first];
            if runtime {
                a.push(bound);
            }
            a.extend(captures.iter().map(|c| Expr::Var(c.clone())));
            a
        };

        // loop(i, [bound,] caps): run the body, advance to j = i·g, and
        // tail-recurse while j != stop. The exit test is the recursive call's
        // own condition (`JUMP`'s nonzero check on j − stop): no is-zero
        // gadget, no inverse hint, and no extra call beyond the one a loop
        // iteration already makes.
        let next_var = format!("__next{id}");
        let next = Expr::Mul(Box::new(Expr::Var(var.to_string())), Box::new(Expr::Gen));
        let mut loop_body: Vec<Stmt> = body.to_vec();
        loop_body.push(Stmt::Let(next_var.clone(), next));
        loop_body.push(Stmt::CallIfNe(
            Expr::Var(next_var.clone()),
            exit,
            loop_name.clone(),
            cap_args(Expr::Var(next_var), Expr::Var(bound_var.clone())),
        ));
        loop_body.push(Stmt::Return(vec![]));
        let const_params = vec![false; params.len()];
        let mut ext_params = vec![false; params.len()];
        let capture_start = 1 + usize::from(runtime);
        for (i, name) in captures.iter().enumerate() {
            ext_params[capture_start + i] = self.scope.stacks.get(name).is_some_and(|(_, size)| *size == 3);
        }
        self.queue.push(Func {
            name: loop_name.clone(),
            params,
            const_params,
            ext_params,
            n_ret: 0,
            return_shapes: vec![],
            body: loop_body,
            inline: false,
        });

        // Enter the loop iff it runs at least once: compile-time for constant
        // bounds (an empty range compiles to nothing), a conditional call on
        // `g^lo != stop` for runtime ones.
        match hi {
            ForBound::Const(hi) => {
                if lo != *hi {
                    self.call(
                        &loop_name,
                        &cap_args(Expr::GPow(lo as u128), Expr::GPow(*hi as u128)),
                        0,
                    );
                }
            }
            ForBound::Runtime(_) => {
                let stmt = Stmt::CallIfNe(
                    Expr::GPow(lo as u128),
                    entry_bound.clone(),
                    loop_name,
                    cap_args(Expr::GPow(lo as u128), entry_bound),
                );
                self.stmt(&stmt);
            }
        }
    }
}

/// A body safe to inline: a single **tail** `return`, and no construct whose
/// lowering needs its own frame or a dispatch: a non-inline user call, a
/// runtime loop, or a match (which would reload a frame pointer that is no
/// longer the callee's). Builtins and nested `@inline` calls are fine;
/// `unroll`/`if` are compile-time / same-frame and recurse into.
fn body_inlinable(body: &[Stmt], defs: &HashMap<String, Func>) -> bool {
    matches!(body.split_last(), Some((Stmt::Return(_), rest)) if rest.iter().all(|s| stmt_inline_safe(s, defs)))
}

fn stmt_inline_safe(s: &Stmt, defs: &HashMap<String, Func>) -> bool {
    match s {
        Stmt::Let(..)
        | Stmt::Store(..)
        | Stmt::HintWitness { .. }
        | Stmt::Print { .. }
        | Stmt::AssertEq(..)
        | Stmt::AssertNe(..)
        | Stmt::AssertLt(..) => true,
        Stmt::Call(f, _) => {
            matches!(
                f.as_str(),
                "blake3" | "xor_192" | "mul_192" | "mul_192_base" | "div_192" | "deref_192"
            ) || defs.get(f).is_some_and(|d| d.inline)
        }
        Stmt::If { then, els, .. } => {
            then.iter().all(|s| stmt_inline_safe(s, defs)) && els.iter().all(|s| stmt_inline_safe(s, defs))
        }
        Stmt::Unroll { body, .. } => body.iter().all(|s| stmt_inline_safe(s, defs)),
        // Return (non-tail), For, Match, LetMatchRange, LetTuple, CallIfNe, user Call.
        _ => false,
    }
}

/// The literal `k` when `hi` is syntactically `lo + k` (either operand order):
/// the shape of a runtime slice, whose bounds cannot be evaluated at compile
/// time.
fn plus_k(lo: &Expr, hi: &Expr) -> Option<u128> {
    match hi {
        Expr::Add(a, b) => match (a.as_ref(), b.as_ref()) {
            (Expr::Lit(k), other) | (other, Expr::Lit(k)) if other == lo => Some(*k),
            _ => None,
        },
        _ => None,
    }
}

/// Collect variable references in `e` into `refs` (in source order).
fn free_vars_expr(e: &Expr, refs: &mut Vec<String>) {
    match e {
        Expr::Var(v) => refs.push(v.clone()),
        Expr::Add(a, b)
        | Expr::Mul(a, b)
        | Expr::Sub(a, b)
        | Expr::Div(a, b)
        | Expr::FieldDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Index(a, b)
        | Expr::Pow(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        Expr::Slice(a, lo, hi) => {
            free_vars_expr(a, refs);
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
        }
        Expr::Call(_, args) | Expr::ListLit(args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        Expr::HeapBufDyn(sz) | Expr::GenPow(sz) => free_vars_expr(sz, refs),
        Expr::Lit(_) | Expr::Gen | Expr::GPow(_) | Expr::HeapBuf(_) | Expr::StackBuf(_) => {}
    }
}

/// Collect references in `s` into `refs` and names it binds into `bound`.
fn free_vars_stmt(s: &Stmt, refs: &mut Vec<String>, bound: &mut std::collections::HashSet<String>) {
    match s {
        Stmt::Let(n, e) => {
            free_vars_expr(e, refs);
            bound.insert(n.clone());
        }
        Stmt::LetTuple(ns, _, args) => {
            args.iter().for_each(|a| free_vars_expr(a, refs));
            ns.iter().for_each(|n| {
                bound.insert(n.clone());
            });
        }
        Stmt::AssertEq(a, b) | Stmt::AssertNe(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        Stmt::AssertLt(e, _) => free_vars_expr(e, refs),
        Stmt::HintWitness { dest, .. } => free_vars_expr(dest, refs),
        Stmt::Print { value, .. } => free_vars_expr(value, refs),
        Stmt::If {
            lhs, rhs, then, els, ..
        } => {
            free_vars_expr(lhs, refs);
            free_vars_expr(rhs, refs);
            then.iter().for_each(|s| free_vars_stmt(s, refs, bound));
            els.iter().for_each(|s| free_vars_stmt(s, refs, bound));
        }
        Stmt::Match { x, cases } => {
            free_vars_expr(x, refs);
            cases
                .iter()
                .for_each(|c| c.iter().for_each(|s| free_vars_stmt(s, refs, bound)));
        }
        Stmt::LetMatchRange { names, x, arms } => {
            free_vars_expr(x, refs);
            arms.iter().for_each(|a| free_vars_expr(a, refs));
            names.iter().for_each(|n| {
                bound.insert(n.clone());
            });
        }
        Stmt::CallIfNe(a, b, _, args) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
            args.iter().for_each(|e| free_vars_expr(e, refs));
        }
        Stmt::Call(_, args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        Stmt::Store(arr, idx, val) => {
            free_vars_expr(arr, refs);
            free_vars_expr(idx, refs);
            free_vars_expr(val, refs);
        }
        Stmt::Return(es) => es.iter().for_each(|e| free_vars_expr(e, refs)),
        Stmt::For { var, hi, body, .. } => {
            if let ForBound::Runtime(b) = hi {
                free_vars_expr(b, refs);
            }
            bound.insert(var.clone());
            body.iter().for_each(|s| free_vars_stmt(s, refs, bound));
        }
        Stmt::Unroll { var, lo, hi, body } => {
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
            bound.insert(var.clone());
            body.iter().for_each(|s| free_vars_stmt(s, refs, bound));
        }
    }
}

/// Lower one function to its instruction list and frame size.
pub(crate) fn lower_func(
    f: &Func,
    queue: &mut Vec<Func>,
    loop_ctr: &mut usize,
    defs: &HashMap<String, Func>,
    const_arrays: &HashMap<String, Vec<F64>>,
    with_filler: bool,
) -> Lowered {
    // `main` shares the global memory image with the four public-input words,
    // so its frame starts after m[0..4]. Ordinary call frames retain their
    // two-cell retpc/retfp prefix.
    let prefix = if f.name == "main" { 4 } else { 2 };
    let mut vars = HashMap::new();
    let mut param_stacks = HashMap::new();
    let mut param_cells = 0u32;
    for ((p, &is_const), &is_ext) in f.params.iter().zip(&f.const_params).zip(&f.ext_params) {
        assert!(!is_const, "Const template reached lowering");
        if is_ext {
            param_stacks.insert(p.clone(), (prefix + param_cells, 3));
            param_cells += 3;
        } else {
            vars.insert(p.clone(), prefix + param_cells);
            param_cells += 1;
        }
    }
    // Reserve [0,1] retpc/retfp, params, then the flattened return area, then
    // locals. A StackBuf(n) return occupies n consecutive physical slots.
    let n_ret_cells: u32 = f.return_shapes.iter().map(|s| s.cells()).sum();
    let next = prefix + param_cells + n_ret_cells;
    let mut lowerer = FnLower {
        filler_start: None,
        scope: Scope {
            vars,
            stacks: param_stacks,
            ..Default::default()
        },
        next,
        n_args: param_cells,
        return_shapes: f.return_shapes.clone(),
        is_main: f.name == "main",
        fn_name: f.name.clone(),
        tail_call: false,
        code: Vec::new(),
        one_off: None,
        heap_sizes: HashMap::new(),
        inline_ret: None,
        inline_stack_ret: None,
        alias: HashMap::new(),
        pending: Vec::new(),
        inline_calls: Vec::new(),
        queue,
        loop_ctr,
        defs,
        const_arrays,
    };
    for (i, s) in f.body.iter().enumerate() {
        // Tail position: a conditional call whose only successor is a bare
        // `return`, in a function that returns nothing. The `mul_range` helper
        // ends exactly like this, so its self-call stops building an unwind
        // chain.
        lowerer.tail_call = !lowerer.is_main
            && f.n_ret == 0
            && matches!(s, Stmt::CallIfNe(..))
            && matches!(f.body.get(i + 1), Some(Stmt::Return(r)) if r.is_empty());
        lowerer.stmt(s);
    }
    let mut filler = Vec::new();
    if lowerer.is_main {
        lowerer.halt(); // main terminates at the sentinel pc, not by falling off
        if with_filler {
            // Past the halt, so no program code reaches them: the fill blocks are cycles
            // the interpreter enters on its own ([`FnLower::lower_filler_blocks`]).
            filler = lowerer.lower_filler_blocks();
        }
    } else if !matches!(f.body.last(), Some(Stmt::Return(_))) {
        // A function must never fall off its end into whatever code the
        // layout placed next: append the implicit bare return.
        lowerer.stmt(&Stmt::Return(vec![]));
    }
    let filler_start = lowerer.filler_start.unwrap_or(lowerer.code.len());
    Lowered {
        name: f.name.clone(),
        code: lowerer.code,
        frame_size: lowerer.next,
        abi_end: 2 + f.params.len() as u32 + n_ret_cells,
        filler_start,
        filler,
    }
}
