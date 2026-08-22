//! Lowering: each function AST is compiled to a sequence of intermediate
//! [`LOp`] instructions (fp-relative offsets, backpatched jump targets).

use super::*;
use crate::filler::FillerOp;
use lean_vm::cpu::filler::Block;
use std::collections::HashSet;

/// [`FnLower::specialized_body`]'s pieces: runtime param names, runtime args,
/// the `Const`-substituted body, and the callee's return arity.
type SpecializedBody = (Vec<String>, Vec<Expr>, Vec<Stmt>, usize);

/// A value equal to `pointer(base)·g^exp`, or the pure constant `g^exp` when
/// `base` is `None`. Heap-address arithmetic (`ptr·gᵏ`, and constant g-power
/// cursors such as a tweak-table index) is tracked symbolically so a later
/// access folds the whole offset into `DEREF`'s `β` immediate rather than
/// emitting a `SET`+`MUL` per step. A cursor read only as an index thus costs
/// nothing; one used as a value is materialized on demand ([`FnLower::materialize`]).
#[derive(Clone, Copy)]
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
fn field_pow(b: F192, k: u32) -> F192 {
    let mut acc = F192::ONE;
    for _ in 0..k {
        acc *= b;
    }
    acc
}

/// A deferred stack-cell store: the cell is a copy of another cell, or a zero.
/// Recorded instead of emitting the `MUL`/`SET`, and forwarded to the source at
/// each use ([`FnLower::word_src`]), so `BLAKE2s`, which addresses its four
/// two-cell input chunks independently, reads them in place without assembling
/// copies.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Alias {
    Cell(Off),
    /// A compile-time constant: forwarded at its uses to the pooled cell
    /// holding that value (`const_cell`), so a constant stored into a
    /// `blake2s` operand cell (the `obs`/`squeeze` tag words, padding
    /// halves) costs ONE `SET` per distinct value per function, not one
    /// per store. A zero constant routes through the zero pool.
    Const(F192),
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
    FConst(F192),
}

/// How an inlined tail return binds in the caller: a `StackBuf` run and a folded
/// g-address alias at zero copies, while anything else (a plain scalar, or a real
/// call, which records no [`RetBind`]) takes the destination cell it wrote.
fn ret_binding(b: Option<RetBind>, dst: Off) -> Binding {
    match b {
        Some(RetBind::Stack(base, size)) => Binding::Stack(base, size),
        Some(RetBind::Gaddr(ga)) => Binding::Gaddr(ga),
        _ => Binding::Scalar(dst),
    }
}

/// Everything a runtime branch may not have executed: the name bindings, plus
/// the lazily materialized cells whose `SET` sits wherever it was first needed.
/// [`FnLower::scoped`] saves one of these and restores it at the join, so a
/// cell written on one path is never trusted on another.
#[derive(Clone, Default)]
struct Scope {
    vars: HashMap<String, Off>,
    /// `StackBuf` bindings: name → (base offset, size). The `size` cells
    /// `base..base+size` are consecutive frame cells (so a size-2 one, or a
    /// 2-cell slice of a larger one, is a direct `blake2s` operand). Kept
    /// separate from `vars` since a stack value is a run of cells, not a
    /// single scalar.
    stacks: HashMap<String, (Off, u32)>,
    /// Names bound to compile-time integer expressions (`x = 10`), usable in
    /// index positions and instruction metadata. Cleared on rebind to anything
    /// else. Index users narrow to `u32`; metadata may consume a wider value.
    /// Integer arithmetic is distinct from the field arithmetic the same syntax
    /// means in a scalar expression.
    consts: HashMap<String, u128>,
    /// Variables bound to a symbolic g-address ([`GAddr`]): index cursors and
    /// shifted pointers, kept virtual so their offsets fold into `DEREF`'s `β`.
    gaddrs: HashMap<String, GAddr>,
    /// Variables bound to a compile-time *field* constant that isn't a g-power
    /// (e.g. a running weight `CHAIN_LENGTH^i`). Kept virtual: folded through
    /// constant field arithmetic and materialized (one `SET`) only when used.
    fconsts: HashMap<String, F192>,
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
    const_cells: HashMap<[u64; 3], Off>,
    /// A cached frame cell holding `0` (for forwarded zero words), set lazily.
    zero_off: Option<Off>,
    /// Two consecutive frame cells holding the standard BLAKE2s IV, emitted
    /// lazily at the first dominating default-IV compression in this
    /// control-flow scope.
    blake2s_iv: Option<Off>,
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
    /// Stack cells something already gives a real value to: an emitted
    /// instruction's destination, a `BLAKE2s` output, or a hint destination. A
    /// store into one of these cannot defer as an [`Alias`], because the store is
    /// then the write-once equality assertion of `zkDSL.md` §Memory rather than an
    /// assembly copy, and an alias would drop it. Accumulated monotonically, and
    /// deliberately NOT restored across a branch: if either arm gives the cell a
    /// value, a later store to it is an assertion on whichever arm ran.
    phys: HashSet<Off>,
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
    const_arrays: &'a HashMap<String, Vec<F192>>,
}

impl FnLower<'_> {
    fn fresh(&mut self) -> Off {
        let o = self.next;
        self.next += 1;
        o
    }

    fn emit(&mut self, op: LOp) {
        // Record the stack cells this instruction gives a real value to, so
        // [`Self::stack_store`] will not defer an alias onto one of them: the alias
        // would win every later read and the store's write-once equality assertion,
        // which is what `zkDSL.md` §Memory promises a second write is, would vanish.
        // `Deref`'s local cell counts, since the interpreter fills whichever side of
        // the equality it names is still unset.
        match op {
            LOp::Set { o, .. } => self.phys.insert(o),
            LOp::Xor { c, .. } | LOp::Mul { c, .. } => self.phys.insert(c),
            LOp::Deref { gamma, .. } => self.phys.insert(gamma),
            LOp::Blake2s { c, .. } => {
                self.phys.insert(c);
                self.phys.insert(c + 1)
            }
            LOp::Jump { .. } => false,
        };
        let hints = std::mem::take(&mut self.pending);
        self.code.push(LInstr { op, hints });
    }

    /// Prepare a stack run that a consumer is about to name by its *physical*
    /// cells: a `BLAKE2s` output, or a hint destination. Those consumers do not go
    /// through [`Self::word_src`], so a cell still carrying a deferred alias would
    /// have the consumer's write land where nothing reads it, and the equality
    /// assertion the source wrote would be gone. Materializing the alias first puts
    /// a real value in the cell, which is what turns the consumer's write back into
    /// that assertion; marking the run `phys` covers the other order, where the
    /// store comes after the consumer.
    fn materialize_run(&mut self, base: Off, len: u32) {
        for o in base..base + len {
            if self.alias.contains_key(&o) {
                let src = self.word_src(o);
                self.alias.remove(&o);
                self.copy(src, o);
            }
            self.phys.insert(o);
        }
    }

    fn set(&mut self, o: Off, k: KVal) {
        self.emit(LOp::Set { o, k });
    }

    fn set_const(&mut self, o: Off, v: F192) {
        self.set(o, KVal::Const(v));
    }

    fn deref(&mut self, alpha: Off, beta: u32, gamma: Off, mode: DerefMode) {
        self.emit(LOp::Deref {
            alpha,
            beta,
            gamma,
            mode,
        });
    }

    /// A no-op instruction to hang a pending hint on, so it fires exactly here
    /// instead of drifting onto whatever is emitted next (which may sit past a
    /// branch join, or on a path this hint does not belong to).
    fn anchor(&mut self) {
        let o = self.fresh();
        self.set_const(o, F192::ZERO);
    }

    /// A top-level constant name is reserved (`zkDSL.md` §Global constants: "do not
    /// reuse it as a parameter or local name"). A scalar constant enforces that by
    /// construction, since the parser substitutes its value textually and a
    /// shadowing binding becomes a literal, which fails loudly. A constant ARRAY is
    /// carried to lowering instead, and [`Self::const_array_elem`] resolves
    /// `NAME[i]` against it without consulting the scope, while `expr` folds
    /// constants before its index arm could see the local. So a colliding local
    /// silently has its compile-time-indexed reads folded to baked literals,
    /// including reads of a `hint_witness` destination, whose asserts and range
    /// checks then run on the constant instead of on the witness. Reject the
    /// collision rather than pick a winner.
    fn check_not_reserved(&self, name: &str) {
        assert!(
            !self.const_arrays.contains_key(name),
            "`{name}` is a top-level constant array, so the name is reserved: rename the local \
             or parameter (zkDSL.md §Global constants)"
        );
    }

    /// Bind `name` to `b`, dropping whatever the other three maps held for it:
    /// they are consulted independently, so a stale binding of another kind
    /// would shadow this one. `consts` is deliberately NOT touched, since a
    /// name can keep its compile-time index role across such a rebind; callers
    /// that must drop it do so themselves.
    fn rebind(&mut self, name: &str, b: Binding) {
        self.check_not_reserved(name);
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
        self.set_const(o, F192::ONE);
        self.one_off = Some(o);
        o
    }

    /// A frame cell holding `v`, shared by every dominated use in the current scope.
    fn const_cell(&mut self, v: F192) -> Off {
        if v == F192::ONE {
            return self.one();
        }
        let key = [v.c0, v.c1, v.c2];
        if let Some(&o) = self.scope.const_cells.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.set_const(o, v);
        self.scope.const_cells.insert(key, o);
        o
    }

    /// A frame cell holding `0`, set lazily once: the source for forwarded zero
    /// words (a `BLAKE2s` padding half).
    fn zero(&mut self) -> Off {
        if let Some(o) = self.scope.zero_off {
            return o;
        }
        let o = self.fresh();
        self.set_const(o, F192::ZERO);
        self.scope.zero_off = Some(o);
        o
    }

    fn default_blake2s_cv(&mut self) -> Off {
        if let Some(o) = self.scope.blake2s_iv {
            return o;
        }
        let o = self.alloc_stack(2);
        for (k, value) in lean_vm::blake2s_flock::IV_CELLS.into_iter().enumerate() {
            self.set_const(o + k as u32, value);
            self.scope
                .const_cells
                .insert([value.c0, value.c1, value.c2], o + k as u32);
        }
        self.scope.blake2s_iv = Some(o);
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
            Expr::Index(arr, idx) => {
                let (base, _) = self.stack_of(arr)?;
                Some(Alias::Cell(base + self.try_const_index(idx)?))
            }
            _ => self.try_field_const(val).map(Alias::Const),
        }
    }

    /// Write `val` into the stack cell `dst`. A plain copy or a constant is
    /// deferred as an [`Alias`] and forwarded at its uses (write-once, so the
    /// source cell keeps its value): the assembling `MUL`/`SET` is never emitted.
    fn stack_store(&mut self, dst: Off, val: &Expr) {
        // Deferring is only sound while nothing else has given `dst` a value. Once
        // something has, the store IS the write-once equality assertion of
        // `zkDSL.md` §Memory, so it has to be emitted: an alias would silently
        // redirect every later read to the source and drop the assertion. This is
        // what makes `s[k] = <checked value>` pin a hint, and what makes a
        // pre-written `blake2s` output assert the digest.
        let aliased = self.alias.contains_key(&dst);
        if !aliased
            && !self.phys.contains(&dst)
            && let Some(a) = self.copy_alias(val)
        {
            self.alias.insert(dst, a);
            return;
        }
        if aliased {
            // Give the cell the value it already stood for, so the store below is a
            // second write of that cell and therefore the assertion. Without this the
            // second alias would simply replace the first and the two values would
            // never meet.
            let src = self.word_src(dst);
            self.alias.remove(&dst);
            self.copy(src, dst);
        }
        self.expr_into(val, dst);
    }

    /// Terminate `main`: jump to the halt sentinel `g^{B-1}` with `fp = g^0`.
    /// The cell holding `1` doubles as the (nonzero) jump condition and the new
    /// frame pointer `g^0`; the dest cell holds `g^{B-1}` (doc §sec:e2e, final state).
    fn halt(&mut self) {
        let one = self.one();
        let dest = self.fresh();
        self.set(dest, KVal::EndSentinel);
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
                            k: KVal::Const(F192::ZERO),
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
                        FillerOp::Blake2s => LOp::Blake2s {
                            ins: [fr::DIGEST + 2, fr::DIGEST + 3, fr::DIGEST + 4, fr::DIGEST + 5],
                            cv: fr::SCRATCH,
                            c: fr::DIGEST,
                            metadata: F192::ZERO,
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
    /// `DEREF`-fp writes it there and a `DEREF`-cell copies it back. In `main`, `fp = g^0 = 1`, which is
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
        self.deref(q, 0, 0, DerefMode::Fp); // m[q] := fp
        let o = self.fresh();
        self.deref(q, 0, o, DerefMode::Cell); // m[fp·g^o] := m[q]
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
    /// (`one`, `self_fp`, range-check bounds, default BLAKE2s IV) revert
    /// afterwards, since a cell whose `SET` sits inside a conditionally-executed
    /// region must not be trusted outside it.
    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        let branch_start = self.next;
        let saved_aliases = self.alias.clone();
        let saved = self.scope.clone();
        f(self);
        // A deferred store into a buffer declared outside the branch must be
        // materialized on that path before the branch-local aliases are dropped.
        let mut branch_outputs: Vec<Off> = self
            .alias
            .iter()
            .filter_map(|(&dst, alias)| (dst < branch_start && saved_aliases.get(&dst) != Some(alias)).then_some(dst))
            .collect();
        // Sorted, because the emitted copies must not depend on `HashMap` iteration
        // order: the bytecode digest leads the Fiat--Shamir transcript, so two builds
        // of one source have to be the same program.
        branch_outputs.sort_unstable();
        for dst in branch_outputs {
            let src = self.word_src(dst);
            self.alias.remove(&dst);
            self.copy(src, dst);
        }
        // A hint pending at the end of a branch (e.g. a trailing
        // `hint_witness`) must not attach to whatever instruction follows the
        // join, which would fire it unconditionally.
        if !self.pending.is_empty() {
            self.anchor();
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

    /// `match log(x)` through a two-instruction trampoline slot per arm. The caller must range-check `x` before dispatch.
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
            let specialized: Vec<(String, Vec<Expr>)> = arms
                .iter()
                .map(|a| {
                    let Expr::Call(f, cargs) = a else { unreachable!() };
                    self.specialize(f, cargs)
                })
                .collect();
            let rt0 = &specialized[0].1;
            if specialized.iter().all(|(_, rt)| rt == rt0) {
                let callees: Vec<String> = specialized.iter().map(|(c, _)| c.clone()).collect();
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
                                    // `copy` reads its source raw, so resolve the arm's
                                    // deferred alias first (as `take_inline_ret_cell` does).
                                    let src = s.word_src(base);
                                    s.copy(src, rc);
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
        // The join below reads one return cell per bound name, so every callee has
        // to declare exactly that many. Unchecked, a name past a callee's arity
        // `DEREF`s a frame offset nothing on that path writes, and since the shared
        // frame is sized to the LARGEST callee the offset exists: the surplus name
        // binds a prover-chosen word. The non-fused path enforces this
        // ([`Self::call_into`]), so leaving it out here means one source is rejected
        // by one lowering of `match_range` and silently miscompiled by the other.
        for callee in callees {
            let Some(shapes) = self.return_shapes_of(callee) else {
                continue;
            };
            assert_eq!(
                shapes.len(),
                names.len(),
                "`{callee}` returns {} values, dispatched call binds {}",
                shapes.len(),
                names.len()
            );
            assert!(
                shapes.iter().all(|s| *s == ReturnShape::Scalar),
                "`{callee}`: a multi-cell StackBuf return cannot cross a dispatched join"
            );
        }
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
        for (i, &ao) in arg_offs.iter().enumerate() {
            self.deref(nfp, 2 + i as u32, ao, DerefMode::Cell);
        }
        self.deref(nfp, 1, 0, DerefMode::Fp); // retfp
        let join_cell = self.fresh();
        let join_set = self.code.len();
        self.set(join_cell, KVal::Local(0)); // patched: the join pc
        self.deref(nfp, 0, join_cell, DerefMode::Cell); // retpc = join

        let kset = self.emit_dispatch(xo, one, sfp);

        // Trampoline: slot j enters `callees[j]` with fp = nfp; the callee's own
        // `return` jumps to retpc (the join) in the caller frame.
        self.patch_local(kset, self.code.len());
        self.emit_slots(callees.len(), one, nfp, |j| KVal::Entry(callees[j].clone()));

        // Join: read the return values (written by whichever callee ran).
        self.patch_local(join_set, self.code.len());
        for (i, &r) in rcells.iter().enumerate() {
            self.deref(nfp, 2 + n_args + i as u32, r, DerefMode::Cell);
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
        self.set(kcell, KVal::Local(0)); // patched: table base T
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
            self.set(c, k(j));
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
        self.set(join, KVal::Local(0)); // patched: the join
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

    /// Lower `if` / `else`, arranging the blocks so the nonzero `XOR` result jumps to the correct arm.
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
        self.set(bdest, KVal::Local(0)); // patched: start of B
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
            self.set(edest, KVal::Local(0)); // patched: the join
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

    /// `assert a != b`: `XOR` for `x = a + b`, a hinted `inv = x⁻¹`, then
    /// `MUL p = x·inv` and `SET p = 1`, the write-once conflict being the
    /// assertion (as for `assert a == b`). Sound because `x = 0` forces `p = 0`
    /// whatever the hint, and `p` cannot then be `1`. Three rows and no `JUMP`,
    /// against the five (`XOR`, two `SET`, two `JUMP`) a branch to the poison pc
    /// used to cost. A compile-time-equal pair is a hard compile error.
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
        let inv = self.fresh();
        self.pending.push(Hint::Resolved(RHint::Inverse { value: x, dst: inv }));
        let p = self.fresh();
        self.emit(LOp::Mul { a: x, b: inv, c: p });
        self.set_const(p, F192::ONE);
    }

    /// The frame cell holding `g^{k-1}`, the range-check product target, set
    /// lazily once per distinct bound `k` and shared by that bound's checks.
    fn bound_cell(&mut self, k: u64) -> Off {
        if let Some(&o) = self.scope.bounds.get(&k) {
            return o;
        }
        let o = self.fresh();
        self.set_const(o, g_pow_u128((k - 1) as u128).into());
        self.scope.bounds.insert(k, o);
        o
    }

    /// Resolve an expression naming a run of consecutive cells: a whole
    /// `StackBuf`, a `StackBuf` slice, a `HeapBuf` slice with compile-time
    /// bounds, or a runtime-start heap slice `buf[i:i + k]` (whose length is
    /// the only thing its bounds reveal). Heap runs fold the buffer's symbolic
    /// shift and the slice start into the pointer offset.
    fn cell_run(&mut self, e: &Expr) -> CellRun {
        match e {
            Expr::Var(_) => {
                let (base, len) = self
                    .stack_of(e)
                    .expect("only a StackBuf names a cell run unsliced; slice a HeapBuf: `buf[lo:lo + k]`");
                CellRun::Stack { base, len }
            }
            Expr::Slice(arr, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                // Compile-time bounds: integer cell indexes `lo..hi` (frame
                // offsets for a stack, g-power exponents for the heap).
                (Some(lo), Some(hi)) => {
                    assert!(lo < hi, "empty slice {lo}:{hi}");
                    let len = hi - lo;
                    if let Some((base, size)) = self.stack_of(arr) {
                        assert!(hi <= size, "slice {lo}:{hi} out of bounds (StackBuf size {size})");
                        CellRun::Stack { base: base + lo, len }
                    } else {
                        self.check_heap_bound(arr, lo as u128, len as u128);
                        let (ptr, lo) = self.heap_base(arr, lo as u128);
                        CellRun::Heap { ptr, lo, len }
                    }
                }
                // Runtime start (heap only): `buf[i:i + k]` with a runtime
                // g-power index `i` names the cells `buf·i·g^j`, j < k. The
                // `hi` bound cannot be evaluated, only shape-checked against
                // `lo`. One MUL folds `i` into the pointer.
                _ => {
                    assert!(
                        self.stack_of(arr).is_none(),
                        "a StackBuf slice needs compile-time bounds (frame offsets are baked into the bytecode)"
                    );
                    let k = plus_k(lo, hi)
                        .unwrap_or_else(|| panic!("a runtime slice must be `buf[i:i + k]`, got `{lo:?}:{hi:?}`"));
                    let len = u32::try_from(k).expect("slice length overflows u32");
                    assert!(len > 0, "empty slice");
                    let (ptr, lo) = self.heap_addr(arr, lo);
                    CellRun::Heap { ptr, lo, len }
                }
            },
            other => panic!("expected a StackBuf, a StackBuf slice, or a HeapBuf slice, got `{other:?}`"),
        }
    }

    /// `hint_witness(dest, "name")`: resolve `dest` to a run of cells and
    /// queue the witness-fill hint (no instructions: the values are written
    /// by the runner before the next instruction executes, unconstrained).
    fn lower_hint_witness(&mut self, dest: &Expr, name: &str) {
        let name = name.to_string();
        let hint = match self.cell_run(dest) {
            CellRun::Stack { base, len } => {
                self.materialize_run(base, len);
                RHint::WitnessStack { name, base, len }
            }
            CellRun::Heap { ptr, lo, len } => RHint::WitnessHeap { name, ptr, lo, len },
        };
        self.pending.push(Hint::Resolved(hint));
    }

    /// `assert log x < log GEN ** k`: the 3-cycle range check *in the
    /// exponent* (leanVM's DEREF trick, see
    /// `doc/leanvm/body/10-isa-programming.tex` §sec:prog-range-checks, transported to g-powers). With `x = g^e`:
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
    ///
    /// A [`LtBound::Runtime`] bound `Y = g^k` reaches the same gadget through one
    /// extra `MUL` for `g^{k-1} = Y·g^{-1}`, which the runner has written before
    /// the range-check `MUL` runs, so the complement is still back-solved rather
    /// than hinted. The `k ≤ 2^MIN_LOG_MEM` obligation moves to the program.
    fn lower_assert_lt(&mut self, e: &Expr, bound: &LtBound) {
        let kcell = match bound {
            LtBound::Const(k) => {
                assert!(*k >= 1, "range-check bound GEN ** 0 names the empty set");
                assert!(
                    *k <= 1 << lean_vm::cpu::MIN_LOG_MEM,
                    "range-check bound GEN ** {k} exceeds 2^{} (the minimum memory size)",
                    lean_vm::cpu::MIN_LOG_MEM,
                );
                self.bound_cell(*k)
            }
            LtBound::Runtime(b) => {
                // A bound that folds only after substitution (`GEN ** i` inside an
                // `unroll`) reaches here rather than the arm above, and would then
                // skip the `k <= 2^MIN_LOG_MEM` cap entirely. Reject it: the author
                // wrote a compile-time bound and should get the compile-time check.
                assert!(
                    self.try_field_const(b).is_none(),
                    "a compile-time range-check bound must be written as `log GEN ** k` or an \
                     integer, so that the 2^{} cap applies",
                    lean_vm::cpu::MIN_LOG_MEM,
                );
                let bcell = self.expr(b);
                let inv = self.const_cell(F192::new(primitives::field::G.inv().0, 0, 0));
                let c = self.fresh();
                self.emit(LOp::Mul { a: bcell, b: inv, c });
                c
            }
        };
        let x = self.expr(e);
        let y = self.fresh(); // the complement g^{k-1-e}, back-solved by the MUL
        let t1 = self.fresh(); // DEREF targets: unconstrained touch cells
        let t2 = self.fresh();
        self.deref(x, 0, t1, DerefMode::Cell);
        self.emit(LOp::Mul { a: x, b: y, c: kcell });
        self.deref(y, 0, t2, DerefMode::Cell);
    }

    fn expr(&mut self, e: &Expr) -> Off {
        // A wholly compile-time expression, whatever its shape, is one pooled
        // `SET` ([`Self::const_cell`]): folded here once rather than arm by arm.
        if let Some(v) = self.try_field_const(e) {
            return self.const_cell(v);
        }
        match e {
            Expr::Lit(_) | Expr::Gen | Expr::GPow(_) => unreachable!("a literal folds above"),
            // Not folded above, so its exponent is not a compile-time integer,
            // which `gpow_exp` reports.
            Expr::GenPow(e) => {
                let k = self.gpow_exp(e);
                self.const_cell(g_pow_u128(k).into())
            }
            Expr::Pow(b, e) => self.pow_expr(b, e),
            Expr::Var(v) => {
                if self.scope.stacks.contains_key(v) {
                    panic!("StackBuf `{v}` used as a scalar; index it (`{v}[k]`) or pass it to blake2s");
                }
                if let Some(&ga) = self.scope.gaddrs.get(v) {
                    return self.materialize(ga);
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
            // A well-formed one folds above, so this is a malformed call.
            Expr::Call(f, _) if f == "f192" => panic!("f192 needs three literal u64 limbs"),
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
                let d = self.call(f, args, 1)[0];
                self.take_inline_ret_cell(d)
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
                self.deref(base, beta, dst, DerefMode::Cell);
                dst
            }
            Expr::Sub(..) | Expr::Div(..) | Expr::Mod(..) => {
                panic!(
                    "`-`, `//`, `%` are compile-time only (field subtraction is `+`); use them in an index, a bound, or a `Const` argument, got `{e:?}`"
                )
            }
            Expr::Slice(..) => panic!("a slice is not a scalar; it is only a blake2s operand"),
            Expr::ListLit(..) => panic!("a list literal must be bound to a name: `x = [a, b]`"),
        }
    }

    /// Allocate `n` *consecutive* fresh frame cells (a stack run), returning the
    /// base. Nothing else may `fresh()` between them, so they stay adjacent.
    fn alloc_stack(&mut self, n: u32) -> Off {
        let base = self.next;
        self.next += n;
        base
    }

    /// If `e` names a `StackBuf` variable, its `(base, size)`.
    fn stack_of(&self, e: &Expr) -> Option<(Off, u32)> {
        match e {
            Expr::Var(v) => self.scope.stacks.get(v).copied(),
            _ => None,
        }
    }

    /// A compile-time integer expression. `None` means either a runtime value
    /// or arithmetic outside the source language's `u128` literal domain.
    fn try_const_int(&self, e: &Expr) -> Option<u128> {
        match e {
            Expr::Lit(k) => Some(*k),
            Expr::Var(v) => self.scope.consts.get(v).copied(),
            Expr::Add(a, b) => self.try_const_int(a)?.checked_add(self.try_const_int(b)?),
            Expr::Sub(a, b) => self.try_const_int(a)?.checked_sub(self.try_const_int(b)?),
            Expr::Mul(a, b) => self.try_const_int(a)?.checked_mul(self.try_const_int(b)?),
            Expr::Div(a, b) => {
                let d = self.try_const_int(b)?;
                assert!(d != 0, "compile-time division by zero");
                Some(self.try_const_int(a)? / d)
            }
            Expr::Mod(a, b) => {
                let d = self.try_const_int(b)?;
                assert!(d != 0, "compile-time modulo by zero");
                Some(self.try_const_int(a)? % d)
            }
            Expr::Index(..) => self
                .const_array_elem(e)
                .and_then(|value| (value.c2 == 0).then_some(value.c0 as u128 | ((value.c1 as u128) << 64))),
            Expr::Call(..) => self.const_len(e).map(|n| n as u128),
            Expr::Pow(b, e) => self
                .try_const_int(b)?
                .checked_pow(u32::try_from(self.try_const_int(e)?).ok()?),
            _ => None,
        }
    }

    /// A compile-time integer index. The general integer evaluator is narrowed
    /// here so stack offsets, bounds, and immediate exponents remain `u32`.
    fn try_const_index(&self, idx: &Expr) -> Option<u32> {
        u32::try_from(self.try_const_int(idx)?).ok()
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
            self.set_const(o, F192::ONE);
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
    fn const_array_elem(&self, e: &Expr) -> Option<F192> {
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
        if self.try_field_const(a) == Some(F192::ZERO) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ZERO)).then_some(a)
    }

    /// The surviving operand of `a * b` when the other is a compile-time one, a
    /// no-op multiply. Kills the `acc = GEN ** 0` (= 1) accumulator seed's first
    /// `1 * f` in every product loop.
    fn mul_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F192::ONE) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ONE)).then_some(a)
    }

    /// The field value of `e` when it is a trivial compile-time constant (a
    /// literal, a literal-bound name, or `GEN ** 0`), for the `x*1`/`x+0`
    /// arithmetic identities and the `== 0` test of [`Self::lower_if`].
    fn try_lit(&self, e: &Expr) -> Option<u64> {
        match e {
            Expr::Lit(n) => u64::try_from(*n).ok(),
            Expr::Var(v) => self.scope.consts.get(v).and_then(|&n| u64::try_from(n).ok()),
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
            Expr::Var(v) => pow2(*self.scope.consts.get(v)?).and_then(cap),
            Expr::Gen => Some(1),
            Expr::GPow(k) => cap(u32::try_from(*k).ok()?),
            Expr::GenPow(e) => cap(self.try_const_index(e)?),
            Expr::Mul(a, b) => cap(self.try_gpow_index(a)?.checked_add(self.try_gpow_index(b)?)?),
            _ => None,
        }
    }

    /// Resolve a `blake2s` operand: a [`Self::cell_run`] pinned to exactly 2
    /// cells, a 256-bit value being two 128-bit cells. Stack operands are used
    /// in place; heap operands must be bridged through the stack, since
    /// `BLAKE2s` addresses only frame cells (see [`Self::blake2s_input`]).
    fn blake2s_operand(&mut self, e: &Expr) -> CellRun {
        let run = self.cell_run(e);
        assert!(
            run.cells() == 2,
            "a blake2s operand must span exactly 2 cells (two 128-bit words); slice a larger buffer: `buf[lo:lo + 2]`"
        );
        run
    }

    /// A `blake2s` *input* operand as its two independently-addressed 128-bit
    /// chunk bases (each chunk is ONE 128-bit cell): stack runs in place; a heap
    /// slice is pulled into a fresh stack pair first, one `DEREF` per cell
    /// (`m[ptr·g^{lo+k}] == m[fp+t+k]`, the `β` immediate doing the pointer
    /// offset). The heap cells must already be written.
    fn blake2s_input(&mut self, e: &Expr) -> [Off; 2] {
        match self.blake2s_operand(e) {
            // A stack operand: the two chunk cells are `o, o+1`; forward each
            // cell's real source where known (a copy or a zero), so a hash of
            // non-adjacent values needs no assembling copies.
            CellRun::Stack { base, .. } => [self.word_src(base), self.word_src(base + 1)],
            CellRun::Heap { ptr, lo, .. } => {
                let t = self.alloc_stack(2);
                for k in 0..2 {
                    self.deref(ptr, lo + k, t + k, DerefMode::Cell);
                }
                [t, t + 1]
            }
        }
    }

    /// A BLAKE2s chaining value must occupy two consecutive frame cells because
    /// the opcode carries one base offset for both words. Preserve a genuine
    /// consecutive pair, including a heap pair already bridged by
    /// [`Self::blake2s_input`]; if deferred copy forwarding exposes two
    /// non-adjacent sources, materialize them into a fresh consecutive run.
    fn blake2s_cv(&mut self, e: &Expr) -> Off {
        let pair = self.blake2s_input(e);
        if pair[1] == pair[0] + 1 {
            return pair[0];
        }
        let cv = self.alloc_stack(2);
        self.copy(pair[0], cv);
        self.copy(pair[1], cv + 1);
        cv
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
        // A wholly compile-time expression (a literal, a constant-array element,
        // constant arithmetic) is one `SET` into `dst`, not a heap read.
        if let Some(v) = self.try_field_const(e) {
            self.set_const(dst, v);
            return;
        }
        match e {
            // Heap read straight into dst (a stack read falls through to the copy).
            Expr::Index(arr, idx) if self.stack_of(arr).is_none() => {
                let (base, beta) = self.heap_addr(arr, idx);
                self.deref(base, beta, dst, DerefMode::Cell);
            }
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
        // `buf[r * GEN ** k]` (either factor order): beta takes the constant,
        // the pointer MUL takes only the runtime factor `r`.
        if let Expr::Mul(a, b) = idx {
            for (c, r) in [(a, b), (b, a)] {
                if let Some(k) = self.try_gpow_index(c) {
                    let (la, lr) = (self.expr(arr), self.expr(r));
                    let ptr = self.fresh();
                    self.emit(LOp::Mul { a: la, b: lr, c: ptr });
                    return (ptr, k);
                }
            }
        }
        let (la, li) = (self.expr(arr), self.expr(idx));
        let ptr = self.fresh();
        self.emit(LOp::Mul { a: la, b: li, c: ptr });
        (ptr, 0)
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
    fn try_field_const(&self, e: &Expr) -> Option<F192> {
        match e {
            // A source literal fills the low 128 bits; g-powers/addresses embed in K.
            Expr::Lit(n) => Some(lit_field(*n)),
            Expr::Gen => Some(g_pow(1).into()),
            Expr::GPow(k) => Some(g_pow_u128(*k).into()),
            Expr::GenPow(e) => Some(g_pow_u128(self.try_const_index(e)? as u128).into()),
            Expr::Var(v) => self
                .scope
                .fconsts
                .get(v)
                .copied()
                .or_else(|| match self.scope.gaddrs.get(v) {
                    Some(GAddr { base: None, exp }) => Some(g_pow_u128(*exp).into()),
                    _ => None,
                }),
            Expr::Add(a, b) => Some(self.try_field_const(a)? + self.try_field_const(b)?),
            Expr::Mul(a, b) => Some(self.try_field_const(a)? * self.try_field_const(b)?),
            // A constant-array element `NAME[i]` as a field value, or `len(NAME)`.
            Expr::Index(..) => self.const_array_elem(e),
            Expr::Call(f, args) if f == "f192" && args.len() == 3 => {
                let limb = |i: usize| match &args[i] {
                    Expr::Lit(n) => u64::try_from(*n).ok(),
                    _ => None,
                };
                Some(F192::new(limb(0)?, limb(1)?, limb(2)?))
            }
            Expr::Call(..) => self.const_len(e).map(|n| F192::new(n as u64, 0, 0)),
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
                self.set_const(k, g_pow_u128(exp).into());
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
        let a = self.expr(arr);
        if extra == 0 {
            return (a, 0);
        }
        let k = self.fresh();
        self.set_const(k, g_pow_u128(extra).into());
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
                "heap index folds to the field constant {:#x}:{:#x}, not a g-power: heap cell k is \
                 addressed as `buf[GEN ** k]` (did an integer index leak in from a StackBuf conversion?)",
                c.c1, c.c0
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
                    "a multi-cell StackBuf return needs a `let` binding, not an expression use"
                );
                // Through `word_src`, like every other read of a stack cell: the body may
                // have filled this cell with a deferred copy or constant, which emits no
                // instruction, and the raw cell would then be one no instruction writes.
                // The `let` consumer follows the alias by taking a `Binding::Stack`
                // ([`ret_binding`]), and an expression use has to agree with it.
                self.word_src(base)
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
            callee != "blake2s",
            "blake2s is a statement: `blake2s(a, b, out)` writes the digest into the 2-cell stack run `out`"
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
        assert!(
            callee != "blake2s",
            "blake2s is a statement, not a value-returning call"
        );
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
            } else if let Some(ga) = self.gaddr_of(a) {
                Bind::Addr(ga)
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
            self.check_not_reserved(&p);
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
    /// arguments (literals, `GEN ** k`, or literal-bound names) substitute into
    /// a copy of the callee, queued once per distinct constant tuple and named
    /// `callee__L5_G3`-style, and only the runtime arguments remain.
    /// A callee's declared return shapes, looked up wherever it lives: an
    /// ordinary definition sits in `defs`, while a `Const` specialization is
    /// registered by [`Self::specialize`] in the queue under its mangled name and
    /// never reaches `defs`. A dispatched `match_range` names specializations, so a
    /// check that consults only `defs` silently passes on every one of them.
    fn return_shapes_of(&self, callee: &str) -> Option<Vec<ReturnShape>> {
        self.defs.get(callee).map(|d| d.return_shapes.clone()).or_else(|| {
            self.queue
                .iter()
                .find(|f| f.name == callee)
                .map(|f| f.return_shapes.clone())
        })
    }

    fn specialize(&mut self, callee: &str, args: &[Expr]) -> (String, Vec<Expr>) {
        let defs: &HashMap<String, Func> = self.defs;
        let Some(def) = defs.get(callee) else {
            return (callee.to_string(), args.to_vec()); // loop helpers, unknown names
        };
        if !def.const_params.contains(&true) {
            return (callee.to_string(), args.to_vec());
        }
        assert_eq!(args.len(), def.params.len(), "call to `{callee}`: wrong arity");
        let mut tag = String::new();
        let (mut rt_params, mut rt_args, mut substs) = (Vec::new(), Vec::new(), Vec::new());
        for ((p, &is_const), a) in def.params.iter().zip(&def.const_params).zip(args) {
            if !is_const {
                rt_params.push(p.clone());
                rt_args.push(a.clone());
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
                n_ret: def.n_ret,
                return_shapes: def.return_shapes.clone(),
                body,
                inline: false,
            });
        }
        (name, rt_args)
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
        let (callee, args) = self.specialize(callee, args);
        let (callee, args) = (callee.as_str(), args.as_slice());
        let arg_offs: Vec<Off> = args.iter().map(|a| self.expr(a)).collect();
        let nfp = self.fresh();
        let entry = self.fresh();
        // Resolve the jump condition up front: `self.one()` may emit a `SET`, and
        // nothing may sit between the retpc `DEREF` and the `JUMP` (the `g²·pc`
        // return target assumes the `JUMP` is exactly one instruction later).
        let oc = cond.unwrap_or_else(|| self.one());
        self.set(entry, KVal::Entry(callee.to_string()));

        // The frame-pointer hint fires before the first DEREF that reads `nfp`.
        self.pending.push(Hint::AllocFrame {
            ptr: nfp,
            callee: callee.to_string(),
        });
        for (i, &ao) in arg_offs.iter().enumerate() {
            self.deref(nfp, 2 + i as u32, ao, DerefMode::Cell);
        }
        if tail {
            // Tail call: hand the callee OUR return target, so it returns to our
            // caller and we are never resumed. Cells 0/1 of this frame already
            // hold that target (written by whoever called us).
            self.deref(nfp, 1, 1, DerefMode::Cell); // retfp := our retfp
            self.deref(nfp, 0, 0, DerefMode::Cell); // retpc := our retpc
        } else {
            self.deref(nfp, 1, 0, DerefMode::Fp); // retfp
            self.deref(nfp, 0, 0, DerefMode::Pc); // retpc = g²·pc
        }
        self.emit(LOp::Jump { oc, od: entry, of: nfp });

        let n_args = args.len() as u32;
        let dsts: Vec<Off> = match dsts_in {
            Some(d) => d.to_vec(),
            None => (0..n_ret).map(|_| self.fresh()).collect(),
        };
        for (i, &d) in dsts.iter().enumerate() {
            self.deref(nfp, 2 + n_args + i as u32, d, DerefMode::Cell);
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
                        self.stack_store(base + k as u32, el);
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
                    let k_int = self.try_const_int(e);
                    match k_int {
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
                    } else if let Some(k) = k_int {
                        // Integer-only fold (`//`, `-`, `%` of constants): a
                        // compile-time value too, and as a scalar it is the field
                        // element with those 128 bits, materialized on demand.
                        self.rebind(name, Binding::FConst(lit_field(k)));
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
                        let b = ret_binding(self.inline_stack_ret.take().and_then(|b| b.into_iter().next()), o);
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
                    let b = ret_binding(binds.as_ref().and_then(|b| b.get(i).copied()), *d);
                    self.scope.consts.remove(n);
                    self.rebind(n, b);
                }
            }
            Stmt::AssertEq(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let t = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: t });
                self.set_const(t, F192::ZERO);
            }
            Stmt::AssertNe(a, b) => self.lower_assert_ne(a, b),
            Stmt::AssertLt(e, bound) => self.lower_assert_lt(e, bound),
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
                self.anchor();
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
                    self.stack_store(base + k, val);
                } else {
                    // Heap store `arr[idx] = val`: assert m[arr·idx] == val (write-once).
                    let v = self.expr(val);
                    let (base, beta) = self.heap_addr(arr, idx);
                    self.deref(base, beta, v, DerefMode::Cell);
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
    /// generation), `hint_f192_limbs` a value's coordinate limbs.
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
            "blake2s" => self.lower_blake2s(args),
            "assert_in_k" => {
                assert_eq!(args.len(), 2, "assert_in_k(a, b) takes two scalar cells");
                let a = self.expr(&args[0]);
                let b = self.expr(&args[1]);
                let zero = self.zero();
                self.emit(LOp::Jump { oc: zero, od: a, of: b });
            }
            "hint_f192_limbs" => {
                assert_eq!(args.len(), 2, "hint_f192_limbs(dest, value)");
                let (base, len) = self
                    .stack_of(&args[0])
                    .expect("hint_f192_limbs destination must be a StackBuf");
                assert!(
                    (1..=3).contains(&len),
                    "hint_f192_limbs destination must have 1..=3 cells"
                );
                let value = self.expr(&args[1]);
                let value = self.word_src(value);
                // Names the physical cells, as the two consumers above do, so the run
                // has to hold real values before the hint fills it. The common
                // destination is a list literal (`limbs = [0, 0, 0]`), whose every
                // element goes through `stack_store` and so defers.
                self.materialize_run(base, len);
                self.pending
                    .push(Hint::Resolved(RHint::FieldLimbs { value, base, len }));
            }
            _ => return false,
        }
        true
    }

    /// `blake2s(a, b, out)`: the digest of the two 256-bit operands lands in the
    /// existing 2-cell run `out` (write-once: if `out` was already written, this
    /// asserts the digest equals it). A heap `out` slice takes the digest via a
    /// fresh stack pair and two `DEREF`s after the hash, the store direction
    /// being the same instruction as the load (write-once fills the unset side).
    /// Keyword arguments set the compile-time metadata.
    fn lower_blake2s(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        assert_eq!(first_kw, 3, "blake2s takes three positional arguments: (a, b, out)");
        assert!(
            args[first_kw..]
                .iter()
                .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)),
            "keyword arguments must follow the three positional blake2s arguments"
        );
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in &args[first_kw..] {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            assert!(
                kwargs.insert(key, &value[0]).is_none(),
                "duplicate blake2s keyword `{key}`"
            );
        }
        let allowed = ["cv", "counter", "final", "last_node"];
        assert!(kwargs.keys().all(|k| allowed.contains(k)), "unknown blake2s keyword");
        let customized = kwargs.keys().any(|k| matches!(*k, "counter" | "final" | "last_node"));
        assert!(
            !kwargs.contains_key("cv") || customized,
            "blake2s with cv= requires counter=, since a chained block is not the default one-block hash"
        );

        let a = self.blake2s_input(&args[0]);
        let b = self.blake2s_input(&args[1]);
        let (c, heap_out) = match self.blake2s_operand(&args[2]) {
            CellRun::Stack { base, .. } => {
                self.materialize_run(base, 2);
                (base, None)
            }
            CellRun::Heap { ptr, lo, .. } => (self.alloc_stack(2), Some((ptr, lo))),
        };
        let cv = if let Some(value) = kwargs.get("cv") {
            self.blake2s_cv(value)
        } else {
            self.default_blake2s_cv()
        };
        let const_kw = |this: &Self, name: &str, default: u128| -> u128 {
            kwargs
                .get(name)
                .map(|e| {
                    this.try_const_int(e)
                        .unwrap_or_else(|| panic!("BLAKE2s `{name}` must be a compile-time integer, got `{e:?}`"))
                })
                .unwrap_or(default)
        };
        // BLAKE2s metadata is just the cumulative byte counter and two flags, so
        // a multi-block hash is `counter = 64 * blocks_before + bytes_in_this_block`
        // and `final = 1` on the last block. The default is the one-block hash of
        // a full 64-byte input, which is what `vmhash::compress` and every Merkle
        // node use.
        let counter = u64::try_from(const_kw(self, "counter", 64)).expect("BLAKE2s counter does not fit in u64");
        let f0 = if const_kw(self, "final", if customized { 0 } else { 1 }) != 0 {
            lean_vm::blake2s_flock::FINAL_FLAG
        } else {
            0
        };
        let f1 = if const_kw(self, "last_node", 0) != 0 {
            u32::MAX
        } else {
            0
        };
        let metadata = lean_vm::blake2s_flock::metadata(counter, f0, f1);
        // Each operand is two 128-bit chunk cells; the flexible opcode addresses
        // the four input cells independently (`blake2s_input` forwards the real
        // chunk sources where it can). The digest occupies the two consecutive
        // output cells `c, g·c`.
        self.emit(LOp::Blake2s {
            ins: [a[0], a[1], b[0], b[1]],
            cv,
            c,
            metadata,
        });
        if let Some((ptr, lo)) = heap_out {
            for k in 0..2 {
                self.deref(ptr, lo + k, c + k, DerefMode::Cell);
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
        // Each logical value lands straight in its flattened return area. A
        // StackBuf is copied cell-by-cell because its callee-frame offsets are
        // not meaningful after control returns to the caller.
        let mut ret = ret_base;
        for (e, shape) in exprs.iter().zip(self.return_shapes.clone()) {
            match shape {
                ReturnShape::Scalar => self.expr_into(e, ret),
                ReturnShape::StackBuf(size) => {
                    let (base, actual) = self
                        .stack_of(e)
                        .unwrap_or_else(|| panic!("expected a StackBuf({size}) return, got `{e:?}`"));
                    assert_eq!(actual, size, "returned StackBuf has size {actual}, expected {size}");
                    for k in 0..size {
                        let src = self.word_src(base + k);
                        self.copy(src, ret + k);
                    }
                }
            }
            ret += shape.cells();
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
            // A StackBuf is a run of cells, not a single scalar arg, and the
            // tail-recursive loop helper can't thread one across iterations, so a
            // StackBuf from the enclosing scope can't be captured. Reject with a
            // clear error (not the misleading "unbound variable" the capture drop
            // would otherwise trigger). Keep it inside the loop body, or carry
            // state through a `HeapBuf`.
            if self.scope.stacks.contains_key(r) {
                panic!(
                    "StackBuf `{r}` cannot be captured into a `for` loop; \
                     define it inside the loop body or carry state via a `HeapBuf`"
                );
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
        self.queue.push(Func {
            name: loop_name.clone(),
            params,
            const_params,
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
            f == "blake2s" || f == "assert_in_k" || f == "hint_f192_limbs" || defs.get(f).is_some_and(|d| d.inline)
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
        Stmt::AssertLt(e, bound) => {
            free_vars_expr(e, refs);
            if let LtBound::Runtime(b) = bound {
                free_vars_expr(b, refs);
            }
        }
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
    const_arrays: &HashMap<String, Vec<F192>>,
    with_filler: bool,
) -> Lowered {
    let mut vars = HashMap::new();
    for (i, p) in f.params.iter().enumerate() {
        assert!(
            !const_arrays.contains_key(p),
            "`{}`: parameter `{p}` collides with a top-level constant array, whose name is \
             reserved (zkDSL.md §Global constants)",
            f.name
        );
        vars.insert(p.clone(), 2 + i as u32);
    }
    // Reserve [0,1] retpc/retfp, params, then the flattened return area, then
    // locals. A StackBuf(n) return occupies n consecutive physical slots.
    let n_ret_cells: u32 = f.return_shapes.iter().map(|s| s.cells()).sum();
    let next = 2 + f.params.len() as u32 + n_ret_cells;
    let mut lowerer = FnLower {
        filler_start: None,
        scope: Scope {
            vars,
            ..Default::default()
        },
        next,
        n_args: f.params.len() as u32,
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
        phys: HashSet::new(),
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
