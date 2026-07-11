//! Lowering: each function AST is compiled to a sequence of intermediate
//! [`LOp`] instructions (fp-relative offsets, backpatched jump targets).

use super::*;

/// [`FnLower::specialized_body`]'s pieces: runtime param names, runtime args,
/// the `Const`-substituted body, and the callee's return arity.
type SpecializedBody = (Vec<String>, Vec<Expr>, Vec<Stmt>, usize);

/// A value equal to `pointer(base)·g^exp`, or the pure constant `g^exp` when
/// `base` is `None`. Heap-address arithmetic — `ptr·gᵏ`, and constant g-power
/// cursors such as a tweak-table index — is tracked symbolically so a later
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
    Some(GAddr { base, exp: a.exp.checked_add(b.exp)? })
}

/// Cap on a `β`-folded exponent: the operand g-power table is sized to the
/// largest immediate, so beyond this a huge constant index falls back to a
/// materialized pointer instead of inflating that table.
const FOLD_MAX: u128 = 1 << 16;

/// A deferred stack-cell store: the cell is a copy of another cell, or a zero.
/// Recorded instead of emitting the `MUL`/`SET`, and forwarded to the source at
/// each use ([`FnLower::word_src`]) — so `BLAKE3`, which now addresses its four
/// input words independently, reads them in place without assembling copies.
#[derive(Clone, Copy)]
enum Alias {
    Cell(Off),
    /// A compile-time constant: forwarded at its uses to the pooled cell
    /// holding that value (`const_cell`), so a constant stored into a
    /// `blake3` operand cell — the `obs`/`squeeze` tag words, padding
    /// halves — costs ONE `SET` per distinct value per function, not one
    /// per store. `Const(0, 0)` routes through the zero pool.
    Const(u64, u64),
}

struct FnLower<'a> {
    vars: HashMap<String, Off>,
    /// `StackBuf` bindings: name → (base offset, size). The `size` cells
    /// `base..base+size` are consecutive frame cells (so a size-2 one, or a
    /// 2-cell slice of a larger one, is a direct `blake3` operand). Kept
    /// separate from `vars` since a stack value is a run of cells, not a
    /// single scalar.
    stacks: HashMap<String, (Off, u32)>,
    /// Names bound to integer literals (`x = 10`), usable in compile-time
    /// index positions: stack indexes and slice bounds. Cleared on rebind to
    /// anything else. (Index arithmetic is integer arithmetic — `x + 2` in a
    /// slice bound is 12, not the field XOR the same syntax means elsewhere.)
    consts: HashMap<String, u32>,
    next: Off,
    n_args: u32,
    is_main: bool,
    code: Vec<LInstr>,
    one_off: Option<Off>,
    const_pool: HashMap<(u64, u64), Off>,
    /// Declared size of each `HeapBuf`, keyed by its pointer cell. Shifted
    /// aliases resolve to the same base cell through their gaddr, so a
    /// compile-time index checks against the ORIGINAL buffer's bound.
    heap_sizes: HashMap<Off, u128>,
    /// The cell holding this function's own `fp`, materialized lazily
    /// ([`Self::self_fp`]) — local (`if`/`else`) jumps reload the frame
    /// pointer on the taken branch.
    self_fp_off: Option<Off>,
    /// Range-check product-target cells: bound `k` → the frame cell holding
    /// `g^{k-1}`, set lazily once and shared by every check of that bound.
    bounds: HashMap<u64, Off>,
    /// Variables bound to a symbolic g-address ([`GAddr`]) — index cursors and
    /// shifted pointers, kept virtual so their offsets fold into `DEREF`'s `β`.
    gaddrs: HashMap<String, GAddr>,
    /// Variables bound to a compile-time *field* constant that isn't a g-power
    /// (e.g. a running weight `CHAIN_LENGTH^i`). Kept virtual — folded through
    /// constant field arithmetic and materialized (one `SET`) only when used.
    fconsts: HashMap<String, F128>,
    /// While inlining an `@inline` call ([`Self::try_inline`]), the destination
    /// cells its tail `return` binds into instead of emitting a return jump.
    /// `None` outside an inlined body.
    inline_ret: Option<Vec<Off>>,
    /// Set by an inlined tail `return <stackbuf>`: the returned cell run, which
    /// the caller's `let` binds as a stack alias (the MD-chain idiom
    /// `cvb = obs(cvb, x)` costs zero copies).
    inline_stack_ret: Option<(Off, u32)>,
    /// Deferred stack-cell copies/zeros ([`Alias`]), forwarded at use.
    alias: HashMap<Off, Alias>,
    /// A cached frame cell holding `0` (for forwarded zero words), set lazily.
    zero_off: Option<Off>,
    /// Hints queued to attach to the next emitted instruction.
    pending: Vec<Hint>,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
    /// The program's function definitions by name, for `Const`-parameter
    /// specialization at call sites ([`Self::specialize`]).
    defs: &'a HashMap<String, Func>,
    /// Top-level constant arrays, resolved at compile time: `NAME[i]` yields the
    /// element (a field value or an index), `len(NAME)` its length.
    const_arrays: &'a HashMap<String, Vec<u128>>,
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

    /// A frame cell holding `1` (always-taken `JUMP` condition), set lazily once.
    /// Materialize a field constant into a frame cell, pooled per function:
    /// frames are write-once, so one cell per distinct constant serves every
    /// use site (`main` alone had ~57k duplicated constant `SET`s before this).
    fn const_cell(&mut self, v: F128) -> Off {
        if let Some(&o) = self.const_pool.get(&(v.lo, v.hi)) {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set { o, k: KVal::Const(v) });
        self.const_pool.insert((v.lo, v.hi), o);
        o
    }

    fn one(&mut self) -> Off {
        if let Some(o) = self.one_off {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set {
            o,
            k: KVal::Const(F128::ONE),
        });
        self.one_off = Some(o);
        o
    }

    /// A frame cell holding `0`, set lazily once — the source for forwarded zero
    /// words (a `BLAKE3` padding half).
    fn zero(&mut self) -> Off {
        if let Some(o) = self.zero_off {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set {
            o,
            k: KVal::Const(F128::ZERO),
        });
        self.zero_off = Some(o);
        o
    }

    /// A stack store `sa[k] = val` whose value is a plain copy or a zero, which we
    /// defer as an [`Alias`] (forwarded at use) instead of emitting.
    fn copy_alias(&self, val: &Expr) -> Option<Alias> {
        match val {
            // A live var / stack cell aliases to that cell directly (no new
            // material); anything else that is a compile-time constant defers
            // to the pooled const cell.
            Expr::Var(v) if self.vars.contains_key(v) => self.vars.get(v).map(|&c| Alias::Cell(c)),
            Expr::Index(arr, idx) if self.stack_of(arr).is_some() => {
                let (base, _) = self.stack_of(arr)?;
                Some(Alias::Cell(base + self.try_const_index(idx)?))
            }
            _ => self.try_field_const(val).map(|c| Alias::Const(c.lo, c.hi)),
        }
    }

    /// Terminate `main`: jump to the halt sentinel `g^{B-1}` with `fp = g^0`.
    /// The cell holding `1` doubles as the (nonzero) jump condition and the new
    /// frame pointer `g^0`; the dest cell holds `g^{B-1}` (\S e2e, final state).
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

    /// `dst = src` (no MOV: multiply by `1`).
    fn copy(&mut self, src: Off, dst: Off) {
        let one = self.one();
        self.emit(LOp::Mul { a: src, b: one, c: dst });
    }

    /// A frame cell holding this function's own `fp` (the g-power element),
    /// materialized lazily once: a taken `JUMP` reloads the frame pointer
    /// from a cell, so local (`if`/`else`) jumps must name it. The ISA has no
    /// fp-read, so bounce it through a fresh 1-cell heap buffer — a
    /// `DEREF`-fp writes it there, a `DEREF`-cell copies it back (2 cycles,
    /// once per function that branches). In `main`, `fp = g^0 = 1`, which is
    /// the [`Self::one`] cell.
    fn self_fp(&mut self) -> Off {
        if self.is_main {
            return self.one();
        }
        if let Some(o) = self.self_fp_off {
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
        self.self_fp_off = Some(o);
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
    /// (`one`, `self_fp`, range-check bounds) revert afterwards — a cell
    /// whose `SET` sits inside a conditionally-executed region must not be
    /// trusted outside it.
    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        let saved = (
            self.vars.clone(),
            self.stacks.clone(),
            self.consts.clone(),
            self.one_off,
            self.self_fp_off,
            self.bounds.clone(),
            self.gaddrs.clone(),
            self.fconsts.clone(),
            self.alias.clone(),
            self.zero_off,
            self.const_pool.clone(),
        );
        f(self);
        // A hint pending at the end of a branch (e.g. a trailing
        // `hint_witness`) must not attach to whatever instruction follows the
        // join — that would fire it unconditionally. Absorb it with a no-op.
        if !self.pending.is_empty() {
            let o = self.fresh();
            self.emit(LOp::Set {
                o,
                k: KVal::Const(F128::ZERO),
            });
        }
        (
            self.vars,
            self.stacks,
            self.consts,
            self.one_off,
            self.self_fp_off,
            self.bounds,
            self.gaddrs,
            self.fconsts,
            self.alias,
            self.zero_off,
            self.const_pool,
        ) = saved;
    }

    /// Lower a branch body with branch-local scope ([`Self::scoped`]).
    fn branch(&mut self, body: &[Stmt]) {
        self.scoped(|s| {
            for st in body {
                s.stmt(st);
            }
        });
    }

    /// `match log(x)` — two jumps through a trampoline table (doc §ISA
    /// programming / Match statements). leanVM's switch jumps to the affine
    /// `pc = a + b·x`; in the exponent the dispatch is multiplicative:
    /// `d = g^T · x²` lands on slot `j` of the table at bytecode base `T` —
    /// `n` consecutive two-instruction slots, slot `j` being `SET c =
    /// g^{block_j}; JUMP c`. The case blocks sit anywhere, unaligned; only
    /// the fixed-size slots are consecutive. The slots are two instructions
    /// rather than one because a `JUMP` reads its target from a *cell*: a
    /// one-instruction slot would need its cell pre-`SET`, i.e. `n` `SET`s
    /// executed before every dispatch — folding the `SET` into the slot puts
    /// it on the taken path only, and the doubled slot stride is absorbed as
    /// `x²` (one extra `MUL`). Cost ≈ 7 cycles, independent of `n`.
    ///
    /// Soundness: nothing here bounds `x` — a scrutinee outside `[0, n)`
    /// dispatches to an arbitrary pc, so hinted values must be range-checked
    /// first (as in leanVM).
    fn lower_match(&mut self, x: &Expr, cases: &[Vec<Stmt>]) {
        let xo = self.expr(x);
        self.lower_match_dispatch(xo, cases.len(), |s, j| s.branch(&cases[j]));
    }

    /// `names = match_range(log(x), …)` — the same dispatch as
    /// [`Self::lower_match`], with generated arms: arm `j` evaluates its
    /// expression (the lambda body at `i = j`) and copies the results into
    /// cells shared by every arm (write-once: exactly one arm executes);
    /// `names` bind to those cells at the join.
    fn lower_match_range(&mut self, names: &[String], x: &Expr, arms: &[Expr]) {
        // Fusion: when every arm is a direct call to the same function with
        // identical runtime args (differing only in `Const` args — the usual
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
            if specialized.iter().all(|(_, rt)| exprs_eq(rt, rt0)) {
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
                    s.call_into(f, cargs, &rcells);
                }
            });
        });
        for (name, &cell) in names.iter().zip(&rcells) {
            self.stacks.remove(name);
            self.consts.remove(name);
            self.gaddrs.remove(name);
            self.fconsts.remove(name);
            self.vars.insert(name.clone(), cell);
        }
    }

    /// `names = match_range(log(x), …, lambda k: f(args, k))` fused: the arms all
    /// call one of `callees` (specializations sharing the arg/return layout) with
    /// the same runtime `args`, so build the callee frame **once** and let the
    /// dispatch jump straight into the selected entry, which returns to the join.
    /// Each taken arm is then just the trampoline's `SET entry; JUMP` — no
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
        for (i, &ao) in arg_offs.iter().enumerate() {
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 2 + i as u32,
                gamma: ao,
                mode: DerefMode::Cell,
            });
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

        // Dispatch: d = g^T · x² lands on the two-instruction slot for the digit.
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
        self.emit(LOp::Jump { oc: one, od: d, of: sfp });

        // Trampoline: slot j enters `callees[j]` with fp = nfp; the callee's own
        // `return` jumps to retpc (the join) in the caller frame.
        self.patch_local(kset, self.code.len());
        for callee in callees {
            let c = self.fresh();
            self.emit(LOp::Set {
                o: c,
                k: KVal::Entry(callee.clone()),
            });
            self.emit(LOp::Jump { oc: one, od: c, of: nfp });
        }

        // Join: read the return values (written by whichever callee ran).
        self.patch_local(join_set, self.code.len());
        for (i, &r) in rcells.iter().enumerate() {
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 2 + n_args + i as u32,
                gamma: r,
                mode: DerefMode::Cell,
            });
        }

        for (name, &cell) in names.iter().zip(&rcells) {
            self.stacks.remove(name);
            self.consts.remove(name);
            self.gaddrs.remove(name);
            self.fconsts.remove(name);
            self.vars.insert(name.clone(), cell);
        }
    }

    /// The trampoline dispatch shared by `match` and `match_range`: jump to
    /// `d = g^T · x²` (slot `j` of the two-instruction table at bytecode base
    /// `T`), then to `body(j)`'s code; every non-final body exits to the
    /// join. `body` lowers arm `j` — with its own branch-local scope.
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
        // d = g^T · x² — slot j (two instructions) sits at T + 2j.
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
        self.emit(LOp::Jump {
            oc: one,
            od: d,
            of: sfp,
        });
        // The trampoline table.
        self.patch_local(kset, self.code.len());
        let mut slots = Vec::new();
        for _ in 0..n {
            let c = self.fresh();
            slots.push(self.code.len());
            self.emit(LOp::Set {
                o: c,
                k: KVal::Local(0),
            }); // patched: its block
            self.emit(LOp::Jump {
                oc: one,
                od: c,
                of: sfp,
            });
        }
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

    /// `if` / `else` — one `XOR` and one conditional `JUMP` (taken ⇔ the
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
        // bindings persist — unlike a runtime branch, whose bindings are
        // branch-local (a runtime branch may not execute).
        if let (Some(a), Some(b)) = (self.try_const_index(lhs), self.try_const_index(rhs)) {
            for st in if (a == b) == eq { then } else { els } {
                self.stmt(st);
            }
            return;
        }
        let (la, lb) = (self.expr(lhs), self.expr(rhs));
        let x = self.fresh();
        self.emit(LOp::Xor { a: la, b: lb, c: x }); // x = lhs + rhs: nonzero ⇔ !=
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

    /// `assert a != b` — one `XOR` and one conditional `JUMP` on `a + b`. When
    /// the sides differ (`a + b ≠ 0`) the jump is taken to the continuation, so
    /// execution proceeds; when they are equal it falls through to a `SET` +
    /// unconditional `JUMP` to the poison pc `g^-1` ([`KVal::Poison`]), which
    /// lies outside the committed bytecode cube — the bytecode bus cannot
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
        self.emit(LOp::Set { o: cont, k: KVal::Local(0) });
        self.emit(LOp::Jump { oc: x, od: cont, of: sfp });
        // a == b: fall through to the poison jump (g^-1, an unreachable pc).
        let pd = self.fresh();
        self.emit(LOp::Set { o: pd, k: KVal::Poison });
        self.emit(LOp::Jump { oc: one, od: pd, of: sfp });
        self.patch_local(cset, self.code.len());
    }

    /// The frame cell holding `g^{k-1}` — the range-check product target — set
    /// lazily once per distinct bound `k` and shared by that bound's checks.
    fn bound_cell(&mut self, k: u64) -> Off {
        if let Some(&o) = self.bounds.get(&k) {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set {
            o,
            k: KVal::Const(g_pow_u128((k - 1) as u128)),
        });
        self.bounds.insert(k, o);
        o
    }

    /// `hint_witness(dest, "name")` — resolve `dest` to a run of cells and
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
                Hint::WitnessStack { name, base, len }
            }
            Expr::Slice(arr, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                (Some(lo), Some(hi)) => {
                    assert!(lo < hi, "empty hint_witness slice {lo}:{hi}");
                    if let Some((base, size)) = self.stack_of(arr) {
                        assert!(hi <= size, "slice {lo}:{hi} out of bounds (StackBuf size {size})");
                        Hint::WitnessStack {
                            name,
                            base: base + lo,
                            len: hi - lo,
                        }
                    } else {
                        let len = hi - lo;
                        self.check_heap_bound(arr, lo as u128, len as u128);
                        let (ptr, lo) = self.heap_base(arr, lo as u128);
                        Hint::WitnessHeap { name, ptr, lo, len }
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
                    Hint::WitnessHeap { name, ptr, lo, len }
                }
            },
            other => panic!("hint_witness dest must be a StackBuf or a slice, got `{other:?}`"),
        };
        self.pending.push(hint);
    }

    /// `assert log x < log GEN ** k` — the 3-cycle range check *in the
    /// exponent* (leanVM's DEREF trick, doc `../leanVM/misc/minimal_zkVM.tex`
    /// §range-checks, transported to g-powers). With `x = g^e`:
    ///
    /// 1. `DEREF` through `x` — the dereferenced address `x·g^0` must be one of
    ///    the memory's `2^h` addresses `{g^0, …, g^{2^h-1}}` (doc §Memory), so
    ///    the bus itself proves `x = g^e` with `e < 2^h`;
    /// 2. `MUL x·y` into the write-once cell holding `g^{k-1}` — asserts
    ///    `x·y = g^{k-1}`. The complement `y = g^{k-1-e}` needs no hint: the
    ///    result cell is already written, so the runner back-solves the one
    ///    unknown operand (leanVM's ADD deduction, multiplicatively);
    /// 3. `DEREF` through `y` — proves `y = g^f` with `f < 2^h`.
    ///
    /// Then `e + f ≡ k-1 (mod 2^128-1)` with `e, f < 2^h`, and since a negative
    /// `k-1-e` wraps to `≈ 2^128 ≫ 2^h`, this forces `e ≤ k-1` — for ANY memory
    /// size the prover announces, provided `k ≤ 2^MIN_LOG_MEM`. The two `DEREF`
    /// target cells are unconstrained touches (only the address matters),
    /// back-filled at the end of execution; the constant cell is one amortized
    /// `SET` per distinct bound.
    fn lower_assert_lt(&mut self, e: &Expr, k: u64) {
        assert!(k >= 1, "range-check bound GEN ** 0 names the empty set");
        assert!(
            k <= 1 << crate::cpu::MIN_LOG_MEM,
            "range-check bound GEN ** {k} exceeds 2^{} (the minimum memory size)",
            crate::cpu::MIN_LOG_MEM,
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
            Expr::Lit(n) => self.const_cell(F128::new(*n as u64, (*n >> 64) as u64)),
            Expr::Gen => self.const_cell(g_pow(1)),
            Expr::GPow(k) => self.const_cell(g_pow_u128(*k)),
            Expr::GenPow(e) => {
                let o = self.fresh();
                self.emit(LOp::Set {
                    o,
                    k: KVal::Const(g_pow_u128(self.gpow_exp(e))),
                });
                o
            }
            Expr::Pow(b, e) => self.pow_expr(b, e),
            Expr::Var(v) => {
                if self.stacks.contains_key(v) {
                    panic!("StackBuf `{v}` used as a scalar; index it (`{v}[k]`) or pass it to blake3");
                }
                if let Some(&ga) = self.gaddrs.get(v) {
                    return self.materialize(ga);
                }
                if let Some(&c) = self.fconsts.get(v) {
                    return self.const_cell(c);
                }
                *self.vars.get(v).unwrap_or_else(|| panic!("unbound variable `{v}`"))
            }
            Expr::Add(a, b) => {
                // Identity fold: a compile-time 0 operand contributes nothing
                // (and, being a constant, has no side effect to preserve), so
                // `x + 0` lowers to just `x` — no cell, no XOR. Kills the
                // `acc = 0; acc = acc + t` accumulator seed and similar.
                if self.try_field_const(a) == Some(F128::ZERO) {
                    return self.expr(b);
                }
                if self.try_field_const(b) == Some(F128::ZERO) {
                    return self.expr(a);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                let o = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: o });
                o
            }
            Expr::Mul(a, b) => {
                // Identity fold: a compile-time 1 operand is a no-op multiply,
                // so `x * 1` lowers to just `x`. Kills the `acc = GEN ** 0`
                // (= 1) accumulator seed's first `1 * f` in every product loop.
                if self.try_field_const(a) == Some(F128::ONE) {
                    return self.expr(b);
                }
                if self.try_field_const(b) == Some(F128::ONE) {
                    return self.expr(a);
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
                // `a` must already be written — `self.expr(a)` guarantees it.
                let (la, lb) = (self.expr(a), self.expr(b));
                let q = self.fresh();
                self.emit(LOp::Mul { a: q, b: lb, c: la });
                q
            }
            Expr::Call(f, args) if f == "hint_log2_ceil" => {
                // Computed advice: the prover fills g^log2_ceil (base-2 ceil-log) of the value in
                // `bits` (a `nbits`-bit buffer), floored at `floor`. Returned
                // UNCONSTRAINED — the caller (log2_ceil) re-verifies it. Same
                // "prover computes, circuit checks" pattern as `/`.
                assert_eq!(args.len(), 3, "log2_ceil(bits, nbits, floor)");
                let bits_ptr = self.expr(&args[0]);
                let nbits = self.const_index(&args[1]);
                let floor = self.const_index(&args[2]);
                let dst = self.fresh();
                self.pending.push(Hint::Log2Ceil { bits_ptr, dst, nbits, floor });
                dst
            }
            Expr::Call(f, args) => {
                if let Some(n) = self.const_len(e) {
                    self.const_cell(F128::new(n as u64, 0))
                } else {
                    self.call(f, args, 1)[0]
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
                    return self.const_cell(F128::new(elem as u64, (elem >> 64) as u64));
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
                panic!("`-`, `//`, `%` are compile-time only (field subtraction is `+`); use them in an index, a bound, or a `Const` argument, got `{e:?}`")
            }
            Expr::Slice(..) => panic!("a slice is not a scalar; it is only a blake3 operand"),
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
            Expr::Var(v) => self.stacks.get(v).copied(),
            _ => None,
        }
    }

    /// A compile-time integer index — a literal, a name bound to a literal,
    /// or `+`/`*`/`//`/`%` of those (evaluated as *integer* arithmetic: this is
    /// index space, not the field). `None` when the expression is a runtime
    /// value (which a heap slice start may be; see [`Self::blake3_operand`]).
    fn try_const_index(&self, idx: &Expr) -> Option<u32> {
        match idx {
            // A literal that fits is an index; a ≥ 2^32 literal is a field value,
            // not an index (`None` — callers that require an index then error).
            Expr::Lit(k) => u32::try_from(*k).ok(),
            Expr::Var(v) => self.consts.get(v).copied(),
            // Overflow (or a negative `-`) means the expression is not a valid
            // index — decline (`None`) rather than panic: this evaluator also
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
            Expr::Index(..) => self.const_array_elem(idx).and_then(|e| u32::try_from(e).ok()),
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
            // value — diagnose it precisely (`sa[2^32]` must not wrap to `sa[0]`).
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
        // Fully constant → evaluate in the field and emit a single `SET`.
        if let Some(bc) = self.try_field_const(b) {
            let mut acc = F128::ONE;
            for _ in 0..k {
                acc *= bc;
            }
            let o = self.fresh();
            self.emit(LOp::Set { o, k: KVal::Const(acc) });
            return o;
        }
        if k == 0 {
            let o = self.fresh();
            self.emit(LOp::Set { o, k: KVal::Const(F128::ONE) });
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
    fn const_array_elem(&self, e: &Expr) -> Option<u128> {
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

    /// Resolve a `blake3` operand — a size-2 `StackBuf` name, a 2-cell
    /// `StackBuf` slice `buf[lo:hi]`, or a 2-cell `HeapBuf` slice (cells
    /// `ptr·g^lo`, `ptr·g^{lo+1}`) — with compile-time bounds. Stack operands
    /// are used in place; heap operands must be bridged through the stack,
    /// since `BLAKE3` addresses only frame cells (see [`Self::blake3_input`]).
    fn blake3_operand(&mut self, e: &Expr) -> B3Operand {
        match e {
            Expr::Var(_) => {
                let (base, size) = self
                    .stack_of(e)
                    .expect("a bare blake3 operand must be a StackBuf; slice a HeapBuf: `buf[lo:lo + 2]`");
                assert!(
                    size == 2,
                    "a whole-StackBuf blake3 operand must have size 2; slice a larger one: `buf[lo:lo + 2]`"
                );
                B3Operand::Stack(base)
            }
            Expr::Slice(arr, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                // Compile-time bounds: integer cell indexes `lo..lo+2` (frame
                // offsets for a stack, g-power exponents for the heap).
                (Some(lo), Some(hi)) => {
                    assert!(hi == lo + 2, "a blake3 slice must span exactly 2 cells, got {lo}:{hi}");
                    if let Some((base, size)) = self.stack_of(arr) {
                        assert!(hi <= size, "slice {lo}:{hi} out of bounds (StackBuf size {size})");
                        B3Operand::Stack(base + lo)
                    } else {
                        // A heap slice: fold `arr`'s shift and `lo` into the
                        // pointer offset, checking the 2-cell span.
                        self.check_heap_bound(arr, lo as u128, 2);
                        let (ptr, lo) = self.heap_base(arr, lo as u128);
                        B3Operand::Heap { ptr, lo }
                    }
                }
                // Runtime start (heap only): `buf[i:i + 2]` with a runtime
                // g-power index `i` names the cells `buf·i`, `buf·i·g`. The
                // `hi` bound cannot be evaluated, only shape-checked: it must
                // be syntactically `lo + 2`. One MUL folds `i` into the
                // pointer; the two-cell bridge is then offsets 0, 1 off it.
                _ => {
                    assert!(
                        self.stack_of(arr).is_none(),
                        "a StackBuf slice needs compile-time bounds (frame offsets are baked into the bytecode)"
                    );
                    assert!(
                        plus_k(lo, hi) == Some(2),
                        "a runtime blake3 slice must have the shape `buf[i:i + 2]`, got `{lo:?}:{hi:?}`"
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

    /// A `blake3` *input* operand as a frame offset: stack runs in place; a
    /// heap slice is pulled into a fresh stack pair first — one `DEREF` per
    /// cell (`m[ptr·g^{lo+k}] == m[fp+t+k]`, the `β` immediate doing the
    /// pointer offset). The heap cells must already be written.
    fn blake3_input(&mut self, e: &Expr) -> [Off; 2] {
        match self.blake3_operand(e) {
            // A stack operand: the two words live at `o, o+1`; forward each cell's
            // real source where one is known (a copy or a zero), so a hash of
            // non-adjacent values needs no assembling copies.
            B3Operand::Stack(o) => [self.word_src(o), self.word_src(o + 1)],
            B3Operand::Heap { ptr, lo } => {
                let t = self.alloc_stack(2);
                for k in 0..2 {
                    self.emit(LOp::Deref {
                        alpha: ptr,
                        beta: lo + k,
                        gamma: t + k,
                        mode: DerefMode::Cell,
                    });
                }
                [t, t + 1]
            }
        }
    }

    /// The cell holding the value of stack cell `o`, following a recorded copy /
    /// zero alias to its real source (so `BLAKE3` reads the source directly and
    /// the assembling copy is never emitted). Returns `o` when it holds a genuine
    /// value.
    fn word_src(&mut self, o: Off) -> Off {
        match self.alias.get(&o).copied() {
            Some(Alias::Cell(s)) => self.word_src(s),
            Some(Alias::Const(0, 0)) => self.zero(),
            Some(Alias::Const(lo, hi)) => self.const_cell(F128::new(lo, hi)),
            None => o,
        }
    }

    /// Evaluate `e` writing its value straight into cell `dst` — no temporary +
    /// copy for the common cases (a heap read DEREFs directly into `dst`; a
    /// constant / arithmetic emits into `dst`). Falls back to `expr` + `copy` for
    /// vars, calls, and stack reads.
    fn expr_into(&mut self, e: &Expr, dst: Off) {
        // A constant-array element is a compile-time value, not a heap read.
        if let Some(elem) = self.const_array_elem(e) {
            self.emit(LOp::Set {
                o: dst,
                k: KVal::Const(F128::new(elem as u64, (elem >> 64) as u64)),
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
                    k: KVal::Const(F128::new(*n as u64, (*n >> 64) as u64)),
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
                // Identity fold (see the `expr` Add arm): `x + 0` copies `x`.
                if self.try_field_const(a) == Some(F128::ZERO) {
                    self.expr_into(b, dst);
                } else if self.try_field_const(b) == Some(F128::ZERO) {
                    self.expr_into(a, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Xor { a: la, b: lb, c: dst });
                }
            }
            Expr::Mul(a, b) => {
                // Identity fold: `x * 1` copies `x`.
                if self.try_field_const(a) == Some(F128::ONE) {
                    self.expr_into(b, dst);
                } else if self.try_field_const(b) == Some(F128::ONE) {
                    self.expr_into(a, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Mul { a: la, b: lb, c: dst });
                }
            }
            // A call writes its single return value straight into `dst`.
            Expr::Call(f, args) => self.call_into(f, args, &[dst]),
            _ => {
                let v = self.expr(e);
                self.copy(v, dst);
            }
        }
    }

    /// Compute the absolute pointer `arr·idx` into a fresh cell (heap addressing
    /// in the exponent: cell `g^k` of the buffer sits at `arr·g^k`).
    fn array_ptr(&mut self, arr: &Expr, idx: &Expr) -> Off {
        let (la, li) = (self.expr(arr), self.expr(idx));
        let ptr = self.fresh();
        self.emit(LOp::Mul { a: la, b: li, c: ptr });
        ptr
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
            Expr::GenPow(e) => Some(GAddr { base: None, exp: self.try_const_index(e)? as u128 }),
            Expr::Var(v) => self
                .gaddrs
                .get(v)
                .copied()
                .or_else(|| self.vars.get(v).map(|&c| GAddr { base: Some(c), exp: 0 })),
            Expr::Mul(a, b) => gmul(self.gaddr_of(a)?, self.gaddr_of(b)?),
            _ => None,
        }
    }

    /// `e` as a compile-time *field* constant, when it is one: a literal, `GEN`,
    /// `GEN ** k`, a var bound to a field constant (or a constant g-power), or
    /// `+`/`*` of those evaluated in the field (XOR / GHASH). `None` for a
    /// runtime value or a compile-time *integer* op (`//`/`%` are index-only).
    fn try_field_const(&self, e: &Expr) -> Option<F128> {
        match e {
            Expr::Lit(n) => Some(F128::new(*n as u64, (*n >> 64) as u64)),
            Expr::Gen => Some(g_pow(1)),
            Expr::GPow(k) => Some(g_pow_u128(*k)),
            Expr::GenPow(e) => Some(g_pow_u128(self.try_const_index(e)? as u128)),
            Expr::Var(v) => self.fconsts.get(v).copied().or_else(|| match self.gaddrs.get(v) {
                Some(GAddr { base: None, exp }) => Some(g_pow_u128(*exp)),
                _ => None,
            }),
            Expr::Add(a, b) => Some(self.try_field_const(a)? + self.try_field_const(b)?),
            Expr::Mul(a, b) => Some(self.try_field_const(a)? * self.try_field_const(b)?),
            // A constant-array element `NAME[i]` as a field value, or `len(NAME)`.
            Expr::Index(..) => self.const_array_elem(e).map(|v| F128::new(v as u64, (v >> 64) as u64)),
            Expr::Call(..) => self.const_len(e).map(|n| F128::new(n as u64, 0)),
            // `b ** e` as a field constant (constant base, compile-time exponent).
            Expr::Pow(b, e) => {
                let bc = self.try_field_const(b)?;
                let k = self.try_const_index(e)?;
                let mut acc = F128::ONE;
                for _ in 0..k {
                    acc *= bc;
                }
                Some(acc)
            }
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
                self.emit(LOp::Set { o: k, k: KVal::Const(g_pow_u128(exp)) });
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
        let (Some(base), Some(exp)) = (ga.base, ga.exp.checked_add(extra)) else { return };
        let Some(&size) = self.heap_sizes.get(&base) else { return };
        if exp + span > size {
            let name = self
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
                && exp <= FOLD_MAX {
                    return (base, exp as u32);
                }
        let a = self.expr(arr);
        if extra == 0 {
            return (a, 0);
        }
        let k = self.fresh();
        self.emit(LOp::Set { o: k, k: KVal::Const(g_pow_u128(extra)) });
        let ptr = self.fresh();
        self.emit(LOp::Mul { a, b: k, c: ptr });
        (ptr, 0)
    }

    /// Address `arr[idx]` as `(base_cell, β)`. A constant g-power `idx` folds
    /// into `β` ([`Self::heap_base`]); a runtime index materializes the pointer.
    fn heap_addr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        match self.gaddr_of(idx) {
            Some(GAddr { base: None, exp }) => return self.heap_base(arr, exp),
            // A runtime-base index carrying a constant g-power shift
            // (`buf[cursor * GEN ** k]`): fold the whole constant part — the
            // index's shift plus `arr`'s own symbolic shift — into `β`, and
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
        (self.array_ptr(arr, idx), 0)
    }

    /// Lower a call; returns the caller offsets bound to the returned values.
    fn call(&mut self, callee: &str, args: &[Expr], n_ret: usize) -> Vec<Off> {
        assert!(
            callee != "blake3",
            "blake3 is a statement: `blake3(a, b, out)` writes the digest into the 2-cell stack run `out`"
        );
        let dsts: Vec<Off> = (0..n_ret).map(|_| self.fresh()).collect();
        self.inline_stack_ret = None;
        self.call_into(callee, args, &dsts);
        dsts
    }

    /// Evaluate `callee(args)` into `dsts` — inlining the callee when it is
    /// `@inline` ([`Self::try_inline`]), else a real call.
    fn call_into(&mut self, callee: &str, args: &[Expr], dsts: &[Off]) {
        assert!(callee != "blake3", "blake3 is a statement, not a value-returning call");
        if !self.try_inline(callee, args, dsts) {
            self.lower_call(callee, args, dsts.len(), None, Some(dsts));
        }
    }

    /// The runtime params, runtime args, and `Const`-substituted body of a call
    /// to a user function — the ingredients for inlining. `None` for a builtin/
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
            let c = match a {
                Expr::Lit(n) => Expr::Lit(*n),
                Expr::Gen => Expr::GPow(1),
                Expr::GPow(k) => Expr::GPow(*k),
                Expr::Var(v) => Expr::Lit(*self.consts.get(v)? as u128),
                // Any other compile-time integer expression (const-array
                // element, arithmetic over Const params) is a valid Const
                // argument — e.g. `foldyr(yr, w, 0, YRLOG2[mi])`.
                other => Expr::Lit(self.try_const_index(other)? as u128),
            };
            body = subst_stmts(&body, p, &c);
        }
        Some((rt_params, rt_args, body, def.n_ret))
    }

    /// Inline an `@inline` `callee(args)` into the current frame, binding its
    /// return values straight into `dsts` — no frame setup, no argument/return
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
        assert_eq!(n_ret, dsts.len(), "`@inline {callee}` returns {n_ret} values, call binds {}", dsts.len());
        assert!(
            body_inlinable(&body),
            "`@inline {callee}` must be a single tail `return` with no call/loop/match (see body_inlinable)"
        );
        // Bind the params from the caller-scope arguments (symbolically where we
        // can, so a shifted-pointer arg keeps folding into `β`; a `StackBuf` arg
        // aliases its cell run), then lower the body in a fresh variable
        // environment — a function sees only its params. The frame, `one`,
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
        let saved = (
            std::mem::take(&mut self.vars),
            std::mem::take(&mut self.stacks),
            std::mem::take(&mut self.consts),
            std::mem::take(&mut self.gaddrs),
            std::mem::take(&mut self.fconsts),
        );
        for (p, b) in binds {
            match b {
                Bind::Stack(base, size) => {
                    self.stacks.insert(p, (base, size));
                }
                Bind::Addr(ga) => {
                    self.gaddrs.insert(p, ga);
                }
                Bind::Cell(cell) => {
                    self.vars.insert(p, cell);
                }
            }
        }
        let saved_ret = self.inline_ret.replace(dsts.to_vec());
        for s in &body {
            self.stmt(s);
        }
        self.inline_ret = saved_ret;
        (self.vars, self.stacks, self.consts, self.gaddrs, self.fconsts) = saved;
        true
    }

    /// A *conditional* tail call: transfer to `callee(args)` iff `cond != 0`,
    /// else fall through (`JUMP`'s nonzero test, doc §7.5). The frame setup runs
    /// either way; when not taken the callee frame is just never entered. Binds
    /// no return values, so the not-taken path continues straight after it.
    fn call_cond(&mut self, callee: &str, args: &[Expr], cond: Off) {
        self.lower_call(callee, args, 0, Some(cond), None);
    }

    /// If `callee` declares `Const` parameters, monomorphize: the constant
    /// arguments (literals, `GEN ** k`, or literal-bound names) substitute
    /// into a copy of the callee — queued once per distinct constant tuple,
    /// named `callee__L5_G3`-style — and only the runtime arguments remain.
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
            let c = match a {
                Expr::Lit(n) => Expr::Lit(*n),
                Expr::Gen => Expr::GPow(1),
                Expr::GPow(k) => Expr::GPow(*k),
                // Any compile-time integer expression (a bound name, a constant-
                // array element `DEPTH[lvl]`, `len(...)`, index arithmetic).
                other => match self.try_const_index(other) {
                    Some(k) => Expr::Lit(k as u128),
                    None => panic!(
                        "argument for Const parameter `{p}` of `{callee}` must be a compile-time \
                         constant, got `{other:?}`"
                    ),
                },
            };
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
                body,
                inline: false,
            });
        }
        (name, rt_args)
    }

    /// Lower a call. Return values land in `dsts_in` when given (write-once, so
    /// distinct arms of a `match_range` may share the same cells), else in fresh
    /// cells — sparing the caller a temp-then-copy.
    fn lower_call(
        &mut self,
        callee: &str,
        args: &[Expr],
        n_ret: usize,
        cond: Option<Off>,
        dsts_in: Option<&[Off]>,
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
        self.emit(LOp::Set {
            o: entry,
            k: KVal::Entry(callee.to_string()),
        });

        // The frame-pointer hint fires before the first DEREF that reads `nfp`.
        self.pending.push(Hint::AllocFrame {
            ptr: nfp,
            callee: callee.to_string(),
        });
        for (i, &ao) in arg_offs.iter().enumerate() {
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 2 + i as u32,
                gamma: ao,
                mode: DerefMode::Cell,
            });
        }
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
        self.emit(LOp::Jump { oc, od: entry, of: nfp });

        let n_args = args.len() as u32;
        let dsts: Vec<Off> = match dsts_in {
            Some(d) => d.to_vec(),
            None => (0..n_ret).map(|_| self.fresh()).collect(),
        };
        for (i, &d) in dsts.iter().enumerate() {
            self.emit(LOp::Deref {
                alpha: nfp,
                beta: 2 + n_args + i as u32,
                gamma: d,
                mode: DerefMode::Cell,
            });
        }
        dsts
    }

    fn stmt(&mut self, s: &Stmt) {
        match s {
            // A `let` rebinds the name's kind; clear the OTHER map so a stale
            // binding (e.g. a former StackBuf now rebound to a scalar) can't
            // shadow the new one. `vars`/`stacks` are consulted independently, so
            // both must be kept in sync on every rebind.
            Stmt::Let(name, e) => match e {
                // `x = StackBuf(n)`: bind a run of `n` consecutive frame cells.
                Expr::StackBuf(n) => {
                    let base = self.alloc_stack(*n as u32);
                    self.vars.remove(name);
                    self.consts.remove(name);
                    self.gaddrs.remove(name);
                    self.fconsts.remove(name);
                    self.stacks.insert(name.clone(), (base, *n as u32));
                }
                // `x = other_stackbuf`: a compile-time alias of the same cell
                // run (zero instructions) — the chaining-state idiom
                // `st = sn` of an MD loop.
                Expr::Var(v) if self.stacks.contains_key(v) => {
                    let bs = self.stacks[v];
                    self.vars.remove(name);
                    self.consts.remove(name);
                    self.gaddrs.remove(name);
                    self.fconsts.remove(name);
                    self.stacks.insert(name.clone(), bs);
                }
                _ => {
                    // NOTE: `name`'s old binding stays visible while the RHS is
                    // lowered (the MD-chain idiom `cvb = obs(cvb, x)` reads it);
                    // each terminal path below unbinds/rebinds afterwards.
                    // A compile-time integer binding (a literal, or an expression
                    // that folds — `FOLDBASE[lvl] + j`, `n // 2`, `len(A) - 1`) is
                    // usable as a compile-time index / bound / exponent.
                    let k_idx = self.try_const_index(e);
                    match k_idx {
                        Some(k) => {
                            self.consts.insert(name.clone(), k);
                        }
                        None => {
                            self.consts.remove(name);
                        }
                    }
                    // A symbolic g-address (a constant g-power or a shifted
                    // pointer) or a compile-time field constant stays virtual:
                    // no instruction here, folded / materialized only on demand.
                    if let Some(ga) = self.gaddr_of(e) {
                        self.vars.remove(name);
                        self.stacks.remove(name);
                        self.fconsts.remove(name);
                        self.gaddrs.insert(name.clone(), ga);
                    } else if let Some(c) = self.try_field_const(e) {
                        self.vars.remove(name);
                        self.stacks.remove(name);
                        self.gaddrs.remove(name);
                        self.fconsts.insert(name.clone(), c);
                    } else if let Some(k) = k_idx {
                        // Integer-only fold (`//`, `-`, `%` of constants): a
                        // compile-time value too — as a scalar it is the field
                        // element with those 128 bits, materialized on demand.
                        self.vars.remove(name);
                        self.stacks.remove(name);
                        self.gaddrs.remove(name);
                        self.fconsts.insert(name.clone(), F128::new(k as u64, 0));
                    } else {
                        let o = self.expr(e);
                        if let Some((base, size)) = self.inline_stack_ret.take() {
                            self.vars.remove(name);
                            self.gaddrs.remove(name);
                            self.fconsts.remove(name);
                            self.stacks.insert(name.clone(), (base, size));
                        } else {
                            self.stacks.remove(name);
                            self.gaddrs.remove(name);
                            self.fconsts.remove(name);
                            self.vars.insert(name.clone(), o);
                        }
                    }
                }
            },
            Stmt::LetTuple(names, f, args) => {
                let dsts = self.call(f, args, names.len());
                for (n, d) in names.iter().zip(dsts) {
                    self.consts.remove(n);
                    self.gaddrs.remove(n);
                    self.fconsts.remove(n);
                    self.vars.insert(n.clone(), d);
                }
            }
            Stmt::AssertEq(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let t = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: t });
                self.emit(LOp::Set {
                    o: t,
                    k: KVal::Const(F128::ZERO),
                });
            }
            Stmt::AssertNe(a, b) => self.lower_assert_ne(a, b),
            Stmt::AssertLt(e, k) => self.lower_assert_lt(e, *k),
            Stmt::HintWitness { dest, name } => self.lower_hint_witness(dest, name),
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
                // Computed advice fills (prover-side, re-checked by the caller):
                // `hint_decompose_bits(bits, value, nbits)` writes value's bits into the
                // buffer; `hint_decompose_bits_exponent(bits, x, nbits)` writes the
                // bits of n where x = g^n (a bounded dlog at witness generation).
                if f == "hint_decompose_bits" {
                    assert_eq!(args.len(), 3, "hint_decompose_bits(bits, value, nbits)");
                    let bits_ptr = self.expr(&args[0]);
                    let value = self.expr(&args[1]);
                    let nbits = self.const_index(&args[2]);
                    self.pending.push(Hint::BitDecompose { value, bits_ptr, nbits });
                    return;
                }
                if f == "hint_decompose_bits_exponent" {
                    assert_eq!(args.len(), 3, "hint_decompose_bits_exponent(bits, x, nbits)");
                    let bits_ptr = self.expr(&args[0]);
                    let value = self.expr(&args[1]);
                    let nbits = self.const_index(&args[2]);
                    self.pending.push(Hint::BitDecomposeExp { value, bits_ptr, nbits });
                    return;
                }
                // `blake3(a, b, out)`: the digest of the two 256-bit operands
                // lands in the existing 2-cell run `out` (write-once: if `out`
                // was already written, this asserts the digest equals it). A
                // heap `out` slice takes the digest via a fresh stack pair and
                // two `DEREF`s after the hash (the store direction is the same
                // instruction as the load — write-once fills the unset side).
                if f == "blake3" {
                    assert_eq!(args.len(), 3, "blake3 takes (a, b, out)");
                    let a = self.blake3_input(&args[0]);
                    let b = self.blake3_input(&args[1]);
                    let (c, heap_out) = match self.blake3_operand(&args[2]) {
                        B3Operand::Stack(o) => (o, None),
                        B3Operand::Heap { ptr, lo } => (self.alloc_stack(2), Some((ptr, lo))),
                    };
                    // Each operand's two words are at `base, base+1`; the flexible
                    // opcode addresses them independently (`blake3_input` forwards
                    // the real word sources where it can).
                    self.emit(LOp::Blake3 {
                        ins: [a[0], a[1], b[0], b[1]],
                        c,
                    });
                    if let Some((ptr, lo)) = heap_out {
                        for k in 0..2 {
                            self.emit(LOp::Deref {
                                alpha: ptr,
                                beta: lo + k,
                                gamma: c + k,
                                mode: DerefMode::Cell,
                            });
                        }
                    }
                    return;
                }
                self.call(f, args, 0);
            }
            Stmt::Store(arr, idx, val) => {
                // Stack write `sa[k] = val`: place `val` straight into cell `base+k`.
                if let Some((base, size)) = self.stack_of(arr) {
                    let k = self.const_index(idx);
                    assert!(k < size, "stack store index {k} out of bounds (size {size})");
                    let dst = base + k;
                    // A plain copy / zero is deferred as an alias and forwarded at
                    // its uses (write-once, so the source cell keeps its value) —
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
                let (la, lb) = (self.expr(lhs), self.expr(rhs));
                let x = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: x }); // x = lhs − rhs; x != 0 ⇔ lhs != rhs
                self.call_cond(callee, args, x);
            }
            Stmt::For { var, lo, hi, body } => self.lower_for(var, *lo, hi, body),
            // Compile-time unrolling: emit the body per integer, the counter
            // substituted as its literal. Every copy executes (this is
            // straight-line code, not a branch), so bindings simply rebind —
            // a fresh binding per iteration — and lazy caches persist.
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

    fn lower_return(&mut self, exprs: &[Expr]) {
        // Inlined (`@inline`): bind the return values into the caller's cells
        // and fall through — the body's tail return, so no jump is needed.
        if let Some(dsts) = self.inline_ret.clone() {
            // `return <stackbuf>` from an `@inline` body: hand the caller the
            // cell run itself (alias), not copies — the buffer was allocated
            // in the caller's frame, so it outlives the inline scope.
            if let [e] = exprs
                && let Some((base, size)) = self.stack_of(e)
            {
                self.inline_stack_ret = Some((base, size));
                return;
            }
            for (e, &d) in exprs.iter().zip(&dsts) {
                self.expr_into(e, d);
            }
            return;
        }
        if self.is_main {
            return; // a `return` in main is a no-op; main halts via the trailing sentinel jump (lower_func).
        }
        let ret_base = 2 + self.n_args;
        for (i, e) in exprs.iter().enumerate() {
            self.expr_into(e, ret_base + i as u32);
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
            // tail-recursive loop helper can't thread one across iterations — so a
            // StackBuf from the enclosing scope can't be captured. Reject with a
            // clear error (not the misleading "unbound variable" the capture drop
            // would otherwise trigger). Keep it inside the loop body, or carry
            // state through a `HeapBuf`.
            if self.stacks.contains_key(r) {
                panic!(
                    "StackBuf `{r}` cannot be captured into a `for` loop; \
                     define it inside the loop body or carry state via a `HeapBuf`"
                );
            }
            if (self.vars.contains_key(r) || self.gaddrs.contains_key(r)) && seen.insert(r.clone()) {
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
        // own condition (`JUMP`'s nonzero check on j − stop) — no is-zero
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

/// Structural equality of two argument lists (small expressions, no interning),
/// via the derived `Debug` form — used to check `match_range` arms share their
/// runtime arguments ([`FnLower::lower_match_range`] fusion).
fn exprs_eq(a: &[Expr], b: &[Expr]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| format!("{x:?}") == format!("{y:?}"))
}

/// A body safe to inline: a single **tail** `return`, and no construct whose
/// lowering needs its own frame or a dispatch — a call to a user function, a
/// runtime loop, or a match (which would recurse the inliner or reload a frame
/// pointer that is no longer the callee's). `blake3` is a builtin statement and
/// is fine; `unroll`/`if` are compile-time / same-frame and recurse into.
fn body_inlinable(body: &[Stmt]) -> bool {
    matches!(body.split_last(), Some((Stmt::Return(_), rest)) if rest.iter().all(stmt_inline_safe))
}

fn stmt_inline_safe(s: &Stmt) -> bool {
    match s {
        Stmt::Let(..)
        | Stmt::Store(..)
        | Stmt::HintWitness { .. }
        | Stmt::AssertEq(..)
        | Stmt::AssertNe(..)
        | Stmt::AssertLt(..) => true,
        Stmt::Call(f, _) => f == "blake3",
        Stmt::If { then, els, .. } => then.iter().all(stmt_inline_safe) && els.iter().all(stmt_inline_safe),
        Stmt::Unroll { body, .. } => body.iter().all(stmt_inline_safe),
        // Return (non-tail), For, Match, LetMatchRange, LetTuple, CallIfNe, user Call.
        _ => false,
    }
}

/// The literal `k` when `hi` is syntactically `lo + k` (either operand
/// order) — the shape of a runtime slice, whose bounds cannot be evaluated at
/// compile time. Structural comparison via the derived `Debug` form
/// (expressions are small and have no interning).
fn plus_k(lo: &Expr, hi: &Expr) -> Option<u128> {
    let eq = |a: &Expr, b: &Expr| format!("{a:?}") == format!("{b:?}");
    match hi {
        Expr::Add(a, b) => match (a.as_ref(), b.as_ref()) {
            (Expr::Lit(k), other) | (other, Expr::Lit(k)) if eq(other, lo) => Some(*k),
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
        Expr::Call(_, args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
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
    const_arrays: &HashMap<String, Vec<u128>>,
) -> Lowered {
    let mut vars = HashMap::new();
    for (i, p) in f.params.iter().enumerate() {
        vars.insert(p.clone(), 2 + i as u32);
    }
    // Reserve [0,1] retpc/retfp, params, then return slots, then locals.
    let next = 2 + f.params.len() as u32 + f.n_ret as u32;
    let mut lowerer = FnLower {
        vars,
        stacks: HashMap::new(),
        consts: HashMap::new(),
        next,
        n_args: f.params.len() as u32,
        is_main: f.name == "main",
        code: Vec::new(),
        one_off: None,
        const_pool: HashMap::new(),
        heap_sizes: HashMap::new(),
        self_fp_off: None,
        bounds: HashMap::new(),
        gaddrs: HashMap::new(),
        fconsts: HashMap::new(),
        inline_ret: None,
        inline_stack_ret: None,
        alias: HashMap::new(),
        zero_off: None,
        pending: Vec::new(),
        queue,
        loop_ctr,
        defs,
        const_arrays,
    };
    for s in &f.body {
        lowerer.stmt(s);
    }
    if lowerer.is_main {
        lowerer.halt(); // main terminates at the sentinel pc, not by falling off
    } else if !matches!(f.body.last(), Some(Stmt::Return(_))) {
        // A function must never fall off its end into whatever code the
        // layout placed next: append the implicit bare return.
        lowerer.stmt(&Stmt::Return(vec![]));
    }
    Lowered {
        name: f.name.clone(),
        code: lowerer.code,
        frame_size: lowerer.next,
    }
}
