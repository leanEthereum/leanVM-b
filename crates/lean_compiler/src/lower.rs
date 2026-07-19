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
    Some(GAddr {
        base,
        exp: a.exp.checked_add(b.exp)?,
    })
}

/// Cap on a `β`-folded exponent: the operand g-power table is sized to the
/// largest immediate, so beyond this a huge constant index falls back to a
/// materialized pointer instead of inflating that table.
const FOLD_MAX: u128 = 1 << 16;

/// A deferred stack-cell store: the cell is a copy of another cell, or a zero.
/// Recorded instead of emitting the `MUL`/`SET`, and forwarded to the source at
/// each use ([`FnLower::word_src`], [`FnLower::chunk_src`]) — so `BLAKE3`,
/// which addresses its four two-cell input chunks independently, reads them in
/// place without assembling copies.
#[derive(Clone, Copy)]
enum Alias {
    Cell(Off),
    /// A compile-time constant: forwarded at its uses to the pooled cell
    /// holding that value (`const_cell`), so a constant stored into a
    /// `blake3` operand cell — the `obs`/`squeeze` tag words, padding
    /// halves — costs ONE `SET` per distinct value per function, not one
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

struct FnLower<'a> {
    vars: HashMap<String, Off>,
    /// `StackBuf` bindings: name → (base offset, size). The `size` cells
    /// `base..base+size` are consecutive frame cells (so a size-4 one, or a
    /// 4-cell slice of a larger one, is a direct `blake3` operand). Kept
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
    /// The cell holding this function's own `fp`, materialized lazily
    /// ([`Self::self_fp`]) — local (`if`/`else`) jumps reload the frame
    /// pointer on the taken branch.
    self_fp_off: Option<Off>,
    /// Range-check product-target cells: bound `k` → the frame cell holding
    /// `g^{k-1}`, set lazily once and shared by every check of that bound.
    bounds: HashMap<u64, Off>,
    /// Constant cells: field value (as bits) → the frame cell holding it, SET
    /// lazily once per distinct constant ([`Self::const_cell`]). Cells are
    /// write-once and read-many, so one `SET` serves every use in scope.
    const_cells: HashMap<u64, Off>,
    /// Variables bound to a symbolic g-address ([`GAddr`]) — index cursors and
    /// shifted pointers, kept virtual so their offsets fold into `DEREF`'s `β`.
    gaddrs: HashMap<String, GAddr>,
    /// Variables bound to a compile-time *field* constant that isn't a g-power
    /// (e.g. a running weight `CHAIN_LENGTH^i`). Kept virtual — folded through
    /// constant field arithmetic and materialized (one `SET`) only when used.
    fconsts: HashMap<String, F64>,
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
    /// A cached frame cell holding `0` (for forwarded zero words), set lazily.
    zero_off: Option<Off>,
    /// A cached pair of CONSECUTIVE zero cells (a forwarded zero `BLAKE3`
    /// chunk — e.g. a hash-chain padding half), set lazily.
    zero2_off: Option<Off>,
    /// Hints queued to attach to the next emitted instruction.
    pending: Vec<Hint>,
    /// Active `@inline` expansion stack. Nested inline helpers are allowed,
    /// but direct or indirect recursion would otherwise recurse forever in
    /// the compiler.
    inline_calls: Vec<String>,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
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
        if let Some(&o) = self.const_cells.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set { o, k: KVal::Const(v) });
        self.const_cells.insert(key, o);
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
            k: KVal::Const(F64::ZERO),
        });
        self.zero_off = Some(o);
        o
    }

    /// Two CONSECUTIVE frame cells both holding `0`, set lazily once — the
    /// source for a forwarded all-zero `BLAKE3` chunk (cells `base`, `base+1`).
    // Retained for a possible return to two-cell chunk forwarding; a 128-bit
    // chunk is now one cell, so `blake3_input` uses `word_src` directly.
    #[allow(dead_code)]
    fn zero_pair(&mut self) -> Off {
        if let Some(o) = self.zero2_off {
            return o;
        }
        let o = self.alloc_stack(2);
        for k in 0..2 {
            self.emit(LOp::Set {
                o: o + k,
                k: KVal::Const(F64::ZERO),
            });
        }
        self.zero2_off = Some(o);
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
            _ => self.try_field_const(val).map(Alias::Const),
        }
    }

    /// Terminate `main`: jump to the halt sentinel `g^{B-1}` with `fp = g^0`.
    /// The cell holding `1` doubles as the (nonzero) jump condition and the new
    /// frame pointer `g^0`; the dest cell holds `g^{B-1}` (doc §e2e, final state).
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
            self.self_fp_off,
            self.bounds.clone(),
            self.const_cells.clone(),
            self.gaddrs.clone(),
            self.fconsts.clone(),
            self.alias.clone(),
            self.zero_off,
            self.zero2_off,
        );
        f(self);
        // A hint pending at the end of a branch (e.g. a trailing
        // `hint_witness`) must not attach to whatever instruction follows the
        // join — that would fire it unconditionally. Absorb it with a no-op.
        if !self.pending.is_empty() {
            let o = self.fresh();
            self.emit(LOp::Set {
                o,
                k: KVal::Const(F64::ZERO),
            });
        }
        (
            self.vars,
            self.stacks,
            self.consts,
            self.self_fp_off,
            self.bounds,
            self.const_cells,
            self.gaddrs,
            self.fconsts,
            self.alias,
            self.zero_off,
            self.zero2_off,
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
        // identical runtime args (differing only in `Const` args — the usual
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
                    .all(|(_, rt, ext)| ext.iter().all(|x| !x) && exprs_eq(rt, rt0))
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
        self.emit(LOp::Jump {
            oc: one,
            od: d,
            of: sfp,
        });

        // Trampoline: slot j enters `callees[j]` with fp = nfp; the callee's own
        // `return` jumps to retpc (the join) in the caller frame.
        self.patch_local(kset, self.code.len());
        for callee in callees {
            let c = self.fresh();
            self.emit(LOp::Set {
                o: c,
                k: KVal::Entry(callee.clone()),
            });
            self.emit(LOp::Jump {
                oc: one,
                od: c,
                of: nfp,
            });
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

    /// The frame cell holding `g^{k-1}` — the range-check product target — set
    /// lazily once per distinct bound `k` and shared by that bound's checks.
    fn bound_cell(&mut self, k: u64) -> Off {
        if let Some(&o) = self.bounds.get(&k) {
            return o;
        }
        let o = self.fresh();
        self.emit(LOp::Set {
            o,
            k: KVal::Const(g_pow_u128((k - 1) as u128).into()),
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
    /// Then `e + f ≡ k-1 (mod 2^64-1)` with `e, f < 2^h`, and since a negative
    /// `k-1-e` wraps to `≈ 2^64 ≫ 2^h`, this forces `e ≤ k-1` — for ANY memory
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
            Expr::Gen => self.const_cell(g_pow(1).into()),
            Expr::GPow(k) => self.const_cell(g_pow_u128(*k).into()),
            Expr::GenPow(e) => {
                let k = self.gpow_exp(e);
                self.const_cell(g_pow_u128(k).into())
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
                if self.try_field_const(a) == Some(F64::ZERO) {
                    return self.expr(b);
                }
                if self.try_field_const(b) == Some(F64::ZERO) {
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
                if self.try_field_const(a) == Some(F64::ONE) {
                    return self.expr(b);
                }
                if self.try_field_const(b) == Some(F64::ONE) {
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
                assert_eq!(args.len(), 3, "hint_log2_ceil(bits, nbits, floor)");
                let bits_ptr = self.expr(&args[0]);
                let nbits = self.const_index(&args[1]);
                let floor = self.const_index(&args[2]);
                let dst = self.fresh();
                self.pending.push(Hint::Log2Ceil {
                    bits_ptr,
                    dst,
                    nbits,
                    floor,
                });
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
    /// arguments such as `mul_ext(a, [1, 0, 0], out)`.
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
            let mut acc = F64::ONE;
            for _ in 0..k {
                acc *= bc;
            }
            return self.const_cell(acc);
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

    /// The field value of `e` when it is a trivial compile-time constant (a
    /// literal, a literal-bound name, or `GEN ** 0`), for the `x*1`/`x+0`
    /// arithmetic identities and the `== 0` test of [`Self::lower_if`].
    fn try_lit(&self, e: &Expr) -> Option<u64> {
        match e {
            Expr::Lit(n) => u64::try_from(*n).ok(),
            Expr::Var(v) => self.consts.get(v).map(|&n| n as u64),
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
            Expr::Var(v) => pow2(*self.consts.get(v)? as u128).and_then(cap),
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

    /// A `blake3` operand as a four-word stack run. A heap slice is bridged into
    /// a fresh stack run — one `DEREF` per cell
    /// (`m[ptr·g^{lo+k}] == m[fp+t+k]`, the `β` immediate doing the pointer
    /// offset). The heap cells must already be written.
    fn blake3_input(&mut self, e: &Expr) -> Off {
        match self.blake3_operand(e) {
            B3Operand::Stack(o) => {
                self.materialize_run(o, 4);
                o
            }
            B3Operand::Heap { ptr, lo } => {
                let t = self.alloc_stack(4);
                for k in 0..4 {
                    self.emit(LOp::Deref {
                        alpha: ptr,
                        beta: lo + k,
                        gamma: t + k,
                        mode: DerefMode::Cell,
                    });
                }
                t
            }
        }
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

    /// Resolve a three-word extension operand. Only StackBuf values and slices
    /// are accepted because the instruction operands are compile-time FP offsets.
    fn ext_operand(&mut self, e: &Expr) -> Off {
        let base = match e {
            Expr::Var(_) => {
                let (base, size) = self
                    .stack_of(e)
                    .expect("extension operands must be StackBuf values or slices");
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
        self.materialize_run(base, 3);
        base
    }

    /// The base of the two-cell chunk holding the values of stack cells `o`,
    /// `o+1`, following recorded copy / zero aliases to their real source when
    /// the pair stays CONTIGUOUS there (so `BLAKE3` reads the source cells
    /// directly and the assembling copies are never emitted): a pair aliasing
    /// adjacent cells `(s, s+1)` forwards to `s`, an all-zero pair to the
    /// shared zero pair. A pair that does not forward as a unit (mixed or
    /// non-adjacent sources) is materialized into its own cells instead.
    #[allow(dead_code)]
    fn chunk_src(&mut self, o: Off) -> Off {
        match (self.alias.get(&o).copied(), self.alias.get(&(o + 1)).copied()) {
            (None, None) => o,
            (Some(Alias::Cell(s0)), Some(Alias::Cell(s1))) if s1 == s0 + 1 => self.chunk_src(s0),
            (Some(Alias::Const(a)), Some(Alias::Const(b))) if a.is_zero() && b.is_zero() => self.zero_pair(),
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

    /// Evaluate `e` writing its value straight into cell `dst` — no temporary +
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
                k: KVal::Const(g_pow(1).into()),
            }),
            Expr::GPow(k) => self.emit(LOp::Set {
                o: dst,
                k: KVal::Const(g_pow_u128(*k).into()),
            }),
            Expr::GenPow(e) => self.emit(LOp::Set {
                o: dst,
                k: KVal::Const(g_pow_u128(self.gpow_exp(e)).into()),
            }),
            Expr::Pow(b, e) => {
                let v = self.pow_expr(b, e);
                self.copy(v, dst);
            }
            Expr::Add(a, b) => {
                // Identity fold (see the `expr` Add arm): `x + 0` copies `x`.
                if self.try_field_const(a) == Some(F64::ZERO) {
                    self.expr_into(b, dst);
                } else if self.try_field_const(b) == Some(F64::ZERO) {
                    self.expr_into(a, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Xor { a: la, b: lb, c: dst });
                }
            }
            Expr::Mul(a, b) => {
                // Identity fold: `x * 1` copies `x`.
                if self.try_field_const(a) == Some(F64::ONE) {
                    self.expr_into(b, dst);
                } else if self.try_field_const(b) == Some(F64::ONE) {
                    self.expr_into(a, dst);
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
    /// of the buffer sits at `arr·g^k`). A constant g-power `idx`, or a
    /// constant g-power *factor* of it, folds into the `beta` immediate, so
    /// only a runtime factor costs a pointer `MUL` (and a wholly constant
    /// index costs nothing at all).
    fn array_ptr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        if let Some(k) = self.try_gpow_index(idx) {
            return (self.expr(arr), k);
        }
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
    /// `+`/`*` of those evaluated in the field (XOR / `K`-mul). `None` for a
    /// runtime value, a literal exceeding the 64-bit word, or a compile-time
    /// *integer* op (`//`/`%` are index-only).
    fn try_field_const(&self, e: &Expr) -> Option<F64> {
        match e {
            // A source value literal fills one F64 word.
            Expr::Lit(n) => Some(lit_field(*n)),
            Expr::Gen => Some(g_pow(1).into()),
            Expr::GPow(k) => Some(g_pow_u128(*k).into()),
            Expr::GenPow(e) => Some(g_pow_u128(self.try_const_index(e)? as u128).into()),
            Expr::Var(v) => self.fconsts.get(v).copied().or_else(|| match self.gaddrs.get(v) {
                Some(GAddr { base: None, exp }) => Some(g_pow_u128(*exp).into()),
                _ => None,
            }),
            Expr::Add(a, b) => Some(self.try_field_const(a)? + self.try_field_const(b)?),
            Expr::Mul(a, b) => Some(self.try_field_const(a)? * self.try_field_const(b)?),
            // A constant-array element `NAME[i]` as a field value, or `len(NAME)`.
            Expr::Index(..) => self.const_array_elem(e),
            Expr::Call(..) => self.const_len(e).map(|n| F64(n as u64)),
            // `b ** e` as a field constant (constant base, compile-time exponent).
            Expr::Pow(b, e) => {
                let bc = self.try_field_const(b)?;
                let k = self.try_const_index(e)?;
                let mut acc = F64::ONE;
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
                self.emit(LOp::Set {
                    o: k,
                    k: KVal::Const(g_pow_u128(exp).into()),
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
        self.emit(LOp::Set {
            o: k,
            k: KVal::Const(g_pow_u128(extra).into()),
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
        // a heap cell — cell k lives at `buf · g^k` — and would deref a wild
        // address at proving time. Reject it here, where the source is known.
        if self.gaddr_of(idx).is_none()
            && let Some(c) = self.try_field_const(idx)
        {
            panic!(
                "heap index `{arr:?}[{idx:?}]` folds to the field constant {:#x}, not a g-power while inlining {:?} — heap cell k is addressed as `buf[GEN ** k]` (did an integer index leak in from a StackBuf conversion?)",
                c.0, self.inline_calls,
            );
        }
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
        // Fall back to the constant-g-power-factor fold (a runtime index still
        // materializes the pointer `MUL`, with any constant factor in `β`).
        self.array_ptr(arr, idx)
    }

    /// Consume the [`RetBind`] a single-value inlined tail return recorded,
    /// for a call in EXPRESSION position (embedded in arithmetic, a store
    /// RHS, a single-target match arm): there is no name to alias-bind, so an
    /// aliased return materializes into a plain cell (free for a var / an
    /// exp-0 g-address; one `MUL` for a shifted pointer). `dst` is the call's
    /// destination cell — already written by a real call or a plain-scalar
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
        self.lower_call(callee, args, physical.len(), None, Some(&physical));
        self.inline_stack_ret = Some(binds);
        logical
    }

    /// Evaluate `callee(args)` into `dsts` — inlining the callee when it is
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
        self.inline_calls.push(callee.to_string());
        for s in &body {
            self.stmt(s);
        }
        let popped = self.inline_calls.pop();
        debug_assert_eq!(popped.as_deref(), Some(callee));
        self.inline_ret = saved_ret;
        (self.vars, self.stacks, self.consts, self.gaddrs, self.fconsts) = saved;
        true
    }

    /// A *conditional* tail call: transfer to `callee(args)` iff `cond != 0`,
    /// else fall through (`JUMP`'s nonzero test, doc §JUMP (sec:tab-jump)). The frame setup runs
    /// either way; when not taken the callee frame is just never entered. Binds
    /// no return values, so the not-taken path continues straight after it.
    fn call_cond(&mut self, callee: &str, args: &[Expr], cond: Off) {
        self.lower_call(callee, args, 0, Some(cond), None);
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
    /// cells — sparing the caller a temp-then-copy.
    fn lower_call(
        &mut self,
        callee: &str,
        args: &[Expr],
        n_ret: usize,
        cond: Option<Off>,
        dsts_in: Option<&[Off]>,
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

        let n_args = arg_offs.len() as u32;
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
                // `x = [a, b, …]`: an initialized StackBuf — allocate the run
                // and write each element in place (each write is the stack-store
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
                    self.vars.remove(name);
                    self.consts.remove(name);
                    self.gaddrs.remove(name);
                    self.fconsts.remove(name);
                    self.stacks.insert(name.clone(), (base, es.len() as u32));
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
                        self.fconsts.insert(name.clone(), lit_field(k as u128));
                    } else if let Expr::Call(cf, cargs) = e
                        && self.defs.contains_key(cf)
                    {
                        // A bare `name = call(...)` of a user function: bind per
                        // the inlined return's RetBind — alias its StackBuf run
                        // or folded g-address at zero copies (the `cvb = obs(...)`
                        // / advanced-cursor idiom), else (a plain scalar, or a
                        // real call) bind the dst cell. Embedded calls do NOT
                        // take this path: `expr` materializes theirs
                        // ([`Self::take_inline_ret_cell`]).
                        self.inline_stack_ret = None;
                        let o = self.call(cf, cargs, 1)[0];
                        self.vars.remove(name);
                        self.stacks.remove(name);
                        self.gaddrs.remove(name);
                        self.fconsts.remove(name);
                        match self.inline_stack_ret.take().and_then(|b| b.into_iter().next()) {
                            Some(RetBind::Stack(base, size)) => {
                                self.stacks.insert(name.clone(), (base, size));
                            }
                            Some(RetBind::Gaddr(ga)) => {
                                self.gaddrs.insert(name.clone(), ga);
                            }
                            _ => {
                                self.vars.insert(name.clone(), o);
                            }
                        }
                    } else {
                        let o = self.expr(e);
                        self.vars.remove(name);
                        self.stacks.remove(name);
                        self.gaddrs.remove(name);
                        self.fconsts.remove(name);
                        self.vars.insert(name.clone(), o);
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
                    self.consts.remove(n);
                    self.vars.remove(n);
                    self.stacks.remove(n);
                    self.gaddrs.remove(n);
                    self.fconsts.remove(n);
                    match binds.as_ref().and_then(|b| b.get(i).copied()) {
                        Some(RetBind::Stack(base, size)) => {
                            self.stacks.insert(n.clone(), (base, size));
                        }
                        Some(RetBind::Gaddr(ga)) => {
                            self.gaddrs.insert(n.clone(), ga);
                        }
                        _ => {
                            self.vars.insert(n.clone(), *d);
                        }
                    }
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
                self.pending.push(Hint::Print {
                    label: label.clone(),
                    cell,
                });
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
                // lands in the existing 4-cell run `out` (write-once: if `out`
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
                        B3Operand::Heap { ptr, lo } => (self.alloc_stack(4), Some((ptr, lo))),
                    };
                    self.materialize_run(c, 4);
                    self.emit(LOp::Blake3 { a, b, c });
                    if let Some((ptr, lo)) = heap_out {
                        for k in 0..4 {
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
                if matches!(f.as_str(), "add_ext" | "sub_ext" | "mul_ext" | "div_ext") {
                    assert_eq!(args.len(), 3, "{f}(a, b, out) takes three extension buffers");
                    let a = self.ext_operand(&args[0]);
                    let b = self.ext_operand(&args[1]);
                    let c = self.ext_operand(&args[2]);
                    match f.as_str() {
                        "add_ext" | "sub_ext" => self.emit(LOp::AddExt { a, b, c }),
                        "mul_ext" => self.emit(LOp::MulExt { a, b, c }),
                        // c = a / b is constrained by c * b = a; the VM's
                        // write-once deduction fills c when it is unset.
                        "div_ext" => self.emit(LOp::MulExt { a: c, b, c: a }),
                        _ => unreachable!(),
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
            // Each returned value is bound into the caller independently, exactly
            // as a `let name = <that expr>` would: a `StackBuf` or a folded
            // g-address hands over its run/pointer (alias, not copies — allocated
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
            if let Some(&(_, size)) = self.stacks.get(r) {
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
        let mut ext_params = vec![false; params.len()];
        let capture_start = 1 + usize::from(runtime);
        for (i, name) in captures.iter().enumerate() {
            ext_params[capture_start + i] = self.stacks.get(name).is_some_and(|(_, size)| *size == 3);
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

/// Structural equality of two argument lists (small expressions, no interning),
/// via the derived `Debug` form — used to check `match_range` arms share their
/// runtime arguments ([`FnLower::lower_match_range`] fusion).
fn exprs_eq(a: &[Expr], b: &[Expr]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| format!("{x:?}") == format!("{y:?}"))
}

/// A body safe to inline: a single **tail** `return`, and no construct whose
/// lowering needs its own frame or a dispatch — a non-inline user call, a
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
            matches!(f.as_str(), "blake3" | "add_ext" | "sub_ext" | "mul_ext" | "div_ext")
                || defs.get(f).is_some_and(|d| d.inline)
        }
        Stmt::If { then, els, .. } => {
            then.iter().all(|s| stmt_inline_safe(s, defs)) && els.iter().all(|s| stmt_inline_safe(s, defs))
        }
        Stmt::Unroll { body, .. } => body.iter().all(|s| stmt_inline_safe(s, defs)),
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
        vars,
        stacks: param_stacks,
        consts: HashMap::new(),
        next,
        n_args: param_cells,
        return_shapes: f.return_shapes.clone(),
        is_main: f.name == "main",
        code: Vec::new(),
        one_off: None,
        heap_sizes: HashMap::new(),
        self_fp_off: None,
        bounds: HashMap::new(),
        const_cells: HashMap::new(),
        gaddrs: HashMap::new(),
        fconsts: HashMap::new(),
        inline_ret: None,
        inline_stack_ret: None,
        alias: HashMap::new(),
        zero_off: None,
        zero2_off: None,
        pending: Vec::new(),
        inline_calls: Vec::new(),
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
