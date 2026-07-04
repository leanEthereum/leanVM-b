//! Lowering: each function AST is compiled to a sequence of intermediate
//! [`LOp`] instructions (fp-relative offsets, backpatched jump targets).

use super::*;

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
    /// The cell holding this function's own `fp`, materialized lazily
    /// ([`Self::self_fp`]) — local (`if`/`else`) jumps reload the frame
    /// pointer on the taken branch.
    self_fp_off: Option<Off>,
    /// Range-check product-target cells: bound `k` → the frame cell holding
    /// `g^{k-1}`, set lazily once and shared by every check of that bound.
    bounds: HashMap<u64, Off>,
    /// Hints queued to attach to the next emitted instruction.
    pending: Vec<Hint>,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
    /// The program's function definitions by name, for `Const`-parameter
    /// specialization at call sites ([`Self::specialize`]).
    defs: &'a HashMap<String, Func>,
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
            k: KVal::Const(F128::ONE),
        });
        self.one_off = Some(o);
        o
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
        let xo = self.expr(x);
        let rcells: Vec<Off> = names.iter().map(|_| self.fresh()).collect();
        self.lower_match_dispatch(xo, arms.len(), |s, j| {
            s.scoped(|s| {
                if let [rcell] = rcells.as_slice() {
                    let o = s.expr(&arms[j]);
                    s.copy(o, *rcell);
                } else {
                    let Expr::Call(f, cargs) = &arms[j] else {
                        panic!(
                            "a multi-target match_range arm must be a function call, got `{:?}`",
                            arms[j]
                        );
                    };
                    let outs = s.call(f, cargs, rcells.len());
                    for (o, &r) in outs.into_iter().zip(&rcells) {
                        s.copy(o, r);
                    }
                }
            });
        });
        for (name, &cell) in names.iter().zip(&rcells) {
            self.stacks.remove(name);
            self.consts.remove(name);
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
                        let ptr = self.expr(arr);
                        Hint::WitnessHeap {
                            name,
                            ptr,
                            lo,
                            len: hi - lo,
                        }
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
                    let ptr = self.array_ptr(arr, lo);
                    Hint::WitnessHeap { name, ptr, lo: 0, len }
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
            Expr::Lit(n) => {
                let o = self.fresh();
                self.emit(LOp::Set {
                    o,
                    k: KVal::Const(F128::new(*n as u64, (*n >> 64) as u64)),
                });
                o
            }
            Expr::Gen => {
                let o = self.fresh();
                self.emit(LOp::Set {
                    o,
                    k: KVal::Const(g_pow(1)),
                });
                o
            }
            Expr::GPow(k) => {
                let o = self.fresh();
                self.emit(LOp::Set {
                    o,
                    k: KVal::Const(g_pow_u128(*k)),
                });
                o
            }
            Expr::Var(v) => {
                if self.stacks.contains_key(v) {
                    panic!("StackBuf `{v}` used as a scalar; index it (`{v}[k]`) or pass it to blake3");
                }
                *self.vars.get(v).unwrap_or_else(|| panic!("unbound variable `{v}`"))
            }
            Expr::Add(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let o = self.fresh();
                self.emit(LOp::Xor { a: la, b: lb, c: o });
                o
            }
            Expr::Mul(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let o = self.fresh();
                self.emit(LOp::Mul { a: la, b: lb, c: o });
                o
            }
            Expr::Call(f, args) => self.call(f, args, 1)[0],
            Expr::HeapBuf(n) => {
                let arr = self.fresh();
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
                // Stack read `sa[k]`: the frame cell `base + k` directly (no deref).
                if let Some((base, size)) = self.stack_of(arr) {
                    let k = self.const_index(idx);
                    assert!(k < size, "stack index {k} out of bounds (size {size})");
                    return base + k;
                }
                // Heap read `m[arr·idx]`.
                let ptr = self.array_ptr(arr, idx);
                let dst = self.fresh();
                // Read: bind dst := m[ptr] (the array cell, written earlier).
                self.emit(LOp::Deref {
                    alpha: ptr,
                    beta: 0,
                    gamma: dst,
                    mode: DerefMode::Cell,
                });
                dst
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
    /// or `+`/`*` of those (evaluated as *integer* arithmetic: this is index
    /// space, not the field). `None` when the expression is a runtime value
    /// (which a heap slice start may be; see [`Self::blake3_operand`]).
    fn try_const_index(&self, idx: &Expr) -> Option<u32> {
        match idx {
            // `as u32` would silently wrap a ≥ 2^32 literal (e.g. `sa[2^32]` → `sa[0]`);
            // reject it so the lowered program matches the source.
            Expr::Lit(k) => Some(u32::try_from(*k).unwrap_or_else(|_| panic!("stack index {k} does not fit in u32"))),
            Expr::Var(v) => self.consts.get(v).copied(),
            Expr::Add(a, b) => Some(
                self.try_const_index(a)?
                    .checked_add(self.try_const_index(b)?)
                    .unwrap_or_else(|| panic!("stack index overflows u32")),
            ),
            Expr::Mul(a, b) => Some(
                self.try_const_index(a)?
                    .checked_mul(self.try_const_index(b)?)
                    .unwrap_or_else(|| panic!("stack index overflows u32")),
            ),
            _ => None,
        }
    }

    /// A stack index or compile-time slice bound: [`Self::try_const_index`],
    /// required to succeed.
    fn const_index(&self, idx: &Expr) -> u32 {
        self.try_const_index(idx)
            .unwrap_or_else(|| panic!("a StackBuf index must be a compile-time integer, got `{idx:?}`"))
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
                        // A heap slice: `arr` evaluates to the buffer pointer (no
                        // compile-time size to check — heap indexing never has one).
                        let ptr = self.expr(arr);
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
                    let ptr = self.array_ptr(arr, lo);
                    B3Operand::Heap { ptr, lo: 0 }
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
    fn blake3_input(&mut self, e: &Expr) -> Off {
        match self.blake3_operand(e) {
            B3Operand::Stack(o) => o,
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
                t
            }
        }
    }

    /// Evaluate `e` writing its value straight into cell `dst` — no temporary +
    /// copy for the common cases (a heap read DEREFs directly into `dst`; a
    /// constant / arithmetic emits into `dst`). Falls back to `expr` + `copy` for
    /// vars, calls, and stack reads.
    fn expr_into(&mut self, e: &Expr, dst: Off) {
        match e {
            // Heap read straight into dst (a stack read falls through to the copy).
            Expr::Index(arr, idx) if self.stack_of(arr).is_none() => {
                let ptr = self.array_ptr(arr, idx);
                self.emit(LOp::Deref {
                    alpha: ptr,
                    beta: 0,
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
            Expr::Add(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                self.emit(LOp::Xor { a: la, b: lb, c: dst });
            }
            Expr::Mul(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                self.emit(LOp::Mul { a: la, b: lb, c: dst });
            }
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

    /// Lower a call; returns the caller offsets bound to the returned values.
    fn call(&mut self, callee: &str, args: &[Expr], n_ret: usize) -> Vec<Off> {
        assert!(
            callee != "blake3",
            "blake3 is a statement: `blake3(a, b, out)` writes the digest into the 2-cell stack run `out`"
        );
        self.lower_call(callee, args, n_ret, None)
    }

    /// A *conditional* tail call: transfer to `callee(args)` iff `cond != 0`,
    /// else fall through (`JUMP`'s nonzero test, doc §7.5). The frame setup runs
    /// either way; when not taken the callee frame is just never entered. Binds
    /// no return values, so the not-taken path continues straight after it.
    fn call_cond(&mut self, callee: &str, args: &[Expr], cond: Off) {
        self.lower_call(callee, args, 0, Some(cond));
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
                Expr::Var(v) if self.consts.contains_key(v) => Expr::Lit(self.consts[v] as u128),
                other => panic!(
                    "argument for Const parameter `{p}` of `{callee}` must be a compile-time \
                     constant, got `{other:?}`"
                ),
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
            });
        }
        (name, rt_args)
    }

    fn lower_call(&mut self, callee: &str, args: &[Expr], n_ret: usize, cond: Option<Off>) -> Vec<Off> {
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
        let dsts: Vec<Off> = (0..n_ret).map(|_| self.fresh()).collect();
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
                    self.stacks.insert(name.clone(), (base, *n as u32));
                }
                // `x = other_stackbuf`: a compile-time alias of the same cell
                // run (zero instructions) — the chaining-state idiom
                // `st = sn` of an MD loop.
                Expr::Var(v) if self.stacks.contains_key(v) => {
                    let bs = self.stacks[v];
                    self.vars.remove(name);
                    self.consts.remove(name);
                    self.stacks.insert(name.clone(), bs);
                }
                _ => {
                    let o = self.expr(e);
                    self.stacks.remove(name);
                    // A literal binding is also usable as a compile-time index.
                    match e {
                        Expr::Lit(n) if u32::try_from(*n).is_ok() => {
                            self.consts.insert(name.clone(), *n as u32);
                        }
                        _ => {
                            self.consts.remove(name);
                        }
                    }
                    self.vars.insert(name.clone(), o);
                }
            },
            Stmt::LetTuple(names, f, args) => {
                let dsts = self.call(f, args, names.len());
                for (n, d) in names.iter().zip(dsts) {
                    self.consts.remove(n);
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
                    self.emit(LOp::Blake3 { a, b, c });
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
                    self.expr_into(val, base + k);
                } else {
                    // Heap store `arr[idx] = val`: assert m[arr·idx] == val (write-once).
                    let v = self.expr(val);
                    let ptr = self.array_ptr(arr, idx);
                    self.emit(LOp::Deref {
                        alpha: ptr,
                        beta: 0,
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
        if self.is_main {
            return; // a `return` in main is a no-op; main halts via the trailing sentinel jump (lower_func).
        }
        let ret_base = 2 + self.n_args;
        let vals: Vec<Off> = exprs.iter().map(|e| self.expr(e)).collect();
        for (i, v) in vals.into_iter().enumerate() {
            self.copy(v, ret_base + i as u32);
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
            if self.vars.contains_key(r) && seen.insert(r.clone()) {
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
        Expr::Add(a, b) | Expr::Mul(a, b) | Expr::Index(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        Expr::Slice(a, lo, hi) => {
            free_vars_expr(a, refs);
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
        }
        Expr::Call(_, args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        Expr::HeapBufDyn(sz) => free_vars_expr(sz, refs),
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
        Stmt::AssertEq(a, b) => {
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
        self_fp_off: None,
        bounds: HashMap::new(),
        pending: Vec::new(),
        queue,
        loop_ctr,
        defs,
    };
    for s in &f.body {
        lowerer.stmt(s);
    }
    if lowerer.is_main {
        lowerer.halt(); // main terminates at the sentinel pc, not by falling off
    }
    Lowered {
        name: f.name.clone(),
        code: lowerer.code,
        frame_size: lowerer.next,
    }
}
