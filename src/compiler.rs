//! A minimal compiler from a Python-like zkDSL to the v1 ISA (`cpu::Op`).
//!
//! Scope (deliberately small): immutable variables, field arithmetic (`+` =
//! `XOR`, `*` = `MUL_NATIVE`), function calls with multiple returns,
//! `assert a == b`, and `mul_range` loops carried out *in the exponent* (the
//! counter is `gᵏ`, advanced by one ×g per iteration). No mutable variables, no
//! `Const` parameters, no `match`/`match_range`.
//!
//! ## Calling convention
//!
//! A frame is fp-relative; operand `gᵏ` names cell `m[fp·gᵏ]`. Layout:
//!
//! | offset | contents |
//! |--------|----------|
//! | 0      | `retpc` — return program counter |
//! | 1      | `retfp` — caller frame pointer |
//! | 2 .. 2+nargs            | arguments |
//! | 2+nargs .. 2+nargs+nret | return values |
//! | rest                    | locals / temporaries / frame-pointer hints |
//!
//! A **call** is a `DEREF`-then-`JUMP`: the callee frame pointer is a prover
//! hint (a fresh, disjoint cell — write-once memory makes an unconstrained cell
//! prover-chosen, exactly like leanVM's `RequestMemory`); the args and `retfp`
//! are stored with `DEREF` (`Cell`/`Fp`), then a `DEREF`(`Pc`) stores the return
//! address `g²·pc` — the instruction two ahead, i.e. the resume point right
//! after the call `JUMP`. The callee **returns** with one `JUMP[one, 0, 1]`.
//!
//! A **`mul_range` loop** lowers to a recursive helper `loop(i)` that tests `i == g^hi`
//! (an is-zero gadget: prover-hinted inverse + a few degree-2 constraints, as in
//! leanVM) and, while not done, runs the body and recurses on `i·g`. The
//! termination test reuses the return `JUMP` as its taken branch.
//!
//! Compilation produces a [`cpu::Program`] — the bytecode plus the prover's
//! allocation hints. Running it ([`cpu::Program::execute`]) interprets the
//! lowered program to produce the write-once memory image (the witness).

use std::collections::HashMap;

use crate::cpu::{DerefMode, Op, Program};
use crate::field::{F128, g_pow};

// ----------------------------------------------------------------------------
// AST
// ----------------------------------------------------------------------------

/// An expression. Arithmetic is the field's own: `+` is `XOR`, `*` is `MUL`.
#[derive(Clone, Debug)]
pub enum Expr {
    /// Integer / field literal: a `u128` taken as the field element's 128 bits,
    /// `F128::new(n_lo, n_hi)`. Small values behave like integers (`5` is
    /// `F128::new(5, 0)`); a full 128-bit value names an arbitrary field
    /// constant (e.g. a Fibonacci result computed in the exponent).
    Lit(u128),
    /// The generator `g` — written `GEN` in source. A logical index `i` is
    /// carried "in the exponent" as `gⁱ`, so `GEN` is the unit step and
    /// `GEN ** k` is `gᵏ`.
    Gen,
    /// The field constant `g^k` (`GEN ** k`, and used by loop lowering). The
    /// exponent is a `u128`, so an index can be a large logical value — e.g. a
    /// Fibonacci number carried in the exponent.
    GPow(u128),
    /// A variable in scope.
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    /// Single-return function call in expression position.
    Call(String, Vec<Expr>),
    /// `HeapBuf(n)` — allocate a heap buffer of `n` cells; evaluates to its pointer.
    HeapBuf(u64),
    /// `StackBuf(n)` — allocate `n` *consecutive* frame (stack) cells, bound as a
    /// stack value. Its cells `sa[0..n]` are written/read directly (no heap deref),
    /// and a size-2 `StackBuf` is a valid `blake3` operand (the two 128-bit words
    /// of a 256-bit value live in the two consecutive cells). See [`FnLower`].
    StackBuf(u64),
    /// `arr[idx]` — read a cell. For a heap `arr` (a pointer): `m[arr·idx]` (idx a
    /// g-power). For a [`Expr::StackBuf`]: the frame cell `base + idx` (idx a
    /// small integer literal), read directly.
    Index(Box<Expr>, Box<Expr>),
}

/// A statement.
#[derive(Clone, Debug)]
pub enum Stmt {
    /// `x = expr` (immutable binding).
    Let(String, Expr),
    /// `x, y, … = f(args)` — call with multiple returns.
    LetTuple(Vec<String>, String, Vec<Expr>),
    /// `assert a == b` — a proof-enforced equality.
    AssertEq(Expr, Expr),
    /// `f(args)` as a statement (returns discarded).
    Call(String, Vec<Expr>),
    /// `arr[idx] = value` — store into a heap cell (write-once).
    Store(Expr, Expr, Expr),
    /// `for i in mul_range(GEN**lo, GEN**hi): body` — the counter is carried in
    /// the exponent as `gⁱ`, starting at the `start` element `g^lo` and advancing
    /// by `×g` each iteration until it reaches the `stop` element `g^hi` (the
    /// terminal bound, not itself executed). The step is always `×g`: `mul_range`
    /// names its bounds as field elements (e.g. `mul_range(1, GEN ** 10)` runs 10
    /// times), so the multiplicative walk is explicit and there is no step knob.
    For {
        var: String,
        lo: u64,
        hi: u64,
        body: Vec<Stmt>,
    },
    /// `return e, …` (a bare `return` is the empty vector).
    Return(Vec<Expr>),
    /// Internal (loop lowering): `if lhs != rhs: callee(args)` — a tail call on
    /// the not-equal branch, dispatched by `JUMP`'s nonzero test.
    CallIfNe(Expr, Expr, String, Vec<Expr>),
}

/// A function definition. `main` is the entry point.
#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub params: Vec<String>,
    pub n_ret: usize,
    pub body: Vec<Stmt>,
}

/// A whole program: a set of functions including `main`.
#[derive(Clone, Debug)]
pub struct Ast {
    pub funcs: Vec<Func>,
}

// ----------------------------------------------------------------------------
// Lowered (intermediate) instructions
// ----------------------------------------------------------------------------

type Off = u32;

/// A `SET` immediate: a field constant, or a function entry address resolved
/// once entry program counters are fixed.
#[derive(Clone, Debug)]
enum KVal {
    Const(F128),
    Entry(String),
    /// The halt sentinel pc `g^{B-1}` (last bytecode slot), fixed once the
    /// padded bytecode size `B` is known. `main` jumps here to terminate.
    EndSentinel,
}

#[derive(Clone, Debug)]
struct LInstr {
    op: LOp,
    /// Prover hints applied (in order) *before* this instruction during witness
    /// generation.
    hints: Vec<Hint>,
}

#[derive(Clone, Debug)]
enum LOp {
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
    /// `BLAKE3`: the two 256-bit inputs `a = (a, a+1)`, `b = (b, b+1)` and output
    /// `c = (c, c+1)` each occupy two CONSECUTIVE frame cells (the op reads/writes
    /// the operand and its successor `×g`).
    Blake3 {
        a: Off,
        b: Off,
        c: Off,
    },
}

#[derive(Clone, Debug)]
enum Hint {
    /// `m[fp·g^ptr] = g^{fresh base}` — a fresh, disjoint frame for `callee`.
    AllocFrame { ptr: Off, callee: String },
    /// `m[fp·g^ptr] = g^{fresh base}` — a fresh, disjoint heap region of `size`
    /// cells (a `HeapBuf(size)`), addressed by g-power offsets from the pointer.
    AllocBuffer { ptr: Off, size: u32 },
}

struct Lowered {
    name: String,
    code: Vec<LInstr>,
    frame_size: u32,
}

// ----------------------------------------------------------------------------
// Per-function lowering
// ----------------------------------------------------------------------------

struct FnLower<'a> {
    vars: HashMap<String, Off>,
    /// `StackBuf` bindings: name → (base offset, size). The `size` cells
    /// `base..base+size` are consecutive frame cells (so a size-2 one is a direct
    /// `blake3` operand). Kept separate from `vars` since a stack value is a run of
    /// cells, not a single scalar.
    stacks: HashMap<String, (Off, u32)>,
    next: Off,
    n_args: u32,
    is_main: bool,
    code: Vec<LInstr>,
    one_off: Option<Off>,
    /// Hints queued to attach to the next emitted instruction.
    pending: Vec<Hint>,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
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

    /// A stack index must be a plain integer literal.
    fn const_index(&self, idx: &Expr) -> u32 {
        match idx {
            // `as u32` would silently wrap a ≥ 2^32 literal (e.g. `sa[2^32]` → `sa[0]`);
            // reject it so the lowered program matches the source.
            Expr::Lit(k) => {
                u32::try_from(*k).unwrap_or_else(|_| panic!("StackBuf index {k} does not fit in u32"))
            }
            _ => panic!("a StackBuf index must be an integer literal, got `{idx:?}`"),
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
                self.emit(LOp::Deref { alpha: ptr, beta: 0, gamma: dst, mode: DerefMode::Cell });
            }
            Expr::Lit(n) => {
                self.emit(LOp::Set { o: dst, k: KVal::Const(F128::new(*n as u64, (*n >> 64) as u64)) });
            }
            Expr::Gen => self.emit(LOp::Set { o: dst, k: KVal::Const(g_pow(1)) }),
            Expr::GPow(k) => self.emit(LOp::Set { o: dst, k: KVal::Const(g_pow_u128(*k)) }),
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
            "blake3 returns a size-2 StackBuf; bind it: `out = blake3(a, b)`"
        );
        self.lower_call(callee, args, n_ret, None)
    }

    /// `c0, c1 = blake3(a0, a1, b0, b1)` — the VM `BLAKE3` of the two 256-bit
    /// inputs `a = (a0, a1)` and `b = (b0, b1)`, output `c = (c0, c1)`. The op
    /// reads each operand at two *consecutive* frame cells, so the four input
    /// words are copied into consecutive slots and the output takes two fresh
    /// consecutive slots. Returns the two output offsets `(c0, c0+1)`.
    /// `out = blake3(a, b)` — `a` and `b` are size-2 `StackBuf`s (each a 256-bit
    /// value in two consecutive frame cells). Reads the operands *in place* and
    /// writes the digest to a fresh size-2 `StackBuf`, so nothing is copied. A
    /// self-hash `blake3(h, h)` passes the same base for both operands (`a == b`),
    /// aliasing one pair into both inputs. Returns the output stack `(base, 2)`.
    fn blake3_call(&mut self, args: &[Expr]) -> (Off, u32) {
        assert_eq!(args.len(), 2, "blake3(a, b) takes two size-2 StackBufs");
        let (a_base, a_size) = self
            .stack_of(&args[0])
            .expect("blake3 operand `a` must be a StackBuf");
        let (b_base, b_size) = self
            .stack_of(&args[1])
            .expect("blake3 operand `b` must be a StackBuf");
        assert_eq!(a_size, 2, "blake3 operand `a` must have size 2");
        assert_eq!(b_size, 2, "blake3 operand `b` must have size 2");
        let out = self.alloc_stack(2);
        self.emit(LOp::Blake3 { a: a_base, b: b_base, c: out });
        (out, 2)
    }

    /// A *conditional* tail call: transfer to `callee(args)` iff `cond != 0`,
    /// else fall through (`JUMP`'s nonzero test, doc §7.5). The frame setup runs
    /// either way; when not taken the callee frame is just never entered. Binds
    /// no return values, so the not-taken path continues straight after it.
    fn call_cond(&mut self, callee: &str, args: &[Expr], cond: Off) {
        self.lower_call(callee, args, 0, Some(cond));
    }

    fn lower_call(&mut self, callee: &str, args: &[Expr], n_ret: usize, cond: Option<Off>) -> Vec<Off> {
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
                    self.stacks.insert(name.clone(), (base, *n as u32));
                }
                // `x = blake3(a, b)`: bind the size-2 output stack.
                Expr::Call(f, args) if f == "blake3" => {
                    let (base, size) = self.blake3_call(args);
                    self.vars.remove(name);
                    self.stacks.insert(name.clone(), (base, size));
                }
                _ => {
                    let o = self.expr(e);
                    self.stacks.remove(name);
                    self.vars.insert(name.clone(), o);
                }
            },
            Stmt::LetTuple(names, f, args) => {
                let dsts = self.call(f, args, names.len());
                for (n, d) in names.iter().zip(dsts) {
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
            Stmt::Call(f, args) => {
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
            Stmt::For {
                var,
                lo,
                hi,
                body,
            } => self.lower_for(var, *lo, *hi, body),
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
    fn lower_for(&mut self, var: &str, lo: u64, hi: u64, body: &[Stmt]) {
        let id = *self.loop_ctr;
        *self.loop_ctr += 1;
        let loop_name = format!("__loop{id}");

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

        // The helper takes the counter, then the captures. `cap_args` builds an
        // argument list (a leading expression, then the captures by name).
        let mut params = vec![var.to_string()];
        params.extend(captures.iter().cloned());
        let cap_args = |first: Expr| {
            let mut a = vec![first];
            a.extend(captures.iter().map(|c| Expr::Var(c.clone())));
            a
        };

        // loop(i, caps): run the body, advance to j = i·g, and tail-recurse
        // while j != g^hi. The exit test is the recursive call's own condition
        // (`JUMP`'s nonzero check on j − g^hi) — no is-zero gadget, no inverse
        // hint, and no extra call beyond the one a loop iteration already makes.
        let next_var = format!("__next{id}");
        let next = Expr::Mul(Box::new(Expr::Var(var.to_string())), Box::new(Expr::Gen));
        let mut loop_body: Vec<Stmt> = body.to_vec();
        loop_body.push(Stmt::Let(next_var.clone(), next));
        loop_body.push(Stmt::CallIfNe(
            Expr::Var(next_var.clone()),
            Expr::GPow(hi as u128),
            loop_name.clone(),
            cap_args(Expr::Var(next_var)),
        ));
        loop_body.push(Stmt::Return(vec![]));
        self.queue.push(Func {
            name: loop_name.clone(),
            params,
            n_ret: 0,
            body: loop_body,
        });

        // Enter the loop iff it runs at least once. `lo` and `hi` are known now,
        // so an empty range (`lo == hi`) compiles to nothing.
        if lo != hi {
            self.call(&loop_name, &cap_args(Expr::GPow(lo as u128)), 0);
        }
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
        Expr::Call(_, args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
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
        Stmt::For { var, body, .. } => {
            bound.insert(var.clone());
            body.iter().for_each(|s| free_vars_stmt(s, refs, bound));
        }
    }
}

/// Lower one function to its instruction list and frame size.
fn lower_func(f: &Func, queue: &mut Vec<Func>, loop_ctr: &mut usize) -> Lowered {
    let mut vars = HashMap::new();
    for (i, p) in f.params.iter().enumerate() {
        vars.insert(p.clone(), 2 + i as u32);
    }
    // Reserve [0,1] retpc/retfp, params, then return slots, then locals.
    let next = 2 + f.params.len() as u32 + f.n_ret as u32;
    let mut lowerer = FnLower {
        vars,
        stacks: HashMap::new(),
        next,
        n_args: f.params.len() as u32,
        is_main: f.name == "main",
        code: Vec::new(),
        one_off: None,
        pending: Vec::new(),
        queue,
        loop_ctr,
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

// ----------------------------------------------------------------------------
// Parser — a minimal indentation-based Python-like surface syntax
// ----------------------------------------------------------------------------

/// Parse Python-like source into an [`Ast`]. Supports `def`, immutable
/// assignment (`x = …`, `a, b = f(…)`), `assert a == b`, `for i in
/// mul_range(GEN**lo, GEN**hi):`, `return`, calls, and `+`/`*` arithmetic over
/// integer literals and variables.
pub fn parse(src: &str) -> Result<Ast, String> {
    // (indent, content) for each significant line.
    let mut lines: Vec<(usize, String)> = Vec::new();
    for raw in src.lines() {
        let no_comment = raw.split('#').next().unwrap();
        if no_comment.trim().is_empty() {
            continue;
        }
        let indent = no_comment.len() - no_comment.trim_start().len();
        lines.push((indent, no_comment.trim().to_string()));
    }
    let mut p = Parser { lines, i: 0 };
    let mut funcs = Vec::new();
    while p.i < p.lines.len() {
        funcs.push(p.func()?);
    }
    Ok(Ast { funcs })
}

struct Parser {
    lines: Vec<(usize, String)>,
    i: usize,
}

impl Parser {
    fn func(&mut self) -> Result<Func, String> {
        let (indent, line) = self.lines[self.i].clone();
        let header = line
            .strip_prefix("def ")
            .ok_or_else(|| format!("expected `def`, got `{line}`"))?;
        let header = header.strip_suffix(':').ok_or("function header needs `:`")?;
        let open = header.find('(').ok_or("function header needs `(`")?;
        let name = header[..open].trim().to_string();
        let params_str = header[open + 1..header.rfind(')').ok_or("missing `)`")?].trim();
        let params: Vec<String> = if params_str.is_empty() {
            vec![]
        } else {
            params_str.split(',').map(|s| s.trim().to_string()).collect()
        };
        self.i += 1;
        let body = self.block(indent)?;
        let n_ret = body
            .iter()
            .filter_map(|s| if let Stmt::Return(es) = s { Some(es.len()) } else { None })
            .max()
            .unwrap_or(0);
        Ok(Func {
            name,
            params,
            n_ret,
            body,
        })
    }

    /// Parse a block: all statements indented strictly more than `parent`.
    fn block(&mut self, parent: usize) -> Result<Vec<Stmt>, String> {
        let mut stmts = Vec::new();
        let block_indent = match self.lines.get(self.i) {
            Some((ind, _)) if *ind > parent => *ind,
            _ => return Err("expected an indented block".into()),
        };
        while let Some((ind, _)) = self.lines.get(self.i) {
            if *ind != block_indent {
                if *ind > parent && *ind > block_indent {
                    return Err("inconsistent indentation".into());
                }
                break;
            }
            stmts.push(self.stmt(block_indent)?);
        }
        Ok(stmts)
    }

    fn stmt(&mut self, indent: usize) -> Result<Stmt, String> {
        let line = self.lines[self.i].1.clone();
        if let Some(rest) = line.strip_prefix("for ") {
            // for VAR in mul_range(START, STOP): the counter walks gᵏ from START
            // to STOP, ×g each iteration (STOP is exclusive). Bounds are field
            // elements (powers of GEN), so the multiplicative walk is explicit.
            let rest = rest.strip_suffix(':').ok_or("`for` needs `:`")?;
            let (var, iter) = rest.split_once(" in ").ok_or("`for` needs `in`")?;
            let inner = iter
                .trim()
                .strip_prefix("mul_range(")
                .and_then(|s| s.strip_suffix(')'))
                .ok_or("`for` needs `mul_range(start, stop)`")?;
            let parts = split_top(inner, ',');
            if parts.len() != 2 {
                return Err("mul_range needs `start, stop` (both powers of GEN)".into());
            }
            let lo = parse_gpow_bound(&parts[0])?;
            let hi = parse_gpow_bound(&parts[1])?;
            if lo > hi {
                return Err(format!(
                    "mul_range: start GEN**{lo} must not exceed stop GEN**{hi}"
                ));
            }
            self.i += 1;
            let body = self.block(indent)?;
            return Ok(Stmt::For {
                var: var.trim().to_string(),
                lo,
                hi,
                body,
            });
        }
        self.i += 1;
        if line == "return" {
            return Ok(Stmt::Return(vec![]));
        }
        if let Some(rest) = line.strip_prefix("return ") {
            return Ok(Stmt::Return(
                split_top(rest, ',')
                    .iter()
                    .map(|e| parse_expr(e))
                    .collect::<Result<_, _>>()?,
            ));
        }
        if let Some(rest) = line.strip_prefix("assert ") {
            let (a, b) = split_once_top(rest, "==").ok_or("`assert` needs `==`")?;
            return Ok(Stmt::AssertEq(parse_expr(&a)?, parse_expr(&b)?));
        }
        // Assignment or bare call.
        if let Some((lhs, rhs)) = split_assign(&line) {
            let rhs_expr = parse_expr(&rhs)?;
            // Indexed LHS `arr[idx] = value` is a heap store.
            if lhs.trim_end().ends_with(']') {
                let lhs = lhs.trim();
                let open = lhs.find('[').ok_or("malformed store target")?;
                let arr = parse_expr(&lhs[..open])?;
                let idx = parse_expr(&lhs[open + 1..lhs.len() - 1])?;
                return Ok(Stmt::Store(arr, idx, rhs_expr));
            }
            let targets = split_top(&lhs, ',');
            if targets.len() == 1 {
                return Ok(Stmt::Let(targets[0].trim().to_string(), rhs_expr));
            }
            // Tuple assignment: RHS must be a call.
            if let Expr::Call(f, args) = rhs_expr {
                let names = targets.iter().map(|t| t.trim().to_string()).collect();
                return Ok(Stmt::LetTuple(names, f, args));
            }
            return Err("tuple assignment requires a call on the right".into());
        }
        // Bare call statement.
        if let Expr::Call(f, args) = parse_expr(&line)? {
            return Ok(Stmt::Call(f, args));
        }
        Err(format!("statement has no effect: `{line}`"))
    }
}

/// Split on a top-level (paren-depth-0) single `=` that is not `==`.
fn split_assign(s: &str) -> Option<(String, String)> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'=' if depth == 0 => {
                let next_eq = i + 1 < b.len() && b[i + 1] == b'=';
                let prev_eq = i > 0 && b[i - 1] == b'=';
                if !next_eq && !prev_eq {
                    return Some((s[..i].to_string(), s[i + 1..].to_string()));
                }
                if next_eq {
                    i += 1; // skip `==`
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Split `s` on every top-level occurrence of `sep` (a single char).
fn split_top(s: &str, sep: char) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ if c == sep && depth == 0 => {
                parts.push(s[start..i].to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(s[start..].to_string());
    parts
}

/// Split `s` on every top-level lone `*` (not part of a `**`).
fn split_mul(s: &str) -> Vec<String> {
    let b = s.as_bytes();
    let mut parts = Vec::new();
    let (mut depth, mut start, mut i) = (0i32, 0usize, 0usize);
    while i < b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'*' if depth == 0 => {
                let double = (i + 1 < b.len() && b[i + 1] == b'*') || (i > 0 && b[i - 1] == b'*');
                if !double {
                    parts.push(s[start..i].to_string());
                    start = i + 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    parts.push(s[start..].to_string());
    parts
}

/// Split `s` once on a top-level multi-char operator `op`.
fn split_once_top(s: &str, op: &str) -> Option<(String, String)> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i + op.len() <= b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            _ if depth == 0 && &s[i..i + op.len()] == op => {
                return Some((s[..i].to_string(), s[i + op.len()..].to_string()));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Parse a `mul_range` bound: a compile-time power of the generator — `1`
/// (= `g^0`), `GEN` (= `g^1`), or `GEN ** k` — returning the exponent `k`. The
/// loop counter starts at the `start` element and is multiplied by `g` each
/// iteration until it equals `stop`, so both bounds must name `g^k` explicitly
/// (a bound that is not a known power of `g` couldn't be reached by the walk).
fn parse_gpow_bound(s: &str) -> Result<u64, String> {
    match parse_expr(s)? {
        // `1` is the multiplicative identity g^0 — the natural loop start.
        Expr::Lit(1) => Ok(0),
        Expr::Gen => Ok(1),
        Expr::GPow(k) => {
            u64::try_from(k).map_err(|_| format!("mul_range bound exponent {k} does not fit in u64"))
        }
        other => Err(format!(
            "mul_range bounds must be powers of GEN (`1`, `GEN`, or `GEN ** k`), got `{other:?}`"
        )),
    }
}

/// Parse an expression with `+` (lowest) then `*`, atoms being integer literals,
/// variables, calls `f(args)`, and parenthesised sub-expressions.
fn parse_expr(s: &str) -> Result<Expr, String> {
    let s = s.trim();
    // `+` at top level (lowest precedence), left-associative.
    let plus = split_top(s, '+');
    if plus.len() > 1 {
        let mut it = plus.iter();
        let mut acc = parse_expr(it.next().unwrap())?;
        for t in it {
            acc = Expr::Add(Box::new(acc), Box::new(parse_expr(t)?));
        }
        return Ok(acc);
    }
    // `*` (binds tighter than `+`), skipping the two-char `**`.
    let star = split_mul(s);
    if star.len() > 1 {
        let mut it = star.iter();
        let mut acc = parse_expr(it.next().unwrap())?;
        for t in it {
            acc = Expr::Mul(Box::new(acc), Box::new(parse_expr(t)?));
        }
        return Ok(acc);
    }
    // `**` (compile-time power), tightest binding: `base ** k` with `k` a
    // (possibly large) integer literal.
    if let Some((base, exp)) = split_once_top(s, "**") {
        let k: u128 = exp
            .trim()
            .parse()
            .map_err(|_| "`**` exponent must be an integer literal")?;
        return match parse_expr(&base)? {
            Expr::Gen => Ok(Expr::GPow(k)),
            other => Err(format!("`**` is only supported with base `GEN`, got `{other:?}`")),
        };
    }
    // Atom.
    if s.starts_with('(') && s.ends_with(')') {
        return parse_expr(&s[1..s.len() - 1]);
    }
    if s == "GEN" {
        return Ok(Expr::Gen);
    }
    if let Ok(n) = s.parse::<u128>() {
        return Ok(Expr::Lit(n));
    }
    // Index `base[idx]` (binds tightest, like a call).
    if s.ends_with(']') {
        let open = s.find('[').ok_or_else(|| format!("unbalanced `]` in `{s}`"))?;
        let base = parse_expr(&s[..open])?;
        let idx = parse_expr(&s[open + 1..s.len() - 1])?;
        return Ok(Expr::Index(Box::new(base), Box::new(idx)));
    }
    if let Some(open) = s.find('(')
        && s.ends_with(')')
    {
        let name = s[..open].trim().to_string();
        let args_str = s[open + 1..s.len() - 1].trim();
        let args = if args_str.is_empty() {
            vec![]
        } else {
            split_top(args_str, ',')
                .iter()
                .map(|a| parse_expr(a))
                .collect::<Result<_, _>>()?
        };
        // `HeapBuf(n)` / `StackBuf(n)` are allocations, not ordinary calls.
        if name == "HeapBuf" {
            if let [Expr::Lit(n)] = args.as_slice() {
                return Ok(Expr::HeapBuf(*n as u64));
            }
            return Err("HeapBuf(n) needs one integer-literal size".into());
        }
        if name == "StackBuf" {
            if let [Expr::Lit(n)] = args.as_slice() {
                return Ok(Expr::StackBuf(*n as u64));
            }
            return Err("StackBuf(n) needs one integer-literal size".into());
        }
        return Ok(Expr::Call(name, args));
    }
    if s.chars().all(|c| c.is_alphanumeric() || c == '_') && !s.is_empty() {
        return Ok(Expr::Var(s.to_string()));
    }
    Err(format!("cannot parse expression `{s}`"))
}

// ----------------------------------------------------------------------------
// Layout, resolution, witness generation
// ----------------------------------------------------------------------------

/// A hint resolved to concrete offsets/sizes, keyed by global program counter.
#[derive(Clone, Debug)]
pub(crate) enum RHint {
    /// Allocate a fresh region of `size` cells and write `g^{base}` to the cell.
    Alloc { ptr: Off, size: u32 },
}

/// Compile an [`Ast`] to a provable [`Program`]. Panics on a malformed program
/// (unbound variable, missing `main`, address overflow).
pub fn compile(ast: &Ast) -> Program {
    // Lower main first (entry pc 0), then the rest, expanding loop helpers.
    let mut queue: Vec<Func> = Vec::new();
    let main = ast
        .funcs
        .iter()
        .find(|f| f.name == "main")
        .expect("program needs a `main`");
    queue.push(main.clone());
    for f in &ast.funcs {
        if f.name != "main" {
            queue.push(f.clone());
        }
    }

    let mut loop_ctr = 0usize;
    let mut lowered: Vec<Lowered> = Vec::new();
    let mut i = 0;
    while i < queue.len() {
        let f = queue[i].clone();
        i += 1;
        let low = lower_func(&f, &mut queue, &mut loop_ctr);
        lowered.push(low);
    }

    // Assign entry program counters and frame sizes.
    let mut entry = HashMap::new();
    let mut frame_size = HashMap::new();
    let mut pc = 0u32;
    for l in &lowered {
        entry.insert(l.name.clone(), pc);
        frame_size.insert(l.name.clone(), l.frame_size);
        pc += l.code.len() as u32;
    }
    // The padded bytecode size `B` is fixed by the lowered length, so the halt
    // sentinel pc `g^{B-1}` (last slot) is known before resolving: `main`'s
    // `EndSentinel` jump dest resolves to it, and the program halts there.
    let total: usize = lowered.iter().map(|l| l.code.len()).sum();
    let bytecode_size = total.max(1).next_power_of_two();
    let sentinel = (bytecode_size - 1) as u32;

    // Resolve to bytecode + a hint map keyed by global pc.
    let mut prog: Vec<Op> = Vec::new();
    let mut hints: HashMap<u32, Vec<RHint>> = HashMap::new();
    for l in &lowered {
        for ins in &l.code {
            let here = prog.len() as u32;
            if !ins.hints.is_empty() {
                let rhs = ins
                    .hints
                    .iter()
                    .map(|h| match h {
                        Hint::AllocFrame { ptr, callee } => RHint::Alloc {
                            ptr: *ptr,
                            size: frame_size[callee],
                        },
                        Hint::AllocBuffer { ptr, size } => RHint::Alloc { ptr: *ptr, size: *size },
                    })
                    .collect();
                hints.insert(here, rhs);
            }
            prog.push(resolve(&ins.op, &entry, sentinel));
        }
    }

    // Pad the bytecode to `B` (the sentinel slot g^{B-1} must exist for execution).
    prog.resize(bytecode_size, Op::Set { o: 0, k: F128::ZERO });
    Program::assemble(prog, 0, 0, hints, frame_size["main"])
}

/// Render compiled bytecode as a human-readable disassembly. `fp[k]` is the cell
/// `m[fp·gᵏ]` (frame offset `k`); `*(p·gᵝ)` is the dereferenced cell. `SET`
/// constants that are small g-powers (code addresses, indices) show as `gʲ`.
pub fn disassemble(prog: &[Op]) -> String {
    // Reverse index for small g-powers, to pretty-print code addresses/indices.
    let mut gmap: HashMap<F128, usize> = HashMap::new();
    let mut acc = F128::ONE;
    for j in 0..(prog.len() + 512) {
        gmap.entry(acc).or_insert(j);
        acc *= crate::field::g();
    }
    let kfmt = |k: F128| match gmap.get(&k) {
        Some(j) => format!("g^{j}"),
        None => format!("0x{:016x}{:016x}", k.hi, k.lo),
    };

    let mut out = String::new();
    for (pc, op) in prog.iter().enumerate() {
        let line = match op {
            Op::Set { o, k } => format!("SET    fp[{o}] = {}", kfmt(*k)),
            Op::Xor { a, b, c } => format!("XOR    fp[{c}] = fp[{a}] ^ fp[{b}]"),
            Op::Mul { a, b, c } => format!("MUL    fp[{c}] = fp[{a}] * fp[{b}]"),
            Op::Deref {
                alpha,
                beta,
                gamma,
                mode,
            } => {
                let src = match mode {
                    DerefMode::Cell => format!("fp[{gamma}]"),
                    DerefMode::Pc => "g²·pc".to_string(),
                    DerefMode::Fp => "fp".to_string(),
                };
                format!("DEREF  *(fp[{alpha}]·g^{beta}) = {src}  [{mode:?}]")
            }
            Op::Jump { oc, od, of } => {
                format!("JUMP   if fp[{oc}]≠0: pc=fp[{od}], fp=fp[{of}]")
            }
            Op::Blake3 { a, b, c } => {
                format!("BLAKE3 fp[{c}..]= H(fp[{a}..], fp[{b}..])")
            }
        };
        out.push_str(&format!("{pc:>4}  {line}\n"));
    }
    out
}

/// `g^e` for a `u128` exponent (square-and-multiply). `field::g_pow` only takes
/// a `usize`; an index carried in the exponent (a Fibonacci number, say) can
/// exceed 64 bits.
fn g_pow_u128(mut e: u128) -> F128 {
    let mut result = F128::ONE;
    let mut base = crate::field::g();
    while e > 0 {
        if e & 1 == 1 {
            result *= base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

fn resolve(op: &LOp, entry: &HashMap<String, u32>, sentinel: u32) -> Op {
    let resolve_kval = |kv: &KVal| match kv {
        KVal::Const(c) => *c,
        KVal::Entry(name) => g_pow(entry[name] as usize),
        KVal::EndSentinel => g_pow(sentinel as usize),
    };
    match op {
        LOp::Set { o, k: kv } => Op::Set {
            o: *o,
            k: resolve_kval(kv),
        },
        LOp::Xor { a, b, c } => Op::Xor { a: *a, b: *b, c: *c },
        LOp::Mul { a, b, c } => Op::Mul { a: *a, b: *b, c: *c },
        LOp::Deref {
            alpha,
            beta,
            gamma,
            mode,
        } => Op::Deref {
            alpha: *alpha,
            beta: *beta,
            gamma: *gamma,
            mode: *mode,
        },
        LOp::Jump { oc, od, of } => Op::Jump {
            oc: *oc,
            od: *od,
            of: *of,
        },
        LOp::Blake3 { a, b, c } => Op::Blake3 { a: *a, b: *b, c: *c },
    }
}

/// Extend the `g^j` table and its reverse index `g^j ↦ j` to cover index `upto`.
pub(crate) fn grow_gpow(gpow: &mut Vec<F128>, gmap: &mut HashMap<F128, u32>, upto: usize) {
    assert!(upto < (1 << 28), "address space overflow (program too large)");
    while gpow.len() <= upto {
        let next = *gpow.last().unwrap() * crate::field::g();
        gmap.insert(next, gpow.len() as u32);
        gpow.push(next);
    }
}
