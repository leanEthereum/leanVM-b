//! The surface AST produced by the parser: expressions, statements, functions.

/// An expression. Arithmetic is the field's own: `+` is `XOR`, `*` is `MUL`.
#[derive(Clone, Debug)]
pub enum Expr {
    /// Integer / field literal: taken as the field element's 64 bits (`5` is
    /// `F64(5)`; a full 64-bit value names an arbitrary field constant, e.g. a
    /// digest word). Must fit `u64` — the machine word is 64 bits now.
    Lit(u128),
    /// The generator `g` — written `GEN` in source. A logical index `i` is
    /// carried "in the exponent" as `gⁱ`, so `GEN` is the unit step and
    /// `GEN ** k` is `gᵏ`.
    Gen,
    /// The field constant `g^k` (`GEN ** k`, and used by loop lowering). The
    /// exponent is a `u128`, so an index can be a large logical value — e.g. a
    /// Fibonacci number carried in the exponent.
    GPow(u128),
    /// `GEN ** (expr)` with a compile-time integer *expression* exponent,
    /// evaluated at lowering (after `unroll`/`Const` substitution turns its
    /// variables into literals), so `GEN ** (2 * s)` works under an unrolled
    /// counter `s`. Integer arithmetic, like stack indexes and slice bounds.
    GPowE(Box<Expr>),
    /// A variable in scope.
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    /// Single-return function call in expression position.
    Call(String, Vec<Expr>),
    /// `HeapBuf(n)` — allocate a heap buffer of `n` cells; evaluates to its pointer.
    HeapBuf(u64),
    /// `HeapBuf(size)` with a *runtime* size carried **in the exponent**: the
    /// buffer holds `k` cells where `size = g^k` (so a size derived from a
    /// g-power count `n` is plain field arithmetic — `HeapBuf(n * n * GEN**2)`
    /// is `2·log(n) + 2` cells). The allocation is a prover convenience (like
    /// every base pointer), so an under-size only hurts the prover:
    /// overlapping regions trip write-once. Evaluates to the pointer.
    HeapBufDyn(Box<Expr>),
    /// `StackBuf(n)` — allocate `n` *consecutive* frame (stack) cells, bound as a
    /// stack value. Its cells `sa[0..n]` are written/read directly (no heap deref),
    /// and a size-4 `StackBuf` is a valid `blake3` operand (the four 64-bit words
    /// of a 256-bit value live in the four consecutive cells). See [`FnLower`].
    StackBuf(u64),
    /// `arr[idx]` — read a cell. For a heap `arr` (a pointer): `m[arr·idx]` (idx a
    /// g-power). For a [`Expr::StackBuf`]: the frame cell `base + idx` (idx a
    /// compile-time integer), read directly.
    Index(Box<Expr>, Box<Expr>),
    /// `buf[lo:hi]` — a run of cells of a [`Expr::StackBuf`] (frame cells
    /// `base+lo..base+hi`) or of a [`Expr::HeapBuf`] (heap cells
    /// `ptr·g^lo..ptr·g^hi`), with compile-time integer bounds (`hi`
    /// exclusive). Only meaningful as a `blake3` operand, where it must span
    /// exactly 4 cells (one 256-bit value).
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
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
    /// `assert log X < log Y` (also `assert log X < k` with an integer
    /// exponent) — a *range check in the exponent*: with `X = g^x`, proves
    /// `x < k`, i.e. `X ∈ {g^0, g^1, …, g^{k-1}}`. The bound `Y = g^k` is a
    /// compile-time power of `GEN` with `1 ≤ k ≤ 2^MIN_LOG_MEM`; see
    /// [`FnLower::lower_assert_lt`] for the 3-cycle gadget (leanVM's DEREF
    /// range-check trick, transported to g-powers).
    AssertLt(Expr, u64),
    /// `f(args)` as a statement (returns discarded).
    Call(String, Vec<Expr>),
    /// `hint_witness(dest, "name")` — fill `dest` (a `StackBuf`, or a
    /// `StackBuf`/`HeapBuf` slice of any length) with the next *entry* of the
    /// named prover witness stream (`Program::set_witness`); the same symbol
    /// may be hinted many times, each call popping the next entry, whose
    /// length must match `dest`. Zero cycles: the values land through the
    /// hint mechanism, completely unconstrained — the program must constrain
    /// them itself (asserts, range checks, hashes).
    HintWitness { dest: Expr, name: String },
    /// `if lhs == rhs:` (`eq`) / `if lhs != rhs:` (`!eq`) with an optional
    /// `else` block (an `elif` parses as an `else` holding a nested `if`).
    /// One conditional `JUMP` on the XOR of the two sides; bindings made
    /// inside a branch are local to it — branches communicate through
    /// write-once memory (only one branch executes, so both may write the
    /// same cell). See [`FnLower::lower_if`].
    If {
        eq: bool,
        lhs: Expr,
        rhs: Expr,
        then: Vec<Stmt>,
        els: Vec<Stmt>,
    },
    /// `match log(x):` with `case 0: … case n-1:` — consecutive integer cases
    /// from 0, matched against the log of the g-power scrutinee (`x = g^j`
    /// runs case `j`). Dispatched through a trampoline table in the bytecode
    /// (doc §ISA programming / Match statements); the scrutinee must be known
    /// to lie in `[0, n)` — range-check a hinted value first. Case bodies are
    /// branch-local, like [`Stmt::If`] branches. See [`FnLower::lower_match`].
    Match { x: Expr, cases: Vec<Vec<Stmt>> },
    /// `names = match_range(log(x), range(a, b), lambda i: expr, …)` — a
    /// [`Stmt::Match`] with generated arms (leanVM's `match_range`): arm `j`
    /// holds the lambda body with the parameter replaced by the integer
    /// literal `j` (expanded at parse time, one entry of `arms` per integer).
    /// Every arm writes its results into the same fresh cells — write-once is
    /// sound, exactly one arm executes — and `names` bind to those cells at
    /// the join. Multiple names take a multi-return call as the arm body.
    LetMatchRange {
        names: Vec<String>,
        x: Expr,
        arms: Vec<Expr>,
    },
    /// `arr[idx] = value` — store into a heap cell (write-once).
    Store(Expr, Expr, Expr),
    /// `for i in mul_range(GEN**lo, stop): body` — the counter is carried in
    /// the exponent as `gⁱ`, starting at the `start` element `g^lo` and advancing
    /// by `×g` each iteration until it reaches the `stop` element (the terminal
    /// bound, not itself executed). The step is always `×g`: `mul_range` names
    /// its bounds as field elements (e.g. `mul_range(1, GEN ** 10)` runs 10
    /// times), so the multiplicative walk is explicit and there is no step knob.
    /// `stop` is a compile-time power of `GEN`, or a *runtime* g-power element
    /// (e.g. a hinted count) — which the program must know to be reachable:
    /// range-check its log first, or the walk never terminates.
    For {
        var: String,
        lo: u64,
        hi: ForBound,
        body: Vec<Stmt>,
    },
    /// `for i in unroll(a, b): body` — compile-time replication: the body is
    /// emitted `b − a` times with `i` substituted by each integer literal in
    /// turn (usable anywhere a literal is: stack indexes, slice bounds,
    /// `Const` arguments). No call, no frame, no counter — zero loop
    /// overhead, at the price of code size. The bounds are compile-time
    /// integer *expressions*, evaluated at lowering — after `Const`-parameter
    /// specialization, so `unroll(0, n)` with `n: Const` works.
    Unroll {
        var: String,
        lo: Expr,
        hi: Expr,
        body: Vec<Stmt>,
    },
    /// `return e, …` (a bare `return` is the empty vector).
    Return(Vec<Expr>),
    /// Internal (loop lowering): `if lhs != rhs: callee(args)` — a tail call on
    /// the not-equal branch, dispatched by `JUMP`'s nonzero test.
    CallIfNe(Expr, Expr, String, Vec<Expr>),
}

/// A `mul_range` stop bound: a compile-time `GEN ** k`, or a runtime g-power
/// element (evaluated once in the enclosing scope and threaded through the
/// loop helper as a parameter).
#[derive(Clone, Debug)]
pub enum ForBound {
    Const(u64),
    Runtime(Expr),
}

/// A function definition. `main` is the entry point.
#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub params: Vec<String>,
    /// Per-parameter `Const` marker (`def f(k: Const, x):`). A function with
    /// a `Const` parameter is a *template*: it is never lowered itself — each
    /// call site with a distinct constant tuple queues a monomorphized copy
    /// with the parameter substituted by its literal (see
    /// [`FnLower::specialize`]).
    pub const_params: Vec<bool>,
    pub n_ret: usize,
    pub body: Vec<Stmt>,
}

/// A whole program: a set of functions including `main`.
#[derive(Clone, Debug)]
pub struct Ast {
    pub funcs: Vec<Func>,
}
