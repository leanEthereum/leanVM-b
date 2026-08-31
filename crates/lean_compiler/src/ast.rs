//! The surface AST produced by the parser: expressions, statements, functions.

use primitives::field::F192;

/// An expression. Arithmetic is the field's own: `+` is `XOR`, `*` is `MUL`.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// Integer / field literal: the source syntax provides a raw 128-bit value,
    /// embedded into the low two limbs of the 192-bit tower element (`c2 = 0`).
    Lit(u128),
    /// The generator `g`, written `GEN` in source. A logical index `i` is
    /// carried "in the exponent" as `gⁱ`, so `GEN` is the unit step and
    /// `GEN ** k` is `gᵏ`.
    Gen,
    /// The field constant `g^k` (`GEN ** k`, and used by loop lowering). The
    /// exponent is a `u128`, so an index can be a large logical value, e.g. a
    /// Fibonacci number carried in the exponent.
    GPow(u128),
    /// `GEN ** e` where `e` is a compile-time integer *expression* (an `unroll`
    /// variable, a constant, `len(...)`, or index arithmetic of those) rather
    /// than a bare literal. Resolved to a concrete `g^k` at lowering by
    /// evaluating `e` in index space. Lets `buf[GEN ** i]` name cell `i` inside
    /// an `unroll` loop without a running-pointer cursor.
    GenPow(Box<Expr>),
    /// `base ** e` with a **non-`GEN`** base and a compile-time integer exponent
    /// `e`. Evaluated by square-and-multiply at lowering: as integer arithmetic
    /// in an index/bound position (`2 ** c`), or as field arithmetic in a value
    /// position (`x ** k` = `x·x·…`, e.g. a loop counter `g^i` raised to a stride
    /// `g^{i·stride}`). The exponent must be compile-time; the base may be runtime.
    Pow(Box<Expr>, Box<Expr>),
    /// A variable in scope.
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    /// Integer subtraction `a - b`, **compile-time only**. In this field `+` is
    /// XOR, so field subtraction *is* `+`; a `-` is therefore only meaningful in
    /// index space (an index / slice bound / `unroll` count / `**` exponent /
    /// folded `if`). Using one as a runtime field value is an error.
    Sub(Box<Expr>, Box<Expr>),
    /// Integer floor-division `a // b` and remainder `a % b`, **compile-time
    /// only** (the field has no integer division). Valid where an index /
    /// slice bound / `Const` argument is expected, or as a folded `if`
    /// condition; using one as a runtime field value is an error.
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    /// Field division `a / b` (single slash): a **runtime** field operation,
    /// `a · b⁻¹`. Lowered to one `MUL` whose quotient operand is unset, so the
    /// write-once back-solve fills it with `a · b⁻¹` and the `MUL` constraint
    /// pins `quotient · b == a` (§range-check trick). No hint: the inverse is
    /// nondeterministic but the constraint binds it. `b == 0` is rejected,
    /// including `0 / 0`; `1 / b` therefore also enforces `b != 0`. Distinct
    /// from the compile-time `//` ([`Expr::Div`]).
    FieldDiv(Box<Expr>, Box<Expr>),
    /// Single-return function call in expression position.
    Call(String, Vec<Expr>),
    /// `HeapBuf(n)`: allocate a heap buffer of `n` cells; evaluates to its pointer.
    HeapBuf(u64),
    /// `HeapBuf(size)` with a *runtime* size carried **in the exponent**: the
    /// buffer holds `k` cells where `size = g^k` (so a size derived from a
    /// g-power count `n` is plain field arithmetic: `HeapBuf(n * n * GEN**2)`
    /// is `2·log(n) + 2` cells). The allocation is a prover convenience (like
    /// every base pointer), so an under-size only hurts the prover:
    /// overlapping regions trip write-once. Evaluates to the pointer.
    HeapBufDyn(Box<Expr>),
    /// `StackBuf(n)`: allocate `n` *consecutive* frame (stack) cells, bound as a
    /// stack value. Its cells `sa[0..n]` are written/read directly (no heap deref),
    /// and a size-2 `StackBuf` is a valid `blake2s` operand (the four 64-bit hash
    /// words live as two lanes in each of two consecutive 128-bit cells).
    StackBuf(u64),
    /// `arr[idx]`: read a cell. For a heap `arr` (a pointer), `m[arr·idx]` (idx a
    /// g-power). For a [`Expr::StackBuf`]: the frame cell `base + idx` (idx a
    /// compile-time integer), read directly.
    Index(Box<Expr>, Box<Expr>),
    /// `buf[lo:hi]`: a run of cells of a [`Expr::StackBuf`] (frame cells
    /// `base+lo..base+hi`) or of a [`Expr::HeapBuf`] (heap cells
    /// `ptr·g^lo..ptr·g^hi`), with compile-time integer bounds (`hi`
    /// exclusive). Only meaningful as a `blake2s` operand, where it must span
    /// exactly 2 cells (one 256-bit value).
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `[a, b, …]`: an initialized [`Expr::StackBuf`], so `x = [a, b]` allocates
    /// a StackBuf of the element count and writes each element in place, sugar
    /// for the alloc-then-store idiom. Only meaningful as the RHS of a plain
    /// assignment (inside a function; a *top-level* `NAME = […]` is a constant
    /// array, see [`Ast::const_arrays`]).
    ListLit(Vec<Expr>),
}

/// A statement, with the source line it came from. The line is what every
/// lowering diagnostic names and what the pc-to-line table is built from: the
/// AST is the only place that still knows it, since lowering works in frame
/// cells and program counters.
#[derive(Clone, Debug)]
pub struct Stmt {
    pub line: u32,
    pub kind: StmtKind,
}

impl Stmt {
    pub fn new(line: u32, kind: StmtKind) -> Self {
        Self { line, kind }
    }

    /// A statement the compiler synthesized (a loop helper's body, a desugared
    /// tail call): it inherits the line of whatever it was generated for.
    pub fn at(&self, kind: StmtKind) -> Self {
        Self { line: self.line, kind }
    }
}

/// What a statement does.
#[derive(Clone, Debug)]
pub enum StmtKind {
    /// `x = expr` (immutable binding).
    Let(String, Expr),
    /// `x, y, … = f(args)`: call with multiple returns.
    LetTuple(Vec<String>, String, Vec<Expr>),
    /// `assert a == b`: a proof-enforced equality.
    AssertEq(Expr, Expr),
    /// `assert a != b`: a proof-enforced inequality. Lowers to `x = a + b`, a
    /// hinted `inv = x⁻¹`, `p = x·inv` and `SET p = 1`, the write-once conflict
    /// being the assertion: `x = 0` forces `p = 0` whatever the hint. See
    /// `FnLower::lower_assert_ne`.
    AssertNe(Expr, Expr),
    /// `assert log X < log Y` (also `assert log X < k` with an integer
    /// exponent), a *range check in the exponent*: with `X = g^x`, proves
    /// `x < k`, i.e. `X ∈ {g^0, g^1, …, g^{k-1}}`. See
    /// `FnLower::lower_assert_lt` for the 3-cycle gadget (leanVM's DEREF
    /// range-check trick, transported to g-powers).
    AssertLt(Expr, LtBound),
    /// `f(args)` as a statement (returns discarded).
    Call(String, Vec<Expr>),
    /// `hint_witness(dest, "name")`: fill `dest` (a `StackBuf`, or a
    /// `StackBuf`/`HeapBuf` slice of any length) with the next *entry* of the
    /// named prover witness stream (`Program::set_witness`); the same symbol
    /// may be hinted many times, each call popping the next entry, whose
    /// length must match `dest`. Zero cycles: the values land through the
    /// hint mechanism, completely unconstrained, so the program must constrain
    /// them itself (asserts, range checks, hashes).
    HintWitness { dest: Expr, name: String },
    /// `x = hint_witness("stream")`: ONE hinted value, bound to a name.
    ///
    /// The run form needs a destination that already exists, so a single hinted
    /// scalar cost a one-cell `StackBuf`, a slice of it, and a read back out.
    /// The guest declared thirty such buffers, twenty-eight of them for nothing
    /// else. The value is as unconstrained as any other hint.
    LetHintWitness { name: String, stream: String },
    /// `print("label", expr)` / `print(expr)`: a prover-side debug print of the
    /// value at this program point (witness generation only, no constraints).
    Print { label: String, value: Expr },
    /// `if lhs == rhs:` (`eq`) / `if lhs != rhs:` (`!eq`) with an optional
    /// `else` block (an `elif` parses as an `else` holding a nested `if`).
    /// One conditional `JUMP` on the XOR of the two sides; bindings made
    /// inside a branch are local to it, and branches communicate through
    /// write-once memory (only one branch executes, so both may write the
    /// same cell). See `FnLower::lower_if`.
    If {
        eq: bool,
        lhs: Expr,
        rhs: Expr,
        then: Vec<Stmt>,
        els: Vec<Stmt>,
        /// Written `if const(a == b):`. The author is asking for the branch to be
        /// decided while compiling, so a condition that cannot be decided then is
        /// an error rather than a runtime test, and one whose integer and field
        /// readings disagree is an error rather than a silent choice between them.
        force_const: bool,
    },
    /// `match log(x):` with `case 0: … case n-1:`, consecutive integer cases
    /// from 0, matched against the log of the g-power scrutinee (`x = g^j`
    /// runs case `j`). Dispatched through a trampoline table in the bytecode
    /// (doc §ISA programming / Match statements); the scrutinee must be known
    /// to lie in `[0, n)`, so range-check a hinted value first. Case bodies are
    /// branch-local, like [`StmtKind::If`] branches. See `FnLower::lower_match`.
    Match { x: Expr, cases: Vec<Vec<Stmt>> },
    /// `names = match_range(log(x), range(a, b), lambda i: expr, …)`: a
    /// [`StmtKind::Match`] with generated arms (leanVM's `match_range`): arm `j`
    /// holds the lambda body with the parameter replaced by the integer
    /// literal `j` (expanded at parse time, one entry of `arms` per integer).
    /// Every arm writes its results into the same fresh cells (write-once is
    /// sound, since exactly one arm executes), and `names` bind to those cells
    /// at the join. Multiple names take a multi-return call as the arm body.
    LetMatchRange {
        names: Vec<String>,
        x: Expr,
        arms: Vec<Expr>,
    },
    /// `arr[idx] = value`: store into a heap cell (write-once).
    Store(Expr, Expr, Expr),
    /// `for i in mul_range(GEN**lo, stop): body`, where the counter is carried in
    /// the exponent as `gⁱ`, starting at the `start` element `g^lo` and advancing
    /// by `×g` each iteration until it reaches the `stop` element (the terminal
    /// bound, not itself executed). The step is always `×g`: `mul_range` names
    /// its bounds as field elements (e.g. `mul_range(1, GEN ** 10)` runs 10
    /// times), so the multiplicative walk is explicit and there is no step knob.
    /// `stop` is a compile-time power of `GEN`, or a *runtime* g-power element
    /// (e.g. a hinted count), which the program must know to be reachable:
    /// range-check its log first, or the walk never terminates.
    For {
        var: String,
        lo: u64,
        hi: ForBound,
        body: Vec<Stmt>,
    },
    /// `for i in unroll(a, b): body`, compile-time replication: the body is
    /// emitted `b − a` times with `i` substituted by each integer literal in
    /// turn (usable anywhere a literal is: stack indexes, slice bounds,
    /// `Const` arguments). No call, no frame, no counter: zero loop
    /// overhead, at the price of code size. The bounds are compile-time
    /// integer *expressions*, evaluated at lowering, after `Const`-parameter
    /// specialization, so `unroll(0, n)` with `n: Const` works.
    Unroll {
        var: String,
        lo: Expr,
        hi: Expr,
        body: Vec<Stmt>,
    },
    /// `return e, …` (a bare `return` is the empty vector).
    Return(Vec<Expr>),
    /// Internal (loop lowering): `if lhs != rhs: callee(args)`, a tail call on
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

/// A range-check bound (`assert log X < …`): a compile-time exponent, or a
/// runtime `g^n`.
///
/// The gadget is the same either way, and so is what it proves: only the cell
/// holding `g^{k-1}` differs (a pooled `SET` against one `MUL` off the runtime
/// bound). What the compiler can no longer check is the `k ≤ 2^MIN_LOG_MEM` cap,
/// so the program owes it: range-check the bound itself first. Without that,
/// `log X < log n` bounds `X` only by the prover-*announced* memory size, and
/// the honest complement `g^{k-1-log X}` may not even be an address.
#[derive(Clone, Debug)]
pub enum LtBound {
    Const(u64),
    Runtime(Expr),
}

/// Compile-time representation of one source-level return value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// One ordinary field element or address cell. Heap buffers use this shape:
    /// allocation happens in the callee and only their pointer crosses.
    Scalar,
    /// A compile-time-sized run of consecutive frame cells.
    StackBuf(u32),
}

impl Shape {
    /// Number of physical call-frame return cells occupied by this source-level
    /// return value.
    pub(crate) fn cells(self) -> u32 {
        match self {
            Self::StackBuf(n) => n,
            Self::Scalar => 1,
        }
    }
}

/// A function definition. `main` is the entry point.
#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub params: Vec<String>,
    /// Per-parameter `Const` marker (`def f(k: Const, x):`). A function with
    /// a `Const` parameter is a *template*: it is never lowered itself, and each
    /// call site with a distinct constant tuple queues a monomorphized copy
    /// with the parameter substituted by its literal (see
    /// `FnLower::specialize`).
    pub const_params: Vec<bool>,
    /// Number of source-level return values (tuple arity).
    pub n_ret: usize,
    /// Compile-time shape of each source-level return value. Stack buffers use
    /// multiple physical ABI cells; everything else uses one cell.
    pub return_shapes: Vec<Shape>,
    /// The same for each parameter, from a `s: StackBuf(n)` annotation. A value
    /// could always be RETURNED as a run of cells and never passed as one, so a
    /// two-cell digest went in through a pointer or an `@inline` expansion while
    /// coming back out whole. The shapes are the same type in both directions
    /// because it is the same question.
    pub param_shapes: Vec<Shape>,
    pub body: Vec<Stmt>,
    /// `@inline` decorator: expand this function at each call site instead of
    /// emitting a real call: no frame, no argument/return plumbing (the
    /// call-convention `DEREF`s and jumps vanish). The body must be a single
    /// tail `return`; it is never lowered standalone. Named `@inline` because
    /// the inlined body costs nothing at runtime (cf. `unroll(a, b)`, which
    /// really does replicate a loop body).
    pub inline: bool,
}

/// A whole program: a set of functions including `main`.
#[derive(Clone, Debug)]
pub struct Ast {
    pub funcs: Vec<Func>,
    /// Top-level constant arrays `NAME = [a, b, c]` (declaration order). Each
    /// element is a `u128` (a field value `extension-field::new(lo,hi)` where used as a
    /// value, or a small integer where used as a compile-time index / bound /
    /// `unroll` count). Indexed `NAME[i]` and measured `len(NAME)` at compile
    /// time only (`i` a literal / constant / `unroll` var). Not textually
    /// substituted (unlike scalar constants), and resolved at lowering.
    pub const_arrays: Vec<(String, Vec<F192>)>,
}

// Free-variable analysis. Pure AST, no lowering state: the only consumer is the
// `for` desugaring, which needs the names a loop body reads from outside itself,
// but the question is about the syntax tree and is answered here rather than in
// the middle of the walker.

use std::collections::HashSet;

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
/// Every name the block binds, ignoring scope. [`free_vars_stmt`] deliberately
/// does not answer this: its `bound` set is scoped, so an arm-local binding is
/// discarded with the arm.
pub(crate) fn binds_anywhere(body: &[Stmt], out: &mut HashSet<String>) {
    for s in body {
        match &s.kind {
            StmtKind::Let(n, _) | StmtKind::LetHintWitness { name: n, .. } => {
                out.insert(n.clone());
            }
            StmtKind::LetTuple(ns, ..) | StmtKind::LetMatchRange { names: ns, .. } => ns.iter().for_each(|n| {
                out.insert(n.clone());
            }),
            StmtKind::If { then, els, .. } => {
                binds_anywhere(then, out);
                binds_anywhere(els, out);
            }
            StmtKind::Match { cases, .. } => cases.iter().for_each(|c| binds_anywhere(c, out)),
            StmtKind::For { var, body, .. } | StmtKind::Unroll { var, body, .. } => {
                out.insert(var.clone());
                binds_anywhere(body, out);
            }
            _ => {}
        }
    }
}

/// Free variables of a block whose bindings do NOT escape it: it sees everything
/// bound so far, and anything it binds stays inside.
fn scoped_vars(body: &[Stmt], refs: &mut Vec<String>, bound: &HashSet<String>) {
    let mut inner = bound.clone();
    for s in body {
        free_vars_stmt(s, refs, &mut inner);
    }
}

pub(crate) fn free_vars_stmt(s: &Stmt, refs: &mut Vec<String>, bound: &mut HashSet<String>) {
    match &s.kind {
        StmtKind::Let(n, e) => {
            free_vars_expr(e, refs);
            bound.insert(n.clone());
        }
        StmtKind::LetTuple(ns, _, args) => {
            args.iter().for_each(|a| free_vars_expr(a, refs));
            ns.iter().for_each(|n| {
                bound.insert(n.clone());
            });
        }
        StmtKind::AssertEq(a, b) | StmtKind::AssertNe(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        StmtKind::AssertLt(e, bound) => {
            free_vars_expr(e, refs);
            if let LtBound::Runtime(b) = bound {
                free_vars_expr(b, refs);
            }
        }
        StmtKind::HintWitness { dest, .. } => free_vars_expr(dest, refs),
        StmtKind::LetHintWitness { name, .. } => {
            bound.insert(name.clone());
        }
        StmtKind::Print { value, .. } => free_vars_expr(value, refs),
        StmtKind::If {
            lhs,
            rhs,
            then,
            els,
            force_const,
            ..
        } => {
            free_vars_expr(lhs, refs);
            free_vars_expr(rhs, refs);
            // An arm's bindings are local to it (`zkDSL.md` §Control flow), so each
            // gets its own scope. Sharing one made a name rebound in ONE arm count
            // as loop-local everywhere, so the OUTER binding the other arm reads
            // was never captured and a legal program failed with `unbound
            // variable`. Over-collecting into `refs` is harmless: a capture naming
            // nothing in the enclosing scope is dropped.
            // `lower_if` FOLDS a compile-time condition and runs the taken branch
            // without `scoped`, so its bindings persist exactly like an `unroll`
            // body's. Modelling that as scoped over-captured, and the loop's own
            // self-call then read a name the folded arm had rebound to a
            // `StackBuf`. Both sides literal is the syntactic half of that test.
            if *force_const || matches!((lhs, rhs), (Expr::Lit(_), Expr::Lit(_))) {
                then.iter().for_each(|s| free_vars_stmt(s, refs, bound));
                els.iter().for_each(|s| free_vars_stmt(s, refs, bound));
            } else {
                scoped_vars(then, refs, bound);
                scoped_vars(els, refs, bound);
            }
        }
        StmtKind::Match { x, cases } => {
            free_vars_expr(x, refs);
            cases.iter().for_each(|c| scoped_vars(c, refs, bound));
        }
        StmtKind::LetMatchRange { names, x, arms } => {
            free_vars_expr(x, refs);
            arms.iter().for_each(|a| free_vars_expr(a, refs));
            names.iter().for_each(|n| {
                bound.insert(n.clone());
            });
        }
        StmtKind::CallIfNe(a, b, _, args) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
            args.iter().for_each(|e| free_vars_expr(e, refs));
        }
        StmtKind::Call(_, args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        StmtKind::Store(arr, idx, val) => {
            free_vars_expr(arr, refs);
            free_vars_expr(idx, refs);
            free_vars_expr(val, refs);
        }
        StmtKind::Return(es) => es.iter().for_each(|e| free_vars_expr(e, refs)),
        StmtKind::For { var, hi, body, .. } => {
            if let ForBound::Runtime(b) = hi {
                free_vars_expr(b, refs);
            }
            // A nested loop's body becomes its own function, so neither its
            // counter nor its bindings exist out here. `unroll` below is the
            // opposite: it replicates straight-line code into THIS scope, so its
            // bindings really do persist and it keeps the shared set.
            let mut inner = bound.clone();
            inner.insert(var.clone());
            body.iter().for_each(|s| free_vars_stmt(s, refs, &mut inner));
        }
        StmtKind::Unroll { var, lo, hi, body } => {
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
            bound.insert(var.clone());
            body.iter().for_each(|s| free_vars_stmt(s, refs, bound));
        }
    }
}
