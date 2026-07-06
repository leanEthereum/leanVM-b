# zkDSL Language Reference (leanVM-b)

The zkDSL is a Python-syntax language that compiles to the leanVM-b ISA — six
instructions (`XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `BLAKE3`) over the binary
field GF(2^128), with write-once memory and all indices carried "in the
exponent" as powers of a fixed generator. For the underlying VM and proving
system, see [`misc/doc.tex`](misc/doc.tex) (released as `doc.pdf`).

Source files use the `.py` extension and are **valid Python**: they import the
[`snark_lib`](snark_lib.py) stub, which defines `GEN`, `log`, `mul_range`,
`HeapBuf`, `StackBuf`, and `blake3` so that editors, linters, and even
`python3` itself accept the file. The compiler skips the import.

Entry points: `compiler::parse` / `compiler::parse_file` → `compiler::compile`
→ `cpu::prove` / `cpu::verify`.

## Dev experience

The repo ships a root [`pyrightconfig.json`](pyrightconfig.json) with
`"extraPaths": ["."]`, so any `.py` program anywhere in the repo resolves
`snark_lib` when the repo root is opened in the editor. Programs also run as
plain Python (`PYTHONPATH=. python3 tests/programs/foo.py`) — the stubs are
no-ops, so this only checks that the file is well-formed.

## The field — and indices in the exponent

Every runtime value is one element of GF(2^128) in GHASH form
(`F_2[x]/(x^128 + x^7 + x^2 + x + 1)`). There are no runtime integers.

- `+` is field addition = bitwise **XOR** (so `x + x == 0`),
- `*` is the field (GHASH) product,
- an integer literal `n` denotes the field element with bit pattern `n`
  (bit `k` is the coefficient of `x^k`) — `5` is `1 + x^2`, not "five",
- `GEN` is the fixed generator `g = x` (multiplicative order `2^128 − 1`),
- `GEN ** k` is the compile-time constant `g^k` (`**` takes base `GEN` and an
  integer-literal exponent only).

A logical **index** `i` is carried as `g^i`: incrementing is one
multiplication by `GEN`, and memory/bytecode addresses are g-powers. This is
the design idiom of the whole VM — loops, heap addressing, and range checks
below all live in the exponent.

## Program shape

A program is a **single** `.py` file:

```python
from snark_lib import *   # for Python tooling; skipped by the compiler


def main():               # required entry point
    ...
    return

def helper(a, b):         # other functions
    ...
    return a * b
```

`import snark_lib` / `from snark_lib import *` are the only imports accepted —
anything else is a compile error (no multi-file programs yet). Comments (`#`)
and blank lines are free. Indentation is block structure, as in Python.

## Public input

Memory cells `m[0]` and `m[1]` hold the two public-input field elements. A
program *publishes* results by asserting them against those cells through the
write-once heap store (the pointer `g^0` addresses absolute memory):

```python
p = GEN ** 0
p[1] = result_a     # m[p·1]  = m[0] — an equality assert against the public input
p[GEN] = result_b   # m[p·g] = m[1]
```

Test programs under `tests/programs/` declare the public input they expect
with a top-of-file annotation of two constant elements (or omit it to run with
two zeros); the generic harness `tests/py_source.rs` proves and verifies every
program in the directory:

```python
# public_input: GEN ** 89, 101229015297003380629709256178361811305
```

## Global constants and placeholders

Above the functions (after the optional `snark_lib` import) a program may
declare **global constants** — top-level `NAME = <const-expr>`:

```python
from snark_lib import *

N = 8                    # an integer size / value
STEP = GEN ** 2          # a g-power constant (index carried in the exponent)
WIDE = N + 1             # compile-time INTEGER arithmetic (`+ - * / **`);
                         # references to *earlier* constants are allowed

def main():
    buf = StackBuf(N)    # a constant is a plain literal: usable as a size,
    x = GEN ** N         # a `**` exponent, a stack/slice index, an operand,
    assert log x < N     # an `assert log _ < _` bound, or a `Const` argument
    return
```

Each constant is **evaluated to its field value** and substituted, as a single
literal, everywhere its name appears below — so unlike a `Const` parameter it
needs no call site and works in every literal position. Constants must precede
the `def`s and are resolved *before* variables, so a constant name is
**reserved**: do not reuse it as a parameter or local name. (Being a valid
Python file, `N = 8` is also just a Python module global.)

**Placeholders** let a host fill values at compile time without editing the
source. Any identifier may be mapped to replacement text before parsing
(`compiler::parse_with_replacements` / `parse_file_with_replacements`, taking a
`BTreeMap<String, String>`); the replacement is identifier-bounded (`FOO` does
not touch `FOOBAR`). The idiom is a placeholder feeding a constant:

```python
V = V_PLACEHOLDER        # with replacement  "V_PLACEHOLDER" ↦ "128"
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER

def main():
    ...                  # V is the constant 128 throughout
```

so one source template compiles at many sizes. An unfilled placeholder (no
replacement, no matching constant) is a compile error, not a silent variable.
A program that uses placeholders only type-checks as Python once its
placeholders are also defined (e.g. bound in `snark_lib` for tooling).

## Functions

```python
def f(a, b):
    return a + b, a * b   # multiple returns

x, y = f(p, q)            # tuple assignment
z = f(p, q)               # expression position: first return
f(p, q)                   # statement: returns discarded
```

Functions may recurse. Each call gets a **fresh frame**: the frame pointer is
prover-hinted (write-once memory makes an unconstrained cell prover-chosen),
arguments and the return address/frame are stored with `DEREF`s, and control
transfers with one `JUMP`. Cost: about `n_args + n_returns + 4` instructions
per call. Every non-`main` function must end in an explicit `return`; in
`main`, `return` is a no-op (main halts at a sentinel automatically).

### `Const` parameters

```python
def hash_pair(buf, k: Const):
    h = StackBuf(2)
    blake3(buf[k * 2:k * 2 + 2], buf[k * 2:k * 2 + 2], h)
    return h[0], h[1]
```

`k: Const` marks a **compile-time parameter**: the call site must pass a
constant (an integer literal, `GEN ** k`, or a literal-bound name), and the
compiler *specializes* the function per distinct constant tuple — a
monomorphized copy (`hash_pair__L1`) with the parameter substituted as its
literal, shared by every call with the same constants; only the runtime
arguments are passed. Inside the body the parameter *is* the literal, so it
works in compile-time positions: stack indexes, slice bounds. A function with
a `Const` parameter is a template — it is never lowered itself. The idiomatic
pairing dispatches a runtime index to a const-indexed helper:

```python
r = match_range(log(x), range(0, 4), lambda i: hash_pair(buf, i))
```

### `@unroll` — inline a function at its call sites

```python
@unroll
def combine(a, b, k: Const):
    s = StackBuf(2)
    if k % 2 == 0:      # a folded `if` (see below): baked per Const value
        s[0] = a
    else:
        s[0] = b
    s[1] = a + b
    return s[k % 2]
```

An `@unroll` function is **expanded at each call site** instead of emitting a
real call — no frame, no argument/return `DEREF`s, no call/return `JUMP`s. The
body must be a single **tail** `return`; it may contain `blake3`, `if`, and
`unroll`, but not a call to another (user) function, a `for`/`match`, or any
nested/early `return`. It is never lowered standalone; a call to a
non-`@unroll` function is unchanged. Named for the DSL's compile-time
expansion verb (cf. `unroll(a, b)` for loops).

Because the body runs in the *caller's* frame, a `Const` parameter whose `if`s
fold (below) bakes straight-line, per-case code — the idiom for a `match_range`
arm that must specialize on the arm value. The trade-off is frame cells: each
call site gets its own copy, so `@unroll` pays off for small, hot callees;
inlining a large body at many sites grows the committed witness (more data
memory), so it is opt-in, not automatic.

## Variables

Bindings are **immutable**: `x = e` names a fresh cell. Re-binding a name is
allowed (it's a new cell; the old value is unaffected), but there is no
mutation and no compound assignment.

A name bound to an integer literal (`x = 2`) additionally acts as a
**compile-time index constant** — usable in stack indexes and slice bounds
(see below). Any other re-binding clears that role.

Two families of binding are folded and carried **virtually**, costing no
instruction until used as a value:

- **g-powers and shifted pointers** — a cursor like `s = s * GEN` or a pointer
  view `p = buf * GEN ** k`. The offset folds into the `DEREF` address of each
  access; only a scalar use materializes it.
- **field constants** — a value built from literals / `GEN ** k` by field `+`
  and `*`, e.g. a running weight `w = w * CHAIN_LENGTH` in an unrolled loop.
  The arithmetic that advances it is compile-time (zero instructions); each use
  is one `SET` of the folded constant.

## Memory

All memory is **write-once**: a cell is set once; a second write of the same
value is a no-op, of a different value a proof failure. This turns stores into
equality assertions and is used throughout (publishing, `blake3` outputs).
Reading a cell nobody ever writes yields an unconstrained value (fixed to zero
at the end of witness generation) — don't.

### `HeapBuf(n)` — heap buffers, indexed in the exponent

```python
buf = HeapBuf(4)      # fresh, disjoint region; `buf` is its pointer (a g-power)
buf[1] = 5            # m[buf·1]   — cell g^0
buf[GEN] = 7          # m[buf·g]   — cell g^1
v = buf[i]            # m[buf·i]   — i is any runtime g-power (e.g. a loop counter)
buf[i * GEN] = v      # the next cell along
```

The index is a field element; cell `k` of the buffer lives at address
`buf · g^k`. A read or store is one `DEREF`. A **runtime** index costs one
extra `MUL` for the `buf·i` pointer, but a **compile-time g-power** offset —
`buf[1]`, `buf[GEN ** k]`, or a cursor advanced by `× GEN ** m` — folds into
the `DEREF`'s address immediate for free: no `MUL`, no `SET`, and the cursor
arithmetic itself vanishes (so a `× GEN` walk over consecutive cells is zero
instructions). There are no bounds checks — the buffer is a region convention,
not a checked type.

### `StackBuf(n)` — frame-cell runs, indexed by compile-time integers

```python
sa = StackBuf(3)      # n consecutive cells of the current frame
sa[0] = 3             # direct frame cell: zero instructions to address
sa[2] = sa[0] + sa[1]
x = 1
v = sa[x + 1]         # indexes: literals, literal-bound names, and + * // % of those
```

Stack indexes and slice bounds are **compile-time integers**, and index
arithmetic (`+ * // %`) is *integer* arithmetic (`x + 1` above is 2, `k // 2`
floor-divides, `k % 2` is a remainder — index space, not the field, where XOR
is what `+` means and `//`/`%` have no meaning at all: using one as a runtime
field value is a compile error). Bounds are checked at compile time. A `StackBuf`
name is a run of cells, not a scalar: using it as one is an error, and it
cannot be captured into a `for` loop body (carry state through a `HeapBuf`
instead).

### Slices — `buf[lo:hi]`

`buf[lo:hi]` names a run of cells (`hi` exclusive). Slices exist only as
`blake3` operands and must span exactly 2 cells (one 256-bit value). Two
forms:

- **compile-time bounds** (integers, as for stack indexes): frame cells
  `base+lo .. base+hi` of a `StackBuf`, or heap cells `ptr·g^lo .. ptr·g^hi`
  of a `HeapBuf` — `hb[2:4]` is the pair `g^2, g^3`;
- **runtime start, heap only**: `buf[i:i + 2]` with a runtime g-power index
  `i` (e.g. a loop counter) names the cells `buf·i`, `buf·i·g` — one `MUL`
  folds `i` into the pointer. The `hi` bound cannot be evaluated, only
  shape-checked: it must be syntactically `lo + 2`
  (`buf[b * GEN ** 2 : b * GEN ** 2 + 2]` is fine). A `StackBuf` slice cannot
  have a runtime start — frame offsets are baked into the bytecode operands.

Note the two index spaces, consistent with plain indexing: compile-time
bounds are integer exponents (`hb[2:4]` ≡ `hb[GEN ** 2 : GEN ** 2 + 2]`),
runtime starts are g-power elements.

## Control flow

### `for i in mul_range(start, stop)` — loops in the exponent

```python
for i in mul_range(1, GEN ** 10):   # i = g^0, g^1, …, g^9
    buf[i * GEN * GEN] = buf[i] * buf[i * GEN]
```

The counter walks multiplicatively: it starts at `start`, advances by `×GEN`
each iteration, and stops on reaching `stop` (exclusive). The start is a
compile-time power of `GEN` (`1`, `GEN`, or `GEN ** k`); the stop is either
compile-time too (an empty range compiles to nothing) or a **runtime** g-power
element — e.g. a hinted count:

```python
hint_witness(nb[0:1], "n_blocks")
n = nb[0]
assert log(n) < 16       # the walk terminates only by REACHING the bound:
for j in mul_range(1, n):   # bound its log first, or it never does
    ...
```

A runtime bound is evaluated once at entry and threaded through the loop as
an extra parameter (+1 argument per iteration call); entry itself is the same
`!=` test, so a bound equal to the start runs zero iterations.

Lowering: the body becomes a tail-recursive helper function whose exit test is
folded into the recursion's `JUMP` condition — one call per iteration, no
separate is-zero gadget. Free variables of the body are captured **by value**
as extra parameters; a `HeapBuf` pointer threads through fine, a `StackBuf`
does not (compile error).

### `for i in unroll(a, b)` — compile-time unrolling

```python
for i in unroll(0, 7):
    sb[i + 1] = sb[i] * GEN          # i is the integer literal of each copy

def chain(buf, n: Const):
    for i in unroll(0, n):           # a Const parameter as a bound
        blake3(buf[i * 2:i * 2 + 2], buf[i * 2:i * 2 + 2], buf[i * 2 + 2:i * 2 + 4])
    return
```

The body is replicated `b − a` times with `i` substituted by each integer
literal in turn — usable anywhere a literal is (stack indexes, slice bounds,
`Const` arguments). Zero loop overhead: no call, no frame, no counter — the
price is code size. Bounds are compile-time integer expressions, evaluated
after `Const` specialization, so `unroll(0, n)` with `n: Const` works (unlike
`mul_range`, whose bounds are parse-time literals). Every copy executes —
this is straight-line code, not a branch — so bindings simply rebind, a fresh
binding per iteration.

### `if` / `elif` / `else`

```python
if x == GEN ** 3:
    r[1] = 5
elif x != y:
    r[1] = 7
else:
    r[1] = 9
```

Conditions are field-equality tests: `a == b` or `a != b` (there are no other
predicates — order facts come from range-check asserts). The lowering is one
`XOR` plus one conditional `JUMP` on it; the taken jump goes to whichever
block the test doesn't fall into, so no negation gadget is needed. An `elif`
is sugar for an `else` holding a nested `if`.

When **both sides are compile-time integers** (e.g. after a `Const` parameter
is substituted — `if k % 2 == 0:`), the condition is known at compile time and
the `if` **folds** to just the taken branch: no `XOR`, no `JUMP`, no `self-fp`.
This is what lets an `@unroll` function bake different straight-line code per
`Const` value.

Two write-once-flavored rules:

- **bindings made inside a branch are local to it** — the compile-time scope
  reverts at the join. Branches communicate through memory: only one branch
  executes, so both may write the *same* cell (`r[1]` above), and the join
  reads it.
- a cell nobody wrote (e.g. skipped-branch territory) stays unconstrained —
  same rule as everywhere else in write-once memory.

Local jumps must carry the frame pointer, which the ISA cannot read directly;
each branching function materializes its own `fp` once (2 `DEREF`s through a
1-cell heap bounce; free in `main`, where `fp = g^0 = 1`).

### `match`

```python
match log(x):        # x = GEN ** j runs case j
    case 0:
        r[1] = 11
    case 1:
        r[1] = 17
    case 2:
        r[1] = 21
```

Matches the **log** of a g-power scrutinee against integer cases, which must
be consecutive from 0 (the dispatch table is dense; no `case _`). The
lowering is two jumps through a *trampoline table* in the bytecode: the
dispatch jumps to `g^T · x²` — the j-th two-instruction slot (`SET` the case
block's address, `JUMP` to it) of a table at base `T` — and the slot jumps to
the case block, which can sit anywhere, unaligned and of any length. Cost ≈ 7
cycles, independent of the case count.

(Why not leanVM's single-jump `pc = a + b·x`: that affine address needs
integer *scaling* by the common block size `b`, which in the exponent becomes
`x^b` — log₂ b squarings — plus padding every block to the longest; the
trampoline collapses the aligned region to 2-instruction slots, so the
scaling is the single squaring `x²`. Other layouts exist — e.g. a
memory-resident address table dispatched with a single jump, worthwhile for
many repeated small matches — but only the trampoline is implemented.)

**Soundness**: nothing in the dispatch bounds `x` — a scrutinee outside
`[0, n)` jumps to an arbitrary pc. A hinted value must be range-checked first
(`assert log(x) < n`, 3 cycles), as in leanVM. Case bodies are branch-local,
like `if` branches.

### `match_range`

```python
r = match_range(log(x), range(0, 6), lambda i: f(i))
a, b = match_range(log(x), range(0, 2), lambda i: g(1), range(2, 6), lambda i: g(i))
```

A `match` with generated arms (leanVM's `match_range`): arm `j` is the lambda
body with the parameter replaced by the **integer literal** `j` — usable as a
field constant or a compile-time index — expanded at parse time over the
contiguous `(range, lambda)` pairs, which must start at 0. Unlike `match`
cases, the arms produce values: every arm writes its results into the same
fresh cells (write-once is sound — exactly one arm executes), and the targets
name those cells after the join. Multiple targets take a multi-return call as
the arm body. The whole call sits on one line (no line continuation), and the
`match` soundness caveat applies unchanged.

**Dispatched-call fusion.** When *every* arm is a call to the same function
with identical runtime arguments — the common `lambda k: f(a, b, k)`, where
only a `Const` argument varies — the compiler builds the callee frame **once**
and the dispatch jumps straight into the selected specialization's entry, which
returns past the join. Each taken arm is then just the trampoline's two
instructions (`SET entry; JUMP`) instead of a full call: no per-arm frame
setup, call jump, or return jump. (The `walk`-per-digit dispatch in the XMSS
verifier is the motivating case.)

Statements without effect are rejected.

## Assertions

### `assert a == b`

A proof-enforced equality: 2 cycles (`XOR` into a fresh cell + `SET` it to
zero, using write-once double-write as the assert).

### Range checks: `assert log x < log Y` and `assert log x < k`

The *range check in the exponent*: proves `x ∈ {g^0, g^1, …, g^{k-1}}`, i.e.
`log_g(x) < k`. The bound is compile-time — either `log GEN ** k` or a plain
integer exponent `k` — with `1 ≤ k ≤ 2^16` (the minimum memory size, which
keeps the gadget sound for every memory size the prover may announce).
`log x` and `log(x)` both parse; the parenthesized form is the valid-Python
spelling. A bare `assert x < y` is rejected: field elements have no order,
only their logs do.

```python
assert log(x) < log(GEN ** 8)
assert log(x) < 8               # the same check
```

Cost: **3 cycles** (leanVM's DEREF range-check trick, in the exponent) plus
one amortized `SET` per distinct bound per frame:

1. `DEREF` through `x` — the dereferenced address must be one of the memory's
   `2^h` g-power addresses, so the memory bus itself proves `x = g^e`, `e < 2^h`;
2. `MUL x·y` into the write-once cell holding `g^{k-1}` — the runner
   back-solves the complement `y = g^{k-1-e}` (the one unknown operand of a
   known product), and the double-write asserts `x·y = g^{k-1}`;
3. `DEREF` through `y` — bounds the complement; a "negative" `k-1-e` would
   wrap to `≈ 2^128`, far beyond any memory size, so together `e ≤ k-1`.

The two `DEREF` target cells are unconstrained touches, back-filled at the end
of execution. A failing check surfaces at witness generation as the
complement's `DEREF` panic ("not a small g-power … a failed range check").

## BLAKE3

```python
h = StackBuf(2)
blake3(a, b, h)                    # digest of (a, b) written into h
blake3(t[0:2], t[x:x + 2], t[4:6])  # slices of one large StackBuf
blake3(h, hb[0:2], hb[2:4])         # HeapBuf slices, input and output
blake3(hb[i:i + 2], h, hb[j:j + 2])  # runtime-indexed heap slices (i, j g-powers)
```

`blake3(a, b, out)` is a **statement**: it compresses the two 256-bit operands
`a`, `b` (64 bytes) and writes the 32-byte digest into the 2-cell run `out`.
Operands are size-2 `StackBuf`s or 2-cell slices:

- **stack operands** are read/written in place — zero copies; a self-hash
  `blake3(h, h, out)` aliases one pair into both inputs;
- **heap slices** are bridged through the stack (the `BLAKE3` instruction
  addresses only frame cells): +2 `DEREF`s per heap operand, inputs pulled
  before the hash, outputs stored after — the same instruction either way,
  write-once memory fills whichever side is unset.

If `out` was already written, the statement *asserts* the digest equals it —
write-once turning the hash into a verification, which is exactly what a
signature verifier wants.

The compression is proven by the vendored flock BLAKE3 R1CS (see `doc.pdf`
§BLAKE3); one instruction per 64→32-byte compression.

## Hints — `hint_witness(dest, "name")`

```python
sb = StackBuf(2)
hint_witness(sb, "r")        # fill the whole StackBuf
hint_witness(hb[0:3], "h")   # or any StackBuf/HeapBuf slice (any length)
assert log(sb[0]) < 8        # hinted values are UNCONSTRAINED: pin them down
```

Prover-supplied data (leanVM's `hint_witness`): a stream is a sequence of
**entries** — one slice of values per `hint_witness` call, and the same
symbol may be hinted many times. Each call pops the stream's next entry
(whose length must match the destination run) and writes it into `dest`
through the hint mechanism, at **zero cycles**. The values are completely
unconstrained; the program must constrain them itself (asserts, range checks,
hashes) — an unconstrained hint consumed by anything security-relevant is a
critical vulnerability. Runtime-start heap slices (`buf[i:i + k]`, `k` a
literal) work too.

The prover supplies streams with `program.set_witness("name", entries)`
(`Vec<Vec<F128>>`); test programs declare them as annotations, one line per
entry — repeated lines with the same name are its successive entries:

```python
# witness r: GEN ** 5, 12
# witness r: 9
```

## Cost cheat sheet

| construct | instructions |
|---|---|
| `x = <literal>` / `GEN ** k` | 1 `SET` |
| `a + b` | 1 `XOR` |
| `a * b` | 1 `MUL` |
| heap read / store `buf[i]` | 1 `DEREF`; +1 `MUL` for a *runtime* index (a compile-time g-power offset folds into the `DEREF` — free) |
| stack read / store `sa[k]` | 0 (direct cell addressing) |
| `assert a == b` | 2 |
| `assert log x < k` | 3 (+1 `SET` amortized per bound per frame) |
| `if a == b: …` | 3 (+2 to skip a non-empty `else`; +2 amortized `self-fp` per branching function); **0 if the condition is compile-time** |
| `match log(x): …` | ≈ 7, independent of the case count |
| `… = match_range(log(x), …)` | the `match` + the arm; results written into the targets directly. Uniform-call arms (`lambda k: f(a, b, k)`) **fuse**: one shared frame + dispatch to entry, each arm just `SET`+`JUMP` |
| function call | ≈ `n_args + n_returns + 4` (0 when the callee is `@unroll`) |
| `mul_range` iteration | body + ≈ 1 `MUL` + 1 `XOR` + call overhead |
| `unroll` iteration | body only (compile-time replication) |
| `blake3(a, b, out)` | 1 (+2 `DEREF`s per heap operand, +1 `MUL` per runtime slice start) |
| `hint_witness(dest, "name")` | 0 (+1 `MUL` for a runtime slice start) |

## Example

Fibonacci in the exponent (`tests/programs/fibonacci.py`): `fib[g^k]` holds
`GEN ** F_k`, so one field `MUL` is one Fibonacci step.

```python
# public_input: GEN ** 89, GEN ** 89
from snark_lib import *


def main():
    fib = HeapBuf(12)
    fib[1] = GEN ** 0  # F_0 = 0
    fib[GEN] = GEN     # F_1 = 1
    for i in mul_range(1, GEN ** 10):
        fib[i * GEN * GEN] = fib[i] * fib[i * GEN]
    out = fib[GEN ** 11]
    assert out == GEN ** 89  # F_11 = 89
    assert log(out) < log(GEN ** 128)
    p = GEN ** 0
    p[1] = out
    p[GEN] = out
    return
```

## Not (yet) supported

Mutable variables and compound assignment; conditions other than field
(in)equality; `match` defaults (`case _`) and non-contiguous cases; top-level
constant *arrays* (only scalar constants — see "Global constants and
placeholders"); multi-file imports; `Const` parameters as `mul_range`
or range-check bounds (a substituted literal is a bit-pattern element, not
the g-power a bound needs); runtime slice starts on a `StackBuf`; runtime
range-check bounds (`assert log a < log b` with runtime `b`); custom hint
kinds beyond `hint_witness`; precompiles beyond `BLAKE3`.
