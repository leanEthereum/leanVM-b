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

## Variables

Bindings are **immutable**: `x = e` names a fresh cell. Re-binding a name is
allowed (it's a new cell; the old value is unaffected), but there is no
mutation and no compound assignment.

A name bound to an integer literal (`x = 2`) additionally acts as a
**compile-time index constant** — usable in stack indexes and slice bounds
(see below). Any other re-binding clears that role.

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

The index is a runtime field element; cell `k` of the buffer lives at address
`buf · g^k`. A read or store is one `DEREF` (plus one `MUL` for the `buf·i`
pointer product). There are no bounds checks — the buffer is a region
convention, not a checked type.

### `StackBuf(n)` — frame-cell runs, indexed by compile-time integers

```python
sa = StackBuf(3)      # n consecutive cells of the current frame
sa[0] = 3             # direct frame cell: zero instructions to address
sa[2] = sa[0] + sa[1]
x = 1
v = sa[x + 1]         # indexes: literals, literal-bound names, + and * of those
```

Stack indexes are **compile-time integers** and index arithmetic is *integer*
arithmetic (`x + 1` above is 2 — index space, not the field XOR the same
syntax means elsewhere). Bounds are checked at compile time. A `StackBuf`
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
each iteration, and stops on reaching `stop` (exclusive). Both bounds are
compile-time powers of `GEN` (`1`, `GEN`, or `GEN ** k`). An empty range
(`lo == hi`) compiles to nothing.

Lowering: the body becomes a tail-recursive helper function whose exit test is
folded into the recursion's `JUMP` condition — one call per iteration, no
separate is-zero gadget. Free variables of the body are captured **by value**
as extra parameters; a `HeapBuf` pointer threads through fine, a `StackBuf`
does not (compile error).

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

## Cost cheat sheet

| construct | instructions |
|---|---|
| `x = <literal>` / `GEN ** k` | 1 `SET` |
| `a + b` | 1 `XOR` |
| `a * b` | 1 `MUL` |
| heap read / store `buf[i]` | 1 `MUL` (pointer) + 1 `DEREF` |
| stack read / store `sa[k]` | 0 (direct cell addressing) |
| `assert a == b` | 2 |
| `assert log x < k` | 3 (+1 `SET` amortized per bound per frame) |
| `if a == b: …` | 3 (+2 to skip a non-empty `else`; +2 amortized `self-fp` per branching function) |
| `match log(x): …` | ≈ 7, independent of the case count |
| `… = match_range(log(x), …)` | the `match`, + 1 `MUL` copy per target |
| function call | ≈ `n_args + n_returns + 4` |
| `mul_range` iteration | body + ≈ 1 `MUL` + 1 `XOR` + call overhead |
| `blake3(a, b, out)` | 1 (+2 `DEREF`s per heap operand, +1 `MUL` per runtime slice start) |

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
constants; multi-file imports; `Const`/typed parameters and `@inline`;
runtime slice starts on a `StackBuf`; runtime range-check bounds
(`assert log a < log b` with runtime `b`); custom hints; precompiles beyond
`BLAKE3`.
