# Import this in zkDSL .py files (`from snark_lib import *`) to make them
# valid Python for editors and linters. The leanVM-b compiler skips the
# import; it does not include other source files (single-file programs only).

from typing import Any

Const = Any
"""Parameter annotation: `def f(k: Const, x):` — `k` is a compile-time
argument; the compiler specializes the function per distinct constant."""


class _Elt:
    """A GF(2^128) element (GHASH form). Indices and addresses are carried as
    powers of GEN — "in the exponent": `GEN ** k` is the k-th index, `x * GEN`
    its successor. A heap pointer is an element too, its cells addressed by
    g-power offsets (`buf[i]` is the cell at `buf * i`, write-once)."""

    def __add__(self, other):  # field addition = XOR
        _ = other
        return _Elt()

    __radd__ = __add__

    def __mul__(self, other):  # field (GHASH) product
        _ = other
        return _Elt()

    __rmul__ = __mul__

    def __pow__(self, k: int):
        _ = k
        return _Elt()

    def __getitem__(self, idx):  # heap read m[self · idx]
        _ = idx
        return _Elt()

    def __setitem__(self, idx, value):  # heap store m[self · idx] (write-once)
        _ = idx, value


GEN = _Elt()
"""The fixed generator g = x of GF(2^128)^× (order 2^128 - 1)."""


def log(x) -> int:
    """The discrete log base GEN: `x = GEN ** log(x)`. Only meaningful inside
    a range-check assert — `assert log(x) < log(GEN ** k)` (equivalently
    `assert log(x) < k`) proves `x ∈ {GEN**0, …, GEN**(k-1)}` in 3 cycles —
    or as the scrutinee of `match` / `match_range`."""
    _ = x
    return 0


def match_range(value: int, *args):
    """A `match` with generated arms: `match_range(log(x), range(a, b),
    lambda i: …, …)` expands to one arm per integer of the contiguous ranges
    (which must start at 0), the lambda applied to the concrete value; the
    results bind to the assignment targets. In Python execution, finds the
    matching range and calls its lambda."""
    for i in range(0, len(args), 2):
        rng, fn = args[i], args[i + 1]
        if value in rng:
            return fn(value)
    raise AssertionError(f"value {value} not in any range")


def mul_range(start, stop) -> list:
    """The loop counter walked in the exponent: from element `start` to `stop`
    (exclusive), ×GEN each iteration. Both bounds are compile-time powers of
    GEN (`1`, `GEN`, or `GEN ** k`)."""
    _ = start, stop
    return []


def unroll(a: int, b: int) -> range:
    """Compile-time unrolling: the body is replicated for i = a, …, b-1, the
    counter substituted as an integer literal (usable as a stack index, slice
    bound, or `Const` argument). Bounds are compile-time integers — including
    `Const` parameters."""
    return range(a, b)


def HeapBuf(n) -> _Elt:
    """Allocate a fresh, disjoint heap buffer; evaluates to its pointer (a
    fresh g-power). `n` is either an integer literal (compile-time size), or a
    runtime value carrying the cell count *in the exponent* — `g^k` allocates
    `k` cells, so a size derived from a g-power count is plain field arithmetic
    (`HeapBuf(cnt * cnt)` is `2·log(cnt)` cells). Allocation is a prover
    convenience, so an under-size only trips write-once."""
    _ = n
    return _Elt()


def StackBuf(n: int) -> _Elt:
    """Allocate `n` consecutive frame (stack) cells. A size-2 StackBuf holds a
    256-bit value and is a valid `blake3` operand."""
    _ = n
    return _Elt()


def hint_witness(dest, name: str) -> None:
    """Fill `dest` — a StackBuf, or a StackBuf/HeapBuf slice of any length —
    with the next ENTRY (a slice of values) of the named prover witness
    stream; the same symbol may be hinted many times, each call popping the
    next entry (`Program::set_witness`; test programs declare one
    `# witness name: v1, …` line per entry). Zero cycles, and the values are
    completely UNCONSTRAINED: the program must constrain them itself
    (asserts, range checks, hashes)."""
    _ = dest, name


def blake3(a, b, out) -> None:
    """The BLAKE3 compression of the two 256-bit operands `a`, `b`, written
    into the 2-cell run `out` (write-once: if `out` was already written, this
    asserts it equals the digest). Operands are size-2 StackBufs or 2-cell
    slices `buf[lo:hi]` of larger StackBufs or of HeapBufs (heap slices are
    bridged through the stack, one DEREF per cell)."""
    _ = a, b, out
