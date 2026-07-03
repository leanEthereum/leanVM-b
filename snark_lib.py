# Import this in zkDSL .py files (`from snark_lib import *`) to make them
# valid Python for editors and linters. The leanVM-b compiler skips the
# import; it does not include other source files (single-file programs only).


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
    `assert log(x) < k`) proves `x ∈ {GEN**0, …, GEN**(k-1)}` in 3 cycles."""
    _ = x
    return 0


def mul_range(start, stop) -> list:
    """The loop counter walked in the exponent: from element `start` to `stop`
    (exclusive), ×GEN each iteration. Both bounds are compile-time powers of
    GEN (`1`, `GEN`, or `GEN ** k`)."""
    _ = start, stop
    return []


def HeapBuf(n: int) -> _Elt:
    """Allocate a fresh, disjoint heap buffer of `n` cells; evaluates to its
    pointer (a fresh g-power)."""
    _ = n
    return _Elt()


def StackBuf(n: int) -> _Elt:
    """Allocate `n` consecutive frame (stack) cells. A size-2 StackBuf holds a
    256-bit value and is a valid `blake3` operand."""
    _ = n
    return _Elt()


def blake3(a, b, out) -> None:
    """The BLAKE3 compression of the two 256-bit operands `a`, `b` — size-2
    StackBufs, or 2-cell slices `buf[lo:hi]` of larger ones — written into the
    existing 2-cell run `out` (write-once: if `out` was already written, this
    asserts it equals the digest)."""
    _ = a, b, out
