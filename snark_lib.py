# Import this in zkDSL .py files (`from snark_lib import *`) to make them
# valid Python for editors and linters. The leanVM-b compiler skips the
# import; it does not include other source files (single-file programs only).

from typing import Any, Optional

Const = Any
"""Parameter annotation: `def f(k: Const, x):` — `k` is a compile-time
argument; the compiler specializes the function per distinct constant."""


class _Elt:
    """A 192-bit machine word in E = GF(2^192), represented as a cubic tower
    over K = GF(2^64). Indices and addresses are K-valued powers of GEN —
    "in the exponent": `GEN ** k` is the k-th index and `x * GEN` its successor.
    A heap pointer is K-valued too; `buf[i]` is the write-once cell at `buf * i`."""

    def __add__(self, other):  # field addition = XOR
        _ = other
        return _Elt()

    __radd__ = __add__

    def __mul__(self, other):  # tower-field product
        _ = other
        return _Elt()

    __rmul__ = __mul__

    def __truediv__(self, other):  # field division a / b = a · b⁻¹ (single slash)
        _ = other
        return _Elt()

    __rtruediv__ = __truediv__

    def __pow__(self, k: int):
        _ = k
        return _Elt()

    def __getitem__(self, idx):  # heap read m[self · idx]
        _ = idx
        return _Elt()

    def __setitem__(self, idx, value):  # heap store m[self · idx] (write-once)
        _ = idx, value


def f192(c0: int, c1: int, c2: int) -> _Elt:
    """Construct a field constant from its three little-endian GF(2^64) limbs."""
    _ = c0, c1, c2
    return _Elt()


GEN = _Elt()
"""The fixed generator g = x of K^× = GF(2^64)^× (order 2^64 - 1)."""


def hint_decompose_bits(bits, value, nbits: int) -> None:
    """Computed advice: the prover writes the `nbits` bits of `value` into the
    `bits` buffer. UNCONSTRAINED — the caller must check booleanity and that the
    bits reconstruct `value` (a range check that `value < 2^nbits`)."""
    _ = bits, value, nbits


def hint_decompose_bits_exponent(bits, x, nbits: int) -> None:
    """Computed advice: the prover writes the `nbits` bits of n, where x = g^n
    (recovered by a bounded discrete log at witness generation), into `bits`.
    UNCONSTRAINED — the caller checks booleanity and Π g^(bit_j 2^j) == x."""
    _ = bits, x, nbits


def hint_log2_ceil(bits, nbits: int, floor: int) -> _Elt:
    """Computed advice: returns `g^max(log2_ceil(v), floor)`, where `v` is the
    integer the `nbits`-cell `bits` buffer decodes to. The prover fills it at
    witness-generation; it is UNCONSTRAINED, so the caller must verify it (see the
    log2_ceil_word / log2_ceil_in_the_exponent wrappers in the recursion guest). log2 = base-2 log of the integer, NOT the
    discrete log base g that `log(...)` means."""
    _ = bits, nbits, floor
    return _Elt()


def log(x) -> int:
    """The discrete log base GEN: `x = GEN ** log(x)`. Only meaningful inside
    a range-check assert — `assert log(x) < log(GEN ** k)` (equivalently
    `assert log(x) < k`) proves `x ∈ {GEN**0, …, GEN**(k-1)}` in 3 cycles —
    or as the scrutinee of `match` / `match_range`."""
    _ = x
    return 0

# @inline decorator (does nothing in Python execution)
def inline(fn):
    return fn


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


def pack64x2(a, b) -> _Elt:
    """Prove that `a` and `b` are GF(2^64)-valued machine words and return
    their canonical 128-bit packing `(a.c0, b.c0, 0)` as one GF(2^192) word.
    This is one VM instruction."""
    _ = a, b
    return _Elt()


def pack64x2_into(a, b, out) -> None:
    """The destination-target form of `pack64x2`: assert that `out` is the
    canonical packing `(a.c0, b.c0, 0)`. All three arguments are scalar cells."""
    _ = a, b, out


def hint_f192_limbs(dest, value) -> None:
    """Computed advice: write the first `len(dest)` GF(2^64) coordinate limbs
    of `value` into a 1-to-3-cell StackBuf. UNCONSTRAINED; callers bind the
    result with `PACK64X2` and/or field reconstruction."""
    _ = dest, value


def blake3(
    a,
    b,
    out,
    *,
    cv=None,
    counter: Optional[int] = None,
    chunk: Optional[int] = None,
    block_len: int = 64,
    flags: Optional[int] = None,
    step: Optional[int] = None,
    end: int = 0,
    root: int = 0,
    parent: int = 0,
) -> None:
    """One standard BLAKE3 compression of the two 256-bit message operands
    `a`, `b`, written into the 2-cell run `out` (write-once: if `out` was
    already written, this asserts it equals the digest).

    With no keywords this hashes exactly 64 bytes using the standard IV,
    counter zero, block length 64, and CHUNK_START | CHUNK_END | ROOT. `cv`
    selects a 2-cell chaining value and requires an explicit structured-mode
    keyword such as `step` or `flags`; `counter`/`chunk`, `block_len`, and
    `flags` set the compile-time metadata directly. In inferred-flag mode,
    `step=0` marks CHUNK_START, while `end`, `root`, and `parent` add the
    corresponding BLAKE3 flags. Bytes after `block_len` must be zero-filled by
    the program.

    Message, chaining-value, and output operands are size-2 StackBufs or
    2-cell slices `buf[lo:hi]` of larger StackBufs or HeapBufs (heap inputs are
>>>>>>> origin/main
    bridged through the stack, one DEREF per cell)."""
    _ = a, b, out, cv, counter, chunk, block_len, flags, step, end, root, parent
