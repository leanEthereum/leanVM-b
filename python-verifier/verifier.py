from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache, reduce
from itertools import accumulate, islice, repeat
from operator import mul
from pathlib import Path
from struct import pack, unpack


class VerificationError(Exception):
    """Invalid proof."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


# Field arithmetic ------------------------------------------------------------


def _base_mul(left: int, right: int) -> int:
    product = 0
    while right:
        if right & 1:
            product ^= left
        right >>= 1
        left <<= 1
    low, high = product & (2**64 - 1), product >> 64
    folded = low ^ high ^ (high << 1) ^ (high << 3) ^ (high << 4)
    overflow = folded >> 64
    return ((folded & (2**64 - 1)) ^ overflow ^ (overflow << 1) ^ (overflow << 3) ^ (overflow << 4)) & (2**64 - 1)


@dataclass(frozen=True, slots=True)
class K:
    """GF(2^64) = F2[x]/(x^64 + x^4 + x^3 + x + 1)"""

    value: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.value, int) or isinstance(self.value, bool) or not 0 <= self.value <= (2**64 - 1):
            raise ValueError("a K element is a 64-bit unsigned integer")

    def __index__(self) -> int:
        return self.value

    def to_bytes(self) -> bytes:
        """Its transport image: one 64-bit little-endian word."""
        return self.value.to_bytes(8, "little")

    def __bool__(self) -> bool:
        return bool(self.value)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, K):
            return self.value == other.value
        return isinstance(other, int) and not isinstance(other, bool) and self.value == other

    def __hash__(self) -> int:
        return hash(self.value)

    def __add__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(self.value ^ rhs.value)

    __radd__ = __add__

    def __mul__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(_base_mul(self.value, rhs.value))

    __rmul__ = __mul__

    def __repr__(self) -> str:
        return f"K(0x{self.value:016x})"


def _as_k(value: object) -> K | None:
    if isinstance(value, K):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= 2**64 - 1:
        return K(value)
    return None


@dataclass(frozen=True, slots=True, init=False)
class E:
    """K[y]/(y^3 + y + 1): the challenge field, a degree-3 extension of K. Limbs may be given as plain integers, which are lifted."""

    c0: K
    c1: K
    c2: K

    def __init__(self, c0: K | int = 0, c1: K | int = 0, c2: K | int = 0) -> None:
        object.__setattr__(self, "c0", c0 if isinstance(c0, K) else K(c0))
        object.__setattr__(self, "c1", c1 if isinstance(c1, K) else K(c1))
        object.__setattr__(self, "c2", c2 if isinstance(c2, K) else K(c2))

    @classmethod
    def from_bytes(cls, data: bytes) -> E:
        require(len(data) == 24, "a field element must contain exactly 24 bytes")
        return cls(*unpack("<3Q", data))

    def to_bytes(self) -> bytes:
        return pack("<3Q", self.c0, self.c1, self.c2)

    @staticmethod
    def lift(value: object) -> E:
        """`value` as an extension element; anything that is not one is an error."""
        if isinstance(value, E):
            return value
        lifted = _as_k(value)
        if lifted is not None:
            return E(lifted)
        raise TypeError(f"cannot use {type(value).__name__} as a field element")

    def __int__(self) -> int:
        return self.c0.value | self.c1.value << 64 | self.c2.value << 128

    def __bool__(self) -> bool:
        return bool(self.c0 or self.c1 or self.c2)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, E):
            return self.c0 == other.c0 and self.c1 == other.c1 and self.c2 == other.c2
        return not (self.c1 or self.c2) and self.c0 == other

    def __hash__(self) -> int:
        return hash(int(self))

    def __add__(self, other: object) -> E:
        rhs = self.lift(other)
        return E(self.c0 + rhs.c0, self.c1 + rhs.c1, self.c2 + rhs.c2)

    __radd__ = __add__

    def __mul__(self, other: object) -> E:
        rhs = self.lift(other)
        # y^3 = y + 1 folds the degree-4 product back into three limbs.
        p0 = self.c0 * rhs.c0
        p1 = self.c0 * rhs.c1 + self.c1 * rhs.c0
        p2 = self.c0 * rhs.c2 + self.c1 * rhs.c1 + self.c2 * rhs.c0
        p3 = self.c1 * rhs.c2 + self.c2 * rhs.c1
        p4 = self.c2 * rhs.c2
        return E(p0 + p3, p1 + p3 + p4, p2 + p4)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> E:
        if exponent < 0:
            return self.inv() ** -exponent
        base, out, n = self, ONE, exponent
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> E:
        require(bool(self), "division by zero in GF(2^192)")
        return self ** (2**192 - 2)

    def __truediv__(self, other: object) -> E:
        rhs = self.lift(other)
        return self * rhs.inv()

    def __repr__(self) -> str:
        return f"E(0x{self.c2.value:016x}{self.c1.value:016x}{self.c0.value:016x})"


ZERO = E(0)
ONE = E(1)
GEN = E(2)
Y = E(0, 1)  # the tower generator, y^3 = y + 1


# BLAKE2s and digests ---------------------------------------------------------

BLAKE2S_IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)  # fmt: skip
BLAKE2S_SIGMA = ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15), (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3), (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4), (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8), (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13), (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9), (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11), (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10), (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5), (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0))  # fmt: skip
BLAKE2S_G_LANES = ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14))  # fmt: skip


def blake2s_hash(data: bytes) -> Digest:
    """Standard 32-byte unkeyed BLAKE2s-256 hash."""
    return Digest(hashlib.blake2s(data).digest())


@dataclass(frozen=True, slots=True)
class Digest:
    """256 bits"""

    value: bytes

    def __post_init__(self) -> None:
        require(len(self.value) == 32, "a digest is 256 bits")

    def halves(self) -> tuple[E, E]:
        """Its two 128-bit halves, the one form a digest travels in."""
        w0, w1, w2, w3 = unpack("<4Q", self.value)
        return (E(w0, w1), E(w2, w3))

    @classmethod
    def from_halves(cls, low: E, high: E) -> Digest:
        require(not (low.c2 or high.c2), "a digest half is 128-bit")
        return cls(pack("<4Q", low.c0, low.c1, high.c0, high.c1))


# Multilinear and stacking helpers --------------------------------------------


type MultilinearPoint = tuple[E, ...]


def eq_kernel(point: Sequence[E]) -> list[E]:
    out = [ONE]
    for r in point:
        out = [v * (ONE + r) for v in out] + [v * r for v in out]
    return out


def multilinear_eval(mle: Sequence[K | E], point: Sequence[E]) -> E:
    require(len(mle) == 2 ** len(point), "multilinear table has the wrong size")
    cur = [E.lift(value) for value in mle]
    for r in point:
        cur = [cur[2 * i] * (ONE + r) + cur[2 * i + 1] * r for i in range(len(cur) // 2)]
    return cur[0]


def log2_ceil(value: int) -> int:
    return max(0, (value - 1).bit_length())


def log2_strict(value: int) -> int:
    require(value > 0 and not value & (value - 1), "expected a power of two")
    return value.bit_length() - 1


@dataclass(frozen=True)
class Placement:
    """Where something of 2^variables entries sits in a stacked cube, as returned
    by `stack_offsets`: one committed column in the witness, or one block of a bus
    side in its leaf cube."""

    variables: int
    offset: int

    @property
    def virtual(self) -> bool:
        return self is VIRTUAL

    @property
    def selector(self) -> int:
        """Which slice of the stacked cube it occupies."""
        return self.offset >> self.variables


VIRTUAL = Placement(-1, 0)
"""An entry stacked elsewhere, taking no room here (`Placement::VIRTUAL` in Rust)."""


def stack_offsets(sizes: Sequence[int | None]) -> tuple[list[Placement], int]:
    """Place a block of 2^size at the next multiple of its own size, largest first.
    Ties keep input order, so both sides derive the same layout from the sizes alone.
    A None size is an entry that is committed elsewhere and takes no room here.
    Returns each entry's placement and the log2 of the padded total.
    """
    offsets = [0] * len(sizes)
    total = 0
    present = [(index, size) for index, size in enumerate(sizes) if size is not None]
    for index, size in sorted(present, key=lambda item: (-item[1], item[0])):
        offsets[index] = total
        total += 2**size
    placed = [VIRTUAL if size is None else Placement(size, offset) for size, offset in zip(sizes, offsets, strict=True)]
    return placed, log2_ceil(max(total, 1))


def eq_eval(left: Sequence[E], right: Sequence[E]) -> E:
    result = ONE
    for x, y in zip(left, right, strict=True):
        result *= ONE + x + y
    return result


def dot(left: Sequence[K | E], right: Sequence[K | E]) -> E:
    """`Σ_i left[i] · right[i]` in E."""
    result = ZERO
    for x, y in zip(left, right, strict=True):
        result += E.lift(x) * y
    return result


def _selector_point(selector: int, length: int) -> MultilinearPoint:
    return tuple(E(selector >> bit & 1) for bit in range(length))


def selector_eq(selector: int, point: Sequence[E]) -> E:
    return eq_eval(_selector_point(selector, len(point)), point)


def index_mle(point: MultilinearPoint) -> E:
    """MLE of ``[1, g, g^2, ...]`` at an LSB-first point."""
    result = ONE
    generator_power = GEN
    for challenge in point:
        result *= ONE + challenge * (ONE + generator_power)
        generator_power **= 2
    return result


def poly_eval(coefficients: Sequence[E], point: E) -> E:
    """A polynomial at `point`, by Horner over its coefficients, constant first."""
    return reduce(lambda acc, c: acc * point + c, reversed(coefficients), ZERO)


# Proof transport ------------------------------------------------------------


@dataclass(frozen=True)
class Proof:
    stream: tuple[E, ...]
    merkle_openings: bytes

    @classmethod
    def load(cls, stream: Path, merkle_openings: Path) -> Proof:
        data = stream.read_bytes()
        require(len(data) % 24 == 0, "the stream is not a whole number of field elements")
        return cls(tuple(E.from_bytes(data[at : at + 24]) for at in range(0, len(data), 24)), merkle_openings.read_bytes())


# Fiat--Shamir ---------------------------------------------------------------


# Every block puts its tag in lane 3 and its data in lanes 0..2, so one role is
# one constant in one place and no two roles can alias.
DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQUEEZE = 4
DS_POW_BASE = 5
DS_POW_NONCE = 6


def compress(left: Sequence[K | int], right: Sequence[K | int]) -> tuple[int, int, int, int]:
    """Hash two four-word operands, a word being a plain integer or the K element standing for it."""
    # Nothing downstream would catch a short operand: it would simply hash to a
    # different value.
    require(len(left) == len(right) == 4, "compression operands must contain four words")
    return unpack("<4Q", blake2s_hash(b"".join(int(x).to_bytes(8, "little") for x in (*left, *right))).value)


class Transcript:
    def __init__(self, proof: Proof, label: bytes, statement: Sequence[E]) -> None:
        self.proof = proof
        self.state = (0, 0, 0, 0)
        self.stream_offset = 0
        self.opening_offset = 0
        self.absorb_bytes(b"leanvm-b/transcript/v4-blake2s")
        self.absorb_bytes(label)
        for value in statement:
            self.observe(value)

    def observe(self, value: E) -> None:
        self.state = compress(self.state, (value.c0, value.c1, value.c2, DS_SCALAR))

    def absorb_bytes(self, data: bytes) -> None:
        self.state = compress(self.state, (len(data), 0, 0, DS_LEN))
        for offset in range(0, len(data), 24):
            block = data[offset : offset + 24].ljust(24, b"\0")
            words = [int.from_bytes(block[i : i + 8], "little") for i in (0, 8, 16)]
            self.state = compress(self.state, (*words, DS_BYTE))

    def sample(self) -> E:
        self.state = compress(self.state, (0, 0, 0, DS_SQUEEZE))
        return E(*self.state[:3])

    def samples(self, count: int) -> list[E]:
        return [self.sample() for _ in range(count)]

    def _next(self) -> E:
        require(self.stream_offset < len(self.proof.stream), "proof stream exhausted")
        value = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        return value

    def scalar(self) -> E:
        value = self._next()
        self.observe(value)
        return value

    def scalars(self, count: int) -> list[E]:
        return [self.scalar() for _ in range(count)]

    def grind_check(self, bits: int) -> None:
        require(0 <= bits < 64, "invalid grinding width")
        nonce = self._next()
        block = (nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE)
        digest = compress(compress(self.state, (0, 0, 0, DS_POW_BASE)), block)[0]
        valid = nonce == ZERO if bits == 0 else digest & (2**bits - 1) == 0
        self.state = compress(self.state, block)
        require(valid, "invalid grinding nonce")

    def _take(self, length: int) -> bytes:
        end = self.opening_offset + length
        require(end <= len(self.proof.merkle_openings), "Merkle opening missing")
        chunk = self.proof.merkle_openings[self.opening_offset : end]
        self.opening_offset = end
        return chunk

    def merkle(self, root: Digest, block_length: int, queries: Sequence[int], leaf_words: int) -> list[tuple[K, ...]]:
        """Pull one opening per query and authenticate each against `root`.

        Not absorbed: an opening's binding is the Merkle structure itself, which
        is checked here rather than by the Fiat-Shamir state. Returns the rows in query
        order, so a repeated position simply re-opens the same authenticated row.
        """
        height = log2_strict(block_length)
        rows = []
        for query in queries:
            require(0 <= query < block_length, "Merkle query is out of range")
            # The leaf's bytes are the committer's preimage as they lie on the wire.
            leaf = self._take(8 * leaf_words)
            node = blake2s_hash(leaf)
            for level in range(height):
                sibling = Digest(self._take(32))
                node = _hash_pair(node, sibling) if query >> level & 1 == 0 else _hash_pair(sibling, node)
            require(node == root, "Merkle root mismatch")
            rows.append(tuple(K(word) for word in unpack(f"<{leaf_words}Q", leaf)))
        return rows

    def round_poly(self, count: int, claim: E, equality: E | None = None) -> list[E]:
        """Read one sumcheck round polynomial, in coefficients.

        The message is every coefficient but one; the split identity fixes the
        remaining one to `claim`, so it is neither sent nor bound, and deriving it
        is an addition either way. A plain round has `h(0) + h(1) = c1 + ... + cd`,
        which fixes `c1`; a round whose eq factor `r` the protocol pulled out has
        `c0 + r·(c1 + ... + cd)`, which fixes `c0`.
        """
        if equality is None:
            constant, tail = self.scalar(), self.scalars(count - 2)
            return [constant, claim + sum(tail, ZERO), *tail]
        tail = self.scalars(count - 1)
        return [claim + equality * sum(tail, ZERO), *tail]

    def finish(self) -> None:
        require(self.stream_offset == len(self.proof.stream), "proof stream not fully consumed")
        require(self.opening_offset == len(self.proof.merkle_openings), "Merkle openings not fully consumed")


# GKR product triple ---------------------------------------------------------


@dataclass(frozen=True)
class ProductTriple:
    roots: tuple[E, E, E]
    point: MultilinearPoint
    values: tuple[E, E, E]


def verify_product_triple(depth: int, transcript: Transcript) -> ProductTriple:
    root_values = transcript.scalars(3)
    roots = (root_values[0], root_values[1], root_values[2])
    combine = transcript.sample()
    point: list[E] = []
    values = list(roots)

    layer = depth
    while layer > 0:
        # Layers are taken two at a time (radix four). An odd depth leaves one
        # binary layer, which can only be the root-most one, where no prior point
        # exists to fold against.
        width = 1 if layer % 2 else 2
        round_count = depth - layer
        require(width == 2 or round_count == 0, "binary GKR layer is not root-most")
        claim = values[0] + combine * (values[1] + combine * values[2])

        round_point: list[E] = []
        for prior in point[:round_count]:
            # Four independent coefficients determine the degree-four round
            # polynomial: with `difference = q(0) + q(1)`, the incoming claim fixes
            # the constant one and characteristic two fixes the linear one.
            difference, c2, c3, c4 = transcript.scalars(4)
            challenge = transcript.sample()
            round_point.append(challenge)
            c0 = claim + prior * difference
            c1 = difference + c2 + c3 + c4
            claim = c0 + challenge * (c1 + challenge * (c2 + challenge * (c3 + challenge * c4)))

        tails = [transcript.scalars(2**width) for _ in range(3)]
        products = [reduce(mul, tail) for tail in tails]
        expected = products[0] + combine * (products[1] + combine * products[2])
        require(claim == expected, f"GKR layer {layer}: tail mismatch")
        challenges = transcript.samples(width)
        values = [multilinear_eval(tail, challenges) for tail in tails]
        combine = transcript.sample()
        point = [*challenges, *round_point]
        layer -= width

    return ProductTriple(roots, tuple(point), (values[0], values[1], values[2]))


# Bus balance and decomposition ---------------------------------------------


@dataclass
class Form:
    """A polynomial of degree at most 2 in a row's columns, one table's own."""

    terms: dict[tuple[int, ...], E] = field(default_factory=dict)

    def add_scaled(self, other: Form, weight: E) -> None:
        for monomial, coefficient in other.terms.items():
            self.terms[monomial] = self.terms.get(monomial, ZERO) + weight * coefficient

    def evaluate(self, column: Callable[[int], E]) -> E:
        """Substitute a value for every column."""
        return sum((reduce(mul, map(column, monomial), c) for monomial, c in self.terms.items()), ZERO)


@dataclass(frozen=True)
class BusBlock:
    """One block of a bus side: 2^log_rows rows of one tuple shape.

    Always a block some table owns: it names that table's columns in ITS OWN
    local indices, which is what its bus form is written over, and stays symbolic
    until the table sumcheck. The three blocks no table owns are a `Framework`.
    """

    log_rows: int
    coordinates: tuple[Form, ...]
    owner: int


@dataclass(frozen=True)
class Framework:
    """The three bus blocks no table owns: the boundary state, then the memory and
    bytecode arrays. Their coordinates are a constant, the index column, one
    committed column, or the bytecode polynomial, so the verifier evaluates their
    fingerprints outright instead of carrying them symbolically."""

    log_memory: int
    bytecode: Sequence[K]

    @property
    def log_bytecode(self) -> int:
        return log2_strict(len(self.bytecode)) - BUS_BITS

    @property
    def log_rows(self) -> tuple[int, int, int]:
        return (0, self.log_memory, self.log_bytecode)

    @property
    def final_pc(self) -> E:
        """Pull's boundary state: the run ends at the bytecode's last cell."""
        return _gpow(2**self.log_bytecode - 1)


@dataclass(frozen=True)
class BusLayout:
    """Where a side's blocks sit in the stacked leaf cube, split by kind so no
    caller has to know that the framework blocks are stacked first."""

    depth: int
    framework: tuple[Placement, ...]
    tables: tuple[Placement, ...]


def bus_layout(framework_log_rows: Sequence[int], blocks: Sequence[BusBlock]) -> BusLayout:
    placements, depth = stack_offsets([*framework_log_rows, *(block.log_rows for block in blocks)])
    split = len(framework_log_rows)
    return BusLayout(depth, tuple(placements[:split]), tuple(placements[split:]))


def selector_weights(placements: Sequence[Placement], point: MultilinearPoint) -> list[E]:
    """Each block's eq weight: which slice of the stacked leaf cube it occupies."""
    return [selector_eq(p.selector, point[p.variables :]) for p in placements]


@dataclass(frozen=True)
class ColumnClaim:
    column: int
    point: MultilinearPoint
    value: E


BUS_BITS = 4


@dataclass(frozen=True)
class BusResult:
    claims: tuple[ColumnClaim, ...]
    point: MultilinearPoint  # the GKR point zeta, which the table sumcheck reuses
    forms: tuple[tuple[Form, ...], ...]  # forms[side][table]
    totals: tuple[E, E, E]  # what the tables owe each side, derived


def verify_bus_balance(layout: Layout, transcript: Transcript) -> BusResult:
    framework = layout.framework
    push_layout = bus_layout(framework.log_rows, layout.push)
    pull_layout = bus_layout(framework.log_rows, layout.pull)
    count_layout = bus_layout((), layout.count)
    require(push_layout.depth == pull_layout.depth, "push/pull bus depths differ")
    require(count_layout.depth <= push_layout.depth, "count bus is deeper than push bus")

    alphas = transcript.samples(BUS_BITS)
    weights = eq_kernel(alphas)
    beta = transcript.sample()
    product = verify_product_triple(push_layout.depth, transcript)
    push_root, pull_root, count_root = product.roots
    require(count_root != ZERO, "a bus read count is zero")

    # Every row of every table is a real row: the prover's fill blocks bring each
    # table's count up to a power of two, so the two sides balance outright with no
    # padding surplus to divide back out.
    require(push_root == pull_root, "bus is unbalanced")

    # The framework blocks' committed columns, in the order the two sides first
    # name them: the memory image on push, then each array's final count on pull.
    point = product.point
    memory_low = tuple(point[: framework.log_memory])
    bytecode_low = tuple(point[: framework.log_bytecode])
    memory = transcript.scalars(3)
    memory_final = transcript.scalar()
    bytecode_final = transcript.scalar()
    claims = [ColumnClaim(column, memory_low, memory[column]) for column in (MEM_0, MEM_1, MEM_2)]
    claims.append(ColumnClaim(MEM_FINAL_CNT, memory_low, memory_final))
    claims.append(ColumnClaim(BYTECODE_FINAL_CNT, bytecode_low, bytecode_final))

    def fingerprints(state: E, memory_count: E, bytecode_count: E) -> tuple[E, E, E]:
        """The three framework tuples, read off directly. A side differs only in
        these: push seeds each array at count one, pull finalizes it with the
        committed final count and ends at the last pc."""
        return (
            weights[0] * SEP_STATE + weights[1] * state + weights[2] * ONE,
            weights[0] * SEP_MEM
            + weights[1] * index_mle(memory_low)
            + weights[2] * memory_count
            + sum((weights[3 + limb] * memory[limb] for limb in range(3)), ZERO),
            # The public coordinates' weighted sum IS the stacked polynomial at
            # (zeta, alpha), the weights being eq(alpha, .): one evaluation, not nine.
            weights[0] * SEP_BYTECODE
            + weights[1] * index_mle(bytecode_low)
            + weights[2] * bytecode_count
            + multilinear_eval(framework.bytecode, (*bytecode_low, *alphas)),
        )

    forms = tuple(tuple(Form() for _ in TABLES) for _ in range(3))
    sides = (
        (layout.push, push_layout, fingerprints(ONE, ONE, ONE), weights, beta),
        (layout.pull, pull_layout, fingerprints(framework.final_pc, memory_final, bytecode_final), weights, beta),
        # The count channel owns no framework block and runs at alpha = beta = 0:
        # its leaf IS the read count.
        (layout.count, count_layout, (), eq_kernel((ZERO,) * BUS_BITS), ZERO),
    )
    totals = []
    for side, (blocks, side_layout, framework_fingerprints, side_weights, side_beta) in enumerate(sides):
        framework_selectors = selector_weights(side_layout.framework, point)
        table_selectors = selector_weights(side_layout.tables, point)
        known = sum(
            (selector * (side_beta + fingerprint) for selector, fingerprint in zip(framework_selectors, framework_fingerprints, strict=True)),
            ZERO,
        )
        # A table's blocks stay symbolic: they accumulate into the form its
        # sumcheck settles over its own columns.
        beta_form = _const(side_beta)
        for selector, block in zip(table_selectors, blocks, strict=True):
            form = forms[side][block.owner]
            form.add_scaled(beta_form, selector)
            for slot, coordinate in enumerate(block.coordinates):
                form.add_scaled(coordinate, selector * side_weights[slot])
        # Every occupied row holds beta + its fingerprint; the rest of the packed
        # leaf cube holds the product identity.
        occupied = sum(framework_selectors + table_selectors, ZERO)
        totals.append(product.values[side] + known + ONE + occupied)

    # The recursive verifier defers a claim on the public bytecode polynomial. Its
    # point comes from alpha alone (doc sec:e2e-bc), so nothing is observed here and
    # no selector challenge is drawn.
    return BusResult(tuple(claims), point, forms, (totals[0], totals[1], totals[2]))


# Table sumcheck -------------------------------------------------------------


@dataclass(frozen=True)
class Air:
    """One table at its announced height, with the bus forms it owes each side."""

    table: Table
    log_height: int
    forms: tuple[Form, ...]

    def evaluate(self, constraint_powers: Sequence[E], form_powers: Sequence[E], columns: Sequence[E]) -> E:
        """This table's share of the batch's summand: its constraints, then its bus forms."""
        terms = self.table.constraints(lambda name: columns[self.table.col(name)])
        constraints = dot(constraint_powers, terms)
        buses = dot(form_powers, [form.evaluate(lambda index: columns[index]) for form in self.forms])
        return constraints + buses


def powers(base: E, count: int) -> list[E]:
    """`[1, base, base^2, ...]`, `count` terms."""
    return list(islice(accumulate(repeat(base), mul, initial=ONE), count))


def verify_constraints(
    airs: Sequence[Air], constraint_powers: Sequence[E], form_powers: Sequence[E], equality_point: MultilinearPoint, target: E, transcript: Transcript
) -> list[ColumnClaim]:
    depth = max((air.log_height for air in airs), default=0)
    require(len(equality_point) >= depth, "AIR equality point is too short")

    # Back-loaded: the first round binds the top variable, so each table reads its
    # own low ones off the head of `point`.
    challenges, claim = sumcheck(transcript, target, 4, [None] * depth)
    point = list(reversed(challenges))
    weights = [ONE] * len(airs)
    for variable, challenge in enumerate(point):
        equality = ONE + equality_point[variable] + challenge
        for table_index, air in enumerate(airs):
            weights[table_index] *= equality if air.log_height > variable else challenge

    final = ZERO
    cursor = 0
    claims: list[ColumnClaim] = []
    for table_index, air in enumerate(airs):
        evaluations = tuple(transcript.scalars(air.table.width))
        table_constraint_powers = constraint_powers[cursor : cursor + air.table.n_constraints]
        cursor += air.table.n_constraints
        final += weights[table_index] * air.evaluate(table_constraint_powers, form_powers, evaluations)
        base, air_point = BASES[air.table.opcode], tuple(point[: air.log_height])
        claims.extend(ColumnClaim(base + local, air_point, value) for local, value in enumerate(evaluations))
    require(final == claim, "AIR terminal mismatch")
    return claims


# VM statement, layout, and AIR -----------------------------------------------

R1CS_DIGEST = bytes.fromhex("537ad20790308f8eb8c0e8bd3e6c58ee64573371e3d53c30613dd04d87c0b7ea")

# The columns no instruction table owns (doc sec:e2e-unrolled, Commitment): the
# memory image's three limbs, the two finalize counts, and flock's packed
# witness. They come first in the global column numbering, the tables after.
GLOBAL_COLUMNS = ("mem_0", "mem_1", "mem_2", "mem_final_cnt", "bytecode_final_cnt", "qflock")
MEM_0, MEM_1, MEM_2, MEM_FINAL_CNT, BYTECODE_FINAL_CNT, QFLOCK = range(len(GLOBAL_COLUMNS))

BLAKE2S_R1CS_LOG_SIZE = 14
K_BITS = 64
FLOCK_K_SKIP = log2_ceil(K_BITS)
LOG_PACKING = log2_ceil(K_BITS)  # bits per committed K-element (pcs::pack::LOG_PACKING)

FLOCK_NUM_LINCHECK_ROUNDS = BLAKE2S_R1CS_LOG_SIZE - FLOCK_K_SKIP
QFLOCK_SLOT_BITS = BLAKE2S_R1CS_LOG_SIZE - LOG_PACKING
BLAKE2S_CONSTANT_COLUMN = 512


@dataclass(frozen=True)
class Layout:
    framework: Framework
    push: tuple[BusBlock, ...]
    pull: tuple[BusBlock, ...]
    count: tuple[BusBlock, ...]
    placements: tuple[Placement, ...]
    stack_log: int
    table_logs: tuple[int, ...]


def _gpow(index: int) -> E:
    return GEN**index


def _const(value: E | int) -> Form:
    return Form({(): value if isinstance(value, E) else E(value)})


def _col(index: int, exponent: int = 0) -> Form:
    return Form({(index,): _gpow(exponent)})


def _prod(a: int, b: int, exponent: int = 0) -> Form:
    return Form({tuple(sorted((a, b))): _gpow(exponent)})


def _sum(forms: Iterable[Form]) -> Form:
    total = Form()
    for form in forms:
        total.add_scaled(form, ONE)
    return total


SEP_STATE = ONE
SEP_MEM = GEN
SEP_BYTECODE = GEN**2


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Form, ...]] = []
        self.pull: list[tuple[Form, ...]] = []

    def pair(self, push: Sequence[Form], pull: Sequence[Form]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state_derived(self, pc: int, fp: int, npc: Form, nfp: Form) -> None:
        self.pair((_const(SEP_STATE), npc, nfp), (_const(SEP_STATE), _col(pc), _col(fp)))

    def state_step(self, pc: int, fp: int) -> None:
        self.state_derived(pc, fp, _col(pc, 1), _col(fp))

    def _counted(self, prefix: Sequence[Form], count: int, suffix: Sequence[Form]) -> None:
        self.pair((*prefix, _col(count, 1), *suffix), (*prefix, _col(count), *suffix))

    def bytecode(self, pc: int, count: int, opcode: int, operands: Sequence[Form]) -> None:
        self._counted((_const(SEP_BYTECODE), _col(pc)), count, (_const(_gpow(opcode)), *operands))

    def memory(self, address: Form, count: int, values: Sequence[Form]) -> None:
        self._counted((_const(SEP_MEM), address), count, values)

    def memory_cols(self, address: Form, count: int, *columns: int) -> None:
        """A word whose lanes are committed columns, low lane first.

        Lanes past the ones named are literal zeros, which is what turns the
        flush into a range assertion on the value: bus balance can only hold if
        the cell really is that narrow.
        """
        lanes = [_col(column) for column in columns] + [_const(ZERO)] * (3 - len(columns))
        self.memory(address, count, lanes)


# The instruction tables (doc sec:tables) -------------------------------------
#
# One table per opcode. Each declares its columns by name, how it flushes the
# bus, and its AIR; everything else about it (its width, where its columns land
# in the global numbering, which of them hold read counts) is read off those
# names, so the views cannot drift apart. A column name prefixed ``cnt`` is a
# read count, and ``<x>_0.._2`` are the three K-lanes of one 192-bit word.


@dataclass(frozen=True)
class Table:
    """One instruction's table: its columns, its bus flushes, its AIR."""

    name: str
    opcode: int  # also its index in TABLES, so g^opcode is its bytecode tag
    columns: tuple[str, ...]
    flushes: Callable[[Table], Flushes]
    constraints: Callable[[Callable[[str], E]], tuple[E, ...]] = lambda _: ()

    @property
    def n_constraints(self) -> int:
        return len(self.constraints(lambda _: ZERO))

    @property
    def width(self) -> int:
        return len(self.columns)

    def col(self, name: str) -> int:
        assert name in self.columns, f"table {self.name} has no column {name!r}"
        return self.columns.index(name)

    def cols(self, *names: str) -> tuple[int, ...]:
        return tuple(self.col(name) for name in names)

    @property
    def count_columns(self) -> tuple[int, ...]:
        return tuple(i for i, name in enumerate(self.columns) if name.startswith("cnt"))


# Operand pairs contributing to each lane after reducing y^3 = y + 1 in E = K[y]/(y^3 + y + 1).
TOWER_LANES = (((0, 0), (1, 2), (2, 1)), ((0, 1), (1, 0), (1, 2), (2, 1), (2, 2)), ((0, 2), (1, 1), (2, 0), (2, 2)))


def _arith_result(multiply: bool, a: Sequence[int], b: Sequence[int]) -> tuple[Form, ...]:
    """The result word's three K-lanes as forms over the two operands' lanes.

    XOR is the lane-wise sum; MUL is the tower product, unrolled through TOWER_LANES.
    """
    if not multiply:
        return tuple(_sum((_col(a[i]), _col(b[i]))) for i in range(3))
    return tuple(_sum(_prod(a[j], b[k]) for j, k in lane) for lane in TOWER_LANES)


def _flushes_arith(table: Table) -> Flushes:
    pc, fp, o_a, o_b, o_c, cnt_a, cnt_b, cnt_c, cnt_bc = table.cols("pc", "fp", "o_a", "o_b", "o_c", "cnt_a", "cnt_b", "cnt_c", "cnt_bc")
    va, vb = table.cols("va_0", "va_1", "va_2"), table.cols("vb_0", "vb_1", "vb_2")
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, table.opcode, (_col(o_a), _col(o_b), _col(o_c), _const(ZERO), _const(ZERO)))
    flushes.memory_cols(_prod(fp, o_a), cnt_a, *va)
    flushes.memory_cols(_prod(fp, o_b), cnt_b, *vb)
    # The destination cell's flush carries the result itself, so bus balance is
    # the assertion and the result is no column.
    flushes.memory(_prod(fp, o_c), cnt_c, _arith_result(table.name == "mul", va, vb))
    return flushes


def _flushes_set(table: Table) -> Flushes:
    pc, fp, o, cnt, cnt_bc = table.cols("pc", "fp", "o", "cnt", "cnt_bc")
    k = table.cols("k_0", "k_1", "k_2")
    flushes = Flushes()
    flushes.state_step(pc, fp)
    # The immediate's three limbs ride the spare operand slots.
    flushes.bytecode(pc, cnt_bc, table.opcode, (_col(o), *(_col(limb) for limb in k), _const(ZERO)))
    flushes.memory_cols(_prod(fp, o), cnt, *k)
    return flushes


def _flushes_deref(table: Table) -> Flushes:
    pc, fp, alpha, beta, gamma, f_pc, f_fp, ptr = table.cols("pc", "fp", "alpha", "beta", "gamma", "f_pc", "f_fp", "ptr")
    cnt_ptr, cnt_target, cnt_local, cnt_bc = table.cols("cnt_ptr", "cnt_target", "cnt_local", "cnt_bc")
    v3 = table.cols("v3_0", "v3_1", "v3_2")

    def gated(lane: int) -> list[Form]:
        return [_col(lane), _prod(f_pc, lane), _prod(f_fp, lane)]

    # v2 = (1 + f_pc + f_fp)*v3 + f_pc*(g^2*pc) + f_fp*fp, lane-wise: only the low
    # lane takes the two K-valued sources.
    store = (_sum((*gated(v3[0]), _prod(f_pc, pc, 2), _prod(f_fp, fp))), _sum(gated(v3[1])), _sum(gated(v3[2])))
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, table.opcode, (_col(alpha), _col(beta), _col(gamma), _col(f_pc), _col(f_fp)))
    flushes.memory_cols(_prod(fp, alpha), cnt_ptr, ptr)
    flushes.memory(_prod(ptr, beta), cnt_target, store)
    flushes.memory_cols(_prod(fp, gamma), cnt_local, *v3)
    return flushes


def _flushes_jump(table: Table) -> Flushes:
    pc, fp, o_c, o_d, o_f, cond, dest, frame, b = table.cols("pc", "fp", "o_c", "o_d", "o_f", "c", "dest", "frame", "b")
    cnt_c, cnt_d, cnt_f, cnt_bc = table.cols("cnt_c", "cnt_d", "cnt_f", "cnt_bc")
    flushes = Flushes()
    # next_pc = b*dest + (b+1)*g*pc, next_fp = b*frame + (b+1)*fp, both derived.
    flushes.state_derived(pc, fp, _sum((_prod(b, dest), _prod(b, pc, 1), _col(pc, 1))), _sum((_prod(b, frame), _prod(b, fp), _col(fp))))
    flushes.bytecode(pc, cnt_bc, table.opcode, (_col(o_c), _col(o_d), _col(o_f), _const(ZERO), _const(ZERO)))
    # The condition, the destination and the frame are K-valued on every row, taken
    # or not, so each is one K-limb read through literal zeros in the upper lanes.
    flushes.memory_cols(_prod(fp, o_c), cnt_c, cond)
    flushes.memory_cols(_prod(fp, o_d), cnt_d, dest)
    flushes.memory_cols(_prod(fp, o_f), cnt_f, frame)
    return flushes


def _jump_constraints(get: Callable[[str], E]) -> tuple[E, ...]:
    """``b = c*w`` and ``c*(b+1) = 0``: the one quantity no interaction pins.

    No table binds an address, an arithmetic result, a DEREF store or a JUMP
    successor, the bus reading each as a degree-2 coordinate, so JUMP's
    is-nonzero indicator is the whole AIR of the machine. The condition is K-valued
    (its memory read carries literal zeros above the low limb), so both relations
    are single-lane.
    """
    condition, inverse, flag = get("c"), get("w"), get("b")
    return (flag + condition * inverse, condition * (flag + ONE))


def _flushes_blake2s(table: Table) -> Flushes:
    pc, fp, cnt_bc = table.cols("pc", "fp", "cnt_bc")
    operands = table.cols("o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "md_0", "md_1")
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, table.opcode, tuple(_col(i) for i in operands))
    # The eight cells a row accesses: the four independently addressed message
    # chunks, then the two consecutive chaining-value cells and the two output
    # ones. Each carries two limbs of q_flock and a zero top limb.
    for operand, exponent, cell in (
        ("o_0", 0, "m0"),
        ("o_1", 0, "m1"),
        ("o_2", 0, "m2"),
        ("o_3", 0, "m3"),
        ("o_v", 0, "cv0"),
        ("o_v", 1, "cv1"),
        ("o_out", 0, "out0"),
        ("o_out", 1, "out1"),
    ):
        lo, hi = table.cols(f"{cell}_lo", f"{cell}_hi")
        flushes.memory_cols(_prod(fp, table.col(operand), exponent), table.col(f"cnt_{cell}"), lo, hi)
    return flushes


# The column names of each table, in the order they are committed. Hand-laid in
# groups: the state, the operands, the values, then the read counts.
ARITH_COLUMNS = (
    "pc", "fp", "o_a", "o_b", "o_c",
    "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2",
    "cnt_a", "cnt_b", "cnt_c", "cnt_bc",
)  # fmt: skip

SET_COLUMNS = ("pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc")

DEREF_COLUMNS = (
    "pc", "fp", "alpha", "beta", "gamma", "f_pc", "f_fp", "ptr",
    "v3_0", "v3_1", "v3_2",
    "cnt_ptr", "cnt_target", "cnt_local", "cnt_bc",
)  # fmt: skip

JUMP_COLUMNS = (
    "pc", "fp", "o_c", "o_d", "o_f", "c", "dest", "frame",
    "cnt_c", "cnt_d", "cnt_f", "cnt_bc",
    "w", "b",  # witness columns: neither read from memory nor in the bytecode
)  # fmt: skip

BLAKE2S_COLUMNS = (
    "pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_v", "o_out",
    # The eighteen value limbs are committed inside q_flock, not here.
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi",
    "out0_lo", "out0_hi", "out1_lo", "out1_hi", "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "md_0", "md_1",
    "cnt_m0", "cnt_m1", "cnt_m2", "cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_bc",
)  # fmt: skip

TABLES = (
    Table("xor", 0, ARITH_COLUMNS, _flushes_arith),
    Table("mul", 1, ARITH_COLUMNS, _flushes_arith),
    Table("set", 2, SET_COLUMNS, _flushes_set),
    Table("deref", 3, DEREF_COLUMNS, _flushes_deref),
    Table("jump", 4, JUMP_COLUMNS, _flushes_jump, _jump_constraints),
    Table("blake2s", 5, BLAKE2S_COLUMNS, _flushes_blake2s),
)
BLAKE2S = TABLES[5]

# Where in the flock witness each embedded BLAKE2s limb lives (doc
# sec:tab-blake2s): one 64-bit slot per limb, the chaining value first, then the
# digest, the message block and the metadata. Slots 8 and 9 hold the
# compression's high output words, which no memory cell carries.
BLAKE2S_SLOTS = (
    "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "out0_lo", "out0_hi", "out1_lo", "out1_hi", None, None,
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi", "md_0", "md_1",
)  # fmt: skip
BLAKE2S_SLOT_BY_COLUMN = {BLAKE2S.col(name): slot for slot, name in enumerate(BLAKE2S_SLOTS) if name}

WIDTHS = tuple(t.width for t in TABLES)
# Global column numbering: the shared columns, then each table's block in turn.
BASES = tuple(len(GLOBAL_COLUMNS) + sum(WIDTHS[:table]) for table in range(len(TABLES)))


def build_layout(bytecode: Sequence[K], log_memory: int, table_log_heights: Sequence[int]) -> Layout:
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(
        16 <= log_memory <= 32
        and all(0 <= log_height <= 32 for log_height in table_log_heights)
        and table_log_heights[BLAKE2S.opcode] >= 3
        and 0 <= log_bytecode <= 32,
        "invalid announced table sizes",
    )
    table_log_heights = list(table_log_heights)

    framework = Framework(log_memory, bytecode)
    push: list[BusBlock] = []
    pull: list[BusBlock] = []
    count: list[BusBlock] = []
    for table, height in zip(TABLES, table_log_heights, strict=True):
        flushes = table.flushes(table)
        for coordinates in flushes.push:
            push.append(BusBlock(height, coordinates, table.opcode))
        for coordinates in flushes.pull:
            pull.append(BusBlock(height, coordinates, table.opcode))
        for local in table.count_columns:
            count.append(BusBlock(height, (_col(local),), table.opcode))

    # Every column's height, in global numbering; None marks the BLAKE2s value
    # columns, which are committed inside q_flock rather than on their own.
    kappas: list[int | None] = [0] * (len(GLOBAL_COLUMNS) + sum(WIDTHS))
    kappas[MEM_0] = kappas[MEM_1] = kappas[MEM_2] = kappas[MEM_FINAL_CNT] = log_memory
    kappas[BYTECODE_FINAL_CNT] = framework.log_bytecode
    kappas[QFLOCK] = table_log_heights[BLAKE2S.opcode] + QFLOCK_SLOT_BITS
    for table, (base, width) in enumerate(zip(BASES, WIDTHS, strict=True)):
        kappas[base : base + width] = [table_log_heights[table]] * width
    for local in BLAKE2S_SLOT_BY_COLUMN:
        kappas[BASES[BLAKE2S.opcode] + local] = None
    placements, total_log = stack_offsets(kappas)
    # Floor at the PCS minimum: WHIR's level ladder needs room, so a tiny
    # witness zero-pads up to it. Both sides derive this from the kappas.
    stack_log = max(MIN_STACKED_LOG, total_log)
    return Layout(framework, tuple(push), tuple(pull), tuple(count), tuple(placements), stack_log, tuple(table_log_heights))


def build_airs(layout: Layout, bus_forms: Sequence[Sequence[Form]]) -> list[Air]:
    return [Air(table, height, tuple(side[table.opcode] for side in bus_forms)) for table, height in zip(TABLES, layout.table_logs, strict=True)]


# WHIR opening ----------------------------------------------------------------

INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 3
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5
# Grinding: one width for every level's queries, none per fold.
QUERY_GRINDING_BITS = 17

MIN_STACKED_LOG = 15
MAX_STACKED_LOG = 28

WHIR_QUERIES = (((223,56,36), (223,56,37), (223,56,37), (224,56,37,28), (224,56,37,28), (224,56,38,28), (224,56,38,28,22), (225,56,38,28,23), (225,56,38,28,23), (225,56,38,28,23,19), (226,56,38,28,23,19), (226,56,38,28,23,19), (227,56,38,28,23,19,16), (228,56,38,28,23,19,16), (228,56,38,28,23,19,16), (229,57,38,28,23,19,17,14), (230,57,38,29,23,19,17,14), (232,57,38,29,23,19,17,15)), ((112,45,31), (112,45,32), (112,45,32), (112,45,32,25), (112,45,32,25), (112,45,32,25), (112,45,32,25,20), (112,45,32,25,21), (112,45,32,25,21), (113,45,32,25,21,17), (113,45,32,25,21,18), (113,45,32,25,21,18), (113,45,32,25,21,18,15), (113,45,32,25,21,18,15), (114,45,32,25,21,18,15), (114,45,33,25,21,18,15,14), (114,45,33,25,21,18,16,14), (115,46,33,25,21,18,16,14)), ((75,37,28), (75,37,28), (75,38,28), (75,38,28,22), (75,38,28,23), (75,38,28,23), (75,38,28,23,19), (75,38,28,23,19), (75,38,28,23,19), (75,38,28,23,19,16), (75,38,28,23,19,16), (75,38,28,23,19,16), (75,38,28,23,19,17,14), (76,38,29,23,19,17,14), (76,38,29,23,19,17,15), (76,38,29,23,19,17,15,13), (76,38,29,23,19,17,15,13), (77,38,29,23,19,17,15,13)), ((56,32,25), (56,32,25), (56,32,25), (56,32,25,20), (56,32,25,21), (56,32,25,21), (56,32,25,21,17), (56,32,25,21,18), (56,32,25,21,18), (57,32,25,21,18,15), (57,32,25,21,18,15), (57,32,25,21,18,15), (57,33,25,21,18,15,14), (57,33,25,21,18,16,14), (57,33,25,21,18,16,14), (57,33,26,21,18,16,14,12), (57,33,26,21,18,16,14,13), (58,33,26,21,18,16,14,13)))  # fmt: skip


@dataclass(frozen=True)
class WhirConfig:
    log_inv_rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]


def derive_config(log_n: int, log_inv_rate: int) -> WhirConfig:
    """The opening shape at this size and rate: the ladder geometry, then the
    tabulated query counts."""
    require(MIN_STACKED_LOG <= log_n <= MAX_STACKED_LOG and 1 <= log_inv_rate <= 4, "invalid WHIR shape")
    folds = [INITIAL_FOLDING_FACTOR]
    log_inv_rates = [log_inv_rate]
    remaining = log_n - INITIAL_FOLDING_FACTOR
    while remaining > RESIDUAL_MAX_LOG:
        first = len(folds) == 1
        log_inv_rates.append(log_inv_rates[-1] + folds[-1] - (RS_DOMAIN_INITIAL_REDUCTION_FACTOR if first else RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR))
        fold = min(SUBSEQUENT_FOLDING_FACTOR, remaining)
        remaining -= fold
        folds.append(fold)
    require(len(folds) >= 2, "WHIR requires at least two levels")
    queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG]
    require(len(queries) == len(folds), "tabulated query count does not match the ladder")
    return WhirConfig(log_inv_rates=tuple(log_inv_rates), folds=tuple(folds), queries=queries)


def _hash_pair(left: Digest, right: Digest) -> Digest:
    return blake2s_hash(left.value + right.value)


def _ext_row(words: Sequence[K]) -> tuple[E, ...]:
    """Regroup a level's leaf words into the E values they encode, three per lane."""
    return tuple(E(*words[i : i + 3]) for i in range(0, len(words), 3))


def sample_queries(transcript: Transcript, block_length: int, count: int) -> list[int]:
    depth = log2_strict(block_length)
    require(0 < depth <= 192, "invalid query domain")
    per_word = 192 // depth
    result: list[int] = []
    while len(result) < count:
        bits = int(transcript.sample())
        for chunk in range(min(per_word, count - len(result))):
            result.append((bits >> (chunk * depth)) & (block_length - 1))
    return result


def _enforced_sum(rows: Sequence[Sequence[K | E]], folds: Sequence[E], query_weights: Sequence[E]) -> E:
    lane_weights = eq_kernel(folds)
    total = ZERO
    for query_weight, row in zip(query_weights, rows, strict=True):
        total += query_weight * dot(row, lane_weights)
    return total


def _subspace_roots(log_n: int) -> list[E]:
    roots = [ONE]
    layer = [E(2**i) for i in range(1, log_n + 1)]
    for _ in range(log_n):
        layer = [value**2 + roots[-1] * value for value in layer]
        roots.append(layer.pop(0))
    return roots


def _induced_weight(message_log: int, queries: Sequence[int], query_weights: Sequence[E], point: Sequence[E]) -> E:
    """The level's batched query claims, as one weight at `point`.

    Each query contributes the novel-basis column weight of doc annex B, Lemma
    lem:colweight, `prod_k (1 + p_k (1 + W-hat_k(x_q)))`, scaled by its power of
    the level's batching challenge.
    """
    require(len(point) == message_log, "bad induced-basis dimensions")
    roots = _subspace_roots(message_log)
    inverses = [value.inv() if value else ZERO for value in roots]
    total = ZERO
    for weight, query in zip(query_weights, queries, strict=True):
        basis = E(query)
        product = weight
        for coordinate, challenge in enumerate(point):
            product *= ONE + challenge * (ONE + basis * inverses[coordinate])
            basis = basis**2 + roots[coordinate] * basis
        total += product
    return total


@dataclass(frozen=True)
class GluedClaim:
    """One claim folded into the running sumcheck, and the weight it owes back.

    A level's batched queries and an out-of-domain claim differ only in that
    weight: both are a power of the level's lambda times a function of the
    terminal point, restricted to the level's own message coordinates.
    """

    scalar: E  # the power of lambda it was glued with
    fold_start: int  # how many fold challenges preceded the level
    weight_at: Callable[[Sequence[E]], E]


def verify_whir(transcript: Transcript, log_n: int, log_inv_rate: int, target: E, root: Digest, evaluate_basis: Callable[[Sequence[E]], E]) -> None:
    """Verify the base-field multilevel opening with a one-point terminal check."""
    config = derive_config(log_n, log_inv_rate)
    levels = len(config.folds)

    running_target = target
    running_quad = transcript.round_poly(3, target)
    folds: list[E] = []
    glued: list[GluedClaim] = []
    current_root = root

    for level, (fold_count, level_rate) in enumerate(zip(config.folds, config.log_inv_rates, strict=True)):
        level_folds: list[E] = []
        for _ in range(fold_count):
            challenge = transcript.sample()
            folds.append(challenge)
            level_folds.append(challenge)
            running_target = poly_eval(running_quad, challenge)
            running_quad = transcript.round_poly(3, running_target)

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        # The level's claims, held until its batching challenge is drawn: the
        # OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        pending: list[tuple[E, Sequence[E], Callable[[Sequence[E]], E]]] = []
        if final_level:
            residual = tuple(transcript.scalars(2**message_log))
        else:
            next_root = Digest.from_halves(*transcript.scalars(2))
            ood_point = tuple(transcript.samples(message_log))
            ood_value = transcript.scalar()
            pending.append((ood_value, transcript.round_poly(3, ood_value), lambda x, z=ood_point: eq_eval(z, x)))

        transcript.grind_check(QUERY_GRINDING_BITS)
        block_length = 2 ** (message_log + level_rate)
        queries = sample_queries(transcript, block_length, config.queries[level])
        # One batching challenge per level, drawn once every claim it batches is
        # fixed: the OOD claims above and these query positions.
        lam = transcript.sample()
        query_weights = powers(lam, len(queries))
        # Level 0 committed the K witness, one leaf word per lane; every deeper
        # level a folded E one, three words per lane.
        lanes = 2**fold_count
        words = transcript.merkle(current_root, block_length, queries, lanes if level == 0 else 3 * lanes)
        rows: list[Sequence[K | E]] = [tuple(reversed(row)) for row in words] if level == 0 else [_ext_row(row) for row in words]
        enforced = _enforced_sum(rows, level_folds, query_weights)

        # Every commitment, including the last one, enters through an intro
        # message; the level's claims are then batched with powers of `lam`,
        # the running claim keeping lam^0 = 1.
        batch = (message_log, tuple(queries), tuple(query_weights))
        pending.append((enforced, transcript.round_poly(3, enforced), lambda x, b=batch: _induced_weight(*b, x)))
        scalar = ONE
        for value, intro, weight_at in pending:
            scalar *= lam
            running_quad = [q + scalar * i for q, i in zip(running_quad, intro, strict=True)]
            running_target += scalar * value
            glued.append(GluedClaim(scalar, len(folds), weight_at))

        if final_level:
            # Finish the remaining sumcheck rounds and close on one evaluation
            # of every basis at the resulting point.
            tail_folds: list[E] = []
            for round_index in range(message_log):
                challenge = transcript.sample()
                running_target = poly_eval(running_quad, challenge)
                tail_folds.append(challenge)
                if round_index + 1 < message_log:
                    running_quad = transcript.round_poly(3, running_target)
            # Each glued claim is rebound at the terminal point: the fold
            # challenges its level fixed after it was made, then the tail.
            point = list(folds) + tail_folds
            lane_folds = config.folds[0]
            weight = evaluate_basis(point[lane_folds:] + point[:lane_folds])
            for claim in glued:
                weight += claim.scalar * claim.weight_at(list(folds[claim.fold_start :]) + tail_folds)
            terminal = weight * multilinear_eval(residual, tail_folds)
            require(terminal == running_target, "WHIR terminal check failed")
            return
        current_root = next_root

    raise VerificationError("WHIR verification ended without a terminal level")


# Flock reduction -------------------------------------------------------------

PHI_BASIS = (E(0x0000000000000001), E(0x033CE8BEDDC8A656), E(0x512620375ED2A108), E(0x0C9E636090AAFC01), E(0xBA4F3CD82801769C), E(0xBA26E7904ADB4A47), E(0x467698598926DC01), E(0x4418AE808B28BDD0))  # fmt: skip
PHI = tuple(sum((PHI_BASIS[bit] for bit in range(8) if value >> bit & 1), ZERO) for value in range(256))

_MEDIUM_GENERATOR = E(0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0)

FIXED_CHALLENGES = (
    PHI[0xF7], PHI[0x53], PHI[0xB5],
    *tuple(_MEDIUM_GENERATOR ** (2**power) / (ONE + _MEDIUM_GENERATOR ** (2**power)) for power in range(4)),
)  # fmt: skip


@cache
def _window_denominator(count: int) -> E:
    """The one barycentric denominator `PHI[:count]` has: `prod_(k != 0) PHI[k]`, inverted.

    PHI is F2-linear in its index, so `PHI[i] + PHI[j] = PHI[i ^ j]`, and over a power-of-two prefix
    `j -> i ^ j` only permutes the block. Every node is left the same product.
    """
    return reduce(mul, PHI[1:count], ONE).inv()


def lagrange_weights(count: int, point: E) -> list[E]:
    """The barycentric weights of `PHI[:count]` at `point`, by prefix and suffix numerator products."""
    differences = [point + node for node in PHI[:count]]
    prefix = list(accumulate(differences, mul, initial=ONE))
    suffix = list(accumulate(reversed(differences), mul, initial=ONE))[::-1]
    denominator = _window_denominator(count)
    return [p * s * denominator for p, s in zip(prefix[:count], suffix[1:], strict=True)]


def lagrange_interpolate(count: int, values: Sequence[E], point: E) -> E:
    return dot(lagrange_weights(count, point), values)


@dataclass(frozen=True)
class ZerocheckResult:
    z_skip: E
    chi: MultilinearPoint
    v_a: E
    v_b: E
    v_c: E


def sumcheck(transcript: Transcript, claim: E, count: int, equalities: Sequence[E | None]) -> tuple[MultilinearPoint, E]:
    """One sumcheck round per entry of `equalities`, each the round's pulled-out eq factor or None: the challenges drawn, and the claim they leave."""
    point = []
    for equality in equalities:
        message = transcript.round_poly(count, claim, equality)
        challenge = transcript.sample()
        point.append(challenge)
        claim = poly_eval(message, challenge)
    return tuple(point), claim


def verify_flock_zerocheck(log_n: int, transcript: Transcript) -> ZerocheckResult:
    """The zerocheck: one univariate skip round, then nflock quadratic ones.
    C rides those rounds with AB, so all three claims come out at one point."""
    require(log_n >= FLOCK_K_SKIP + len(FIXED_CHALLENGES), "Flock zerocheck input is too small")
    # The point r: seven fixed coordinates, the rest sampled.
    r = (*FIXED_CHALLENGES, *transcript.samples(log_n - FLOCK_K_SKIP - len(FIXED_CHALLENGES)))

    # P = P^AB + P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    p_coset = transcript.scalars(K_BITS)
    z_skip = transcript.sample()
    v_p = lagrange_interpolate(2 * K_BITS, [ZERO] * K_BITS + list(p_coset), z_skip)

    # nflock quadratic rounds on P, closed by v_a, v_b.
    chi, running = sumcheck(transcript, v_p, 3, r)
    v_a, v_b = transcript.scalars(2)
    # v_c is what the terminal identity leaves, never transmitted: nothing is
    # checked here, lincheck pins all three claims against the committed witness.
    v_c = running + v_a * v_b
    return ZerocheckResult(z_skip, chi, v_a, v_b, v_c)


def verify_flock_lincheck(zc: ZerocheckResult, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """Lincheck at the quirky point (z_skip, chi): the claim's point, then its 64 slices s."""
    # alpha batches the two matrix identities, the c claim and the
    # constant-position check in its powers.
    alpha = transcript.sample()
    alpha_sq = alpha**2
    alpha_cu = alpha**3
    # e_row: phi8 Lagrange in the skip coordinate, eq in the slot variables.
    skip_weights = lagrange_weights(K_BITS, zc.z_skip)
    chi_in = zc.chi[:FLOCK_NUM_LINCHECK_ROUNDS]
    e_row = [weight * value for weight in eq_kernel(chi_in) for value in skip_weights]

    # The 8 rounds that bind the high column coordinates, leaving 64 unfolded.
    claim = zc.v_a + alpha * zc.v_b + alpha_sq * zc.v_c + alpha_cu
    round_challenges, r_lc = sumcheck(transcript, claim, 3, [None] * FLOCK_NUM_LINCHECK_ROUNDS)

    # The residual, then the terminal identity: pin term and c term included.
    # C = I, so the c weight is e_row itself, and both sides being tensors it
    # collapses to eq(chi_in, chi_in_prime) times a 64-term Lagrange combination.
    s = tuple(transcript.scalars(K_BITS))
    chi_in_prime = tuple(reversed(round_challenges))
    w_col = [value * weight for weight in eq_kernel(chi_in_prime) for value in s]
    terminal = (
        blake2s_bilinear(alpha, e_row, w_col)
        + alpha_sq * eq_eval(chi_in, chi_in_prime) * dot(skip_weights, s)
        + alpha_cu * w_col[BLAKE2S_CONSTANT_COLUMN]
    )
    require(terminal == r_lc, "Flock lincheck terminal mismatch")
    return chi_in_prime + zc.chi[FLOCK_NUM_LINCHECK_ROUNDS:], s


def blake2s_row_values(column_weights: Sequence[E]) -> tuple[list[E], list[E]]:
    """Compute `A0 w` and `B0 w` by one forward walk of the circuit."""
    size = 2**BLAKE2S_R1CS_LOG_SIZE
    require(len(column_weights) == size, "bad BLAKE2s column-weight vector")
    constant = BLAKE2S_CONSTANT_COLUMN
    message_base = 640
    counter_low = 1152
    counter_high = 1184
    final_flag = 1216
    last_node_flag = 1248
    gates_base = 1280
    gate_stride = 184
    left_values = [ZERO] * size
    right_values = [ZERO] * size

    def slots(base: int) -> tuple[E, ...]:
        return tuple(column_weights[base + bit] for bit in range(32))

    empty_word = (ZERO,) * 32

    def literal(value: int) -> tuple[E, ...]:
        return tuple(column_weights[constant] if value >> bit & 1 else ZERO for bit in range(32))

    def xor(x: Sequence[E], y: Sequence[E]) -> tuple[E, ...]:
        return tuple(a + b for a, b in zip(x, y, strict=True))

    def rotate_right(word: Sequence[E], amount: int) -> tuple[E, ...]:
        return tuple(word[(bit + amount) & 31] for bit in range(32))

    def add(x: Sequence[E], y: Sequence[E], carry_base: int) -> tuple[E, ...]:
        carry = ZERO
        output = []
        for bit in range(32):
            if bit < 31:
                left_values[carry_base + bit] = x[bit] + carry
                right_values[carry_base + bit] = y[bit] + carry
            output.append(x[bit] + y[bit] + carry)
            if bit < 31:
                carry += column_weights[carry_base + bit]
        return tuple(output)

    def add3(x: Sequence[E], y: Sequence[E], z: Sequence[E], base: int) -> tuple[E, ...]:
        """Fused three-operand add: 31 majority rows then 30 ripple rows.

        The majority of bit `i` is `maj_aux[i] + z[i]`, since over GF(2)
        `(x+z)(y+z) = xy + xz + yz + z`; then `x + y + z` is the ripple sum of
        `p = x^y^z` against `q[i] = maj[i-1]`, whose bit 0 is zero, so the
        ripple layer's bit 0 needs no row and slot `base + 31 + i - 1` carries
        bit `i`.
        """
        majority = []
        for bit in range(31):
            left_values[base + bit] = x[bit] + z[bit]
            right_values[base + bit] = y[bit] + z[bit]
            majority.append(column_weights[base + bit] + z[bit])
        ripple_base = base + 31
        carry = ZERO
        output = []
        for bit in range(32):
            q = ZERO if bit == 0 else majority[bit - 1]
            left = x[bit] + y[bit] + z[bit] + carry
            output.append(left + q)
            if 1 <= bit <= 30:
                left_values[ripple_base + bit - 1] = left
                right_values[ripple_base + bit - 1] = q + carry
                carry += column_weights[ripple_base + bit - 1]
        return tuple(output)

    def linear_rows(values: Sequence[E], base: int) -> None:
        for bit in range(32):
            left_values[base + bit] = values[bit]
            right_values[base + bit] = column_weights[constant]

    for base, length in ((0, 256), (message_base, 512), (counter_low, 128)):
        for row in range(base, base + length):
            left_values[row] = column_weights[row]
            right_values[row] = column_weights[constant]

    # v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
    state = [empty_word for _ in range(16)]
    for word in range(8):
        state[word] = slots(32 * word)
    for word in range(4):
        state[8 + word] = literal(BLAKE2S_IV[word])
    for word, base in enumerate((counter_low, counter_high, final_flag, last_node_flag)):
        state[12 + word] = xor(literal(BLAKE2S_IV[4 + word]), slots(base))

    for round_index in range(10):
        sigma = BLAKE2S_SIGMA[round_index]
        for gate_index, (lane_a, lane_b, lane_c, lane_d) in enumerate(BLAKE2S_G_LANES):
            gate = round_index * 8 + gate_index
            gate_base = gates_base + gate_stride * gate
            a, b, c, d = state[lane_a], state[lane_b], state[lane_c], state[lane_d]
            mx = slots(message_base + 32 * sigma[2 * gate_index])
            my = slots(message_base + 32 * sigma[2 * gate_index + 1])
            a1 = add3(a, b, mx, gate_base)
            d1 = rotate_right(xor(d, a1), 16)
            c1 = add(c, d1, gate_base + 61)
            b1 = rotate_right(xor(b, c1), 12)
            a2 = add3(a1, b1, my, gate_base + 92)
            d2 = rotate_right(xor(d1, a2), 8)
            c2 = add(c1, d2, gate_base + 153)
            b2 = rotate_right(xor(b1, c2), 7)
            # Every lane cascades: this encoding materializes no intermediate word.
            state[lane_a] = a2
            state[lane_b] = b2
            state[lane_c] = c2
            state[lane_d] = d2

    # out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for word in range(8):
        out = xor(xor(state[word], state[word + 8]), slots(32 * word))
        linear_rows(out, 256 + 32 * word)

    left_values[constant] = column_weights[constant]
    right_values[constant] = column_weights[constant]
    return left_values, right_values


def blake2s_bilinear(alpha: E, row_weights: Sequence[E], column_weights: Sequence[E]) -> E:
    """Compute `e_row^T (A0 + alpha B0) w_col` from the two forward row vectors."""
    size = 2**BLAKE2S_R1CS_LOG_SIZE
    require(len(row_weights) == size, "bad BLAKE2s row-weight vector")
    left_values, right_values = blake2s_row_values(column_weights)
    return dot(row_weights, left_values) + alpha * dot(row_weights, right_values)


def verify_flock(log_n: int, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """The reduction in protocol order: zerocheck, then lincheck. What it leaves is the
    point and the 64 claims s[i] = z(i, point), i < 64, for ring switching to bind."""
    zc = verify_flock_zerocheck(log_n, transcript)
    return verify_flock_lincheck(zc, transcript)


# Ring switching --------------------------------------------------------------

# The Frobenius shifts of the six stages composing Phi, one challenge each.
RING_MAP_SHIFTS = (32, 16, 8, 4, 2, 1)


def _phi(value: E, challenges: Sequence[E]) -> E:
    """The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`."""
    for challenge, shift in zip(challenges, RING_MAP_SHIFTS, strict=True):
        value += challenge * value ** (2**shift)
    return value


def _ring_weight(r: MultilinearPoint, r_prime: Sequence[E], coefficients: Sequence[E]) -> E:
    """The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
    `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`."""
    total = ZERO
    frobenius = list(r)
    for c in coefficients:
        product = c
        for value, challenge in zip(frobenius, r_prime, strict=True):
            product *= ONE + value + challenge
        total += product
        frobenius = [value**2 for value in frobenius]
    return total


def ring_switch(point: MultilinearPoint, s: Sequence[E], transcript: Transcript) -> tuple[E, Callable[[Sequence[E]], E]]:
    """The 64 claims s[i] = z(i, point) become the one dense claim `sum_u W(u) qflock(u) = target`.

    Draw Phi once they are fixed, then take the target `T = sum_i x^i Phi(s_i)` against the
    MLE-friendly weight `W(u) = Phi(eq(point, u))`. Returns the target and W as a closure."""
    challenges = transcript.samples(len(RING_MAP_SHIFTS))
    # The same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for k < 64.
    coefficients = [reduce(mul, (f ** (2 ** (k % s)) for f, s in zip(challenges, RING_MAP_SHIFTS, strict=True) if k & s), ONE) for k in range(K_BITS)]
    target = dot(powers(GEN, K_BITS), [_phi(value, challenges) for value in s])
    return target, lambda r_prime: _ring_weight(point, r_prime, coefficients)


# Stacked opening -------------------------------------------------------------


type StackClaim = tuple[E, Callable[[Sequence[E]], E]]
"""A claim on the committed stack: its value, and the weight it puts on the stack."""


def verify_stacked_opening(transcript: Transcript, root: Digest, stack_log: int, log_inv_rate: int, claims: Sequence[StackClaim]) -> None:
    """Discharge every claim on the committed stack in one opening.
    Batching is then powers of one challenge over both halves of every claim.
    """
    scales = powers(transcript.sample(), len(claims))
    target = dot(scales, [value for value, _ in claims])

    def evaluate_basis(point: Sequence[E]) -> E:
        """Every claim's weight at the opening's terminal point."""
        return sum((scale * weight(point) for scale, (_, weight) in zip(scales, claims, strict=True)), ZERO)

    verify_whir(transcript, stack_log, log_inv_rate, target, root, evaluate_basis)


def verify_execution(bytecode: Sequence[K], public_input: Digest, proof: Proof) -> None:
    pi = public_input.halves()
    # The public statement, bound before any challenge (`lean_vm::cpu::fs_seed`).
    # The seed hashes the bytecode multilinear itself, not a structured program,
    # so a verifier holding only the polynomial can reproduce it.
    bytecode_hash = blake2s_hash(b"".join(word.to_bytes() for word in bytecode))
    seed = blake2s_hash(b"leanvm-b-fs-seed-v2-blake2s" + R1CS_DIGEST + bytecode_hash.value)
    transcript = Transcript(proof, b"leanvm-b", (*seed.halves(), *pi))

    # 1] memory log-size, table log-size, and log-inv-rate in WHIR
    announced = transcript.scalars(2 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced size has a nonzero high limb")
    log_memory = int(announced[0].c0)
    table_logs = tuple(int(value.c0) for value in announced[1 : 1 + len(TABLES)])
    log_inverse_rate = int(announced[-1].c0)
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    layout = build_layout(bytecode, log_memory, table_logs)
    # The announced sizes bound themselves, but what the PCS has to be configured
    # for is the stacked size they IMPLY, and the instance caps admit a `stack_log`
    # far past the largest the WHIR ladder is feasible for. Checked here, before any
    # reduction runs against the layout, and against the same window the Rust
    # verifier's `pcs::{MIN_MU, MAX_MU}` and the recursion guest declare.
    require(MIN_STACKED_LOG <= layout.stack_log <= MAX_STACKED_LOG, "committed size outside the PCS window")

    # 2] WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    root = Digest.from_halves(*transcript.scalars(2))

    # 3] Bus: one batched GKR over the push, pull and count trees, then the leaf
    # decomposition, which leaves each table a degree-2 form and a total.
    bus = verify_bus_balance(layout, transcript)

    # 4] Rows: one back-loaded table sumcheck over all six tables, at
    # the bus point, starting from the target the three leaf claims derive.
    # Every table takes a disjoint range of xi powers for its constraints; the
    # three bus sides share the three above them (doc sec:air).
    xi = transcript.sample()
    n_constraints = sum(table.n_constraints for table in TABLES)
    xi_powers = powers(xi, n_constraints + 3)
    constraint_powers, form_powers = xi_powers[:n_constraints], xi_powers[n_constraints:]
    target = dot(form_powers, bus.totals)
    air_claims = verify_constraints(build_airs(layout, bus.forms), constraint_powers, form_powers, bus.point, target, transcript)
    claims = [*bus.claims, *air_claims]

    # 5] Public input: the first two memory cells, as one claim per limb on the
    # line through them. The prover sends one evaluation per limb; the three must
    # reassemble the line's value at the challenge (doc sec:e2e-pi).
    public_challenge = transcript.sample()
    public_limbs = transcript.scalars(3)
    public_point = [ZERO] * layout.placements[MEM_0].variables
    public_point[0] = public_challenge
    public_value = multilinear_eval(pi, [public_challenge])
    require(public_limbs[0] + Y * public_limbs[1] + Y**2 * public_limbs[2] == public_value, "public input limbs are off the line")
    claims.extend(ColumnClaim(column, tuple(public_point), value) for column, value in zip((MEM_0, MEM_1, MEM_2), public_limbs, strict=True))

    # 6] Locate every claim in the stack: a column claim keeps its point and
    # gains its placement's selector bits; a BLAKE2s value claim is re-routed to
    # the equal q_flock slot evaluation.
    stack_claims: list[StackClaim] = []
    qflock = layout.placements[QFLOCK]
    for claim in claims:
        # A BLAKE2s value column is committed inside q_flock rather than on its
        # own, so its claim is re-routed to the equal evaluation of q_flock's
        # slot: the same point, under a different placement, behind the slot bits.
        slot = BLAKE2S_SLOT_BY_COLUMN.get(claim.column - BASES[BLAKE2S.opcode])
        placement = qflock if slot is not None else layout.placements[claim.column]
        prefix = _selector_point(slot, QFLOCK_SLOT_BITS) if slot is not None else ()
        require(not placement.virtual, "claim targets an uncommitted column")
        require(len(prefix) + len(claim.point) == placement.variables, "column claim dimension mismatch")
        tail = _selector_point(placement.selector, layout.stack_log - placement.variables)
        point = prefix + claim.point + tail
        stack_claims.append((claim.value, lambda x, p=point: eq_eval(p, x)))

    # 7] BLAKE2s validity, its 64 claims ring-switched, then the one opening that
    # discharges every claim.
    flock_point, flock_s = verify_flock(BLAKE2S_R1CS_LOG_SIZE + layout.table_logs[BLAKE2S.opcode], transcript)
    ringswitch_target, ringswitch_weight = ring_switch(flock_point, flock_s, transcript)
    # That claim is supported on q_flock's region of the stack, so its weight carries the
    # placement's selector, and it leads the batch, taking the first power.
    ringswitch = (ringswitch_target, lambda x: selector_eq(qflock.selector, x[qflock.variables :]) * ringswitch_weight(x[: qflock.variables]))
    verify_stacked_opening(transcript, root, layout.stack_log, log_inverse_rate, [ringswitch, *stack_claims])
    transcript.finish()


def main(argv: Sequence[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Verify a leanVM-b execution proof")
    parser.add_argument("bytecode", type=Path, help="stacked bytecode multilinear, little-endian 64-bit words")
    parser.add_argument("public_input", type=Path, help="256-bit public input")
    parser.add_argument("stream", type=Path, help="the proof's scalar stream, 24-byte little-endian field elements")
    parser.add_argument("merkle_openings", type=Path, help="every Merkle opening: its leaf's words, then its sibling digests")
    arguments = parser.parse_args(argv)
    try:
        encoded_bytecode = arguments.bytecode.read_bytes()
        require(len(encoded_bytecode) % 8 == 0, "bytecode is not a whole number of 64-bit words")
        bytecode = [K(int.from_bytes(encoded_bytecode[i : i + 8], "little")) for i in range(0, len(encoded_bytecode), 8)]
        proof = Proof.load(arguments.stream, arguments.merkle_openings)
        verify_execution(bytecode, Digest(arguments.public_input.read_bytes()), proof)
    except (OSError, ValueError, KeyError, VerificationError) as exc:
        parser.exit(1, f"verification failed: {exc}\n")
    print("verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
