from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache, reduce
from pathlib import Path
from operator import mul
from struct import pack, unpack


class VerificationError(Exception):
    """Invalid proof."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


# Field arithmetic and BLAKE2s ------------------------------------------------


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
        # Deferring lets `K + E` and `K * E` fall through to E's reflected
        # operator, which lifts the K side into the extension.
        return NotImplemented if rhs is None else K(self.value ^ rhs.value)

    __radd__ = __add__

    def __mul__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(_base_mul(self.value, rhs.value))

    __rmul__ = __mul__

    def __repr__(self) -> str:
        return f"K(0x{self.value:016x})"


def _as_k(value: object) -> K | None:
    """`value` as a K element, or None if it is not one (see `K.__add__`)."""
    if isinstance(value, K):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= 2**64 - 1:
        return K(value)
    return None


@dataclass(frozen=True, slots=True, init=False)
class E:
    """K[y]/(y^3 + y + 1): the challenge field, a degree-3 extension of K.

    The three limbs are K elements, so the tower product below is written in K
    arithmetic rather than in raw 64-bit words. Limbs may be given as plain
    integers, which are lifted.
    """

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


# BLAKE2s -------------------------------------------------------------------

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
    """`Σ_i left[i] · right[i]` in E. Either side may be K-valued; lifting the
    left one is what `K * E`'s reflected operator would do anyway."""
    result = ZERO
    for x, y in zip(left, right, strict=True):
        result += E.lift(x) * y
    return result


def _selector_point(selector: int, length: int) -> tuple[E, ...]:
    return tuple(E(selector >> bit & 1) for bit in range(length))


def selector_eq(selector: int, point: Sequence[E]) -> E:
    return eq_eval(_selector_point(selector, len(point)), point)


def index_mle(point: Sequence[E]) -> E:
    """MLE of ``[1, g, g^2, ...]`` at an LSB-first point."""
    result = ONE
    generator_power = GEN
    for challenge in point:
        result *= ONE + challenge * (ONE + generator_power)
        generator_power *= generator_power
    return result


def poly_eval(coefficients: Sequence[E], point: E) -> E:
    """A polynomial at `point`, by Horner over its coefficients, constant first."""
    return reduce(lambda acc, c: acc * point + c, reversed(coefficients), ZERO)


@cache
def _denominators(nodes: tuple[E, ...]) -> tuple[E, ...]:
    result = []
    for index, node in enumerate(nodes):
        denominator = ONE
        for other_index, other in enumerate(nodes):
            if other_index != index:
                denominator *= node + other
        result.append(denominator.inv())
    return tuple(result)


def lagrange_weights(nodes: Sequence[E], point: E) -> list[E]:
    fixed_nodes = tuple(nodes)
    differences = [point + node for node in fixed_nodes]
    prefix = [ONE]
    for difference in differences:
        prefix.append(prefix[-1] * difference)
    suffix = ONE
    result = [ZERO] * len(fixed_nodes)
    inverses = _denominators(fixed_nodes)
    for index in range(len(fixed_nodes) - 1, -1, -1):
        result[index] = prefix[index] * suffix * inverses[index]
        suffix *= differences[index]
    return result


def lagrange_interpolate(nodes: Sequence[E], values: Sequence[E], point: E) -> E:
    return dot(lagrange_weights(nodes, point), values)


# Proof transport ------------------------------------------------------------


class BinaryReader:
    """Strict reader for bincode's fixed-width encoding used by the project."""

    def __init__(self, data: bytes) -> None:
        self.data = data
        self.offset = 0

    def take(self, length: int) -> bytes:
        end = self.offset + length
        require(end <= len(self.data), "truncated proof encoding")
        result = self.data[self.offset : end]
        self.offset = end
        return result

    def u64(self) -> int:
        return int.from_bytes(self.take(8), "little")

    def field(self) -> E:
        return E.from_bytes(self.take(24))

    def count(self, item_size: int, what: str) -> range:
        """The length prefix of a vector of `item_size`-byte items."""
        length = self.u64()
        require(length <= self.remaining // item_size, f"invalid {what} length")
        return range(length)

    def fields(self) -> tuple[E, ...]:
        return tuple(self.field() for _ in self.count(24, "field vector"))

    def base_fields(self) -> tuple[K, ...]:
        return tuple(K(self.u64()) for _ in self.count(8, "base-field vector"))

    def hashes(self) -> tuple[Digest, ...]:
        return tuple(Digest(self.take(32)) for _ in self.count(32, "hash vector"))

    @property
    def remaining(self) -> int:
        return len(self.data) - self.offset

    def finish(self) -> None:
        require(self.remaining == 0, "trailing proof encoding")


@dataclass(frozen=True)
class RawMerklePath:
    """One query's opening: its leaf words and the full sibling path to the root.

    A leaf is its raw K words, which is what the committer hashed, so an E-valued
    row of width `w` arrives as `3w` of them and is regrouped by the reader.
    Unpruned: two queries of the same phase repeat whatever siblings they share,
    which is what makes checking one a walk up one path.
    """

    leaf_data: tuple[K, ...]
    path: tuple[Digest, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> RawMerklePath:
        return cls(reader.base_fields(), reader.hashes())

    def root(self, leaf_index: int) -> Digest:
        """The root this opening claims, recomputed from its leaf and path."""
        node = _row_hash(self.leaf_data)
        for sibling in self.path:
            node = _hash_pair(node, sibling) if leaf_index & 1 == 0 else _hash_pair(sibling, node)
            leaf_index >>= 1
        return node


@dataclass(frozen=True)
class Proof:
    stream: tuple[E, ...]
    merkle: tuple[RawMerklePath, ...]

    @classmethod
    def from_bincode(cls, data: bytes) -> Proof:
        reader = BinaryReader(data)
        stream = reader.fields()
        merkle = tuple(RawMerklePath.read(reader) for _ in reader.count(16, "opening"))
        reader.finish()
        return cls(stream, merkle)

    @classmethod
    def load(cls, path: str | Path) -> Proof:
        return cls.from_bincode(Path(path).read_bytes())


# Fiat--Shamir ---------------------------------------------------------------


DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQUEEZE = 4
DS_POW = 5


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
        self.absorb_bytes(b"leanvm-b/transcript/v3-blake2s")
        self.absorb_bytes(label)
        for value in statement:
            self.observe(value)

    def observe(self, value: E) -> None:
        self.state = compress(self.state, (value.c0, value.c1, value.c2, DS_SCALAR))

    def absorb_bytes(self, data: bytes) -> None:
        self.state = compress(self.state, (len(data), 0, DS_LEN, 0))
        for offset in range(0, len(data), 16):
            block = data[offset : offset + 16].ljust(16, b"\0")
            self.state = compress(
                self.state,
                (int.from_bytes(block[:8], "little"), int.from_bytes(block[8:], "little"), DS_BYTE, 0),
            )

    def sample(self) -> E:
        self.state = compress(self.state, (0, 0, DS_SQUEEZE, 0))
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
        block = (nonce.c0, nonce.c1, nonce.c2, DS_POW)
        digest = compress(compress(self.state, (0, 0, DS_POW, 0)), block)[0]
        valid = nonce == ZERO if bits == 0 else digest & (2**bits - 1) == 0
        self.state = compress(self.state, block)
        require(valid, "invalid grinding nonce")

    def merkle(self, root: Digest, block_length: int, queries: Sequence[int], leaf_words: int) -> list[tuple[K, ...]]:
        """Pull one opening per query and authenticate each against `root`.

        Not absorbed: an opening's binding is the Merkle structure itself, which
        is checked here rather than by the sponge. Returns the rows in query
        order, so a repeated position simply re-opens the same authenticated row.
        """
        height = log2_strict(block_length)
        rows = []
        for query in queries:
            require(self.opening_offset < len(self.proof.merkle), "Merkle opening missing")
            opening = self.proof.merkle[self.opening_offset]
            self.opening_offset += 1
            require(0 <= query < block_length, "Merkle query is out of range")
            require(len(opening.leaf_data) == leaf_words, "opened row has the wrong width")
            require(len(opening.path) == height, "Merkle path has the wrong length")
            require(opening.root(query) == root, "Merkle root mismatch")
            rows.append(opening.leaf_data)
        return rows

    def round_poly(self, count: int, claim: E, equality: E | None = None) -> list[E]:
        """Read one sumcheck round polynomial, in coefficients.

        The message is every coefficient but one; the split identity fixes the
        remaining one to `claim`, so it is neither sent nor bound, and deriving it
        is an addition either way. A plain round has `h(0) + h(1) = c1 + ... + cd`,
        which fixes `c1`; a round whose eq factor `r` the protocol pulled out has
        `c0 + r·(c1 + ... + cd)`, which fixes `c0`.
        """
        fixed = 1 if equality is None else 0
        coefficients = [ZERO if index == fixed else self.scalar() for index in range(count)]
        if equality is None:
            coefficients[fixed] = claim + sum(coefficients[2:], ZERO)
        else:
            coefficients[fixed] = claim + equality * sum(coefficients[1:], ZERO)
        return coefficients

    def finish(self) -> None:
        require(self.stream_offset == len(self.proof.stream), "proof stream not fully consumed")
        require(self.opening_offset == len(self.proof.merkle), "Merkle openings not fully consumed")


# GKR product triple ---------------------------------------------------------


@dataclass(frozen=True)
class ProductTriple:
    roots: tuple[E, E, E]
    point: tuple[E, ...]
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


def selector_weights(placements: Sequence[Placement], point: Sequence[E]) -> list[E]:
    """Each block's eq weight: which slice of the stacked leaf cube it occupies."""
    return [selector_eq(p.selector, point[p.variables :]) for p in placements]


@dataclass(frozen=True)
class ColumnClaim:
    column: int
    point: tuple[E, ...]
    value: E


BUS_BITS = 4


@dataclass(frozen=True)
class BusResult:
    claims: tuple[ColumnClaim, ...]
    point: tuple[E, ...]  # the GKR point zeta, which the table sumcheck reuses
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
    gamma = transcript.sample()
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
        (layout.push, push_layout, fingerprints(ONE, ONE, ONE), weights, gamma),
        (layout.pull, pull_layout, fingerprints(framework.final_pc, memory_final, bytecode_final), weights, gamma),
        # The count channel owns no framework block and runs at alpha = gamma = 0:
        # its leaf IS the read count.
        (layout.count, count_layout, (), eq_kernel((ZERO,) * BUS_BITS), ZERO),
    )
    totals = []
    for side, (blocks, side_layout, framework_fingerprints, side_weights, side_gamma) in enumerate(sides):
        framework_selectors = selector_weights(side_layout.framework, point)
        table_selectors = selector_weights(side_layout.tables, point)
        known = sum(
            (selector * (side_gamma + fingerprint) for selector, fingerprint in zip(framework_selectors, framework_fingerprints, strict=True)),
            ZERO,
        )
        # A table's blocks stay symbolic: they accumulate into the form its
        # sumcheck settles over its own columns.
        gamma_form = _const(side_gamma)
        for selector, block in zip(table_selectors, blocks, strict=True):
            form = forms[side][block.owner]
            form.add_scaled(gamma_form, selector)
            for slot, coordinate in enumerate(block.coordinates):
                form.add_scaled(coordinate, selector * side_weights[slot])
        # Every occupied row holds gamma + its fingerprint; the rest of the packed
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
    result, current = [], ONE
    for _ in range(count):
        result.append(current)
        current *= base
    return result


def verify_constraints(
    airs: Sequence[Air],
    constraint_powers: Sequence[E],
    form_powers: Sequence[E],
    equality_point: Sequence[E],
    target: E,
    transcript: Transcript,
) -> list[ColumnClaim]:
    depth = max((air.log_height for air in airs), default=0)
    require(len(equality_point) >= depth, "AIR equality point is too short")

    claim = target
    weights = [ONE] * len(airs)
    point = [ZERO] * depth
    for round_index in range(depth):
        variable = depth - 1 - round_index
        message = transcript.round_poly(4, claim)
        challenge = transcript.sample()
        point[variable] = challenge
        equality = ONE + equality_point[variable] + challenge
        claim = poly_eval(message, challenge)
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

R1CS_DIGEST = bytes.fromhex("ec91e9d8d9ca4e306205907a0d236e53a6cdbda0382ef6c433ef9363edfe042e")

# The columns no instruction table owns (doc sec:e2e-unrolled, Commitment): the
# memory image's three limbs, the two finalize counts, and flock's packed
# witness. They come first in the global column numbering, the tables after.
GLOBAL_COLUMNS = ("mem_0", "mem_1", "mem_2", "mem_final_cnt", "bytecode_final_cnt", "qflock")
MEM_0, MEM_1, MEM_2, MEM_FINAL_CNT, BYTECODE_FINAL_CNT, QFLOCK = range(len(GLOBAL_COLUMNS))

BLAKE2S_R1CS_LOG_SIZE = 14
K_BITS = 64
FLOCK_K_SKIP = log2_ceil(K_BITS)
QFLOCK_SLOT_BITS = BLAKE2S_R1CS_LOG_SIZE - FLOCK_K_SKIP
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


def _col(index: int) -> Form:
    return Form({(index,): ONE})


def _gcol(index: int) -> Form:
    return Form({(index,): GEN})


def _sum(forms: Iterable[Form]) -> Form:
    total = Form()
    for form in forms:
        total.add_scaled(form, ONE)
    return total


def _prod(a: int, b: int, exponent: int = 0) -> Form:
    return Form({tuple(sorted((a, b))): _gpow(exponent)})


SEP_STATE = ONE
SEP_MEM = GEN
SEP_BYTECODE = GEN * GEN


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Form, ...]] = []
        self.pull: list[tuple[Form, ...]] = []

    def pair(self, push: Sequence[Form], pull: Sequence[Form]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state_step(self, pc: int, fp: int) -> None:
        self.pair((_const(SEP_STATE), _gcol(pc), _col(fp)), (_const(SEP_STATE), _col(pc), _col(fp)))

    def state_derived(self, pc: int, fp: int, npc: Form, nfp: Form) -> None:
        self.pair((_const(SEP_STATE), npc, nfp), (_const(SEP_STATE), _col(pc), _col(fp)))

    def bytecode(self, pc: int, count: int, opcode: int, operands: Sequence[Form]) -> None:
        prefix_push = (_const(SEP_BYTECODE), _col(pc), _gcol(count), _const(_gpow(opcode)))
        prefix_pull = (_const(SEP_BYTECODE), _col(pc), _col(count), _const(_gpow(opcode)))
        self.pair((*prefix_push, *operands), (*prefix_pull, *operands))

    def memory(self, address: Form, count: int, values: Sequence[Form]) -> None:
        self.pair(
            (_const(SEP_MEM), address, _gcol(count), *values),
            (_const(SEP_MEM), address, _col(count), *values),
        )

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
TOWER_LANES = (
    ((0, 0), (1, 2), (2, 1)),
    ((0, 1), (1, 0), (1, 2), (2, 1), (2, 2)),
    ((0, 2), (1, 1), (2, 0), (2, 2)),
)


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
    store = (
        _sum((*gated(v3[0]), _prod(f_pc, pc, 2), _prod(f_fp, fp))),
        _sum(gated(v3[1])),
        _sum(gated(v3[2])),
    )
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
    flushes.state_derived(
        pc,
        fp,
        _sum((_prod(b, dest), _prod(b, pc, 1), _gcol(pc))),
        _sum((_prod(b, frame), _prod(b, fp), _col(fp))),
    )
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


def _flushes_pack(table: Table) -> Flushes:
    pc, fp, o_a, o_b, o_c, v_a, v_b, cnt_a, cnt_b, cnt_c, cnt_bc = table.cols(
        "pc", "fp", "o_a", "o_b", "o_c", "v_a", "v_b", "cnt_a", "cnt_b", "cnt_c", "cnt_bc"
    )
    flushes = Flushes()
    flushes.state_step(pc, fp)
    flushes.bytecode(pc, cnt_bc, table.opcode, (_col(o_a), _col(o_b), _col(o_c), _const(ZERO), _const(ZERO)))
    # The literal zeros make the two source range assertions and the destination
    # packing exact through bus balance.
    flushes.memory_cols(_prod(fp, o_a), cnt_a, v_a)
    flushes.memory_cols(_prod(fp, o_b), cnt_b, v_b)
    flushes.memory_cols(_prod(fp, o_c), cnt_c, v_a, v_b)
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

PACK_COLUMNS = ("pc", "fp", "o_a", "o_b", "o_c", "v_a", "v_b", "cnt_a", "cnt_b", "cnt_c", "cnt_bc")

TABLES = (
    Table("xor", 0, ARITH_COLUMNS, _flushes_arith),
    Table("mul", 1, ARITH_COLUMNS, _flushes_arith),
    Table("set", 2, SET_COLUMNS, _flushes_set),
    Table("deref", 3, DEREF_COLUMNS, _flushes_deref),
    Table("jump", 4, JUMP_COLUMNS, _flushes_jump, _jump_constraints),
    Table("blake2s", 5, BLAKE2S_COLUMNS, _flushes_blake2s),
    Table("pack64x2", 6, PACK_COLUMNS, _flushes_pack),
)
BLAKE2S = TABLES[5]

# Where in the flock witness each embedded BLAKE2s limb lives (doc
# sec:tab-blake2s): one 64-bit slot per limb, the chaining value first, then the
# digest, the message block and the metadata. Slots 8 and 9 hold the
# compression's high output words, which no memory cell carries.
BLAKE2S_SLOT_BY_COLUMN = {
    BLAKE2S.col(name): slot
    for name, slot in {
        "cv0_lo": 0,
        "cv0_hi": 1,
        "cv1_lo": 2,
        "cv1_hi": 3,
        "out0_lo": 4,
        "out0_hi": 5,
        "out1_lo": 6,
        "out1_hi": 7,
        "m0_lo": 10,
        "m0_hi": 11,
        "m1_lo": 12,
        "m1_hi": 13,
        "m2_lo": 14,
        "m2_hi": 15,
        "m3_lo": 16,
        "m3_hi": 17,
        "md_0": 18,
        "md_1": 19,
    }.items()
}

WIDTHS = tuple(t.width for t in TABLES)
# Global column numbering: the shared columns, then each table's block in turn.
BASES = tuple(len(GLOBAL_COLUMNS) + sum(WIDTHS[:table]) for table in range(len(TABLES)))


def build_layout(bytecode: Sequence[K], log_memory: int, table_log_heights: Sequence[int]) -> Layout:
    require(
        16 <= log_memory <= 32 and all(0 <= log_height <= 32 for log_height in table_log_heights) and table_log_heights[BLAKE2S.opcode] >= 3,
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


def virtual_slot(column: int) -> int | None:
    """The q_flock slot a BLAKE2s value column rides in, or None if committed."""
    return BLAKE2S_SLOT_BY_COLUMN.get(column - BASES[BLAKE2S.opcode])


# WHIR opening ----------------------------------------------------------------

INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 3
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5
# Grinding: one width for every level's queries, none per fold.
QUERY_GRINDING_BITS = 17

MIN_STACKED_LOG = 15
MAX_STACKED_LOG = 32

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
    return WhirConfig(
        log_inv_rates=tuple(log_inv_rates),
        folds=tuple(folds),
        queries=queries,
    )


def _hash_pair(left: Digest, right: Digest) -> Digest:
    return blake2s_hash(left.value + right.value)


def _row_hash(row: Sequence[K]) -> Digest:
    """The committer's leaf preimage: the row's words in their 8-byte transport image."""
    return blake2s_hash(b"".join(word.to_bytes() for word in row))


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


def _enforced_sum(
    rows: Sequence[Sequence[K | E]],
    folds: Sequence[E],
    query_weights: Sequence[E],
) -> E:
    lane_weights = eq_kernel(folds)
    total = ZERO
    for query_weight, row in zip(query_weights, rows, strict=True):
        total += query_weight * dot(row, lane_weights)
    return total


def _subspace_roots(log_n: int) -> list[E]:
    roots = [ZERO] * (log_n + 1)
    roots[0] = ONE
    layer = [E(2**i) for i in range(1, log_n + 1)]
    for level in range(log_n):
        for index in range(log_n - level):
            value = layer[index] * layer[index] + roots[level] * layer[index]
            if index == 0:
                roots[level + 1] = value
            else:
                layer[index - 1] = value
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
            basis = basis * basis + roots[coordinate] * basis
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


def verify_whir(
    transcript: Transcript,
    log_n: int,
    log_inv_rate: int,
    target: E,
    root: Digest,
    evaluate_basis: Callable[[Sequence[E]], E],
) -> None:
    """Verify the base-field multilevel opening with a one-point terminal check."""
    config = derive_config(log_n, log_inv_rate)
    levels = len(config.folds)

    transcript.observe(target)
    for half in root.halves():
        transcript.observe(half)
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
        try:
            words = transcript.merkle(current_root, block_length, queries, lanes if level == 0 else 3 * lanes)
        except VerificationError as exc:
            raise VerificationError(f"WHIR level {level}: {exc}") from exc
        rows: list[Sequence[K | E]] = list(words) if level == 0 else [_ext_row(row) for row in words]
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
            weight = evaluate_basis(list(folds) + tail_folds)
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


@dataclass(frozen=True)
class ZerocheckResult:
    z_skip: E
    rho: tuple[E, ...]
    r: tuple[E, ...]
    v_a: E
    v_b: E
    v_c: E


def verify_flock_zerocheck(log_n: int, transcript: Transcript) -> ZerocheckResult:
    """The zerocheck: one univariate skip round, then nflock quadratic ones."""
    require(log_n >= FLOCK_K_SKIP + len(FIXED_CHALLENGES), "Flock zerocheck input is too small")
    # The point r: seven fixed coordinates, the rest sampled.
    r = (*FIXED_CHALLENGES, *transcript.samples(log_n - FLOCK_K_SKIP - len(FIXED_CHALLENGES)))

    # P^AB and P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    p_ab_coset = transcript.scalars(K_BITS)
    p_c_coset = transcript.scalars(K_BITS)
    z_skip = transcript.sample()
    p_sum_coset = [ab + c for ab, c in zip(p_ab_coset, p_c_coset, strict=True)]
    v_c = lagrange_interpolate(PHI[K_BITS : 2 * K_BITS], p_c_coset, z_skip)
    v_ab = lagrange_interpolate(PHI[: 2 * K_BITS], [ZERO] * K_BITS + p_sum_coset, z_skip) + v_c

    # nflock quadratic rounds on P^AB, closed by v_a, v_b.
    running, rho = v_ab, []
    for equality in r:
        message = transcript.round_poly(3, running, equality)
        challenge = transcript.sample()
        rho.append(challenge)
        running = poly_eval(message, challenge)
    v_a, v_b = transcript.scalars(2)
    require(running == v_a * v_b, "Flock zerocheck terminal mismatch")
    return ZerocheckResult(z_skip, tuple(rho), r, v_a, v_b, v_c)


def verify_flock_lincheck(
    z_skip: E,
    rho: tuple[E, ...],
    v_a: E,
    v_b: E,
    transcript: Transcript,
) -> tuple[tuple[E, ...], tuple[E, ...]]:
    """Lincheck at the quirky point (z_skip, rho): the ab claim's point, then its 64 slices s_ab."""
    # alpha batches the two identities and the constant-position check in its powers.
    alpha = transcript.sample()
    alpha_sq = alpha * alpha
    # e_row: phi8 Lagrange in the skip coordinate, eq in the slot variables.
    skip_weights = lagrange_weights(PHI[:K_BITS], z_skip)
    e_row = [weight * value for weight in eq_kernel(rho[:QFLOCK_SLOT_BITS]) for value in skip_weights]

    # The 8 rounds that bind the high column coordinates, leaving 64 unfolded.
    running, round_challenges = alpha * v_a + v_b + alpha_sq, []
    for _ in range(QFLOCK_SLOT_BITS):
        message = transcript.round_poly(3, running)
        challenge = transcript.sample()
        running = poly_eval(message, challenge)
        round_challenges.append(challenge)
    r_lc = running

    # The residual, then the terminal identity, pin term included.
    s_ab = tuple(transcript.scalars(K_BITS))
    rho_in_prime = tuple(reversed(round_challenges))
    w_col = [value * weight for weight in eq_kernel(rho_in_prime) for value in s_ab]
    terminal = blake2s_bilinear(alpha, e_row, w_col) + alpha_sq * w_col[BLAKE2S_CONSTANT_COLUMN]
    require(terminal == r_lc, "Flock lincheck terminal mismatch")
    return rho_in_prime + rho[QFLOCK_SLOT_BITS:], s_ab


def blake2s_bilinear(
    alpha: E,
    row_weights: Sequence[E],
    column_weights: Sequence[E],
) -> E:
    """Both matrix terms at once, `sum_{k,j} (alpha*A0 + B0)(k,j) e_row(k) w_col(j)`,
    by one forward walk of the circuit instead of touching its ~89M nonzeros."""
    size = 2**BLAKE2S_R1CS_LOG_SIZE
    require(len(row_weights) == size, "bad BLAKE2s row-weight vector")
    require(len(column_weights) == size, "bad BLAKE2s column-weight vector")
    constant = BLAKE2S_CONSTANT_COLUMN
    message_base = 640
    counter_low = 1152
    counter_high = 1184
    final_flag = 1216
    last_node_flag = 1248
    gates_base = 1280
    gate_stride = 184
    left_total = ZERO
    right_total = ZERO
    constant_rows = ZERO

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
        nonlocal left_total, right_total
        carry = ZERO
        output = []
        for bit in range(32):
            if bit < 31:
                weight = row_weights[carry_base + bit]
                left_total += weight * (x[bit] + carry)
                right_total += weight * (y[bit] + carry)
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
        nonlocal left_total, right_total
        majority = []
        for bit in range(31):
            weight = row_weights[base + bit]
            left_total += weight * (x[bit] + z[bit])
            right_total += weight * (y[bit] + z[bit])
            majority.append(column_weights[base + bit] + z[bit])
        ripple_base = base + 31
        carry = ZERO
        output = []
        for bit in range(32):
            q = ZERO if bit == 0 else majority[bit - 1]
            left = x[bit] + y[bit] + z[bit] + carry
            output.append(left + q)
            if 1 <= bit <= 30:
                weight = row_weights[ripple_base + bit - 1]
                left_total += weight * left
                right_total += weight * (q + carry)
                carry += column_weights[ripple_base + bit - 1]
        return tuple(output)

    def linear_rows(values: Sequence[E], base: int) -> None:
        nonlocal left_total, constant_rows
        for bit in range(32):
            left_total += row_weights[base + bit] * values[bit]
            constant_rows += row_weights[base + bit]

    for base, length in ((0, 256), (message_base, 512), (counter_low, 128)):
        for row in range(base, base + length):
            left_total += row_weights[row] * column_weights[row]
            constant_rows += row_weights[row]

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

    constant_weight = column_weights[constant]
    left_total += constant_weight * row_weights[constant]
    right_total += constant_weight * (constant_rows + row_weights[constant])
    return alpha * left_total + right_total


@dataclass(frozen=True)
class FlockClaims:
    """The two families of 64 claims ring switching has to bind to q_flock:
    s_ab[i] = z(i, ab_point) and s_c[i] = z(i, c_point) for i < 64."""

    ab_point: tuple[E, ...]
    c_point: tuple[E, ...]
    s_ab: tuple[E, ...]
    s_c: tuple[E, ...]


def verify_flock(log_n: int, transcript: Transcript) -> FlockClaims:
    """The reduction in protocol order: zerocheck, the C family, lincheck."""
    zc = verify_flock_zerocheck(log_n, transcript)
    # The C family, tied to v_c by the quirky extension at z_skip.
    s_c = tuple(transcript.scalars(K_BITS))
    require(lagrange_interpolate(PHI[:K_BITS], s_c, zc.z_skip) == zc.v_c, "Flock c-slice mismatch")
    ab_point, s_ab = verify_flock_lincheck(zc.z_skip, zc.rho, zc.v_a, zc.v_b, transcript)
    return FlockClaims(ab_point, zc.r, s_ab, s_c)


# Ring switching --------------------------------------------------------------

RING_MAP_SHIFTS = (32, 16, 8, 4, 2, 1)


def _coordinate_weights(challenges: Sequence[E]) -> list[E]:
    """`ring_switch::build_coordinate_weights`: the images `Phi(basis_w)` of the
    F2-coordinate basis under the six composed two-term linearized maps. The
    verifier weights the transposed columns with these; the guest applies the
    same composition directly."""
    weights = []
    for w in range(192):
        # b_w has only bit w set: limb w // 64, bit w % 64.
        limbs = [0, 0, 0]
        limbs[w // 64] = 2 ** (w % 64)
        element = E(*limbs)
        for challenge, shift in zip(challenges, RING_MAP_SHIFTS, strict=True):
            frobenius = element
            for _ in range(shift):
                frobenius *= frobenius
            element += challenge * frobenius
        weights.append(element)
    return weights


def _linear_map(value: E, weights: Sequence[E]) -> E:
    result = ZERO
    bits = int(value)
    while bits:
        bit = (bits & -bits).bit_length() - 1
        result += weights[bit]
        bits &= bits - 1
    return result


def _ring_weight(
    suffix_point: Sequence[E],
    query: Sequence[E],
    coordinate_weights: Sequence[E],
) -> E:
    """The MLE of the transparent weight `W(u) = Phi(eq(suffix_point, u))`, at `query`."""
    suffix_tensor = eq_kernel(suffix_point)
    query_tensor = eq_kernel(query)
    return dot(query_tensor, [_linear_map(weight, coordinate_weights) for weight in suffix_tensor])


# Stacked opening -------------------------------------------------------------


def verify_stacked_opening(
    transcript: Transcript,
    root: Digest,
    stack_log: int,
    log_inv_rate: int,
    qflock: Placement,
    reduction: FlockClaims,
    point_claims: Sequence[tuple[Sequence[E], E]],
) -> None:
    """Bind both ring-switched claims and all ordinary stack point claims."""
    # Flock checked both families already, so nothing is read from the transcript.
    ring_points = (reduction.ab_point, reduction.c_point)
    ring_families = (reduction.s_ab, reduction.s_c)

    map_challenges = transcript.samples(len(RING_MAP_SHIFTS))
    coordinate_weights = _coordinate_weights(map_challenges)
    # Each family's target: `sum_i x^i Phi(s_i)` with x = GEN (doc annex A).
    ring_values = [dot(powers(GEN, K_BITS), [_linear_map(value, coordinate_weights) for value in values]) for values in ring_families]

    # One challenge for both families over disjoint power ranges: the ring-switch
    # pair takes its low powers, the claim pool the rest.
    for _, value in point_claims:
        transcript.observe(value)
    scales = powers(transcript.sample(), len(ring_points) + len(point_claims))
    ring_scales, point_scales = scales[: len(ring_points)], scales[len(ring_points) :]
    target = dot(ring_scales, ring_values) + dot(point_scales, [value for _, value in point_claims])

    selector = qflock.selector

    def evaluate_basis(point: Sequence[E]) -> E:
        """Every pooled claim's weight at the opening's terminal point.

        The two ring-switched claims are supported on the q_flock region, so
        they carry that placement's selector; an ordinary point claim is an eq
        against the full stacked point.
        """
        low, high = point[: qflock.variables], point[qflock.variables :]
        selector_weight = selector_eq(selector, high)
        ring_value = dot(ring_scales, [_ring_weight(tail, low, coordinate_weights) for tail in ring_points])
        value = selector_weight * ring_value
        for scale, (claim_point, _) in zip(point_scales, point_claims, strict=True):
            value += scale * eq_eval(claim_point, point)
        return value

    verify_whir(
        transcript,
        stack_log,
        log_inv_rate,
        target,
        root,
        evaluate_basis,
    )


# Complete VM verification and CLI -------------------------------------------


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

    # 2] WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    root = Digest.from_halves(*transcript.scalars(2))

    # 3] Bus: one batched GKR over the push, pull and count trees, then the leaf
    # decomposition, which leaves each table a degree-2 form and a total.
    bus = verify_bus_balance(layout, transcript)

    # 4] Rows: one back-loaded table sumcheck over all seven tables, at
    # the bus point, starting from the target the three leaf claims derive.
    # Every table takes a disjoint range of eta powers for its constraints; the
    # three bus sides share the three above them (doc sec:air).
    eta = transcript.sample()
    n_constraints = sum(table.n_constraints for table in TABLES)
    eta_powers = powers(eta, n_constraints + 3)
    constraint_powers, form_powers = eta_powers[:n_constraints], eta_powers[n_constraints:]
    target = dot(form_powers, bus.totals)
    air_claims = verify_constraints(
        build_airs(layout, bus.forms),
        constraint_powers,
        form_powers,
        bus.point,
        target,
        transcript,
    )
    claims = [*bus.claims, *air_claims]

    # 5] Public input: the first two memory cells, as one claim per limb on the
    # line through them. The prover sends one evaluation per limb; the three must
    # reassemble the line's value at the challenge (doc sec:e2e-pi).
    public_challenge = transcript.sample()
    public_limbs = transcript.scalars(3)
    public_point = [ZERO] * layout.placements[MEM_0].variables
    public_point[0] = public_challenge
    public_value = multilinear_eval(pi, [public_challenge])
    require(
        public_limbs[0] + Y * public_limbs[1] + Y * Y * public_limbs[2] == public_value,
        "public input limbs are off the line",
    )
    claims.extend(ColumnClaim(column, tuple(public_point), value) for column, value in zip((MEM_0, MEM_1, MEM_2), public_limbs, strict=True))

    # 6] Locate every claim in the stack: a column claim keeps its point and
    # gains its placement's selector bits; a BLAKE2s value claim is re-routed to
    # the equal q_flock slot evaluation.
    point_claims: list[tuple[tuple[E, ...], E]] = []
    qflock = layout.placements[QFLOCK]
    for claim in claims:
        # A BLAKE2s value column is committed inside q_flock rather than on its
        # own, so its claim is re-routed to the equal evaluation of q_flock's
        # slot: the same point, under a different placement, behind the slot bits.
        slot = virtual_slot(claim.column)
        placement = qflock if slot is not None else layout.placements[claim.column]
        prefix = _selector_point(slot, QFLOCK_SLOT_BITS) if slot is not None else ()
        require(not placement.virtual, "claim targets an uncommitted column")
        require(len(prefix) + len(claim.point) == placement.variables, "column claim dimension mismatch")
        tail = _selector_point(placement.selector, layout.stack_log - placement.variables)
        point_claims.append((prefix + claim.point + tail, claim.value))

    # 7] BLAKE2s validity, then the one opening that discharges every claim.
    reduction = verify_flock(BLAKE2S_R1CS_LOG_SIZE + layout.table_logs[BLAKE2S.opcode], transcript)
    verify_stacked_opening(
        transcript,
        root,
        layout.stack_log,
        log_inverse_rate,
        qflock,
        reduction,
        point_claims,
    )
    transcript.finish()


def main(argv: Sequence[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Verify a leanVM-b execution proof")
    parser.add_argument("bytecode", type=Path, help="stacked bytecode multilinear, little-endian 64-bit words")
    parser.add_argument("public_input", type=Path, help="256-bit public input")
    parser.add_argument("proof", type=Path, help="bincode proof")
    arguments = parser.parse_args(argv)
    try:
        encoded_bytecode = arguments.bytecode.read_bytes()
        require(len(encoded_bytecode) % 8 == 0, "bytecode is not a whole number of 64-bit words")
        bytecode = [K(int.from_bytes(encoded_bytecode[i : i + 8], "little")) for i in range(0, len(encoded_bytecode), 8)]
        verify_execution(bytecode, Digest(arguments.public_input.read_bytes()), Proof.load(arguments.proof))
    except (OSError, ValueError, KeyError, VerificationError) as exc:
        parser.exit(1, f"verification failed: {exc}\n")
    print("verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
