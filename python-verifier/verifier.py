from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache, partial, reduce
from pathlib import Path
from operator import mul
from struct import pack, unpack


class VerificationError(Exception):
    """Invalid proof."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


# Field arithmetic and BLAKE2s ------------------------------------------------

MASK64 = 2**64 - 1


def _base_mul(left: int, right: int) -> int:
    product = 0
    while right:
        if right & 1:
            product ^= left
        right >>= 1
        left <<= 1
    low, high = product & MASK64, product >> 64
    folded = low ^ high ^ (high << 1) ^ (high << 3) ^ (high << 4)
    overflow = folded >> 64
    return ((folded & MASK64) ^ overflow ^ (overflow << 1) ^ (overflow << 3) ^ (overflow << 4)) & MASK64


@dataclass(frozen=True, slots=True)
class K:
    """GF(2^64) = F2[x]/(x^64 + x^4 + x^3 + x + 1): the field the witness is committed over.

    A `K` behaves as its 64-bit representation under `__index__`, so transport
    code (struct packing, byte splitting, bit masking) uses one directly without
    unwrapping it, while arithmetic stays in the field.
    """

    value: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.value, int) or isinstance(self.value, bool) or not 0 <= self.value <= MASK64:
            raise ValueError("a K element is a 64-bit unsigned integer")

    def __index__(self) -> int:
        return self.value

    def to_bytes(self) -> bytes:
        """Its transport image: one 64-bit little-endian word."""
        return self.value.to_bytes(8, "little")

    @staticmethod
    def lift(value: object) -> K:
        """`value` as a K element; anything that is not one is an error."""
        lifted = _as_k(value)
        if lifted is None:
            raise TypeError(f"cannot use {type(value).__name__} as a base-field element")
        return lifted

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
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= MASK64:
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
        object.__setattr__(self, "c0", K.lift(c0))
        object.__setattr__(self, "c1", K.lift(c1))
        object.__setattr__(self, "c2", K.lift(c2))

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
        return isinstance(other, int) and not isinstance(other, bool) and 0 <= other <= MASK64 and self.c0 == other and not (self.c1 or self.c2)

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
#
# One compression, ten rounds, and a byte counter plus a final-block flag that
# are ordinary inputs. There is no chunk tree and no parent-node mode, so a hash
# of any length is a straight chain of compressions, and a hash of exactly 64
# bytes is a single one. That is what the VM's `BLAKE2S` opcode computes and what
# flock proves.

BLAKE2S_IV = (
    0x6A09E667,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
)
BLAKE2S_SIGMA = (
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
    (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3),
    (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4),
    (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8),
    (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13),
    (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9),
    (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11),
    (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10),
    (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5),
    (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0),
)
BLAKE2S_G_LANES = (
    (0, 4, 8, 12),
    (1, 5, 9, 13),
    (2, 6, 10, 14),
    (3, 7, 11, 15),
    (0, 5, 10, 15),
    (1, 6, 11, 12),
    (2, 7, 8, 13),
    (3, 4, 9, 14),
)


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


def stack_offsets(sizes: Sequence[int | None]) -> tuple[list[int], int]:
    """Place a block of 2^size at the next multiple of its own size, largest first.
    Ties keep input order, so both sides derive the same layout from the sizes alone.
    A None size is an entry that is committed elsewhere and takes no room here.
    Returns the offset of each entry and the log2 of the padded total.
    """
    offsets = [0] * len(sizes)
    total = 0
    present = [(index, size) for index, size in enumerate(sizes) if size is not None]
    for index, size in sorted(present, key=lambda item: (-item[1], item[0])):
        offsets[index] = total
        total += 2**size
    return offsets, log2_ceil(max(total, 1))


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


QUAD_NODES = (ZERO, ONE, GEN, GEN**2)


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

    def fields(self) -> list[E]:
        length = self.u64()
        require(length <= self.remaining // 24, "invalid field-vector length")
        return [self.field() for _ in range(length)]

    def base_fields(self) -> list[K]:
        length = self.u64()
        require(length <= self.remaining // 8, "invalid base-field-vector length")
        return [K(self.u64()) for _ in range(length)]

    def hashes(self) -> tuple[Digest, ...]:
        length = self.u64()
        require(length <= self.remaining // 32, "invalid hash-vector length")
        return tuple(Digest(self.take(32)) for _ in range(length))

    @property
    def remaining(self) -> int:
        return len(self.data) - self.offset

    def finish(self) -> None:
        require(self.remaining == 0, "trailing proof encoding")


@dataclass(frozen=True)
class MerkleOpening:
    """One query's opening: its leaf words and the full sibling path to the root.

    A leaf is its raw K words, which is what the committer hashed, so an E-valued
    row of width `w` arrives as `3w` of them and is regrouped by the reader.
    Unpruned: two queries of the same phase repeat whatever siblings they share,
    which is what makes checking one a walk up one path.
    """

    leaf_data: tuple[K, ...]
    path: tuple[Digest, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> MerkleOpening:
        return cls(tuple(reader.base_fields()), reader.hashes())

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
    merkle_openings: tuple[MerkleOpening, ...]

    @classmethod
    def from_bincode(cls, data: bytes) -> Proof:
        reader = BinaryReader(data)
        stream = tuple(reader.fields())
        count = reader.u64()
        require(count <= reader.remaining // 16, "invalid opening count")
        merkle_openings = tuple(MerkleOpening.read(reader) for _ in range(count))
        reader.finish()
        return cls(stream, merkle_openings)

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
    # The one removed-guard site with nothing downstream to catch a bad length:
    # a short operand would silently hash to a different value.
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
            require(self.opening_offset < len(self.proof.merkle_openings), "Merkle opening missing")
            opening = self.proof.merkle_openings[self.opening_offset]
            self.opening_offset += 1
            require(0 <= query < block_length, "Merkle query is out of range")
            require(len(opening.leaf_data) == leaf_words, "opened row has the wrong width")
            require(len(opening.path) == height, "Merkle path has the wrong length")
            require(opening.root(query) == root, "Merkle root mismatch")
            rows.append(opening.leaf_data)
        return rows

    def round_poly(self, count: int, claim: E, equality: E | None = None) -> list[E]:
        """Read one sumcheck round polynomial and check it answers `claim`.

        Vanilla sumcheck: every evaluation is on the stream, `h(0)` included, so
        nothing is reconstructed here. What the wire saved by omitting `h(0)` is
        exactly the identity checked here, `h(0) + h(1) = claim`, or its
        eq-weighted form `(1 + r)·h(0) + r·h(1) = claim` for a round whose eq
        factor the protocol pulled out.
        """
        evaluations = self.scalars(count)
        split = evaluations[0] + evaluations[1] if equality is None else (ONE + equality) * evaluations[0] + equality * evaluations[1]
        require(split == claim, "sumcheck round does not answer the running claim")
        return evaluations

    def finish(self) -> None:
        require(self.stream_offset == len(self.proof.stream), "proof stream not fully consumed")
        require(self.opening_offset == len(self.proof.merkle_openings), "Merkle openings not fully consumed")


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
    """A degree-2 polynomial over columns: a bus coordinate and a bus form both.

    A coordinate of a bus tuple and a table's accumulated bus contribution are
    the same object, which is why one type serves as both. ``linear`` and
    ``quadratic`` are keyed by column (local to a table for the blocks it owns,
    global for the framework blocks); ``quadratic`` is what carries an address
    ``fp*g^o`` or an arithmetic result without committing a column for it.
    ``index`` is the coefficient of the g-power column g^i, the one coordinate a
    row derives from its position rather than from a committed column.

    Degree stays at 2, which the AIR identities already are, so the table
    sumcheck's round polynomial does not grow.
    """

    constant: E = ZERO
    linear: dict[int, E] = field(default_factory=dict)
    quadratic: dict[tuple[int, int], E] = field(default_factory=dict)
    index: E = ZERO

    def add_scaled(self, other: Form, weight: E) -> None:
        self.constant += weight * other.constant
        for column, coefficient in other.linear.items():
            self.linear[column] = self.linear.get(column, ZERO) + weight * coefficient
        for pair, coefficient in other.quadratic.items():
            self.quadratic[pair] = self.quadratic.get(pair, ZERO) + weight * coefficient
        self.index += weight * other.index

    def evaluate(self, column: Callable[[int], E], point: Sequence[E] = ()) -> E:
        """Substitute a value for every column, and the point for the index term."""
        total = self.constant
        for index, coefficient in self.linear.items():
            total += coefficient * column(index)
        for (a, b), coefficient in self.quadratic.items():
            total += coefficient * column(a) * column(b)
        if self.index != ZERO:
            total += self.index * index_mle(point)
        return total


@dataclass(frozen=True)
class BusBlock:
    """One block of a bus side: 2^log_rows rows of one tuple shape.

    A block a table owns names that table's columns in ITS OWN local indices,
    which is what its bus form is written over; the framework blocks (memory,
    bytecode, boundary) name global columns.
    """

    log_rows: int
    coordinates: tuple[Form, ...]
    owner: int | None = None
    # The stacked bytecode multilinear, on the one block whose remaining tuple
    # coordinates are public: its slots ARE those coordinates.
    public: Sequence[K] | None = None


@dataclass(frozen=True)
class BusLayout:
    depth: int
    offsets: tuple[int, ...]


def bus_layout(blocks: Sequence[BusBlock]) -> BusLayout:
    offsets, depth = stack_offsets([block.log_rows for block in blocks])
    return BusLayout(depth, tuple(offsets))


@dataclass(frozen=True)
class ColumnClaim:
    column: int
    point: tuple[E, ...]
    value: E


# A tuple is fingerprinted MULTILINEARLY: slot x weighs eq(alphas, x), not
# alpha^x (doc sec:gp). Each leaf factor is then of total degree N_TUPLE_BITS in
# the challenges, and the aligned bytecode polynomial is read off at the
# challenge vector itself (doc sec:e2e-bc).
N_TUPLE_BITS = 4


def _decompose_bus_side(
    blocks: Sequence[BusBlock],
    layout: BusLayout,
    point: Sequence[E],
    alphas: Sequence[E],
    gamma: E,
    forms: Sequence[Form],
    claims: list[ColumnClaim],
    transcript: Transcript,
) -> E:
    require(len(point) == layout.depth, "bus point dimension mismatch")
    weights = eq_kernel(alphas)

    def committed_value(column: int, low_point: tuple[E, ...]) -> E:
        for prior in claims:
            if prior.column == column and prior.point == low_point:
                return prior.value
        value = transcript.scalar()
        claims.append(ColumnClaim(column, low_point, value))
        return value

    result = ZERO
    selector_sum = ZERO
    for block_index, block in enumerate(blocks):
        low = tuple(point[: block.log_rows])
        high = point[block.log_rows :]
        selector_weight = selector_eq(layout.offsets[block_index] >> block.log_rows, high)
        selector_sum += selector_weight

        if block.owner is not None:
            # A table's block stays symbolic: it is accumulated into the form the
            # table sumcheck will evaluate over that table's own columns.
            form = forms[block.owner]
            form.constant += selector_weight * gamma
            for slot, coordinate in enumerate(block.coordinates):
                form.add_scaled(coordinate, selector_weight * weights[slot])
            continue

        # A framework block is evaluated here instead, its columns read as claims.
        fingerprint = sum(
            (weights[slot] * c.evaluate(partial(committed_value, low_point=low), low) for slot, c in enumerate(block.coordinates)),
            ZERO,
        )
        # The public coordinates' weighted sum IS the stacked polynomial at
        # (zeta, alpha), the weights being eq(alpha, .): one evaluation, not nine.
        if block.public is not None:
            fingerprint += multilinear_eval(block.public, (*low, *alphas))
        result += selector_weight * (gamma + fingerprint)

    # Unoccupied rows of the packed leaf cube contain the product identity.
    return result + ONE + selector_sum


@dataclass(frozen=True)
class BusResult:
    claims: tuple[ColumnClaim, ...]
    point: tuple[E, ...]  # the GKR point zeta, which the table sumcheck reuses
    forms: tuple[tuple[Form, ...], ...]  # forms[side][table]
    totals: tuple[E, E, E]  # what the tables owe each side, derived


def verify_bus_balance(
    push: Sequence[BusBlock],
    pull: Sequence[BusBlock],
    count: Sequence[BusBlock],
    transcript: Transcript,
) -> BusResult:
    push_layout = bus_layout(push)
    pull_layout = bus_layout(pull)
    count_layout = bus_layout(count)
    require(push_layout.depth == pull_layout.depth, "push/pull bus depths differ")
    require(count_layout.depth <= push_layout.depth, "count bus is deeper than push bus")

    alphas = transcript.samples(N_TUPLE_BITS)
    count_alphas = (ZERO,) * N_TUPLE_BITS
    gamma = transcript.sample()
    padded_count_layout = BusLayout(push_layout.depth, count_layout.offsets)
    product = verify_product_triple(push_layout.depth, transcript)
    push_root, pull_root, count_root = product.roots
    require(count_root != ZERO, "a bus read count is zero")

    # Every row of every table is a real row: the prover's fill blocks bring each
    # table's count up to a power of two, so the two sides balance outright with no
    # padding surplus to divide back out.
    require(push_root == pull_root, "bus is unbalanced")

    claims: list[ColumnClaim] = []
    forms = tuple(tuple(Form() for _ in TABLES) for _ in range(3))
    sides = (
        (push, push_layout, alphas, gamma),
        (pull, pull_layout, alphas, gamma),
        (count, padded_count_layout, count_alphas, ZERO),
    )
    totals = []
    for side, (blocks, side_layout, side_alphas, side_gamma) in enumerate(sides):
        known_contribution = _decompose_bus_side(
            blocks,
            side_layout,
            product.point,
            side_alphas,
            side_gamma,
            forms[side],
            claims,
            transcript,
        )
        totals.append(known_contribution + product.values[side])

    # The recursive verifier defers a claim on the public bytecode polynomial. Its
    # point comes from alpha alone (doc sec:e2e-bc), so nothing is observed here and
    # no selector challenge is drawn.
    return BusResult(tuple(claims), product.point, forms, (totals[0], totals[1], totals[2]))


# Table sumcheck -------------------------------------------------------------


@dataclass(frozen=True)
class Air:
    """One table at its announced height, with the bus forms it owes each side."""

    table: Table
    log_height: int
    forms: tuple[Form, ...]

    def evaluate(self, constraint_powers: Sequence[E], form_powers: Sequence[E], columns: Sequence[E]) -> E:
        """This table's share of the batch's summand: its identities, then its bus forms."""
        terms = self.table.constraints(lambda name: columns[self.table.col(name)])
        identities = dot(constraint_powers, terms)
        buses = dot(form_powers, [form.evaluate(lambda index: columns[index]) for form in self.forms])
        return identities + buses


@dataclass(frozen=True)
class AirClaim:
    point: tuple[E, ...]
    evaluations: tuple[E, ...]


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
) -> list[AirClaim]:
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
        claim = lagrange_interpolate(QUAD_NODES, message, challenge)
        for table_index, air in enumerate(airs):
            weights[table_index] *= equality if air.log_height > variable else challenge

    final = ZERO
    cursor = 0
    claims: list[AirClaim] = []
    for table_index, air in enumerate(airs):
        evaluations = tuple(transcript.scalars(air.table.width))
        table_constraint_powers = constraint_powers[cursor : cursor + air.table.n_constraints]
        cursor += air.table.n_constraints
        final += weights[table_index] * air.evaluate(table_constraint_powers, form_powers, evaluations)
        claims.append(AirClaim(tuple(point[: air.log_height]), evaluations))
    require(final == claim, "AIR terminal mismatch")
    return claims


# VM statement, layout, and AIR -----------------------------------------------

R1CS_DIGEST = bytes.fromhex("ec91e9d8d9ca4e306205907a0d236e53a6cdbda0382ef6c433ef9363edfe042e")

# The bytecode's nine public columns (opcode + eight operand/immediate slots)
# stack along 2^N_BYTECODE_SELECTORS slots of the polynomial the verifier is
# handed (`lean_vm::cpu::layout::bytecode_table`), each at its bus tuple
# coordinate, which is what makes the program's whole share of a bus leaf ONE
# evaluation of that polynomial at (zeta, alpha) (doc sec:e2e-bc).
N_BYTECODE_SELECTORS = 4


# The columns no instruction table owns (doc sec:e2e-unrolled, Commitment): the
# memory image's three limbs, the two finalize counts, and flock's packed
# witness. They come first in the global column numbering, the tables after.
GLOBAL_COLUMNS = ("mem_0", "mem_1", "mem_2", "mem_final_cnt", "bytecode_final_cnt", "qflock")
MEM_0, MEM_1, MEM_2, MEM_FINAL_CNT, BYTECODE_FINAL_CNT, QFLOCK = range(len(GLOBAL_COLUMNS))

# flock proves one BLAKE2s compression over 2^14 witness bits, packed 64 to a
# K-element, so q_flock has QFLOCK_SLOT_BITS low variables selecting the word
# within an instance and the table's log height above them (doc sec:tab-blake2s).
FLOCK_LOG_BITS = 14
PACKED_BITS = 64  # bits per committed K-element (doc sec:ringswitch)
FLOCK_K_SKIP = log2_ceil(PACKED_BITS)
QFLOCK_SLOT_BITS = FLOCK_LOG_BITS - FLOCK_K_SKIP
BLAKE2S_CONSTANT_COLUMN = 512


@dataclass(frozen=True)
class Placement:
    variables: int
    offset: int

    @property
    def virtual(self) -> bool:
        return self.variables < 0


@dataclass(frozen=True)
class Layout:
    push: tuple[BusBlock, ...]
    pull: tuple[BusBlock, ...]
    count: tuple[BusBlock, ...]
    placements: tuple[Placement, ...]
    stack_log: int
    table_logs: tuple[int, ...]


def _gpow(index: int) -> E:
    return GEN**index


def _const(value: E | int) -> Form:
    return Form(constant=value if isinstance(value, E) else E(value))


def _col(index: int) -> Form:
    return Form(linear={index: ONE})


def _gcol(index: int) -> Form:
    return Form(linear={index: GEN})


def _sum(terms: Iterable[Form]) -> Form:
    total = Form()
    for term in terms:
        total.add_scaled(term, ONE)
    return total


def _prod(a: int, b: int, exponent: int = 0) -> Form:
    return Form(quadratic={(a, b): _gpow(exponent)})


_INDEX_COORDINATE = Form(index=ONE)


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Form, ...]] = []
        self.pull: list[tuple[Form, ...]] = []

    def pair(self, push: Sequence[Form], pull: Sequence[Form]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state_step(self, pc: int, fp: int) -> None:
        self.pair((_const(ONE), _gcol(pc), _col(fp)), (_const(ONE), _col(pc), _col(fp)))

    def state_derived(self, pc: int, fp: int, npc: Form, nfp: Form) -> None:
        self.pair((_const(ONE), npc, nfp), (_const(ONE), _col(pc), _col(fp)))

    def bytecode(self, pc: int, count: int, opcode: int, operands: Sequence[Form]) -> None:
        prefix_push = (_const(GEN * GEN), _col(pc), _gcol(count), _const(_gpow(opcode)))
        prefix_pull = (_const(GEN * GEN), _col(pc), _col(count), _const(_gpow(opcode)))
        self.pair((*prefix_push, *operands), (*prefix_pull, *operands))

    def memory(self, address: Form, count: int, values: Sequence[Form]) -> None:
        self.pair(
            (_const(GEN), address, _gcol(count), *values),
            (_const(GEN), address, _col(count), *values),
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
    n_constraints: int = 0

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
    Table("jump", 4, JUMP_COLUMNS, _flushes_jump, _jump_constraints, 2),
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


def build_layout(bytecode: Sequence[K], log_memory: int, table_logs: Sequence[int]) -> Layout:
    log_bytecode = log2_strict(len(bytecode)) - N_BYTECODE_SELECTORS
    require(
        16 <= log_memory <= 32
        and len(table_logs) == len(TABLES)
        and all(0 <= height <= 32 for height in table_logs)
        # flock sizes its argument to at least 2^3 instances and the BLAKE2s table's value
        # columns share that instance cube, so a smaller height is not expressible.
        and table_logs[BLAKE2S.opcode] >= 3,
        "invalid announced table sizes",
    )
    table_logs = list(table_logs)

    def frame(state: Form, memory_count: Form, bytecode_count: Form) -> list[BusBlock]:
        """The blocks no table owns: the boundary state, then the two arrays.

        The two sides run the same three blocks and differ only here. Push seeds
        each array with count one; pull finalizes it with the committed final
        count, and its boundary state is the last pc rather than the first.
        """
        return [
            BusBlock(0, (_const(ONE), state, _const(ONE))),
            BusBlock(log_memory, (_const(GEN), _INDEX_COORDINATE, memory_count, _col(MEM_0), _col(MEM_1), _col(MEM_2))),
            BusBlock(log_bytecode, (_const(GEN * GEN), _INDEX_COORDINATE, bytecode_count), public=bytecode),
        ]

    push = frame(_const(ONE), _const(ONE), _const(ONE))
    pull = frame(_const(_gpow(2**log_bytecode - 1)), _col(MEM_FINAL_CNT), _col(BYTECODE_FINAL_CNT))
    count: list[BusBlock] = []
    for table, height in zip(TABLES, table_logs, strict=True):
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
    kappas[BYTECODE_FINAL_CNT] = log_bytecode
    kappas[QFLOCK] = table_logs[BLAKE2S.opcode] + QFLOCK_SLOT_BITS
    for table, (base, width) in enumerate(zip(BASES, WIDTHS, strict=True)):
        kappas[base : base + width] = [table_logs[table]] * width
    for local in BLAKE2S_SLOT_BY_COLUMN:
        kappas[BASES[BLAKE2S.opcode] + local] = None
    offsets, total_log = stack_offsets(kappas)
    placements = [Placement(-1, 0) if variables is None else Placement(variables, offset) for variables, offset in zip(kappas, offsets, strict=True)]
    # Floor at the PCS minimum: WHIR's level ladder needs room, so a tiny
    # witness zero-pads up to it. Both sides derive this from the kappas.
    stack_log = max(15, total_log)
    return Layout(tuple(push), tuple(pull), tuple(count), tuple(placements), stack_log, tuple(table_logs))


def build_airs(layout: Layout, bus_forms: Sequence[Sequence[Form]]) -> list[Air]:
    return [Air(table, height, tuple(side[table.opcode] for side in bus_forms)) for table, height in zip(TABLES, layout.table_logs, strict=True)]


def constraint_claims(claims: Sequence[AirClaim]) -> list[ColumnClaim]:
    result: list[ColumnClaim] = []
    for base, claim in zip(BASES, claims, strict=True):
        for local, value in enumerate(claim.evaluations):
            result.append(ColumnClaim(base + local, claim.point, value))
    return result


def virtual_slot(column: int) -> int | None:
    """The q_flock slot a BLAKE2s value column rides in, or None if committed."""
    return BLAKE2S_SLOT_BY_COLUMN.get(column - BASES[BLAKE2S.opcode])


# WHIR opening ----------------------------------------------------------------

INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 3
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5

MIN_STACKED_LOG = 15
MAX_STACKED_LOG = 32

WHIR_QUERIES = (((223,56,36), (223,56,37), (223,56,37), (224,56,37,28), (224,56,37,28), (224,56,38,28), (224,56,38,28,22), (225,56,38,28,23), (225,56,38,28,23), (225,56,38,28,23,19), (226,56,38,28,23,19), (226,56,38,28,23,19), (227,56,38,28,23,19,16), (228,56,38,28,23,19,16), (228,56,38,28,23,19,16), (229,57,38,28,23,19,17,14), (230,57,38,29,23,19,17,14), (232,57,38,29,23,19,17,15)), ((112,45,31), (112,45,32), (112,45,32), (112,45,32,25), (112,45,32,25), (112,45,32,25), (112,45,32,25,20), (112,45,32,25,21), (112,45,32,25,21), (113,45,32,25,21,17), (113,45,32,25,21,18), (113,45,32,25,21,18), (113,45,32,25,21,18,15), (113,45,32,25,21,18,15), (114,45,32,25,21,18,15), (114,45,33,25,21,18,15,14), (114,45,33,25,21,18,16,14), (115,46,33,25,21,18,16,14)), ((75,37,28), (75,37,28), (75,38,28), (75,38,28,22), (75,38,28,23), (75,38,28,23), (75,38,28,23,19), (75,38,28,23,19), (75,38,28,23,19), (75,38,28,23,19,16), (75,38,28,23,19,16), (75,38,28,23,19,16), (75,38,28,23,19,17,14), (76,38,29,23,19,17,14), (76,38,29,23,19,17,15), (76,38,29,23,19,17,15,13), (76,38,29,23,19,17,15,13), (77,38,29,23,19,17,15,13)), ((56,32,25), (56,32,25), (56,32,25), (56,32,25,20), (56,32,25,21), (56,32,25,21), (56,32,25,21,17), (56,32,25,21,18), (56,32,25,21,18), (57,32,25,21,18,15), (57,32,25,21,18,15), (57,32,25,21,18,15), (57,33,25,21,18,15,14), (57,33,25,21,18,16,14), (57,33,25,21,18,16,14), (57,33,26,21,18,16,14,12), (57,33,26,21,18,16,14,13), (58,33,26,21,18,16,14,13)))  # fmt: skip


@dataclass(frozen=True)
class WhirConfig:
    log_inv_rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]
    query_grinding_bits: tuple[int, ...]
    fold_grinding_bits: tuple[int, ...]
    ood_samples: tuple[int, ...]


def derive_config(log_n: int, log_inv_rate: int) -> WhirConfig:
    """Derive the production Johnson/OOD ladder used by the Rust PCS."""
    require(MIN_STACKED_LOG <= log_n <= MAX_STACKED_LOG and 1 <= log_inv_rate <= 4, "invalid WHIR shape")
    folds = [INITIAL_FOLDING_FACTOR]
    message_logs = [log_n - INITIAL_FOLDING_FACTOR]
    log_inv_rates = [log_inv_rate]
    remaining = message_logs[0]
    prior_fold = INITIAL_FOLDING_FACTOR
    reduction = RS_DOMAIN_INITIAL_REDUCTION_FACTOR
    while remaining > RESIDUAL_MAX_LOG:
        fold = min(SUBSEQUENT_FOLDING_FACTOR, remaining)
        log_inv_rates.append(log_inv_rates[-1] + prior_fold - reduction)
        remaining -= fold
        folds.append(fold)
        message_logs.append(remaining)
        prior_fold = fold
        reduction = RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
    require(len(folds) >= 2, "WHIR requires at least two levels")
    queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG]
    require(len(queries) == len(folds), "tabulated query count does not match the ladder")
    return WhirConfig(
        log_inv_rates=tuple(log_inv_rates),
        folds=tuple(folds),
        queries=queries,
        query_grinding_bits=(17,) * len(folds),
        fold_grinding_bits=(0,) * len(folds),
        # Not a searched parameter: one per level, except level 0 which needs none.
        ood_samples=(0,) + (1,) * (len(folds) - 1),
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


@dataclass(frozen=True)
class QuadraticMessage:
    constant: E
    linear: E
    quadratic: E

    def evaluate(self, point: E) -> E:
        return self.constant + point * (self.linear + point * self.quadratic)

    def add_scaled(self, other: QuadraticMessage, scale: E) -> QuadraticMessage:
        return QuadraticMessage(
            self.constant + scale * other.constant,
            self.linear + scale * other.linear,
            self.quadratic + scale * other.quadratic,
        )


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
    message_log: int  # the level's message width, which rebuilds its share of the point
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

    def next_quad(claim: E) -> QuadraticMessage:
        at_zero, at_one, at_infinity = transcript.round_poly(3, claim)
        return QuadraticMessage(at_zero, at_zero + at_one + at_infinity, at_infinity)

    transcript.observe(target)
    for half in root.halves():
        transcript.observe(half)
    running_target = target
    running_quad = next_quad(target)
    folds: list[E] = []
    glued: list[GluedClaim] = []
    current_root = root

    for level, (fold_count, level_rate) in enumerate(zip(config.folds, config.log_inv_rates, strict=True)):
        level_folds: list[E] = []
        for fold_index in range(fold_count):
            bits = max(0, config.fold_grinding_bits[level] - fold_index)
            if bits:
                transcript.grind_check(bits)
            challenge = transcript.sample()
            folds.append(challenge)
            level_folds.append(challenge)
            running_target = running_quad.evaluate(challenge)
            running_quad = next_quad(running_target)

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        # The level's claims, held until its batching challenge is drawn: the
        # OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        pending_ood: list[tuple[tuple[E, ...], E, QuadraticMessage]] = []
        if final_level:
            residual = tuple(transcript.scalars(2**message_log))
        else:
            next_root = Digest.from_halves(*transcript.scalars(2))
            for _ in range(config.ood_samples[level + 1]):
                point = tuple(transcript.samples(message_log))
                value = transcript.scalar()
                pending_ood.append((point, value, next_quad(value)))

        transcript.grind_check(config.query_grinding_bits[level])
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
        intro = next_quad(enforced)
        scalar = ONE
        for point, value, ood_intro in pending_ood:
            scalar *= lam
            running_quad = running_quad.add_scaled(ood_intro, scalar)
            running_target += scalar * value
            glued.append(GluedClaim(scalar, message_log, len(folds), lambda x, z=point: eq_eval(z, x)))
        scalar *= lam
        running_quad = running_quad.add_scaled(intro, scalar)
        running_target += scalar * enforced
        batch = (message_log, tuple(queries), tuple(query_weights))
        glued.append(GluedClaim(scalar, message_log, len(folds), lambda x, b=batch: _induced_weight(*b, x)))

        if final_level:
            # Finish the remaining sumcheck rounds and close on one evaluation
            # of every basis at the resulting point.
            tail_folds: list[E] = []
            for round_index in range(message_log):
                challenge = transcript.sample()
                running_target = running_quad.evaluate(challenge)
                tail_folds.append(challenge)
                if round_index + 1 < message_log:
                    running_quad = next_quad(running_target)
            # Each glued claim is rebound at the terminal point: the fold
            # challenges its level fixed after it was made, then the tail.
            weight = evaluate_basis(list(folds) + tail_folds)
            for claim in glued:
                fixed = claim.message_log - message_log
                weight += claim.scalar * claim.weight_at(list(folds[claim.fold_start : claim.fold_start + fixed]) + tail_folds)
            terminal = weight * multilinear_eval(residual, tail_folds)
            require(terminal == running_target, "WHIR terminal check failed")
            return
        current_root = next_root

    raise VerificationError("WHIR verification ended without a terminal level")


# Flock reduction -------------------------------------------------------------

PHI_BASIS = (
    E(0x0000000000000001),
    E(0x033CE8BEDDC8A656),
    E(0x512620375ED2A108),
    E(0x0C9E636090AAFC01),
    E(0xBA4F3CD82801769C),
    E(0xBA26E7904ADB4A47),
    E(0x467698598926DC01),
    E(0x4418AE808B28BDD0),
)
PHI = tuple(sum((PHI_BASIS[bit] for bit in range(8) if value >> bit & 1), ZERO) for value in range(256))
_MEDIUM_GENERATOR = E(
    0x243F6A8885A308D3,
    0x13198A2E03707344,
    0xA4093822299F31D0,
)
_MEDIUM_POWERS = (
    _MEDIUM_GENERATOR,
    _MEDIUM_GENERATOR**2,
    _MEDIUM_GENERATOR**4,
    _MEDIUM_GENERATOR**8,
)

FIXED_CHALLENGES = (
    PHI[0xF7],
    PHI[0x53],
    PHI[0xB5],
    *tuple(value / (ONE + value) for value in _MEDIUM_POWERS),
)
FLOCK_N_INNER = len(FIXED_CHALLENGES)


def quirky_weights(skip_point: E, rest: Sequence[E]) -> list[E]:
    skip = lagrange_weights(PHI[:PACKED_BITS], skip_point)
    tail = eq_kernel(rest)
    return [a * b for b in tail for a in skip]


@dataclass(frozen=True)
class QuirkyPoint:
    skip: E
    inner: tuple[E, ...]
    outer: tuple[E, ...]

    @property
    def ring_tail(self) -> tuple[E, ...]:
        return self.inner + self.outer


@dataclass(frozen=True)
class ZClaim:
    point: QuirkyPoint
    value: E


@dataclass(frozen=True)
class ZerocheckResult:
    skip: E
    rounds: tuple[E, ...]
    equality_tail: tuple[E, ...]
    a: E
    b: E
    c: E


def verify_flock_zerocheck(log_n: int, transcript: Transcript) -> ZerocheckResult:
    require(log_n >= FLOCK_K_SKIP + FLOCK_N_INNER, "Flock zerocheck input is too small")
    require(len(FIXED_CHALLENGES) == FLOCK_N_INNER, "wrong fixed-challenge count")
    sampled_outer = transcript.samples(log_n - FLOCK_K_SKIP - FLOCK_N_INNER)
    equality_tail = (*FIXED_CHALLENGES, *sampled_outer)
    ab_values = transcript.scalars(PACKED_BITS)
    c_values = transcript.scalars(PACKED_BITS)
    skip = transcript.sample()

    c_evaluation = lagrange_interpolate(PHI[PACKED_BITS : 2 * PACKED_BITS], c_values, skip)
    combined = [a + c for a, c in zip(ab_values, c_values, strict=True)]
    combined_evaluation = lagrange_interpolate(PHI[: 2 * PACKED_BITS], [ZERO] * PACKED_BITS + combined, skip)
    running = combined_evaluation + c_evaluation
    rounds = []
    for equality in equality_tail:
        at_zero, at_one, at_infinity = transcript.round_poly(3, running, equality)
        challenge = transcript.sample()
        rounds.append(challenge)
        running = QuadraticMessage(at_zero, at_zero + at_one + at_infinity, at_infinity).evaluate(challenge)
    final_a, final_b = transcript.scalars(2)
    require(running == final_a * final_b, "Flock zerocheck terminal mismatch")
    return ZerocheckResult(skip, tuple(rounds), equality_tail, final_a, final_b, c_evaluation)


@dataclass(frozen=True)
class FlockReduction:
    ab: ZClaim
    c: ZClaim
    ab_s_hat_v: tuple[E, ...]


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


def _transpose(values: Sequence[E]) -> list[E]:
    require(len(values) == PACKED_BITS, "ring-switch slice has the wrong length")
    output = [0] * 192
    for row, value in enumerate(values):
        bits = int(value)
        while bits:
            bit = (bits & -bits).bit_length() - 1
            output[bit] ^= 2**row
            bits &= bits - 1
    return [E(value) for value in output]


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
    """Evaluate the transparent ring-switch weight at one query point."""
    suffix_tensor = eq_kernel(suffix_point)
    query_tensor = eq_kernel(query)
    return dot(query_tensor, [_linear_map(weight, coordinate_weights) for weight in suffix_tensor])


def verify_stacked_opening(
    transcript: Transcript,
    root: Digest,
    stack_log: int,
    log_inv_rate: int,
    qflock_offset: int,
    qflock_variables: int,
    reduction: FlockReduction,
    point_claims: Sequence[tuple[Sequence[E], E]],
) -> None:
    """Bind both ring-switched claims and all ordinary stack point claims."""
    ring_claims = (reduction.ab, reduction.c)
    # A/B's values were already derived from the bound z_partial; only C is sent.
    c_values = tuple(transcript.scalars(PACKED_BITS))
    require(lagrange_interpolate(PHI[:PACKED_BITS], c_values, reduction.c.point.skip) == reduction.c.value, "ring-switch claim mismatch")
    slices = (reduction.ab_s_hat_v, c_values)

    map_challenges = transcript.samples(len(RING_MAP_SHIFTS))
    coordinate_weights = _coordinate_weights(map_challenges)
    ring_values = [dot(_transpose(values), coordinate_weights) for values in slices]

    # One challenge for both families over disjoint power ranges: the ring-switch
    # pair takes its low powers, the claim pool the rest.
    for _, value in point_claims:
        transcript.observe(value)
    scales = powers(transcript.sample(), len(ring_claims) + len(point_claims))
    ring_scales, point_scales = scales[: len(ring_claims)], scales[len(ring_claims) :]
    target = dot(ring_scales, ring_values) + dot(point_scales, [value for _, value in point_claims])

    selector = qflock_offset >> qflock_variables

    def evaluate_basis(point: Sequence[E]) -> E:
        """Every pooled claim's weight at the opening's terminal point.

        The two ring-switched claims are supported on the q_flock region, so
        they carry that placement's selector; an ordinary point claim is an eq
        against the full stacked point.
        """
        low, high = point[:qflock_variables], point[qflock_variables:]
        selector_weight = selector_eq(selector, high)
        ring_value = dot(ring_scales, [_ring_weight(claim.point.ring_tail, low, coordinate_weights) for claim in ring_claims])
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


def verify_flock_lincheck(
    point: QuirkyPoint,
    a: E,
    b: E,
    transcript: Transcript,
) -> tuple[ZClaim, tuple[E, ...]]:
    """Replay the fixed BLAKE2s matrix reduction."""
    alpha = transcript.sample()
    inner_weights = quirky_weights(point.skip, point.inner)
    beta = transcript.sample()
    running = alpha * a + b + beta
    challenges = []
    for _ in range(8):
        at_zero, at_one, at_infinity = transcript.round_poly(3, running)
        challenge = transcript.sample()
        running = QuadraticMessage(at_zero, at_zero + at_one + at_infinity, at_infinity).evaluate(challenge)
        challenges.append(challenge)
    partial = tuple(transcript.scalars(PACKED_BITS))
    rounds = tuple(reversed(challenges))
    rest_weights = eq_kernel(rounds)
    column_weights = [value * weight for weight in rest_weights for value in partial]
    terminal = blake2s_bilinear(alpha, inner_weights, column_weights)
    terminal += beta * column_weights[BLAKE2S_CONSTANT_COLUMN]
    require(terminal == running, "Flock lincheck terminal mismatch")
    skip = transcript.sample()
    value = lagrange_interpolate(PHI[:PACKED_BITS], partial, skip)
    return ZClaim(QuirkyPoint(skip, rounds, point.outer), value), partial


def verify_flock(log_n: int, transcript: Transcript) -> FlockReduction:
    zerocheck = verify_flock_zerocheck(log_n, transcript)
    inner_length = QFLOCK_SLOT_BITS  # the slot bits, the outer ones indexing instances
    ab_point = QuirkyPoint(zerocheck.skip, zerocheck.rounds[:inner_length], zerocheck.rounds[inner_length:])
    ab, ab_s_hat_v = verify_flock_lincheck(ab_point, zerocheck.a, zerocheck.b, transcript)
    c_point = QuirkyPoint(zerocheck.skip, zerocheck.equality_tail[:inner_length], zerocheck.equality_tail[inner_length:])
    return FlockReduction(ab, ZClaim(c_point, zerocheck.c), ab_s_hat_v)


def blake2s_bilinear(
    alpha: E,
    row_weights: Sequence[E],
    column_weights: Sequence[E],
) -> E:
    """Evaluate the two BLAKE2s R1CS matrix forms by walking the circuit."""
    size = 2**FLOCK_LOG_BITS
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


# Complete VM verification and CLI -------------------------------------------


def verify_execution(bytecode: Sequence[K], public_input: Digest, proof: Proof) -> None:
    pi = public_input.halves()
    # The public statement, bound before any challenge (`lean_vm::cpu::fs_seed`).
    # The seed hashes the bytecode multilinear itself, not a structured program,
    # so a verifier holding only the polynomial can reproduce it.
    bytecode_hash = blake2s_hash(b"".join(word.to_bytes() for word in bytecode))
    seed = blake2s_hash(b"leanvm-b-fs-seed-v2-blake2s" + R1CS_DIGEST + bytecode_hash.value)
    transcript = Transcript(proof, b"leanvm-b", (*seed.halves(), *pi))

    # 1] Statement binding: the announced instance shape, checked against the
    # public caps before any reduction runs on it.
    announced = transcript.scalars(2 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced size has a nonzero high limb")
    # These limbs are announced sizes, not field elements: read them as integers.
    log_memory = int(announced[0].c0)
    table_logs = tuple(int(value.c0) for value in announced[1 : 1 + len(TABLES)])
    log_inverse_rate = int(announced[-1].c0)
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    layout = build_layout(bytecode, log_memory, table_logs)

    # 2] WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    root = Digest.from_halves(*transcript.scalars(2))

    # 3] Bus: one batched GKR over the push, pull and count trees, then the leaf
    # decomposition, which leaves each table a degree-2 form and a total.
    bus = verify_bus_balance(layout.push, layout.pull, layout.count, transcript)

    # 4] Rows: one back-loaded table sumcheck over all seven tables, at
    # the bus point, starting from the target the three leaf claims derive.
    # Every table takes a disjoint range of eta powers for its constraints; the
    # three bus sides share the three above them (doc sec:air).
    eta = transcript.sample()
    n_identities = sum(table.n_constraints for table in TABLES)
    eta_powers = powers(eta, n_identities + 3)
    constraint_powers, form_powers = eta_powers[:n_identities], eta_powers[n_identities:]
    target = dot(form_powers, bus.totals)
    air_claims = verify_constraints(
        build_airs(layout, bus.forms),
        constraint_powers,
        form_powers,
        bus.point,
        target,
        transcript,
    )
    claims = list(bus.claims)
    claims.extend(constraint_claims(air_claims))

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
        selector = placement.offset >> placement.variables
        point_claims.append((prefix + claim.point + _selector_point(selector, layout.stack_log - placement.variables), claim.value))

    # 7] BLAKE2s validity, then the one opening that discharges every claim.
    reduction = verify_flock(FLOCK_LOG_BITS + layout.table_logs[BLAKE2S.opcode], transcript)
    verify_stacked_opening(
        transcript,
        root,
        layout.stack_log,
        log_inverse_rate,
        qflock.offset,
        qflock.variables,
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
