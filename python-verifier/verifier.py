"""Dependency-free verifier for leanVM-b execution proofs.

The command-line interface consumes a public statement JSON file and the
project's bincode proof. No prover-side auxiliary data is accepted. The file is
ordered along the verification path: arithmetic and hashing, proof transport,
GKR/bus/AIR checks, VM layout, Ligerito, Flock, and final orchestration.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import ceil, log2
from pathlib import Path
from struct import pack, unpack
from typing import Any, Callable, Sequence


class VerificationError(Exception):
    """The proof or public statement is malformed or inconsistent."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


# Field arithmetic and BLAKE3 -------------------------------------------------

MASK32 = (1 << 32) - 1
MASK128 = (1 << 128) - 1
REDUCTION = 0x87  # x^128 = x^7 + x^2 + x + 1


@dataclass(frozen=True, slots=True)
class F128:
    """GF(2^128), in the GHASH polynomial basis."""

    value: int = 0

    def __post_init__(self) -> None:
        object.__setattr__(self, "value", self.value & MASK128)

    @classmethod
    def new(cls, lo: int, hi: int) -> "F128":
        return cls((lo & ((1 << 64) - 1)) | ((hi & ((1 << 64) - 1)) << 64))

    @classmethod
    def from_bytes(cls, data: bytes) -> "F128":
        require(len(data) == 16, "a field element must contain exactly 16 bytes")
        return cls(int.from_bytes(data, "little"))

    @property
    def lo(self) -> int:
        return self.value & ((1 << 64) - 1)

    @property
    def hi(self) -> int:
        return self.value >> 64

    def to_bytes(self) -> bytes:
        return self.value.to_bytes(16, "little")

    @staticmethod
    def _coerce(other: object) -> "F128":
        if isinstance(other, F128):
            return other
        if isinstance(other, int):
            return F128(other)
        return NotImplemented

    def __int__(self) -> int:
        return self.value

    def __bool__(self) -> bool:
        return self.value != 0

    def __eq__(self, other: object) -> bool:
        rhs = self._coerce(other)
        return False if rhs is NotImplemented else self.value == rhs.value

    def __hash__(self) -> int:
        return hash(self.value)

    def __add__(self, other: object) -> "F128":
        rhs = self._coerce(other)
        if rhs is NotImplemented:
            return NotImplemented
        return F128(self.value ^ rhs.value)

    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__

    def __neg__(self) -> "F128":
        return self

    def __mul__(self, other: object) -> "F128":
        rhs = self._coerce(other)
        if rhs is NotImplemented:
            return NotImplemented
        # Four-bit carry-less windows cut the Python loop from 128 iterations
        # to 32.  Accumulate an unreduced polynomial, then fold its upper half
        # with x^128 = x^7 + x^2 + x + 1 (and fold the at-most-seven overflow
        # bits once more).
        a, b, product = self.value, rhs.value, 0
        multiples = [0] * 16
        for nibble in range(1, 16):
            multiples[nibble] = (
                (a if nibble & 1 else 0)
                ^ (a << 1 if nibble & 2 else 0)
                ^ (a << 2 if nibble & 4 else 0)
                ^ (a << 3 if nibble & 8 else 0)
            )
        shift = 0
        while b:
            product ^= multiples[b & 15] << shift
            b >>= 4
            shift += 4
        low, high = product & MASK128, product >> 128
        folded = low ^ high ^ (high << 1) ^ (high << 2) ^ (high << 7)
        overflow = folded >> 128
        product = (
            (folded & MASK128)
            ^ overflow
            ^ (overflow << 1)
            ^ (overflow << 2)
            ^ (overflow << 7)
        )
        return F128(product & MASK128)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> "F128":
        if exponent < 0:
            return self.inv() ** -exponent
        base, out, n = self, ONE, exponent
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> "F128":
        require(self.value != 0, "division by zero in GF(2^128)")
        return self ** ((1 << 128) - 2)

    def __truediv__(self, other: object) -> "F128":
        rhs = self._coerce(other)
        if rhs is NotImplemented:
            return NotImplemented
        return self * rhs.inv()

    def __rtruediv__(self, other: object) -> "F128":
        lhs = self._coerce(other)
        if lhs is NotImplemented:
            return NotImplemented
        return lhs * self.inv()

    def __repr__(self) -> str:
        return f"F128(0x{self.value:032x})"


ZERO = F128(0)
ONE = F128(1)
GEN = F128(2)


# BLAKE3 --------------------------------------------------------------------

BLAKE3_IV = (
    0x6A09E667,
    0xBB67AE85,
    0x3C6EF372,
    0xA54FF53A,
    0x510E527F,
    0x9B05688C,
    0x1F83D9AB,
    0x5BE0CD19,
)
MSG_PERMUTATION = (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)
CHUNK_START, CHUNK_END, PARENT, ROOT = 1, 2, 4, 8


def _rotr32(x: int, n: int) -> int:
    return ((x >> n) | (x << (32 - n))) & MASK32


def _g(v: list[int], a: int, b: int, c: int, d: int, mx: int, my: int) -> None:
    v[a] = (v[a] + v[b] + mx) & MASK32
    v[d] = _rotr32(v[d] ^ v[a], 16)
    v[c] = (v[c] + v[d]) & MASK32
    v[b] = _rotr32(v[b] ^ v[c], 12)
    v[a] = (v[a] + v[b] + my) & MASK32
    v[d] = _rotr32(v[d] ^ v[a], 8)
    v[c] = (v[c] + v[d]) & MASK32
    v[b] = _rotr32(v[b] ^ v[c], 7)


def blake3_compress_words(
    cv: Sequence[int],
    block_words: Sequence[int],
    counter: int,
    block_len: int,
    flags: int,
) -> tuple[int, ...]:
    """The BLAKE3 compression function, returning all 16 output words."""
    require(len(cv) == 8 and len(block_words) == 16, "invalid BLAKE3 compression input")
    v = list(cv) + list(BLAKE3_IV[:4]) + [
        counter & MASK32,
        (counter >> 32) & MASK32,
        block_len,
        flags,
    ]
    schedule = list(block_words)
    for _ in range(7):
        _g(v, 0, 4, 8, 12, schedule[0], schedule[1])
        _g(v, 1, 5, 9, 13, schedule[2], schedule[3])
        _g(v, 2, 6, 10, 14, schedule[4], schedule[5])
        _g(v, 3, 7, 11, 15, schedule[6], schedule[7])
        _g(v, 0, 5, 10, 15, schedule[8], schedule[9])
        _g(v, 1, 6, 11, 12, schedule[10], schedule[11])
        _g(v, 2, 7, 8, 13, schedule[12], schedule[13])
        _g(v, 3, 4, 9, 14, schedule[14], schedule[15])
        schedule = [schedule[i] for i in MSG_PERMUTATION]
    return tuple((v[i] ^ v[i + 8]) & MASK32 for i in range(8)) + tuple(
        (v[i + 8] ^ cv[i]) & MASK32 for i in range(8)
    )


def _words(block: bytes) -> tuple[int, ...]:
    return unpack("<16I", block.ljust(64, b"\0"))


def _parent_output(
    left: Sequence[int], right: Sequence[int], flags: int = 0
) -> tuple[tuple[int, ...], tuple[int, ...], int, int, int]:
    return BLAKE3_IV, tuple(left) + tuple(right), 0, 64, flags | PARENT


def _output_cv(output: tuple[Sequence[int], Sequence[int], int, int, int]) -> tuple[int, ...]:
    cv, block, counter, block_len, flags = output
    return blake3_compress_words(cv, block, counter, block_len, flags)[:8]


def _output_root(output: tuple[Sequence[int], Sequence[int], int, int, int]) -> bytes:
    cv, block, _counter, block_len, flags = output
    words = blake3_compress_words(cv, block, 0, block_len, flags | ROOT)
    return pack("<16I", *words)[:32]


def _chunk_output(
    chunk: bytes, chunk_counter: int
) -> tuple[Sequence[int], Sequence[int], int, int, int]:
    require(len(chunk) <= 1024, "a BLAKE3 chunk cannot exceed 1024 bytes")
    cv: Sequence[int] = BLAKE3_IV
    blocks = [chunk[i : i + 64] for i in range(0, len(chunk), 64)] or [b""]
    for i, block in enumerate(blocks[:-1]):
        flags = CHUNK_START if i == 0 else 0
        cv = blake3_compress_words(cv, _words(block), chunk_counter, 64, flags)[:8]
    last = blocks[-1]
    flags = CHUNK_END | (CHUNK_START if len(blocks) == 1 else 0)
    return cv, _words(last), chunk_counter, len(last), flags


def blake3_hash(data: bytes) -> bytes:
    """Standard 32-byte unkeyed BLAKE3 hash."""
    chunks = [data[i : i + 1024] for i in range(0, len(data), 1024)] or [b""]
    stack: list[tuple[int, ...]] = []
    last_output = None
    for chunk_index, chunk in enumerate(chunks):
        output = _chunk_output(chunk, chunk_index)
        cv = _output_cv(output)
        total = chunk_index + 1
        while total & 1 == 0:
            left = stack.pop()
            output = _parent_output(left, cv)
            cv = _output_cv(output)
            total >>= 1
        stack.append(cv)
        last_output = output
    if last_output is None:
        raise VerificationError("BLAKE3 produced no chunks")
    # For more than one chunk, combine the right edge with saved left subtrees.
    output = last_output
    right = _output_cv(output)
    for left in reversed(stack[:-1]):
        output = _parent_output(left, right)
        right = _output_cv(output)
    return _output_root(output)


def build_eq(point: Sequence[F128]) -> list[F128]:
    out = [ONE]
    for r in point:
        out = [v * (ONE + r) for v in out] + [v * r for v in out]
    return out


def mle_eval(evals: Sequence[F128], point: Sequence[F128]) -> F128:
    require(len(evals) == 1 << len(point), "multilinear table has the wrong size")
    cur = list(evals)
    for r in point:
        cur = [cur[2 * i] * (ONE + r) + cur[2 * i + 1] * r for i in range(len(cur) // 2)]
    return cur[0]

# Shared verification helpers -------------------------------------------------
def interpolate(a: F128, b: F128, point: F128) -> F128:
    """Evaluate the line through ``a`` and ``b`` at ``point``."""
    return a + point * (a + b)


def eq_eval(left: Sequence[F128], right: Sequence[F128]) -> F128:
    require(len(left) == len(right), "eq: dimension mismatch")
    result = ONE
    for x, y in zip(left, right):
        result *= ONE + x + y
    return result


TRI_NODES = (ZERO, ONE, GEN)
QUAD_NODES = (ZERO, ONE, GEN, GEN * GEN)


def lagrange_eval(
    nodes: Sequence[F128], values: Sequence[F128], point: F128
) -> F128:
    require(len(nodes) == len(values), "Lagrange data length mismatch")
    result = ZERO
    for index, (node, value) in enumerate(zip(nodes, values)):
        numerator = denominator = ONE
        for other_index, other in enumerate(nodes):
            if index != other_index:
                numerator *= point + other
                denominator *= node + other
        result += value * numerator / denominator
    return result


# Proof transport ------------------------------------------------------------


class BinaryReader:
    """Strict reader for bincode's fixed-width encoding used by the project."""

    def __init__(self, data: bytes):
        self.data = data
        self.offset = 0

    def take(self, length: int) -> bytes:
        end = self.offset + length
        require(end <= len(self.data), "truncated proof encoding")
        result = self.data[self.offset:end]
        self.offset = end
        return result

    def u64(self) -> int:
        return int.from_bytes(self.take(8), "little")

    def field(self) -> F128:
        return F128.from_bytes(self.take(16))

    def fields(self) -> list[F128]:
        length = self.u64()
        require(length <= self.remaining // 16, "invalid field-vector length")
        return [self.field() for _ in range(length)]

    @property
    def remaining(self) -> int:
        return len(self.data) - self.offset

    def finish(self) -> None:
        require(self.remaining == 0, "trailing proof encoding")


@dataclass(frozen=True)
class LevelOpening:
    opened_rows: tuple[tuple[F128, ...], ...]
    merkle_proof: tuple[bytes, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> "LevelOpening":
        row_count = reader.u64()
        require(row_count <= reader.remaining // 8, "invalid opened-row count")
        rows = tuple(tuple(reader.fields()) for _ in range(row_count))
        path_length = reader.u64()
        require(path_length <= reader.remaining // 32, "invalid Merkle proof length")
        return cls(rows, tuple(reader.take(32) for _ in range(path_length)))


@dataclass(frozen=True)
class LigeritoOpening:
    initial: LevelOpening
    levels: tuple[LevelOpening, ...]
    final: LevelOpening

    @classmethod
    def read(cls, reader: BinaryReader) -> "LigeritoOpening":
        initial = LevelOpening.read(reader)
        count = reader.u64()
        require(count <= 32, "too many Ligerito levels")
        levels = tuple(LevelOpening.read(reader) for _ in range(count))
        return cls(initial, levels, LevelOpening.read(reader))


@dataclass(frozen=True)
class Proof:
    stream: tuple[F128, ...]
    openings: tuple[LigeritoOpening, ...]

    @classmethod
    def from_bincode(cls, data: bytes) -> "Proof":
        reader = BinaryReader(data)
        stream = tuple(reader.fields())
        count = reader.u64()
        require(count <= 8, "too many PCS openings")
        openings = tuple(LigeritoOpening.read(reader) for _ in range(count))
        reader.finish()
        return cls(stream, openings)

    @classmethod
    def load(cls, path: str | Path) -> "Proof":
        return cls.from_bincode(Path(path).read_bytes())


# Fiat--Shamir ---------------------------------------------------------------


DS_SCALAR = F128(1)
DS_BYTE = F128(2)
DS_LEN = F128(3)
DS_SQUEEZE = F128(4)
DS_POW = F128(5)


def compress(left: Sequence[F128], right: Sequence[F128]) -> tuple[F128, F128]:
    require(len(left) == len(right) == 2, "compression operands must contain two fields")
    digest = blake3_hash(b"".join(x.to_bytes() for x in (*left, *right)))
    return F128.from_bytes(digest[:16]), F128.from_bytes(digest[16:])


class Sponge:
    def __init__(self, label: bytes, statement: Sequence[F128]):
        self.state = (ZERO, ZERO)
        self.absorb_bytes(b"leanvm-b/transcript/v1")
        self.absorb_bytes(label)
        for value in statement:
            self.observe(value)

    def observe(self, value: F128) -> None:
        self.state = compress(self.state, (value, DS_SCALAR))

    def absorb_bytes(self, data: bytes) -> None:
        self.state = compress(self.state, (F128(len(data)), DS_LEN))
        for offset in range(0, len(data), 16):
            block = F128.from_bytes(data[offset : offset + 16].ljust(16, b"\0"))
            self.state = compress(self.state, (block, DS_BYTE))

    def sample(self) -> F128:
        self.state = compress(self.state, (ZERO, DS_SQUEEZE))
        return self.state[0]

    def check_pow(self, nonce: int, bits: int) -> None:
        require(0 <= bits < 64, "invalid grinding width")
        base = compress(self.state, (ZERO, DS_POW))
        digest = compress(base, (F128(nonce), DS_POW))[0]
        valid = nonce == 0 if bits == 0 else digest.lo & ((1 << bits) - 1) == 0
        self.state = compress(self.state, (F128(nonce), DS_POW))
        require(valid, "invalid grinding nonce")


class Transcript:
    def __init__(self, proof: Proof, label: bytes, statement: Sequence[F128]):
        self.proof = proof
        self.sponge = Sponge(label, statement)
        self.stream_offset = 0
        self.opening_offset = 0

    def scalar(self) -> F128:
        require(self.stream_offset < len(self.proof.stream), "proof stream exhausted")
        value = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        self.sponge.observe(value)
        return value

    def scalars(self, count: int) -> list[F128]:
        return [self.scalar() for _ in range(count)]

    def sample(self) -> F128:
        return self.sponge.sample()

    def samples(self, count: int) -> list[F128]:
        return [self.sample() for _ in range(count)]

    def observe(self, value: F128) -> None:
        self.sponge.observe(value)

    def absorb_bytes(self, data: bytes) -> None:
        self.sponge.absorb_bytes(data)

    def grind(self, bits: int) -> None:
        require(self.stream_offset < len(self.proof.stream), "missing grinding nonce")
        encoded = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        require(encoded.hi == 0, "grinding nonce has a nonzero high limb")
        self.sponge.check_pow(encoded.lo, bits)

    def opening(self) -> LigeritoOpening:
        require(self.opening_offset < len(self.proof.openings), "PCS opening missing")
        result = self.proof.openings[self.opening_offset]
        self.opening_offset += 1
        return result

    def finish(self) -> None:
        require(self.stream_offset == len(self.proof.stream), "proof stream not fully consumed")
        require(self.opening_offset == len(self.proof.openings), "PCS openings not fully consumed")


# GKR product triple ---------------------------------------------------------


@dataclass(frozen=True)
class ProductTriple:
    roots: tuple[F128, F128, F128]
    point: tuple[F128, ...]
    values: tuple[F128, F128, F128]


def quartic_eval_from_eq(
    claim: F128,
    equality_point: F128,
    difference: F128,
    c2: F128,
    c3: F128,
    c4: F128,
    challenge: F128,
) -> F128:
    c0 = claim + equality_point * difference
    c1 = difference + c2 + c3 + c4
    return c0 + challenge * (c1 + challenge * (c2 + challenge * (c3 + challenge * c4)))


def verify_product_triple(depth: int, transcript: Transcript) -> ProductTriple:
    root_values = transcript.scalars(3)
    roots = (root_values[0], root_values[1], root_values[2])
    combine = transcript.sample()
    point: list[F128] = []
    values = list(roots)

    layer = depth
    while layer > 0:
        round_count = depth - layer
        claim = values[0] + combine * (values[1] + combine * values[2])
        if layer % 2 == 1:
            require(round_count == 0, "binary GKR layer is not root-most")
            tails = [transcript.scalars(2) for _ in range(3)]
            products = [tail[0] * tail[1] for tail in tails]
            expected = products[0] + combine * (products[1] + combine * products[2])
            require(claim == expected, f"GKR layer {layer}: binary tail mismatch")
            challenge = transcript.sample()
            values = [interpolate(tail[0], tail[1], challenge) for tail in tails]
            combine = transcript.sample()
            point = [challenge]
            layer -= 1
            continue

        round_point: list[F128] = []
        for prior in point[:round_count]:
            message = transcript.scalars(4)
            challenge = transcript.sample()
            round_point.append(challenge)
            claim = quartic_eval_from_eq(claim, prior, *message, challenge)

        tails = [transcript.scalars(4) for _ in range(3)]
        products = [tail[0] * tail[1] * tail[2] * tail[3] for tail in tails]
        expected = products[0] + combine * (products[1] + combine * products[2])
        require(claim == expected, f"GKR layer {layer}: radix-four tail mismatch")
        low_challenge = transcript.sample()
        high_challenge = transcript.sample()
        values = [
            interpolate(
                interpolate(tail[0], tail[1], low_challenge),
                interpolate(tail[2], tail[3], low_challenge),
                high_challenge,
            )
            for tail in tails
        ]
        combine = transcript.sample()
        point = [low_challenge, high_challenge, *round_point]
        layer -= 2

    return ProductTriple(roots, tuple(point), (values[0], values[1], values[2]))


# Bus balance and decomposition ---------------------------------------------


@dataclass(frozen=True)
class Coordinate:
    """One coordinate of a bus tuple.

    Exactly one payload is set. ``column`` and ``generator_column`` refer to
    committed global columns; ``public`` is a dense public multilinear table.
    """

    constant: F128 | None = None
    column: int | None = None
    generator_column: int | None = None
    index: bool = False
    public: tuple[F128, ...] | None = None

    def __post_init__(self) -> None:
        choices = (
            self.constant is not None,
            self.column is not None,
            self.generator_column is not None,
            self.index,
            self.public is not None,
        )
        require(sum(choices) == 1, "a bus coordinate must have exactly one source")


@dataclass(frozen=True)
class BusBlock:
    log_rows: int
    coordinates: tuple[Coordinate, ...]
    real_rows: int
    owner: tuple[int, int] | None = None

    def __post_init__(self) -> None:
        require(0 <= self.real_rows <= 1 << self.log_rows, "invalid bus block row count")


@dataclass(frozen=True)
class BusLayout:
    depth: int
    offsets: tuple[int, ...]


def bus_layout(blocks: Sequence[BusBlock]) -> BusLayout:
    order = sorted(range(len(blocks)), key=lambda i: (-blocks[i].log_rows, i))
    offsets = [0] * len(blocks)
    offset = 0
    for index in order:
        offsets[index] = offset
        offset += 1 << blocks[index].log_rows
    depth = max(0, (max(offset, 1) - 1).bit_length())
    return BusLayout(depth, tuple(offsets))


def index_mle(point: Sequence[F128]) -> F128:
    """MLE of ``[1, g, g^2, ...]`` at an LSB-first point."""
    result = ONE
    generator_power = GEN
    for challenge in point:
        result *= ONE + challenge * (ONE + generator_power)
        generator_power *= generator_power
    return result


@dataclass(frozen=True)
class ColumnClaim:
    column: int
    point: tuple[F128, ...]
    value: F128


@dataclass(frozen=True)
class BytecodeClaim:
    point: tuple[F128, ...]
    value: F128


@dataclass
class BusForm:
    coefficients: list[F128]
    constant: F128 = ZERO

    def evaluate(self, values: Sequence[F128]) -> F128:
        require(len(values) == len(self.coefficients), "bus form width mismatch")
        return sum(
            (coefficient * value for coefficient, value in zip(self.coefficients, values)),
            self.constant,
        )


def _decompose_bus_side(
    blocks: Sequence[BusBlock],
    layout: BusLayout,
    point: Sequence[F128],
    alpha: F128,
    gamma: F128,
    forms: Sequence[BusForm],
    claims: list[ColumnClaim],
    transcript: Transcript,
) -> F128:
    require(len(point) == layout.depth, "bus point dimension mismatch")

    def committed_value(column: int, low_point: tuple[F128, ...]) -> F128:
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
        selector = layout.offsets[block_index] >> block.log_rows
        selector_bits = tuple(
            F128((selector >> bit) & 1)
            for bit in range(layout.depth - block.log_rows)
        )
        selector_weight = eq_eval(selector_bits, high)
        selector_sum += selector_weight

        if block.owner is not None:
            table, base = block.owner
            form = forms[table]
            form.constant += selector_weight * gamma
            coefficient = ONE
            for coordinate in block.coordinates:
                if coordinate.constant is not None:
                    form.constant += selector_weight * coefficient * coordinate.constant
                elif coordinate.column is not None:
                    form.coefficients[coordinate.column - base] += selector_weight * coefficient
                elif coordinate.generator_column is not None:
                    form.coefficients[coordinate.generator_column - base] += (
                        selector_weight * coefficient * GEN
                    )
                else:
                    raise VerificationError("table bus block has a virtual coordinate")
                coefficient *= alpha
            continue

        fingerprint = ZERO
        coefficient = ONE
        for coordinate in block.coordinates:
            if coordinate.constant is not None:
                value = coordinate.constant
            elif coordinate.column is not None:
                value = committed_value(coordinate.column, low)
            elif coordinate.generator_column is not None:
                value = GEN * committed_value(coordinate.generator_column, low)
            elif coordinate.index:
                value = index_mle(low)
            else:
                public = coordinate.public
                if public is None:
                    raise VerificationError("bus coordinate has no value source")
                value = mle_eval(public, low)
            fingerprint += coefficient * value
            coefficient *= alpha
        result += selector_weight * (gamma + fingerprint)

    # Unoccupied rows of the packed leaf cube contain the product identity.
    return result + ONE + selector_sum


def _padding_fingerprint(block: BusBlock, padding: Sequence[F128], alpha: F128) -> F128:
    result = ZERO
    coefficient = ONE
    for coordinate in block.coordinates:
        if coordinate.constant is not None:
            value = coordinate.constant
        elif coordinate.column is not None:
            value = padding[coordinate.column]
        elif coordinate.generator_column is not None:
            value = GEN * padding[coordinate.generator_column]
        else:
            value = ZERO
        result += coefficient * value
        coefficient *= alpha
    return result


def _padding_surplus(
    blocks: Sequence[BusBlock],
    padding: Sequence[F128],
    alpha: F128,
    gamma: F128,
) -> F128:
    result = ONE
    for block in blocks:
        surplus_rows = (1 << block.log_rows) - block.real_rows
        if surplus_rows:
            result *= (gamma + _padding_fingerprint(block, padding, alpha)) ** surplus_rows
    return result


def _public_evaluations(
    blocks: Sequence[BusBlock], point: Sequence[F128]
) -> tuple[int, list[F128]]:
    log_rows = 0
    values: list[F128] = []
    for block in blocks:
        for coordinate in block.coordinates:
            if coordinate.public is not None:
                log_rows = block.log_rows
                values.append(mle_eval(coordinate.public, point[: block.log_rows]))
    return log_rows, values


def _stack_public_evaluations(values: Sequence[F128], selector_point: Sequence[F128]) -> F128:
    require(len(values) <= 1 << len(selector_point), "too many public columns")
    result = ZERO
    for column, value in enumerate(values):
        weight = ONE
        for bit, challenge in enumerate(selector_point):
            weight *= challenge if column >> bit & 1 else ONE + challenge
        result += weight * value
    return result


@dataclass(frozen=True)
class BusResult:
    claims: tuple[ColumnClaim, ...]
    bytecode_claim: BytecodeClaim
    count_root: F128
    point: tuple[F128, ...]
    forms: tuple[tuple[BusForm, ...], ...]
    totals: tuple[F128, F128, F128]


def verify_bus_balance(
    push: Sequence[BusBlock],
    pull: Sequence[BusBlock],
    count: Sequence[BusBlock],
    padding: Sequence[F128],
    transcript: Transcript,
) -> BusResult:
    push_layout = bus_layout(push)
    pull_layout = bus_layout(pull)
    count_layout = bus_layout(count)
    require(push_layout.depth == pull_layout.depth, "push/pull bus depths differ")
    require(count_layout.depth <= push_layout.depth, "count bus is deeper than push bus")

    grinding_bits = max(0, 120 + push_layout.depth + 1 - 128)
    transcript.grind(grinding_bits)
    alpha = transcript.sample()
    gamma = transcript.sample()
    padded_count_layout = BusLayout(push_layout.depth, count_layout.offsets)
    product = verify_product_triple(push_layout.depth, transcript)
    push_root, pull_root, count_root = product.roots
    require(count_root != ZERO, "a bus read count is zero")

    push_surplus = _padding_surplus(push, padding, alpha, gamma)
    pull_surplus = _padding_surplus(pull, padding, alpha, gamma)
    require(push_root * pull_surplus == pull_root * push_surplus, "bus is unbalanced")

    claims: list[ColumnClaim] = []
    forms = tuple(
        tuple(BusForm([ZERO] * width) for width in WIDTHS)
        for _ in range(3)
    )
    sides = (
        (push, push_layout, alpha, gamma),
        (pull, pull_layout, alpha, gamma),
        (count, padded_count_layout, ONE, ZERO),
    )
    totals = []
    for side, (blocks, side_layout, side_alpha, side_gamma) in enumerate(sides):
        framework = _decompose_bus_side(
            blocks,
            side_layout,
            product.point,
            side_alpha,
            side_gamma,
            forms[side],
            claims,
            transcript,
        )
        totals.append(framework + product.values[side])

    public_log_rows, public_values = _public_evaluations(push, product.point)
    for value in public_values:
        transcript.observe(value)
    selector_point = transcript.samples(3)
    bytecode_claim = BytecodeClaim(
        tuple(product.point[:public_log_rows]) + tuple(selector_point),
        _stack_public_evaluations(public_values, selector_point),
    )
    return BusResult(
        tuple(claims),
        bytecode_claim,
        count_root,
        product.point,
        forms,
        (totals[0], totals[1], totals[2]),
    )


# Batched AIR zerocheck ------------------------------------------------------


@dataclass(frozen=True)
class Air:
    log_height: int
    column_count: int
    constraint_count: int
    evaluate: Callable[[Sequence[F128], Sequence[F128]], F128]


@dataclass(frozen=True)
class AirClaim:
    point: tuple[F128, ...]
    evaluations: tuple[F128, ...]


def powers(base: F128, count: int) -> list[F128]:
    result, current = [], ONE
    for _ in range(count):
        result.append(current)
        current *= base
    return result


def verify_constraints(
    airs: Sequence[Air],
    eta: F128,
    equality_point: Sequence[F128],
    target: F128,
    transcript: Transcript,
) -> list[AirClaim]:
    depth = max((air.log_height for air in airs), default=0)
    offsets, total = [], 0
    for air in airs:
        offsets.append(total)
        total += air.constraint_count
    eta_powers = powers(eta, total)
    require(len(equality_point) >= depth, "AIR equality point is too short")

    claim = target
    weights = [ONE] * len(airs)
    point = [ZERO] * depth
    for round_index in range(depth):
        variable = depth - 1 - round_index
        message = transcript.scalars(4)
        require(
            message[0] + message[1] == claim,
            f"AIR round {round_index}: inconsistent sumcheck",
        )
        challenge = transcript.sample()
        point[variable] = challenge
        equality = ONE + equality_point[variable] + challenge
        claim = lagrange_eval(QUAD_NODES, message, challenge)
        for table_index, air in enumerate(airs):
            weights[table_index] *= equality if air.log_height > variable else challenge

    final = ZERO
    claims: list[AirClaim] = []
    for table_index, air in enumerate(airs):
        evaluations = tuple(transcript.scalars(air.column_count))
        table_powers = eta_powers[
            offsets[table_index] : offsets[table_index] + air.constraint_count
        ]
        final += weights[table_index] * air.evaluate(table_powers, evaluations)
        claims.append(AirClaim(tuple(point[: air.log_height]), evaluations))
    require(final == claim, "AIR terminal mismatch")
    return claims

# VM statement, layout, and AIR -----------------------------------------------

FAMILY_DIGEST = bytes.fromhex("afed7472c6f771a857599272ff33a4da86b21f2600f057fa0da797d15863eb58")
BASES = (4, 19, 34, 41, 58, 77)
WIDTHS = (15, 15, 7, 17, 19, 32)
CONSTRAINT_COUNTS = (4, 4, 1, 4, 7, 6)
COUNT_COLUMNS = ((11, 12, 13, 14), (11, 12, 13, 14), (5, 6),
                 (13, 14, 15, 16), (13, 14, 15, 16),
                 (23, 24, 25, 26, 27, 28, 29, 30, 31))
BLAKE3_VALUES = (14, 15, 16, 17, 18, 19, 20, 21, 22)
BLAKE3_SLOTS = (5, 6, 7, 8, 2, 3, 0, 1, 9)
BLAKE3_SLOT_BY_VALUE: dict[int, int] = dict(zip(BLAKE3_VALUES, BLAKE3_SLOTS))
VM_IV = (
    F128.new(0xBB67AE856A09E667, 0xA54FF53A3C6EF372),
    F128.new(0x9B05688C510E527F, 0x5BE0CD191F83D9AB),
)


def _field(value: Any) -> F128:
    if isinstance(value, F128):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        integer = value
    elif isinstance(value, str):
        try:
            integer = int(value, 0)
        except ValueError as exc:
            raise VerificationError(f"invalid field element: {value!r}") from exc
    else:
        integer = None
    if integer is not None:
        require(0 <= integer < 1 << 128, f"field element is out of range: {value!r}")
        return F128(integer)
    if isinstance(value, (list, tuple)) and len(value) == 2:
        try:
            low, high = (int(limb) for limb in value)
        except (TypeError, ValueError) as exc:
            raise VerificationError(f"invalid field limbs: {value!r}") from exc
        require(
            0 <= low < 1 << 64 and 0 <= high < 1 << 64,
            f"field limb is out of range: {value!r}",
        )
        return F128.new(low, high)
    raise VerificationError(f"invalid field element: {value!r}")


def parse_field(value: Any) -> F128:
    """Parse the field-element forms accepted by the statement JSON schema."""
    return _field(value)


def _u32(value: Any, name: str) -> int:
    require(
        isinstance(value, int) and not isinstance(value, bool) and 0 <= value < 1 << 32,
        f"{name} must be a 32-bit unsigned integer",
    )
    return value


@dataclass(frozen=True)
class Operation:
    name: str
    values: dict[str, Any]

    @classmethod
    def parse(cls, data: dict[str, Any]) -> "Operation":
        require(isinstance(data, dict), "each program operation must be an object")
        name = str(data.get("op", "")).lower()
        require(name in {"xor", "mul", "set", "deref", "jump", "blake3"},
                f"unknown operation {name!r}")
        if name in {"xor", "mul"}:
            for key in ("a", "b", "c"):
                _u32(data[key], f"{name}.{key}")
        elif name == "set":
            _u32(data["o"], "set.o")
            _field(data["k"])
        elif name == "deref":
            for key in ("alpha", "beta", "gamma"):
                _u32(data[key], f"deref.{key}")
            require(str(data["mode"]).lower() in {"cell", "pc", "fp"},
                    "deref.mode must be cell, pc, or fp")
        elif name == "jump":
            for key in ("oc", "od", "of"):
                _u32(data[key], f"jump.{key}")
        elif name == "blake3":
            inputs = data["ins"]
            require(isinstance(inputs, (list, tuple)) and len(inputs) == 4,
                    "blake3.ins must contain four addresses")
            for index, value in enumerate(inputs):
                _u32(value, f"blake3.ins[{index}]")
            _u32(data["cv"], "blake3.cv")
            _u32(data["out"], "blake3.out")
            _field(data["metadata"])
        return cls(name, dict(data))


@dataclass(frozen=True)
class Program:
    operations: tuple[Operation, ...]

    @classmethod
    def parse(cls, data: dict[str, Any]) -> "Program":
        require(isinstance(data, dict), "the public statement must be an object")
        encoded = data.get("program")
        if not isinstance(encoded, list):
            raise VerificationError("program must be an array")
        operations = tuple(Operation.parse(item) for item in encoded)
        require(bool(operations) and not len(operations) & (len(operations) - 1),
                "program length must be a nonzero power of two")
        return cls(operations)

    def digest(self) -> tuple[F128, F128]:
        words = [F128.new(len(self.operations), 1)]
        tags = {"xor": 0, "mul": 1, "set": 2, "jump": 6, "blake3": 7}
        for operation in self.operations:
            d = operation.values
            name = operation.name
            k = x = y = ZERO
            if name in {"xor", "mul"}:
                a, b, c = int(d["a"]), int(d["b"]), int(d["c"])
                tag = tags[name]
            elif name == "set":
                a, b, c, tag, k = int(d["o"]), 0, 0, 2, _field(d["k"])
            elif name == "deref":
                a, b, c = int(d["alpha"]), int(d["beta"]), int(d["gamma"])
                modes = {"cell": 3, "pc": 4, "fp": 5}
                tag = modes[str(d["mode"]).lower()]
            elif name == "jump":
                a, b, c, tag = int(d["oc"]), int(d["od"]), int(d["of"]), 6
            else:
                inputs = [int(v) for v in d["ins"]]
                a, b, c, tag = inputs[0], inputs[1], inputs[2], 7
                k = _field(d["metadata"])
                x = F128.new(inputs[3], int(d["cv"]))
                y = F128.new(int(d["out"]), 0)
            words.extend((F128.new(a | b << 32, c | tag << 32), k, x, y))
        digest = blake3_hash(b"".join(word.to_bytes() for word in words))
        return F128.from_bytes(digest[:16]), F128.from_bytes(digest[16:])

    def transcript_statement(self, public_input: Sequence[F128]) -> tuple[F128, ...]:
        program_digest = self.digest()
        seed = blake3_hash(b"leanvm-b-fs-seed-v1" + FAMILY_DIGEST
                           + program_digest[0].to_bytes() + program_digest[1].to_bytes())
        return (F128.from_bytes(seed[:16]), F128.from_bytes(seed[16:]), *public_input)


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
    padding: tuple[F128, ...]
    placements: tuple[Placement, ...]
    stack_log: int
    table_logs: tuple[int, ...]


def _ceil_log(value: int) -> int:
    return max(0, (value - 1).bit_length())


def _gpow(index: int) -> F128:
    return GEN ** index


def _const(value: F128 | int) -> Coordinate:
    return Coordinate(constant=_field(value))


def _col(index: int) -> Coordinate:
    return Coordinate(column=index)


def _gcol(index: int) -> Coordinate:
    return Coordinate(generator_column=index)


def _public(values: Sequence[F128]) -> Coordinate:
    return Coordinate(public=tuple(values))


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Coordinate, ...]] = []
        self.pull: list[tuple[Coordinate, ...]] = []

    def pair(self, push: Sequence[Coordinate], pull: Sequence[Coordinate]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state_step(self, pc: int, fp: int) -> None:
        self.pair((_const(ONE), _gcol(pc), _col(fp)), (_const(ONE), _col(pc), _col(fp)))

    def state_jump(self, pc: int, fp: int, npc: int, nfp: int) -> None:
        self.pair((_const(ONE), _col(npc), _col(nfp)), (_const(ONE), _col(pc), _col(fp)))

    def bytecode(self, pc: int, count: int, opcode: int, operands: Sequence[Coordinate]) -> None:
        prefix_push = (_const(GEN * GEN), _col(pc), _gcol(count), _const(_gpow(opcode)))
        prefix_pull = (_const(GEN * GEN), _col(pc), _col(count), _const(_gpow(opcode)))
        self.pair((*prefix_push, *operands), (*prefix_pull, *operands))

    def memory(self, address: int, count: int, value: int, successor: bool = False) -> None:
        addr = _gcol(address) if successor else _col(address)
        self.pair((_const(GEN), addr, _gcol(count), _col(value)),
                  (_const(GEN), addr, _col(count), _col(value)))


def _table_flushes(table: int) -> Flushes:
    f = Flushes()
    if table in (0, 1):
        f.state_step(0, 1)
        f.bytecode(0, 14, table, (_col(2), _col(3), _col(4), _const(ZERO), _const(ZERO)))
        f.memory(5, 11, 8)
        f.memory(6, 12, 9)
        f.memory(7, 13, 10)
    elif table == 2:
        f.state_step(0, 1)
        f.bytecode(0, 6, 2, (_col(2), _col(3), _const(ZERO), _const(ZERO), _const(ZERO)))
        f.memory(4, 5, 3)
    elif table == 3:
        f.state_step(0, 1)
        f.bytecode(0, 16, 3, (_col(2), _col(3), _col(4), _col(5), _col(6)))
        f.memory(7, 13, 10)
        f.memory(8, 14, 11)
        f.memory(9, 15, 12)
    elif table == 4:
        f.state_jump(0, 1, 2, 3)
        f.bytecode(0, 16, 4, (_col(4), _col(5), _col(6), _const(ZERO), _const(ZERO)))
        f.memory(7, 13, 10)
        f.memory(8, 14, 11)
        f.memory(9, 15, 12)
    else:
        f.state_step(0, 1)
        f.bytecode(0, 31, 5, tuple(_col(i) for i in (2, 3, 4, 5, 6, 7, 22)))
        for address, count, value, successor in (
            (8,23,14,False), (9,24,15,False), (10,25,16,False), (11,26,17,False),
            (12,27,20,False), (12,28,21,True), (13,29,18,False), (13,30,19,True),
        ):
            f.memory(address, count, value, successor)
    return f


def _offset_coordinate(coordinate: Coordinate, base: int) -> Coordinate:
    if coordinate.column is not None:
        return _col(base + coordinate.column)
    if coordinate.generator_column is not None:
        return _gcol(base + coordinate.generator_column)
    return coordinate


def _program_columns(program: Program) -> tuple[tuple[F128, ...], ...]:
    columns = [[] for _ in range(8)]
    opcodes = {"xor": 0, "mul": 1, "set": 2, "deref": 3, "jump": 4, "blake3": 5}
    for operation in program.operations:
        d, name = operation.values, operation.name
        operands = [ZERO] * 7
        if name in {"xor", "mul"}:
            operands[:3] = [_gpow(int(d[k])) for k in ("a", "b", "c")]
        elif name == "set":
            operands[:2] = [_gpow(int(d["o"])), _field(d["k"])]
        elif name == "deref":
            operands[:3] = [_gpow(int(d[k])) for k in ("alpha", "beta", "gamma")]
            mode = str(d["mode"]).lower()
            operands[3:5] = [ONE if mode == "pc" else ZERO, ONE if mode == "fp" else ZERO]
        elif name == "jump":
            operands[:3] = [_gpow(int(d[k])) for k in ("oc", "od", "of")]
        else:
            inputs = [int(v) for v in d["ins"]]
            operands = [*(_gpow(v) for v in inputs), _gpow(int(d["cv"])),
                        _gpow(int(d["out"])), _field(d["metadata"])]
        row = [_gpow(opcodes[name]), *operands]
        for column, value in zip(columns, row):
            column.append(value)
    return tuple(tuple(column) for column in columns)


def build_layout(program: Program, log_memory: int, row_counts: Sequence[int]) -> Layout:
    require(
        16 <= log_memory <= 32
        and len(row_counts) == 6
        and all(0 <= count < 1 << 32 for count in row_counts),
        "invalid announced table sizes",
    )
    table_logs = [_ceil_log(max(1, count)) for count in row_counts]
    table_logs[5] = max(3, table_logs[5])
    bytecode_log = len(program.operations).bit_length() - 1
    public_columns = _program_columns(program)

    push = [
        BusBlock(0, (_const(ONE), _const(ONE), _const(ONE)), 1),
        BusBlock(
            log_memory,
            (_const(GEN), Coordinate(index=True), _const(ONE), _col(0)),
            1 << log_memory,
        ),
        BusBlock(
            bytecode_log,
            (
                _const(GEN * GEN),
                Coordinate(index=True),
                _const(ONE),
                *(_public(column) for column in public_columns),
            ),
            len(program.operations),
        ),
    ]
    pull = [
        BusBlock(0, (_const(ONE), _const(_gpow(len(program.operations) - 1)), _const(ONE)), 1),
        BusBlock(
            log_memory,
            (_const(GEN), Coordinate(index=True), _col(1), _col(0)),
            1 << log_memory,
        ),
        BusBlock(
            bytecode_log,
            (
                _const(GEN * GEN),
                Coordinate(index=True),
                _col(2),
                *(_public(column) for column in public_columns),
            ),
            len(program.operations),
        ),
    ]
    count: list[BusBlock] = []
    padding = [ZERO] * (4 + sum(WIDTHS))
    for table, (base, height, real) in enumerate(zip(BASES, table_logs, row_counts)):
        flushes = _table_flushes(table)
        for coordinates in flushes.push:
            shifted = tuple(_offset_coordinate(c, base) for c in coordinates)
            push.append(BusBlock(height, shifted, real, (table, base)))
        for coordinates in flushes.pull:
            shifted = tuple(_offset_coordinate(c, base) for c in coordinates)
            pull.append(BusBlock(height, shifted, real, (table, base)))
        for local in COUNT_COLUMNS[table]:
            count.append(BusBlock(height, (_col(base + local),), real, (table, base)))
            padding[base + local] = ONE

    zero_digest = blake3_hash(bytes(64))
    b3 = BASES[5]
    padding[b3 + 18] = F128.from_bytes(zero_digest[:16])
    padding[b3 + 19] = F128.from_bytes(zero_digest[16:])
    padding[b3 + 20], padding[b3 + 21] = VM_IV
    padding[b3 + 22] = F128.new(0, 64 | 11 << 32)

    kappas: list[int | None] = [0] * (4 + sum(WIDTHS))
    kappas[0] = kappas[1] = log_memory
    kappas[2] = bytecode_log
    kappas[3] = table_logs[5] + 7
    for table, (base, width) in enumerate(zip(BASES, WIDTHS)):
        kappas[base : base + width] = [table_logs[table]] * width
    for local in BLAKE3_VALUES:
        kappas[b3 + local] = None
    order = sorted(
        (
            (index, variables)
            for index, variables in enumerate(kappas)
            if variables is not None
        ),
        key=lambda item: (-item[1], item[0]),
    )
    placements = [Placement(-1, 0) for _ in kappas]
    offset = 0
    for index, variables in order:
        placements[index] = Placement(variables, offset)
        offset += 1 << variables
    stack_log = max(15, _ceil_log(max(1, offset)))
    return Layout(tuple(push), tuple(pull), tuple(count), tuple(padding), tuple(placements),
                  stack_log, tuple(table_logs))


def _air_evaluator(
    table: int,
    forms: Sequence[BusForm],
    form_powers: Sequence[F128],
) -> Callable[[Sequence[F128], Sequence[F128]], F128]:
    def evaluate(weights: Sequence[F128], columns: Sequence[F128]) -> F128:
        def value(column: int) -> F128:
            return columns[column]

        if table in (0, 1):
            operation = (
                value(8) + value(9) if table == 0 else value(8) * value(9)
            )
            terms = (
                value(5) + value(1) * value(2),
                value(6) + value(1) * value(3),
                value(7) + value(1) * value(4),
                value(10) + operation,
            )
        elif table == 2:
            terms = (value(4) + value(1) * value(2),)
        elif table == 3:
            source = (
                (ONE + value(5) + value(6)) * value(12)
                + value(5) * GEN * GEN * value(0)
                + value(6) * value(1)
            )
            terms = (
                value(7) + value(1) * value(2),
                value(8) + value(10) * value(3),
                value(9) + value(1) * value(4),
                value(11) + source,
            )
        elif table == 4:
            flag, condition = value(18), value(10)
            terms = (
                value(7) + value(1) * value(4),
                value(8) + value(1) * value(5),
                value(9) + value(1) * value(6),
                flag + condition * value(17),
                condition * (flag + ONE),
                value(2) + flag * value(11) + (flag + ONE) * GEN * value(0),
                value(3) + flag * value(12) + (flag + ONE) * value(1),
            )
        else:
            terms = tuple(
                value(address) + value(1) * value(operand)
                for address, operand in zip((8, 9, 10, 11, 12, 13), (2, 3, 4, 5, 6, 7))
            )

        require(len(weights) == len(terms), "AIR constraint weight mismatch")
        identities = sum((weight * term for weight, term in zip(weights, terms)), ZERO)
        buses = sum(
            (weight * form.evaluate(columns) for weight, form in zip(form_powers, forms)),
            ZERO,
        )
        return identities + buses

    return evaluate


def build_airs(
    layout: Layout,
    bus_forms: Sequence[Sequence[BusForm]],
    form_powers: Sequence[F128],
) -> list[Air]:
    return [
        Air(
            height,
            WIDTHS[table],
            count,
            _air_evaluator(table, [side[table] for side in bus_forms], form_powers),
        )
        for table, (height, count) in enumerate(
            zip(layout.table_logs, CONSTRAINT_COUNTS)
        )
    ]


def constraint_claims(layout: Layout, claims: Sequence[AirClaim]) -> list[ColumnClaim]:
    result: list[ColumnClaim] = []
    for table, claim in enumerate(claims):
        for local, value in enumerate(claim.evaluations):
            result.append(ColumnClaim(BASES[table] + local, claim.point, value))
    return result


def virtual_slot(column: int) -> int | None:
    return BLAKE3_SLOT_BY_VALUE.get(column - BASES[5])

# Ligerito opening ------------------------------------------------------------

@dataclass(frozen=True)
class LigeritoConfig:
    rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]
    query_grinding: tuple[int, ...]
    fold_grinding: tuple[int, ...]


def _per_query_bits(rate: int, message_log: int) -> float:
    rho = 2.0 ** -rate
    delta = 1.0 - rho
    codeword_length = 2.0 ** (message_log + rate)
    radius = delta / 2.0 - 3.0 / (delta * codeword_length)
    return log2(1.0 / (1.0 - radius))


def derive_config(log_n: int) -> LigeritoConfig:
    """Reproduce ``LigeritoSecurityConfig::derive_config(log_n + 7)``."""
    require(log_n > 6, "Ligerito input is too small")
    message_logs = [log_n - 6]
    folds = [6]
    rates = [1]

    # The feasibility pass in Rust uses the asymptotic UDR query bound.
    def feasible_queries(rate: int) -> int:
        rho = 2.0 ** -rate
        bits = log2(1.0 / (1.0 - (1.0 - rho) / 2.0))
        return ceil(107.0 / bits)

    require(1 << (message_logs[0] + rates[0]) >= feasible_queries(1),
           "Ligerito level zero cannot hold its query set")
    remaining = message_logs[0]
    while remaining > 5:
        fold = min(3, remaining)
        next_message_log = remaining - fold
        rate = rates[-1] + 1
        while 1 << (next_message_log + rate) < feasible_queries(rate):
            rate += 1
            require(rate <= 20, "no feasible Ligerito rate")
        folds.append(fold)
        message_logs.append(next_message_log)
        rates.append(rate)
        remaining = next_message_log

    require(len(folds) >= 2, "Ligerito requires at least two levels")
    queries = tuple(ceil(102.0 / _per_query_bits(r, n)) for r, n in zip(rates, message_logs))
    fold_grinding = []
    for rate, n in zip(rates, message_logs):
        rho = 2.0 ** -rate
        delta = 1.0 - rho
        codeword_length = 2.0 ** (n + rate)
        radius = delta / 2.0 - 3.0 / (delta * codeword_length)
        exceptional_log = log2(radius * codeword_length + 1.0)
        fold_grinding.append(max(0, ceil(120.0 - (128.0 - exceptional_log))))
    return LigeritoConfig(tuple(rates), tuple(folds), queries,
                          (18,) * len(folds), tuple(fold_grinding))


def _hash_pair(left: bytes, right: bytes) -> bytes:
    return blake3_hash(left + right)


def _row_hash(row: Sequence[F128]) -> bytes:
    return blake3_hash(b"".join(value.to_bytes() for value in row))


def authenticate_rows(
    root: bytes,
    leaf_count: int,
    queries: Sequence[int],
    rows: Sequence[Sequence[F128]],
    row_width: int,
    octopus: Sequence[bytes],
) -> list[Sequence[F128]]:
    """Authenticate a compressed multiproof and restore transcript row order."""
    require(leaf_count > 0 and leaf_count & (leaf_count - 1) == 0,
           "invalid Merkle leaf count")
    unique = sorted(set(queries))
    require(len(unique) == len(rows),
           f"opened-row count {len(rows)} does not match {len(unique)} distinct queries")
    require(all(0 <= q < leaf_count for q in unique), "Merkle query is out of range")
    require(all(len(row) == row_width for row in rows), "opened row has the wrong width")

    nodes = [(index, _row_hash(row)) for index, row in zip(unique, rows)]
    supplied = iter(octopus)
    for _ in range(leaf_count.bit_length() - 1):
        parents: list[tuple[int, bytes]] = []
        cursor = 0
        while cursor < len(nodes):
            index, value = nodes[cursor]
            paired = (
                index & 1 == 0
                and cursor + 1 < len(nodes)
                and nodes[cursor + 1][0] == index + 1
            )
            if paired:
                left, right = value, nodes[cursor + 1][1]
                cursor += 2
            else:
                sibling = next(supplied, None)
                if sibling is None:
                    raise VerificationError("truncated Merkle multiproof")
                left, right = (value, sibling) if index & 1 == 0 else (sibling, value)
                cursor += 1
            parents.append((index >> 1, _hash_pair(left, right)))
        nodes = parents
    require(len(nodes) == 1 and nodes[0] == (0, root), "Merkle root mismatch")
    require(next(supplied, None) is None, "Merkle multiproof has trailing nodes")

    by_query = dict(zip(unique, rows))
    return [by_query[q] for q in queries]


def sample_queries(sponge: Sponge, block_length: int, count: int) -> list[int]:
    depth = block_length.bit_length() - 1
    require(block_length == 1 << depth and depth > 0, "invalid query domain")
    per_word = 128 // depth
    result: list[int] = []
    while len(result) < count:
        bits = int(sponge.sample())
        for chunk in range(min(per_word, count - len(result))):
            result.append((bits >> (chunk * depth)) & (block_length - 1))
    return result


@dataclass(frozen=True)
class QuadraticMessage:
    constant: F128
    linear: F128
    quadratic: F128

    @classmethod
    def read(cls, transcript: Transcript, target: F128) -> "QuadraticMessage":
        constant, quadratic = transcript.scalars(2)
        return cls(constant, target + quadratic, quadratic)

    def evaluate(self, point: F128) -> F128:
        return self.constant + point * self.linear + point * point * self.quadratic

    def add_scaled(self, other: "QuadraticMessage", scale: F128) -> "QuadraticMessage":
        return QuadraticMessage(
            self.constant + scale * other.constant,
            self.linear + scale * other.linear,
            self.quadratic + scale * other.quadratic,
        )


def _enforced_sum(
    rows: Sequence[Sequence[F128]],
    folds: Sequence[F128],
    alpha: Sequence[F128],
) -> F128:
    lane_weights = build_eq(folds)
    query_weights = build_eq(alpha)[: len(rows)]
    total = ZERO
    for query_weight, row in zip(query_weights, rows):
        require(len(row) == len(lane_weights), "Ligerito row/fold width mismatch")
        total += query_weight * sum((x * y for x, y in zip(row, lane_weights)), ZERO)
    return total


def _subspace_roots(log_n: int) -> list[F128]:
    roots = [ZERO] * (log_n + 1)
    roots[0] = ONE
    layer = [F128(1 << i) for i in range(1, log_n + 1)]
    for level in range(log_n):
        for index in range(log_n - level):
            value = layer[index] * layer[index] + roots[level] * layer[index]
            if index == 0:
                roots[level + 1] = value
            else:
                layer[index - 1] = value
    return roots


def _induced_residual(
    message_log: int,
    queries: Sequence[int],
    alpha: Sequence[F128],
    prefix: Sequence[F128],
    residual_log: int,
) -> list[F128]:
    require(len(prefix) + residual_log == message_log, "bad induced-basis dimensions")
    roots = _subspace_roots(message_log)
    inverses = [value.inv() if value else ZERO for value in roots]
    query_weights = build_eq(alpha)[: len(queries)]
    prepared: list[tuple[F128, tuple[F128, ...]]] = []
    for query in queries:
        normalized: list[F128] = []
        current = F128(query)
        for coordinate in range(message_log):
            normalized.append(current * inverses[coordinate])
            current = current * current + roots[coordinate] * current
        fixed = ONE
        for challenge, basis_value in zip(prefix, normalized):
            fixed *= ONE + challenge * (ONE + basis_value)
        prepared.append((fixed, tuple(normalized[len(prefix) :])))

    result: list[F128] = []
    for vertex in range(1 << residual_log):
        value = ZERO
        for query_weight, (fixed, tail) in zip(query_weights, prepared):
            suffix = ONE
            for bit, basis_value in enumerate(tail):
                if vertex >> bit & 1:
                    suffix *= basis_value
            value += query_weight * fixed * suffix
        result.append(value)
    return result


def verify_ligerito(
    transcript: Transcript,
    opening: LigeritoOpening,
    log_n: int,
    target: F128,
    root: bytes,
    evaluate_basis: Callable[[Sequence[F128], int], Sequence[F128]],
) -> None:
    """Verify one succinct multilevel opening and consume its transcript data."""
    config = derive_config(log_n)
    level_count = len(config.folds)
    require(len(opening.levels) == max(0, level_count - 2), "wrong Ligerito level count")
    transcript.observe(target)
    transcript.absorb_bytes(root)

    running_target = target
    running_quad = QuadraticMessage.read(transcript, running_target)
    all_folds: list[F128] = []
    level_contexts: list[tuple[int, list[int], list[F128], int, F128]] = []
    previous_root: bytes | None = None
    previous_message_log = 0
    previous_rate = 0
    previous_fold = 0
    middle_index = 0

    for level in range(level_count):
        fold_values: list[F128] = []
        for fold_index in range(config.folds[level]):
            bits = max(0, config.fold_grinding[level] - fold_index)
            if bits:
                transcript.grind(bits)
            challenge = transcript.sample()
            all_folds.append(challenge)
            fold_values.append(challenge)
            running_target = running_quad.evaluate(challenge)
            running_quad = QuadraticMessage.read(transcript, running_target)

        message_log = log_n - len(all_folds)
        if level == 0:
            opened = opening.initial
            authentication_root = root
            opened_message_log = message_log
            opened_rate = config.rates[0]
            opened_width = 1 << config.folds[0]
        else:
            opened = opening.final if level == level_count - 1 else opening.levels[middle_index]
            if level < level_count - 1:
                middle_index += 1
            if previous_root is None:
                raise VerificationError("missing preceding Ligerito commitment")
            authentication_root = previous_root
            opened_message_log = previous_message_log
            opened_rate = previous_rate
            opened_width = 1 << previous_fold

        if level == level_count - 1:
            residual = transcript.scalars(1 << message_log)
        else:
            root_words = transcript.scalars(2)
            next_root = root_words[0].to_bytes() + root_words[1].to_bytes()

        transcript.grind(config.query_grinding[level])
        block_length = 1 << (opened_message_log + opened_rate)
        queries = sample_queries(transcript.sponge, block_length, config.queries[level])
        alpha = transcript.samples(max(0, (len(queries) - 1).bit_length()))
        try:
            rows = authenticate_rows(
                authentication_root,
                block_length,
                queries,
                opened.opened_rows,
                opened_width,
                opened.merkle_proof,
            )
        except VerificationError as exc:
            raise VerificationError(f"Ligerito level {level}: {exc}") from exc
        enforced = _enforced_sum(rows, fold_values, alpha)

        if level == level_count - 1:
            beta = transcript.sample()
            running_target += beta * enforced
            level_contexts.append((message_log, queries, alpha, len(all_folds), beta))
            basis_values = list(evaluate_basis(all_folds, message_log))
            require(len(basis_values) == len(residual), "basis residual has the wrong length")
            combined = basis_values
            for context_log, context_queries, context_alpha, start, context_beta in level_contexts:
                prefix_length = context_log - message_log
                induced = _induced_residual(
                    context_log,
                    context_queries,
                    context_alpha,
                    all_folds[start : start + prefix_length],
                    message_log,
                )
                combined = [a + context_beta * b for a, b in zip(combined, induced)]
            terminal = sum((a * b for a, b in zip(residual, combined)), ZERO)
            require(terminal == running_target, "Ligerito residual check failed")
            return

        intro = QuadraticMessage.read(transcript, enforced)
        beta = transcript.sample()
        running_quad = running_quad.add_scaled(intro, beta)
        running_target += beta * enforced
        level_contexts.append((message_log, queries, alpha, len(all_folds), beta))
        previous_root = next_root
        previous_message_log = message_log - config.folds[level + 1]
        previous_rate = config.rates[level + 1]
        previous_fold = config.folds[level + 1]

    raise VerificationError("Ligerito verification ended without a terminal level")

# Flock reduction -------------------------------------------------------------

PHI_BASIS = (
    F128.new(0x0000000000000001, 0x0000000000000000),
    F128.new(0x6B8330483C2E9849, 0x0DCB364640A222FE),
    F128.new(0x7573DA4A5F7710ED, 0x3D5BD35C94646A24),
    F128.new(0x41A12DB1F974F3AC, 0x6D58C4E181F9199F),
    F128.new(0x5E2F716F4EDE412F, 0xA72EC17764D7CED5),
    F128.new(0x5CB10FBABCF00118, 0x4D52354A3A3D8C86),
    F128.new(0x95ED1F57F3632D4D, 0x553E92E8BC0AE9A7),
    F128.new(0x512625B1F09FA87E, 0x93252331BF042B11),
)
PHI = tuple(sum((PHI_BASIS[bit] for bit in range(8) if value >> bit & 1), ZERO)
            for value in range(256))
FIXED_CHALLENGES = (
    PHI[0xF7], PHI[0x53], PHI[0xB5],
    F128(2) / F128(3), F128(4) / F128(5), F128(16) / F128(17), F128(256) / F128(257),
)


@lru_cache(maxsize=None)
def _denominators(nodes: tuple[F128, ...]) -> tuple[F128, ...]:
    result = []
    for index, node in enumerate(nodes):
        denominator = ONE
        for other_index, other in enumerate(nodes):
            if other_index != index:
                denominator *= node + other
        result.append(denominator.inv())
    return tuple(result)


def lagrange_weights(nodes: Sequence[F128], point: F128) -> list[F128]:
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


def lagrange_interpolate(nodes: Sequence[F128], values: Sequence[F128], point: F128) -> F128:
    weights = lagrange_weights(nodes, point)
    return sum((weight * value for weight, value in zip(weights, values)), ZERO)


def quirky_weights(skip_point: F128, rest: Sequence[F128]) -> list[F128]:
    skip = lagrange_weights(PHI[:64], skip_point)
    tail = build_eq(rest)
    return [a * b for b in tail for a in skip]


@dataclass(frozen=True)
class QuirkyPoint:
    skip: F128
    inner: tuple[F128, ...]
    outer: tuple[F128, ...]

    @property
    def ring_tail(self) -> tuple[F128, ...]:
        return self.inner + self.outer


@dataclass(frozen=True)
class ZClaim:
    point: QuirkyPoint
    value: F128


@dataclass(frozen=True)
class ZerocheckResult:
    skip: F128
    rounds: tuple[F128, ...]
    equality_tail: tuple[F128, ...]
    a: F128
    b: F128
    c: F128


def verify_zerocheck(log_n: int, transcript: Transcript) -> ZerocheckResult:
    require(log_n >= 13, "Flock zerocheck input is too small")
    sampled_prefix = transcript.samples(6)
    sampled_outer = transcript.samples(log_n - 13)
    equality_point = (*sampled_prefix, *FIXED_CHALLENGES, *sampled_outer)
    ab_values = transcript.scalars(64)
    c_values = transcript.scalars(64)
    skip = transcript.sample()

    c_evaluation = lagrange_interpolate(PHI[64:128], c_values, skip)
    combined = [a + c for a, c in zip(ab_values, c_values)]
    combined_evaluation = lagrange_interpolate(PHI[:128], [ZERO] * 64 + combined, skip)
    running = combined_evaluation + c_evaluation
    rounds = []
    for equality in equality_point[6:]:
        at_one, at_infinity = transcript.scalars(2)
        at_zero = (running + equality * at_one) / (ONE + equality)
        challenge = transcript.sample()
        rounds.append(challenge)
        running = (at_zero * (ONE + challenge) + at_one * challenge
                   + at_infinity * challenge * (ONE + challenge))
    final_a, final_b = transcript.scalars(2)
    require(running == final_a * final_b, "Flock zerocheck terminal mismatch")
    return ZerocheckResult(skip, tuple(rounds), tuple(equality_point[6:]),
                           final_a, final_b, c_evaluation)


@dataclass(frozen=True)
class LincheckResult:
    point: QuirkyPoint
    value: F128


@dataclass(frozen=True)
class Reduction:
    ab: ZClaim
    c: ZClaim


def _claim_weights(point: QuirkyPoint) -> list[F128]:
    low = lagrange_weights(PHI[:64], point.skip)
    low_scale, high_scale = ONE + point.ring_tail[0], point.ring_tail[0]
    return [value * low_scale for value in low] + [value * high_scale for value in low]


def _transpose(values: Sequence[F128]) -> list[F128]:
    require(len(values) == 128, "ring-switch slice has the wrong length")
    output = [0] * 128
    for row, value in enumerate(values):
        bits = int(value)
        while bits:
            bit = (bits & -bits).bit_length() - 1
            output[bit] ^= 1 << row
            bits &= bits - 1
    return [F128(value) for value in output]


def _fold_binary_elements(elements: Sequence[F128], weights: Sequence[F128]) -> list[F128]:
    output = []
    for element in elements:
        bits = int(element)
        value = ZERO
        while bits:
            bit = (bits & -bits).bit_length() - 1
            value += weights[bit]
            bits &= bits - 1
        output.append(value)
    return output


def verify_stacked_opening(
    transcript: Transcript,
    opening: LigeritoOpening,
    root: bytes,
    stack_log: int,
    qpkd_offset: int,
    qpkd_variables: int,
    reduction: Reduction,
    point_claims: Sequence[tuple[Sequence[F128], F128]],
) -> None:
    """Bind both ring-switched claims and all ordinary stack point claims."""
    ring_claims = (reduction.ab, reduction.c)
    slices = []
    for claim in ring_claims:
        values = transcript.scalars(128)
        expected = sum((a * b for a, b in zip(_claim_weights(claim.point), values)), ZERO)
        require(expected == claim.value, "ring-switch claim mismatch")
        slices.append(values)

    ring_challenge = transcript.samples(7)
    ring_weights = build_eq(ring_challenge)
    ring_values = [sum((a * b for a, b in zip(_transpose(values), ring_weights)), ZERO)
                   for values in slices]
    ring_scales = transcript.samples(2)
    target = sum((scale * value for scale, value in zip(ring_scales, ring_values)), ZERO)

    for _, value in point_claims:
        transcript.observe(value)
    point_scales = transcript.samples(len(point_claims))
    target += sum((scale * value for scale, (_, value) in zip(point_scales, point_claims)), ZERO)

    ring_polynomials = []
    for claim in ring_claims:
        suffix = build_eq(claim.point.ring_tail[1:])
        ring_polynomials.append(_fold_binary_elements(suffix, ring_weights))
    selector = qpkd_offset >> qpkd_variables

    def evaluate_basis(prefix: Sequence[F128], residual_log: int) -> list[F128]:
        result = []
        for vertex in range(1 << residual_log):
            point = list(prefix) + [F128(vertex >> bit & 1) for bit in range(residual_log)]
            low, high = point[:qpkd_variables], point[qpkd_variables:]
            selector_weight = ONE
            for bit, challenge in enumerate(high):
                selector_weight *= challenge if selector >> bit & 1 else ONE + challenge
            value = selector_weight * sum(
                (scale * mle_eval(poly, low)
                 for scale, poly in zip(ring_scales, ring_polynomials)), ZERO)
            for scale, (claim_point, _) in zip(point_scales, point_claims):
                require(len(claim_point) == len(point), "stack point has the wrong dimension")
                factor = ONE
                for expected, challenge in zip(claim_point, point):
                    factor *= ONE + expected + challenge
                value += scale * factor
            result.append(value)
        return result

    verify_ligerito(transcript, opening, stack_log, target, root, evaluate_basis)


def verify_reduction(log_n: int, transcript: Transcript) -> Reduction:
    zerocheck = verify_zerocheck(log_n, transcript)
    inner_length = 8
    ab_point = QuirkyPoint(zerocheck.skip, zerocheck.rounds[:inner_length],
                           zerocheck.rounds[inner_length:])
    lincheck = verify_lincheck(log_n, ab_point, zerocheck.a, zerocheck.b, transcript)
    c_point = QuirkyPoint(zerocheck.skip, zerocheck.equality_tail[:inner_length],
                          zerocheck.equality_tail[inner_length:])
    return Reduction(ZClaim(lincheck.point, lincheck.value), ZClaim(c_point, zerocheck.c))


def verify_lincheck(
    log_n: int,
    point: QuirkyPoint,
    a: F128,
    b: F128,
    transcript: Transcript,
) -> LincheckResult:
    """Replay the fixed BLAKE3 matrix reduction."""
    alpha = transcript.sample()
    inner_weights = quirky_weights(point.skip, point.inner)
    coefficients = blake3_matrix_fold(alpha, inner_weights)
    beta = transcript.sample()
    coefficients[512] += beta
    running = alpha * a + b + beta
    challenges = []
    for _ in range(8):
        at_one, at_infinity = transcript.scalars(2)
        at_zero = running + at_one
        linear = at_zero + at_one + at_infinity
        challenge = transcript.sample()
        running = at_infinity * challenge * challenge + linear * challenge + at_zero
        half = len(coefficients) // 2
        coefficients = [coefficients[i] * (ONE + challenge) + coefficients[i + half] * challenge
                        for i in range(half)]
        challenges.append(challenge)
    partial = transcript.scalars(64)
    require(sum((x * y for x, y in zip(coefficients, partial)), ZERO) == running,
           "Flock lincheck terminal mismatch")
    skip = transcript.sample()
    value = sum((x * y for x, y in zip(lagrange_weights(PHI[:64], skip), partial)), ZERO)
    return LincheckResult(QuirkyPoint(skip, tuple(reversed(challenges)), point.outer), value)


def blake3_matrix_fold(alpha: F128, row_weights: Sequence[F128]) -> list[F128]:
    """Compute ``alpha * eq^T A + eq^T B`` by walking the fixed circuit."""
    require(len(row_weights) == 1 << 14, "bad BLAKE3 row-weight vector")
    size = 1 << 14
    constant = 512
    message_base = 640
    counter_low = 1152
    counter_high = 1184
    block_length = 1216
    flags = 1248
    gates_base = 1280
    gate_stride = 250
    output_high = 15280
    iv = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A)
    lanes = ((0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),
             (0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14))
    message_pairs = ((0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15))
    permutation = (2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8)
    accumulated = [0] * size

    def emit(row: int, left: frozenset[int], right: frozenset[int]) -> None:
        weight = row_weights[row]
        scaled = int(alpha * weight)
        plain = int(weight)
        for column in left:
            accumulated[column] ^= scaled
        for column in right:
            accumulated[column] ^= plain

    def slots(base: int) -> tuple[frozenset[int], ...]:
        return tuple(frozenset((base + bit,)) for bit in range(32))

    empty_word = tuple(frozenset() for _ in range(32))

    def literal(value: int) -> tuple[frozenset[int], ...]:
        return tuple(frozenset((constant,)) if value >> bit & 1 else frozenset()
                     for bit in range(32))

    def xor(x: Sequence[frozenset[int]], y: Sequence[frozenset[int]]) -> tuple[frozenset[int], ...]:
        return tuple(a ^ b for a, b in zip(x, y))

    def rotate_right(word: Sequence[frozenset[int]], amount: int) -> tuple[frozenset[int], ...]:
        return tuple(word[(bit + amount) & 31] for bit in range(32))

    def add(x: Sequence[frozenset[int]], y: Sequence[frozenset[int]], carry_base: int):
        carry: set[int] = set()
        output = []
        for bit in range(32):
            if bit < 31:
                emit(carry_base + bit, x[bit] ^ carry, y[bit] ^ carry)
            output.append(x[bit] ^ y[bit] ^ carry)
            if bit < 31:
                carry.add(carry_base + bit)
        return tuple(output)

    # Booleanity/constant and unconstrained public input rows.
    emit(constant, frozenset((constant,)), frozenset((constant,)))
    for base, length in ((0,256),(message_base,512),(counter_low,64),(block_length,32),(flags,32)):
        for row in range(base, base + length):
            emit(row, frozenset((row,)), frozenset((constant,)))

    state = [empty_word for _ in range(16)]
    for word in range(8):
        state[word] = slots(32 * word)
    for word in range(4):
        state[8 + word] = literal(iv[word])
    state[12], state[13], state[14], state[15] = (
        slots(counter_low), slots(counter_high), slots(block_length), slots(flags))

    message_order = list(range(16))
    for round_index in range(7):
        for gate_index, (lane_a, lane_b, lane_c, lane_d) in enumerate(lanes):
            gate = round_index * 8 + gate_index
            gate_base = gates_base + gate_stride * gate
            a, b, c, d = state[lane_a], state[lane_b], state[lane_c], state[lane_d]
            mx_index, my_index = message_pairs[gate_index]
            mx = slots(message_base + 32 * message_order[mx_index])
            my = slots(message_base + 32 * message_order[my_index])
            temp0 = add(a, b, gate_base)
            a1 = add(temp0, mx, gate_base + 31)
            d1 = rotate_right(xor(d, a1), 16)
            c1 = add(c, d1, gate_base + 62)
            b1 = rotate_right(xor(b, c1), 12)
            temp1 = add(a1, b1, gate_base + 93)
            a2 = add(temp1, my, gate_base + 124)
            d2 = rotate_right(xor(d1, a2), 8)
            c2 = add(c1, d2, gate_base + 155)
            b_new = rotate_right(xor(b1, c2), 7)
            b_base = gate_base + 186
            d_base = b_base + 32
            for bit in range(32):
                emit(b_base + bit, b_new[bit], frozenset((constant,)))
                emit(d_base + bit, d2[bit], frozenset((constant,)))
            state[lane_a] = a2
            state[lane_b] = slots(b_base)
            state[lane_c] = c2
            state[lane_d] = slots(d_base)
        message_order = [message_order[index] for index in permutation]

    for word in range(8):
        low = xor(state[word], state[word + 8])
        high = xor(state[word + 8], slots(32 * word))
        for bit in range(32):
            emit(256 + 32 * word + bit, low[bit], frozenset((constant,)))
            emit(output_high + 32 * word + bit, high[bit], frozenset((constant,)))
    return [F128(value) for value in accumulated]

# Complete VM verification and CLI -------------------------------------------


def _selector_point(selector: int, length: int) -> tuple[F128, ...]:
    return tuple(F128(selector >> bit & 1) for bit in range(length))


def verify_execution(statement: dict[str, Any], proof: Proof) -> None:
    """Verify a complete leanVM-b execution proof against its public statement."""
    program = Program.parse(statement)
    encoded_input = statement.get("public_input")
    if not isinstance(encoded_input, list) or len(encoded_input) != 2:
        raise VerificationError("public input must contain two field elements")
    public_input = tuple(parse_field(value) for value in encoded_input)
    transcript = Transcript(proof, b"leanvm-b", program.transcript_statement(public_input))

    announced = transcript.scalars(7)
    require(all(value.hi == 0 for value in announced), "announced size has a nonzero high limb")
    log_memory = announced[0].lo
    row_counts = tuple(value.lo for value in announced[1:])
    layout = build_layout(program, log_memory, row_counts)

    root_words = transcript.scalars(2)
    root = root_words[0].to_bytes() + root_words[1].to_bytes()
    bus = verify_bus_balance(layout.push, layout.pull, layout.count, layout.padding, transcript)
    eta = transcript.sample()
    identity_count = sum(CONSTRAINT_COUNTS)
    form_powers = powers(eta, identity_count + 3)[identity_count:]
    target = sum(
        (weight * total for weight, total in zip(form_powers, bus.totals)),
        ZERO,
    )
    air_claims = verify_constraints(
        build_airs(layout, bus.forms, form_powers),
        eta,
        bus.point,
        target,
        transcript,
    )

    claims = list(bus.claims)
    claims.extend(constraint_claims(layout, air_claims))
    public_challenge = transcript.sample()
    public_point = [ZERO] * layout.placements[0].variables
    public_point[0] = public_challenge
    public_value = interpolate(public_input[0], public_input[1], public_challenge)
    claims.append(ColumnClaim(0, tuple(public_point), public_value))

    point_claims: list[tuple[tuple[F128, ...], F128]] = []
    qpkd = layout.placements[3]
    for claim in claims:
        slot = virtual_slot(claim.column)
        if slot is None:
            placement = layout.placements[claim.column]
            require(not placement.virtual, "claim targets an uncommitted column")
            require(len(claim.point) == placement.variables, "column claim dimension mismatch")
            selector = placement.offset >> placement.variables
            full_point = claim.point + _selector_point(
                selector, layout.stack_log - placement.variables
            )
        else:
            require(len(claim.point) + 7 == qpkd.variables, "BLAKE3 slot claim dimension mismatch")
            selector = qpkd.offset >> qpkd.variables
            full_point = (
                _selector_point(slot, 7)
                + claim.point
                + _selector_point(selector, layout.stack_log - qpkd.variables)
            )
        point_claims.append((full_point, claim.value))

    reduction = verify_reduction(14 + layout.table_logs[5], transcript)
    opening = transcript.opening()
    verify_stacked_opening(
        transcript,
        opening,
        root,
        layout.stack_log,
        qpkd.offset,
        qpkd.variables,
        reduction,
        point_claims,
    )
    transcript.finish()


def main(argv: Sequence[str] | None = None) -> int:
    import argparse
    import json

    parser = argparse.ArgumentParser(description="Verify a leanVM-b execution proof")
    parser.add_argument("statement", type=Path, help="public statement JSON")
    parser.add_argument("proof", type=Path, help="bincode proof")
    arguments = parser.parse_args(argv)
    try:
        verify_execution(json.loads(arguments.statement.read_text()), Proof.load(arguments.proof))
    except (OSError, ValueError, KeyError, VerificationError) as exc:
        parser.exit(1, f"verification failed: {exc}\n")
    print("verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
