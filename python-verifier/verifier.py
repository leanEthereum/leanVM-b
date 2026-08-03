"""Dependency-free verifier for leanVM-b execution proofs.

The command-line interface consumes a public statement JSON file and the
project's bincode proof. No prover-side auxiliary data is accepted. The file is
ordered along the verification path: arithmetic and hashing, proof transport,
GKR/bus/AIR checks, VM layout, Ligerito, Flock, and final orchestration.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import ceil, isfinite, log2, nextafter, sqrt
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
MASK64 = (1 << 64) - 1
RING_SWITCH_SOUNDNESS_DEGREE = (1 << 31) + (1 << 15) + (1 << 7) + (1 << 3) + (1 << 1) + 1


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
    return (
        (folded & MASK64)
        ^ overflow
        ^ (overflow << 1)
        ^ (overflow << 3)
        ^ (overflow << 4)
    ) & MASK64


@dataclass(frozen=True, slots=True)
class F192:
    """The tower field GF(2^192) = GF(2^64)[y]/(y^3 + y + 1)."""

    c0: int = 0
    c1: int = 0
    c2: int = 0

    def __post_init__(self) -> None:
        object.__setattr__(self, "c0", self.c0 & MASK64)
        object.__setattr__(self, "c1", self.c1 & MASK64)
        object.__setattr__(self, "c2", self.c2 & MASK64)

    @classmethod
    def new(cls, c0: int, c1: int, c2: int = 0) -> "F192":
        return cls(c0, c1, c2)

    @classmethod
    def from_bytes(cls, data: bytes) -> "F192":
        require(len(data) == 24, "a field element must contain exactly 24 bytes")
        return cls(*(int.from_bytes(data[offset : offset + 8], "little") for offset in (0, 8, 16)))

    def to_bytes(self) -> bytes:
        return b"".join(limb.to_bytes(8, "little") for limb in (self.c0, self.c1, self.c2))

    @staticmethod
    def _coerce(other: object) -> "F192":
        if isinstance(other, F192):
            return other
        if isinstance(other, int):
            return F192(other)
        raise TypeError(f"cannot use {type(other).__name__} as a field element")

    def __int__(self) -> int:
        return self.c0 | self.c1 << 64 | self.c2 << 128

    def __bool__(self) -> bool:
        return bool(self.c0 or self.c1 or self.c2)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, (F192, int)):
            return False
        rhs = self._coerce(other)
        return self.c0 == rhs.c0 and self.c1 == rhs.c1 and self.c2 == rhs.c2

    def __hash__(self) -> int:
        return hash((self.c0, self.c1, self.c2))

    def __add__(self, other: object) -> "F192":
        rhs = self._coerce(other)
        return F192(self.c0 ^ rhs.c0, self.c1 ^ rhs.c1, self.c2 ^ rhs.c2)

    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__

    def __neg__(self) -> "F192":
        return self

    def __mul__(self, other: object) -> "F192":
        rhs = self._coerce(other)
        p0 = _base_mul(self.c0, rhs.c0)
        p1 = _base_mul(self.c0, rhs.c1) ^ _base_mul(self.c1, rhs.c0)
        p2 = _base_mul(self.c0, rhs.c2) ^ _base_mul(self.c1, rhs.c1) ^ _base_mul(self.c2, rhs.c0)
        p3 = _base_mul(self.c1, rhs.c2) ^ _base_mul(self.c2, rhs.c1)
        p4 = _base_mul(self.c2, rhs.c2)
        return F192(p0 ^ p3, p1 ^ p3 ^ p4, p2 ^ p4)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> "F192":
        if exponent < 0:
            return self.inv() ** -exponent
        base, out, n = self, ONE, exponent
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> "F192":
        require(bool(self), "division by zero in GF(2^192)")
        return self ** ((1 << 192) - 2)

    def __truediv__(self, other: object) -> "F192":
        rhs = self._coerce(other)
        return self * rhs.inv()

    def __rtruediv__(self, other: object) -> "F192":
        lhs = self._coerce(other)
        return lhs * self.inv()

    def __repr__(self) -> str:
        return f"F192(0x{self.c2:016x}{self.c1:016x}{self.c0:016x})"


ZERO = F192(0)
ONE = F192(1)
GEN = F192(2)


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


def build_eq(point: Sequence[F192]) -> list[F192]:
    out = [ONE]
    for r in point:
        out = [v * (ONE + r) for v in out] + [v * r for v in out]
    return out


def mle_eval(evals: Sequence[F192], point: Sequence[F192]) -> F192:
    require(len(evals) == 1 << len(point), "multilinear table has the wrong size")
    cur = list(evals)
    for r in point:
        cur = [cur[2 * i] * (ONE + r) + cur[2 * i + 1] * r for i in range(len(cur) // 2)]
    return cur[0]

# Shared verification helpers -------------------------------------------------
def interpolate(a: F192, b: F192, point: F192) -> F192:
    """Evaluate the line through ``a`` and ``b`` at ``point``."""
    return a + point * (a + b)


def eq_eval(left: Sequence[F192], right: Sequence[F192]) -> F192:
    require(len(left) == len(right), "eq: dimension mismatch")
    result = ONE
    for x, y in zip(left, right):
        result *= ONE + x + y
    return result


TRI_NODES = (ZERO, ONE, GEN)
QUAD_NODES = (ZERO, ONE, GEN, GEN * GEN)


def lagrange_eval(
    nodes: Sequence[F192], values: Sequence[F192], point: F192
) -> F192:
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

    def field(self) -> F192:
        return F192.from_bytes(self.take(24))

    def base_field(self) -> int:
        return self.u64()

    def fields(self) -> list[F192]:
        length = self.u64()
        require(length <= self.remaining // 24, "invalid field-vector length")
        return [self.field() for _ in range(length)]

    def base_fields(self) -> list[int]:
        length = self.u64()
        require(length <= self.remaining // 8, "invalid base-field-vector length")
        return [self.base_field() for _ in range(length)]

    def hashes(self) -> tuple[bytes, ...]:
        length = self.u64()
        require(length <= self.remaining // 32, "invalid hash-vector length")
        return tuple(self.take(32) for _ in range(length))

    @property
    def remaining(self) -> int:
        return len(self.data) - self.offset

    def finish(self) -> None:
        require(self.remaining == 0, "trailing proof encoding")


@dataclass(frozen=True)
class InitialOpening:
    opened_rows: tuple[tuple[int, ...], ...]
    merkle_proof: tuple[bytes, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> "InitialOpening":
        row_count = reader.u64()
        require(row_count <= reader.remaining // 8, "invalid opened-row count")
        rows = tuple(tuple(reader.base_fields()) for _ in range(row_count))
        return cls(rows, reader.hashes())


@dataclass(frozen=True)
class RecursiveOpening:
    opened_rows: tuple[tuple[F192, ...], ...]
    merkle_proof: tuple[bytes, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> "RecursiveOpening":
        row_count = reader.u64()
        require(row_count <= reader.remaining // 8, "invalid opened-row count")
        rows = tuple(tuple(reader.fields()) for _ in range(row_count))
        return cls(rows, reader.hashes())


@dataclass(frozen=True)
class FinalOpening:
    residual: tuple[F192, ...]
    opened_rows: tuple[tuple[F192, ...], ...]
    merkle_proof: tuple[bytes, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> "FinalOpening":
        residual = tuple(reader.fields())
        opened = RecursiveOpening.read(reader)
        return cls(residual, opened.opened_rows, opened.merkle_proof)


@dataclass(frozen=True)
class SumcheckMessage:
    constant: F192
    quadratic: F192


@dataclass(frozen=True)
class LigeritoProofData:
    initial: InitialOpening
    recursive_roots: tuple[bytes, ...]
    recursive: tuple[RecursiveOpening, ...]
    final: FinalOpening
    sumcheck: tuple[SumcheckMessage, ...]
    grinding_nonces: tuple[int, ...]
    ood_values: tuple[F192, ...]
    fold_grinding_nonces: tuple[int, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> "LigeritoProofData":
        initial = InitialOpening.read(reader)
        roots = reader.hashes()
        count = reader.u64()
        require(count <= 32, "too many Ligerito levels")
        recursive = tuple(RecursiveOpening.read(reader) for _ in range(count))
        final = FinalOpening.read(reader)
        message_count = reader.u64()
        require(message_count <= reader.remaining // 48, "invalid sumcheck length")
        sumcheck = tuple(SumcheckMessage(reader.field(), reader.field()) for _ in range(message_count))
        nonce_count = reader.u64()
        require(nonce_count <= reader.remaining // 8, "invalid nonce-vector length")
        nonces = tuple(reader.u64() for _ in range(nonce_count))
        ood_values = tuple(reader.fields())
        fold_count = reader.u64()
        require(fold_count <= reader.remaining // 8, "invalid fold-nonce length")
        fold_nonces = tuple(reader.u64() for _ in range(fold_count))
        return cls(initial, roots, recursive, final, sumcheck, nonces, ood_values, fold_nonces)


@dataclass(frozen=True)
class LigeritoOpening:
    ring_switches: tuple[tuple[F192, ...], ...]
    ligerito: LigeritoProofData

    @classmethod
    def read(cls, reader: BinaryReader) -> "LigeritoOpening":
        count = reader.u64()
        require(count <= 16, "too many ring-switch proofs")
        ring_switches = tuple(tuple(reader.fields()) for _ in range(count))
        return cls(ring_switches, LigeritoProofData.read(reader))


@dataclass(frozen=True)
class Proof:
    stream: tuple[F192, ...]
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


DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQUEEZE = 4
DS_POW = 5


def compress(left: Sequence[int], right: Sequence[int]) -> tuple[int, int, int, int]:
    require(len(left) == len(right) == 4, "compression operands must contain four words")
    digest = blake3_hash(b"".join(x.to_bytes(8, "little") for x in (*left, *right)))
    return tuple(int.from_bytes(digest[offset : offset + 8], "little") for offset in (0, 8, 16, 24))


class Sponge:
    def __init__(self, label: bytes, statement: Sequence[F192]):
        self.state = (0, 0, 0, 0)
        self.absorb_bytes(b"leanvm-b/transcript/v2")
        self.absorb_bytes(label)
        for value in statement:
            self.observe(value)

    def observe(self, value: F192) -> None:
        self.state = compress(self.state, (value.c0, value.c1, value.c2, DS_SCALAR))

    def absorb_bytes(self, data: bytes) -> None:
        self.state = compress(self.state, (len(data), 0, DS_LEN, 0))
        for offset in range(0, len(data), 16):
            block = data[offset : offset + 16].ljust(16, b"\0")
            self.state = compress(
                self.state,
                (int.from_bytes(block[:8], "little"), int.from_bytes(block[8:], "little"), DS_BYTE, 0),
            )

    def sample(self) -> F192:
        self.state = compress(self.state, (0, 0, DS_SQUEEZE, 0))
        return F192(*self.state[:3])

    def check_pow(self, nonce: int | F192, bits: int) -> None:
        require(0 <= bits < 64, "invalid grinding width")
        encoded = nonce if isinstance(nonce, F192) else F192(nonce)
        block = (encoded.c0, encoded.c1, encoded.c2, DS_POW)
        base = compress(self.state, (0, 0, DS_POW, 0))
        digest = compress(base, block)[0]
        valid = encoded == F192(0) if bits == 0 else digest & ((1 << bits) - 1) == 0
        self.state = compress(self.state, block)
        require(valid, "invalid grinding nonce")


class Transcript:
    def __init__(self, proof: Proof, label: bytes, statement: Sequence[F192]):
        self.proof = proof
        self.sponge = Sponge(label, statement)
        self.stream_offset = 0
        self.opening_offset = 0

    def scalar(self) -> F192:
        require(self.stream_offset < len(self.proof.stream), "proof stream exhausted")
        value = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        self.sponge.observe(value)
        return value

    def scalars(self, count: int) -> list[F192]:
        return [self.scalar() for _ in range(count)]

    def sample(self) -> F192:
        return self.sponge.sample()

    def samples(self, count: int) -> list[F192]:
        return [self.sample() for _ in range(count)]

    def observe(self, value: F192) -> None:
        self.sponge.observe(value)

    def absorb_bytes(self, data: bytes) -> None:
        self.sponge.absorb_bytes(data)

    def grind(self, bits: int) -> None:
        require(self.stream_offset < len(self.proof.stream), "missing grinding nonce")
        encoded = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        self.sponge.check_pow(encoded, bits)

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
    roots: tuple[F192, F192, F192]
    point: tuple[F192, ...]
    values: tuple[F192, F192, F192]


def quartic_eval_from_eq(
    claim: F192,
    equality_point: F192,
    difference: F192,
    c2: F192,
    c3: F192,
    c4: F192,
    challenge: F192,
) -> F192:
    c0 = claim + equality_point * difference
    c1 = difference + c2 + c3 + c4
    return c0 + challenge * (c1 + challenge * (c2 + challenge * (c3 + challenge * c4)))


def verify_product_triple(depth: int, transcript: Transcript) -> ProductTriple:
    root_values = transcript.scalars(3)
    roots = (root_values[0], root_values[1], root_values[2])
    combine = transcript.sample()
    point: list[F192] = []
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

        round_point: list[F192] = []
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

    constant: F192 | None = None
    column: int | None = None
    generator_column: int | None = None
    index: bool = False
    public: tuple[F192, ...] | None = None

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


def index_mle(point: Sequence[F192]) -> F192:
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
    point: tuple[F192, ...]
    value: F192


@dataclass(frozen=True)
class BytecodeClaim:
    point: tuple[F192, ...]
    value: F192


@dataclass
class BusForm:
    coefficients: list[F192]
    constant: F192 = ZERO

    def evaluate(self, values: Sequence[F192]) -> F192:
        require(len(values) == len(self.coefficients), "bus form width mismatch")
        return sum(
            (coefficient * value for coefficient, value in zip(self.coefficients, values)),
            self.constant,
        )


def _decompose_bus_side(
    blocks: Sequence[BusBlock],
    layout: BusLayout,
    point: Sequence[F192],
    alpha: F192,
    gamma: F192,
    forms: Sequence[BusForm],
    claims: list[ColumnClaim],
    transcript: Transcript,
) -> F192:
    require(len(point) == layout.depth, "bus point dimension mismatch")

    def committed_value(column: int, low_point: tuple[F192, ...]) -> F192:
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
            F192((selector >> bit) & 1)
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


def _padding_fingerprint(block: BusBlock, padding: Sequence[F192], alpha: F192) -> F192:
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
    padding: Sequence[F192],
    alpha: F192,
    gamma: F192,
) -> F192:
    result = ONE
    for block in blocks:
        surplus_rows = (1 << block.log_rows) - block.real_rows
        if surplus_rows:
            result *= (gamma + _padding_fingerprint(block, padding, alpha)) ** surplus_rows
    return result


def _public_evaluations(
    blocks: Sequence[BusBlock], point: Sequence[F192]
) -> tuple[int, list[F192]]:
    log_rows = 0
    values: list[F192] = []
    for block in blocks:
        for coordinate in block.coordinates:
            if coordinate.public is not None:
                log_rows = block.log_rows
                values.append(mle_eval(coordinate.public, point[: block.log_rows]))
    return log_rows, values


def _stack_public_evaluations(values: Sequence[F192], selector_point: Sequence[F192]) -> F192:
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
    count_root: F192
    point: tuple[F192, ...]
    forms: tuple[tuple[BusForm, ...], ...]
    totals: tuple[F192, F192, F192]


def verify_bus_balance(
    push: Sequence[BusBlock],
    pull: Sequence[BusBlock],
    count: Sequence[BusBlock],
    padding: Sequence[F192],
    transcript: Transcript,
) -> BusResult:
    push_layout = bus_layout(push)
    pull_layout = bus_layout(pull)
    count_layout = bus_layout(count)
    require(push_layout.depth == pull_layout.depth, "push/pull bus depths differ")
    require(count_layout.depth <= push_layout.depth, "count bus is deeper than push bus")

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
    selector_point = transcript.samples(4)
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
    evaluate: Callable[[Sequence[F192], Sequence[F192]], F192]


@dataclass(frozen=True)
class AirClaim:
    point: tuple[F192, ...]
    evaluations: tuple[F192, ...]


def powers(base: F192, count: int) -> list[F192]:
    result, current = [], ONE
    for _ in range(count):
        result.append(current)
        current *= base
    return result


def verify_constraints(
    airs: Sequence[Air],
    eta: F192,
    equality_point: Sequence[F192],
    target: F192,
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
BASES = (6, 27, 48, 57, 78, 105, 146)
WIDTHS = (21, 21, 9, 21, 27, 41, 14)
CONSTRAINT_COUNTS = (4, 4, 1, 4, 7, 6, 3)
COUNT_COLUMNS = (
    (17, 18, 19, 20),
    (17, 18, 19, 20),
    (7, 8),
    (17, 18, 19, 20),
    (19, 20, 21, 22),
    (32, 33, 34, 35, 36, 37, 38, 39, 40),
    (10, 11, 12, 13),
)
BLAKE3_VALUES = tuple(range(14, 32))
BLAKE3_SLOTS = (10, 11, 12, 13, 14, 15, 16, 17, 4, 5, 6, 7, 0, 1, 2, 3, 18, 19)
BLAKE3_SLOT_BY_VALUE: dict[int, int] = dict(zip(BLAKE3_VALUES, BLAKE3_SLOTS))
VM_IV = (0xBB67AE856A09E667, 0xA54FF53A3C6EF372, 0x9B05688C510E527F, 0x5BE0CD191F83D9AB)


def _field(value: Any) -> F192:
    if isinstance(value, F192):
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
        require(0 <= integer < 1 << 192, f"field element is out of range: {value!r}")
        return F192(integer & MASK64, integer >> 64 & MASK64, integer >> 128)
    if isinstance(value, (list, tuple)) and len(value) == 3:
        try:
            limbs = tuple(int(limb) for limb in value)
        except (TypeError, ValueError) as exc:
            raise VerificationError(f"invalid field limbs: {value!r}") from exc
        require(
            all(0 <= limb < 1 << 64 for limb in limbs),
            f"field limb is out of range: {value!r}",
        )
        return F192(*limbs)
    raise VerificationError(f"invalid field element: {value!r}")


def parse_field(value: Any) -> F192:
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
        require(name in {"xor", "mul", "set", "deref", "jump", "pack64x2", "blake3"},
                f"unknown operation {name!r}")
        if name in {"xor", "mul", "pack64x2"}:
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

    def digest(self) -> tuple[int, int, int, int]:
        words = [len(self.operations), 3]
        tags = {"xor": 0, "mul": 1, "set": 2, "jump": 6, "blake3": 7, "pack64x2": 9}
        for operation in self.operations:
            d = operation.values
            name = operation.name
            k = x = y = ZERO
            if name in {"xor", "mul", "pack64x2"}:
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
                x = inputs[3] | int(d["cv"]) << 32
                y = int(d["out"])
            words.extend((a | b << 32, c | tag << 32, k.c0, k.c1, k.c2, int(x), int(y)))
        digest = blake3_hash(b"".join(word.to_bytes(8, "little") for word in words))
        return tuple(int.from_bytes(digest[offset : offset + 8], "little") for offset in (0, 8, 16, 24))

    def transcript_statement(self, public_input: Sequence[F192]) -> tuple[F192, ...]:
        program_digest = self.digest()
        seed = blake3_hash(
            b"leanvm-b-fs-seed-v1"
            + FAMILY_DIGEST
            + b"".join(word.to_bytes(8, "little") for word in program_digest)
        )
        words = tuple(int.from_bytes(seed[offset : offset + 8], "little") for offset in (0, 8, 16, 24))
        return (F192(words[0], words[1]), F192(words[2], words[3]), *public_input)


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
    padding: tuple[F192, ...]
    placements: tuple[Placement, ...]
    stack_log: int
    table_logs: tuple[int, ...]


def _ceil_log(value: int) -> int:
    return max(0, (value - 1).bit_length())


def _gpow(index: int) -> F192:
    return GEN ** index


def _const(value: F192 | int) -> Coordinate:
    return Coordinate(constant=_field(value))


def _col(index: int) -> Coordinate:
    return Coordinate(column=index)


def _gcol(index: int) -> Coordinate:
    return Coordinate(generator_column=index)


def _public(values: Sequence[F192]) -> Coordinate:
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

    def memory(
        self, address: int, count: int, values: Sequence[Coordinate], successor: bool = False
    ) -> None:
        addr = _gcol(address) if successor else _col(address)
        self.pair(
            (_const(GEN), addr, _gcol(count), *values),
            (_const(GEN), addr, _col(count), *values),
        )

    def memory_word(self, address: int, count: int, lo: int, hi: int, top: int) -> None:
        self.memory(address, count, (_col(lo), _col(hi), _col(top)))

    def memory_base(self, address: int, count: int, value: int) -> None:
        self.memory(address, count, (_col(value), _const(ZERO), _const(ZERO)))

    def memory_128(self, address: int, count: int, lo: int, hi: int, successor: bool = False) -> None:
        self.memory(address, count, (_col(lo), _col(hi), _const(ZERO)), successor)


def _table_flushes(table: int) -> Flushes:
    f = Flushes()
    if table in (0, 1):
        f.state_step(0, 1)
        f.bytecode(0, 20, table, (_col(2), _col(3), _col(4), _const(ZERO), _const(ZERO)))
        f.memory_word(5, 17, 8, 9, 10)
        f.memory_word(6, 18, 11, 12, 13)
        f.memory_word(7, 19, 14, 15, 16)
    elif table == 2:
        f.state_step(0, 1)
        f.bytecode(0, 8, 2, (_col(2), _col(3), _col(4), _col(5), _const(ZERO)))
        f.memory_word(6, 7, 3, 4, 5)
    elif table == 3:
        f.state_step(0, 1)
        f.bytecode(0, 20, 3, (_col(2), _col(3), _col(4), _col(5), _col(6)))
        f.memory_base(7, 17, 10)
        f.memory_word(8, 18, 11, 12, 13)
        f.memory_word(9, 19, 14, 15, 16)
    elif table == 4:
        f.state_jump(0, 1, 2, 3)
        f.bytecode(0, 22, 4, (_col(4), _col(5), _col(6), _const(ZERO), _const(ZERO)))
        f.memory_word(7, 19, 10, 11, 12)
        f.memory_word(8, 20, 13, 14, 15)
        f.memory_word(9, 21, 16, 17, 18)
    elif table == 5:
        f.state_step(0, 1)
        f.bytecode(0, 40, 5, tuple(_col(i) for i in (2, 3, 4, 5, 6, 7, 30, 31)))
        for address, count, lo, hi, successor in (
            (8, 32, 14, 15, False),
            (9, 33, 16, 17, False),
            (10, 34, 18, 19, False),
            (11, 35, 20, 21, False),
            (12, 36, 26, 27, False),
            (12, 37, 28, 29, True),
            (13, 38, 22, 23, False),
            (13, 39, 24, 25, True),
        ):
            f.memory_128(address, count, lo, hi, successor)
    else:
        f.state_step(0, 1)
        f.bytecode(0, 13, 6, (_col(2), _col(3), _col(4), _const(ZERO), _const(ZERO)))
        f.memory_base(5, 10, 8)
        f.memory_base(6, 11, 9)
        f.memory_128(7, 12, 8, 9)
    return f


def _offset_coordinate(coordinate: Coordinate, base: int) -> Coordinate:
    if coordinate.column is not None:
        return _col(base + coordinate.column)
    if coordinate.generator_column is not None:
        return _gcol(base + coordinate.generator_column)
    return coordinate


def _program_columns(program: Program) -> tuple[tuple[F192, ...], ...]:
    columns = [[] for _ in range(9)]
    opcodes = {"xor": 0, "mul": 1, "set": 2, "deref": 3, "jump": 4, "blake3": 5, "pack64x2": 6}
    for operation in program.operations:
        d, name = operation.values, operation.name
        operands = [ZERO] * 8
        if name in {"xor", "mul", "pack64x2"}:
            operands[:3] = [_gpow(int(d[k])) for k in ("a", "b", "c")]
        elif name == "set":
            immediate = _field(d["k"])
            operands[:4] = [_gpow(int(d["o"])), F192(immediate.c0), F192(immediate.c1), F192(immediate.c2)]
        elif name == "deref":
            operands[:3] = [_gpow(int(d[k])) for k in ("alpha", "beta", "gamma")]
            mode = str(d["mode"]).lower()
            operands[3:5] = [ONE if mode == "pc" else ZERO, ONE if mode == "fp" else ZERO]
        elif name == "jump":
            operands[:3] = [_gpow(int(d[k])) for k in ("oc", "od", "of")]
        else:
            inputs = [int(v) for v in d["ins"]]
            metadata = _field(d["metadata"])
            operands = [
                *(_gpow(v) for v in inputs),
                _gpow(int(d["cv"])),
                _gpow(int(d["out"])),
                F192(metadata.c0),
                F192(metadata.c1),
            ]
        row = [_gpow(opcodes[name]), *operands]
        for column, value in zip(columns, row):
            column.append(value)
    return tuple(tuple(column) for column in columns)


def build_layout(program: Program, log_memory: int, row_counts: Sequence[int]) -> Layout:
    require(
        16 <= log_memory <= 32
        and len(row_counts) == 7
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
            (_const(GEN), Coordinate(index=True), _const(ONE), _col(0), _col(1), _col(2)),
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
            (_const(GEN), Coordinate(index=True), _col(3), _col(0), _col(1), _col(2)),
            1 << log_memory,
        ),
        BusBlock(
            bytecode_log,
            (
                _const(GEN * GEN),
                Coordinate(index=True),
                _col(4),
                *(_public(column) for column in public_columns),
            ),
            len(program.operations),
        ),
    ]
    count: list[BusBlock] = []
    padding = [ZERO] * (6 + sum(WIDTHS))
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
    digest_words = [int.from_bytes(zero_digest[offset : offset + 8], "little") for offset in (0, 8, 16, 24)]
    for index, value in enumerate(digest_words):
        padding[b3 + 22 + index] = F192(value)
        padding[b3 + 26 + index] = F192(VM_IV[index])
    padding[b3 + 30] = ZERO
    padding[b3 + 31] = F192(64 | 11 << 32)

    kappas: list[int | None] = [0] * (6 + sum(WIDTHS))
    kappas[0] = kappas[1] = kappas[2] = kappas[3] = log_memory
    kappas[4] = bytecode_log
    kappas[5] = table_logs[5] + 8
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
    form_powers: Sequence[F192],
) -> Callable[[Sequence[F192], Sequence[F192]], F192]:
    def evaluate(weights: Sequence[F192], columns: Sequence[F192]) -> F192:
        def value(column: int) -> F192:
            return columns[column]

        def word(lo: int, hi: int, top: int) -> F192:
            return value(lo) + F192(0, 1) * (value(hi) + F192(0, 1) * value(top))

        if table in (0, 1):
            va, vb, vc = word(8, 9, 10), word(11, 12, 13), word(14, 15, 16)
            operation = va + vb if table == 0 else va * vb
            terms = (
                value(5) + value(1) * value(2),
                value(6) + value(1) * value(3),
                value(7) + value(1) * value(4),
                vc + operation,
            )
        elif table == 2:
            terms = (value(6) + value(1) * value(2),)
        elif table == 3:
            v2, v3 = word(11, 12, 13), word(14, 15, 16)
            source = (ONE + value(5) + value(6)) * v3 + value(5) * GEN * GEN * value(0) + value(6) * value(1)
            terms = (
                value(7) + value(1) * value(2),
                value(8) + value(10) * value(3),
                value(9) + value(1) * value(4),
                v2 + source,
            )
        elif table == 4:
            condition = word(10, 11, 12)
            destination = word(13, 14, 15)
            frame = word(16, 17, 18)
            inverse, flag = word(23, 24, 25), value(26)
            terms = (
                value(7) + value(1) * value(4),
                value(8) + value(1) * value(5),
                value(9) + value(1) * value(6),
                flag + condition * inverse,
                condition * (flag + ONE),
                value(2) + flag * destination + (flag + ONE) * GEN * value(0),
                value(3) + flag * frame + (flag + ONE) * value(1),
            )
        elif table == 5:
            terms = tuple(
                value(address) + value(1) * value(operand)
                for address, operand in zip((8, 9, 10, 11, 12, 13), (2, 3, 4, 5, 6, 7))
            )
        else:
            terms = tuple(
                value(address) + value(1) * value(operand)
                for address, operand in zip((5, 6, 7), (2, 3, 4))
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
    form_powers: Sequence[F192],
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
    ood_samples: tuple[int, ...]


def _reduced_rate(rate: int, message_log: int) -> float:
    return ((2.0 ** message_log) - 1.0) / (2.0 ** (message_log + rate))


def _johnson_parameters(rate: int, message_log: int, interleaved_log: int) -> tuple[int, int]:
    rho = _reduced_rate(rate, message_log)
    root_rho = sqrt(rho)
    block_length = 1 << (message_log + rate)
    variables = message_log + interleaved_log
    best: tuple[int, int] | None = None
    for theorem_m in range(3, 4097):
        eta = root_rho / theorem_m
        while ceil(root_rho / eta) > theorem_m:
            eta = nextafter(eta, float("inf"))
        if eta >= 1.0 - root_rho:
            continue
        gamma = 1.0 - root_rho - eta
        half = theorem_m + 0.5
        a = ((2.0 * half ** 5 + 3.0 * half * gamma * rho)
             / (3.0 * rho ** 1.5) * block_length + half / root_rho)
        proximity_bits = 192.0 - log2(a) - max(0, interleaved_log - 1)
        if proximity_bits + 1e-12 < 128.0:
            break
        per_query = log2(1.0 / (1.0 - gamma))
        if not isfinite(per_query) or per_query <= 0.0:
            continue
        queries = ceil(111.0 / per_query)
        if queries > block_length:
            continue
        list_log = log2(1.0 / (2.0 * eta * root_rho))
        ood = 0 if interleaved_log == 6 else next(
            (count for count in range(1, 9)
             if count * (192.0 - log2(variables)) - (2.0 * list_log - 1.0) + 1e-12 >= 128.0),
            0,
        )
        ood_bits = (192.0 - list_log - log2(variables) if ood == 0
                    else ood * (192.0 - log2(variables)) - (2.0 * list_log - 1.0))
        algebraic_bits = 192.0 - log2(max(RING_SWITCH_SOUNDNESS_DEGREE, ceil(log2(queries)), 2)) - list_log
        if ood_bits + 1e-12 < 128.0 or algebraic_bits + 1e-12 < 128.0:
            continue
        candidate = (queries, ood)
        if best is None or queries < best[0]:
            best = candidate
    require(best is not None, "no secure Ligerito configuration")
    return best


def derive_config(log_n: int, initial_rate: int) -> LigeritoConfig:
    """Derive the production Johnson/OOD ladder used by the Rust PCS."""
    require(log_n > 6 and 1 <= initial_rate <= 4, "invalid Ligerito shape")
    folds = [6]
    message_logs = [log_n - 6]
    rates = [initial_rate]
    remaining = message_logs[0]
    prior_fold = 6
    reduction = 3
    while remaining > 5:
        fold = min(3, remaining)
        rates.append(rates[-1] + prior_fold - reduction)
        remaining -= fold
        folds.append(fold)
        message_logs.append(remaining)
        prior_fold = fold
        reduction = 1
    require(len(folds) >= 2, "Ligerito requires at least two levels")
    parameters = tuple(
        _johnson_parameters(rate, columns, fold)
        for rate, columns, fold in zip(rates, message_logs, folds)
    )
    return LigeritoConfig(
        tuple(rates),
        tuple(folds),
        tuple(value[0] for value in parameters),
        (17,) * len(folds),
        (0,) * len(folds),
        tuple(value[1] for value in parameters),
    )


def _hash_pair(left: bytes, right: bytes) -> bytes:
    return blake3_hash(left + right)


FieldValue = F192 | int


def _row_hash(row: Sequence[FieldValue], base_field: bool) -> bytes:
    if base_field:
        return blake3_hash(b"".join(int(value).to_bytes(8, "little") for value in row))
    require(all(isinstance(value, F192) for value in row), "non-field value in extension row")
    return blake3_hash(b"".join(value.to_bytes() for value in row if isinstance(value, F192)))


def authenticate_rows(
    root: bytes,
    leaf_count: int,
    queries: Sequence[int],
    rows: Sequence[Sequence[FieldValue]],
    row_width: int,
    octopus: Sequence[bytes],
    base_field: bool = False,
) -> list[Sequence[FieldValue]]:
    """Authenticate a compressed multiproof and restore transcript row order."""
    require(leaf_count > 0 and leaf_count & (leaf_count - 1) == 0,
           "invalid Merkle leaf count")
    unique = sorted(set(queries))
    require(len(unique) == len(rows),
           f"opened-row count {len(rows)} does not match {len(unique)} distinct queries")
    require(all(0 <= q < leaf_count for q in unique), "Merkle query is out of range")
    require(all(len(row) == row_width for row in rows), "opened row has the wrong width")

    nodes = [(index, _row_hash(row, base_field)) for index, row in zip(unique, rows)]
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
    per_word = 192 // depth
    result: list[int] = []
    while len(result) < count:
        bits = int(sponge.sample())
        for chunk in range(min(per_word, count - len(result))):
            result.append((bits >> (chunk * depth)) & (block_length - 1))
    return result


@dataclass(frozen=True)
class QuadraticMessage:
    constant: F192
    linear: F192
    quadratic: F192

    def evaluate(self, point: F192) -> F192:
        return self.constant + point * self.linear + point * point * self.quadratic

    def add_scaled(self, other: "QuadraticMessage", scale: F192) -> "QuadraticMessage":
        return QuadraticMessage(
            self.constant + scale * other.constant,
            self.linear + scale * other.linear,
            self.quadratic + scale * other.quadratic,
        )


def _enforced_sum(
    rows: Sequence[Sequence[FieldValue]],
    folds: Sequence[F192],
    alpha: Sequence[F192],
) -> F192:
    lane_weights = build_eq(folds)
    query_weights = build_eq(alpha)[: len(rows)]
    total = ZERO
    for query_weight, row in zip(query_weights, rows):
        require(len(row) == len(lane_weights), "Ligerito row/fold width mismatch")
        total += query_weight * sum(
            ((F192(x) if isinstance(x, int) else x) * y for x, y in zip(row, lane_weights)),
            ZERO,
        )
    return total


def _subspace_roots(log_n: int) -> list[F192]:
    roots = [ZERO] * (log_n + 1)
    roots[0] = ONE
    layer = [F192(1 << i) for i in range(1, log_n + 1)]
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
    alpha: Sequence[F192],
    prefix: Sequence[F192],
    residual_log: int,
) -> list[F192]:
    require(len(prefix) + residual_log == message_log, "bad induced-basis dimensions")
    roots = _subspace_roots(message_log)
    inverses = [value.inv() if value else ZERO for value in roots]
    query_weights = build_eq(alpha)[: len(queries)]
    prepared: list[tuple[F192, tuple[F192, ...]]] = []
    for query in queries:
        normalized: list[F192] = []
        current = F192(query)
        for coordinate in range(message_log):
            normalized.append(current * inverses[coordinate])
            current = current * current + roots[coordinate] * current
        fixed = ONE
        for challenge, basis_value in zip(prefix, normalized):
            fixed *= ONE + challenge * (ONE + basis_value)
        prepared.append((fixed, tuple(normalized[len(prefix) :])))

    result: list[F192] = []
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
    proof: LigeritoProofData,
    log_n: int,
    initial_rate: int,
    target: F192,
    root: bytes,
    evaluate_basis: Callable[[Sequence[F192], int], Sequence[F192]],
) -> None:
    """Verify the base-field multilevel opening with a one-point terminal check."""
    config = derive_config(log_n, initial_rate)
    levels = len(config.folds)
    require(len(proof.recursive_roots) == levels - 1, "wrong Ligerito root count")
    require(len(proof.recursive) == levels - 2, "wrong Ligerito recursive-proof count")
    require(len(proof.grinding_nonces) == levels, "wrong Ligerito nonce count")

    def observe_root(value: bytes) -> None:
        require(len(value) == 32, "invalid Merkle root")
        transcript.observe(F192.from_bytes(value[:24]))
        transcript.observe(F192(int.from_bytes(value[24:], "little")))

    message_index = 0

    def next_quad(claim: F192) -> QuadraticMessage:
        nonlocal message_index
        require(message_index < len(proof.sumcheck), "truncated Ligerito sumcheck")
        message = proof.sumcheck[message_index]
        message_index += 1
        transcript.observe(message.constant)
        transcript.observe(message.quadratic)
        return QuadraticMessage(message.constant, claim + message.quadratic, message.quadratic)

    transcript.observe(target)
    observe_root(root)
    running_target = target
    running_quad = next_quad(target)
    folds: list[F192] = []
    contexts: list[tuple[int, list[int], list[F192], int, F192]] = []
    ood_contexts: list[tuple[tuple[F192, ...], int, F192]] = []
    fold_nonce_index = 0
    ood_index = 0
    current_root = root

    for level, (fold_count, rate) in enumerate(zip(config.folds, config.rates)):
        level_folds: list[F192] = []
        for fold_index in range(fold_count):
            bits = max(0, config.fold_grinding[level] - fold_index)
            if bits:
                require(fold_nonce_index < len(proof.fold_grinding_nonces),
                        "missing Ligerito fold nonce")
                transcript.sponge.check_pow(proof.fold_grinding_nonces[fold_nonce_index], bits)
                fold_nonce_index += 1
            challenge = transcript.sample()
            folds.append(challenge)
            level_folds.append(challenge)
            running_target = running_quad.evaluate(challenge)
            running_quad = next_quad(running_target)

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        if final_level:
            residual = proof.final.residual
            require(len(residual) == 1 << message_log, "wrong Ligerito residual length")
            for value in residual:
                transcript.observe(value)
        else:
            next_root = proof.recursive_roots[level]
            observe_root(next_root)
            for _ in range(config.ood_samples[level + 1]):
                point = tuple(transcript.samples(message_log))
                require(ood_index < len(proof.ood_values), "missing Ligerito OOD value")
                value = proof.ood_values[ood_index]
                ood_index += 1
                transcript.observe(value)
                intro = next_quad(value)
                beta = transcript.sample()
                running_quad = running_quad.add_scaled(intro, beta)
                running_target += beta * value
                ood_contexts.append((point, len(folds), beta))

        transcript.sponge.check_pow(proof.grinding_nonces[level], config.query_grinding[level])
        block_length = 1 << (message_log + rate)
        queries = sample_queries(transcript.sponge, block_length, config.queries[level])
        alpha = transcript.samples(max(0, (len(queries) - 1).bit_length()))
        if level == 0:
            opened = proof.initial
        elif final_level:
            opened = proof.final
        else:
            opened = proof.recursive[level - 1]
        try:
            rows = authenticate_rows(
                current_root,
                block_length,
                queries,
                opened.opened_rows,
                1 << fold_count,
                opened.merkle_proof,
                level == 0,
            )
        except VerificationError as exc:
            raise VerificationError(f"Ligerito level {level}: {exc}") from exc
        enforced = _enforced_sum(rows, level_folds, alpha)

        # Every commitment, including the last one, enters through an intro
        # message before its separation challenge.
        intro = next_quad(enforced)
        beta = transcript.sample()
        running_quad = running_quad.add_scaled(intro, beta)
        running_target += beta * enforced
        contexts.append((message_log, queries, alpha, len(folds), beta))

        if final_level:
            # Finish the remaining sumcheck rounds and close on one evaluation
            # of every basis at the resulting point.
            tail_folds: list[F192] = []
            for round_index in range(message_log):
                challenge = transcript.sample()
                running_target = running_quad.evaluate(challenge)
                tail_folds.append(challenge)
                if round_index + 1 < message_log:
                    running_quad = next_quad(running_target)
            require(message_index == len(proof.sumcheck), "trailing Ligerito sumcheck messages")
            require(ood_index == len(proof.ood_values), "trailing Ligerito OOD values")
            require(fold_nonce_index == len(proof.fold_grinding_nonces),
                    "trailing Ligerito fold nonces")
            weight_values = list(evaluate_basis(list(folds) + tail_folds, 0))
            require(len(weight_values) == 1, "basis point evaluation has the wrong length")
            weight = weight_values[0]
            for context_log, context_queries, context_alpha, start, separation in contexts:
                fixed = context_log - message_log
                point = list(folds[start : start + fixed]) + tail_folds
                induced = _induced_residual(
                    context_log,
                    context_queries,
                    context_alpha,
                    point,
                    0,
                )
                require(len(induced) == 1, "induced point evaluation has the wrong length")
                weight += separation * induced[0]
            for point, start, separation in ood_contexts:
                fixed = len(point) - message_log
                scale = separation
                for expected, actual in zip(point[:fixed], folds[start : start + fixed]):
                    scale *= ONE + expected + actual
                for expected, actual in zip(point[fixed:], tail_folds):
                    scale *= ONE + expected + actual
                weight += scale
            terminal = weight * mle_eval(residual, tail_folds)
            require(terminal == running_target, "Ligerito terminal check failed")
            return
        current_root = next_root

    raise VerificationError("Ligerito verification ended without a terminal level")

# Flock reduction -------------------------------------------------------------

PHI_BASIS = (
    F192(0x0000000000000001),
    F192(0x033CE8BEDDC8A656),
    F192(0x512620375ED2A108),
    F192(0x0C9E636090AAFC01),
    F192(0xBA4F3CD82801769C),
    F192(0xBA26E7904ADB4A47),
    F192(0x467698598926DC01),
    F192(0x4418AE808B28BDD0),
)
PHI = tuple(sum((PHI_BASIS[bit] for bit in range(8) if value >> bit & 1), ZERO)
            for value in range(256))
_MEDIUM_GENERATOR = F192.new(
    0x243F6A8885A308D3,
    0x13198A2E03707344,
    0xA4093822299F31D0,
)
_MEDIUM_POWERS = (
    _MEDIUM_GENERATOR,
    _MEDIUM_GENERATOR ** 2,
    _MEDIUM_GENERATOR ** 4,
    _MEDIUM_GENERATOR ** 8,
)
FIXED_CHALLENGES = (
    PHI[0xF7], PHI[0x53], PHI[0xB5],
    *tuple(value / (ONE + value) for value in _MEDIUM_POWERS),
)


@lru_cache(maxsize=None)
def _denominators(nodes: tuple[F192, ...]) -> tuple[F192, ...]:
    result = []
    for index, node in enumerate(nodes):
        denominator = ONE
        for other_index, other in enumerate(nodes):
            if other_index != index:
                denominator *= node + other
        result.append(denominator.inv())
    return tuple(result)


def lagrange_weights(nodes: Sequence[F192], point: F192) -> list[F192]:
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


def lagrange_interpolate(nodes: Sequence[F192], values: Sequence[F192], point: F192) -> F192:
    weights = lagrange_weights(nodes, point)
    return sum((weight * value for weight, value in zip(weights, values)), ZERO)


def quirky_weights(skip_point: F192, rest: Sequence[F192]) -> list[F192]:
    skip = lagrange_weights(PHI[:64], skip_point)
    tail = build_eq(rest)
    return [a * b for b in tail for a in skip]


@dataclass(frozen=True)
class QuirkyPoint:
    skip: F192
    inner: tuple[F192, ...]
    outer: tuple[F192, ...]

    @property
    def ring_tail(self) -> tuple[F192, ...]:
        return self.inner + self.outer


@dataclass(frozen=True)
class ZClaim:
    point: QuirkyPoint
    value: F192


@dataclass(frozen=True)
class ZerocheckResult:
    skip: F192
    rounds: tuple[F192, ...]
    equality_tail: tuple[F192, ...]
    a: F192
    b: F192
    c: F192


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
    value: F192


@dataclass(frozen=True)
class Reduction:
    ab: ZClaim
    c: ZClaim


def _claim_weights(point: QuirkyPoint) -> list[F192]:
    return lagrange_weights(PHI[:64], point.skip)


RING_MAP_SHIFTS = (32, 16, 8, 4, 2, 1)


def _coordinate_weights(challenges: Sequence[F192]) -> list[F192]:
    """`ring_switch::build_coordinate_weights`: the images `Phi(basis_w)` of the
    F2-coordinate basis under the six composed two-term linearized maps. The
    verifier weights the transposed columns with these; the guest applies the
    same composition directly."""
    require(len(challenges) == len(RING_MAP_SHIFTS), "wrong ring-map challenge count")
    weights = []
    for w in range(192):
        # b_w has only bit w set: limb w // 64, bit w % 64.
        limbs = [0, 0, 0]
        limbs[w // 64] = 1 << (w % 64)
        element = F192(*limbs)
        for challenge, shift in zip(challenges, RING_MAP_SHIFTS):
            frobenius = element
            for _ in range(shift):
                frobenius *= frobenius
            element += challenge * frobenius
        weights.append(element)
    return weights


def _transpose(values: Sequence[F192]) -> list[F192]:
    require(len(values) == 64, "ring-switch slice has the wrong length")
    output = [0] * 192
    for row, value in enumerate(values):
        bits = int(value)
        while bits:
            bit = (bits & -bits).bit_length() - 1
            output[bit] ^= 1 << row
            bits &= bits - 1
    return [F192(value) for value in output]


def _linear_map(value: F192, weights: Sequence[F192]) -> F192:
    result = ZERO
    bits = int(value)
    while bits:
        bit = (bits & -bits).bit_length() - 1
        result += weights[bit]
        bits &= bits - 1
    return result


def _ring_weight(
    suffix_point: Sequence[F192],
    query: Sequence[F192],
    coordinate_weights: Sequence[F192],
) -> F192:
    """Evaluate the transparent ring-switch weight at one query point."""
    require(len(suffix_point) == len(query), "ring-switch query dimension mismatch")
    suffix_tensor = build_eq(suffix_point)
    query_tensor = build_eq(query)
    return sum(
        (query_weight * _linear_map(suffix_weight, coordinate_weights)
         for query_weight, suffix_weight in zip(query_tensor, suffix_tensor)),
        ZERO,
    )


def verify_stacked_opening(
    transcript: Transcript,
    opening: LigeritoOpening,
    root: bytes,
    stack_log: int,
    initial_rate: int,
    qpkd_offset: int,
    qpkd_variables: int,
    reduction: Reduction,
    point_claims: Sequence[tuple[Sequence[F192], F192]],
) -> None:
    """Bind both ring-switched claims and all ordinary stack point claims."""
    ring_claims = (reduction.ab, reduction.c)
    require(len(opening.ring_switches) == len(ring_claims), "wrong ring-switch proof count")
    slices: list[Sequence[F192]] = []
    for claim, values in zip(ring_claims, opening.ring_switches):
        require(len(values) == 64, "ring-switch proof has the wrong width")
        for value in values:
            transcript.observe(value)
        expected = sum((a * b for a, b in zip(_claim_weights(claim.point), values)), ZERO)
        require(expected == claim.value, "ring-switch claim mismatch")
        slices.append(values)

    map_challenges = [transcript.sample() for _ in RING_MAP_SHIFTS]
    coordinate_weights = _coordinate_weights(map_challenges)
    ring_values = [sum((a * b for a, b in zip(_transpose(values), coordinate_weights)), ZERO)
                   for values in slices]
    ring_scales = transcript.samples(2)
    target = sum((scale * value for scale, value in zip(ring_scales, ring_values)), ZERO)

    for _, value in point_claims:
        transcript.observe(value)
    point_scales = transcript.samples(len(point_claims))
    target += sum((scale * value for scale, (_, value) in zip(point_scales, point_claims)), ZERO)

    selector = qpkd_offset >> qpkd_variables

    def evaluate_basis(prefix: Sequence[F192], residual_log: int) -> list[F192]:
        shared_ring = None
        if len(prefix) >= qpkd_variables:
            shared_ring = sum(
                (scale * _ring_weight(
                    claim.point.ring_tail,
                    prefix[:qpkd_variables],
                    coordinate_weights,
                ) for scale, claim in zip(ring_scales, ring_claims)),
                ZERO,
            )
        result = []
        for vertex in range(1 << residual_log):
            point = list(prefix) + [F192(vertex >> bit & 1) for bit in range(residual_log)]
            low, high = point[:qpkd_variables], point[qpkd_variables:]
            selector_weight = ONE
            for bit, challenge in enumerate(high):
                selector_weight *= challenge if selector >> bit & 1 else ONE + challenge
            ring_value = shared_ring if shared_ring is not None else sum(
                (scale * _ring_weight(claim.point.ring_tail, low, coordinate_weights)
                 for scale, claim in zip(ring_scales, ring_claims)), ZERO)
            value = selector_weight * ring_value
            for scale, (claim_point, _) in zip(point_scales, point_claims):
                require(len(claim_point) == len(point), "stack point has the wrong dimension")
                factor = ONE
                for expected, challenge in zip(claim_point, point):
                    factor *= ONE + expected + challenge
                value += scale * factor
            result.append(value)
        return result

    verify_ligerito(
        transcript,
        opening.ligerito,
        stack_log,
        initial_rate,
        target,
        root,
        evaluate_basis,
    )


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
    a: F192,
    b: F192,
    transcript: Transcript,
) -> LincheckResult:
    """Replay the fixed BLAKE3 matrix reduction."""
    alpha = transcript.sample()
    inner_weights = quirky_weights(point.skip, point.inner)
    beta = transcript.sample()
    running = alpha * a + b + beta
    challenges = []
    for _ in range(8):
        at_one, at_infinity = transcript.scalars(2)
        at_zero = running + at_one
        linear = at_zero + at_one + at_infinity
        challenge = transcript.sample()
        running = at_infinity * challenge * challenge + linear * challenge + at_zero
        challenges.append(challenge)
    partial = transcript.scalars(64)
    rest_weights = build_eq(tuple(reversed(challenges)))
    column_weights = [value * weight for weight in rest_weights for value in partial]
    terminal = blake3_bilinear(alpha, inner_weights, column_weights)
    terminal += beta * column_weights[512]
    require(terminal == running,
           "Flock lincheck terminal mismatch")
    skip = transcript.sample()
    value = sum((x * y for x, y in zip(lagrange_weights(PHI[:64], skip), partial)), ZERO)
    return LincheckResult(QuirkyPoint(skip, tuple(reversed(challenges)), point.outer), value)


def blake3_bilinear(
    alpha: F192,
    row_weights: Sequence[F192],
    column_weights: Sequence[F192],
) -> F192:
    """Evaluate the two BLAKE3 R1CS matrix forms by walking the circuit."""
    size = 1 << 14
    require(len(row_weights) == size, "bad BLAKE3 row-weight vector")
    require(len(column_weights) == size, "bad BLAKE3 column-weight vector")
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
    left_total = ZERO
    right_total = ZERO
    constant_rows = ZERO

    def slots(base: int) -> tuple[F192, ...]:
        return tuple(column_weights[base + bit] for bit in range(32))

    empty_word = (ZERO,) * 32

    def literal(value: int) -> tuple[F192, ...]:
        return tuple(column_weights[constant] if value >> bit & 1 else ZERO
                     for bit in range(32))

    def xor(x: Sequence[F192], y: Sequence[F192]) -> tuple[F192, ...]:
        return tuple(a + b for a, b in zip(x, y))

    def rotate_right(word: Sequence[F192], amount: int) -> tuple[F192, ...]:
        return tuple(word[(bit + amount) & 31] for bit in range(32))

    def add(x: Sequence[F192], y: Sequence[F192], carry_base: int) -> tuple[F192, ...]:
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

    def linear_rows(values: Sequence[F192], base: int) -> None:
        nonlocal left_total, constant_rows
        for bit in range(32):
            left_total += row_weights[base + bit] * values[bit]
            constant_rows += row_weights[base + bit]

    for base, length in ((0, 256), (message_base, 512), (counter_low, 64),
                         (block_length, 32), (flags, 32)):
        for row in range(base, base + length):
            left_total += row_weights[row] * column_weights[row]
            constant_rows += row_weights[row]

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
            linear_rows(b_new, b_base)
            linear_rows(d2, d_base)
            state[lane_a] = a2
            state[lane_b] = slots(b_base)
            state[lane_c] = c2
            state[lane_d] = slots(d_base)
        message_order = [message_order[index] for index in permutation]

    for word in range(8):
        low = xor(state[word], state[word + 8])
        high = xor(state[word + 8], slots(32 * word))
        linear_rows(low, 256 + 32 * word)
        linear_rows(high, output_high + 32 * word)

    constant_weight = column_weights[constant]
    left_total += constant_weight * row_weights[constant]
    right_total += constant_weight * (constant_rows + row_weights[constant])
    return alpha * left_total + right_total

# Complete VM verification and CLI -------------------------------------------


def _selector_point(selector: int, length: int) -> tuple[F192, ...]:
    return tuple(F192(selector >> bit & 1) for bit in range(length))


def verify_execution(statement: dict[str, Any], proof: Proof) -> None:
    """Verify a complete leanVM-b execution proof against its public statement."""
    program = Program.parse(statement)
    encoded_input = statement.get("public_input")
    if not isinstance(encoded_input, list) or len(encoded_input) != 2:
        raise VerificationError("public input must contain two field elements")
    public_input = tuple(parse_field(value) for value in encoded_input)
    transcript = Transcript(proof, b"leanvm-b", program.transcript_statement(public_input))

    announced = transcript.scalars(9)
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced size has a nonzero high limb")
    log_memory = announced[0].c0
    row_counts = tuple(value.c0 for value in announced[1:8])
    log_inverse_rate = announced[8].c0
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    layout = build_layout(program, log_memory, row_counts)

    root_words = transcript.scalars(2)
    require(all(word.c2 == 0 for word in root_words), "commitment root has a nonzero top limb")
    root = b"".join(
        limb.to_bytes(8, "little")
        for limb in (root_words[0].c0, root_words[0].c1, root_words[1].c0, root_words[1].c1)
    )
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
    public_low, public_high = transcript.scalars(2)
    public_point = [ZERO] * layout.placements[0].variables
    public_point[0] = public_challenge
    public_value = interpolate(public_input[0], public_input[1], public_challenge)
    y = F192(0, 1)
    public_top = (public_value + public_low + y * public_high) / (y * y)
    claims.extend(
        ColumnClaim(column, tuple(public_point), value)
        for column, value in enumerate((public_low, public_high, public_top))
    )

    point_claims: list[tuple[tuple[F192, ...], F192]] = []
    qpkd = layout.placements[5]
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
            require(len(claim.point) + 8 == qpkd.variables, "BLAKE3 slot claim dimension mismatch")
            selector = qpkd.offset >> qpkd.variables
            full_point = (
                _selector_point(slot, 8)
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
        log_inverse_rate,
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
