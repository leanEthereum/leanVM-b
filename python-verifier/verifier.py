"""Dependency-free verifier for leanVM-b execution proofs.

The command-line interface consumes a public statement JSON file and the
project's bincode proof. No prover-side auxiliary data is accepted. The file is
ordered along the verification path: arithmetic and hashing, proof transport,
GKR/bus/AIR checks, VM layout, Ligerito, Flock, and final orchestration.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from math import ceil, isfinite, log2, nextafter, sqrt
from pathlib import Path
from struct import pack, unpack
from typing import Any, Callable, Iterable, Sequence


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
    return ((folded & MASK64) ^ overflow ^ (overflow << 1) ^ (overflow << 3) ^ (overflow << 4)) & MASK64


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
    def new(cls, c0: int, c1: int, c2: int = 0) -> F192:
        return cls(c0, c1, c2)

    @classmethod
    def from_bytes(cls, data: bytes) -> F192:
        require(len(data) == 24, "a field element must contain exactly 24 bytes")
        return cls(*(int.from_bytes(data[offset : offset + 8], "little") for offset in (0, 8, 16)))

    def to_bytes(self) -> bytes:
        return b"".join(limb.to_bytes(8, "little") for limb in (self.c0, self.c1, self.c2))

    @staticmethod
    def _coerce(other: object) -> F192:
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

    def __add__(self, other: object) -> F192:
        rhs = self._coerce(other)
        return F192(self.c0 ^ rhs.c0, self.c1 ^ rhs.c1, self.c2 ^ rhs.c2)

    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__

    def __neg__(self) -> F192:
        return self

    def __mul__(self, other: object) -> F192:
        rhs = self._coerce(other)
        p0 = _base_mul(self.c0, rhs.c0)
        p1 = _base_mul(self.c0, rhs.c1) ^ _base_mul(self.c1, rhs.c0)
        p2 = _base_mul(self.c0, rhs.c2) ^ _base_mul(self.c1, rhs.c1) ^ _base_mul(self.c2, rhs.c0)
        p3 = _base_mul(self.c1, rhs.c2) ^ _base_mul(self.c2, rhs.c1)
        p4 = _base_mul(self.c2, rhs.c2)
        return F192(p0 ^ p3, p1 ^ p3 ^ p4, p2 ^ p4)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> F192:
        if exponent < 0:
            return self.inv() ** -exponent
        base, out, n = self, ONE, exponent
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> F192:
        require(bool(self), "division by zero in GF(2^192)")
        return self ** ((1 << 192) - 2)

    def __truediv__(self, other: object) -> F192:
        rhs = self._coerce(other)
        return self * rhs.inv()

    def __rtruediv__(self, other: object) -> F192:
        lhs = self._coerce(other)
        return lhs * self.inv()

    def __repr__(self) -> str:
        return f"F192(0x{self.c2:016x}{self.c1:016x}{self.c0:016x})"


ZERO = F192(0)
ONE = F192(1)
GEN = F192(2)
Y = F192(0, 1)  # the tower generator, y^3 = y + 1


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
    v = (
        list(cv)
        + list(BLAKE3_IV[:4])
        + [
            counter & MASK32,
            (counter >> 32) & MASK32,
            block_len,
            flags,
        ]
    )
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
    return tuple((v[i] ^ v[i + 8]) & MASK32 for i in range(8)) + tuple((v[i + 8] ^ cv[i]) & MASK32 for i in range(8))


def _words(block: bytes) -> tuple[int, ...]:
    return unpack("<16I", block.ljust(64, b"\0"))


def _parent_output(left: Sequence[int], right: Sequence[int], flags: int = 0) -> tuple[tuple[int, ...], tuple[int, ...], int, int, int]:
    return BLAKE3_IV, tuple(left) + tuple(right), 0, 64, flags | PARENT


def _output_cv(output: tuple[Sequence[int], Sequence[int], int, int, int]) -> tuple[int, ...]:
    cv, block, counter, block_len, flags = output
    return blake3_compress_words(cv, block, counter, block_len, flags)[:8]


def _output_root(output: tuple[Sequence[int], Sequence[int], int, int, int]) -> bytes:
    cv, block, _counter, block_len, flags = output
    words = blake3_compress_words(cv, block, 0, block_len, flags | ROOT)
    return pack("<16I", *words)[:32]


def _chunk_output(chunk: bytes, chunk_counter: int) -> tuple[Sequence[int], Sequence[int], int, int, int]:
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


def digest_words(digest: bytes) -> tuple[int, int, int, int]:
    """Read the first 32 bytes of a digest as four little-endian 64-bit words."""
    return (
        int.from_bytes(digest[0:8], "little"),
        int.from_bytes(digest[8:16], "little"),
        int.from_bytes(digest[16:24], "little"),
        int.from_bytes(digest[24:32], "little"),
    )


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


def _ceil_log(value: int) -> int:
    return max(0, (value - 1).bit_length())


def stack_offsets(sizes: Sequence[int | None]) -> tuple[list[int], int]:
    """Stack 2^size blocks largest first at aligned offsets (doc sec:stacking).

    The one layout rule, shared by the witness columns and the three leaf
    vectors; a None size marks a virtual entry, which takes no room. Returns the
    per-entry offsets and the log of the padded total.
    """
    offsets = [0] * len(sizes)
    total = 0
    present = [(index, size) for index, size in enumerate(sizes) if size is not None]
    for index, size in sorted(present, key=lambda item: (-item[1], item[0])):
        offsets[index] = total
        total += 1 << size
    return offsets, _ceil_log(max(total, 1))


def eq_eval(left: Sequence[F192], right: Sequence[F192]) -> F192:
    require(len(left) == len(right), "eq: dimension mismatch")
    result = ONE
    for x, y in zip(left, right):
        result *= ONE + x + y
    return result


QUAD_NODES = (ZERO, ONE, GEN, GEN * GEN)


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


# Proof transport ------------------------------------------------------------


class BinaryReader:
    """Strict reader for bincode's fixed-width encoding used by the project."""

    def __init__(self, data: bytes):
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

    def field(self) -> F192:
        return F192.from_bytes(self.take(24))

    def fields(self) -> list[F192]:
        length = self.u64()
        require(length <= self.remaining // 24, "invalid field-vector length")
        return [self.field() for _ in range(length)]

    def base_fields(self) -> list[int]:
        length = self.u64()
        require(length <= self.remaining // 8, "invalid base-field-vector length")
        return [self.u64() for _ in range(length)]

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
class Opening:
    """One level's opened rows and the octopus authenticating them.

    Level 0 committed the K-valued witness, so its rows are base-field words;
    every deeper level committed a folded E-valued one.
    """

    opened_rows: tuple[tuple[FieldValue, ...], ...]
    merkle_proof: tuple[bytes, ...]

    @classmethod
    def read(cls, reader: BinaryReader, base_field: bool) -> Opening:
        row_count = reader.u64()
        require(row_count <= reader.remaining // 8, "invalid opened-row count")
        read_row = reader.base_fields if base_field else reader.fields
        rows = tuple(tuple(read_row()) for _ in range(row_count))
        return cls(rows, reader.hashes())


@dataclass(frozen=True)
class SumcheckMessage:
    constant: F192
    quadratic: F192


@dataclass(frozen=True)
class LigeritoProofData:
    initial: Opening
    recursive_roots: tuple[bytes, ...]
    recursive: tuple[Opening, ...]
    residual: tuple[F192, ...]  # the last level's plaintext multilinear
    final: Opening
    sumcheck: tuple[SumcheckMessage, ...]
    grinding_nonces: tuple[int, ...]
    ood_values: tuple[F192, ...]
    fold_grinding_nonces: tuple[int, ...]

    @classmethod
    def read(cls, reader: BinaryReader) -> LigeritoProofData:
        initial = Opening.read(reader, base_field=True)
        roots = reader.hashes()
        count = reader.u64()
        require(count <= 32, "too many Ligerito levels")
        recursive = tuple(Opening.read(reader, base_field=False) for _ in range(count))
        residual = tuple(reader.fields())
        final = Opening.read(reader, base_field=False)
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
        return cls(initial, roots, recursive, residual, final, sumcheck, nonces, ood_values, fold_nonces)


@dataclass(frozen=True)
class LigeritoOpening:
    ring_switches: tuple[tuple[F192, ...], ...]
    ligerito: LigeritoProofData

    @classmethod
    def read(cls, reader: BinaryReader) -> LigeritoOpening:
        count = reader.u64()
        require(count <= 16, "too many ring-switch proofs")
        ring_switches = tuple(tuple(reader.fields()) for _ in range(count))
        return cls(ring_switches, LigeritoProofData.read(reader))


@dataclass(frozen=True)
class Proof:
    stream: tuple[F192, ...]
    openings: tuple[LigeritoOpening, ...]

    @classmethod
    def from_bincode(cls, data: bytes) -> Proof:
        reader = BinaryReader(data)
        stream = tuple(reader.fields())
        count = reader.u64()
        require(count <= 8, "too many PCS openings")
        openings = tuple(LigeritoOpening.read(reader) for _ in range(count))
        reader.finish()
        return cls(stream, openings)

    @classmethod
    def load(cls, path: str | Path) -> Proof:
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
    return digest_words(digest)


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
            claim = quartic_eval_from_eq(claim, prior, message[0], message[1], message[2], message[3], challenge)

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
    committed global columns; ``product`` is ``(a, b, k)`` for ``g^k * col_a *
    col_b``, an address ``fp*g^o`` carried without committing it; ``public`` is a
    dense public multilinear table; ``terms`` is a sum of the above, any degree-2
    form over a table's columns, which is what carries a value a row derives from
    its columns without committing one for it.
    """

    constant: F192 | None = None
    column: int | None = None
    generator_column: int | None = None
    product: tuple[int, int, int] | None = None
    index: bool = False
    public: tuple[F192, ...] | None = None
    terms: tuple["Coordinate", ...] | None = None

    def __post_init__(self) -> None:
        sources = [value for value in vars(self).values() if value is not None and value is not False]
        require(len(sources) == 1, "a bus coordinate must have exactly one source")


@dataclass(frozen=True)
class BusBlock:
    log_rows: int
    coordinates: tuple[Coordinate, ...]
    owner: tuple[int, int] | None = None


@dataclass(frozen=True)
class BusLayout:
    depth: int
    offsets: tuple[int, ...]


def bus_layout(blocks: Sequence[BusBlock]) -> BusLayout:
    offsets, depth = stack_offsets([block.log_rows for block in blocks])
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


# The bytecode is one multilinear over sixteen slots, nine of them used (doc
# sec:e2e-bc), so its point carries four selector coordinates above the index.
N_BYTECODE_SELECTORS = 4


@dataclass(frozen=True)
class BytecodeClaim:
    point: tuple[F192, ...]
    value: F192


@dataclass
class BusForm:
    """A table's bus contribution as a degree-2 form over its committed columns.

    ``products`` holds ``(a, b, coefficient)`` in local indices, contributed by the
    product coordinates. The form stays degree 2, which the AIR identities already
    are, so the batch's round polynomial does not grow.
    """

    coefficients: list[F192]
    products: list[tuple[int, int, F192]] = field(default_factory=list)
    constant: F192 = ZERO

    def evaluate(self, values: Sequence[F192]) -> F192:
        require(len(values) == len(self.coefficients), "bus form width mismatch")
        return sum(
            (coefficient * value for coefficient, value in zip(self.coefficients, values)),
            self.constant,
        ) + sum(
            (coefficient * values[a] * values[b] for a, b, coefficient in self.products),
            ZERO,
        )


def _accumulate_form(coordinate: Coordinate, weight: F192, form: BusForm, base: int) -> None:
    """Accumulate one coordinate of a table's block into that table's form.

    A sum's children share their coordinate's alpha-power, so a derived value lands
    as the several coefficients and products it is made of.
    """
    if coordinate.constant is not None:
        form.constant += weight * coordinate.constant
    elif coordinate.column is not None:
        form.coefficients[coordinate.column - base] += weight
    elif coordinate.generator_column is not None:
        form.coefficients[coordinate.generator_column - base] += weight * GEN
    elif coordinate.product is not None:
        a, b, exponent = coordinate.product
        form.products.append((a - base, b - base, weight * _gpow(exponent)))
    elif coordinate.terms is not None:
        for term in coordinate.terms:
            _accumulate_form(term, weight, form, base)
    else:
        raise VerificationError("table bus block has a virtual coordinate")


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
        selector_bits = tuple(F192((selector >> bit) & 1) for bit in range(layout.depth - block.log_rows))
        selector_weight = eq_eval(selector_bits, high)
        selector_sum += selector_weight

        if block.owner is not None:
            table, base = block.owner
            form = forms[table]
            form.constant += selector_weight * gamma
            coefficient = ONE
            for coordinate in block.coordinates:
                _accumulate_form(coordinate, selector_weight * coefficient, form, base)
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


def _public_evaluations(blocks: Sequence[BusBlock], point: Sequence[F192]) -> tuple[int, list[F192]]:
    """The public columns' evaluations and the height they sit at.

    Only the bytecode seed block has any: the program is public, so the verifier
    forms its nine encoding columns itself (doc sec:bytecode).
    """
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
    point: tuple[F192, ...]  # the GKR point zeta, which the zerocheck reuses
    forms: tuple[tuple[BusForm, ...], ...]  # forms[side][table]
    totals: tuple[F192, F192, F192]  # what the tables owe each side, derived
    bytecode_claim: BytecodeClaim


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

    alpha = transcript.sample()
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
    forms = tuple(tuple(BusForm([ZERO] * width) for width in WIDTHS) for _ in range(3))
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

    # The claim on the stacked bytecode polynomial. Nothing here consumes it: the
    # program is public, so the nine columns above were evaluated directly. It is
    # the recursive verifier that defers this claim instead (doc sec:recursion),
    # and it is formed here because its transcript steps are shared.
    public_log_rows, public_values = _public_evaluations(push, product.point)
    for value in public_values:
        transcript.observe(value)
    selector_point = transcript.samples(N_BYTECODE_SELECTORS)
    bytecode_claim = BytecodeClaim(
        tuple(product.point[:public_log_rows]) + tuple(selector_point),
        _stack_public_evaluations(public_values, selector_point),
    )
    return BusResult(tuple(claims), product.point, forms, (totals[0], totals[1], totals[2]), bytecode_claim)


# Batched AIR zerocheck ------------------------------------------------------


@dataclass(frozen=True)
class Air:
    """One table at its announced height, with the bus forms it owes each side."""

    table: Table
    log_height: int
    forms: tuple[BusForm, ...]

    def evaluate(self, constraint_powers: Sequence[F192], form_powers: Sequence[F192], columns: Sequence[F192]) -> F192:
        """This table's share of the batch's summand: its identities, then its bus forms."""
        terms = self.table.constraints(lambda name: columns[self.table.col(name)])
        require(len(constraint_powers) == len(terms), "AIR constraint weight mismatch")
        identities = sum((weight * term for weight, term in zip(constraint_powers, terms)), ZERO)
        buses = sum((weight * form.evaluate(columns) for weight, form in zip(form_powers, self.forms)), ZERO)
        return identities + buses


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
    constraint_powers: Sequence[F192],
    form_powers: Sequence[F192],
    equality_point: Sequence[F192],
    target: F192,
    transcript: Transcript,
) -> list[AirClaim]:
    depth = max((air.log_height for air in airs), default=0)
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
        claim = lagrange_interpolate(QUAD_NODES, message, challenge)
        for table_index, air in enumerate(airs):
            weights[table_index] *= equality if air.log_height > variable else challenge

    final = ZERO
    cursor = 0
    claims: list[AirClaim] = []
    for table_index, air in enumerate(airs):
        evaluations = tuple(transcript.scalars(air.table.width))
        own = constraint_powers[cursor : cursor + air.table.n_constraints]
        cursor += air.table.n_constraints
        final += weights[table_index] * air.evaluate(own, form_powers, evaluations)
        claims.append(AirClaim(tuple(point[: air.log_height]), evaluations))
    require(final == claim, "AIR terminal mismatch")
    return claims


# VM statement, layout, and AIR -----------------------------------------------

FAMILY_DIGEST = bytes.fromhex("afed7472c6f771a857599272ff33a4da86b21f2600f057fa0da797d15863eb58")
MAX_LOG_BYTECODE = 32

# The columns no instruction table owns (doc sec:e2e-unrolled, Commitment): the
# memory image's three limbs, the two finalize counts, and flock's packed
# witness. They come first in the global column numbering, the tables after.
GLOBAL_COLUMNS = ("mem_0", "mem_1", "mem_2", "mem_final_cnt", "bytecode_final_cnt", "qflock")
MEM_0, MEM_1, MEM_2, MEM_FINAL_CNT, BYTECODE_FINAL_CNT, QFLOCK = range(len(GLOBAL_COLUMNS))

# flock proves one BLAKE3 compression over 2^14 witness bits, packed 64 to a
# K-element, so q_flock has QFLOCK_SLOT_BITS low variables selecting the word
# within an instance and the table's log height above them (doc sec:tab-blake3).
FLOCK_LOG_BITS = 14
PACKED_BITS = 64  # bits per committed K-element (doc sec:ringswitch)
QFLOCK_SLOT_BITS = FLOCK_LOG_BITS - 6


def parse_field(value: Any) -> F192:
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


def _u32(value: Any, name: str) -> int:
    require(
        isinstance(value, int) and not isinstance(value, bool) and 0 <= value < 1 << 32,
        f"{name} must be a 32-bit unsigned integer",
    )
    return value


# The ISA discriminant the program digest binds, per instruction; DEREF's comes
# from its store mode instead.
DIGEST_TAGS = {"xor": 0, "mul": 1, "set": 2, "jump": 6, "blake3": 7, "pack64x2": 9}
DEREF_MODE_TAGS = {"cell": 3, "pc": 4, "fp": 5}


@dataclass(frozen=True)
class Operation:
    """One parsed instruction, normalized to what the two encodings need.

    ``offsets`` are the validated frame offsets in bytecode-slot order and
    ``lanes`` the slots that follow them (SET's immediate limbs, DEREF's mode
    flags, BLAKE3's metadata). ``tag`` is the ISA discriminant the program digest
    binds, which is not the bus opcode: DEREF carries its store mode instead.
    """

    name: str
    offsets: tuple[int, ...]
    lanes: tuple[F192, ...]
    immediate: F192
    tag: int

    @classmethod
    def parse(cls, data: dict[str, Any]) -> Operation:
        require(isinstance(data, dict), "each program operation must be an object")
        name = str(data.get("op", "")).lower()
        require(name in OPCODES, f"unknown operation {name!r}")

        def offsets_of(*keys: str) -> tuple[int, ...]:
            return tuple(_u32(data[key], f"{name}.{key}") for key in keys)

        lanes: tuple[F192, ...] = ()
        immediate, tag = ZERO, DIGEST_TAGS.get(name, 0)
        if name in {"xor", "mul", "pack64x2"}:
            offsets = offsets_of("a", "b", "c")
        elif name == "set":
            offsets = offsets_of("o")
            immediate = parse_field(data["k"])
            lanes = (F192(immediate.c0), F192(immediate.c1), F192(immediate.c2))
        elif name == "deref":
            offsets = offsets_of("alpha", "beta", "gamma")
            mode = str(data["mode"]).lower()
            require(mode in DEREF_MODE_TAGS, "deref.mode must be cell, pc, or fp")
            tag = DEREF_MODE_TAGS[mode]
            lanes = (ONE if mode == "pc" else ZERO, ONE if mode == "fp" else ZERO)
        elif name == "jump":
            offsets = offsets_of("oc", "od", "of")
        else:
            inputs = data["ins"]
            require(isinstance(inputs, (list, tuple)) and len(inputs) == 4, "blake3.ins must contain four addresses")
            offsets = tuple(_u32(value, f"blake3.ins[{index}]") for index, value in enumerate(inputs))
            offsets += offsets_of("cv", "out")
            immediate = parse_field(data["metadata"])
            lanes = (F192(immediate.c0), F192(immediate.c1))
        return cls(name, offsets, lanes, immediate, tag)


@dataclass(frozen=True)
class Program:
    operations: tuple[Operation, ...]

    @classmethod
    def parse(cls, data: dict[str, Any]) -> Program:
        require(isinstance(data, dict), "the public statement must be an object")
        encoded = data.get("program")
        if not isinstance(encoded, list):
            raise VerificationError("program must be an array")
        operations = tuple(Operation.parse(item) for item in encoded)
        require(bool(operations) and not len(operations) & (len(operations) - 1), "program length must be a nonzero power of two")
        # One of the public instance caps the counting arguments rest on (doc
        # sec:bytecode, sec:memchan): reject an oversized announcement outright.
        require(len(operations) <= 1 << MAX_LOG_BYTECODE, "program exceeds the bytecode cap")
        return cls(operations)

    def digest(self) -> tuple[int, int, int, int]:
        """The program's binding digest, as the assembler computes it."""
        words = [len(self.operations), 3]
        for op in self.operations:
            a, b, c = (*op.offsets[:3], 0, 0)[:3]
            # BLAKE3 is the only instruction with more than three offsets: its
            # fourth message chunk shares a word with the chaining value, and the
            # output address takes the next.
            x, y = (op.offsets[3] | op.offsets[4] << 32, op.offsets[5]) if op.name == "blake3" else (0, 0)
            k = op.immediate
            words.extend((a | b << 32, c | op.tag << 32, k.c0, k.c1, k.c2, x, y))
        return digest_words(blake3_hash(b"".join(word.to_bytes(8, "little") for word in words)))

    def transcript_statement(self, public_input: Sequence[F192]) -> tuple[F192, ...]:
        program_digest = self.digest()
        seed = blake3_hash(b"leanvm-b-fs-seed-v1" + FAMILY_DIGEST + b"".join(word.to_bytes(8, "little") for word in program_digest))
        words = digest_words(seed)
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
    placements: tuple[Placement, ...]
    stack_log: int
    table_logs: tuple[int, ...]


def _gpow(index: int) -> F192:
    return GEN**index


def _const(value: F192 | int) -> Coordinate:
    return Coordinate(constant=parse_field(value))


def _col(index: int) -> Coordinate:
    return Coordinate(column=index)


def _gcol(index: int) -> Coordinate:
    return Coordinate(generator_column=index)


def _sum(terms: Iterable[Coordinate]) -> Coordinate:
    return Coordinate(terms=tuple(terms))


def _prod(a: int, b: int, exponent: int = 0) -> Coordinate:
    return Coordinate(product=(a, b, exponent))


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

    def state_derived(self, pc: int, fp: int, npc: Coordinate, nfp: Coordinate) -> None:
        self.pair((_const(ONE), npc, nfp), (_const(ONE), _col(pc), _col(fp)))

    def bytecode(self, pc: int, count: int, opcode: int, operands: Sequence[Coordinate]) -> None:
        prefix_push = (_const(GEN * GEN), _col(pc), _gcol(count), _const(_gpow(opcode)))
        prefix_pull = (_const(GEN * GEN), _col(pc), _col(count), _const(_gpow(opcode)))
        self.pair((*prefix_push, *operands), (*prefix_pull, *operands))

    def memory(self, address: Coordinate, count: int, values: Sequence[Coordinate]) -> None:
        self.pair(
            (_const(GEN), address, _gcol(count), *values),
            (_const(GEN), address, _col(count), *values),
        )

    def memory_word(self, address: Coordinate, count: int, lo: int, hi: int, top: int) -> None:
        self.memory(address, count, (_col(lo), _col(hi), _col(top)))

    def memory_base(self, address: Coordinate, count: int, value: int) -> None:
        self.memory(address, count, (_col(value), _const(ZERO), _const(ZERO)))

    def memory_128(self, address: Coordinate, count: int, lo: int, hi: int) -> None:
        self.memory(address, count, (_col(lo), _col(hi), _const(ZERO)))


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
    constraints: Callable[[Callable[[str], F192]], tuple[F192, ...]] = lambda _: ()
    n_constraints: int = 0

    @property
    def width(self) -> int:
        return len(self.columns)

    def col(self, name: str) -> int:
        require(name in self.columns, f"table {self.name} has no column {name!r}")
        return self.columns.index(name)

    def cols(self, *names: str) -> tuple[int, ...]:
        return tuple(self.col(name) for name in names)

    @property
    def count_columns(self) -> tuple[int, ...]:
        return tuple(i for i, name in enumerate(self.columns) if name.startswith("cnt"))


# The tower product in E = K[y]/(y^3+y+1), lane by lane: lane i sums ``x[j]*y[k]``
# over TOWER_LANES[i], the five partials of doc sec:tab-mul folded into
# ``c0 = p0+p3``, ``c1 = p1+p3+p4``, ``c2 = p2+p4``. Written once: MUL's result
# coordinate and JUMP's inverse identity need the same unrolling, and every identity
# is K-valued (doc sec:air), so a word relation is three lane relations.
TOWER_LANES = (
    ((0, 0), (1, 2), (2, 1)),
    ((0, 1), (1, 0), (1, 2), (2, 1), (2, 2)),
    ((0, 2), (1, 1), (2, 0), (2, 2)),
)


def _tower_lanes(x: Sequence[F192], y: Sequence[F192]) -> tuple[F192, ...]:
    """The tower product of two words given as their K-lanes."""
    return tuple(sum((x[j] * y[k] for j, k in lane), ZERO) for lane in TOWER_LANES)


def _arith_result(multiply: bool, a: Sequence[int], b: Sequence[int]) -> tuple[Coordinate, ...]:
    """The result word's three K-lanes as forms over the two operands' lanes.

    XOR is the lane-wise sum; MUL is the tower product, unrolled through TOWER_LANES.
    """
    if not multiply:
        return tuple(_sum((_col(a[i]), _col(b[i]))) for i in range(3))
    return tuple(_sum(_prod(a[j], b[k]) for j, k in lane) for lane in TOWER_LANES)


def _flushes_arith(t: Table) -> Flushes:
    pc, fp, o_a, o_b, o_c, cnt_a, cnt_b, cnt_c, cnt_bc = t.cols("pc", "fp", "o_a", "o_b", "o_c", "cnt_a", "cnt_b", "cnt_c", "cnt_bc")
    va, vb = t.cols("va_0", "va_1", "va_2"), t.cols("vb_0", "vb_1", "vb_2")
    f = Flushes()
    f.state_step(pc, fp)
    f.bytecode(pc, cnt_bc, t.opcode, (_col(o_a), _col(o_b), _col(o_c), _const(ZERO), _const(ZERO)))
    f.memory_word(_prod(fp, o_a), cnt_a, *va)
    f.memory_word(_prod(fp, o_b), cnt_b, *vb)
    # The destination cell's flush carries the result itself, so bus balance is
    # the assertion and the result is no column.
    f.memory(_prod(fp, o_c), cnt_c, _arith_result(t.name == "mul", va, vb))
    return f


def _flushes_set(t: Table) -> Flushes:
    pc, fp, o, cnt, cnt_bc = t.cols("pc", "fp", "o", "cnt", "cnt_bc")
    k = t.cols("k_0", "k_1", "k_2")
    f = Flushes()
    f.state_step(pc, fp)
    # The immediate's three limbs ride the spare operand slots.
    f.bytecode(pc, cnt_bc, t.opcode, (_col(o), *(_col(limb) for limb in k), _const(ZERO)))
    f.memory_word(_prod(fp, o), cnt, *k)
    return f


def _flushes_deref(t: Table) -> Flushes:
    pc, fp, alpha, beta, gamma, f_pc, f_fp, ptr = t.cols("pc", "fp", "alpha", "beta", "gamma", "f_pc", "f_fp", "ptr")
    cnt_ptr, cnt_target, cnt_local, cnt_bc = t.cols("cnt_ptr", "cnt_target", "cnt_local", "cnt_bc")
    v3 = t.cols("v3_0", "v3_1", "v3_2")

    def gated(lane: int) -> list[Coordinate]:
        return [_col(lane), _prod(f_pc, lane), _prod(f_fp, lane)]

    # v2 = (1 + f_pc + f_fp)*v3 + f_pc*(g^2*pc) + f_fp*fp, lane-wise: only the low
    # lane takes the two K-valued sources.
    store = (
        _sum(gated(v3[0]) + [_prod(f_pc, pc, 2), _prod(f_fp, fp)]),
        _sum(gated(v3[1])),
        _sum(gated(v3[2])),
    )
    f = Flushes()
    f.state_step(pc, fp)
    f.bytecode(pc, cnt_bc, t.opcode, (_col(alpha), _col(beta), _col(gamma), _col(f_pc), _col(f_fp)))
    f.memory_base(_prod(fp, alpha), cnt_ptr, ptr)
    f.memory(_prod(ptr, beta), cnt_target, store)
    f.memory_word(_prod(fp, gamma), cnt_local, *v3)
    return f


def _flushes_jump(t: Table) -> Flushes:
    pc, fp, o_c, o_d, o_f, cond, dest, frame, b = t.cols("pc", "fp", "o_c", "o_d", "o_f", "c", "dest", "frame", "b")
    cnt_c, cnt_d, cnt_f, cnt_bc = t.cols("cnt_c", "cnt_d", "cnt_f", "cnt_bc")
    f = Flushes()
    # next_pc = b*dest + (b+1)*g*pc, next_fp = b*frame + (b+1)*fp, both derived.
    f.state_derived(
        pc,
        fp,
        _sum((_prod(b, dest), _prod(b, pc, 1), _gcol(pc))),
        _sum((_prod(b, frame), _prod(b, fp), _col(fp))),
    )
    f.bytecode(pc, cnt_bc, t.opcode, (_col(o_c), _col(o_d), _col(o_f), _const(ZERO), _const(ZERO)))
    # The condition, the destination and the frame are K-valued on every row, taken
    # or not, so each is one K-limb read through literal zeros in the upper lanes.
    f.memory_base(_prod(fp, o_c), cnt_c, cond)
    f.memory_base(_prod(fp, o_d), cnt_d, dest)
    f.memory_base(_prod(fp, o_f), cnt_f, frame)
    return f


def _jump_constraints(get: Callable[[str], F192]) -> tuple[F192, ...]:
    """``b = c*w`` and ``c*(b+1) = 0``: the one quantity no interaction pins.

    No table binds an address, an arithmetic result, a DEREF store or a JUMP
    successor, the bus reading each as a degree-2 coordinate, so JUMP's
    is-nonzero indicator is the whole AIR of the machine. The condition is K-valued
    (its memory read carries literal zeros above the low limb), so both relations
    are single-lane.
    """
    condition, inverse, flag = get("c"), get("w"), get("b")
    return (flag + condition * inverse, condition * (flag + ONE))


def _flushes_blake3(t: Table) -> Flushes:
    pc, fp, cnt_bc = t.cols("pc", "fp", "cnt_bc")
    operands = t.cols("o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "md_0", "md_1")
    f = Flushes()
    f.state_step(pc, fp)
    f.bytecode(pc, cnt_bc, t.opcode, tuple(_col(i) for i in operands))
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
        lo, hi = t.cols(f"{cell}_lo", f"{cell}_hi")
        f.memory_128(_prod(fp, t.col(operand), exponent), t.col(f"cnt_{cell}"), lo, hi)
    return f


def _flushes_pack(t: Table) -> Flushes:
    pc, fp, o_a, o_b, o_c, v_a, v_b, cnt_a, cnt_b, cnt_c, cnt_bc = t.cols(
        "pc", "fp", "o_a", "o_b", "o_c", "v_a", "v_b", "cnt_a", "cnt_b", "cnt_c", "cnt_bc"
    )
    f = Flushes()
    f.state_step(pc, fp)
    f.bytecode(pc, cnt_bc, t.opcode, (_col(o_a), _col(o_b), _col(o_c), _const(ZERO), _const(ZERO)))
    # The literal zeros make the two source range assertions and the destination
    # packing exact through bus balance.
    f.memory_base(_prod(fp, o_a), cnt_a, v_a)
    f.memory_base(_prod(fp, o_b), cnt_b, v_b)
    f.memory_128(_prod(fp, o_c), cnt_c, v_a, v_b)
    return f


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

BLAKE3_COLUMNS = (
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
    Table("blake3", 5, BLAKE3_COLUMNS, _flushes_blake3),
    Table("pack64x2", 6, PACK_COLUMNS, _flushes_pack),
)
BLAKE3 = TABLES[5]

# Where in the flock witness each embedded BLAKE3 limb lives (doc
# sec:tab-blake3): one 64-bit slot per limb, the chaining value first, then the
# digest, the message block and the metadata. Slots 8 and 9 hold the
# compression's high output words, which no memory cell carries.
BLAKE3_SLOT_BY_COLUMN = {
    BLAKE3.col(name): slot
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
    }.items()  # fmt: skip
}

# The instruction names the statement JSON uses are the table names, and the bus
# opcode is the table's index (doc sec:e2e-const).
OPCODES = {table.name: table.opcode for table in TABLES}

# Coordinates 4..11 of a bytecode tuple: eight operand or immediate slots.
N_BYTECODE_OPERANDS = 8

WIDTHS = tuple(t.width for t in TABLES)
# Global column numbering: the shared columns, then each table's block in turn.
BASES = tuple(len(GLOBAL_COLUMNS) + sum(WIDTHS[:table]) for table in range(len(TABLES)))


def _offset_coordinate(coordinate: Coordinate, base: int) -> Coordinate:
    if coordinate.column is not None:
        return _col(base + coordinate.column)
    if coordinate.generator_column is not None:
        return _gcol(base + coordinate.generator_column)
    if coordinate.product is not None:
        a, b, exponent = coordinate.product
        return _prod(base + a, base + b, exponent)
    if coordinate.terms is not None:
        return _sum(_offset_coordinate(term, base) for term in coordinate.terms)
    return coordinate


def _program_columns(program: Program) -> tuple[tuple[F192, ...], ...]:
    """The nine public bytecode columns: the opcode, then eight operand slots.

    Each reference operand is a g-power; the immediate lanes ride the slots the
    instruction leaves spare, and shorter instructions zero the rest.
    """
    columns: list[list[F192]] = [[] for _ in range(1 + N_BYTECODE_OPERANDS)]
    for op in program.operations:
        row = [_gpow(OPCODES[op.name]), *(_gpow(offset) for offset in op.offsets), *op.lanes]
        require(len(row) <= len(columns), f"{op.name} overflows the bytecode encoding")
        for column, value in zip(columns, row + [ZERO] * (len(columns) - len(row))):
            column.append(value)
    return tuple(tuple(column) for column in columns)


def build_layout(program: Program, log_memory: int, table_logs: Sequence[int]) -> Layout:
    require(
        16 <= log_memory <= 32
        and len(table_logs) == 7
        and all(0 <= height <= 32 for height in table_logs)
        # flock sizes its argument to at least 2^3 instances and the BLAKE3 table's value
        # columns share that instance cube, so a smaller height is not expressible.
        and table_logs[5] >= 3,
        "invalid announced table sizes",
    )
    table_logs = list(table_logs)
    bytecode_log = len(program.operations).bit_length() - 1
    public_columns = _program_columns(program)

    push = [
        BusBlock(0, (_const(ONE), _const(ONE), _const(ONE))),
        BusBlock(
            log_memory,
            (_const(GEN), Coordinate(index=True), _const(ONE), _col(MEM_0), _col(MEM_1), _col(MEM_2)),
        ),
        BusBlock(
            bytecode_log,
            (
                _const(GEN * GEN),
                Coordinate(index=True),
                _const(ONE),
                *(_public(column) for column in public_columns),
            ),
        ),
    ]
    pull = [
        BusBlock(0, (_const(ONE), _const(_gpow(len(program.operations) - 1)), _const(ONE))),
        BusBlock(
            log_memory,
            (_const(GEN), Coordinate(index=True), _col(MEM_FINAL_CNT), _col(MEM_0), _col(MEM_1), _col(MEM_2)),
        ),
        BusBlock(
            bytecode_log,
            (
                _const(GEN * GEN),
                Coordinate(index=True),
                _col(BYTECODE_FINAL_CNT),
                *(_public(column) for column in public_columns),
            ),
        ),
    ]
    count: list[BusBlock] = []
    for table, (base, height) in enumerate(zip(BASES, table_logs)):
        flushes = TABLES[table].flushes(TABLES[table])
        for coordinates in flushes.push:
            shifted = tuple(_offset_coordinate(c, base) for c in coordinates)
            push.append(BusBlock(height, shifted, (table, base)))
        for coordinates in flushes.pull:
            shifted = tuple(_offset_coordinate(c, base) for c in coordinates)
            pull.append(BusBlock(height, shifted, (table, base)))
        for local in TABLES[table].count_columns:
            count.append(BusBlock(height, (_col(base + local),), (table, base)))

    # Every column's height, in global numbering; None marks the BLAKE3 value
    # columns, which are committed inside q_flock rather than on their own.
    kappas: list[int | None] = [0] * (len(GLOBAL_COLUMNS) + sum(WIDTHS))
    kappas[MEM_0] = kappas[MEM_1] = kappas[MEM_2] = kappas[MEM_FINAL_CNT] = log_memory
    kappas[BYTECODE_FINAL_CNT] = bytecode_log
    kappas[QFLOCK] = table_logs[BLAKE3.opcode] + QFLOCK_SLOT_BITS
    for table, (base, width) in enumerate(zip(BASES, WIDTHS)):
        kappas[base : base + width] = [table_logs[table]] * width
    for local in BLAKE3_SLOT_BY_COLUMN:
        kappas[BASES[BLAKE3.opcode] + local] = None
    offsets, total_log = stack_offsets(kappas)
    placements = [Placement(-1, 0) if variables is None else Placement(variables, offset) for variables, offset in zip(kappas, offsets)]
    # Floor at the PCS minimum: WHIR's level ladder needs room, so a tiny
    # witness zero-pads up to it. Both sides derive this from the kappas.
    stack_log = max(15, total_log)
    return Layout(tuple(push), tuple(pull), tuple(count), tuple(placements), stack_log, tuple(table_logs))


def build_airs(layout: Layout, bus_forms: Sequence[Sequence[BusForm]]) -> list[Air]:
    return [Air(table, height, tuple(side[table.opcode] for side in bus_forms)) for table, height in zip(TABLES, layout.table_logs)]


def constraint_claims(claims: Sequence[AirClaim]) -> list[ColumnClaim]:
    result: list[ColumnClaim] = []
    for base, claim in zip(BASES, claims):
        for local, value in enumerate(claim.evaluations):
            result.append(ColumnClaim(base + local, claim.point, value))
    return result


def virtual_slot(column: int) -> int | None:
    """The q_flock slot a BLAKE3 value column rides in, or None if committed."""
    return BLAKE3_SLOT_BY_COLUMN.get(column - BASES[BLAKE3.opcode])


# Ligerito opening ------------------------------------------------------------

# Ligerito ladder geometry. These mirror the Rust source of truth in
# crates/pcs/src/ligerito_config.rs and must stay in sync with it: the prover
# derives its opening shape from those constants, so a mismatch here rejects a
# valid proof. Change a factor there, change it here.
INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 3
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5


@dataclass(frozen=True)
class LigeritoConfig:
    rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]
    query_grinding: tuple[int, ...]
    fold_grinding: tuple[int, ...]
    ood_samples: tuple[int, ...]


def _reduced_rate(rate: int, message_log: int) -> float:
    return ((2.0**message_log) - 1.0) / (2.0 ** (message_log + rate))


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
        a = (2.0 * half**5 + 3.0 * half * gamma * rho) / (3.0 * rho**1.5) * block_length + half / root_rho
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
        ood = (
            0
            if interleaved_log == INITIAL_FOLDING_FACTOR
            else next(
                (count for count in range(1, 9) if count * (192.0 - log2(variables)) - (2.0 * list_log - 1.0) + 1e-12 >= 128.0),
                0,
            )
        )
        ood_bits = 192.0 - list_log - log2(variables) if ood == 0 else ood * (192.0 - log2(variables)) - (2.0 * list_log - 1.0)
        # The batch polynomial's degree in the level's single lambda is
        # J - 1 = queries + ood (residual, OOD, one claim per query).
        algebraic_bits = 192.0 - log2(max(RING_SWITCH_SOUNDNESS_DEGREE, queries + ood, 2)) - list_log
        if ood_bits + 1e-12 < 128.0 or algebraic_bits + 1e-12 < 128.0:
            continue
        candidate = (queries, ood)
        if best is None or queries < best[0]:
            best = candidate
    if best is None:
        raise VerificationError("no secure Ligerito configuration")
    return best


def derive_config(log_n: int, initial_rate: int) -> LigeritoConfig:
    """Derive the production Johnson/OOD ladder used by the Rust PCS."""
    require(log_n > INITIAL_FOLDING_FACTOR and 1 <= initial_rate <= 4, "invalid Ligerito shape")
    folds = [INITIAL_FOLDING_FACTOR]
    message_logs = [log_n - INITIAL_FOLDING_FACTOR]
    rates = [initial_rate]
    remaining = message_logs[0]
    prior_fold = INITIAL_FOLDING_FACTOR
    reduction = RS_DOMAIN_INITIAL_REDUCTION_FACTOR
    while remaining > RESIDUAL_MAX_LOG:
        fold = min(SUBSEQUENT_FOLDING_FACTOR, remaining)
        rates.append(rates[-1] + prior_fold - reduction)
        remaining -= fold
        folds.append(fold)
        message_logs.append(remaining)
        prior_fold = fold
        reduction = RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
    require(len(folds) >= 2, "Ligerito requires at least two levels")
    parameters = tuple(_johnson_parameters(rate, columns, fold) for rate, columns, fold in zip(rates, message_logs, folds))
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
    require(leaf_count > 0 and leaf_count & (leaf_count - 1) == 0, "invalid Merkle leaf count")
    unique = sorted(set(queries))
    require(len(unique) == len(rows), f"opened-row count {len(rows)} does not match {len(unique)} distinct queries")
    require(all(0 <= q < leaf_count for q in unique), "Merkle query is out of range")
    require(all(len(row) == row_width for row in rows), "opened row has the wrong width")

    nodes = [(index, _row_hash(row, base_field)) for index, row in zip(unique, rows)]
    supplied = iter(octopus)
    for _ in range(leaf_count.bit_length() - 1):
        parents: list[tuple[int, bytes]] = []
        cursor = 0
        while cursor < len(nodes):
            index, value = nodes[cursor]
            paired = index & 1 == 0 and cursor + 1 < len(nodes) and nodes[cursor + 1][0] == index + 1
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

    def add_scaled(self, other: QuadraticMessage, scale: F192) -> QuadraticMessage:
        return QuadraticMessage(
            self.constant + scale * other.constant,
            self.linear + scale * other.linear,
            self.quadratic + scale * other.quadratic,
        )


def _enforced_sum(
    rows: Sequence[Sequence[FieldValue]],
    folds: Sequence[F192],
    query_weights: Sequence[F192],
) -> F192:
    lane_weights = build_eq(folds)
    require(len(query_weights) == len(rows), "Ligerito query-weight count mismatch")
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


def _induced_weight(message_log: int, queries: Sequence[int], query_weights: Sequence[F192], point: Sequence[F192]) -> F192:
    """The level's batched query claims, as one weight at `point`.

    Each query contributes the novel-basis column weight of doc annex B, Lemma
    lem:colweight, `prod_k (1 + p_k (1 + W-hat_k(x_q)))`, scaled by its power of
    the level's batching challenge.
    """
    require(len(point) == message_log, "bad induced-basis dimensions")
    require(len(query_weights) == len(queries), "Ligerito query-weight count mismatch")
    roots = _subspace_roots(message_log)
    inverses = [value.inv() if value else ZERO for value in roots]
    total = ZERO
    for weight, query in zip(query_weights, queries):
        basis = F192(query)
        product = weight
        for coordinate, challenge in enumerate(point):
            product *= ONE + challenge * (ONE + basis * inverses[coordinate])
            basis = basis * basis + roots[coordinate] * basis
        total += product
    return total


@dataclass(frozen=True)
class QueryContext:
    """One level's batched query claim, as the terminal weight needs it back."""

    message_log: int
    queries: tuple[int, ...]
    weights: tuple[F192, ...]  # one power of the level's lambda per query
    fold_start: int  # how many fold challenges preceded this level
    scalar: F192  # the power of lambda the whole batch was glued with


@dataclass(frozen=True)
class OodContext:
    """One out-of-domain claim: its point, and how it was glued in."""

    point: tuple[F192, ...]
    fold_start: int
    scalar: F192


def verify_ligerito(
    transcript: Transcript,
    proof: LigeritoProofData,
    log_n: int,
    initial_rate: int,
    target: F192,
    root: bytes,
    evaluate_basis: Callable[[Sequence[F192]], F192],
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
    contexts: list[QueryContext] = []
    ood_contexts: list[OodContext] = []
    fold_nonce_index = 0
    ood_index = 0
    current_root = root

    for level, (fold_count, rate) in enumerate(zip(config.folds, config.rates)):
        level_folds: list[F192] = []
        for fold_index in range(fold_count):
            bits = max(0, config.fold_grinding[level] - fold_index)
            if bits:
                require(fold_nonce_index < len(proof.fold_grinding_nonces), "missing Ligerito fold nonce")
                transcript.sponge.check_pow(proof.fold_grinding_nonces[fold_nonce_index], bits)
                fold_nonce_index += 1
            challenge = transcript.sample()
            folds.append(challenge)
            level_folds.append(challenge)
            running_target = running_quad.evaluate(challenge)
            running_quad = next_quad(running_target)

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        # The level's claims, held until its batching challenge is drawn: the
        # OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        pending_ood: list[tuple[tuple[F192, ...], int, F192, QuadraticMessage]] = []
        if final_level:
            residual = proof.residual
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
                pending_ood.append((point, len(folds), value, next_quad(value)))

        transcript.sponge.check_pow(proof.grinding_nonces[level], config.query_grinding[level])
        block_length = 1 << (message_log + rate)
        queries = sample_queries(transcript.sponge, block_length, config.queries[level])
        # One batching challenge per level, drawn once every claim it batches is
        # fixed: the OOD claims above and these query positions.
        lam = transcript.sample()
        query_weights = powers(lam, len(queries))
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
        enforced = _enforced_sum(rows, level_folds, query_weights)

        # Every commitment, including the last one, enters through an intro
        # message; the level's claims are then batched with powers of `lam`,
        # the running claim keeping lam^0 = 1.
        intro = next_quad(enforced)
        scalar = ONE
        for point, start, value, ood_intro in pending_ood:
            scalar *= lam
            running_quad = running_quad.add_scaled(ood_intro, scalar)
            running_target += scalar * value
            ood_contexts.append(OodContext(point, start, scalar))
        scalar *= lam
        running_quad = running_quad.add_scaled(intro, scalar)
        running_target += scalar * enforced
        contexts.append(QueryContext(message_log, tuple(queries), tuple(query_weights), len(folds), scalar))

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
            require(fold_nonce_index == len(proof.fold_grinding_nonces), "trailing Ligerito fold nonces")
            weight = evaluate_basis(list(folds) + tail_folds)
            for ctx in contexts:
                fixed = ctx.message_log - message_log
                point = list(folds[ctx.fold_start : ctx.fold_start + fixed]) + tail_folds
                weight += ctx.scalar * _induced_weight(ctx.message_log, ctx.queries, ctx.weights, point)
            for ood in ood_contexts:
                fixed = len(ood.point) - message_log
                scale = ood.scalar
                folded = folds[ood.fold_start : ood.fold_start + fixed]
                for expected, actual in zip(ood.point[:fixed], folded):
                    scale *= ONE + expected + actual
                for expected, actual in zip(ood.point[fixed:], tail_folds):
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
PHI = tuple(sum((PHI_BASIS[bit] for bit in range(8) if value >> bit & 1), ZERO) for value in range(256))
_MEDIUM_GENERATOR = F192.new(
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
# flock's zerocheck folds its first PACKED_BITS variables in one univariate skip
# (K_SKIP of them, since 2^K_SKIP = PACKED_BITS), and fixes the next N_INNER
# coordinates to public constants instead of sampling them. Their F2-linear
# independence is what that optimization's soundness rests on.
FLOCK_K_SKIP = 6
FLOCK_N_INNER = 7

FIXED_CHALLENGES = (
    PHI[0xF7],
    PHI[0x53],
    PHI[0xB5],
    *tuple(value / (ONE + value) for value in _MEDIUM_POWERS),
)


def quirky_weights(skip_point: F192, rest: Sequence[F192]) -> list[F192]:
    skip = lagrange_weights(PHI[:PACKED_BITS], skip_point)
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
    require(log_n >= FLOCK_K_SKIP + FLOCK_N_INNER, "Flock zerocheck input is too small")
    require(len(FIXED_CHALLENGES) == FLOCK_N_INNER, "wrong fixed-challenge count")
    sampled_prefix = transcript.samples(FLOCK_K_SKIP)
    sampled_outer = transcript.samples(log_n - FLOCK_K_SKIP - FLOCK_N_INNER)
    equality_point = (*sampled_prefix, *FIXED_CHALLENGES, *sampled_outer)
    ab_values = transcript.scalars(PACKED_BITS)
    c_values = transcript.scalars(PACKED_BITS)
    skip = transcript.sample()

    c_evaluation = lagrange_interpolate(PHI[PACKED_BITS : 2 * PACKED_BITS], c_values, skip)
    combined = [a + c for a, c in zip(ab_values, c_values)]
    combined_evaluation = lagrange_interpolate(PHI[: 2 * PACKED_BITS], [ZERO] * PACKED_BITS + combined, skip)
    running = combined_evaluation + c_evaluation
    rounds = []
    for equality in equality_point[FLOCK_K_SKIP:]:
        at_one, at_infinity = transcript.scalars(2)
        at_zero = (running + equality * at_one) / (ONE + equality)
        challenge = transcript.sample()
        rounds.append(challenge)
        running = at_zero * (ONE + challenge) + at_one * challenge + at_infinity * challenge * (ONE + challenge)
    final_a, final_b = transcript.scalars(2)
    require(running == final_a * final_b, "Flock zerocheck terminal mismatch")
    return ZerocheckResult(skip, tuple(rounds), tuple(equality_point[FLOCK_K_SKIP:]), final_a, final_b, c_evaluation)


@dataclass(frozen=True)
class LincheckResult:
    point: QuirkyPoint
    value: F192


@dataclass(frozen=True)
class Reduction:
    ab: ZClaim
    c: ZClaim


def _claim_weights(point: QuirkyPoint) -> list[F192]:
    return lagrange_weights(PHI[:PACKED_BITS], point.skip)


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
    require(len(values) == PACKED_BITS, "ring-switch slice has the wrong length")
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
        (query_weight * _linear_map(suffix_weight, coordinate_weights) for query_weight, suffix_weight in zip(query_tensor, suffix_tensor)),
        ZERO,
    )


def verify_stacked_opening(
    transcript: Transcript,
    opening: LigeritoOpening,
    root: bytes,
    stack_log: int,
    initial_rate: int,
    qflock_offset: int,
    qflock_variables: int,
    reduction: Reduction,
    point_claims: Sequence[tuple[Sequence[F192], F192]],
) -> None:
    """Bind both ring-switched claims and all ordinary stack point claims."""
    ring_claims = (reduction.ab, reduction.c)
    require(len(opening.ring_switches) == len(ring_claims), "wrong ring-switch proof count")
    slices: list[Sequence[F192]] = []
    for claim, values in zip(ring_claims, opening.ring_switches):
        require(len(values) == PACKED_BITS, "ring-switch proof has the wrong width")
        for value in values:
            transcript.observe(value)
        expected = sum((a * b for a, b in zip(_claim_weights(claim.point), values)), ZERO)
        require(expected == claim.value, "ring-switch claim mismatch")
        slices.append(values)

    map_challenges = [transcript.sample() for _ in RING_MAP_SHIFTS]
    coordinate_weights = _coordinate_weights(map_challenges)
    ring_values = [sum((a * b for a, b in zip(_transpose(values), coordinate_weights)), ZERO) for values in slices]
    ring_scales = powers(transcript.sample(), 2)
    target = sum((scale * value for scale, value in zip(ring_scales, ring_values)), ZERO)

    for _, value in point_claims:
        transcript.observe(value)
    point_scales = powers(transcript.sample(), len(point_claims))
    target += sum((scale * value for scale, (_, value) in zip(point_scales, point_claims)), ZERO)

    selector = qflock_offset >> qflock_variables

    def evaluate_basis(point: Sequence[F192]) -> F192:
        """Every pooled claim's weight at the opening's terminal point.

        The two ring-switched claims are supported on the q_flock region, so
        they carry that placement's selector; an ordinary point claim is an eq
        against the full stacked point.
        """
        low, high = point[:qflock_variables], point[qflock_variables:]
        selector_weight = ONE
        for bit, challenge in enumerate(high):
            selector_weight *= challenge if selector >> bit & 1 else ONE + challenge
        ring_value = sum(
            (scale * _ring_weight(claim.point.ring_tail, low, coordinate_weights) for scale, claim in zip(ring_scales, ring_claims)),
            ZERO,
        )
        value = selector_weight * ring_value
        for scale, (claim_point, _) in zip(point_scales, point_claims):
            require(len(claim_point) == len(point), "stack point has the wrong dimension")
            factor = ONE
            for expected, challenge in zip(claim_point, point):
                factor *= ONE + expected + challenge
            value += scale * factor
        return value

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
    inner_length = QFLOCK_SLOT_BITS  # the slot bits, the outer ones indexing instances
    ab_point = QuirkyPoint(zerocheck.skip, zerocheck.rounds[:inner_length], zerocheck.rounds[inner_length:])
    lincheck = verify_lincheck(log_n, ab_point, zerocheck.a, zerocheck.b, transcript)
    c_point = QuirkyPoint(zerocheck.skip, zerocheck.equality_tail[:inner_length], zerocheck.equality_tail[inner_length:])
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
    partial = transcript.scalars(PACKED_BITS)
    rest_weights = build_eq(tuple(reversed(challenges)))
    column_weights = [value * weight for weight in rest_weights for value in partial]
    terminal = blake3_bilinear(alpha, inner_weights, column_weights)
    terminal += beta * column_weights[512]
    require(terminal == running, "Flock lincheck terminal mismatch")
    skip = transcript.sample()
    value = sum((x * y for x, y in zip(lagrange_weights(PHI[:PACKED_BITS], skip), partial)), ZERO)
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
    lanes = ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14))
    message_pairs = ((0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11), (12, 13), (14, 15))
    permutation = (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)
    left_total = ZERO
    right_total = ZERO
    constant_rows = ZERO

    def slots(base: int) -> tuple[F192, ...]:
        return tuple(column_weights[base + bit] for bit in range(32))

    empty_word = (ZERO,) * 32

    def literal(value: int) -> tuple[F192, ...]:
        return tuple(column_weights[constant] if value >> bit & 1 else ZERO for bit in range(32))

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

    for base, length in ((0, 256), (message_base, 512), (counter_low, 64), (block_length, 32), (flags, 32)):
        for row in range(base, base + length):
            left_total += row_weights[row] * column_weights[row]
            constant_rows += row_weights[row]

    state = [empty_word for _ in range(16)]
    for word in range(8):
        state[word] = slots(32 * word)
    for word in range(4):
        state[8 + word] = literal(iv[word])
    state[12], state[13], state[14], state[15] = (slots(counter_low), slots(counter_high), slots(block_length), slots(flags))

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
    """Verify a complete leanVM-b execution proof against its public statement.

    The phases of doc sec:e2e-unrolled, in order.
    """
    program = Program.parse(statement)
    encoded_input = statement.get("public_input")
    if not isinstance(encoded_input, list) or len(encoded_input) != 2:
        raise VerificationError("public input must contain two field elements")
    public_input = tuple(parse_field(value) for value in encoded_input)
    transcript = Transcript(proof, b"leanvm-b", program.transcript_statement(public_input))

    # 1] Statement binding: the announced instance shape, checked against the
    # public caps before any reduction runs on it.
    announced = transcript.scalars(2 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced size has a nonzero high limb")
    log_memory = announced[0].c0
    table_logs = tuple(value.c0 for value in announced[1 : 1 + len(TABLES)])
    log_inverse_rate = announced[-1].c0
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    layout = build_layout(program, log_memory, table_logs)

    # 2] Commitment: one Merkle root over the stacked witness.
    root_words = transcript.scalars(2)
    require(all(word.c2 == 0 for word in root_words), "commitment root has a nonzero top limb")
    root = b"".join(limb.to_bytes(8, "little") for limb in (root_words[0].c0, root_words[0].c1, root_words[1].c0, root_words[1].c1))

    # 3] Bus: one batched GKR over the push, pull and count trees, then the leaf
    # decomposition, which leaves each table a degree-2 form and a total.
    bus = verify_bus_balance(layout.push, layout.pull, layout.count, transcript)

    # 4] Local constraints: one back-loaded zerocheck over all seven tables, at
    # the bus point, starting from the target the three leaf claims derive.
    # Every table takes a disjoint range of eta powers for its constraints; the
    # three bus sides share the three above them (doc sec:air).
    eta = transcript.sample()
    n_identities = sum(table.n_constraints for table in TABLES)
    eta_powers = powers(eta, n_identities + 3)
    constraint_powers, form_powers = eta_powers[:n_identities], eta_powers[n_identities:]
    target = sum((weight * total for weight, total in zip(form_powers, bus.totals)), ZERO)
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
    # line through them. The prover sends two limbs; the third follows.
    public_challenge = transcript.sample()
    public_low, public_high = transcript.scalars(2)
    public_point = [ZERO] * layout.placements[MEM_0].variables
    public_point[0] = public_challenge
    public_value = interpolate(public_input[0], public_input[1], public_challenge)
    public_top = (public_value + public_low + Y * public_high) / (Y * Y)
    claims.extend(
        ColumnClaim(column, tuple(public_point), value) for column, value in zip((MEM_0, MEM_1, MEM_2), (public_low, public_high, public_top))
    )

    # 6] Locate every claim in the stack: a column claim keeps its point and
    # gains its placement's selector bits; a BLAKE3 value claim is re-routed to
    # the equal q_flock slot evaluation.
    point_claims: list[tuple[tuple[F192, ...], F192]] = []
    qflock = layout.placements[QFLOCK]
    for claim in claims:
        slot = virtual_slot(claim.column)
        if slot is None:
            placement = layout.placements[claim.column]
            require(not placement.virtual, "claim targets an uncommitted column")
            require(len(claim.point) == placement.variables, "column claim dimension mismatch")
            selector = placement.offset >> placement.variables
            full_point = claim.point + _selector_point(selector, layout.stack_log - placement.variables)
        else:
            require(
                len(claim.point) + QFLOCK_SLOT_BITS == qflock.variables,
                "BLAKE3 slot claim dimension mismatch",
            )
            selector = qflock.offset >> qflock.variables
            full_point = _selector_point(slot, QFLOCK_SLOT_BITS) + claim.point + _selector_point(selector, layout.stack_log - qflock.variables)
        point_claims.append((full_point, claim.value))

    # 7] BLAKE3 validity, then the one opening that discharges every claim.
    reduction = verify_reduction(FLOCK_LOG_BITS + layout.table_logs[BLAKE3.opcode], transcript)
    opening = transcript.opening()
    verify_stacked_opening(
        transcript,
        opening,
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
