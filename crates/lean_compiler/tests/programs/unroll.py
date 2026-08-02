# `for i in unroll(a, b)` replicates the body at compile time, i substituted
# as the integer literal of each iteration — zero loop overhead (no call, no
# frame, no counter). Bounds are compile-time integers, including Const
# parameters: `chain(buf, 3)` specializes and unrolls three BLAKE3 steps over
# heap slices indexed by `i` (a 256-bit BLAKE3 value is four F64 cells).
# Published: the four digest words of H^3(5, 7) — same chain as
# blake3_heap_chain.py, unrolled instead of looped.
# public_input: 9179625039470602661, 14089184190295358934, 1788154028250263227, 3881161908982872004
from snark_lib import *


def main():
    sb = StackBuf(8)
    sb[0] = 1
    for i in unroll(0, 7):
        sb[i + 1] = sb[i] * GEN  # sb[k] = g^k
    assert sb[7] == GEN ** 7
    buf = HeapBuf(16)
    buf[1] = 5
    buf[GEN] = 0
    buf[GEN ** 2] = 7
    buf[GEN ** 3] = 0
    chain(buf, 3)
    p = GEN ** 0
    p[1] = buf[GEN ** 12]
    p[GEN] = buf[GEN ** 13]
    p[GEN ** 2] = buf[GEN ** 14]
    p[GEN ** 3] = buf[GEN ** 15]
    return


def chain(buf, n: Const):
    for i in unroll(0, n):
        blake3(buf[i * 4:i * 4 + 4], buf[i * 4:i * 4 + 4], buf[i * 4 + 4:i * 4 + 8])
    return
