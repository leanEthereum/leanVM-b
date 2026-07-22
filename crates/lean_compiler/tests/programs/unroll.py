# `for i in unroll(a, b)` replicates the body at compile time, i substituted
# as the integer literal of each iteration — zero loop overhead (no call, no
# frame, no counter). Bounds are compile-time integers, including Const
# parameters: `chain(buf, 3)` specializes and unrolls three BLAKE3 steps over
# heap slices indexed by `i` (a 256-bit BLAKE3 value is two canonical cells).
# Published: the two 128-bit digest cells of H^3(5, 7) — same chain as
# blake3_heap_chain.py, unrolled instead of looped.
# public_input: 259899574965733219954697446670390340005, 71594800443637044304569228067009621691
from snark_lib import *


def main():
    sb = StackBuf(8)
    sb[0] = 1
    for i in unroll(0, 7):
        sb[i + 1] = sb[i] * GEN  # sb[k] = g^k
    assert sb[7] == GEN ** 7
    buf = HeapBuf(8)
    buf[1] = 5
    buf[GEN] = 7
    chain(buf, 3)
    p = GEN ** 0
    p[1] = buf[GEN ** 6]
    p[GEN] = buf[GEN ** 7]
    return


def chain(buf, n: Const):
    for i in unroll(0, n):
        blake3(buf[i * 2:i * 2 + 2], buf[i * 2:i * 2 + 2], buf[i * 2 + 2:i * 2 + 4])
    return
