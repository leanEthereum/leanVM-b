# `Const` parameters: `def hash_pair(buf, k: Const)` is a template — each call
# site passes a compile-time constant and gets a monomorphized copy with `k`
# substituted as the integer literal, usable in compile-time positions (the
# slice bounds below). The direct call and match_range arm 0 share the k=0
# specialization. A 256-bit SHA256 value occupies two canonical cells.
# Published: the two 128-bit digest cells of H(quad0, quad0) XOR H(quad1, quad1)
# — the direct k=0 digest XORed with the arm the runtime x = GEN selects (k=1).
# public_input: 103281898447189108178865428981366615000, 215098267749361558445247258756249015119
from snark_lib import *


def main():
    buf = HeapBuf(4)
    buf[1] = 5
    buf[GEN] = 7
    buf[GEN ** 2] = 11
    buf[GEN ** 3] = 13
    a0, a1 = hash_pair(buf, 0)
    x = GEN
    b0, b1 = match_range(log(x), range(0, 2), lambda i: hash_pair(buf, i))
    p = GEN ** 0
    p[1] = a0 + b0
    p[GEN] = a1 + b1
    return


def hash_pair(buf, k: Const):
    h = StackBuf(2)
    sha256(buf[k * 2:k * 2 + 2], buf[k * 2:k * 2 + 2], h)
    return h[0], h[1]
