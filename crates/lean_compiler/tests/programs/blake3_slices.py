# BLAKE3 over slices: `buf[lo:hi]` (4 cells) is a 256-bit operand under 64-bit
# machine words, with compile-time bounds — literals, literal-bound names, and
# their integer arithmetic (`x:x + 4`). Slices work on a large StackBuf (in
# place) and on a HeapBuf (bridged through the stack, one DEREF per cell), as
# inputs and as the output. Published: the four digest words read back from the heap.
# public_input: 2910646302306008541, 3971110100326522597, 12274690806251735658, 11991957982951544561
from snark_lib import *


def main():
    a = StackBuf(8)
    a[0] = 5
    a[1] = 0
    a[2] = 7
    a[3] = 0
    hb = HeapBuf(8)
    hb[1] = 11        # heap cell g^0
    hb[GEN] = 0
    hb[GEN ** 2] = 13
    hb[GEN ** 3] = 0
    x = 0
    h = StackBuf(4)
    blake3(a[x:x + 4], hb[0:4], h)
    blake3(h, a[0:4], hb[4:8])
    p = GEN ** 0
    p[1] = hb[GEN ** 4]
    p[GEN] = hb[GEN ** 5]
    p[GEN ** 2] = hb[GEN ** 6]
    p[GEN ** 3] = hb[GEN ** 7]
    return
