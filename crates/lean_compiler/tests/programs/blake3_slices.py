# BLAKE3 over slices: `buf[lo:hi]` (4 cells) is a 256-bit operand, with
# compile-time bounds — literals, literal-bound names, and their integer
# arithmetic (`x:x + 4`). Slices work on a large StackBuf (in place) and on a
# HeapBuf (bridged through the stack, one DEREF per cell), as inputs and as
# the output. Published: the first two words of H(H(a[0:4], hb[0:4]), a[0:4])
# read back from the heap.
# public_input: 2910646302306008541, 3971110100326522597
from snark_lib import *


def main():
    a = StackBuf(8)
    a[0] = 5
    a[1] = 0
    a[2] = 7
    a[3] = 0
    hb = HeapBuf(8)
    hb[1] = 11        # heap cell g^0
    hb[GEN] = 0       # heap cell g^1
    hb[GEN ** 2] = 13  # heap cell g^2
    hb[GEN ** 3] = 0   # heap cell g^3
    x = 0
    h = StackBuf(4)
    blake3(a[x:x + 4], hb[0:4], h)  # stack slice + heap input slice
    blake3(h, a[0:4], hb[4:8])  # digest lands in heap cells g^4..g^7
    p = GEN ** 0
    p[1] = hb[GEN ** 4]
    p[GEN] = hb[GEN ** 5]
    return
