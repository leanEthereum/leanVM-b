# SHA256 over slices: `buf[lo:hi]` (2 cells) is a 256-bit operand under 128-bit
# machine words, with compile-time bounds — literals, literal-bound names, and
# their integer arithmetic (`x:x + 2`). Slices work on a large StackBuf (in
# place) and on a HeapBuf (bridged through the stack, one DEREF per cell), as
# inputs and as the output. Published: the two 128-bit digest cells of
# H(H(a[0:2], hb[0:2]), a[0:2]) read back from the heap.
# public_input: 116184158538570683948057849739013136319, 21823686390146404096869105959906788705
from snark_lib import *


def main():
    a = StackBuf(4)
    a[0] = 5
    a[1] = 7
    a[2] = 0
    a[3] = 0
    hb = HeapBuf(4)
    hb[1] = 11        # heap cell g^0
    hb[GEN] = 13      # heap cell g^1
    x = 0
    h = StackBuf(2)
    sha256(a[x:x + 2], hb[0:2], h)  # stack slice + heap input slice
    sha256(h, a[0:2], hb[2:4])  # digest lands in heap cells g^2, g^3
    p = GEN ** 0
    p[1] = hb[GEN ** 2]
    p[GEN] = hb[GEN ** 3]
    return
