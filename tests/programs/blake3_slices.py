# BLAKE3 over slices of a large StackBuf: `buf[lo:hi]` (2 cells) is a 256-bit
# operand, with compile-time bounds — literals, literal-bound names, and their
# integer arithmetic (`x:x + 2`). `blake3(a, b, out)` writes the digest into
# the 2-cell run `out`. Published: H(H(a[0:2], a[2:4]), a[0:2]).
# public_input: 73254051709246423672821570119667875293, 221212579854185352854904196652205296234
from snark_lib import *


def main():
    a = StackBuf(8)
    a[0] = 5
    a[1] = 7
    a[2] = 11
    a[3] = 13
    x = 2
    h = StackBuf(2)
    blake3(a[0:2], a[x:x + 2], h)  # slice operands
    b = StackBuf(4)
    blake3(h, a[0:2], b[2:4])  # digest lands in b[2:4]
    p = GEN ** 0
    p[1] = b[2]
    p[GEN] = b[3]
    return
