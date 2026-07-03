# `match log(x)`: x = GEN ** j runs case j. Dispatch is two jumps through a
# trampoline table in the bytecode — jump to g^T · x², landing on the j-th
# two-instruction slot (SET the block address; JUMP to it); case blocks are
# unaligned. Cases must be consecutive from 0, and a hinted scrutinee must be
# range-checked first. Published: (21, 5 + 7 + 9) = (21, 11) — `+` is XOR.
# public_input: 21, 11
from snark_lib import *


def main():
    r = HeapBuf(4)
    x = GEN ** 2
    match log(x):
        case 0:
            r[1] = 11
        case 1:
            r[1] = 17
        case 2:
            r[1] = 21
        case 3:
            r[1] = 27
        case 4:
            r[1] = 31
        case 5:
            r[1] = 37
    for i in mul_range(1, GEN ** 3):
        match log(i):
            case 0:
                r[GEN] = 5
            case 1:
                r[GEN ** 2] = 7
            case 2:
                r[GEN ** 3] = 9
    p = GEN ** 0
    p[1] = r[1]
    p[GEN] = r[GEN] + r[GEN ** 2] + r[GEN ** 3]
    return
