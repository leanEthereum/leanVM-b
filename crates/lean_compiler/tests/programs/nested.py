# Deep nesting across frames: a mul_range loop whose helper body range-checks
# the counter, matches on it, calls a recursive function from one arm (five
# frames deep, with its base-case `return` inside an `if` branch), and
# branches inside another arm — self_fp and the hoisted caches shared between
# the match dispatch and the inner `if` in the same helper frame.
# geom(1) = 1 + g + g² + g³ + g⁴ = 31. Published: (31 + 5, 9) = (26, 9).
# public_input: 26, 9
from snark_lib import *


def main():
    acc = HeapBuf(6)
    for i in mul_range(1, GEN ** 3):
        assert log(i) < 3
        match log(i):
            case 0:
                acc[i] = geom(1)
            case 1:
                if i == GEN:
                    acc[i] = 5
                else:
                    acc[i] = 11
            case 2:
                acc[i] = 9
    p = GEN ** 0
    p[1] = acc[1] + acc[GEN]
    p[GEN] = acc[GEN ** 2]
    return


def geom(x):
    if x == GEN ** 4:
        return x  # early return from inside the branch
    y = geom(x * GEN)
    return x + y
