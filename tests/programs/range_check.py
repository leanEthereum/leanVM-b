# Range checks in the exponent: `log(x)` is the index of `x = GEN ** log(x)`,
# and `assert log(x) < k` proves x ∈ {GEN**0, …, GEN**(k-1)} in 3 cycles.
# public_input: GEN ** 10, GEN ** 20
from snark_lib import *


def main():
    x = GEN ** 5
    assert log(x) < log(GEN ** 8)

    # The bound can also be a plain integer exponent.
    y = x * x
    assert log(y) < 16

    # Boundaries: g^7 passes a bound of 8; g^0 = 1 passes any bound.
    top = GEN ** 7
    assert log(top) < 8
    assert log(GEN ** 0) < 8

    z = double_index(y)
    assert z == GEN ** 20

    p = GEN ** 0
    p[1] = y
    p[GEN] = z
    return


def double_index(a):
    # A helper with its own frame: its check gets its own g^{k-1} cell, and
    # 65536 = 2^16 is the largest allowed bound (the minimum memory size).
    b = a * a
    assert log(b) < 65536
    return b
