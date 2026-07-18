# Runtime slices: `buf[i:i + 2]` with a runtime g-power index `i` names the
# heap cells `buf·i·g^k`, k < 2 (one MUL folds `i` into the pointer). A SHA256
# chain over heap pairs (256-bit SHA256 value = two canonical cells),
# addressed by the loop counter: value k sits at cells g^{2k}..g^{2k+1}, and
# value k+1 = H(value k, value k). Published: the two 128-bit digest cells of
# H^3(5, 7).
# public_input: 303375857594630778590881045930673789313, 105277639902723802262468460103475501222
from snark_lib import *


def main():
    buf = HeapBuf(8)
    buf[1] = 5
    buf[GEN] = 7
    for i in mul_range(1, GEN ** 3):
        b = i * i  # value k at cells g^{2k}..g^{2k+1}
        sha256(buf[b:b + 2], buf[b:b + 2], buf[b * GEN ** 2:b * GEN ** 2 + 2])
    p = GEN ** 0
    p[1] = buf[GEN ** 6]
    p[GEN] = buf[GEN ** 7]
    return
