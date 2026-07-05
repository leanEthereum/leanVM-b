# Runtime slices: `buf[i:i + 4]` with a runtime g-power index `i` names the
# heap cells `buf·i·g^k`, k < 4 (one MUL folds `i` into the pointer). A BLAKE3
# chain over heap quads, addressed by the loop counter: quad k sits at cells
# g^{4k}..g^{4k+3}, and quad k+1 = H(quad k, quad k). Published: the first two
# words of H³(5, 7).
# public_input: 9179625039470602661, 14089184190295358934
from snark_lib import *


def main():
    buf = HeapBuf(16)
    buf[1] = 5
    buf[GEN] = 0
    buf[GEN ** 2] = 7
    buf[GEN ** 3] = 0
    for i in mul_range(1, GEN ** 3):
        b = i * i * i * i  # quad k at cells g^{4k}..g^{4k+3}
        blake3(buf[b:b + 4], buf[b:b + 4], buf[b * GEN ** 4:b * GEN ** 4 + 4])
    p = GEN ** 0
    p[1] = buf[GEN ** 12]
    p[GEN] = buf[GEN ** 13]
    return
