# Runtime slices: `buf[i:i + 4]` with a runtime g-power index `i` names four
# heap cells starting at `buf·i` (one MUL folds `i` into the pointer). A BLAKE3
# chain over four-word heap values, addressed by the loop counter: value k
# starts at cell g^{4k}, and value k+1 = H(value k, value k). Published: the four digest words of
# H^3(5, 7).
# public_input: 9179625039470602661, 14089184190295358934, 1788154028250263227, 3881161908982872004
from snark_lib import *


def main():
    buf = HeapBuf(16)
    buf[1] = 5
    buf[GEN] = 0
    buf[GEN ** 2] = 7
    buf[GEN ** 3] = 0
    for i in mul_range(1, GEN ** 3):
        i2 = i * i
        b = i2 * i2
        blake3(buf[b:b + 4], buf[b:b + 4], buf[b * GEN ** 4:b * GEN ** 4 + 4])
    p = GEN ** 0
    p[1] = buf[GEN ** 12]
    p[GEN] = buf[GEN ** 13]
    p[GEN ** 2] = buf[GEN ** 14]
    p[GEN ** 3] = buf[GEN ** 15]
    return
