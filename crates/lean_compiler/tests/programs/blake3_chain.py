# A short BLAKE3 chain over 256-bit stack values: blake3(h, h, h2), twice.
# A 256-bit BLAKE3 value uses four F64 cells (StackBuf(4)). The digest lands in
# the pre-allocated run and its four words are the public input.
# public_input: 6435064747262329193, 5487635915178971307, 11033477629434050085, 10814665273705721660
from snark_lib import *


def main():
    h = StackBuf(4)
    h[0] = 5
    h[1] = 0
    h[2] = 7
    h[3] = 0
    h2 = StackBuf(4)
    blake3(h, h, h2)
    h3 = StackBuf(4)
    blake3(h2, h2, h3)
    p = GEN ** 0
    p[1] = h3[0]
    p[GEN] = h3[1]
    p[GEN ** 2] = h3[2]
    p[GEN ** 3] = h3[3]
    return
