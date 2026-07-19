# A short BLAKE3 chain over 256-bit stack values: blake3(h, h, h2), twice.
# A 256-bit BLAKE3 value uses two canonical 128-bit cells (StackBuf(2)); each
# scalar cell holds one word in its low lane, so `h = [5, 7]` hashes the words
# [5, 0, 7, 0]. The digest lands in the pre-allocated pair. The public input is
# the two 128-bit digest cells of the chain's result, BLAKE3(BLAKE3(·)).
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
