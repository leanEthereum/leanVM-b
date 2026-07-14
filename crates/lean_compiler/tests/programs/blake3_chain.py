# A short BLAKE3 chain over 256-bit stack values: blake3(h, h, h2), twice.
# With 128-bit machine words a 256-bit value is TWO cells (StackBuf(2)); each
# scalar cell holds one word in its low lane, so `h = [5, 7]` hashes the words
# [5, 0, 7, 0]. The digest lands in the pre-allocated pair. The public input is
# the two 128-bit digest cells of the chain's result, BLAKE3(BLAKE3(·)).
# public_input: 101229015297003380629709256178361811305, 199495362546883507010283175921733252645
from snark_lib import *


def main():
    h = StackBuf(2)
    h[0] = 5
    h[1] = 7
    h2 = StackBuf(2)
    blake3(h, h, h2)
    h3 = StackBuf(2)
    blake3(h2, h2, h3)
    p = GEN ** 0
    p[1] = h3[0]
    p[GEN] = h3[1]
    return
