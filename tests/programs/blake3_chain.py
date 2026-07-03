# A short BLAKE3 chain over 256-bit stack values: blake3(h, h, h2), twice.
# Each StackBuf(2) holds the two 128-bit words of a 256-bit value in two
# consecutive frame cells, read in place by the BLAKE3 instruction, which
# writes the digest into the pre-allocated output pair. The public input is
# the chain's digest, BLAKE3²(5, 7), as two 128-bit words.
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
