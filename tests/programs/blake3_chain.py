# A short BLAKE3 chain over 256-bit stack values: blake3(h, h, h2), twice.
# Each StackBuf(4) holds the four 64-bit words of a 256-bit value in four
# consecutive frame cells, read in place by the BLAKE3 instruction, which
# writes the digest into the pre-allocated output quad. The public input is
# the first two words of the chain's digest, BLAKE3²(5, 7).
# public_input: 6435064747262329193, 5487635915178971307
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
    return
