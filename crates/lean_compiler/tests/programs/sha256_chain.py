# A short SHA256 chain over 256-bit stack values: sha256(h, h, h2), twice.
# A 256-bit SHA256 value uses two canonical 128-bit cells (StackBuf(2)); each
# scalar cell holds one word in its low lane, so `h = [5, 7]` hashes the words
# [5, 0, 7, 0]. The digest lands in the pre-allocated pair. The public input is
# the two 128-bit digest cells of the chain's result, SHA256(SHA256(·)).
# public_input: 113344336591085340315322503817062598913, 125831114350981363556889679095242986262
from snark_lib import *


def main():
    h = StackBuf(2)
    h[0] = 5
    h[1] = 7
    h2 = StackBuf(2)
    sha256(h, h, h2)
    h3 = StackBuf(2)
    sha256(h2, h2, h3)
    p = GEN ** 0
    p[1] = h3[0]
    p[GEN] = h3[1]
    return
