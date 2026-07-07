from snark_lib import *

# Building block for the m33 verifier: verify N independent Merkle query-openings
# in ONE mul_range loop (body compiled once), with each query's leaf/path/bit
# offsets derived from the loop counter x = g^i (leaf at cell 2i = x^2, path at
# cell 4i = x^4, bits at cell 2i = x^2). num_interleaved = 2 (1-block leaf), depth 2.

ROOT0 = ROOT0_PLACEHOLDER
ROOT1 = ROOT1_PLACEHOLDER
N = 4


def hleaf2(a, b):
    iv = StackBuf(2)
    iv[0] = GEN ** 32
    iv[1] = 0
    lf = StackBuf(2)
    lf[0] = a
    lf[1] = b
    o = StackBuf(2)
    blake3(iv, lf, o)
    return o[0], o[1]


def mstep(n0, n1, s0, s1, bit):
    nb = StackBuf(2)
    nb[0] = n0
    nb[1] = n1
    sb = StackBuf(2)
    sb[0] = s0
    sb[1] = s1
    pr = StackBuf(2)
    if bit == 0:
        blake3(nb, sb, pr)
    else:
        blake3(sb, nb, pr)
    return pr[0], pr[1]


def main():
    leaves = HeapBuf(8)
    hint_witness(leaves[0:8], "leaves")
    paths = HeapBuf(16)
    hint_witness(paths[0:16], "paths")
    bits = HeapBuf(8)
    hint_witness(bits[0:8], "bits")
    for x in mul_range(1, GEN ** N):
        x2 = x * x
        x4 = x2 * x2
        n0, n1 = hleaf2(leaves[x2], leaves[x2 * GEN])
        pc = x4
        bc = x2
        for l in unroll(0, 2):
            n0, n1 = mstep(n0, n1, paths[pc], paths[pc * GEN], bits[bc])
            pc = pc * GEN ** 2
            bc = bc * GEN
        assert n0 == ROOT0
        assert n1 == ROOT1
    return
