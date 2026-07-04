# Stage 1 of the in-VM XMSS verifier: the WOTS core. Everything the prover
# supplies is a witness stream (driven by tests/xmss_vm.rs from a real
# signature); every hinted value is constrained below.
#
# - The encoding digest D = MD(tweak|pp, msg, randomness) with the absorbed
#   size in the IV, in the exponent (g^96 — 3 blocks of 32 bytes).
# - Per chain i: the digit is hinted in the exponent (d = g^{e_i}), range
#   checked, and dispatched once: arm k walks the remaining 7-k chain steps
#   (`unroll(k, 7)` — no subtraction needed) and returns the tip AND the
#   digit literal k. The target sum is the product of the hinted digits
#   (g^{sum} == g^194), and the encoding is reconstructed in the monomial
#   subspaces: acc = XOR_i bits_i * x^{3i}, compared against D.
# - The WOTS public key hash is MD over the 42 tips (size 704 bytes in the
#   IV), and its digest is published together with D.
from snark_lib import *


def main():
    # D = MD(tweak|pp, msg, randomness): IV = g^96 | 0.
    iv = StackBuf(2)
    iv[0] = GEN ** 96
    iv[1] = 0
    tpp = StackBuf(2)
    hint_witness(tpp, "enc_tweak")
    msg = StackBuf(2)
    hint_witness(msg, "msg")
    rnd = StackBuf(2)
    hint_witness(rnd, "rand")
    s1 = StackBuf(2)
    blake3(iv, tpp, s1)
    s2 = StackBuf(2)
    blake3(s1, msg, s2)
    s3 = StackBuf(2)
    blake3(s2, rnd, s3)

    # 42 chains: hint g^{e_i}, range check, dispatch, accumulate.
    tips = StackBuf(42)
    prod = 1
    acc = 0
    w = 1
    for i in unroll(0, 42):
        db = StackBuf(1)
        hint_witness(db[0:1], "digits")
        d = db[0]
        assert log(d) < 8
        vb = StackBuf(1)
        hint_witness(vb[0:1], "sig")
        t, bits = match_range(log(d), range(0, 8), lambda k: walk(vb[0], k))
        tips[i] = t
        prod = prod * d
        acc = acc + bits * w  # bits ⊗ x^{3i}: the digit in its monomial subspace
        w = w * 8
    assert prod == GEN ** 194  # target sum, in the exponent
    assert acc == s3[0]  # the digits ARE the encoding digest

    # WOTS pk hash: MD over the tips, IV = g^704 | 0 (32 + 672 bytes).
    iv2 = StackBuf(2)
    iv2[0] = GEN ** 704
    iv2[1] = 0
    ptw = StackBuf(2)
    hint_witness(ptw, "pk_tweak")
    st = StackBuf(2)
    blake3(iv2, ptw, st)
    for j in unroll(0, 21):
        sn = StackBuf(2)
        blake3(st, tips[2 * j:2 * j + 2], sn)
        st = sn

    p = GEN ** 0
    p[1] = st[0]  # the Merkle leaf (WOTS pk hash)
    p[GEN] = s3[0]  # the encoding digest
    return


def walk(v, k: Const):
    # Walk chain steps k..6 (7-k compressions), each step's tweak|pp pair
    # hinted in execution order: value' = H(tweak|pp, value|0).
    vp = StackBuf(2)
    vp[0] = v
    vp[1] = 0
    for s in unroll(k, 7):
        tw = StackBuf(2)
        hint_witness(tw, "chain_tweaks")
        out = StackBuf(2)
        blake3(tw, vp, out)
        vp = StackBuf(2)
        vp[0] = out[0]
        vp[1] = 0
    return vp[0], k
