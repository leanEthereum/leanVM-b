from snark_lib import *

# In-circuit Ligerito PCS-opening verifier — a zkDSL port of flock's
# `recursive_verifier_with_basis_succinct` (leanVM-b's actual opening scheme).
# Loaded via `parse_file_with_replacements`; the `*_PLACEHOLDER` constants are
# filled per proof by the Rust harness (mirroring `recursion.py`'s convention).
#
# Config here: log_n=8, initial_k=2, one recursive step, 1 query/level (the octopus
# multi-proof degenerates to a single Merkle path). The transcript sponge is the
# `blake3` opcode with a domain tag in the 2nd word (1 scalar, 2 byte-word, 3 len,
# 4 squeeze); challenges/positions are re-derived, never trusted.

SEED0 = SEED0_PLACEHOLDER
SEED1 = SEED1_PLACEHOLDER
TARGET = TARGET_PLACEHOLDER
INITROOT0 = INITROOT0_PLACEHOLDER
INITROOT1 = INITROOT1_PLACEHOLDER
RECROOT0 = RECROOT0_PLACEHOLDER
RECROOT1 = RECROOT1_PLACEHOLDER
LBLA = LBLA_PLACEHOLDER
LBLB = LBLB_PLACEHOLDER
# Novel-basis nodes sks_vks(6) / sks_vks(4) and their inverses (residual).
SV6_0 = SV6_0_PLACEHOLDER
SV6_1 = SV6_1_PLACEHOLDER
SV6_2 = SV6_2_PLACEHOLDER
SV6_3 = SV6_3_PLACEHOLDER
SV6_4 = SV6_4_PLACEHOLDER
IV6_0 = IV6_0_PLACEHOLDER
IV6_1 = IV6_1_PLACEHOLDER
IV6_2 = IV6_2_PLACEHOLDER
IV6_3 = IV6_3_PLACEHOLDER
IV6_4 = IV6_4_PLACEHOLDER
IV6_5 = IV6_5_PLACEHOLDER
SV4_0 = SV4_0_PLACEHOLDER
SV4_1 = SV4_1_PLACEHOLDER
SV4_2 = SV4_2_PLACEHOLDER
IV4_0 = IV4_0_PLACEHOLDER
IV4_1 = IV4_1_PLACEHOLDER
IV4_2 = IV4_2_PLACEHOLDER
IV4_3 = IV4_3_PLACEHOLDER
# The evaluation point z (log_n = 8 coords): z[0..4] pair with the fold challenges
# `ris`, z[4..8] with the `yr` residual variables.
Z0 = Z0_PLACEHOLDER
Z1 = Z1_PLACEHOLDER
Z2 = Z2_PLACEHOLDER
Z3 = Z3_PLACEHOLDER
Z4 = Z4_PLACEHOLDER
Z5 = Z5_PLACEHOLDER
Z6 = Z6_PLACEHOLDER
Z7 = Z7_PLACEHOLDER

DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQ = 4
DS_POW = 5


def obs(c0, c1, x):
    # Absorb one scalar: cv <- compress(cv, [x, DS_SCALAR]).
    a = StackBuf(2)
    a[0] = c0
    a[1] = c1
    b = StackBuf(2)
    b[0] = x
    b[1] = DS_SCALAR
    o = StackBuf(2)
    blake3(a, b, o)
    return o[0], o[1]


def absorb(c0, c1, x, tag):
    # Absorb one tagged word (byte-word or length frame).
    a = StackBuf(2)
    a[0] = c0
    a[1] = c1
    b = StackBuf(2)
    b[0] = x
    b[1] = tag
    o = StackBuf(2)
    blake3(a, b, o)
    return o[0], o[1]


def sqz(c0, c1):
    # Squeeze a challenge and ratchet: challenge = first word of the squeeze.
    a = StackBuf(2)
    a[0] = c0
    a[1] = c1
    b = StackBuf(2)
    b[0] = 0
    b[1] = DS_SQ
    o = StackBuf(2)
    blake3(a, b, o)
    return o[0], o[0], o[1]


def chk(bp, v):
    # Full 128-bit decomposition of `v`: boolean-constrain each bit, reconstruct
    # Sigma b_i*GEN^i and assert == v (pins the bits, no wraparound).
    cb = bp
    w = GEN ** 0
    acc = 0
    for i in unroll(0, 128):
        b = cb[1]
        sq = b * b
        assert sq == b
        acc = acc + b * w
        cb = cb * GEN
        w = w * GEN
    assert acc == v
    return


def hleaf(r0, r1, r2, r3):
    # Merkle leaf hash of a 4-lane row (64 bytes = 2 blocks), length-in-IV MD chain.
    iv = StackBuf(2)
    iv[0] = GEN ** 64
    iv[1] = 0
    q0 = StackBuf(2)
    q0[0] = r0
    q0[1] = r1
    c1 = StackBuf(2)
    blake3(iv, q0, c1)
    q1 = StackBuf(2)
    q1[0] = r2
    q1[1] = r3
    c2 = StackBuf(2)
    blake3(c1, q1, c2)
    return c2[0], c2[1]


def mstep(n0, n1, s0, s1, bit):
    # One Merkle level: sibling order by the query-index bit.
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


def foldyr(yp, a0, b0, a1, b1, a2, b2, a3, b3):
    # Fold a 16-value multilinear (LSB-first) over 4 variables: each var j combines
    # yp'[i] = a_j*yp[2i] + b_j*yp[2i+1]. Returns the scalar Sigma_y yp[y]*Pi_j
    # f_j(bit_j(y)) with f_j(0)=a_j, f_j(1)=b_j. Used for both the eval_b MLE eval
    # and the per-level residual folds.
    l1 = HeapBuf(8)
    src = yp
    dst = l1
    for i in unroll(0, 8):
        dst[1] = a0 * src[1] + b0 * src[GEN]
        src = src * GEN ** 2
        dst = dst * GEN
    l2 = HeapBuf(4)
    src = l1
    dst = l2
    for i in unroll(0, 4):
        dst[1] = a1 * src[1] + b1 * src[GEN]
        src = src * GEN ** 2
        dst = dst * GEN
    l3 = HeapBuf(2)
    src = l2
    dst = l3
    for i in unroll(0, 2):
        dst[1] = a2 * src[1] + b2 * src[GEN]
        src = src * GEN ** 2
        dst = dst * GEN
    res = a3 * l3[1] + b3 * l3[GEN]
    return res


def main():
    sc = HeapBuf(12)
    hint_witness(sc[0:12], "sc")
    l0row = HeapBuf(4)
    hint_witness(l0row[0:4], "l0row")
    l0path = HeapBuf(14)
    hint_witness(l0path[0:14], "l0path")
    lastrow = HeapBuf(4)
    hint_witness(lastrow[0:4], "lastrow")
    lastpath = HeapBuf(10)
    hint_witness(lastpath[0:10], "lastpath")
    yr = HeapBuf(16)
    hint_witness(yr[0:16], "yr")
    vq0 = HeapBuf(128)
    hint_witness(vq0[0:128], "vq0")
    vql = HeapBuf(128)
    hint_witness(vql[0:128], "vql")

    cv0 = SEED0
    cv1 = SEED1
    # observe_label("flock-ligerito-basis-v0") = len 23 + two byte-words
    cv0, cv1 = absorb(cv0, cv1, 23, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, LBLA, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, LBLB, DS_BYTE)
    cv0, cv1 = obs(cv0, cv1, TARGET)
    cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, INITROOT0, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, INITROOT1, DS_BYTE)

    # prologue: msg0 -> quad, t_r = target
    sp = sc
    u0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, u0)
    sp = sp * GEN
    u2 = sp[1]
    cv0, cv1 = obs(cv0, cv1, u2)
    sp = sp * GEN
    qc = u0
    qb = TARGET + u2
    qa = u2
    tr = TARGET

    # L0 lane fold: 2 rounds
    ri0, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + ri0 * qb + ri0 * ri0 * qa
    a0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, a0)
    sp = sp * GEN
    b0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, b0)
    sp = sp * GEN
    qc = a0
    qb = tr + b0
    qa = b0
    ri1, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + ri1 * qb + ri1 * ri1 * qa
    a1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, a1)
    sp = sp * GEN
    b1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, b1)
    sp = sp * GEN
    qc = a1
    qb = tr + b1
    qa = b1

    # observe root_1, absorb L0 query nonce (0), sample the query value
    cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, RECROOT0, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, RECROOT1, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)
    vq0v, cv0, cv1 = sqz(cv0, cv1)

    # enforced_0 = <l0row, eq_table([ri0, ri1])>
    om0 = 1 + ri0
    om1 = 1 + ri1
    eq0 = om0 * om1
    eq1 = ri0 * om1
    eq2 = om0 * ri1
    eq3 = ri0 * ri1
    enf0 = l0row[GEN ** 0] * eq0 + l0row[GEN ** 1] * eq1 + l0row[GEN ** 2] * eq2 + l0row[GEN ** 3] * eq3

    # intro glue: read msg, sample beta0, fold quad, t_r += beta0*enf0
    iu0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, iu0)
    sp = sp * GEN
    iu2 = sp[1]
    cv0, cv1 = obs(cv0, cv1, iu2)
    sp = sp * GEN
    beta0, cv0, cv1 = sqz(cv0, cv1)
    ib = enf0 + iu2
    qc = qc + beta0 * iu0
    qb = qb + beta0 * ib
    qa = qa + beta0 * iu2
    tr = tr + beta0 * enf0

    # last recursive level: 2 folds
    ry0, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + ry0 * qb + ry0 * ry0 * qa
    c0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, c0)
    sp = sp * GEN
    d0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, d0)
    sp = sp * GEN
    qc = c0
    qb = tr + d0
    qa = d0
    ry1, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + ry1 * qb + ry1 * ry1 * qa
    c1v = sp[1]
    cv0, cv1 = obs(cv0, cv1, c1v)
    sp = sp * GEN
    d1v = sp[1]
    cv0, cv1 = obs(cv0, cv1, d1v)
    sp = sp * GEN

    # observe yr (16 values), absorb last-level nonce (0), sample the query value
    yp = yr
    for i in unroll(0, 16):
        yv = yp[1]
        cv0, cv1 = obs(cv0, cv1, yv)
        yp = yp * GEN
    cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)
    vqlv, cv0, cv1 = sqz(cv0, cv1)

    # enforced_last = <lastrow, eq_table([ry0, ry1])>; beta_last; t_r += ...
    pm0 = 1 + ry0
    pm1 = 1 + ry1
    fq0 = pm0 * pm1
    fq1 = ry0 * pm1
    fq2 = pm0 * ry1
    fq3 = ry0 * ry1
    enfL = lastrow[GEN ** 0] * fq0 + lastrow[GEN ** 1] * fq1 + lastrow[GEN ** 2] * fq2 + lastrow[GEN ** 3] * fq3
    betaL, cv0, cv1 = sqz(cv0, cv1)
    tr = tr + betaL * enfL

    # bit-check the sampled query values, then verify the single Merkle paths
    chk(vq0, vq0v)
    chk(vql, vqlv)
    ld0, ld1 = hleaf(l0row[GEN ** 0], l0row[GEN ** 1], l0row[GEN ** 2], l0row[GEN ** 3])
    lp = l0path
    vb = vq0
    for i in unroll(0, 7):
        ld0, ld1 = mstep(ld0, ld1, lp[1], lp[GEN], vb[1])
        lp = lp * GEN ** 2
        vb = vb * GEN
    assert ld0 == INITROOT0
    assert ld1 == INITROOT1
    ed0, ed1 = hleaf(lastrow[GEN ** 0], lastrow[GEN ** 1], lastrow[GEN ** 2], lastrow[GEN ** 3])
    ep = lastpath
    wb = vql
    for i in unroll(0, 5):
        ed0, ed1 = mstep(ed0, ed1, ep[1], ep[GEN], wb[1])
        ep = ep * GEN ** 2
        wb = wb * GEN
    assert ed0 == RECROOT0
    assert ed1 == RECROOT1

    # residual level L0: q_field (low 7 bits of the sampled value), novel-basis W_k
    qf0 = vq0[GEN ** 0] * (GEN ** 0) + vq0[GEN ** 1] * (GEN ** 1) + vq0[GEN ** 2] * (GEN ** 2) + vq0[GEN ** 3] * (GEN ** 3) + vq0[GEN ** 4] * (GEN ** 4) + vq0[GEN ** 5] * (GEN ** 5) + vq0[GEN ** 6] * (GEN ** 6)
    s60 = qf0
    s61 = s60 * s60 + SV6_0 * s60
    s62 = s61 * s61 + SV6_1 * s61
    s63 = s62 * s62 + SV6_2 * s62
    s64 = s63 * s63 + SV6_3 * s63
    s65 = s64 * s64 + SV6_4 * s64
    w60 = s60 * IV6_0
    w61 = s61 * IV6_1
    w62 = s62 * IV6_2
    w63 = s63 * IV6_3
    w64 = s64 * IV6_4
    w65 = s65 * IV6_5
    pp0a = 1 + ry0 * (1 + w60)
    pp0b = 1 + ry1 * (1 + w61)
    pp0 = pp0a * pp0b

    # residual last level: q_field (low 5 bits), W_k
    qfL = vql[GEN ** 0] * (GEN ** 0) + vql[GEN ** 1] * (GEN ** 1) + vql[GEN ** 2] * (GEN ** 2) + vql[GEN ** 3] * (GEN ** 3) + vql[GEN ** 4] * (GEN ** 4)
    s40 = qfL
    s41 = s40 * s40 + SV4_0 * s40
    s42 = s41 * s41 + SV4_1 * s41
    s43 = s42 * s42 + SV4_2 * s42
    w40 = s40 * IV4_0
    w41 = s41 * IV4_1
    w42 = s42 * IV4_2
    w43 = s43 * IV4_3

    # eqris = prod_{k<4} (1 + Z_k + ris_k), ris = [ri0, ri1, ry0, ry1]
    er0 = 1 + Z0 + ri0
    er1 = 1 + Z1 + ri1
    er2 = 1 + Z2 + ry0
    er3 = 1 + Z3 + ry1
    eqris = er0 * er1 * er2 * er3

    # terminal (as folds of yr, no per-y unroll):
    #   Sigma_y yr[y]*eval_b[y]  = eqris * MLE_eval(yr, z[4..8])
    #   Sigma_y yr[y]*resid0[y]  = pp0 * fold(yr, [w6_2,w6_3,w6_4,w6_5])
    #   Sigma_y yr[y]*residL[y]  =        fold(yr, [w4_0,w4_1,w4_2,w4_3])
    one = GEN ** 0
    az4 = 1 + Z4
    az5 = 1 + Z5
    az6 = 1 + Z6
    az7 = 1 + Z7
    sy_evb = foldyr(yr, az4, Z4, az5, Z5, az6, Z6, az7, Z7)
    sy_r0 = foldyr(yr, one, w62, one, w63, one, w64, one, w65)
    sy_rl = foldyr(yr, one, w40, one, w41, one, w42, one, w43)
    inner = eqris * sy_evb + beta0 * pp0 * sy_r0 + betaL * sy_rl
    assert inner == tr
    return
