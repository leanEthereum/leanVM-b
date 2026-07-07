from snark_lib import *

SEED0 = SEED0_PLACEHOLDER
SEED1 = SEED1_PLACEHOLDER
TARGET = TARGET_PLACEHOLDER
TR = TR_PLACEHOLDER
INITROOT0 = INITROOT0_PLACEHOLDER
INITROOT1 = INITROOT1_PLACEHOLDER
REC0A = REC0A_PLACEHOLDER
REC0B = REC0B_PLACEHOLDER
REC1A = REC1A_PLACEHOLDER
REC1B = REC1B_PLACEHOLDER
LBLA = LBLA_PLACEHOLDER
LBLB = LBLB_PLACEHOLDER
Z0 = Z0_PLACEHOLDER
Z1 = Z1_PLACEHOLDER
Z2 = Z2_PLACEHOLDER
Z3 = Z3_PLACEHOLDER
Z4 = Z4_PLACEHOLDER
Z5 = Z5_PLACEHOLDER
Z6 = Z6_PLACEHOLDER
Z7 = Z7_PLACEHOLDER
Z8 = Z8_PLACEHOLDER
Z9 = Z9_PLACEHOLDER
Z10 = Z10_PLACEHOLDER
Z11 = Z11_PLACEHOLDER
SVK0_0 = SVK0_0_PLACEHOLDER
IVK0_0 = IVK0_0_PLACEHOLDER
SVK0_1 = SVK0_1_PLACEHOLDER
IVK0_1 = IVK0_1_PLACEHOLDER
SVK0_2 = SVK0_2_PLACEHOLDER
IVK0_2 = IVK0_2_PLACEHOLDER
SVK0_3 = SVK0_3_PLACEHOLDER
IVK0_3 = IVK0_3_PLACEHOLDER
SVK0_4 = SVK0_4_PLACEHOLDER
IVK0_4 = IVK0_4_PLACEHOLDER
SVK0_5 = SVK0_5_PLACEHOLDER
IVK0_5 = IVK0_5_PLACEHOLDER
SVK0_6 = SVK0_6_PLACEHOLDER
IVK0_6 = IVK0_6_PLACEHOLDER
SVK0_7 = SVK0_7_PLACEHOLDER
IVK0_7 = IVK0_7_PLACEHOLDER
SVK0_8 = SVK0_8_PLACEHOLDER
IVK0_8 = IVK0_8_PLACEHOLDER
SVK1_0 = SVK1_0_PLACEHOLDER
IVK1_0 = IVK1_0_PLACEHOLDER
SVK1_1 = SVK1_1_PLACEHOLDER
IVK1_1 = IVK1_1_PLACEHOLDER
SVK1_2 = SVK1_2_PLACEHOLDER
IVK1_2 = IVK1_2_PLACEHOLDER
SVK1_3 = SVK1_3_PLACEHOLDER
IVK1_3 = IVK1_3_PLACEHOLDER
SVK1_4 = SVK1_4_PLACEHOLDER
IVK1_4 = IVK1_4_PLACEHOLDER
SVK1_5 = SVK1_5_PLACEHOLDER
IVK1_5 = IVK1_5_PLACEHOLDER
SVK1_6 = SVK1_6_PLACEHOLDER
IVK1_6 = IVK1_6_PLACEHOLDER
SVK2_0 = SVK2_0_PLACEHOLDER
IVK2_0 = IVK2_0_PLACEHOLDER
SVK2_1 = SVK2_1_PLACEHOLDER
IVK2_1 = IVK2_1_PLACEHOLDER
SVK2_2 = SVK2_2_PLACEHOLDER
IVK2_2 = IVK2_2_PLACEHOLDER
SVK2_3 = SVK2_3_PLACEHOLDER
IVK2_3 = IVK2_3_PLACEHOLDER
SVK2_4 = SVK2_4_PLACEHOLDER
IVK2_4 = IVK2_4_PLACEHOLDER
FN0 = FN0_PLACEHOLDER
FN1 = FN1_PLACEHOLDER
FN2 = FN2_PLACEHOLDER
ENF0 = ENF0_PLACEHOLDER
FN3 = FN3_PLACEHOLDER
FN4 = FN4_PLACEHOLDER
FN5 = FN5_PLACEHOLDER
DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQ = 4
DS_POW = 5

def obs(c0, c1, x):
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
    a = StackBuf(2)
    a[0] = c0
    a[1] = c1
    b = StackBuf(2)
    b[0] = 0
    b[1] = DS_SQ
    o = StackBuf(2)
    blake3(a, b, o)
    return o[0], o[0], o[1]

def dec128(bp, v):
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

def foldyr(yp, a0, b0, a1, b1, a2, b2, a3, b3, a4, b4):
    l0 = HeapBuf(16)
    src = yp
    dst = l0
    for i in unroll(0, 16):
        dst[1] = a0 * src[1] + b0 * src[GEN]
        src = src * GEN ** 2
        dst = dst * GEN
    l1 = HeapBuf(8)
    src = l0
    dst = l1
    for i in unroll(0, 8):
        dst[1] = a1 * src[1] + b1 * src[GEN]
        src = src * GEN ** 2
        dst = dst * GEN
    l2 = HeapBuf(4)
    src = l1
    dst = l2
    for i in unroll(0, 4):
        dst[1] = a2 * src[1] + b2 * src[GEN]
        src = src * GEN ** 2
        dst = dst * GEN
    l3 = HeapBuf(2)
    src = l2
    dst = l3
    for i in unroll(0, 2):
        dst[1] = a3 * src[1] + b3 * src[GEN]
        src = src * GEN ** 2
        dst = dst * GEN
    res = a4 * l3[1] + b4 * l3[GEN]
    return res

def main():
    sc = HeapBuf(20)
    hint_witness(sc[0:20], "sc")
    row0 = HeapBuf(48)
    hint_witness(row0[0:48], "row0")
    path0 = HeapBuf(120)
    hint_witness(path0[0:120], "path0")
    sbits0 = HeapBuf(768)
    hint_witness(sbits0[0:768], "sbits0")
    row1 = HeapBuf(20)
    hint_witness(row1[0:20], "row1")
    path1 = HeapBuf(90)
    hint_witness(path1[0:90], "path1")
    sbits1 = HeapBuf(640)
    hint_witness(sbits1[0:640], "sbits1")
    row2 = HeapBuf(16)
    hint_witness(row2[0:16], "row2")
    path2 = HeapBuf(64)
    hint_witness(path2[0:64], "path2")
    sbits2 = HeapBuf(512)
    hint_witness(sbits2[0:512], "sbits2")
    fpb0 = HeapBuf(128)
    hint_witness(fpb0[0:128], "fpb0")
    fpb1 = HeapBuf(128)
    hint_witness(fpb1[0:128], "fpb1")
    fpb2 = HeapBuf(128)
    hint_witness(fpb2[0:128], "fpb2")
    fpb3 = HeapBuf(128)
    hint_witness(fpb3[0:128], "fpb3")
    fpb4 = HeapBuf(128)
    hint_witness(fpb4[0:128], "fpb4")
    fpb5 = HeapBuf(128)
    hint_witness(fpb5[0:128], "fpb5")
    cv0 = SEED0
    cv1 = SEED1
    cv0, cv1 = absorb(cv0, cv1, 23, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, LBLA, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, LBLB, DS_BYTE)
    cv0, cv1 = obs(cv0, cv1, TARGET)
    cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, INITROOT0, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, INITROOT1, DS_BYTE)
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
    pb_0 = StackBuf(2)
    pb_0[0] = cv0
    pb_0[1] = cv1
    pz_0 = StackBuf(2)
    pz_0[0] = 0
    pz_0[1] = DS_POW
    pbase_0 = StackBuf(2)
    blake3(pb_0, pz_0, pbase_0)
    pn_0 = StackBuf(2)
    pn_0[0] = FN0
    pn_0[1] = DS_POW
    ph_0 = StackBuf(2)
    blake3(pbase_0, pn_0, ph_0)
    fpv_0 = ph_0[0]
    dec128(fpb0, fpv_0)
    zb_0_5 = fpb0[GEN ** 5]
    assert zb_0_5 == 0
    zb_0_6 = fpb0[GEN ** 6]
    assert zb_0_6 == 0
    zb_0_7 = fpb0[GEN ** 7]
    assert zb_0_7 == 0
    cv0, cv1 = absorb(cv0, cv1, FN0, DS_POW)
    r0_0, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + r0_0 * qb + r0_0 * r0_0 * qa
    a0_0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, a0_0)
    sp = sp * GEN
    b0_0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, b0_0)
    sp = sp * GEN
    qc = a0_0
    qb = tr + b0_0
    qa = b0_0
    pb_1 = StackBuf(2)
    pb_1[0] = cv0
    pb_1[1] = cv1
    pz_1 = StackBuf(2)
    pz_1[0] = 0
    pz_1[1] = DS_POW
    pbase_1 = StackBuf(2)
    blake3(pb_1, pz_1, pbase_1)
    pn_1 = StackBuf(2)
    pn_1[0] = FN1
    pn_1[1] = DS_POW
    ph_1 = StackBuf(2)
    blake3(pbase_1, pn_1, ph_1)
    fpv_1 = ph_1[0]
    dec128(fpb1, fpv_1)
    zb_1_6 = fpb1[GEN ** 6]
    assert zb_1_6 == 0
    zb_1_7 = fpb1[GEN ** 7]
    assert zb_1_7 == 0
    cv0, cv1 = absorb(cv0, cv1, FN1, DS_POW)
    r0_1, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + r0_1 * qb + r0_1 * r0_1 * qa
    a0_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, a0_1)
    sp = sp * GEN
    b0_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, b0_1)
    sp = sp * GEN
    qc = a0_1
    qb = tr + b0_1
    qa = b0_1
    pb_2 = StackBuf(2)
    pb_2[0] = cv0
    pb_2[1] = cv1
    pz_2 = StackBuf(2)
    pz_2[0] = 0
    pz_2[1] = DS_POW
    pbase_2 = StackBuf(2)
    blake3(pb_2, pz_2, pbase_2)
    pn_2 = StackBuf(2)
    pn_2[0] = FN2
    pn_2[1] = DS_POW
    ph_2 = StackBuf(2)
    blake3(pbase_2, pn_2, ph_2)
    fpv_2 = ph_2[0]
    dec128(fpb2, fpv_2)
    zb_2_7 = fpb2[GEN ** 7]
    assert zb_2_7 == 0
    cv0, cv1 = absorb(cv0, cv1, FN2, DS_POW)
    r0_2, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + r0_2 * qb + r0_2 * r0_2 * qa
    a0_2 = sp[1]
    cv0, cv1 = obs(cv0, cv1, a0_2)
    sp = sp * GEN
    b0_2 = sp[1]
    cv0, cv1 = obs(cv0, cv1, b0_2)
    sp = sp * GEN
    qc = a0_2
    qb = tr + b0_2
    qa = b0_2
    cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, REC0A, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, REC0B, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)
    c0b_0 = HeapBuf(7)
    c1b_0 = HeapBuf(7)
    c0b_0[1] = cv0
    c1b_0[1] = cv1
    qv0 = HeapBuf(6)
    for xq in mul_range(1, GEN ** 6):
        chq, nc0, nc1 = sqz(c0b_0[xq], c1b_0[xq])
        qv0[xq] = chq
        c0b_0[xq * GEN] = nc0
        c1b_0[xq * GEN] = nc1
    cv0 = c0b_0[GEN ** 6]
    cv1 = c1b_0[GEN ** 6]
    al_0_0, cv0, cv1 = sqz(cv0, cv1)
    al_0_1, cv0, cv1 = sqz(cv0, cv1)
    al_0_2, cv0, cv1 = sqz(cv0, cv1)
    eq_0 = HeapBuf(8)
    om_eq_0_0 = 1 + r0_0
    om_eq_0_1 = 1 + r0_1
    om_eq_0_2 = 1 + r0_2
    eq_0[GEN ** 0] = om_eq_0_0 * om_eq_0_1 * om_eq_0_2
    eq_0[GEN ** 1] = r0_0 * om_eq_0_1 * om_eq_0_2
    eq_0[GEN ** 2] = om_eq_0_0 * r0_1 * om_eq_0_2
    eq_0[GEN ** 3] = r0_0 * r0_1 * om_eq_0_2
    eq_0[GEN ** 4] = om_eq_0_0 * om_eq_0_1 * r0_2
    eq_0[GEN ** 5] = r0_0 * om_eq_0_1 * r0_2
    eq_0[GEN ** 6] = om_eq_0_0 * r0_1 * r0_2
    eq_0[GEN ** 7] = r0_0 * r0_1 * r0_2
    aw_0 = HeapBuf(6)
    om_aw_0_0 = 1 + al_0_0
    om_aw_0_1 = 1 + al_0_1
    om_aw_0_2 = 1 + al_0_2
    aw_0[GEN ** 0] = om_aw_0_0 * om_aw_0_1 * om_aw_0_2
    aw_0[GEN ** 1] = al_0_0 * om_aw_0_1 * om_aw_0_2
    aw_0[GEN ** 2] = om_aw_0_0 * al_0_1 * om_aw_0_2
    aw_0[GEN ** 3] = al_0_0 * al_0_1 * om_aw_0_2
    aw_0[GEN ** 4] = om_aw_0_0 * om_aw_0_1 * al_0_2
    aw_0[GEN ** 5] = al_0_0 * om_aw_0_1 * al_0_2
    accE_0 = HeapBuf(7)
    accE_0[1] = 0
    for xe in mul_range(1, GEN ** 6):
        rb_0 = xe
        rb_0 = rb_0 * rb_0
        rb_0 = rb_0 * rb_0
        rb_0 = rb_0 * rb_0
        rc_0 = rb_0
        ec_0 = GEN ** 0
        dot_0 = 0
        for c in unroll(0, 8):
            dot_0 = dot_0 + row0[rc_0] * eq_0[ec_0]
            rc_0 = rc_0 * GEN
            ec_0 = ec_0 * GEN
        accE_0[xe * GEN] = accE_0[xe] + aw_0[xe] * dot_0
    enf0 = accE_0[GEN ** 6]
    assert enf0 == ENF0
    iu0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, iu0)
    sp = sp * GEN
    iu2 = sp[1]
    cv0, cv1 = obs(cv0, cv1, iu2)
    sp = sp * GEN
    beta0, cv0, cv1 = sqz(cv0, cv1)
    qc = qc + beta0 * iu0
    qb = qb + beta0 * (enf0 + iu2)
    qa = qa + beta0 * iu2
    tr = tr + beta0 * enf0
    pb_3 = StackBuf(2)
    pb_3[0] = cv0
    pb_3[1] = cv1
    pz_3 = StackBuf(2)
    pz_3[0] = 0
    pz_3[1] = DS_POW
    pbase_3 = StackBuf(2)
    blake3(pb_3, pz_3, pbase_3)
    pn_3 = StackBuf(2)
    pn_3[0] = FN3
    pn_3[1] = DS_POW
    ph_3 = StackBuf(2)
    blake3(pbase_3, pn_3, ph_3)
    fpv_3 = ph_3[0]
    dec128(fpb3, fpv_3)
    zb_3_6 = fpb3[GEN ** 6]
    assert zb_3_6 == 0
    zb_3_7 = fpb3[GEN ** 7]
    assert zb_3_7 == 0
    cv0, cv1 = absorb(cv0, cv1, FN3, DS_POW)
    r1_0, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + r1_0 * qb + r1_0 * r1_0 * qa
    c1_0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, c1_0)
    sp = sp * GEN
    d1_0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, d1_0)
    sp = sp * GEN
    qc = c1_0
    qb = tr + d1_0
    qa = d1_0
    pb_4 = StackBuf(2)
    pb_4[0] = cv0
    pb_4[1] = cv1
    pz_4 = StackBuf(2)
    pz_4[0] = 0
    pz_4[1] = DS_POW
    pbase_4 = StackBuf(2)
    blake3(pb_4, pz_4, pbase_4)
    pn_4 = StackBuf(2)
    pn_4[0] = FN4
    pn_4[1] = DS_POW
    ph_4 = StackBuf(2)
    blake3(pbase_4, pn_4, ph_4)
    fpv_4 = ph_4[0]
    dec128(fpb4, fpv_4)
    zb_4_7 = fpb4[GEN ** 7]
    assert zb_4_7 == 0
    cv0, cv1 = absorb(cv0, cv1, FN4, DS_POW)
    r1_1, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + r1_1 * qb + r1_1 * r1_1 * qa
    c1_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, c1_1)
    sp = sp * GEN
    d1_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, d1_1)
    sp = sp * GEN
    qc = c1_1
    qb = tr + d1_1
    qa = d1_1
    cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, REC1A, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, REC1B, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)
    c0b_1 = HeapBuf(6)
    c1b_1 = HeapBuf(6)
    c0b_1[1] = cv0
    c1b_1[1] = cv1
    qv1 = HeapBuf(5)
    for xq in mul_range(1, GEN ** 5):
        chq, nc0, nc1 = sqz(c0b_1[xq], c1b_1[xq])
        qv1[xq] = chq
        c0b_1[xq * GEN] = nc0
        c1b_1[xq * GEN] = nc1
    cv0 = c0b_1[GEN ** 5]
    cv1 = c1b_1[GEN ** 5]
    al_1_0, cv0, cv1 = sqz(cv0, cv1)
    al_1_1, cv0, cv1 = sqz(cv0, cv1)
    al_1_2, cv0, cv1 = sqz(cv0, cv1)
    eq_1 = HeapBuf(4)
    om_eq_1_0 = 1 + r1_0
    om_eq_1_1 = 1 + r1_1
    eq_1[GEN ** 0] = om_eq_1_0 * om_eq_1_1
    eq_1[GEN ** 1] = r1_0 * om_eq_1_1
    eq_1[GEN ** 2] = om_eq_1_0 * r1_1
    eq_1[GEN ** 3] = r1_0 * r1_1
    aw_1 = HeapBuf(5)
    om_aw_1_0 = 1 + al_1_0
    om_aw_1_1 = 1 + al_1_1
    om_aw_1_2 = 1 + al_1_2
    aw_1[GEN ** 0] = om_aw_1_0 * om_aw_1_1 * om_aw_1_2
    aw_1[GEN ** 1] = al_1_0 * om_aw_1_1 * om_aw_1_2
    aw_1[GEN ** 2] = om_aw_1_0 * al_1_1 * om_aw_1_2
    aw_1[GEN ** 3] = al_1_0 * al_1_1 * om_aw_1_2
    aw_1[GEN ** 4] = om_aw_1_0 * om_aw_1_1 * al_1_2
    accE_1 = HeapBuf(6)
    accE_1[1] = 0
    for xe in mul_range(1, GEN ** 5):
        rb_1 = xe
        rb_1 = rb_1 * rb_1
        rb_1 = rb_1 * rb_1
        rc_1 = rb_1
        ec_1 = GEN ** 0
        dot_1 = 0
        for c in unroll(0, 4):
            dot_1 = dot_1 + row1[rc_1] * eq_1[ec_1]
            rc_1 = rc_1 * GEN
            ec_1 = ec_1 * GEN
        accE_1[xe * GEN] = accE_1[xe] + aw_1[xe] * dot_1
    enf1 = accE_1[GEN ** 5]
    iu0_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, iu0_1)
    sp = sp * GEN
    iu2_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, iu2_1)
    sp = sp * GEN
    beta1, cv0, cv1 = sqz(cv0, cv1)
    qc = qc + beta1 * iu0_1
    qb = qb + beta1 * (enf1 + iu2_1)
    qa = qa + beta1 * iu2_1
    tr = tr + beta1 * enf1
    pb_5 = StackBuf(2)
    pb_5[0] = cv0
    pb_5[1] = cv1
    pz_5 = StackBuf(2)
    pz_5[0] = 0
    pz_5[1] = DS_POW
    pbase_5 = StackBuf(2)
    blake3(pb_5, pz_5, pbase_5)
    pn_5 = StackBuf(2)
    pn_5[0] = FN5
    pn_5[1] = DS_POW
    ph_5 = StackBuf(2)
    blake3(pbase_5, pn_5, ph_5)
    fpv_5 = ph_5[0]
    dec128(fpb5, fpv_5)
    zb_5_7 = fpb5[GEN ** 7]
    assert zb_5_7 == 0
    cv0, cv1 = absorb(cv0, cv1, FN5, DS_POW)
    r2_0, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + r2_0 * qb + r2_0 * r2_0 * qa
    c2_0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, c2_0)
    sp = sp * GEN
    d2_0 = sp[1]
    cv0, cv1 = obs(cv0, cv1, d2_0)
    sp = sp * GEN
    qc = c2_0
    qb = tr + d2_0
    qa = d2_0
    r2_1, cv0, cv1 = sqz(cv0, cv1)
    tr = qc + r2_1 * qb + r2_1 * r2_1 * qa
    c2_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, c2_1)
    sp = sp * GEN
    d2_1 = sp[1]
    cv0, cv1 = obs(cv0, cv1, d2_1)
    sp = sp * GEN
    qc = c2_1
    qb = tr + d2_1
    qa = d2_1
    yr = HeapBuf(32)
    hint_witness(yr[0:32], "yr")
    yp = yr
    for iy in unroll(0, 32):
        yv = yp[1]
        cv0, cv1 = obs(cv0, cv1, yv)
        yp = yp * GEN
    cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)
    c0b_2 = HeapBuf(5)
    c1b_2 = HeapBuf(5)
    c0b_2[1] = cv0
    c1b_2[1] = cv1
    qv2 = HeapBuf(4)
    for xq in mul_range(1, GEN ** 4):
        chq, nc0, nc1 = sqz(c0b_2[xq], c1b_2[xq])
        qv2[xq] = chq
        c0b_2[xq * GEN] = nc0
        c1b_2[xq * GEN] = nc1
    cv0 = c0b_2[GEN ** 4]
    cv1 = c1b_2[GEN ** 4]
    al_2_0, cv0, cv1 = sqz(cv0, cv1)
    al_2_1, cv0, cv1 = sqz(cv0, cv1)
    eq_2 = HeapBuf(4)
    om_eq_2_0 = 1 + r2_0
    om_eq_2_1 = 1 + r2_1
    eq_2[GEN ** 0] = om_eq_2_0 * om_eq_2_1
    eq_2[GEN ** 1] = r2_0 * om_eq_2_1
    eq_2[GEN ** 2] = om_eq_2_0 * r2_1
    eq_2[GEN ** 3] = r2_0 * r2_1
    aw_2 = HeapBuf(4)
    om_aw_2_0 = 1 + al_2_0
    om_aw_2_1 = 1 + al_2_1
    aw_2[GEN ** 0] = om_aw_2_0 * om_aw_2_1
    aw_2[GEN ** 1] = al_2_0 * om_aw_2_1
    aw_2[GEN ** 2] = om_aw_2_0 * al_2_1
    aw_2[GEN ** 3] = al_2_0 * al_2_1
    accE_2 = HeapBuf(5)
    accE_2[1] = 0
    for xe in mul_range(1, GEN ** 4):
        rb_2 = xe
        rb_2 = rb_2 * rb_2
        rb_2 = rb_2 * rb_2
        rc_2 = rb_2
        ec_2 = GEN ** 0
        dot_2 = 0
        for c in unroll(0, 4):
            dot_2 = dot_2 + row2[rc_2] * eq_2[ec_2]
            rc_2 = rc_2 * GEN
            ec_2 = ec_2 * GEN
        accE_2[xe * GEN] = accE_2[xe] + aw_2[xe] * dot_2
    enf2 = accE_2[GEN ** 4]
    beta2, cv0, cv1 = sqz(cv0, cv1)
    tr = tr + beta2 * enf2
    for xm0 in mul_range(1, GEN ** 6):
        s128_0 = xm0
        s128_0 = s128_0 * s128_0
        s128_0 = s128_0 * s128_0
        s128_0 = s128_0 * s128_0
        s128_0 = s128_0 * s128_0
        s128_0 = s128_0 * s128_0
        s128_0 = s128_0 * s128_0
        s128_0 = s128_0 * s128_0
        sbp_0 = sbits0 * s128_0
        dec128(sbp_0, qv0[xm0])
        rl_0 = xm0
        rl_0 = rl_0 * rl_0
        rl_0 = rl_0 * rl_0
        rl_0 = rl_0 * rl_0
        rc_0 = rl_0
        ld0_0 = GEN ** 128
        ld1_0 = 0
        for jb in unroll(0, 4):
            aa_0 = StackBuf(2)
            aa_0[0] = ld0_0
            aa_0[1] = ld1_0
            mm_0 = StackBuf(2)
            mm_0[0] = row0[rc_0]
            rc_0 = rc_0 * GEN
            mm_0[1] = row0[rc_0]
            rc_0 = rc_0 * GEN
            oo_0 = StackBuf(2)
            blake3(aa_0, mm_0, oo_0)
            ld0_0 = oo_0[0]
            ld1_0 = oo_0[1]
        pbase_0 = xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbase_0 = pbase_0 * xm0
        pbp_0 = path0 * pbase_0
        bb_0 = sbp_0
        for lw in unroll(0, 10):
            ld0_0, ld1_0 = mstep(ld0_0, ld1_0, pbp_0[1], pbp_0[GEN], bb_0[1])
            pbp_0 = pbp_0 * GEN ** 2
            bb_0 = bb_0 * GEN
        assert ld0_0 == INITROOT0
        assert ld1_0 == INITROOT1
    for xm1 in mul_range(1, GEN ** 5):
        s128_1 = xm1
        s128_1 = s128_1 * s128_1
        s128_1 = s128_1 * s128_1
        s128_1 = s128_1 * s128_1
        s128_1 = s128_1 * s128_1
        s128_1 = s128_1 * s128_1
        s128_1 = s128_1 * s128_1
        s128_1 = s128_1 * s128_1
        sbp_1 = sbits1 * s128_1
        dec128(sbp_1, qv1[xm1])
        rl_1 = xm1
        rl_1 = rl_1 * rl_1
        rl_1 = rl_1 * rl_1
        rc_1 = rl_1
        ld0_1 = GEN ** 64
        ld1_1 = 0
        for jb in unroll(0, 2):
            aa_1 = StackBuf(2)
            aa_1[0] = ld0_1
            aa_1[1] = ld1_1
            mm_1 = StackBuf(2)
            mm_1[0] = row1[rc_1]
            rc_1 = rc_1 * GEN
            mm_1[1] = row1[rc_1]
            rc_1 = rc_1 * GEN
            oo_1 = StackBuf(2)
            blake3(aa_1, mm_1, oo_1)
            ld0_1 = oo_1[0]
            ld1_1 = oo_1[1]
        pbase_1 = xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbase_1 = pbase_1 * xm1
        pbp_1 = path1 * pbase_1
        bb_1 = sbp_1
        for lw in unroll(0, 9):
            ld0_1, ld1_1 = mstep(ld0_1, ld1_1, pbp_1[1], pbp_1[GEN], bb_1[1])
            pbp_1 = pbp_1 * GEN ** 2
            bb_1 = bb_1 * GEN
        assert ld0_1 == REC0A
        assert ld1_1 == REC0B
    for xm2 in mul_range(1, GEN ** 4):
        s128_2 = xm2
        s128_2 = s128_2 * s128_2
        s128_2 = s128_2 * s128_2
        s128_2 = s128_2 * s128_2
        s128_2 = s128_2 * s128_2
        s128_2 = s128_2 * s128_2
        s128_2 = s128_2 * s128_2
        s128_2 = s128_2 * s128_2
        sbp_2 = sbits2 * s128_2
        dec128(sbp_2, qv2[xm2])
        rl_2 = xm2
        rl_2 = rl_2 * rl_2
        rl_2 = rl_2 * rl_2
        rc_2 = rl_2
        ld0_2 = GEN ** 64
        ld1_2 = 0
        for jb in unroll(0, 2):
            aa_2 = StackBuf(2)
            aa_2[0] = ld0_2
            aa_2[1] = ld1_2
            mm_2 = StackBuf(2)
            mm_2[0] = row2[rc_2]
            rc_2 = rc_2 * GEN
            mm_2[1] = row2[rc_2]
            rc_2 = rc_2 * GEN
            oo_2 = StackBuf(2)
            blake3(aa_2, mm_2, oo_2)
            ld0_2 = oo_2[0]
            ld1_2 = oo_2[1]
        pbase_2 = xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbase_2 = pbase_2 * xm2
        pbp_2 = path2 * pbase_2
        bb_2 = sbp_2
        for lw in unroll(0, 8):
            ld0_2, ld1_2 = mstep(ld0_2, ld1_2, pbp_2[1], pbp_2[GEN], bb_2[1])
            pbp_2 = pbp_2 * GEN ** 2
            bb_2 = bb_2 * GEN
        assert ld0_2 == REC1A
        assert ld1_2 == REC1B
    one = GEN ** 0
    accR0 = HeapBuf(7)
    accR0[1] = 0
    for xr0 in mul_range(1, GEN ** 6):
        sq_0 = xr0
        sq_0 = sq_0 * sq_0
        sq_0 = sq_0 * sq_0
        sq_0 = sq_0 * sq_0
        sq_0 = sq_0 * sq_0
        sq_0 = sq_0 * sq_0
        sq_0 = sq_0 * sq_0
        sq_0 = sq_0 * sq_0
        sbp_0 = sbits0 * sq_0
        qc_0 = sbp_0
        wq_0 = GEN ** 0
        qf_0 = 0
        for bq in unroll(0, 10):
            qf_0 = qf_0 + qc_0[1] * wq_0
            qc_0 = qc_0 * GEN
            wq_0 = wq_0 * GEN
        sr_0_0 = qf_0
        wr_0_0 = sr_0_0 * IVK0_0
        sr_0_1 = sr_0_0 * sr_0_0 + SVK0_0 * sr_0_0
        wr_0_1 = sr_0_1 * IVK0_1
        sr_0_2 = sr_0_1 * sr_0_1 + SVK0_1 * sr_0_1
        wr_0_2 = sr_0_2 * IVK0_2
        sr_0_3 = sr_0_2 * sr_0_2 + SVK0_2 * sr_0_2
        wr_0_3 = sr_0_3 * IVK0_3
        sr_0_4 = sr_0_3 * sr_0_3 + SVK0_3 * sr_0_3
        wr_0_4 = sr_0_4 * IVK0_4
        sr_0_5 = sr_0_4 * sr_0_4 + SVK0_4 * sr_0_4
        wr_0_5 = sr_0_5 * IVK0_5
        sr_0_6 = sr_0_5 * sr_0_5 + SVK0_5 * sr_0_5
        wr_0_6 = sr_0_6 * IVK0_6
        sr_0_7 = sr_0_6 * sr_0_6 + SVK0_6 * sr_0_6
        wr_0_7 = sr_0_7 * IVK0_7
        sr_0_8 = sr_0_7 * sr_0_7 + SVK0_7 * sr_0_7
        wr_0_8 = sr_0_8 * IVK0_8
        prefix_0 = GEN ** 0
        prefix_0 = prefix_0 * (1 + r1_0 * (1 + wr_0_0))
        prefix_0 = prefix_0 * (1 + r1_1 * (1 + wr_0_1))
        prefix_0 = prefix_0 * (1 + r2_0 * (1 + wr_0_2))
        prefix_0 = prefix_0 * (1 + r2_1 * (1 + wr_0_3))
        S_0 = foldyr(yr, one, wr_0_4, one, wr_0_5, one, wr_0_6, one, wr_0_7, one, wr_0_8)
        accR0[xr0 * GEN] = accR0[xr0] + aw_0[xr0] * prefix_0 * S_0
    residsum0 = accR0[GEN ** 6]
    accR1 = HeapBuf(6)
    accR1[1] = 0
    for xr1 in mul_range(1, GEN ** 5):
        sq_1 = xr1
        sq_1 = sq_1 * sq_1
        sq_1 = sq_1 * sq_1
        sq_1 = sq_1 * sq_1
        sq_1 = sq_1 * sq_1
        sq_1 = sq_1 * sq_1
        sq_1 = sq_1 * sq_1
        sq_1 = sq_1 * sq_1
        sbp_1 = sbits1 * sq_1
        qc_1 = sbp_1
        wq_1 = GEN ** 0
        qf_1 = 0
        for bq in unroll(0, 9):
            qf_1 = qf_1 + qc_1[1] * wq_1
            qc_1 = qc_1 * GEN
            wq_1 = wq_1 * GEN
        sr_1_0 = qf_1
        wr_1_0 = sr_1_0 * IVK1_0
        sr_1_1 = sr_1_0 * sr_1_0 + SVK1_0 * sr_1_0
        wr_1_1 = sr_1_1 * IVK1_1
        sr_1_2 = sr_1_1 * sr_1_1 + SVK1_1 * sr_1_1
        wr_1_2 = sr_1_2 * IVK1_2
        sr_1_3 = sr_1_2 * sr_1_2 + SVK1_2 * sr_1_2
        wr_1_3 = sr_1_3 * IVK1_3
        sr_1_4 = sr_1_3 * sr_1_3 + SVK1_3 * sr_1_3
        wr_1_4 = sr_1_4 * IVK1_4
        sr_1_5 = sr_1_4 * sr_1_4 + SVK1_4 * sr_1_4
        wr_1_5 = sr_1_5 * IVK1_5
        sr_1_6 = sr_1_5 * sr_1_5 + SVK1_5 * sr_1_5
        wr_1_6 = sr_1_6 * IVK1_6
        prefix_1 = GEN ** 0
        prefix_1 = prefix_1 * (1 + r2_0 * (1 + wr_1_0))
        prefix_1 = prefix_1 * (1 + r2_1 * (1 + wr_1_1))
        S_1 = foldyr(yr, one, wr_1_2, one, wr_1_3, one, wr_1_4, one, wr_1_5, one, wr_1_6)
        accR1[xr1 * GEN] = accR1[xr1] + aw_1[xr1] * prefix_1 * S_1
    residsum1 = accR1[GEN ** 5]
    accR2 = HeapBuf(5)
    accR2[1] = 0
    for xr2 in mul_range(1, GEN ** 4):
        sq_2 = xr2
        sq_2 = sq_2 * sq_2
        sq_2 = sq_2 * sq_2
        sq_2 = sq_2 * sq_2
        sq_2 = sq_2 * sq_2
        sq_2 = sq_2 * sq_2
        sq_2 = sq_2 * sq_2
        sq_2 = sq_2 * sq_2
        sbp_2 = sbits2 * sq_2
        qc_2 = sbp_2
        wq_2 = GEN ** 0
        qf_2 = 0
        for bq in unroll(0, 8):
            qf_2 = qf_2 + qc_2[1] * wq_2
            qc_2 = qc_2 * GEN
            wq_2 = wq_2 * GEN
        sr_2_0 = qf_2
        wr_2_0 = sr_2_0 * IVK2_0
        sr_2_1 = sr_2_0 * sr_2_0 + SVK2_0 * sr_2_0
        wr_2_1 = sr_2_1 * IVK2_1
        sr_2_2 = sr_2_1 * sr_2_1 + SVK2_1 * sr_2_1
        wr_2_2 = sr_2_2 * IVK2_2
        sr_2_3 = sr_2_2 * sr_2_2 + SVK2_2 * sr_2_2
        wr_2_3 = sr_2_3 * IVK2_3
        sr_2_4 = sr_2_3 * sr_2_3 + SVK2_3 * sr_2_3
        wr_2_4 = sr_2_4 * IVK2_4
        prefix_2 = GEN ** 0
        S_2 = foldyr(yr, one, wr_2_0, one, wr_2_1, one, wr_2_2, one, wr_2_3, one, wr_2_4)
        accR2[xr2 * GEN] = accR2[xr2] + aw_2[xr2] * prefix_2 * S_2
    residsum2 = accR2[GEN ** 4]
    eqris = GEN ** 0
    eqris = eqris * (1 + Z0 + r0_0)
    eqris = eqris * (1 + Z1 + r0_1)
    eqris = eqris * (1 + Z2 + r0_2)
    eqris = eqris * (1 + Z3 + r1_0)
    eqris = eqris * (1 + Z4 + r1_1)
    eqris = eqris * (1 + Z5 + r2_0)
    eqris = eqris * (1 + Z6 + r2_1)
    az0 = 1 + Z7
    az1 = 1 + Z8
    az2 = 1 + Z9
    az3 = 1 + Z10
    az4 = 1 + Z11
    sy_evb = foldyr(yr, az0, Z7, az1, Z8, az2, Z9, az3, Z10, az4, Z11)
    inner = eqris * sy_evb + beta0 * residsum0 + beta1 * residsum1 + beta2 * residsum2
    assert inner == tr
    return
