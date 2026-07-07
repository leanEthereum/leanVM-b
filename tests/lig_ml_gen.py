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

def main():
    sc = HeapBuf(20)
    hint_witness(sc[0:20], "sc")
    row0 = HeapBuf(48)
    hint_witness(row0[0:48], "row0")
    row1 = HeapBuf(20)
    hint_witness(row1[0:20], "row1")
    row2 = HeapBuf(16)
    hint_witness(row2[0:16], "row2")
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
    for xq in mul_range(1, GEN ** 6):
        chq, nc0, nc1 = sqz(c0b_0[xq], c1b_0[xq])
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
    for xq in mul_range(1, GEN ** 5):
        chq, nc0, nc1 = sqz(c0b_1[xq], c1b_1[xq])
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
    for xq in mul_range(1, GEN ** 4):
        chq, nc0, nc1 = sqz(c0b_2[xq], c1b_2[xq])
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
    assert tr == TR
    return
