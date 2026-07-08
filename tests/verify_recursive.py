from snark_lib import *

# In-circuit replay of leanVM-b's `cpu::verify` for a fixed inner proof — the
# recursion guest (doc.tex §Recursive aggregation). Config-driven by placeholder
# constants computed by the harness from the REAL `cpu::layout` of the inner
# program; the inner proof stream arrives as one hint buffer and every scalar
# read is bound into the sponge exactly as the native verifier does.
#
# Deferred evaluation claims (doc.tex §Deferred evaluation claims): the bytecode
# MLE evaluations (the bus decomposition's Public coordinates) are HINTED, used
# in the formula, and exported as claims instead of being computed in-circuit.
#
# Phase A (this file so far): seed → announced sizes → commitment root → bus
# (α, grinding, γ, 3× GKR grand product, count≠0, balance with default surplus,
# 3× leaf decomposition with the claim pool).
#
# Naming: `cur` is the stream cursor (heap pointer, advanced ×g per word read);
# `cv0/cv1` the sponge; `zeta` holds the three GKR points side by side.

STREAM_LEN = STREAM_LEN_PLACEHOLDER
ANN = ANN_PLACEHOLDER
GFULL = GFULL_PLACEHOLDER
GEXTRA = GEXTRA_PLACEHOLDER
GG = GG_PLACEHOLDER
ILD0 = ILD0_PLACEHOLDER
ILD1 = ILD1_PLACEHOLDER
ILD2 = ILD2_PLACEHOLDER

# GKR sides: 0=push, 1=pull, 2=count. SMU = layer counts; ZOFF = offsets of the
# per-side final points inside `zeta`; MUMAX = max(SMU)+1 buffer bound.
SMU = SMU_PLACEHOLDER
ZOFF = ZOFF_PLACEHOLDER
MUMAX = MUMAX_PLACEHOLDER

# Bus blocks, flattened across the 3 sides (side s covers blocks
# [SBLK[s], SBLK[s+1])): per block its κ, its selector (offset >> κ), the number
# of padding rows DELTA = 2^κ − real, and its coord range [BC0, BC0+BCN) in the
# flat coord arrays. Per coord: CT (0=const, 1=col, 2=gcol, 3=index, 4=public),
# CV (the const value, else 0), FPV (its default-padding fingerprint value).
# Per side: SALPHA selects (α, γ) for push/pull and (1, 0) for count.
SBLK = SBLK_PLACEHOLDER
BKAPPA = BKAPPA_PLACEHOLDER
BSEL = BSEL_PLACEHOLDER
BDELTA = BDELTA_PLACEHOLDER
BC0 = BC0_PLACEHOLDER
BCN = BCN_PLACEHOLDER
CT = CT_PLACEHOLDER
CVAL = CVAL_PLACEHOLDER
FPV = FPV_PLACEHOLDER
# index_mle factor constants: IDXC[i] = 1 + g^(2^i).
IDXC = IDXC_PLACEHOLDER
# Number of committed-coordinate claims (Col/GCol coords across all sides), the
# deferred bytecode values (Public coords), and the count-root inverse hint.
NCLAIMS = NCLAIMS_PLACEHOLDER
NBCV = NBCV_PLACEHOLDER
# Zerochecks: per-table log row counts, constraint-column counts, eval offsets.
TAU = TAU_PLACEHOLDER
NCOL = NCOL_PLACEHOLDER
TAUMAX = TAUMAX_PLACEHOLDER
# Phase C: the public input (baked; the seed already binds it), the real BLAKE3
# count + pin-point location, and the three public pin constants.
NB3 = NB3_PLACEHOLDER
NLOGB3 = NLOGB3_PLACEHOLDER
PINZOFF = PINZOFF_PLACEHOLDER
PINV = PINV_PLACEHOLDER
# Phase D (flock reduction): the r1cs statement label/digest words, zerocheck +
# lincheck label words, the seven fixed inner challenges (+ inverses of 1+c),
# the phi8 node table + baked Lagrange inverse denominators (Lambda domain,
# combined domain, S domain), and shapes: MR1CS = r1cs.m, NMLV = MR1CS-6,
# LCR = k_log - k_skip, PINCOL = the const-pin column.
R1CSLBL = R1CSLBL_PLACEHOLDER
SD0 = SD0_PLACEHOLDER
SD1 = SD1_PLACEHOLDER
ZCLBLA = ZCLBLA_PLACEHOLDER
ZCLBLB = ZCLBLB_PLACEHOLDER
LCLBLA = LCLBLA_PLACEHOLDER
LCLBLB = LCLBLB_PLACEHOLDER
INNER7 = INNER7_PLACEHOLDER
I7INV = I7INV_PLACEHOLDER
PHI = PHI_PLACEHOLDER
ILAM = ILAM_PLACEHOLDER
ICMB = ICMB_PLACEHOLDER
ISDOM = ISDOM_PLACEHOLDER
MR1CS = MR1CS_PLACEHOLDER
NMLV = NMLV_PLACEHOLDER
LCR = LCR_PLACEHOLDER
PINCOL = PINCOL_PLACEHOLDER
KLOG = KLOG_PLACEHOLDER
# Phase E: the stacked mixed opening. Labels; the two ring-switch fronts
# (claim check in-circuit; the tensor transpose + eval_rs_eq DEFERRED); the
# gamma-combination of the two ring-switch claims and the NCL pool claims.
OBLBLA = OBLBLA_PLACEHOLDER
OBLBLB = OBLBLB_PLACEHOLDER
RSLBLA = RSLBLA_PLACEHOLDER
RSLBLB = RSLBLB_PLACEHOLDER
PDLBLA = PDLBLA_PLACEHOLDER
PDLBLB = PDLBLB_PLACEHOLDER
NCL = NCL_PLACEHOLDER
# Phase E2: the Ligerito opening core over the stacked commitment (config-driven
# exactly like tests/ligerito_recursive.py), plus the generalized eval_b
# terminal: per pooled claim, its point location (CPBUF: 0=zeta, 1=rho,
# 2=pi, 3=pin, 4=strided value), offsets/lengths, baked low bits (pin slot /
# stride slot), the selector, and its residual-cube slot YT.
LIGLBLA = LIGLBLA_PLACEHOLDER
LIGLBLB = LIGLBLB_PLACEHOLDER
NLEVELS = NLEVELS_PLACEHOLDER
R = R_PLACEHOLDER
YR_LOG_N = YR_LOG_N_PLACEHOLDER
YR_LEN = YR_LEN_PLACEHOLDER
LENRIS = LENRIS_PLACEHOLDER
MAXNI = MAXNI_PLACEHOLDER
MAXQ = MAXQ_PLACEHOLDER
MAXNSQ = MAXNSQ_PLACEHOLDER
MAXLMC = MAXLMC_PLACEHOLDER
QP_LEN = QP_LEN_PLACEHOLDER
LSC_LEN = LSC_LEN_PLACEHOLDER
LROWS_LEN = LROWS_LEN_PLACEHOLDER
LPATHS_LEN = LPATHS_LEN_PLACEHOLDER
LSBITS_LEN = LSBITS_LEN_PLACEHOLDER
LFPB_LEN = LFPB_LEN_PLACEHOLDER
QUERIES = QUERIES_PLACEHOLDER
KLVL = KLVL_PLACEHOLDER
NUMINTER = NUMINTER_PLACEHOLDER
NBYTES = NBYTES_PLACEHOLDER
BLOCKS = BLOCKS_PLACEHOLDER
DEPTH = DEPTH_PLACEHOLDER
PER = PER_PLACEHOLDER
NSQ = NSQ_PLACEHOLDER
QPOFF = QPOFF_PLACEHOLDER
ALPHALEN = ALPHALEN_PLACEHOLDER
LMC = LMC_PLACEHOLDER
RISSTART = RISSTART_PLACEHOLDER
PREFIXLEN = PREFIXLEN_PLACEHOLDER
FOLDBASE = FOLDBASE_PLACEHOLDER
ROWOFF = ROWOFF_PLACEHOLDER
PATHOFF = PATHOFF_PLACEHOLDER
SBITSOFF = SBITSOFF_PLACEHOLDER
SVKOFF = SVKOFF_PLACEHOLDER
BITS = BITS_PLACEHOLDER
FULL = FULL_PLACEHOLDER
EXTRA8 = EXTRA8_PLACEHOLDER
SVK = SVK_PLACEHOLDER
IVK = IVK_PLACEHOLDER
# eval_b claim descriptors + the ring-switch selector data.
CPBUF = CPBUF_PLACEHOLDER
CPOFF = CPOFF_PLACEHOLDER
CPLEN = CPLEN_PLACEHOLDER
CSLOT = CSLOT_PLACEHOLDER
CSEL = CSEL_PLACEHOLDER
NOVER = NOVER_PLACEHOLDER
SELN = SELN_PLACEHOLDER
YTHI = YTHI_PLACEHOLDER
QPKDV = QPKDV_PLACEHOLDER
RSSEL = RSSEL_PLACEHOLDER
YRS = YRS_PLACEHOLDER
# Ring-switch linearized algebra: the trace-dual basis (bit_i(y) = Tr(delta_i y))
# (any eq-weighted bit-sum is the linearized
# polynomial L_w(y) = sum_k c_k y^(2^k), c_k = sum_i w_i delta_i^(2^k); squaring
# is one MUL, so the tensor transpose and eval_rs_eq run in-circuit.
DELTA = DELTA_PLACEHOLDER
# Phase F: log rows of the bytecode blocks (the deferred bytecode points).
KBC = KBC_PLACEHOLDER
# Aggregation: NSUB sub-proofs of the same program; per-sub proof data arrives
# as hints. The seed sponge state after the two byte-string absorbs is baked
# (SEEDB), then the hinted sub statement + the baked program digest are bound.
NSUB = NSUB_PLACEHOLDER
KBCV = KBCV_PLACEHOLDER
SEEDB0 = SEEDB0_PLACEHOLDER
SEEDB1 = SEEDB1_PLACEHOLDER
DIG0 = DIG0_PLACEHOLDER
DIG1 = DIG1_PLACEHOLDER

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
    # Boolean-constrain 128 hinted bits and assert they reconstruct v.
    acc = 0
    for i in unroll(0, 128):
        b = bp[GEN ** i]
        sq = b * b
        assert sq == b
        acc = acc + b * GEN ** i
    assert acc == v
    return


def decq(bp, v, qfp, qbpp, d: Const, per: Const):
    # dec128 fused with query extraction (see tests/ligerito_recursive.py).
    acc = 0
    for j in unroll(0, per):
        qf = 0
        for b in unroll(0, d):
            t = bp[GEN ** (j * d + b)]
            sq = t * t
            assert sq == t
            qf = qf + t * GEN ** b
        qfp[GEN ** j] = qf
        qbpp[GEN ** j] = bp * GEN ** (j * d)
        acc = acc + qf * GEN ** (j * d)
    for i in unroll(per * d, 128):
        t = bp[GEN ** i]
        sq = t * t
        assert sq == t
        acc = acc + t * GEN ** i
    assert acc == v
    return


@unroll
def foldyr(yp, weights, wbase: Const):
    # Weighted fold of the yr multilinear (see tests/ligerito_recursive.py).
    l0 = StackBuf(YR_LEN)
    for t in unroll(0, YR_LEN // 2):
        l0[t] = weights[wbase] * yp[GEN ** (2 * t)] + weights[wbase + 1] * yp[GEN ** (2 * t + 1)]
    cur = l0
    n = YR_LEN // 2
    for j in unroll(1, YR_LOG_N):
        nxt = StackBuf(YR_LEN)
        for t in unroll(0, n // 2):
            nxt[t] = weights[wbase + 2 * j] * cur[2 * t] + weights[wbase + 2 * j + 1] * cur[2 * t + 1]
        cur = nxt
        n = n // 2
    return cur[0]


def main():
    stream = HeapBuf(NSUB * (STREAM_LEN))
    hint_witness(stream[0:NSUB * (STREAM_LEN)], "stream")
    fpb = HeapBuf(NSUB * (128))
    hint_witness(fpb[0:NSUB * (128)], "fpb")
    bcv = HeapBuf(NSUB * (NBCV))
    hint_witness(bcv[0:NSUB * (NBCV)], "bcv")
    cinv = HeapBuf(NSUB * (1))
    hint_witness(cinv[0:NSUB * (1)], "cinv")
    zc1 = HeapBuf(NSUB * (128))
    hint_witness(zc1[0:NSUB * (128)], "zc1")
    zcr = HeapBuf(NSUB * (2 * NMLV))
    hint_witness(zcr[0:NSUB * (2 * NMLV)], "zcr")
    zcf = HeapBuf(NSUB * (2))
    hint_witness(zcf[0:NSUB * (2)], "zcf")
    zinv = HeapBuf(NSUB * (NMLV))
    hint_witness(zinv[0:NSUB * (NMLV)], "zinv")
    lcr = HeapBuf(NSUB * (2 * LCR))
    hint_witness(lcr[0:NSUB * (2 * LCR)], "lcr")
    lcz = HeapBuf(NSUB * (64))
    hint_witness(lcz[0:NSUB * (64)], "lcz")
    matp = HeapBuf(NSUB * (1))
    hint_witness(matp[0:NSUB * (1)], "matpart")
    shv = HeapBuf(NSUB * (256))
    hint_witness(shv[0:NSUB * (256)], "shv")
    lsc = HeapBuf(NSUB * (LSC_LEN))
    hint_witness(lsc[0:NSUB * (LSC_LEN)], "lsc")
    lrows = HeapBuf(NSUB * (LROWS_LEN))
    hint_witness(lrows[0:NSUB * (LROWS_LEN)], "lrows")
    lpaths = HeapBuf(NSUB * (LPATHS_LEN))
    hint_witness(lpaths[0:NSUB * (LPATHS_LEN)], "lpaths")
    lsbits = HeapBuf(NSUB * (LSBITS_LEN))
    hint_witness(lsbits[0:NSUB * (LSBITS_LEN)], "lsbits")
    lfpb = HeapBuf(NSUB * (LFPB_LEN))
    hint_witness(lfpb[0:NSUB * (LFPB_LEN)], "lfpb")
    lyr = HeapBuf(NSUB * (YR_LEN))
    hint_witness(lyr[0:NSUB * (YR_LEN)], "lyr")
    spi = HeapBuf(NSUB * 2)
    hint_witness(spi[0:NSUB * 2], "spi")
    rta = HeapBuf(NSUB * NLEVELS)
    hint_witness(rta[0:NSUB * NLEVELS], "rta")
    rtb = HeapBuf(NSUB * NLEVELS)
    hint_witness(rtb[0:NSUB * NLEVELS], "rtb")
    fnn = HeapBuf(NSUB * LENRIS)
    hint_witness(fnn[0:NSUB * LENRIS], "fnn")
    cvh = HeapBuf(NSUB * 5)
    hint_witness(cvh[0:NSUB * 5], "cvh")
    bscr = HeapBuf(2 * KBCV)
    hint_witness(bscr[0:2 * KBCV], "bscr")
    mscr = HeapBuf(4 * KLOG)
    hint_witness(mscr[0:4 * KLOG], "mscr")
    bst = HeapBuf(1)
    hint_witness(bst[0:1], "bst")
    mst = HeapBuf(2)
    hint_witness(mst[0:2], "mst")
    # The dual-basis Frobenius powers dt[128k + i] = DELTA[i]^(2^k) are claim-
    # and sub-independent: build the table once, read-only afterwards.
    dt = HeapBuf(128 * 128)
    for i in unroll(0, 128):
        dt[GEN ** i] = DELTA[i]
    for xk in mul_range(1, GEN ** 127):
        rowd = dt * xk ** 128
        nrowd = rowd * GEN ** 128
        for i in unroll(0, 128):
            dv = rowd[GEN ** i]
            nrowd[GEN ** i] = dv * dv

    # cross-sub buffers holding each sub-proof's deferred-claim data
    dzt = HeapBuf(NSUB * 2 * KBC)
    dsb = HeapBuf(NSUB * 3)
    dwb = HeapBuf(NSUB * 2)
    dal = HeapBuf(NSUB)
    dzz = HeapBuf(NSUB)
    dzr = HeapBuf(NSUB * LCR)
    dlr = HeapBuf(NSUB * LCR)

    for sub in unroll(0, NSUB):
        stream_s = stream * GEN ** (sub * (STREAM_LEN))
        fpb_s = fpb * GEN ** (sub * (128))
        bcv_s = bcv * GEN ** (sub * (NBCV))
        cinv_s = cinv * GEN ** (sub * (1))
        zc1_s = zc1 * GEN ** (sub * (128))
        zcr_s = zcr * GEN ** (sub * (2 * NMLV))
        zcf_s = zcf * GEN ** (sub * (2))
        zinv_s = zinv * GEN ** (sub * (NMLV))
        lcr_s = lcr * GEN ** (sub * (2 * LCR))
        lcz_s = lcz * GEN ** (sub * (64))
        matp_s = matp * GEN ** (sub * (1))
        shv_s = shv * GEN ** (sub * (256))
        lsc_s = lsc * GEN ** (sub * (LSC_LEN))
        lrows_s = lrows * GEN ** (sub * (LROWS_LEN))
        lpaths_s = lpaths * GEN ** (sub * (LPATHS_LEN))
        lsbits_s = lsbits * GEN ** (sub * (LSBITS_LEN))
        lfpb_s = lfpb * GEN ** (sub * (LFPB_LEN))
        lyr_s = lyr * GEN ** (sub * (YR_LEN))
        spi_s = spi * GEN ** (sub * 2)
        rta_s = rta * GEN ** (sub * NLEVELS)
        rtb_s = rtb * GEN ** (sub * NLEVELS)
        fnn_s = fnn * GEN ** (sub * LENRIS)
        cvh_s = cvh * GEN ** (sub * 5)
        # Claim pool: values of every committed-coordinate claim, in decompose order
        # (their points are the GKR ζ's, resolvable from the baked block structure).
        clv = HeapBuf(NCLAIMS)
        # The three GKR leaf points, stored side by side (ZOFF offsets).
        zeta = HeapBuf(3 * MUMAX)

        # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
        pv0 = spi_s[GEN ** 0]
        pv1 = spi_s[GEN ** 1]
        cv0, cv1 = obs(SEEDB0, SEEDB1, pv0)
        cv0, cv1 = obs(cv0, cv1, pv1)
        cv0, cv1 = obs(cv0, cv1, DIG0)
        cv0, cv1 = obs(cv0, cv1, DIG1)
        cur = stream_s

        # ---- announced sizes: log_mem + 6 row counts (assert = baked config) ----
        for i in unroll(0, 7):
            x = cur[GEN ** 0]
            cv0, cv1 = obs(cv0, cv1, x)
            assert x == ANN[i]
            cur = cur * GEN

        # ---- commitment root (2 words), kept for the opening phase ----
        rt0 = cur[GEN ** 0]
        cv0, cv1 = obs(cv0, cv1, rt0)
        cur = cur * GEN
        rt1 = cur[GEN ** 0]
        cv0, cv1 = obs(cv0, cv1, rt1)
        cur = cur * GEN

        # ---- bus: α, grinding, γ ----
        alpha, cv0, cv1 = sqz(cv0, cv1)
        # grinding nonce: raw stream_s word (NOT observed), PoW-checked, then bound.
        nonce = cur[GEN ** 0]
        cur = cur * GEN
        pb = StackBuf(2)
        pb[0] = cv0
        pb[1] = cv1
        pz = StackBuf(2)
        pz[0] = 0
        pz[1] = DS_POW
        pbase = StackBuf(2)
        blake3(pb, pz, pbase)
        pn = StackBuf(2)
        pn[0] = nonce
        pn[1] = DS_POW
        ph = StackBuf(2)
        blake3(pbase, pn, ph)
        dec128(fpb_s, ph[0])
        for b in unroll(0, 8 * GFULL):
            z0 = fpb_s[GEN ** b]
            assert z0 == 0
        for b in unroll(8 * GFULL + 8 - GEXTRA, 8 * GFULL + 8):
            z1 = fpb_s[GEN ** b]
            assert z1 == 0
        cv0, cv1 = absorb(cv0, cv1, nonce, DS_POW)
        gamma, cv0, cv1 = sqz(cv0, cv1)

        # ---- 3× GKR grand product (push / pull / count) ----
        groot = HeapBuf(3)
        gval = HeapBuf(3)
        for s in unroll(0, 3):
            rootv = cur[GEN ** 0]
            cv0, cv1 = obs(cv0, cv1, rootv)
            cur = cur * GEN
            claim = rootv
            rprev = HeapBuf(MUMAX)
            for li in unroll(0, SMU[s]):
                eq_acc = GEN ** 0
                rnew = HeapBuf(MUMAX)
                for j in unroll(0, li):
                    m0 = cur[GEN ** 0]
                    cv0, cv1 = obs(cv0, cv1, m0)
                    cur = cur * GEN
                    m1 = cur[GEN ** 0]
                    cv0, cv1 = obs(cv0, cv1, m1)
                    cur = cur * GEN
                    m2 = cur[GEN ** 0]
                    cv0, cv1 = obs(cv0, cv1, m2)
                    cur = cur * GEN
                    rj = rprev[GEN ** j]
                    lhs = eq_acc * ((1 + rj) * m0 + rj * m1)
                    assert lhs == claim
                    rk, cv0, cv1 = sqz(cv0, cv1)
                    rnew[GEN ** (j + 1)] = rk
                    eq_acc = eq_acc * (1 + rj + rk)
                    # Lagrange at nodes {0, 1, g} with baked inverse denominators.
                    l0 = (rk + 1) * (rk + GG) * ILD0
                    l1 = rk * (rk + GG) * ILD1
                    l2 = rk * (rk + 1) * ILD2
                    claim = eq_acc * (m0 * l0 + m1 * l1 + m2 * l2)
                e0 = cur[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, e0)
                cur = cur * GEN
                e1 = cur[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, e1)
                cur = cur * GEN
                assert claim == eq_acc * e0 * e1
                c, cv0, cv1 = sqz(cv0, cv1)
                claim = e0 + c * (e0 + e1)
                rnew[GEN ** 0] = c
                rprev = rnew
            for t in unroll(0, SMU[s]):
                zeta[GEN ** (ZOFF[s] + t)] = rprev[GEN ** t]
            groot[GEN ** s] = rootv
            gval[GEN ** s] = claim

        # ---- count root nonzero (hinted inverse) ----
        cprod = groot[GEN ** 2] * cinv_s[GEN ** 0]
        assert cprod == 1

        # ---- balance: push_root · d_pull == pull_root · d_push ----
        # d_side = Π_b (γ + Σ_i α^i·FPV[i])^DELTA_b over the side's padded blocks.
        dsur = HeapBuf(2)
        for s in unroll(0, 2):
            d = GEN ** 0
            for b in unroll(SBLK[s], SBLK[s + 1]):
                if BDELTA[b] != 0:
                    fp = 0
                    apw = GEN ** 0
                    for i in unroll(0, BCN[b]):
                        fp = fp + apw * FPV[BC0[b] + i]
                        apw = apw * alpha
                    d = d * (gamma + fp) ** BDELTA[b]
            dsur[GEN ** s] = d
        lhsb = groot[GEN ** 0] * dsur[GEN ** 1]
        rhsb = groot[GEN ** 1] * dsur[GEN ** 0]
        assert lhsb == rhsb

        # ---- 3× leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
        # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
        # committed-coordinate values ride the stream_s (observed, pooled); the Public
        # (bytecode) coordinate values are hinted (bcv_s) and exported as deferred
        # claims; Index coordinates use the factored index MLE.
        ci = 0
        bi = 0
        for s in unroll(0, 3):
            acc = 0
            selsum = 0
            for b in unroll(SBLK[s], SBLK[s + 1]):
                # eq_hi over the ζ coords above κ, against the baked selector bits.
                eqh = GEN ** 0
                for k in unroll(0, SMU[s] - BKAPPA[b]):
                    zk = zeta[GEN ** (ZOFF[s] + BKAPPA[b] + k)]
                    if (BSEL[b] // (2 ** k)) % 2 == 1:
                        eqh = eqh * zk
                    else:
                        eqh = eqh * (1 + zk)
                selsum = selsum + eqh
                # inner fingerprint Σ_i α^i · coord_i(ζ_lo); count side uses α=1,γ=0.
                inner = 0
                apw = GEN ** 0
                for i in unroll(0, BCN[b]):
                    if CT[BC0[b] + i] == 0:
                        cval = CVAL[BC0[b] + i]
                    if CT[BC0[b] + i] == 1:
                        cval = cur[GEN ** 0]
                        cv0, cv1 = obs(cv0, cv1, cval)
                        cur = cur * GEN
                        clv[GEN ** ci] = cval
                        ci = ci + 1
                    if CT[BC0[b] + i] == 2:
                        rawv = cur[GEN ** 0]
                        cv0, cv1 = obs(cv0, cv1, rawv)
                        cur = cur * GEN
                        clv[GEN ** ci] = rawv
                        ci = ci + 1
                        cval = GG * rawv
                    if CT[BC0[b] + i] == 3:
                        cval = GEN ** 0
                        for t in unroll(0, BKAPPA[b]):
                            cval = cval * (1 + zeta[GEN ** (ZOFF[s] + t)] * IDXC[t])
                    if CT[BC0[b] + i] == 4:
                        cval = bcv_s[GEN ** bi]
                        bi = bi + 1
                    if s == 2:
                        inner = inner + cval
                    else:
                        inner = inner + apw * cval
                        apw = apw * alpha
                if s == 2:
                    acc = acc + eqh * inner
                else:
                    acc = acc + eqh * (gamma + inner)
            acc = acc + 1 + selsum
            assert acc == gval[GEN ** s]

        # ---- stacked-bytecode reduction (part of the native protocol) ----
        # The bytecode is ONE multilinear polynomial in KBC + 3 variables (the six
        # encoding columns stacked along three selector bits). Absorb the twelve
        # per-column values, sample three eq challenges, and reduce each point's
        # six claims to B(zeta_lo, sb) = sum_c eq(sb, c) * v_c.
        for k in unroll(0, NBCV):
            cv0, cv1 = obs(cv0, cv1, bcv_s[GEN ** k])
        sb = HeapBuf(3)
        for t in unroll(0, 3):
            sv, cv0, cv1 = sqz(cv0, cv1)
            sb[GEN ** t] = sv
        wbc = HeapBuf(2)
        for s in unroll(0, 2):
            wv = 0
            for c in unroll(0, 6):
                e = GEN ** 0
                for t in unroll(0, 3):
                    if (c // (2 ** t)) % 2 == 1:
                        e = e * sb[GEN ** t]
                    else:
                        e = e * (1 + sb[GEN ** t])
                wv = wv + e * bcv_s[GEN ** (6 * s + c)]
            wbc[GEN ** s] = wv

        # ---- Phase A checkpoint: sponge state matches the mirror ----
        cck = cvh_s[GEN ** 0]
        assert cv0 == cck

        # ---- 6x per-table zerocheck (XOR, MUL, SET, DEREF, JUMP, BLAKE3) ----
        # For each table: eta, the zerocheck point r (tau samples), tau eq-trick
        # rounds (claim starts at 0), then the involved-column evaluations (pooled)
        # and the final AIR check claim == eq_acc * C_t(eta, evals).
        rho = HeapBuf(6 * TAUMAX)
        for t in unroll(0, 6):
            eta, cv0, cv1 = sqz(cv0, cv1)
            rr = HeapBuf(TAUMAX)
            for k in unroll(0, TAU[t]):
                rv, cv0, cv1 = sqz(cv0, cv1)
                rr[GEN ** k] = rv
            claim = 0
            eq_acc = GEN ** 0
            for k in unroll(0, TAU[t]):
                p0 = cur[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, p0)
                cur = cur * GEN
                p1 = cur[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, p1)
                cur = cur * GEN
                p2 = cur[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, p2)
                cur = cur * GEN
                rj = rr[GEN ** k]
                lhs = eq_acc * ((1 + rj) * p0 + rj * p1)
                assert lhs == claim
                rk, cv0, cv1 = sqz(cv0, cv1)
                rho[GEN ** (t * TAUMAX + k)] = rk
                eq_acc = eq_acc * (1 + rj + rk)
                l0 = (rk + 1) * (rk + GG) * ILD0
                l1 = rk * (rk + GG) * ILD1
                l2 = rk * (rk + 1) * ILD2
                claim = eq_acc * (p0 * l0 + p1 * l1 + p2 * l2)
            ee = HeapBuf(16)
            for k in unroll(0, NCOL[t]):
                e = cur[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, e)
                cur = cur * GEN
                ee[GEN ** k] = e
                clv[GEN ** ci] = e
                ci = ci + 1
            # the table's AIR constraint at the final point (ev order = the table's
            # constraint_columns order; formulas mirror tables.rs eval_constraint).
            if t == 0:
                cst = (ee[GEN ** 4] + ee[GEN ** 0] * ee[GEN ** 1]) + eta * (ee[GEN ** 5] + ee[GEN ** 0] * ee[GEN ** 2]) + eta * eta * (ee[GEN ** 6] + ee[GEN ** 0] * ee[GEN ** 3]) + eta * eta * eta * (ee[GEN ** 9] + ee[GEN ** 7] + ee[GEN ** 8])
            if t == 1:
                cst = (ee[GEN ** 4] + ee[GEN ** 0] * ee[GEN ** 1]) + eta * (ee[GEN ** 5] + ee[GEN ** 0] * ee[GEN ** 2]) + eta * eta * (ee[GEN ** 6] + ee[GEN ** 0] * ee[GEN ** 3]) + eta * eta * eta * (ee[GEN ** 9] + ee[GEN ** 7] * ee[GEN ** 8])
            if t == 2:
                cst = ee[GEN ** 2] + ee[GEN ** 0] * ee[GEN ** 1]
            if t == 3:
                src = (1 + ee[GEN ** 8] + ee[GEN ** 9]) * ee[GEN ** 11] + ee[GEN ** 8] * (GG * GG * ee[GEN ** 12]) + ee[GEN ** 9] * ee[GEN ** 0]
                cst = (ee[GEN ** 4] + ee[GEN ** 0] * ee[GEN ** 1]) + eta * (ee[GEN ** 5] + ee[GEN ** 7] * ee[GEN ** 2]) + eta * eta * (ee[GEN ** 6] + ee[GEN ** 0] * ee[GEN ** 3]) + eta * eta * eta * (ee[GEN ** 10] + src)
            if t == 4:
                ft = GG * ee[GEN ** 0]
                addrs = (ee[GEN ** 7] + ee[GEN ** 1] * ee[GEN ** 4]) + eta * (ee[GEN ** 8] + ee[GEN ** 1] * ee[GEN ** 5]) + eta * eta * (ee[GEN ** 9] + ee[GEN ** 1] * ee[GEN ** 6])
                eta3 = eta * eta * eta
                ind_def = eta3 * (ee[GEN ** 14] + ee[GEN ** 10] * ee[GEN ** 13])
                ind_nz = eta3 * eta * (ee[GEN ** 10] * (ee[GEN ** 14] + 1))
                sel_pc = eta3 * eta * eta * (ee[GEN ** 2] + ee[GEN ** 14] * ee[GEN ** 11] + (ee[GEN ** 14] + 1) * ft)
                sel_fp = eta3 * eta * eta * eta * (ee[GEN ** 3] + ee[GEN ** 14] * ee[GEN ** 12] + (ee[GEN ** 14] + 1) * ee[GEN ** 1])
                cst = addrs + ind_def + ind_nz + sel_pc + sel_fp
            if t == 5:
                cst = (ee[GEN ** 6] + ee[GEN ** 0] * ee[GEN ** 1]) + eta * (ee[GEN ** 7] + ee[GEN ** 0] * ee[GEN ** 2]) + eta * eta * (ee[GEN ** 8] + ee[GEN ** 0] * ee[GEN ** 3]) + eta * eta * eta * (ee[GEN ** 9] + ee[GEN ** 0] * ee[GEN ** 4]) + eta * eta * eta * eta * (ee[GEN ** 10] + ee[GEN ** 0] * ee[GEN ** 5])
            assert claim == eq_acc * cst

        # ---- Phase B checkpoint ----
        cck = cvh_s[GEN ** 1]
        assert cv0 == cck

        # ---- public-input binding claim: MEM(r_m, 0..) = interp(pi0, pi1, r_m) ----
        rm, cv0, cv1 = sqz(cv0, cv1)
        piv = pv0 + rm * (pv0 + pv1)
        clv[GEN ** ci] = piv
        ci = ci + 1

        # ---- BLAKE3 constant-pin claims (on q_pkd, at the pin bus point) ----
        # prefix = MLE of [1;NB3, 0;...] at the pin point (the first BLAKE3
        # value-column bus claim's ζ_lo: NLOGB3 coords starting at zeta[PINZOFF]):
        # one eq-term per set bit of NB3, over the aligned block's high bits.
        prefix = 0
        base = 0
        for tb in unroll(0, NLOGB3 + 1):
            t = NLOGB3 - tb
            if (NB3 // (2 ** t)) % 2 == 1:
                a = base // (2 ** t)
                e = GEN ** 0
                for iv in unroll(0, NLOGB3 - t):
                    zk = zeta[GEN ** (PINZOFF + t + iv)]
                    if (a // (2 ** iv)) % 2 == 1:
                        e = e * zk
                    else:
                        e = e * (1 + zk)
                prefix = prefix + e
                base = base + 2 ** t
        for pk in unroll(0, 3):
            clv[GEN ** ci] = PINV[pk] * prefix
            ci = ci + 1

        # ---- Phase C checkpoint ----
        cck = cvh_s[GEN ** 2]
        assert cv0 == cck

        # ---- flock reduction: bind_statement ----
        cv0, cv1 = absorb(cv0, cv1, 13, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, R1CSLBL, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, SD0, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, SD1, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, rt0, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, rt1, DS_BYTE)

        # ---- flock zerocheck (univariate skip, k_skip = 6) ----
        cv0, cv1 = absorb(cv0, cv1, 18, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, ZCLBLA, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, ZCLBLB, DS_BYTE)
        # the full r vector: 6 sampled skips, 7 fixed inner, MR1CS-13 sampled outer.
        zr = HeapBuf(MR1CS)
        for i in unroll(0, 6):
            rv, cv0, cv1 = sqz(cv0, cv1)
            zr[GEN ** i] = rv
        for i in unroll(0, 7):
            zr[GEN ** (6 + i)] = INNER7[i]
        for i in unroll(0, MR1CS - 13):
            rv, cv0, cv1 = sqz(cv0, cv1)
            zr[GEN ** (13 + i)] = rv
        # observe round-1 messages (ab then c), sample z.
        for i in unroll(0, 128):
            cv0, cv1 = obs(cv0, cv1, zc1_s[GEN ** i])
        zz, cv0, cv1 = sqz(cv0, cv1)
        # interpolate P^C(z) on the Lambda domain (phi8 nodes 64..128): prefix/
        # suffix numerator products with baked inverse denominators.
        lpre = HeapBuf(65)
        lpre[GEN ** 0] = GEN ** 0
        for i in unroll(0, 64):
            lpre[GEN ** (i + 1)] = lpre[GEN ** i] * (zz + PHI[64 + i])
        lsuf = HeapBuf(65)
        lsuf[GEN ** 64] = GEN ** 0
        for i in unroll(0, 64):
            lsuf[GEN ** (63 - i)] = lsuf[GEN ** (64 - i)] * (zz + PHI[64 + 63 - i])
        ceval = 0
        for i in unroll(0, 64):
            ceval = ceval + lpre[GEN ** i] * lsuf[GEN ** (i + 1)] * ILAM[i] * zc1_s[GEN ** (64 + i)]
        # combined interpolation at z over ALL 128 phi8 nodes (Lambda values only;
        # the S half is zero by the zerocheck identity). The Lambda-node numerators
        # reuse lpre/lsuf: the full-domain product only adds the S-half factor.
        sfull = GEN ** 0
        for i in unroll(0, 64):
            sfull = sfull * (zz + PHI[i])
        comb = 0
        for i in unroll(0, 64):
            comb = comb + lpre[GEN ** i] * lsuf[GEN ** (i + 1)] * ICMB[i] * (zc1_s[GEN ** i] + zc1_s[GEN ** (64 + i)])
        comb = comb * sfull
        crun = comb + ceval
        # multilinear rounds.
        zrho = HeapBuf(NMLV)
        for i in unroll(0, 7):
            g1 = zcr_s[GEN ** (2 * i)]
            gi = zcr_s[GEN ** (2 * i + 1)]
            req = zr[GEN ** (6 + i)]
            g0 = (crun + req * g1) * I7INV[i]
            cv0, cv1 = obs(cv0, cv1, g1)
            cv0, cv1 = obs(cv0, cv1, gi)
            rhov, cv0, cv1 = sqz(cv0, cv1)
            zrho[GEN ** i] = rhov
            crun = g0 * (1 + rhov) + g1 * rhov + gi * rhov * (1 + rhov)
        for i in unroll(7, NMLV):
            g1 = zcr_s[GEN ** (2 * i)]
            gi = zcr_s[GEN ** (2 * i + 1)]
            req = zr[GEN ** (6 + i)]
            ionepr = zinv_s[GEN ** i]
            chkinv = (1 + req) * ionepr
            assert chkinv == 1
            g0 = (crun + req * g1) * ionepr
            cv0, cv1 = obs(cv0, cv1, g1)
            cv0, cv1 = obs(cv0, cv1, gi)
            rhov, cv0, cv1 = sqz(cv0, cv1)
            zrho[GEN ** i] = rhov
            crun = g0 * (1 + rhov) + g1 * rhov + gi * rhov * (1 + rhov)
        # final: crun == a_eval * b_eval; observe both.
        fa = zcf_s[GEN ** 0]
        fb = zcf_s[GEN ** 1]
        fchk = fa * fb
        assert crun == fchk
        cv0, cv1 = obs(cv0, cv1, fa)
        cv0, cv1 = obs(cv0, cv1, fb)

        # ---- flock lincheck (matrix evaluation DEFERRED) ----
        cv0, cv1 = absorb(cv0, cv1, 17, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, LCLBLA, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, LCLBLB, DS_BYTE)
        lal, cv0, cv1 = sqz(cv0, cv1)
        lbe, cv0, cv1 = sqz(cv0, cv1)
        lrun = lal * fa + fb + lbe
        lrr = HeapBuf(LCR)
        for i in unroll(0, LCR):
            e1 = lcr_s[GEN ** (2 * i)]
            ei = lcr_s[GEN ** (2 * i + 1)]
            cv0, cv1 = obs(cv0, cv1, e1)
            cv0, cv1 = obs(cv0, cv1, ei)
            rv, cv0, cv1 = sqz(cv0, cv1)
            lrr[GEN ** i] = rv
            e0 = lrun + e1
            c1q = e0 + e1 + ei
            lrun = ei * rv * rv + c1q * rv + e0
        for i in unroll(0, 64):
            cv0, cv1 = obs(cv0, cv1, lcz_s[GEN ** i])
        # final consistency: running == matpart (DEFERRED) + beta * pin term. The
        # const-pin column folds through the top-variable bindings: weight =
        # prod_j (bit_{klog-1-j}(PINCOL) ? r_j : 1+r_j), surviving z_partial index
        # = PINCOL low 6 bits.
        pinw = lbe
        for j in unroll(0, LCR):
            if (PINCOL // (2 ** (KLOG - 1 - j))) % 2 == 1:
                pinw = pinw * lrr[GEN ** j]
            else:
                pinw = pinw * (1 + lrr[GEN ** j])
        pinw = pinw * lcz_s[GEN ** (PINCOL % 64)]
        mp = matp_s[GEN ** 0]
        lchk = mp + pinw
        assert lrun == lchk
        # fresh z_skip; w = <lagrange_S(r_inner_skip), z_partial> (phi8 nodes 0..64).
        lsk, cv0, cv1 = sqz(cv0, cv1)
        spre = HeapBuf(65)
        spre[GEN ** 0] = GEN ** 0
        for i in unroll(0, 64):
            spre[GEN ** (i + 1)] = spre[GEN ** i] * (lsk + PHI[i])
        ssuf = HeapBuf(65)
        ssuf[GEN ** 64] = GEN ** 0
        for i in unroll(0, 64):
            ssuf[GEN ** (63 - i)] = ssuf[GEN ** (64 - i)] * (lsk + PHI[63 - i])
        lw = 0
        for i in unroll(0, 64):
            lw = lw + spre[GEN ** i] * ssuf[GEN ** (i + 1)] * ISDOM[i] * lcz_s[GEN ** i]

        # ---- Phase D checkpoint ----
        cck = cvh_s[GEN ** 3]
        assert cv0 == cck

        # ---- stacked mixed opening: ring-switch fronts + claim combination ----
        cv0, cv1 = absorb(cv0, cv1, 23, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, OBLBLA, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, OBLBLB, DS_BYTE)
        # Ring-switch claim 0 (ab): value lw, z_skip = lsk, x_outer[0] = lrr[LCR-1]
        # (x_inner_rest is the REVERSED lincheck round vector). Claim 1 (c): value
        # ceval, z_skip = zz, x_outer[0] = zr[6].
        tclv = HeapBuf(2)
        rsqv = HeapBuf(2)
        ckb = HeapBuf(2 * 128)
        zvb = HeapBuf(2 * QPKDV)
        rdp = HeapBuf(14)
        for rs in unroll(0, 2):
            cv0, cv1 = absorb(cv0, cv1, 20, DS_LEN)
            cv0, cv1 = absorb(cv0, cv1, RSLBLA, DS_BYTE)
            cv0, cv1 = absorb(cv0, cv1, RSLBLB, DS_BYTE)
            for i in unroll(0, 128):
                cv0, cv1 = obs(cv0, cv1, shv_s[GEN ** (128 * rs + i)])
            # claim check: weights[i] = lambda_{i&63}(z_skip) * eq(x_outer0, i>>6).
            if rs == 0:
                zsk = lsk
                xo0 = lrr[GEN ** (LCR - 1)]
                clm = lw
            else:
                zsk = zz
                xo0 = zr[GEN ** 6]
                clm = ceval
            wpre = HeapBuf(65)
            wpre[GEN ** 0] = GEN ** 0
            for i in unroll(0, 64):
                wpre[GEN ** (i + 1)] = wpre[GEN ** i] * (zsk + PHI[i])
            wsuf = HeapBuf(65)
            wsuf[GEN ** 64] = GEN ** 0
            for i in unroll(0, 64):
                wsuf[GEN ** (63 - i)] = wsuf[GEN ** (64 - i)] * (zsk + PHI[63 - i])
            cchk = 0
            for i in unroll(0, 64):
                lam = wpre[GEN ** i] * wsuf[GEN ** (i + 1)] * ISDOM[i]
                cchk = cchk + lam * ((1 + xo0) * shv_s[GEN ** (128 * rs + i)] + xo0 * shv_s[GEN ** (128 * rs + 64 + i)])
            assert cchk == clm
            # r'' (7 samples).
            for i in unroll(0, 7):
                rv, cv0, cv1 = sqz(cv0, cv1)
                rdp[GEN ** (7 * rs + i)] = rv
            # w = eq tensor of the seven r'' coords (doubling tree, final 128 at 126).
            wq = HeapBuf(254)
            wq[GEN ** 0] = 1 + rdp[GEN ** (7 * rs)]
            wq[GEN ** 1] = rdp[GEN ** (7 * rs)]
            for t in unroll(1, 7):
                for i in unroll(0, 2 ** t):
                    pw = wq[GEN ** (2 ** t - 2 + i)]
                    wq[GEN ** (2 ** (t + 1) - 2 + i)] = pw * (1 + rdp[GEN ** (7 * rs + t)])
                    wq[GEN ** (2 ** (t + 1) - 2 + 2 ** t + i)] = pw * rdp[GEN ** (7 * rs + t)]
            # One runtime loop over the Frobenius levels k computes both
            # c_k = sum_i w_i * dt[k][i] (stored for the terminal eval_rs_eq)
            # and the transposed claim T = sum_k c_k * S_k, where
            # S_k = sum_j x^j * shv_j^(2^k) accumulates by Horner in x and the
            # s_hat_v powers evolve by squaring.
            ytab = HeapBuf(129 * 128)
            for j in unroll(0, 128):
                ytab[GEN ** j] = shv_s[GEN ** (128 * rs + j)]
            ckrow = ckb * GEN ** (128 * rs)
            tacc = HeapBuf(129)
            tacc[GEN ** 0] = 0
            for xk in mul_range(1, GEN ** 128):
                rowd = dt * xk ** 128
                rowy = ytab * xk ** 128
                nrowy = rowy * GEN ** 128
                cacc = 0
                for i in unroll(0, 128):
                    cacc = cacc + wq[GEN ** (126 + i)] * rowd[GEN ** i]
                xh = StackBuf(1)
                xh[0] = 2
                sk = 0
                for j in unroll(0, 128):
                    yv = rowy[GEN ** (127 - j)]
                    sk = sk * xh[0] + yv
                    nrowy[GEN ** (127 - j)] = yv * yv
                ckrow[xk] = cacc
                tacc[xk * GEN] = tacc[xk] + cacc * sk
            tclv[GEN ** rs] = tacc[GEN ** 128]
            # z_vals for eval_rs_eq (the x_outer tail), used at the opening terminal.
            if rs == 0:
                for t in unroll(0, LCR - 1):
                    zvb[GEN ** t] = lrr[GEN ** (LCR - 2 - t)]
                for t in unroll(0, NMLV - LCR):
                    zvb[GEN ** (LCR - 1 + t)] = zrho[GEN ** (LCR + t)]
            else:
                for t in unroll(0, QPKDV):
                    zvb[GEN ** (QPKDV + t)] = zr[GEN ** (7 + t)]
        # gamma-combine the two transposed sumcheck claims (computed in-circuit).
        g0, cv0, cv1 = sqz(cv0, cv1)
        g1, cv0, cv1 = sqz(cv0, cv1)
        target = g0 * tclv[GEN ** 0] + g1 * tclv[GEN ** 1]
        # ...then every pooled point claim, each labeled and observed.
        for j in unroll(0, NCL):
            cv0, cv1 = absorb(cv0, cv1, 26, DS_LEN)
            cv0, cv1 = absorb(cv0, cv1, PDLBLA, DS_BYTE)
            cv0, cv1 = absorb(cv0, cv1, PDLBLB, DS_BYTE)
            cv0, cv1 = obs(cv0, cv1, clv[GEN ** j])
        gpd = HeapBuf(NCL)
        for j in unroll(0, NCL):
            gv, cv0, cv1 = sqz(cv0, cv1)
            gpd[GEN ** j] = gv
            target = target + gv * clv[GEN ** j]

        # ---- Phase E1 checkpoint ----
        cck = cvh_s[GEN ** 4]
        assert cv0 == cck

        # ================= the Ligerito opening core (stacked, m = STACK) ========

        ris = HeapBuf(LENRIS)
        lbet = HeapBuf(NLEVELS)
        lenf = HeapBuf(NLEVELS)
        law = HeapBuf(NLEVELS * MAXQ)
        qfb = HeapBuf(QP_LEN)
        qbp = HeapBuf(QP_LEN)

        cv0, cv1 = absorb(cv0, cv1, 23, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, LIGLBLA, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, LIGLBLB, DS_BYTE)
        cv0, cv1 = obs(cv0, cv1, target)
        cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, rt0, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, rt1, DS_BYTE)

        lsp = lsc_s
        lu0 = lsp[GEN ** 0]
        cv0, cv1 = obs(cv0, cv1, lu0)
        lu2 = lsp[GEN ** 1]
        cv0, cv1 = obs(cv0, cv1, lu2)
        lsp = lsp * GEN ** 2
        lqc = lu0
        lqb = target + lu2
        lqa = lu2
        tr = target

        for lvl in unroll(0, NLEVELS):
            for j in unroll(0, KLVL[lvl]):
                lg = FOLDBASE[lvl] + j
                if BITS[lg] != 0:
                    lpb = StackBuf(2)
                    lpb[0] = cv0
                    lpb[1] = cv1
                    lpz = StackBuf(2)
                    lpz[0] = 0
                    lpz[1] = DS_POW
                    lpbase = StackBuf(2)
                    blake3(lpb, lpz, lpbase)
                    lpn = StackBuf(2)
                    lpn[0] = fnn_s[GEN ** lg]
                    lpn[1] = DS_POW
                    lph = StackBuf(2)
                    blake3(lpbase, lpn, lph)
                    dec128(lfpb_s * GEN ** (128 * lg), lph[0])
                    for b in unroll(0, 8 * FULL[lg]):
                        lz0 = lfpb_s[GEN ** (128 * lg + b)]
                        assert lz0 == 0
                    for b in unroll(8 * FULL[lg] + 8 - EXTRA8[lg], 8 * FULL[lg] + 8):
                        lz1 = lfpb_s[GEN ** (128 * lg + b)]
                        assert lz1 == 0
                    fnv = fnn_s[GEN ** lg]
                    cv0, cv1 = absorb(cv0, cv1, fnv, DS_POW)
                lri, cv0, cv1 = sqz(cv0, cv1)
                ris[GEN ** (FOLDBASE[lvl] + j)] = lri
                tr = lqc + lri * lqb + lri * lri * lqa
                la = lsp[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, la)
                lb = lsp[GEN ** 1]
                cv0, cv1 = obs(cv0, cv1, lb)
                lsp = lsp * GEN ** 2
                lqc = la
                lqb = tr + lb
                lqa = lb

            if lvl == R:
                for iy in unroll(0, YR_LEN):
                    cv0, cv1 = obs(cv0, cv1, lyr_s[GEN ** iy])
            else:
                cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
                nra = rta_s[GEN ** (lvl + 1)]
                nrb = rtb_s[GEN ** (lvl + 1)]
                cv0, cv1 = absorb(cv0, cv1, nra, DS_BYTE)
                cv0, cv1 = absorb(cv0, cv1, nrb, DS_BYTE)
            cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)

            c0b = HeapBuf(MAXNSQ + 1)
            c1b = HeapBuf(MAXNSQ + 1)
            c0b[GEN ** 0] = cv0
            c1b[GEN ** 0] = cv1
            for xs in mul_range(1, GEN ** NSQ[lvl]):
                chq, nc0, nc1 = sqz(c0b[xs], c1b[xs])
                c0b[xs * GEN] = nc0
                c1b[xs * GEN] = nc1
                lbp = lsbits_s * GEN ** SBITSOFF[lvl] * xs ** 128
                lqpp = xs ** PER[lvl]
                decq(lbp, chq, qfb * GEN ** QPOFF[lvl] * lqpp, qbp * GEN ** QPOFF[lvl] * lqpp, DEPTH[lvl], PER[lvl])
            cv0 = c0b[GEN ** NSQ[lvl]]
            cv1 = c1b[GEN ** NSQ[lvl]]

            lalr = HeapBuf(MAXNI)
            for t in unroll(0, ALPHALEN[lvl]):
                lav, cv0, cv1 = sqz(cv0, cv1)
                lalr[GEN ** t] = lav
            leqt = HeapBuf(MAXNI)
            for i in unroll(0, NUMINTER[lvl]):
                lp = GEN ** 0
                for c in unroll(0, KLVL[lvl]):
                    lrc = ris[GEN ** (FOLDBASE[lvl] + c)]
                    if (i // (2 ** c)) % 2 == 1:
                        lp = lp * lrc
                    else:
                        lp = lp * (1 + lrc)
                leqt[GEN ** i] = lp
            for i in unroll(0, QUERIES[lvl]):
                lp = GEN ** 0
                for c in unroll(0, ALPHALEN[lvl]):
                    lac = lalr[GEN ** c]
                    if (i // (2 ** c)) % 2 == 1:
                        lp = lp * lac
                    else:
                        lp = lp * (1 + lac)
                law[GEN ** (lvl * MAXQ + i)] = lp

            accE = HeapBuf(MAXQ + 1)
            accE[GEN ** 0] = 0
            for xe in mul_range(1, GEN ** QUERIES[lvl]):
                lrb = xe ** NUMINTER[lvl]
                lst = StackBuf(2)
                lst[0] = GEN ** NBYTES[lvl]
                lst[1] = 0
                ldot = 0
                for jb in unroll(0, BLOCKS[lvl]):
                    lmm = StackBuf(2)
                    lmm[0] = lrows_s[GEN ** ROWOFF[lvl] * lrb * GEN ** (2 * jb)]
                    lmm[1] = lrows_s[GEN ** ROWOFF[lvl] * lrb * GEN ** (2 * jb + 1)]
                    loo = StackBuf(2)
                    blake3(lst, lmm, loo)
                    lst = loo
                    ldot = ldot + lmm[0] * leqt[GEN ** (2 * jb)] + lmm[1] * leqt[GEN ** (2 * jb + 1)]
                ld0 = lst[0]
                ld1 = lst[1]
                accE[xe * GEN] = accE[xe] + law[GEN ** (lvl * MAXQ) * xe] * ldot
                lsbp = qbp[GEN ** QPOFF[lvl] * xe]
                lpb2 = xe ** (2 * DEPTH[lvl])
                for lw2 in unroll(0, DEPTH[lvl]):
                    ls0 = lpaths_s[GEN ** PATHOFF[lvl] * lpb2 * GEN ** (2 * lw2)]
                    ls1 = lpaths_s[GEN ** PATHOFF[lvl] * lpb2 * GEN ** (2 * lw2 + 1)]
                    lbit = lsbp[GEN ** lw2]
                    lt0 = ld0 + ls0
                    lt1 = ld1 + ls1
                    lla = StackBuf(2)
                    lla[0] = ld0 + lbit * lt0
                    lla[1] = ld1 + lbit * lt1
                    lra = StackBuf(2)
                    lra[0] = lt0 + lla[0]
                    lra[1] = lt1 + lla[1]
                    loo2 = StackBuf(2)
                    blake3(lla, lra, loo2)
                    ld0 = loo2[0]
                    ld1 = loo2[1]
                if lvl == 0:
                    assert ld0 == rt0
                    assert ld1 == rt1
                else:
                    lra = rta_s[GEN ** lvl]
                    lrb2 = rtb_s[GEN ** lvl]
                    assert ld0 == lra
                    assert ld1 == lrb2
            lenf[GEN ** lvl] = accE[GEN ** QUERIES[lvl]]

            if lvl == R:
                lbl2, cv0, cv1 = sqz(cv0, cv1)
                lbet[GEN ** lvl] = lbl2
                tr = tr + lbl2 * lenf[GEN ** lvl]
            else:
                liu0 = lsp[GEN ** 0]
                cv0, cv1 = obs(cv0, cv1, liu0)
                liu2 = lsp[GEN ** 1]
                cv0, cv1 = obs(cv0, cv1, liu2)
                lsp = lsp * GEN ** 2
                lbl2, cv0, cv1 = sqz(cv0, cv1)
                lbet[GEN ** lvl] = lbl2
                le = lenf[GEN ** lvl]
                lqc = lqc + lbl2 * liu0
                lqb = lqb + lbl2 * (le + liu2)
                lqa = lqa + lbl2 * liu2
                tr = tr + lbl2 * le

        # ---- residual (per level, novel basis) ----
        innerbuf = HeapBuf(NLEVELS + 1)
        innerbuf[GEN ** 0] = 0
        for lvl in unroll(0, NLEVELS):
            accR = HeapBuf(MAXQ + 1)
            accR[GEN ** 0] = 0
            for xr in mul_range(1, GEN ** QUERIES[lvl]):
                wbuf = StackBuf(MAXLMC)
                ls = qfb[GEN ** QPOFF[lvl] * xr]
                wbuf[0] = ls * IVK[SVKOFF[lvl]]
                for t in unroll(1, LMC[lvl]):
                    ls = ls * ls + SVK[SVKOFF[lvl] + t - 1] * ls
                    wbuf[t] = ls * IVK[SVKOFF[lvl] + t]
                lprefix = GEN ** 0
                for t in unroll(0, PREFIXLEN[lvl]):
                    lrc = ris[GEN ** (RISSTART[lvl] + t)]
                    lprefix = lprefix * (1 + lrc * (1 + wbuf[t]))
                sfw = StackBuf(2 * YR_LOG_N)
                for j in unroll(0, YR_LOG_N):
                    sfw[2 * j] = GEN ** 0
                    sfw[2 * j + 1] = wbuf[PREFIXLEN[lvl] + j]
                lsy = foldyr(lyr_s, sfw, 0)
                accR[xr * GEN] = accR[xr] + law[GEN ** (lvl * MAXQ) * xr] * lprefix * lsy
            innerbuf[GEN ** (lvl + 1)] = innerbuf[GEN ** lvl] + lbet[GEN ** lvl] * accR[GEN ** QUERIES[lvl]]

        # ---- generalized eval_b terminal ----
        # Per pooled claim j: eqbase_j = eq(low point, ris) x eq(selector low bits,
        # remaining ris coords); its full weight lands at residual slot YT[j]. The
        # ring-switch part (deferred rsq values) lands at slot YRS with the qpkd
        # selector eq over ris[QPKDV..].
        ebase = HeapBuf(NCL)
        for j in unroll(0, NCL):
            eb = GEN ** 0
            if CPBUF[j] == 0:
                for k in unroll(0, CPLEN[j] - NOVER[j]):
                    eb = eb * (1 + zeta[GEN ** (CPOFF[j] + k)] + ris[GEN ** k])
            if CPBUF[j] == 1:
                for k in unroll(0, CPLEN[j] - NOVER[j]):
                    eb = eb * (1 + rho[GEN ** (CPOFF[j] + k)] + ris[GEN ** k])
            if CPBUF[j] == 2:
                eb = 1 + rm + ris[GEN ** 0]
                for k in unroll(1, CPLEN[j]):
                    eb = eb * (1 + ris[GEN ** k])
            if CPBUF[j] == 3:
                for k in unroll(0, 7):
                    if (CSLOT[j] // (2 ** k)) % 2 == 1:
                        eb = eb * ris[GEN ** k]
                    else:
                        eb = eb * (1 + ris[GEN ** k])
                for k in unroll(0, CPLEN[j]):
                    eb = eb * (1 + zeta[GEN ** (CPOFF[j] + k)] + ris[GEN ** (7 + k)])
            # selector part over the ris coords above the claim's low span (SELN
            # baked as max(0, LENRIS - nvt); empty when the point overlaps y).
            nvt = CPLEN[j]
            if CPBUF[j] == 3:
                nvt = 7 + CPLEN[j]
            for k in unroll(0, SELN[j]):
                if (CSEL[j] // (2 ** k)) % 2 == 1:
                    eb = eb * ris[GEN ** (nvt + k)]
                else:
                    eb = eb * (1 + ris[GEN ** (nvt + k)])
            ebase[GEN ** j] = eb * gpd[GEN ** j]
        # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
        # (the telescoped product formula; z powers evolve by squaring per k).
        rq = HeapBuf(QPKDV)
        for j in unroll(0, QPKDV):
            rq[GEN ** j] = 1 + ris[GEN ** j]
        for rs in unroll(0, 2):
            zpt = HeapBuf(129 * QPKDV)
            for j in unroll(0, QPKDV):
                zpt[GEN ** j] = zvb[GEN ** (QPKDV * rs + j)]
            eacc = HeapBuf(129)
            eacc[GEN ** 0] = 0
            ckrow = ckb * GEN ** (128 * rs)
            for xk in mul_range(1, GEN ** 128):
                rowz = zpt * xk ** QPKDV
                nrowz = rowz * GEN ** QPKDV
                prod = GEN ** 0
                for j in unroll(0, QPKDV):
                    zv = rowz[GEN ** j]
                    prod = prod * (zv + rq[GEN ** j])
                    nrowz[GEN ** j] = zv * zv
                eacc[xk * GEN] = eacc[xk] + ckrow[xk] * prod
            rsqv[GEN ** rs] = eacc[GEN ** 128]
        # ring-switch weight base over ris[QPKDV..LENRIS).
        rsb = g0 * rsqv[GEN ** 0] + g1 * rsqv[GEN ** 1]
        for k in unroll(0, LENRIS - QPKDV):
            if (RSSEL // (2 ** k)) % 2 == 1:
                rsb = rsb * ris[GEN ** (QPKDV + k)]
            else:
                rsb = rsb * (1 + ris[GEN ** (QPKDV + k)])
        # inner = sum_y lyr_s[y] * eval_b[y] + the residual sums.
        inner = innerbuf[GEN ** NLEVELS]
        for y in unroll(0, YR_LEN):
            ey = 0
            if y == YRS:
                ey = ey + rsb
            for j in unroll(0, NCL):
                if (y // (2 ** NOVER[j])) == YTHI[j]:
                    f = ebase[GEN ** j]
                    for t in unroll(0, NOVER[j]):
                        if CPBUF[j] == 0:
                            pv = zeta[GEN ** (CPOFF[j] + CPLEN[j] - NOVER[j] + t)]
                        else:
                            pv = rho[GEN ** (CPOFF[j] + CPLEN[j] - NOVER[j] + t)]
                        if (y // (2 ** t)) % 2 == 1:
                            f = f * pv
                        else:
                            f = f * (1 + pv)
                    ey = ey + f
            inner = inner + lyr_s[GEN ** y] * ey
        assert inner == tr


        # ---- save this sub-proof's deferred-claim data for the aggregation ----
        for k in unroll(0, KBC):
            dzt[GEN ** (sub * 2 * KBC + k)] = zeta[GEN ** k]
            dzt[GEN ** (sub * 2 * KBC + KBC + k)] = zeta[GEN ** (MUMAX + k)]
        for k in unroll(0, 3):
            dsb[GEN ** (sub * 3 + k)] = sb[GEN ** k]
        dwb[GEN ** (2 * sub)] = wbc[GEN ** 0]
        dwb[GEN ** (2 * sub + 1)] = wbc[GEN ** 1]
        dal[GEN ** sub] = lal
        dzz[GEN ** sub] = zz
        for k in unroll(0, LCR):
            dzr[GEN ** (sub * LCR + k)] = zrho[GEN ** k]
            dlr[GEN ** (sub * LCR + k)] = lrr[GEN ** k]

    # ================= aggregation: batch the deferred claims =================
    # A fresh transcript absorbs every deferred claim (points and values),
    # samples the RLC coefficients, and verifies the two batching sumchecks of
    # doc.tex §Deferred evaluation claims. Only the reduced claims (one per
    # fixed polynomial) reach the public input.
    h0 = 0
    h1 = 0
    for sub in unroll(0, NSUB):
        h0, h1 = obs(h0, h1, spi[GEN ** (2 * sub)])
        h0, h1 = obs(h0, h1, spi[GEN ** (2 * sub + 1)])
        for k in unroll(0, 2 * KBC):
            h0, h1 = obs(h0, h1, dzt[GEN ** (sub * 2 * KBC + k)])
        for k in unroll(0, 3):
            h0, h1 = obs(h0, h1, dsb[GEN ** (sub * 3 + k)])
        h0, h1 = obs(h0, h1, dwb[GEN ** (2 * sub)])
        h0, h1 = obs(h0, h1, dwb[GEN ** (2 * sub + 1)])
        h0, h1 = obs(h0, h1, dal[GEN ** sub])
        h0, h1 = obs(h0, h1, dzz[GEN ** sub])
        for k in unroll(0, LCR):
            h0, h1 = obs(h0, h1, dzr[GEN ** (sub * LCR + k)])
        for k in unroll(0, LCR):
            h0, h1 = obs(h0, h1, dlr[GEN ** (sub * LCR + k)])
        for k in unroll(0, 64):
            h0, h1 = obs(h0, h1, lcz[GEN ** (sub * 64 + k)])
        h0, h1 = obs(h0, h1, matp[GEN ** sub])

    # ---- bytecode batching sumcheck (KBCV variables, 2*NSUB claims) ----
    gbc = HeapBuf(2 * NSUB)
    brun = 0
    for t in unroll(0, 2 * NSUB):
        gv, h0, h1 = sqz(h0, h1)
        gbc[GEN ** t] = gv
        brun = brun + gv * dwb[GEN ** t]
    rbs = HeapBuf(KBCV)
    for rd in unroll(0, KBCV):
        g1v = bscr[GEN ** (2 * rd)]
        giv = bscr[GEN ** (2 * rd + 1)]
        cv0h, cv1h = obs(h0, h1, g1v)
        h0, h1 = obs(cv0h, cv1h, giv)
        rv, h0, h1 = sqz(h0, h1)
        rbs[GEN ** rd] = rv
        g0v = brun + g1v
        c1v = g0v + g1v + giv
        brun = giv * rv * rv + c1v * rv + g0v
    # terminal: W(r*) in-circuit; the reduced bytecode claim B(r*) is deferred.
    wsum = 0
    for t in unroll(0, 2 * NSUB):
        e = GEN ** 0
        for k in unroll(0, KBC):
            e = e * (1 + dzt[GEN ** ((t // 2) * 2 * KBC + (t % 2) * KBC + k)] + rbs[GEN ** k])
        for k in unroll(0, 3):
            e = e * (1 + dsb[GEN ** ((t // 2) * 3 + k)] + rbs[GEN ** (KBC + k)])
        wsum = wsum + gbc[GEN ** t] * e
    bcstar = bst[GEN ** 0]
    bchk = bcstar * wsum
    assert brun == bchk

    # ---- matrix batching sumcheck (2*KLOG variables, NSUB weighted claims) ----
    gmt = HeapBuf(NSUB)
    mrun = 0
    for t in unroll(0, NSUB):
        gv, h0, h1 = sqz(h0, h1)
        gmt[GEN ** t] = gv
        mrun = mrun + gv * matp[GEN ** t]
    rms = HeapBuf(2 * KLOG)
    for rd in unroll(0, 2 * KLOG):
        g1v = mscr[GEN ** (2 * rd)]
        giv = mscr[GEN ** (2 * rd + 1)]
        cv0h, cv1h = obs(h0, h1, g1v)
        h0, h1 = obs(cv0h, cv1h, giv)
        rv, h0, h1 = sqz(h0, h1)
        rms[GEN ** rd] = rv
        g0v = mrun + g1v
        c1v = g0v + g1v + giv
        mrun = giv * rv * rv + c1v * rv + g0v
    # terminal weights: U_t(r*) = urow_t(r*_row) * wcol_t(r*_col), with
    # urow = (sum_i L_i(zz_t) eq(r*[0..6], i)) * eq(zrho_t, r*[6..KLOG]) and
    # wcol = (sum_i z_partial_t[i] eq(r*[KLOG..KLOG+6], i)) * prod_j (1 + lrr_j
    # + r*[2*KLOG-1-j]) (the lincheck binds column variables top-down).
    eqr = HeapBuf(126)
    eqr[GEN ** 0] = 1 + rms[GEN ** 0]
    eqr[GEN ** 1] = rms[GEN ** 0]
    for t in unroll(1, 6):
        for i in unroll(0, 2 ** t):
            pw = eqr[GEN ** (2 ** t - 2 + i)]
            eqr[GEN ** (2 ** (t + 1) - 2 + i)] = pw * (1 + rms[GEN ** t])
            eqr[GEN ** (2 ** (t + 1) - 2 + 2 ** t + i)] = pw * rms[GEN ** t]
    eqc = HeapBuf(126)
    eqc[GEN ** 0] = 1 + rms[GEN ** KLOG]
    eqc[GEN ** 1] = rms[GEN ** KLOG]
    for t in unroll(1, 6):
        for i in unroll(0, 2 ** t):
            pw = eqc[GEN ** (2 ** t - 2 + i)]
            eqc[GEN ** (2 ** (t + 1) - 2 + i)] = pw * (1 + rms[GEN ** (KLOG + t)])
            eqc[GEN ** (2 ** (t + 1) - 2 + 2 ** t + i)] = pw * rms[GEN ** (KLOG + t)]
    wam = 0
    wbm = 0
    for t in unroll(0, NSUB):
        zzv = dzz[GEN ** t]
        lpre2 = HeapBuf(65)
        lpre2[GEN ** 0] = GEN ** 0
        for i in unroll(0, 64):
            lpre2[GEN ** (i + 1)] = lpre2[GEN ** i] * (zzv + PHI[i])
        lsuf2 = HeapBuf(65)
        lsuf2[GEN ** 64] = GEN ** 0
        for i in unroll(0, 64):
            lsuf2[GEN ** (63 - i)] = lsuf2[GEN ** (64 - i)] * (zzv + PHI[63 - i])
        urow = 0
        for i in unroll(0, 64):
            urow = urow + lpre2[GEN ** i] * lsuf2[GEN ** (i + 1)] * ISDOM[i] * eqr[GEN ** (62 + i)]
        for k in unroll(0, LCR):
            urow = urow * (1 + dzr[GEN ** (t * LCR + k)] + rms[GEN ** (6 + k)])
        wcol = 0
        for i in unroll(0, 64):
            wcol = wcol + lcz[GEN ** (t * 64 + i)] * eqc[GEN ** (62 + i)]
        for j in unroll(0, LCR):
            wcol = wcol * (1 + dlr[GEN ** (t * LCR + j)] + rms[GEN ** (2 * KLOG - 1 - j)])
        u = urow * wcol
        wam = wam + gmt[GEN ** t] * dal[GEN ** t] * u
        wbm = wbm + gmt[GEN ** t] * u
    astar = mst[GEN ** 0]
    mbstar = mst[GEN ** 1]
    mchk = astar * wam + mbstar * wbm
    assert mrun == mchk

    # ---- bind the sub statements + the reduced claims to the public input ----
    e0 = 0
    e1 = 0
    for sub in unroll(0, NSUB):
        e0, e1 = obs(e0, e1, spi[GEN ** (2 * sub)])
        e0, e1 = obs(e0, e1, spi[GEN ** (2 * sub + 1)])
    for k in unroll(0, KBCV):
        e0, e1 = obs(e0, e1, rbs[GEN ** k])
    e0, e1 = obs(e0, e1, bcstar)
    for k in unroll(0, 2 * KLOG):
        e0, e1 = obs(e0, e1, rms[GEN ** k])
    e0, e1 = obs(e0, e1, astar)
    e0, e1 = obs(e0, e1, mbstar)
    pp = GEN ** 0
    pia = pp[1]
    pib = pp[GEN]
    assert pia == e0
    assert pib == e1
    return
