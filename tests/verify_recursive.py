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

SEED0 = SEED0_PLACEHOLDER
SEED1 = SEED1_PLACEHOLDER
STREAM_LEN = STREAM_LEN_PLACEHOLDER
ANN = ANN_PLACEHOLDER
GFULL = GFULL_PLACEHOLDER
GEXTRA = GEXTRA_PLACEHOLDER
GG = GG_PLACEHOLDER
ILD0 = ILD0_PLACEHOLDER
ILD1 = ILD1_PLACEHOLDER
ILD2 = ILD2_PLACEHOLDER
CVCHK_A = CVCHK_A_PLACEHOLDER

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
EVOFF = EVOFF_PLACEHOLDER
TAUMAX = TAUMAX_PLACEHOLDER
EVTOT = EVTOT_PLACEHOLDER
CVCHK_B = CVCHK_B_PLACEHOLDER
# Phase C: the public input (baked; the seed already binds it), the real BLAKE3
# count + pin-point location, and the three public pin constants.
PI0 = PI0_PLACEHOLDER
PI1 = PI1_PLACEHOLDER
NB3 = NB3_PLACEHOLDER
NLOGB3 = NLOGB3_PLACEHOLDER
PINZOFF = PINZOFF_PLACEHOLDER
PINV = PINV_PLACEHOLDER
CVCHK_C = CVCHK_C_PLACEHOLDER
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
CVCHK_D = CVCHK_D_PLACEHOLDER
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
CVCHK_E1 = CVCHK_E1_PLACEHOLDER
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
ROOTA = ROOTA_PLACEHOLDER
ROOTB = ROOTB_PLACEHOLDER
FOLDBASE = FOLDBASE_PLACEHOLDER
ROWOFF = ROWOFF_PLACEHOLDER
PATHOFF = PATHOFF_PLACEHOLDER
SBITSOFF = SBITSOFF_PLACEHOLDER
SVKOFF = SVKOFF_PLACEHOLDER
BITS = BITS_PLACEHOLDER
FULL = FULL_PLACEHOLDER
EXTRA8 = EXTRA8_PLACEHOLDER
FN = FN_PLACEHOLDER
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
# Phase F: log rows of the bytecode blocks (the deferred bytecode points).
KBC = KBC_PLACEHOLDER

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
    stream = HeapBuf(STREAM_LEN)
    hint_witness(stream[0:STREAM_LEN], "stream")
    fpb = HeapBuf(128)
    hint_witness(fpb[0:128], "fpb")
    bcv = HeapBuf(NBCV)
    hint_witness(bcv[0:NBCV], "bcv")
    cinv = HeapBuf(1)
    hint_witness(cinv[0:1], "cinv")
    zc1 = HeapBuf(128)
    hint_witness(zc1[0:128], "zc1")
    zcr = HeapBuf(2 * NMLV)
    hint_witness(zcr[0:2 * NMLV], "zcr")
    zcf = HeapBuf(2)
    hint_witness(zcf[0:2], "zcf")
    zinv = HeapBuf(NMLV)
    hint_witness(zinv[0:NMLV], "zinv")
    lcr = HeapBuf(2 * LCR)
    hint_witness(lcr[0:2 * LCR], "lcr")
    lcz = HeapBuf(64)
    hint_witness(lcz[0:64], "lcz")
    matp = HeapBuf(1)
    hint_witness(matp[0:1], "matpart")

    # Claim pool: values of every committed-coordinate claim, in decompose order
    # (their points are the GKR ζ's, resolvable from the baked block structure).
    clv = HeapBuf(NCLAIMS)
    # The three GKR leaf points, stored side by side (ZOFF offsets).
    zeta = HeapBuf(3 * MUMAX)

    # ---- seed (statement pre-bound: pi + inner program digest) ----
    cv0 = SEED0
    cv1 = SEED1
    cur = stream

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
    # grinding nonce: raw stream word (NOT observed), PoW-checked, then bound.
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
    dec128(fpb, ph[0])
    for b in unroll(0, 8 * GFULL):
        z0 = fpb[GEN ** b]
        assert z0 == 0
    for b in unroll(8 * GFULL + 8 - GEXTRA, 8 * GFULL + 8):
        z1 = fpb[GEN ** b]
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
    cprod = groot[GEN ** 2] * cinv[GEN ** 0]
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
    # committed-coordinate values ride the stream (observed, pooled); the Public
    # (bytecode) coordinate values are hinted (bcv) and exported as deferred
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
                    cval = bcv[GEN ** bi]
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

    # ---- Phase A checkpoint: sponge state matches the mirror ----
    assert cv0 == CVCHK_A

    # ---- 6x per-table zerocheck (XOR, MUL, SET, DEREF, JUMP, BLAKE3) ----
    # For each table: eta, the zerocheck point r (tau samples), tau eq-trick
    # rounds (claim starts at 0), then the involved-column evaluations (pooled)
    # and the final AIR check claim == eq_acc * C_t(eta, evals).
    rho = HeapBuf(6 * TAUMAX)
    evb = HeapBuf(EVTOT)
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
            evb[GEN ** (EVOFF[t] + k)] = e
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
    assert cv0 == CVCHK_B

    # ---- public-input binding claim: MEM(r_m, 0..) = interp(pi0, pi1, r_m) ----
    rm, cv0, cv1 = sqz(cv0, cv1)
    piv = PI0 + rm * (PI0 + PI1)
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
    assert cv0 == CVCHK_C

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
        cv0, cv1 = obs(cv0, cv1, zc1[GEN ** i])
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
        ceval = ceval + lpre[GEN ** i] * lsuf[GEN ** (i + 1)] * ILAM[i] * zc1[GEN ** (64 + i)]
    # combined interpolation at z over ALL 128 phi8 nodes (Lambda values only;
    # the S half is zero by the zerocheck identity).
    cpre = HeapBuf(129)
    cpre[GEN ** 0] = GEN ** 0
    for i in unroll(0, 128):
        cpre[GEN ** (i + 1)] = cpre[GEN ** i] * (zz + PHI[i])
    csuf = HeapBuf(129)
    csuf[GEN ** 128] = GEN ** 0
    for i in unroll(0, 128):
        csuf[GEN ** (127 - i)] = csuf[GEN ** (128 - i)] * (zz + PHI[127 - i])
    comb = 0
    for i in unroll(0, 64):
        comb = comb + cpre[GEN ** (64 + i)] * csuf[GEN ** (64 + i + 1)] * ICMB[i] * (zc1[GEN ** i] + zc1[GEN ** (64 + i)])
    crun = comb + ceval
    # multilinear rounds.
    zrho = HeapBuf(NMLV)
    for i in unroll(0, 7):
        g1 = zcr[GEN ** (2 * i)]
        gi = zcr[GEN ** (2 * i + 1)]
        req = zr[GEN ** (6 + i)]
        g0 = (crun + req * g1) * I7INV[i]
        cv0, cv1 = obs(cv0, cv1, g1)
        cv0, cv1 = obs(cv0, cv1, gi)
        rhov, cv0, cv1 = sqz(cv0, cv1)
        zrho[GEN ** i] = rhov
        crun = g0 * (1 + rhov) + g1 * rhov + gi * rhov * (1 + rhov)
    for i in unroll(7, NMLV):
        g1 = zcr[GEN ** (2 * i)]
        gi = zcr[GEN ** (2 * i + 1)]
        req = zr[GEN ** (6 + i)]
        ionepr = zinv[GEN ** i]
        chkinv = (1 + req) * ionepr
        assert chkinv == 1
        g0 = (crun + req * g1) * ionepr
        cv0, cv1 = obs(cv0, cv1, g1)
        cv0, cv1 = obs(cv0, cv1, gi)
        rhov, cv0, cv1 = sqz(cv0, cv1)
        zrho[GEN ** i] = rhov
        crun = g0 * (1 + rhov) + g1 * rhov + gi * rhov * (1 + rhov)
    # final: crun == a_eval * b_eval; observe both.
    fa = zcf[GEN ** 0]
    fb = zcf[GEN ** 1]
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
        e1 = lcr[GEN ** (2 * i)]
        ei = lcr[GEN ** (2 * i + 1)]
        cv0, cv1 = obs(cv0, cv1, e1)
        cv0, cv1 = obs(cv0, cv1, ei)
        rv, cv0, cv1 = sqz(cv0, cv1)
        lrr[GEN ** i] = rv
        e0 = lrun + e1
        c1q = e0 + e1 + ei
        lrun = ei * rv * rv + c1q * rv + e0
    for i in unroll(0, 64):
        cv0, cv1 = obs(cv0, cv1, lcz[GEN ** i])
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
    pinw = pinw * lcz[GEN ** (PINCOL % 64)]
    mp = matp[GEN ** 0]
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
        lw = lw + spre[GEN ** i] * ssuf[GEN ** (i + 1)] * ISDOM[i] * lcz[GEN ** i]

    # ---- Phase D checkpoint ----
    assert cv0 == CVCHK_D

    # ---- stacked mixed opening: ring-switch fronts + claim combination ----
    cv0, cv1 = absorb(cv0, cv1, 23, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, OBLBLA, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, OBLBLB, DS_BYTE)
    # Ring-switch claim 0 (ab): value lw, z_skip = lsk, x_outer[0] = lrr[LCR-1]
    # (x_inner_rest is the REVERSED lincheck round vector). Claim 1 (c): value
    # ceval, z_skip = zz, x_outer[0] = zr[6].
    shv = HeapBuf(256)
    hint_witness(shv[0:256], "shv")
    tcl = HeapBuf(2)
    hint_witness(tcl[0:2], "tclaim")
    rsq = HeapBuf(2)
    hint_witness(rsq[0:2], "rsq")
    rdp = HeapBuf(14)
    for rs in unroll(0, 2):
        cv0, cv1 = absorb(cv0, cv1, 20, DS_LEN)
        cv0, cv1 = absorb(cv0, cv1, RSLBLA, DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, RSLBLB, DS_BYTE)
        for i in unroll(0, 128):
            cv0, cv1 = obs(cv0, cv1, shv[GEN ** (128 * rs + i)])
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
            cchk = cchk + lam * ((1 + xo0) * shv[GEN ** (128 * rs + i)] + xo0 * shv[GEN ** (128 * rs + 64 + i)])
        assert cchk == clm
        # r'' (7 samples), kept for the deferred transpose/eval_rs_eq claims.
        for i in unroll(0, 7):
            rv, cv0, cv1 = sqz(cv0, cv1)
            rdp[GEN ** (7 * rs + i)] = rv
    # gamma-combine the two (deferred) transposed sumcheck claims...
    g0, cv0, cv1 = sqz(cv0, cv1)
    g1, cv0, cv1 = sqz(cv0, cv1)
    target = g0 * tcl[GEN ** 0] + g1 * tcl[GEN ** 1]
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
    assert cv0 == CVCHK_E1

    # ================= the Ligerito opening core (stacked, m = STACK) ========
    lsc = HeapBuf(LSC_LEN)
    hint_witness(lsc[0:LSC_LEN], "lsc")
    lrows = HeapBuf(LROWS_LEN)
    hint_witness(lrows[0:LROWS_LEN], "lrows")
    lpaths = HeapBuf(LPATHS_LEN)
    hint_witness(lpaths[0:LPATHS_LEN], "lpaths")
    lsbits = HeapBuf(LSBITS_LEN)
    hint_witness(lsbits[0:LSBITS_LEN], "lsbits")
    lfpb = HeapBuf(LFPB_LEN)
    hint_witness(lfpb[0:LFPB_LEN], "lfpb")
    lyr = HeapBuf(YR_LEN)
    hint_witness(lyr[0:YR_LEN], "lyr")

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

    lsp = lsc
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
                lpn[0] = FN[lg]
                lpn[1] = DS_POW
                lph = StackBuf(2)
                blake3(lpbase, lpn, lph)
                dec128(lfpb * GEN ** (128 * lg), lph[0])
                for b in unroll(0, 8 * FULL[lg]):
                    lz0 = lfpb[GEN ** (128 * lg + b)]
                    assert lz0 == 0
                for b in unroll(8 * FULL[lg] + 8 - EXTRA8[lg], 8 * FULL[lg] + 8):
                    lz1 = lfpb[GEN ** (128 * lg + b)]
                    assert lz1 == 0
                cv0, cv1 = absorb(cv0, cv1, FN[lg], DS_POW)
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
                cv0, cv1 = obs(cv0, cv1, lyr[GEN ** iy])
        else:
            cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
            cv0, cv1 = absorb(cv0, cv1, ROOTA[lvl + 1], DS_BYTE)
            cv0, cv1 = absorb(cv0, cv1, ROOTB[lvl + 1], DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)

        c0b = HeapBuf(MAXNSQ + 1)
        c1b = HeapBuf(MAXNSQ + 1)
        c0b[GEN ** 0] = cv0
        c1b[GEN ** 0] = cv1
        for xs in mul_range(1, GEN ** NSQ[lvl]):
            chq, nc0, nc1 = sqz(c0b[xs], c1b[xs])
            c0b[xs * GEN] = nc0
            c1b[xs * GEN] = nc1
            lbp = lsbits * GEN ** SBITSOFF[lvl] * xs ** 128
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
            ld0 = GEN ** NBYTES[lvl]
            ld1 = 0
            ldot = 0
            for jb in unroll(0, BLOCKS[lvl]):
                laa = StackBuf(2)
                laa[0] = ld0
                laa[1] = ld1
                lmm = StackBuf(2)
                lmm[0] = lrows[GEN ** ROWOFF[lvl] * lrb * GEN ** (2 * jb)]
                lmm[1] = lrows[GEN ** ROWOFF[lvl] * lrb * GEN ** (2 * jb + 1)]
                loo = StackBuf(2)
                blake3(laa, lmm, loo)
                ld0 = loo[0]
                ld1 = loo[1]
                ldot = ldot + lmm[0] * leqt[GEN ** (2 * jb)] + lmm[1] * leqt[GEN ** (2 * jb + 1)]
            accE[xe * GEN] = accE[xe] + law[GEN ** (lvl * MAXQ) * xe] * ldot
            lsbp = qbp[GEN ** QPOFF[lvl] * xe]
            lpb2 = xe ** (2 * DEPTH[lvl])
            for lw2 in unroll(0, DEPTH[lvl]):
                ls0 = lpaths[GEN ** PATHOFF[lvl] * lpb2 * GEN ** (2 * lw2)]
                ls1 = lpaths[GEN ** PATHOFF[lvl] * lpb2 * GEN ** (2 * lw2 + 1)]
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
                assert ld0 == ROOTA[lvl]
                assert ld1 == ROOTB[lvl]
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
            lsy = foldyr(lyr, sfw, 0)
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
    # ring-switch weight base over ris[QPKDV..LENRIS).
    rsb = g0 * rsq[GEN ** 0] + g1 * rsq[GEN ** 1]
    for k in unroll(0, LENRIS - QPKDV):
        if (RSSEL // (2 ** k)) % 2 == 1:
            rsb = rsb * ris[GEN ** (QPKDV + k)]
        else:
            rsb = rsb * (1 + ris[GEN ** (QPKDV + k)])
    # inner = sum_y lyr[y] * eval_b[y] + the residual sums.
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
        inner = inner + lyr[GEN ** y] * ey
    assert inner == tr

    # ---- Phase F: bind the deferred data to the outer public input ----
    # A fresh hash chain (same tagged compress as the FS observe) over: the
    # inner public input; the two bytecode points + the 12 deferred bytecode
    # values; the deferred matrix claim (alpha, row point, round challenges,
    # z_partial, value); the deferred tensor data (s_hat_v, r'', transposed
    # claims, eval_rs_eq values, and the coords the outer checker needs to
    # rebuild the eval_rs_eq inputs). The outer public input must equal it.
    h0 = 0
    h1 = 0
    h0, h1 = obs(h0, h1, PI0)
    h0, h1 = obs(h0, h1, PI1)
    for s in unroll(0, 2):
        for k in unroll(0, KBC):
            h0, h1 = obs(h0, h1, zeta[GEN ** (s * MUMAX + k)])
    for k in unroll(0, NBCV):
        h0, h1 = obs(h0, h1, bcv[GEN ** k])
    h0, h1 = obs(h0, h1, lal)
    h0, h1 = obs(h0, h1, zz)
    for k in unroll(0, LCR):
        h0, h1 = obs(h0, h1, zrho[GEN ** k])
    for k in unroll(0, LCR):
        h0, h1 = obs(h0, h1, lrr[GEN ** k])
    for k in unroll(0, 64):
        h0, h1 = obs(h0, h1, lcz[GEN ** k])
    h0, h1 = obs(h0, h1, matp[GEN ** 0])
    for k in unroll(0, 256):
        h0, h1 = obs(h0, h1, shv[GEN ** k])
    for k in unroll(0, 14):
        h0, h1 = obs(h0, h1, rdp[GEN ** k])
    h0, h1 = obs(h0, h1, tcl[GEN ** 0])
    h0, h1 = obs(h0, h1, tcl[GEN ** 1])
    h0, h1 = obs(h0, h1, rsq[GEN ** 0])
    h0, h1 = obs(h0, h1, rsq[GEN ** 1])
    for k in unroll(0, QPKDV):
        h0, h1 = obs(h0, h1, ris[GEN ** k])
    for k in unroll(LCR, NMLV):
        h0, h1 = obs(h0, h1, zrho[GEN ** k])
    for k in unroll(13, MR1CS):
        h0, h1 = obs(h0, h1, zr[GEN ** k])
    pp = GEN ** 0
    pia = pp[1]
    pib = pp[GEN]
    assert pia == h0
    assert pib == h1
    return
