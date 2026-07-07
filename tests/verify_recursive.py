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


def main():
    stream = HeapBuf(STREAM_LEN)
    hint_witness(stream[0:STREAM_LEN], "stream")
    fpb = HeapBuf(128)
    hint_witness(fpb[0:128], "fpb")
    bcv = HeapBuf(NBCV)
    hint_witness(bcv[0:NBCV], "bcv")
    cinv = HeapBuf(1)
    hint_witness(cinv[0:1], "cinv")

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
    return
