from snark_lib import *

# In-circuit multi-level Ligerito PCS-opening verifier — a config-driven zkDSL port
# of flock's `recursive_verifier_with_basis_succinct` (leanVM-b's opening scheme).
# ONE source, specialised per proof by placeholder-filled constant arrays; no
# Rust-side code generation. Verifies each query independently (no dedup/sort —
# that is proof-storage compression). The transcript sponge is the `blake3` opcode
# with a domain tag in word 2 (1 scalar, 2 byte-word, 3 len, 4 squeeze, 5 pow).
#
# Config (all filled by the harness):
#   scalars  NLEVELS, R (=NLEVELS-1), YR_LOG_N, LENRIS, MAXNI, MAXQ, SEED0/1,
#            TARGET, LBLA/B, and the pow domain tags.
#   arrays   QUERIES[lvl], KLVL[lvl] (fold count = log2 num-interleaved),
#            NUMINTER[lvl] (=2^KLVL), NBYTES[lvl] (=16·NUMINTER), BLOCKS[lvl]
#            (=NUMINTER/2), DEPTH[lvl] (Merkle depth), ALPHALEN[lvl], LMC[lvl],
#            RISSTART[lvl], PREFIXLEN[lvl] (=LMC-YR_LOG_N), ROOTA/ROOTB[lvl],
#            FOLDBASE[lvl] (fold-index prefix sum), Z[..LOG_N],
#            per-fold  BITS[g], FULL[g], EXTRA8[g], FN[g] (pow nonce),
#            per-level flattened novel-basis  SVK[..], IVK[..], SVKOFF[lvl].
#   hints    sc, rows, paths, sbits, fpb (flat, with ROWOFF/PATHOFF/... arrays), yr.

SEED0 = SEED0_PLACEHOLDER
SEED1 = SEED1_PLACEHOLDER
TARGET = TARGET_PLACEHOLDER
LBLA = LBLA_PLACEHOLDER
LBLB = LBLB_PLACEHOLDER
NLEVELS = NLEVELS_PLACEHOLDER
R = R_PLACEHOLDER
YR_LOG_N = YR_LOG_N_PLACEHOLDER
YR_LEN = YR_LEN_PLACEHOLDER
LENRIS = LENRIS_PLACEHOLDER
MAXNI = MAXNI_PLACEHOLDER
MAXQ = MAXQ_PLACEHOLDER
SC_LEN = SC_LEN_PLACEHOLDER
ROWS_LEN = ROWS_LEN_PLACEHOLDER
PATHS_LEN = PATHS_LEN_PLACEHOLDER
SBITS_LEN = SBITS_LEN_PLACEHOLDER
FPB_LEN = FPB_LEN_PLACEHOLDER

QUERIES = QUERIES_PLACEHOLDER
KLVL = KLVL_PLACEHOLDER
NUMINTER = NUMINTER_PLACEHOLDER
NBYTES = NBYTES_PLACEHOLDER
BLOCKS = BLOCKS_PLACEHOLDER
DEPTH = DEPTH_PLACEHOLDER
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
Z = Z_PLACEHOLDER
SVK = SVK_PLACEHOLDER
IVK = IVK_PLACEHOLDER

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


def foldyr(yp, weights, wbase):
    # Fold a 2^YR_LOG_N multilinear (LSB-first) over YR_LOG_N vars: level j
    # combines out[t] = weights[wbase+2j]·in[2t] + weights[wbase+2j+1]·in[2t+1].
    # `weights` holds the (a_j, b_j) pairs starting at wbase. Returns the scalar.
    cur = yp
    n = YR_LEN
    for j in unroll(0, YR_LOG_N):
        a = weights[GEN ** (wbase + 2 * j)]
        b = weights[GEN ** (wbase + 2 * j + 1)]
        half = n // 2
        nxt = HeapBuf(MAXNI)
        for t in unroll(0, half):
            nxt[GEN ** t] = a * cur[GEN ** (2 * t)] + b * cur[GEN ** (2 * t + 1)]
        cur = nxt
        n = half
    return cur[GEN ** 0]


def eqtab(dst, src, sbase, k):
    # dst[i] = Π_j (bit_j(i) ? src[sbase+j] : 1+src[sbase+j]), i in [0, 2^k), k Const.
    for i in unroll(0, GEN ** 0 * 0 + 1):
        pass
    return


def main():
    sc = HeapBuf(SC_LEN)
    hint_witness(sc[0:SC_LEN], "sc")
    rows = HeapBuf(ROWS_LEN)
    hint_witness(rows[0:ROWS_LEN], "rows")
    paths = HeapBuf(PATHS_LEN)
    hint_witness(paths[0:PATHS_LEN], "paths")
    sbits = HeapBuf(SBITS_LEN)
    hint_witness(sbits[0:SBITS_LEN], "sbits")
    fpb = HeapBuf(FPB_LEN)
    hint_witness(fpb[0:FPB_LEN], "fpb")
    yr = HeapBuf(YR_LEN)
    hint_witness(yr[0:YR_LEN], "yr")

    # Per-level scratch that outlives the level loop (residual + terminal read them).
    ris = HeapBuf(LENRIS)
    beta = HeapBuf(NLEVELS)
    enf = HeapBuf(NLEVELS)
    qv = HeapBuf(NLEVELS * MAXQ)
    aw = HeapBuf(NLEVELS * MAXQ)

    # ---- sponge seed: label, target, initial root ----
    cv0 = SEED0
    cv1 = SEED1
    cv0, cv1 = absorb(cv0, cv1, 23, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, LBLA, DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, LBLB, DS_BYTE)
    cv0, cv1 = obs(cv0, cv1, TARGET)
    cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
    cv0, cv1 = absorb(cv0, cv1, ROOTA[0], DS_BYTE)
    cv0, cv1 = absorb(cv0, cv1, ROOTB[0], DS_BYTE)

    # ---- prologue: msg0 -> quad, t_r = target ----
    sp = sc
    u0 = sp[GEN ** 0]
    cv0, cv1 = obs(cv0, cv1, u0)
    u2 = sp[GEN ** 1]
    cv0, cv1 = obs(cv0, cv1, u2)
    sp = sp * GEN ** 2
    qc = u0
    qb = TARGET + u2
    qa = u2
    tr = TARGET

    # ---- per-level: folds + fold-PoW + observe + query phase + glue ----
    for lvl in unroll(0, NLEVELS):
        for j in unroll(0, KLVL[lvl]):
            g = FOLDBASE[lvl] + j
            # fold-PoW leading-zero check (only when this fold grinds)
            if BITS[g] == 0:
                pass
            else:
                pb = StackBuf(2)
                pb[0] = cv0
                pb[1] = cv1
                pz = StackBuf(2)
                pz[0] = 0
                pz[1] = DS_POW
                pbase = StackBuf(2)
                blake3(pb, pz, pbase)
                pn = StackBuf(2)
                pn[0] = FN[g]
                pn[1] = DS_POW
                ph = StackBuf(2)
                blake3(pbase, pn, ph)
                dec128(fpb * GEN ** (128 * g), ph[0])
                for b in unroll(0, 8 * FULL[g]):
                    z0 = fpb[GEN ** (128 * g + b)]
                    assert z0 == 0
                for b in unroll(8 * FULL[g] + 8 - EXTRA8[g], 8 * FULL[g] + 8):
                    z1 = fpb[GEN ** (128 * g + b)]
                    assert z1 == 0
                cv0, cv1 = absorb(cv0, cv1, FN[g], DS_POW)
            ri, cv0, cv1 = sqz(cv0, cv1)
            ris[GEN ** (RISSTART[lvl] + j)] = ri
            tr = qc + ri * qb + ri * ri * qa
            a = sp[GEN ** 0]
            cv0, cv1 = obs(cv0, cv1, a)
            bb = sp[GEN ** 1]
            cv0, cv1 = obs(cv0, cv1, bb)
            sp = sp * GEN ** 2
            qc = a
            qb = tr + bb
            qa = bb

        # observe the next commitment root, or (last level) the yr vector
        if lvl == R:
            for iy in unroll(0, YR_LEN):
                cv0, cv1 = obs(cv0, cv1, yr[GEN ** iy])
        else:
            cv0, cv1 = absorb(cv0, cv1, 32, DS_LEN)
            cv0, cv1 = absorb(cv0, cv1, ROOTA[lvl + 1], DS_BYTE)
            cv0, cv1 = absorb(cv0, cv1, ROOTB[lvl + 1], DS_BYTE)
        cv0, cv1 = absorb(cv0, cv1, 0, DS_POW)

        # query sampling: advance cv QUERIES[lvl] times, capturing each value.
        qbase = lvl * MAXQ
        c0b = HeapBuf(MAXQ + 1)
        c1b = HeapBuf(MAXQ + 1)
        c0b[GEN ** 0] = cv0
        c1b[GEN ** 0] = cv1
        for xq in mul_range(1, GEN ** QUERIES[lvl]):
            chq, nc0, nc1 = sqz(c0b[xq], c1b[xq])
            qv[GEN ** qbase * xq] = chq
            c0b[xq * GEN] = nc0
            c1b[xq * GEN] = nc1
        cv0 = c0b[GEN ** QUERIES[lvl]]
        cv1 = c1b[GEN ** QUERIES[lvl]]

        # sample alpha, build eq(fold challenges) and alpha_weights.
        alr = HeapBuf(MAXNI)
        for t in unroll(0, ALPHALEN[lvl]):
            al, cv0, cv1 = sqz(cv0, cv1)
            alr[GEN ** t] = al
        eqt = HeapBuf(MAXNI)
        for i in unroll(0, NUMINTER[lvl]):
            p = GEN ** 0
            for c in unroll(0, KLVL[lvl]):
                rc = ris[GEN ** (RISSTART[lvl] + c)]
                if (i // (2 ** c)) % 2 == 1:
                    p = p * rc
                else:
                    p = p * (1 + rc)
            eqt[GEN ** i] = p
        for i in unroll(0, QUERIES[lvl]):
            p = GEN ** 0
            for c in unroll(0, ALPHALEN[lvl]):
                ac = alr[GEN ** c]
                if (i // (2 ** c)) % 2 == 1:
                    p = p * ac
                else:
                    p = p * (1 + ac)
            aw[GEN ** qbase * GEN ** i] = p

        # enforced_sum = Σ_i alpha_w[i]·<row_i, eq>
        accE = HeapBuf(MAXQ + 1)
        accE[GEN ** 0] = 0
        for xe in mul_range(1, GEN ** QUERIES[lvl]):
            rb = xe ** NUMINTER[lvl]
            dot = 0
            for c in unroll(0, NUMINTER[lvl]):
                dot = dot + rows[GEN ** ROWOFF[lvl] * rb * GEN ** c] * eqt[GEN ** c]
            accE[xe * GEN] = accE[xe] + aw[GEN ** qbase * xe] * dot
        enf[GEN ** lvl] = accE[GEN ** QUERIES[lvl]]

        # glue (folds the intro sumcheck msg), or the final beta.
        if lvl == R:
            bl, cv0, cv1 = sqz(cv0, cv1)
            beta[GEN ** lvl] = bl
            tr = tr + bl * enf[GEN ** lvl]
        else:
            iu0 = sp[GEN ** 0]
            cv0, cv1 = obs(cv0, cv1, iu0)
            iu2 = sp[GEN ** 1]
            cv0, cv1 = obs(cv0, cv1, iu2)
            sp = sp * GEN ** 2
            bl, cv0, cv1 = sqz(cv0, cv1)
            beta[GEN ** lvl] = bl
            e = enf[GEN ** lvl]
            qc = qc + bl * iu0
            qb = qb + bl * (e + iu2)
            qa = qa + bl * iu2
            tr = tr + bl * e

    # ---- per-query Merkle openings (one single path per query, per level) ----
    for lvl in unroll(0, NLEVELS):
        for xm in mul_range(1, GEN ** QUERIES[lvl]):
            sbp = sbits * GEN ** SBITSOFF[lvl] * xm ** 128
            dec128(sbp, qv[GEN ** (lvl * MAXQ) * xm])
            rb = xm ** NUMINTER[lvl]
            ld0 = GEN ** NBYTES[lvl]
            ld1 = 0
            for jb in unroll(0, BLOCKS[lvl]):
                aa = StackBuf(2)
                aa[0] = ld0
                aa[1] = ld1
                mm = StackBuf(2)
                mm[0] = rows[GEN ** ROWOFF[lvl] * rb * GEN ** (2 * jb)]
                mm[1] = rows[GEN ** ROWOFF[lvl] * rb * GEN ** (2 * jb + 1)]
                oo = StackBuf(2)
                blake3(aa, mm, oo)
                ld0 = oo[0]
                ld1 = oo[1]
            pb2 = xm ** (2 * DEPTH[lvl])
            for lw in unroll(0, DEPTH[lvl]):
                s0 = paths[GEN ** PATHOFF[lvl] * pb2 * GEN ** (2 * lw)]
                s1 = paths[GEN ** PATHOFF[lvl] * pb2 * GEN ** (2 * lw + 1)]
                ld0, ld1 = mstep(ld0, ld1, s0, s1, sbp[GEN ** lw])
            assert ld0 == ROOTA[lvl]
            assert ld1 == ROOTB[lvl]

    # ---- residual (per level) + terminal inner == t_r ----
    # inner = eqris·Σ_y yr[y]·EVB_y  +  Σ_lvl beta_lvl·Σ_y yr[y]·resid_lvl[y]
    # Each Σ_y is a fold of yr; the residual per query is a novel-basis recurrence.
    innerbuf = HeapBuf(NLEVELS + 1)
    innerbuf[GEN ** 0] = 0
    for lvl in unroll(0, NLEVELS):
        accR = HeapBuf(MAXQ + 1)
        accR[GEN ** 0] = 0
        for xr in mul_range(1, GEN ** QUERIES[lvl]):
            sbp = sbits * GEN ** SBITSOFF[lvl] * xr ** 128
            qf = 0
            for b in unroll(0, DEPTH[lvl]):
                qf = qf + sbp[GEN ** b] * GEN ** b
            # w_t = s_t · inv(svk_t); s_0=qf, s_t = s_{t-1}²+svk_{t-1}·s_{t-1}
            wbuf = HeapBuf(MAXNI)
            s = qf
            wbuf[GEN ** 0] = s * IVK[GEN ** SVKOFF[lvl]]
            for t in unroll(1, LMC[lvl]):
                s = s * s + SVK[GEN ** (SVKOFF[lvl] + t - 1)] * s
                wbuf[GEN ** t] = s * IVK[GEN ** (SVKOFF[lvl] + t)]
            prefix = GEN ** 0
            for t in unroll(0, PREFIXLEN[lvl]):
                rc = ris[GEN ** (RISSTART[lvl] + t)]
                prefix = prefix * (1 + rc * (1 + wbuf[GEN ** t]))
            # suffix fold weights [1, w_{prefix+j}] for j<YR_LOG_N
            sfw = HeapBuf(MAXNI)
            for j in unroll(0, YR_LOG_N):
                sfw[GEN ** (2 * j)] = GEN ** 0
                sfw[GEN ** (2 * j + 1)] = wbuf[GEN ** (PREFIXLEN[lvl] + j)]
            sy = foldyr(yr, sfw, 0)
            contrib = aw[GEN ** (lvl * MAXQ) * xr] * prefix * sy
            accR[xr * GEN] = accR[xr] + contrib
        innerbuf[GEN ** (lvl + 1)] = innerbuf[GEN ** lvl] + beta[GEN ** lvl] * accR[GEN ** QUERIES[lvl]]

    # eqris = Π_{t<LENRIS} (1 + Z[t] + ris[t])
    eqris = GEN ** 0
    for t in unroll(0, LENRIS):
        eqris = eqris * (1 + Z[t] + ris[GEN ** t])
    # sy_evb: fold yr with (1+Z[LENRIS+j], Z[LENRIS+j])
    evbw = HeapBuf(MAXNI)
    for j in unroll(0, YR_LOG_N):
        evbw[GEN ** (2 * j)] = 1 + Z[LENRIS + j]
        evbw[GEN ** (2 * j + 1)] = Z[LENRIS + j]
    sy_evb = foldyr(yr, evbw, 0)

    inner = eqris * sy_evb + innerbuf[GEN ** NLEVELS]
    assert inner == tr
    return
