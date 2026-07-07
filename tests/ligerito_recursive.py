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
#            (=NUMINTER/2), DEPTH[lvl] (Merkle depth), PER[lvl] (=128//DEPTH,
#            positions per squeeze), NSQ[lvl] (squeezes = ceil(QUERIES/PER)),
#            QPOFF[lvl] (position-table offsets), ALPHALEN[lvl], LMC[lvl],
#            RISSTART[lvl], PREFIXLEN[lvl] (=LMC-YR_LOG_N), ROOTA/ROOTB[lvl],
#            FOLDBASE[lvl] (fold-index prefix sum), Z[..LOG_N],
#            per-fold  BITS[g], FULL[g], EXTRA8[g], FN[g] (pow nonce),
#            per-level flattened novel-basis  SVK[..], IVK[..], SVKOFF[lvl].
#   hints    sc, rows, paths, sbits, fpb (flat, with ROWOFF/PATHOFF/... arrays), yr.
#
# Query sampling packs ⌊128/DEPTH⌋ positions per squeeze (its disjoint DEPTH-bit
# chunks, low bits first — mirrored by flock's sample_queries_ordered), so ONE
# 128-bit decomposition covers ~6 queries instead of one: the sampling loop
# decomposes each squeeze and stores every position's q_field and bit-pointer;
# the Merkle/residual loops just read them back.

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
MAXNSQ = MAXNSQ_PLACEHOLDER
MAXLMC = MAXLMC_PLACEHOLDER
QP_LEN = QP_LEN_PLACEHOLDER
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


def decq(bp, v, qfp, qbpp, d: Const, per: Const):
    # dec128 fused with query extraction: boolean-constrain the 128 hinted bits
    # at `bp`, assert they reconstruct the squeeze `v`, and store each d-bit
    # chunk's position value (chunk j at qfp[g^j]) and bit-pointer (qbpp[g^j]).
    # The full reconstruction is just the chunk sums re-weighted:
    # v = Σ_j qf_j·g^{j·d} + Σ_{i≥per·d} b_i·g^i.
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
    # Weighted fold of the 2^YR_LOG_N multilinear `yp` (heap, LSB-first): level j
    # combines out[t] = weights[wbase+2j]·in[2t] + weights[wbase+2j+1]·in[2t+1];
    # returns the scalar. Inlined at the call site with stack-cell intermediates
    # (`weights` is a StackBuf), so only the first level touches the heap.
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
    aw = HeapBuf(NLEVELS * MAXQ)
    # Per-query position tables, filled by the sampling loop: q_field (the
    # position as a field element) and a pointer to its DEPTH sample bits.
    qfb = HeapBuf(QP_LEN)
    qbp = HeapBuf(QP_LEN)

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
            if BITS[g] != 0:
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
            ris[GEN ** (FOLDBASE[lvl] + j)] = ri
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

        # query sampling: NSQ squeezes, each yielding PER positions (its disjoint
        # DEPTH-bit chunks, low bits first). Decompose each squeeze once and
        # store every position's q_field + bit-pointer for the later loops.
        c0b = HeapBuf(MAXNSQ + 1)
        c1b = HeapBuf(MAXNSQ + 1)
        c0b[GEN ** 0] = cv0
        c1b[GEN ** 0] = cv1
        for xs in mul_range(1, GEN ** NSQ[lvl]):
            chq, nc0, nc1 = sqz(c0b[xs], c1b[xs])
            c0b[xs * GEN] = nc0
            c1b[xs * GEN] = nc1
            bp = sbits * GEN ** SBITSOFF[lvl] * xs ** 128
            qpp = xs ** PER[lvl]
            decq(bp, chq, qfb * GEN ** QPOFF[lvl] * qpp, qbp * GEN ** QPOFF[lvl] * qpp, DEPTH[lvl], PER[lvl])
        cv0 = c0b[GEN ** NSQ[lvl]]
        cv1 = c1b[GEN ** NSQ[lvl]]

        # sample alpha, build eq(fold challenges) and alpha_weights.
        alr = HeapBuf(MAXNI)
        for t in unroll(0, ALPHALEN[lvl]):
            al, cv0, cv1 = sqz(cv0, cv1)
            alr[GEN ** t] = al
        eqt = HeapBuf(MAXNI)
        for i in unroll(0, NUMINTER[lvl]):
            p = GEN ** 0
            for c in unroll(0, KLVL[lvl]):
                rc = ris[GEN ** (FOLDBASE[lvl] + c)]
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
            aw[GEN ** (lvl * MAXQ + i)] = p

        # Per-query pass: one read of each opened row value feeds BOTH the
        # enforced_sum dot (Σ_i alpha_w[i]·<row_i, eq>) and the Merkle leaf hash;
        # then walk the query's single path to the level root.
        accE = HeapBuf(MAXQ + 1)
        accE[GEN ** 0] = 0
        for xe in mul_range(1, GEN ** QUERIES[lvl]):
            rb = xe ** NUMINTER[lvl]
            ld0 = GEN ** NBYTES[lvl]
            ld1 = 0
            dot = 0
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
                dot = dot + mm[0] * eqt[GEN ** (2 * jb)] + mm[1] * eqt[GEN ** (2 * jb + 1)]
            accE[xe * GEN] = accE[xe] + aw[GEN ** (lvl * MAXQ) * xe] * dot
            # walk: hash (left, right) = bit ? (sibling, node) : (node, sibling),
            # selected branch-free — left = node + bit·(node+sibling) (bit boolean).
            sbp = qbp[GEN ** QPOFF[lvl] * xe]
            pb2 = xe ** (2 * DEPTH[lvl])
            for lw in unroll(0, DEPTH[lvl]):
                s0 = paths[GEN ** PATHOFF[lvl] * pb2 * GEN ** (2 * lw)]
                s1 = paths[GEN ** PATHOFF[lvl] * pb2 * GEN ** (2 * lw + 1)]
                b = sbp[GEN ** lw]
                t0 = ld0 + s0
                t1 = ld1 + s1
                la = StackBuf(2)
                la[0] = ld0 + b * t0
                la[1] = ld1 + b * t1
                ra = StackBuf(2)
                ra[0] = t0 + la[0]
                ra[1] = t1 + la[1]
                oo2 = StackBuf(2)
                blake3(la, ra, oo2)
                ld0 = oo2[0]
                ld1 = oo2[1]
            assert ld0 == ROOTA[lvl]
            assert ld1 == ROOTB[lvl]
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


    # ---- residual (per level) + terminal inner == t_r ----
    # inner = eqris·Σ_y yr[y]·EVB_y  +  Σ_lvl beta_lvl·Σ_y yr[y]·resid_lvl[y]
    # Each Σ_y is a fold of yr; the residual per query is a novel-basis recurrence.
    innerbuf = HeapBuf(NLEVELS + 1)
    innerbuf[GEN ** 0] = 0
    for lvl in unroll(0, NLEVELS):
        accR = HeapBuf(MAXQ + 1)
        accR[GEN ** 0] = 0
        for xr in mul_range(1, GEN ** QUERIES[lvl]):
            # w_t = s_t · inv(svk_t); s_0 = q_field, s_t = s_{t-1}²+svk_{t-1}·s_{t-1}
            wbuf = StackBuf(MAXLMC)
            s = qfb[GEN ** QPOFF[lvl] * xr]
            wbuf[0] = s * IVK[SVKOFF[lvl]]
            for t in unroll(1, LMC[lvl]):
                s = s * s + SVK[SVKOFF[lvl] + t - 1] * s
                wbuf[t] = s * IVK[SVKOFF[lvl] + t]
            prefix = GEN ** 0
            for t in unroll(0, PREFIXLEN[lvl]):
                rc = ris[GEN ** (RISSTART[lvl] + t)]
                prefix = prefix * (1 + rc * (1 + wbuf[t]))
            # suffix fold weights [1, w_{prefix+j}] for j<YR_LOG_N
            sfw = StackBuf(2 * YR_LOG_N)
            for j in unroll(0, YR_LOG_N):
                sfw[2 * j] = GEN ** 0
                sfw[2 * j + 1] = wbuf[PREFIXLEN[lvl] + j]
            sy = foldyr(yr, sfw, 0)
            contrib = aw[GEN ** (lvl * MAXQ) * xr] * prefix * sy
            accR[xr * GEN] = accR[xr] + contrib
        innerbuf[GEN ** (lvl + 1)] = innerbuf[GEN ** lvl] + beta[GEN ** lvl] * accR[GEN ** QUERIES[lvl]]

    # eqris = Π_{t<LENRIS} (1 + Z[t] + ris[t])
    eqris = GEN ** 0
    for t in unroll(0, LENRIS):
        eqris = eqris * (1 + Z[t] + ris[GEN ** t])
    # sy_evb: fold yr with (1+Z[LENRIS+j], Z[LENRIS+j])
    evbw = StackBuf(2 * YR_LOG_N)
    for j in unroll(0, YR_LOG_N):
        evbw[2 * j] = 1 + Z[LENRIS + j]
        evbw[2 * j + 1] = Z[LENRIS + j]
    sy_evb = foldyr(yr, evbw, 0)

    inner = eqris * sy_evb + innerbuf[GEN ** NLEVELS]
    assert inner == tr
    return
