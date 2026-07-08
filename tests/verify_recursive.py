from snark_lib import *

# The recursion guest: in-circuit replay of leanVM-b's `cpu::verify` for NSUB
# sub-proofs of one fixed inner program, followed by the aggregation of their
# deferred claims (doc.tex §Recursive aggregation, §Deferred evaluation claims,
# §Ring-switch claims via linearized polynomials).
#
# Per sub-proof: seed (hinted statement + baked program digest) → announced
# sizes → commitment root → bus (grinding, 3× GKR grand product, balance,
# 3× leaf decomposition with the claim pool, stacked-bytecode reduction) →
# 6 AIR zerochecks → public-input claim + BLAKE3 pins → flock reduction
# (univariate-skip zerocheck, lincheck with the matrix evaluation DEFERRED) →
# ring-switch fronts (tensor algebra in-circuit via linearized polynomials) →
# the stacked Ligerito opening (config-driven levels, fused query passes,
# generalized eval_b terminal). Then the aggregation phase batches the deferred
# bytecode and matrix claims with two sumchecks and binds the reduced claims to
# the public input.
#
# Config-driven by placeholder constants the harness computes from the REAL
# `cpu::layout` and the transcript trace of a native verify run; all per-proof
# data (streams, sub statements, level roots, fold nonces, sponge checkpoints)
# arrives as hints (`tests/recursion_e2e.rs::gen_verify`).
#
# SOUNDNESS: every hint is untrusted prover input; each is bound one of four
# ways, and nothing else enters the computation:
#   - sponge-bound (observed/absorbed before any challenge that depends on it):
#     the stream scalars, zc_round1/zc_msgs/zc_finals, lincheck_msgs/z_partial, s_hat_v, lsc, yr, the level roots
#     rta/rtb, the fold nonces fnn, the aggregation round messages bscr/mscr,
#     and the deferred bytecode values bcv (absorbed by the in-protocol
#     stacked-bytecode reduction before its selector challenges);
#   - assert-checked: count_root_inv and zc_invs (hinted inverses, product asserted 1),
#     grind_bits/fold_grind_bits (grinding digest bits: booleanity + reconstruction against the
#     in-circuit digest + leading-zero asserts), lsbits (query bits: booleanity
#     + reconstruction equal to the squeezed word), lrows/lpaths (Merkle
#     inclusion against the bound roots);
#   - statement-bound (fed to the outer public-input hash): spi (the sub
#     statements, which also derive the transcript seeds), matpart (with its
#     complete weight data), and the reduced claims bst/mst with their points;
#   - debug-only, no soundness role: cvh (sponge checkpoints, self-asserts
#     that localize a divergence during development).
# The stream hint itself is transport, never trusted: binding always comes from
# the sponge absorb of each value read off it. The outer verifier's total
# obligation is: verify the outer proof, recompute the statement hash from the
# claimed sub statements + reduced claims, and evaluate the three fixed
# polynomials (stacked bytecode, A0, B0) at the reduced points.
#
# Conventions: `fs` is the Fiat-Shamir sponge chain (a StackBuf pair aliased
# forward per compression; `agg_fs` and `out_fs` are the aggregation and
# public-input chains); `cursor` walks the proof stream (heap pointer, advanced
# by g per word read); `_s`-suffixed names are this sub-proof's slice of an
# NSUB-wide hint buffer; chains across runtime loop iterations live in
# g-indexed heap buffers (`*_chain`).

STREAM_LEN = STREAM_LEN_PLACEHOLDER
ANN = ANN_PLACEHOLDER
# Baked exponents of the certified structural logs (scaffolding, see P1).
ANNLOG = ANNLOG_PLACEHOLDER
# Per-table tau floor: BLAKE3 is sized to flock's instance count (>= 2^3).
FLOORS = [0, 0, 0, 0, 0, 3]
GINV = GINV_PLACEHOLDER
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
# GKR runtime-loop chain capacities: per-tree round positions (triangle
# rounds plus one slot per layer) and the point triangle (rows x MUMAX).
TRICAP = TRICAP_PLACEHOLDER
PTSCAP = PTSCAP_PLACEHOLDER

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
# Query-phase grinding: QBITS[lvl] leading zero bits checked on the digest
# before the query indexes are sampled (queries then only cover
# target - QBITS bits of soundness).
QBITS = QBITS_PLACEHOLDER
QGFULL = QGFULL_PLACEHOLDER
QGEXTRA = QGEXTRA_PLACEHOLDER
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
# One sub-proof's deferred-claim region: 2*KBC + 2*LCR + 72 words.
DEFSZ = DEFSZ_PLACEHOLDER
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


@inline
def foldyr(yp, weights, wbase: Const):
    # Weighted fold of the yr multilinear (see tests/ligerito_recursive.py).
    l0 = StackBuf(YR_LEN)
    for t in unroll(0, YR_LEN // 2):
        l0[t] = weights[wbase] * yp[GEN ** (2 * t)] + weights[wbase + 1] * yp[GEN ** (2 * t + 1)]
    cursor = l0
    n = YR_LEN // 2
    for j in unroll(1, YR_LOG_N):
        nxt = StackBuf(YR_LEN)
        for t in unroll(0, n // 2):
            nxt[t] = weights[wbase + 2 * j] * cursor[2 * t] + weights[wbase + 2 * j + 1] * cursor[2 * t + 1]
        cursor = nxt
        n = n // 2
    return cursor[0]


@inline
def obs(cb, x):
    # Bind one scalar into the sponge chain: cb <- compress(cb, (x, SCALAR)).
    # Returns the successor StackBuf; the call site aliases it (zero copies).
    tg = StackBuf(2)
    tg[0] = x
    tg[1] = DS_SCALAR
    nb = StackBuf(2)
    blake3(cb, tg, nb)
    return nb


@inline
def absorb(cb, x, tag):
    # Tagged absorb (length frames, byte words, grinding nonces).
    tg = StackBuf(2)
    tg[0] = x
    tg[1] = tag
    nb = StackBuf(2)
    blake3(cb, tg, nb)
    return nb


@inline
def squeeze(cb, zt):
    # Ratchet: the compress output is the new state; word 0 is the challenge.
    nb = StackBuf(2)
    blake3(cb, zt, nb)
    return nb


@inline
def lag64(z, w, nbase: Const):
    # The 64 phi8-domain Lagrange NUMERATORS at z, nodes PHI[nbase..nbase+64]:
    # w[i] = prod_{j != i} (z + PHI[nbase + j]). Callers multiply by their
    # baked inverse-denominator table (ISDOM / ILAM / ICMB).
    pre = StackBuf(65)
    pre[0] = 1
    for i in unroll(0, 64):
        pre[i + 1] = pre[i] * (z + PHI[nbase + i])
    suf = StackBuf(65)
    suf[64] = 1
    for i in unroll(0, 64):
        suf[63 - i] = suf[64 - i] * (z + PHI[nbase + 63 - i])
    for i in unroll(0, 64):
        w[i] = pre[i] * suf[i + 1]
    return


@inline
def eqtree(rp, out, nc: Const):
    # The eq tensor of the nc challenges at rp[0..nc], built by doubling into
    # out (size 2^(nc+1) - 2); the final 2^nc values start at offset 2^nc - 2.
    r0 = rp[GEN ** 0]
    out[GEN ** 0] = 1 + r0
    out[GEN ** 1] = r0
    for t in unroll(1, nc):
        rt = rp[GEN ** t]
        commit_root_1 = 1 + rt
        for i in unroll(0, 2 ** t):
            pw = out[GEN ** (2 ** t - 2 + i)]
            out[GEN ** (2 ** (t + 1) - 2 + i)] = pw * commit_root_1
            out[GEN ** (2 ** (t + 1) - 2 + 2 ** t + i)] = pw * rt
    return


def verify_sub(pi_0, pi_1, delta_pows, dout):
    # In-circuit verification of ONE inner proof for the statement
    # (pi_0, pi_1). All proof data is hinted HERE: each call pops the next
    # sub-proof's entry of every witness stream, so the body lowers once and
    # main just calls it per statement. `delta_pows` is the shared dual-basis
    # Frobenius table; the deferred-claim data is written to `dout`.
    sqz_tag = StackBuf(2)
    sqz_tag[0] = 0
    sqz_tag[1] = DS_SQ
    rta = HeapBuf(NLEVELS)
    hint_witness(rta[0:NLEVELS], "rta")
    rtb = HeapBuf(NLEVELS)
    hint_witness(rtb[0:NLEVELS], "rtb")
    fnn = HeapBuf(LENRIS)
    hint_witness(fnn[0:LENRIS], "fnn")
    qnonce = HeapBuf(NLEVELS)
    hint_witness(qnonce[0:NLEVELS], "qnonce")
    qgrind = HeapBuf(NLEVELS * 128)
    hint_witness(qgrind[0:NLEVELS * 128], "qgrind")
    cvh = HeapBuf(4)
    hint_witness(cvh[0:4], "cvh")
    stream = HeapBuf(STREAM_LEN)
    hint_witness(stream[0:STREAM_LEN], "stream")
    grind_bits = HeapBuf(128)
    hint_witness(grind_bits[0:128], "grind_bits")
    bcv = HeapBuf(NBCV)
    hint_witness(bcv[0:NBCV], "bcv")
    count_root_inv = HeapBuf(1)
    hint_witness(count_root_inv[0:1], "count_root_inv")
    zc_round1 = HeapBuf(128)
    hint_witness(zc_round1[0:128], "zc_round1")
    zc_msgs = HeapBuf(2 * NMLV)
    hint_witness(zc_msgs[0:2 * NMLV], "zc_msgs")
    zc_finals = HeapBuf(2)
    hint_witness(zc_finals[0:2], "zc_finals")
    zc_invs = HeapBuf(NMLV)
    hint_witness(zc_invs[0:NMLV], "zc_invs")
    lincheck_msgs = HeapBuf(2 * LCR)
    hint_witness(lincheck_msgs[0:2 * LCR], "lincheck_msgs")
    z_partial = HeapBuf(64)
    hint_witness(z_partial[0:64], "z_partial")
    matrix_eval = HeapBuf(1)
    hint_witness(matrix_eval[0:1], "matpart")
    s_hat_v = HeapBuf(256)
    hint_witness(s_hat_v[0:256], "s_hat_v")
    lsc = HeapBuf(LSC_LEN)
    hint_witness(lsc[0:LSC_LEN], "lsc")
    lrows = HeapBuf(LROWS_LEN)
    hint_witness(lrows[0:LROWS_LEN], "lrows")
    lpaths = HeapBuf(LPATHS_LEN)
    hint_witness(lpaths[0:LPATHS_LEN], "lpaths")
    lsbits = HeapBuf(LSBITS_LEN)
    hint_witness(lsbits[0:LSBITS_LEN], "lsbits")
    fold_grind_bits = HeapBuf(LFPB_LEN)
    hint_witness(fold_grind_bits[0:LFPB_LEN], "fold_grind_bits")
    yr = HeapBuf(YR_LEN)
    hint_witness(yr[0:YR_LEN], "yr")
    # Claim pool: values of every committed-coordinate claim, in decompose order
    # (their points are the GKR ζ's, resolvable from the baked block structure).
    claim_pool = HeapBuf(NCLAIMS)
    # The three GKR leaf points, stored side by side (ZOFF offsets).
    zeta = HeapBuf(3 * MUMAX)

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    fs = StackBuf(2)
    fs[0] = SEEDB0
    fs[1] = SEEDB1
    fs = obs(fs, pi_0)
    fs = obs(fs, pi_1)
    fs = obs(fs, DIG0)
    fs = obs(fs, DIG1)
    cursor = stream

    # ---- announced sizes: log_mem + 6 row counts (assert = baked config) ----
    sizes = HeapBuf(7)
    for i in unroll(0, 7):
        x = cursor[GEN ** 0]
        fs = obs(fs, x)
        assert x == ANN[i]
        sizes[GEN ** i] = x
        cursor = cursor * GEN

    # ---- certify the hinted structural logs against the announced words ----
    # ann_exp[0] = g^log_mem, ann_exp[1 + t] = g^tau_t: witness hints (off
    # transcript), pinned to the announced words in-circuit (plan doc, P1).
    # The downstream shape-generic phases consume ann_exp; the ANNLOG
    # equality at the end is scaffolding until they do.
    ann_exp = HeapBuf(7)
    hint_witness(ann_exp[0:7], "annexp")
    ann_bits = HeapBuf(198)
    hint_witness(ann_bits[0:198], "annbits")
    ann_inv = HeapBuf(6)
    hint_witness(ann_inv[0:6], "anninv")
    # Baked tables over exponents 0..32: T[g^j] = j and W[g^j] = 2^j (words).
    exp_word = HeapBuf(33)
    pow_word = HeapBuf(33)
    for j in unroll(0, 33):
        exp_word[GEN ** j] = j
        pow_word[GEN ** j] = 2 ** j
    # log_mem is announced AS a log (an integer word L): T[g^L] == L pins the
    # hinted g-power to it.
    g_log_mem = ann_exp[GEN ** 0]
    assert log(g_log_mem) < 33
    lm_word = exp_word[g_log_mem]
    lm_ann = sizes[GEN ** 0]
    assert lm_word == lm_ann
    assert g_log_mem == GEN ** ANNLOG[0]
    # Per count: 32 hinted bits -> partial sums p[j] = value of the low j
    # bits; p[32] == count binds the bits to the announced word; then
    # p[g^tau] pins count < 2^tau (or count == 2^tau via W), and a
    # hinted-inverse nonzero check pins minimality, waived at the table's
    # floor (BLAKE3 sizes to flock's instance count, ceil_log2(max(n, 8))).
    psums = HeapBuf(6 * 35)
    for t in unroll(0, 6):
        count = sizes[GEN ** (t + 1)]
        pt = psums * GEN ** (35 * t)
        pt[GEN ** 0] = 0
        acc = 0
        for j in unroll(0, 33):
            b = ann_bits[GEN ** (33 * t + j)]
            assert b * b == b
            acc = acc + b * (2 ** j)
            pt[GEN ** (j + 1)] = acc
        assert acc == count
        gtau = ann_exp[GEN ** (t + 1)]
        assert log(gtau) < 33
        low = pt[gtau]
        diff_low = low + count
        diff_pow = count + pow_word[gtau]
        assert diff_low * low == 0
        assert diff_low * diff_pow == 0
        if gtau != GEN ** FLOORS[t]:
            low_prev = pt[gtau * GINV]
            min_a = low_prev + count
            min_b = count + pow_word[gtau * GINV]
            min_prod = min_a * min_b
            prod_inv = ann_inv[GEN ** t]
            assert min_prod * prod_inv == 1
        assert gtau == GEN ** ANNLOG[t + 1]

    # ---- commitment root (2 words), kept for the opening phase ----
    commit_root_0 = cursor[GEN ** 0]
    fs = obs(fs, commit_root_0)
    cursor = cursor * GEN
    commit_root_1 = cursor[GEN ** 0]
    fs = obs(fs, commit_root_1)
    cursor = cursor * GEN

    # ---- bus: α, grinding, γ ----
    fs = squeeze(fs, sqz_tag)
    alpha = fs[0]
    # grinding nonce: raw stream word (NOT observed), PoW-checked, then bound.
    nonce = cursor[GEN ** 0]
    cursor = cursor * GEN
    pz = StackBuf(2)
    pz[0] = 0
    pz[1] = DS_POW
    pbase = StackBuf(2)
    blake3(fs, pz, pbase)
    pn = StackBuf(2)
    pn[0] = nonce
    pn[1] = DS_POW
    ph = StackBuf(2)
    blake3(pbase, pn, ph)
    dec128(grind_bits, ph[0])
    for b in unroll(0, 8 * GFULL):
        z0 = grind_bits[GEN ** b]
        assert z0 == 0
    for b in unroll(8 * GFULL + 8 - GEXTRA, 8 * GFULL + 8):
        z1 = grind_bits[GEN ** b]
        assert z1 == 0
    fs = absorb(fs, nonce, DS_POW)
    fs = squeeze(fs, sqz_tag)
    gamma = fs[0]

    # ---- 3× GKR grand product (push / pull / count), RUNTIME depth ----
    # The layer count mu_s is a hinted g-power (pinned to the baked SMU while
    # downstream phases still bake shapes; certified from the announced sizes
    # in P4). Both loop levels are runtime mul_range; the sponge, stream
    # cursor, claim, and eq accumulator thread through write-once heap
    # chains: layer state indexed by the layer cursor, round state by a
    # per-tree position pointer that advances once per round.
    gkr_roots = HeapBuf(3)
    gkr_claims = HeapBuf(3)
    ann_mus = HeapBuf(3)
    hint_witness(ann_mus[0:3], "annmus")
    lc_fs0 = HeapBuf(3 * (MUMAX + 2))
    lc_fs1 = HeapBuf(3 * (MUMAX + 2))
    lc_cur = HeapBuf(3 * (MUMAX + 2))
    lc_claim = HeapBuf(3 * (MUMAX + 2))
    lc_row = HeapBuf(3 * (MUMAX + 2))
    lc_rnd = HeapBuf(3 * (MUMAX + 2))
    rc_fs0 = HeapBuf(3 * TRICAP)
    rc_fs1 = HeapBuf(3 * TRICAP)
    rc_cur = HeapBuf(3 * TRICAP)
    rc_claim = HeapBuf(3 * TRICAP)
    rc_eq = HeapBuf(3 * TRICAP)
    gkr_pts = HeapBuf(3 * PTSCAP)
    for s in unroll(0, 3):
        mu_g = ann_mus[GEN ** s]
        assert log(mu_g) < 33
        assert mu_g == GEN ** SMU[s]
        rootv = cursor[GEN ** 0]
        fs = obs(fs, rootv)
        cursor = cursor * GEN
        lfs0 = lc_fs0 * GEN ** (s * (MUMAX + 2))
        lfs1 = lc_fs1 * GEN ** (s * (MUMAX + 2))
        lcur = lc_cur * GEN ** (s * (MUMAX + 2))
        lclaim = lc_claim * GEN ** (s * (MUMAX + 2))
        lrow = lc_row * GEN ** (s * (MUMAX + 2))
        lrnd = lc_rnd * GEN ** (s * (MUMAX + 2))
        lfs0[GEN ** 0] = fs[0]
        lfs1[GEN ** 0] = fs[1]
        lcur[GEN ** 0] = cursor
        lclaim[GEN ** 0] = rootv
        lrow[GEN ** 0] = gkr_pts * GEN ** (s * PTSCAP)
        lrnd[GEN ** 0] = GEN ** (s * TRICAP)
        for xl in mul_range(1, mu_g):
            hfs = StackBuf(2)
            hfs[0] = lfs0[xl]
            hfs[1] = lfs1[xl]
            curp = lcur[xl]
            claim_l = lclaim[xl]
            rowp = lrow[xl]
            rndp = lrnd[xl]
            nextrow = rowp * GEN ** MUMAX
            rc_fs0[rndp] = hfs[0]
            rc_fs1[rndp] = hfs[1]
            rc_cur[rndp] = curp
            rc_claim[rndp] = claim_l
            rc_eq[rndp] = 1
            for xj in mul_range(1, xl):
                ip = rndp * xj
                jfs = StackBuf(2)
                jfs[0] = rc_fs0[ip]
                jfs[1] = rc_fs1[ip]
                jcur = rc_cur[ip]
                jclaim = rc_claim[ip]
                jeq = rc_eq[ip]
                m0 = jcur[GEN ** 0]
                jfs = obs(jfs, m0)
                m1 = jcur[GEN ** 1]
                jfs = obs(jfs, m1)
                m2 = jcur[GEN ** 2]
                jfs = obs(jfs, m2)
                jcur = jcur * GEN ** 3
                rj = rowp[xj]
                lhs = jeq * ((1 + rj) * m0 + rj * m1)
                assert lhs == jclaim
                jtag = StackBuf(2)
                jtag[0] = 0
                jtag[1] = DS_SQ
                jfs = squeeze(jfs, jtag)
                rk = jfs[0]
                nextrow[xj * GEN] = rk
                jeq = jeq * (1 + rj + rk)
                # Lagrange at nodes {0, 1, g} with baked inverse denominators.
                l0 = (rk + 1) * (rk + GG) * ILD0
                l1 = rk * (rk + GG) * ILD1
                l2 = rk * (rk + 1) * ILD2
                jclaim = jeq * (m0 * l0 + m1 * l1 + m2 * l2)
                ipn = ip * GEN
                rc_fs0[ipn] = jfs[0]
                rc_fs1[ipn] = jfs[1]
                rc_cur[ipn] = jcur
                rc_claim[ipn] = jclaim
                rc_eq[ipn] = jeq
            fpos = rndp * xl
            tfs = StackBuf(2)
            tfs[0] = rc_fs0[fpos]
            tfs[1] = rc_fs1[fpos]
            tcur = rc_cur[fpos]
            tclaim = rc_claim[fpos]
            teq = rc_eq[fpos]
            e0 = tcur[GEN ** 0]
            tfs = obs(tfs, e0)
            e1 = tcur[GEN ** 1]
            tfs = obs(tfs, e1)
            tcur = tcur * GEN ** 2
            assert tclaim == teq * e0 * e1
            ttag = StackBuf(2)
            ttag[0] = 0
            ttag[1] = DS_SQ
            tfs = squeeze(tfs, ttag)
            c = tfs[0]
            claim_n = e0 + c * (e0 + e1)
            nextrow[GEN ** 0] = c
            xln = xl * GEN
            lfs0[xln] = tfs[0]
            lfs1[xln] = tfs[1]
            lcur[xln] = tcur
            lclaim[xln] = claim_n
            lrow[xln] = nextrow
            lrnd[xln] = rndp * xl * GEN
        fs = StackBuf(2)
        fs[0] = lfs0[mu_g]
        fs[1] = lfs1[mu_g]
        cursor = lcur[mu_g]
        frow = lrow[mu_g]
        zeta_s = zeta * GEN ** ZOFF[s]
        for xt in mul_range(1, mu_g):
            zeta_s[xt] = frow[xt]
        gkr_roots[GEN ** s] = rootv
        gkr_claims[GEN ** s] = lclaim[mu_g]

    # ---- count root nonzero (hinted inverse) ----
    count_product = gkr_roots[GEN ** 2] * count_root_inv[GEN ** 0]
    assert count_product == 1

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
    lhsb = gkr_roots[GEN ** 0] * dsur[GEN ** 1]
    rhsb = gkr_roots[GEN ** 1] * dsur[GEN ** 0]
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
            inner_sum = 0
            apw = GEN ** 0
            for i in unroll(0, BCN[b]):
                if CT[BC0[b] + i] == 0:
                    cval = CVAL[BC0[b] + i]
                if CT[BC0[b] + i] == 1:
                    cval = cursor[GEN ** 0]
                    fs = obs(fs, cval)
                    cursor = cursor * GEN
                    claim_pool[GEN ** ci] = cval
                    ci = ci + 1
                if CT[BC0[b] + i] == 2:
                    rawv = cursor[GEN ** 0]
                    fs = obs(fs, rawv)
                    cursor = cursor * GEN
                    claim_pool[GEN ** ci] = rawv
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
                    inner_sum = inner_sum + cval
                else:
                    inner_sum = inner_sum + apw * cval
                    apw = apw * alpha
            if s == 2:
                acc = acc + eqh * inner_sum
            else:
                acc = acc + eqh * (gamma + inner_sum)
        acc = acc + 1 + selsum
        assert acc == gkr_claims[GEN ** s]

    # ---- stacked-bytecode reduction (part of the native protocol) ----
    # The bytecode is ONE multilinear polynomial in KBC + 3 variables (the six
    # encoding columns stacked along three selector bits). Absorb the twelve
    # per-column values, sample three eq challenges, and reduce each point's
    # six claims to B(zeta_lo, sb) = sum_c eq(sb, c) * v_c.
    for k in unroll(0, NBCV):
        fs = obs(fs, bcv[GEN ** k])
    sb = HeapBuf(3)
    for t in unroll(0, 3):
        fs = squeeze(fs, sqz_tag)
        sv = fs[0]
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
            wv = wv + e * bcv[GEN ** (6 * s + c)]
        wbc[GEN ** s] = wv

    # ---- Phase A checkpoint: sponge state matches the mirror ----
    want_state = cvh[GEN ** 0]
    sponge_state = fs[0]
    assert sponge_state == want_state

    # ---- 6x per-table zerocheck (XOR, MUL, SET, DEREF, JUMP, BLAKE3) ----
    # For each table: eta, the zerocheck point r (tau samples), tau eq-trick
    # rounds (claim starts at 0), then the involved-column evaluations (pooled)
    # and the final AIR check claim == eq_acc * C_t(eta, evals).
    # RUNTIME round counts: tau_t is the certified announced log height
    # (ann_exp[1 + t]) — the first consumer of the count gadget, no
    # scaffolding needed. Round state threads through heap chains exactly
    # like the GKR trees.
    rho = HeapBuf(6 * TAUMAX)
    zp_fs0 = HeapBuf(6 * (TAUMAX + 2))
    zp_fs1 = HeapBuf(6 * (TAUMAX + 2))
    zr_fs0 = HeapBuf(6 * (TAUMAX + 2))
    zr_fs1 = HeapBuf(6 * (TAUMAX + 2))
    zr_cur = HeapBuf(6 * (TAUMAX + 2))
    zr_claim = HeapBuf(6 * (TAUMAX + 2))
    zr_eq = HeapBuf(6 * (TAUMAX + 2))
    for t in unroll(0, 6):
        tau_g = ann_exp[GEN ** (t + 1)]
        fs = squeeze(fs, sqz_tag)
        eta = fs[0]
        # the zerocheck point r: tau squeezes, sponge chained by round.
        rr = HeapBuf(TAUMAX)
        pfs0 = zp_fs0 * GEN ** (t * (TAUMAX + 2))
        pfs1 = zp_fs1 * GEN ** (t * (TAUMAX + 2))
        pfs0[GEN ** 0] = fs[0]
        pfs1[GEN ** 0] = fs[1]
        for xk in mul_range(1, tau_g):
            kfs = StackBuf(2)
            kfs[0] = pfs0[xk]
            kfs[1] = pfs1[xk]
            ktag = StackBuf(2)
            ktag[0] = 0
            ktag[1] = DS_SQ
            kfs = squeeze(kfs, ktag)
            rr[xk] = kfs[0]
            xkn = xk * GEN
            pfs0[xkn] = kfs[0]
            pfs1[xkn] = kfs[1]
        fs = StackBuf(2)
        fs[0] = pfs0[tau_g]
        fs[1] = pfs1[tau_g]
        # tau eq-trick rounds (claim starts at 0, eq at 1).
        rfs0 = zr_fs0 * GEN ** (t * (TAUMAX + 2))
        rfs1 = zr_fs1 * GEN ** (t * (TAUMAX + 2))
        rcur = zr_cur * GEN ** (t * (TAUMAX + 2))
        rclaim = zr_claim * GEN ** (t * (TAUMAX + 2))
        req = zr_eq * GEN ** (t * (TAUMAX + 2))
        rho_t = rho * GEN ** (t * TAUMAX)
        rfs0[GEN ** 0] = fs[0]
        rfs1[GEN ** 0] = fs[1]
        rcur[GEN ** 0] = cursor
        rclaim[GEN ** 0] = 0
        req[GEN ** 0] = 1
        for xk in mul_range(1, tau_g):
            jfs = StackBuf(2)
            jfs[0] = rfs0[xk]
            jfs[1] = rfs1[xk]
            jcur = rcur[xk]
            jclaim = rclaim[xk]
            jeq = req[xk]
            p0 = jcur[GEN ** 0]
            jfs = obs(jfs, p0)
            p1 = jcur[GEN ** 1]
            jfs = obs(jfs, p1)
            p2 = jcur[GEN ** 2]
            jfs = obs(jfs, p2)
            jcur = jcur * GEN ** 3
            rj = rr[xk]
            lhs = jeq * ((1 + rj) * p0 + rj * p1)
            assert lhs == jclaim
            jtag = StackBuf(2)
            jtag[0] = 0
            jtag[1] = DS_SQ
            jfs = squeeze(jfs, jtag)
            rk = jfs[0]
            rho_t[xk] = rk
            jeq = jeq * (1 + rj + rk)
            l0 = (rk + 1) * (rk + GG) * ILD0
            l1 = rk * (rk + GG) * ILD1
            l2 = rk * (rk + 1) * ILD2
            jclaim = jeq * (p0 * l0 + p1 * l1 + p2 * l2)
            xkn = xk * GEN
            rfs0[xkn] = jfs[0]
            rfs1[xkn] = jfs[1]
            rcur[xkn] = jcur
            rclaim[xkn] = jclaim
            req[xkn] = jeq
        fs = StackBuf(2)
        fs[0] = rfs0[tau_g]
        fs[1] = rfs1[tau_g]
        cursor = rcur[tau_g]
        claim = rclaim[tau_g]
        eq_acc = req[tau_g]
        ee = HeapBuf(16)
        for k in unroll(0, NCOL[t]):
            e = cursor[GEN ** 0]
            fs = obs(fs, e)
            cursor = cursor * GEN
            ee[GEN ** k] = e
            claim_pool[GEN ** ci] = e
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
    want_state = cvh[GEN ** 1]
    sponge_state = fs[0]
    assert sponge_state == want_state

    # ---- public-input binding claim: MEM(r_m, 0..) = interp(pi0, pi1, r_m) ----
    fs = squeeze(fs, sqz_tag)
    rm = fs[0]
    pi_interp = pi_0 + rm * (pi_0 + pi_1)
    claim_pool[GEN ** ci] = pi_interp
    ci = ci + 1

    # ---- BLAKE3 constant-pin claims (on q_pkd, at the pin bus point) ----
    # prefix = MLE of [1;NB3, 0;...] at the pin point (the first BLAKE3
    # value-column bus claim's ζ_lo: NLOGB3 coords starting at zeta[PINZOFF]):
    # one eq-term per set bit of NB3, over the aligned block's high bits.
    # Telescoping over the certified count bits, low to high: adding coord
    # z_k for bit b_k maps P -> (1+z)(b + (1+b)P) + z*b*P (b = 1 fills the
    # z_k = 0 half with the all-ones MLE 1); the top bit (count == 2^tau_5
    # exactly) forces the all-ones MLE.
    bits5 = ann_bits * GEN ** (33 * 5)
    zeta_pin = zeta * GEN ** PINZOFF
    tau5_g = ann_exp[GEN ** 6]
    pin_chain = HeapBuf(35)
    pin_chain[GEN ** 0] = 0
    for xk in mul_range(1, tau5_g):
        pv = pin_chain[xk]
        bk = bits5[xk]
        zk = zeta_pin[xk]
        pn = (1 + zk) * (bk + (1 + bk) * pv) + zk * bk * pv
        pin_chain[xk * GEN] = pn
    b_top = bits5[tau5_g]
    prefix = b_top + (1 + b_top) * pin_chain[tau5_g]
    for pk in unroll(0, 3):
        claim_pool[GEN ** ci] = PINV[pk] * prefix
        ci = ci + 1

    # ---- Phase C checkpoint ----
    want_state = cvh[GEN ** 2]
    sponge_state = fs[0]
    assert sponge_state == want_state

    # ---- flock reduction: bind_statement ----
    fs = absorb(fs, 13, DS_LEN)
    fs = absorb(fs, R1CSLBL, DS_BYTE)
    fs = absorb(fs, 32, DS_LEN)
    fs = absorb(fs, SD0, DS_BYTE)
    fs = absorb(fs, SD1, DS_BYTE)
    fs = absorb(fs, 32, DS_LEN)
    fs = absorb(fs, commit_root_0, DS_BYTE)
    fs = absorb(fs, commit_root_1, DS_BYTE)

    # ---- flock zerocheck (univariate skip, k_skip = 6) ----
    fs = absorb(fs, 18, DS_LEN)
    fs = absorb(fs, ZCLBLA, DS_BYTE)
    fs = absorb(fs, ZCLBLB, DS_BYTE)
    # the full r vector: 6 sampled skips, 7 fixed inner, MR1CS-13 sampled outer.
    zerocheck_r = HeapBuf(MR1CS)
    for i in unroll(0, 6):
        fs = squeeze(fs, sqz_tag)
        rv = fs[0]
        zerocheck_r[GEN ** i] = rv
    for i in unroll(0, 7):
        zerocheck_r[GEN ** (6 + i)] = INNER7[i]
    # outer samples at runtime count: MR1CS = KLOG + tau_5 (certified).
    mr1cs_g = ann_exp[GEN ** 6] * GEN ** KLOG
    zcr_fs0 = HeapBuf(MR1CS + 2)
    zcr_fs1 = HeapBuf(MR1CS + 2)
    zcr_fs0[GEN ** 13] = fs[0]
    zcr_fs1[GEN ** 13] = fs[1]
    for xi in mul_range(GEN ** 13, mr1cs_g):
        kfs = StackBuf(2)
        kfs[0] = zcr_fs0[xi]
        kfs[1] = zcr_fs1[xi]
        ktag = StackBuf(2)
        ktag[0] = 0
        ktag[1] = DS_SQ
        kfs = squeeze(kfs, ktag)
        zerocheck_r[xi] = kfs[0]
        xin = xi * GEN
        zcr_fs0[xin] = kfs[0]
        zcr_fs1[xin] = kfs[1]
    fs = StackBuf(2)
    fs[0] = zcr_fs0[mr1cs_g]
    fs[1] = zcr_fs1[mr1cs_g]
    # observe round-1 messages (ab then c), sample z.
    for i in unroll(0, 128):
        fs = obs(fs, zc_round1[GEN ** i])
    fs = squeeze(fs, sqz_tag)
    zerocheck_z = fs[0]
    # interpolate P^C(z) on the Lambda domain (phi8 nodes 64..128): prefix/
    # suffix numerator products with baked inverse denominators.
    lagrange_nums = StackBuf(64)
    lag64(zerocheck_z, lagrange_nums, 64)
    c_eval = 0
    for i in unroll(0, 64):
        c_eval = c_eval + lagrange_nums[i] * ILAM[i] * zc_round1[GEN ** (64 + i)]
    # combined interpolation at z over ALL 128 phi8 nodes (Lambda values only;
    # the S half is zero by the zerocheck identity). The Lambda-node numerators
    # reuse lagrange_nums: the full-domain product only adds the S-half factor.
    s_half_product = GEN ** 0
    for i in unroll(0, 64):
        s_half_product = s_half_product * (zerocheck_z + PHI[i])
    combined_eval = 0
    for i in unroll(0, 64):
        combined_eval = combined_eval + lagrange_nums[i] * ICMB[i] * (zc_round1[GEN ** i] + zc_round1[GEN ** (64 + i)])
    combined_eval = combined_eval * s_half_product
    zc_running = combined_eval + c_eval
    # multilinear rounds.
    zerocheck_rhos = HeapBuf(NMLV)
    for i in unroll(0, 7):
        gamma_c = zc_msgs[GEN ** (2 * i)]
        g_inf = zc_msgs[GEN ** (2 * i + 1)]
        r_eq = zerocheck_r[GEN ** (6 + i)]
        gamma_ab = (zc_running + r_eq * gamma_c) * I7INV[i]
        fs = obs(fs, gamma_c)
        fs = obs(fs, g_inf)
        fs = squeeze(fs, sqz_tag)
        rho_v = fs[0]
        zerocheck_rhos[GEN ** i] = rho_v
        zc_running = gamma_ab * (1 + rho_v) + gamma_c * rho_v + g_inf * rho_v * (1 + rho_v)
    # rounds 7..NMLV at runtime count: NMLV = KLOG + tau_5 - 6 (certified).
    nmlv_g = ann_exp[GEN ** 6] * GEN ** (KLOG - 6)
    uv_fs0 = HeapBuf(NMLV + 2)
    uv_fs1 = HeapBuf(NMLV + 2)
    uv_run = HeapBuf(NMLV + 2)
    uv_fs0[GEN ** 7] = fs[0]
    uv_fs1[GEN ** 7] = fs[1]
    uv_run[GEN ** 7] = zc_running
    for xi in mul_range(GEN ** 7, nmlv_g):
        jfs = StackBuf(2)
        jfs[0] = uv_fs0[xi]
        jfs[1] = uv_fs1[xi]
        jrun = uv_run[xi]
        gamma_c = zc_msgs[xi * xi]
        g_inf = zc_msgs[xi * xi * GEN]
        r_eq = zerocheck_r[GEN ** 6 * xi]
        inv_one_plus_r = zc_invs[xi]
        inv_check = (1 + r_eq) * inv_one_plus_r
        assert inv_check == 1
        gamma_ab = (jrun + r_eq * gamma_c) * inv_one_plus_r
        jfs = obs(jfs, gamma_c)
        jfs = obs(jfs, g_inf)
        jtag = StackBuf(2)
        jtag[0] = 0
        jtag[1] = DS_SQ
        jfs = squeeze(jfs, jtag)
        rho_v = jfs[0]
        zerocheck_rhos[xi] = rho_v
        jrun = gamma_ab * (1 + rho_v) + gamma_c * rho_v + g_inf * rho_v * (1 + rho_v)
        xin = xi * GEN
        uv_fs0[xin] = jfs[0]
        uv_fs1[xin] = jfs[1]
        uv_run[xin] = jrun
    fs = StackBuf(2)
    fs[0] = uv_fs0[nmlv_g]
    fs[1] = uv_fs1[nmlv_g]
    zc_running = uv_run[nmlv_g]
    # final: zc_running == a_eval * b_eval; observe both.
    a_eval = zc_finals[GEN ** 0]
    b_eval = zc_finals[GEN ** 1]
    ab_product = a_eval * b_eval
    assert zc_running == ab_product
    fs = obs(fs, a_eval)
    fs = obs(fs, b_eval)

    # ---- flock lincheck (matrix evaluation DEFERRED) ----
    fs = absorb(fs, 17, DS_LEN)
    fs = absorb(fs, LCLBLA, DS_BYTE)
    fs = absorb(fs, LCLBLB, DS_BYTE)
    fs = squeeze(fs, sqz_tag)
    lincheck_alpha = fs[0]
    fs = squeeze(fs, sqz_tag)
    lincheck_beta = fs[0]
    lc_running = lincheck_alpha * a_eval + b_eval + lincheck_beta
    lincheck_rs = HeapBuf(LCR)
    for i in unroll(0, LCR):
        e1 = lincheck_msgs[GEN ** (2 * i)]
        ei = lincheck_msgs[GEN ** (2 * i + 1)]
        fs = obs(fs, e1)
        fs = obs(fs, ei)
        fs = squeeze(fs, sqz_tag)
        rv = fs[0]
        lincheck_rs[GEN ** i] = rv
        e0 = lc_running + e1
        c1q = e0 + e1 + ei
        lc_running = ei * rv * rv + c1q * rv + e0
    for i in unroll(0, 64):
        fs = obs(fs, z_partial[GEN ** i])
    # final consistency: running == matpart (DEFERRED) + beta * pin term. The
    # const-pin column folds through the top-variable bindings: weight =
    # prod_j (bit_{klog-1-j}(PINCOL) ? r_j : 1+r_j), surviving z_partial index
    # = PINCOL low 6 bits.
    pin_term = lincheck_beta
    for j in unroll(0, LCR):
        if (PINCOL // (2 ** (KLOG - 1 - j))) % 2 == 1:
            pin_term = pin_term * lincheck_rs[GEN ** j]
        else:
            pin_term = pin_term * (1 + lincheck_rs[GEN ** j])
    pin_term = pin_term * z_partial[GEN ** (PINCOL % 64)]
    matrix_part = matrix_eval[GEN ** 0]
    lincheck_final = matrix_part + pin_term
    assert lc_running == lincheck_final
    # fresh z_skip; w = <lagrange_S(r_inner_skip), z_partial> (phi8 nodes 0..64).
    fs = squeeze(fs, sqz_tag)
    lincheck_z_skip = fs[0]
    skip_nums = StackBuf(64)
    lag64(lincheck_z_skip, skip_nums, 0)
    lincheck_w = 0
    for i in unroll(0, 64):
        lincheck_w = lincheck_w + skip_nums[i] * ISDOM[i] * z_partial[GEN ** i]

    # ---- Phase D checkpoint ----
    want_state = cvh[GEN ** 3]
    sponge_state = fs[0]
    assert sponge_state == want_state

    # ---- stacked mixed opening: ring-switch fronts + claim combination ----
    fs = absorb(fs, 23, DS_LEN)
    fs = absorb(fs, OBLBLA, DS_BYTE)
    fs = absorb(fs, OBLBLB, DS_BYTE)
    # Ring-switch claim 0 (ab): value lincheck_w, z_skip = lincheck_z_skip, x_outer[0] = lincheck_rs[LCR-1]
    # (x_inner_rest is the REVERSED lincheck round vector). Claim 1 (c): value
    # c_eval, z_skip = zerocheck_z, x_outer[0] = zerocheck_r[6].
    transposed_claims = HeapBuf(2)
    rs_eq_vals = HeapBuf(2)
    c_table = HeapBuf(128)
    z_vals = HeapBuf(2 * QPKDV)
    r_dprime = HeapBuf(7)
    for rs in unroll(0, 2):
        fs = absorb(fs, 20, DS_LEN)
        fs = absorb(fs, RSLBLA, DS_BYTE)
        fs = absorb(fs, RSLBLB, DS_BYTE)
        for i in unroll(0, 128):
            fs = obs(fs, s_hat_v[GEN ** (128 * rs + i)])
        # claim check: weights[i] = lambda_{i&63}(z_skip) * eq(x_outer0, i>>6).
        if rs == 0:
            claim_z_skip = lincheck_z_skip
            claim_x_outer_0 = lincheck_rs[GEN ** (LCR - 1)]
            claim_val = lincheck_w
        else:
            claim_z_skip = zerocheck_z
            claim_x_outer_0 = zerocheck_r[GEN ** 6]
            claim_val = c_eval
        claim_nums = StackBuf(64)
        lag64(claim_z_skip, claim_nums, 0)
        claim_check = 0
        for i in unroll(0, 64):
            lagrange_w = claim_nums[i] * ISDOM[i]
            claim_check = claim_check + lagrange_w * ((1 + claim_x_outer_0) * s_hat_v[GEN ** (128 * rs + i)] + claim_x_outer_0 * s_hat_v[GEN ** (128 * rs + 64 + i)])
        assert claim_check == claim_val
    # ONE r'' shared by both claims (each slice was absorbed before the
    # sample), so one eq tensor and one linearized coefficient table
    # serve the whole batch.
    for i in unroll(0, 7):
        fs = squeeze(fs, sqz_tag)
        rv = fs[0]
        r_dprime[GEN ** i] = rv
    w_eq = HeapBuf(254)
    eqtree(r_dprime, w_eq, 7)
    # c_k = sum_i w_i * delta_pows[k][i], one runtime loop over the levels k.
    for xk in mul_range(1, GEN ** 128):
        delta_row = delta_pows * xk ** 128
        c_acc = 0
        for i in unroll(0, 128):
            c_acc = c_acc + w_eq[GEN ** (126 + i)] * delta_row[GEN ** i]
        c_table[xk] = c_acc
    for rs in unroll(0, 2):
        # transposed claim T = sum_j x^j * L_w(shv_j): one runtime pass over
        # the observed values; per value the Frobenius powers evolve as a
        # scalar against the c table, and x^j chains through a heap cell.
        shvrow = s_hat_v * GEN ** (128 * rs)
        x_pow_chain = HeapBuf(129)
        x_pow_chain[GEN ** 0] = GEN ** 0
        t_chain = HeapBuf(129)
        t_chain[GEN ** 0] = 0
        for xj in mul_range(1, GEN ** 128):
            xh = StackBuf(1)
            xh[0] = 2
            y_pow = shvrow[xj]
            lin_eval = 0
            for k in unroll(0, 128):
                lin_eval = lin_eval + c_table[GEN ** k] * y_pow
                y_pow = y_pow * y_pow
            t_chain[xj * GEN] = t_chain[xj] + x_pow_chain[xj] * lin_eval
            x_pow_chain[xj * GEN] = x_pow_chain[xj] * xh[0]
        transposed_claims[GEN ** rs] = t_chain[GEN ** 128]
        # z_vals for eval_rs_eq (the x_outer tail), used at the opening terminal.
        if rs == 0:
            for t in unroll(0, LCR - 1):
                z_vals[GEN ** t] = lincheck_rs[GEN ** (LCR - 2 - t)]
            zv_lo = z_vals * GEN ** (LCR - 1)
            zr_hi = zerocheck_rhos * GEN ** LCR
            for xt in mul_range(1, ann_exp[GEN ** 6]):
                zv_lo[xt] = zr_hi[xt]
        else:
            for t in unroll(0, QPKDV):
                z_vals[GEN ** (QPKDV + t)] = zerocheck_r[GEN ** (7 + t)]
    # gamma-combine the two transposed sumcheck claims (computed in-circuit).
    fs = squeeze(fs, sqz_tag)
    gamma_ab = fs[0]
    fs = squeeze(fs, sqz_tag)
    gamma_c = fs[0]
    target = gamma_ab * transposed_claims[GEN ** 0] + gamma_c * transposed_claims[GEN ** 1]
    # ...then every pooled point claim, each labeled and observed.
    for j in unroll(0, NCL):
        fs = absorb(fs, 26, DS_LEN)
        fs = absorb(fs, PDLBLA, DS_BYTE)
        fs = absorb(fs, PDLBLB, DS_BYTE)
        fs = obs(fs, claim_pool[GEN ** j])
    gamma_pool = HeapBuf(NCL)
    for j in unroll(0, NCL):
        fs = squeeze(fs, sqz_tag)
        gv = fs[0]
        gamma_pool[GEN ** j] = gv
        target = target + gv * claim_pool[GEN ** j]

    # ================= the Ligerito opening core (stacked, m = STACK) ========

    ris = HeapBuf(LENRIS)
    betas = HeapBuf(NLEVELS)
    enforced_sums = HeapBuf(NLEVELS)
    alpha_weights = HeapBuf(NLEVELS * MAXQ)
    qfb = HeapBuf(QP_LEN)
    qbp = HeapBuf(QP_LEN)

    fs = absorb(fs, 23, DS_LEN)
    fs = absorb(fs, LIGLBLA, DS_BYTE)
    fs = absorb(fs, LIGLBLB, DS_BYTE)
    fs = obs(fs, target)
    fs = absorb(fs, 32, DS_LEN)
    fs = absorb(fs, commit_root_0, DS_BYTE)
    fs = absorb(fs, commit_root_1, DS_BYTE)

    msg_cursor = lsc
    msg_u0 = msg_cursor[GEN ** 0]
    fs = obs(fs, msg_u0)
    msg_u2 = msg_cursor[GEN ** 1]
    fs = obs(fs, msg_u2)
    msg_cursor = msg_cursor * GEN ** 2
    quad_c = msg_u0
    quad_b = target + msg_u2
    quad_a = msg_u2
    t_r = target

    for lvl in unroll(0, NLEVELS):
        for j in unroll(0, KLVL[lvl]):
            fold_idx = FOLDBASE[lvl] + j
            if BITS[fold_idx] != 0:
                pow_tag = StackBuf(2)
                pow_tag[0] = 0
                pow_tag[1] = DS_POW
                pow_base = StackBuf(2)
                blake3(fs, pow_tag, pow_base)
                pow_nonce = StackBuf(2)
                pow_nonce[0] = fnn[GEN ** fold_idx]
                pow_nonce[1] = DS_POW
                pow_out = StackBuf(2)
                blake3(pow_base, pow_nonce, pow_out)
                dec128(fold_grind_bits * GEN ** (128 * fold_idx), pow_out[0])
                for b in unroll(0, 8 * FULL[fold_idx]):
                    zero_bit_lo = fold_grind_bits[GEN ** (128 * fold_idx + b)]
                    assert zero_bit_lo == 0
                for b in unroll(8 * FULL[fold_idx] + 8 - EXTRA8[fold_idx], 8 * FULL[fold_idx] + 8):
                    zero_bit_hi = fold_grind_bits[GEN ** (128 * fold_idx + b)]
                    assert zero_bit_hi == 0
                nonce_v = fnn[GEN ** fold_idx]
                fs = absorb(fs, nonce_v, DS_POW)
            fs = squeeze(fs, sqz_tag)
            fold_challenge = fs[0]
            ris[GEN ** (FOLDBASE[lvl] + j)] = fold_challenge
            t_r = quad_c + fold_challenge * quad_b + fold_challenge * fold_challenge * quad_a
            msg_a = msg_cursor[GEN ** 0]
            fs = obs(fs, msg_a)
            msg_b = msg_cursor[GEN ** 1]
            fs = obs(fs, msg_b)
            msg_cursor = msg_cursor * GEN ** 2
            quad_c = msg_a
            quad_b = t_r + msg_b
            quad_a = msg_b

        if lvl == R:
            for iy in unroll(0, YR_LEN):
                fs = obs(fs, yr[GEN ** iy])
        else:
            fs = absorb(fs, 32, DS_LEN)
            next_root_a = rta[GEN ** (lvl + 1)]
            next_root_b = rtb[GEN ** (lvl + 1)]
            fs = absorb(fs, next_root_a, DS_BYTE)
            fs = absorb(fs, next_root_b, DS_BYTE)
        if QBITS[lvl] != 0:
            pow_tag = StackBuf(2)
            pow_tag[0] = 0
            pow_tag[1] = DS_POW
            pow_base = StackBuf(2)
            blake3(fs, pow_tag, pow_base)
            pow_nonce = StackBuf(2)
            pow_nonce[0] = qnonce[GEN ** lvl]
            pow_nonce[1] = DS_POW
            pow_out = StackBuf(2)
            blake3(pow_base, pow_nonce, pow_out)
            dec128(qgrind * GEN ** (128 * lvl), pow_out[0])
            for b in unroll(0, 8 * QGFULL[lvl]):
                zero_bit_lo = qgrind[GEN ** (128 * lvl + b)]
                assert zero_bit_lo == 0
            for b in unroll(8 * QGFULL[lvl] + 8 - QGEXTRA[lvl], 8 * QGFULL[lvl] + 8):
                zero_bit_hi = qgrind[GEN ** (128 * lvl + b)]
                assert zero_bit_hi == 0
            q_nonce = qnonce[GEN ** lvl]
            fs = absorb(fs, q_nonce, DS_POW)
        else:
            fs = absorb(fs, 0, DS_POW)

        sqz_chain_0 = HeapBuf(MAXNSQ + 1)
        sqz_chain_1 = HeapBuf(MAXNSQ + 1)
        sqz_chain_0[GEN ** 0] = fs[0]
        sqz_chain_1[GEN ** 0] = fs[1]
        for xs in mul_range(1, GEN ** NSQ[lvl]):
            packed_word, next_c0, next_c1 = sqz(sqz_chain_0[xs], sqz_chain_1[xs])
            sqz_chain_0[xs * GEN] = next_c0
            sqz_chain_1[xs * GEN] = next_c1
            bits_ptr = lsbits * GEN ** SBITSOFF[lvl] * xs ** 128
            query_ptr = xs ** PER[lvl]
            decq(bits_ptr, packed_word, qfb * GEN ** QPOFF[lvl] * query_ptr, qbp * GEN ** QPOFF[lvl] * query_ptr, DEPTH[lvl], PER[lvl])
        fs = StackBuf(2)
        fs[0] = sqz_chain_0[GEN ** NSQ[lvl]]
        fs[1] = sqz_chain_1[GEN ** NSQ[lvl]]

        alphas = HeapBuf(MAXNI)
        for t in unroll(0, ALPHALEN[lvl]):
            fs = squeeze(fs, sqz_tag)
            lav = fs[0]
            alphas[GEN ** t] = lav
        eq_tab = HeapBuf(MAXNI)
        for i in unroll(0, NUMINTER[lvl]):
            lp = GEN ** 0
            for c in unroll(0, KLVL[lvl]):
                lrc = ris[GEN ** (FOLDBASE[lvl] + c)]
                if (i // (2 ** c)) % 2 == 1:
                    lp = lp * lrc
                else:
                    lp = lp * (1 + lrc)
            eq_tab[GEN ** i] = lp
        for i in unroll(0, QUERIES[lvl]):
            lp = GEN ** 0
            for c in unroll(0, ALPHALEN[lvl]):
                lac = alphas[GEN ** c]
                if (i // (2 ** c)) % 2 == 1:
                    lp = lp * lac
                else:
                    lp = lp * (1 + lac)
            alpha_weights[GEN ** (lvl * MAXQ + i)] = lp

        enforced_chain = HeapBuf(MAXQ + 1)
        enforced_chain[GEN ** 0] = 0
        for xe in mul_range(1, GEN ** QUERIES[lvl]):
            row_base = xe ** NUMINTER[lvl]
            row_ptr = lrows * GEN ** ROWOFF[lvl] * row_base
            leaf_state = StackBuf(2)
            leaf_state[0] = GEN ** NBYTES[lvl]
            leaf_state[1] = 0
            row_dot = 0
            for jb in unroll(0, BLOCKS[lvl]):
                row_pair = StackBuf(2)
                row_pair[0] = row_ptr[GEN ** (2 * jb)]
                row_pair[1] = row_ptr[GEN ** (2 * jb + 1)]
                leaf_digest = StackBuf(2)
                blake3(leaf_state, row_pair, leaf_digest)
                leaf_state = leaf_digest
                row_dot = row_dot + row_pair[0] * eq_tab[GEN ** (2 * jb)] + row_pair[1] * eq_tab[GEN ** (2 * jb + 1)]
            node_0 = leaf_state[0]
            node_1 = leaf_state[1]
            enforced_chain[xe * GEN] = enforced_chain[xe] + alpha_weights[GEN ** (lvl * MAXQ) * xe] * row_dot
            walk_bits = qbp[GEN ** QPOFF[lvl] * xe]
            path_base = xe ** (2 * DEPTH[lvl])
            path_ptr = lpaths * GEN ** PATHOFF[lvl] * path_base
            for lw2 in unroll(0, DEPTH[lvl]):
                sibling_0 = path_ptr[GEN ** (2 * lw2)]
                sibling_1 = path_ptr[GEN ** (2 * lw2 + 1)]
                dir_bit = walk_bits[GEN ** lw2]
                diff_0 = node_0 + sibling_0
                diff_1 = node_1 + sibling_1
                left_node = StackBuf(2)
                left_node[0] = node_0 + dir_bit * diff_0
                left_node[1] = node_1 + dir_bit * diff_1
                right_node = StackBuf(2)
                right_node[0] = diff_0 + left_node[0]
                right_node[1] = diff_1 + left_node[1]
                walk_digest = StackBuf(2)
                blake3(left_node, right_node, walk_digest)
                node_0 = walk_digest[0]
                node_1 = walk_digest[1]
            if lvl == 0:
                assert node_0 == commit_root_0
                assert node_1 == commit_root_1
            else:
                right_node = rta[GEN ** lvl]
                root_hi = rtb[GEN ** lvl]
                assert node_0 == right_node
                assert node_1 == root_hi
        enforced_sums[GEN ** lvl] = enforced_chain[GEN ** QUERIES[lvl]]

        if lvl == R:
            fs = squeeze(fs, sqz_tag)
            beta_lvl = fs[0]
            betas[GEN ** lvl] = beta_lvl
            t_r = t_r + beta_lvl * enforced_sums[GEN ** lvl]
        else:
            intro_u0 = msg_cursor[GEN ** 0]
            fs = obs(fs, intro_u0)
            intro_u2 = msg_cursor[GEN ** 1]
            fs = obs(fs, intro_u2)
            msg_cursor = msg_cursor * GEN ** 2
            fs = squeeze(fs, sqz_tag)
            beta_lvl = fs[0]
            betas[GEN ** lvl] = beta_lvl
            enforced = enforced_sums[GEN ** lvl]
            quad_c = quad_c + beta_lvl * intro_u0
            quad_b = quad_b + beta_lvl * (enforced + intro_u2)
            quad_a = quad_a + beta_lvl * intro_u2
            t_r = t_r + beta_lvl * enforced

    # ---- residual (per level, novel basis) ----
    inner_chain = HeapBuf(NLEVELS + 1)
    inner_chain[GEN ** 0] = 0
    for lvl in unroll(0, NLEVELS):
        residual_chain = HeapBuf(MAXQ + 1)
        residual_chain[GEN ** 0] = 0
        for xr in mul_range(1, GEN ** QUERIES[lvl]):
            basis_w = StackBuf(MAXLMC)
            s_chain = qfb[GEN ** QPOFF[lvl] * xr]
            basis_w[0] = s_chain * IVK[SVKOFF[lvl]]
            for t in unroll(1, LMC[lvl]):
                s_chain = s_chain * (s_chain + SVK[SVKOFF[lvl] + t - 1])
                basis_w[t] = s_chain * IVK[SVKOFF[lvl] + t]
            prefix_eq = GEN ** 0
            for t in unroll(0, PREFIXLEN[lvl]):
                lrc = ris[GEN ** (RISSTART[lvl] + t)]
                prefix_eq = prefix_eq * (1 + lrc * (1 + basis_w[t]))
            fold_w = StackBuf(2 * YR_LOG_N)
            for j in unroll(0, YR_LOG_N):
                fold_w[2 * j] = GEN ** 0
                fold_w[2 * j + 1] = basis_w[PREFIXLEN[lvl] + j]
            yr_eval = foldyr(yr, fold_w, 0)
            residual_chain[xr * GEN] = residual_chain[xr] + alpha_weights[GEN ** (lvl * MAXQ) * xr] * prefix_eq * yr_eval
        inner_chain[GEN ** (lvl + 1)] = inner_chain[GEN ** lvl] + betas[GEN ** lvl] * residual_chain[GEN ** QUERIES[lvl]]

    # ---- generalized eval_b terminal ----
    # Per pooled claim j: eqbase_j = eq(low point, ris) x eq(selector low bits,
    # remaining ris coords); its full weight lands at residual slot YT[j]. The
    # ring-switch part (deferred rsq values) lands at slot YRS with the qpkd
    # selector eq over ris[QPKDV..].
    claim_weights = HeapBuf(NCL)
    for j in unroll(0, NCL):
        out_fs = GEN ** 0
        if CPBUF[j] == 0:
            for k in unroll(0, CPLEN[j] - NOVER[j]):
                out_fs = out_fs * (1 + zeta[GEN ** (CPOFF[j] + k)] + ris[GEN ** k])
        if CPBUF[j] == 1:
            for k in unroll(0, CPLEN[j] - NOVER[j]):
                out_fs = out_fs * (1 + rho[GEN ** (CPOFF[j] + k)] + ris[GEN ** k])
        if CPBUF[j] == 2:
            out_fs = 1 + rm + ris[GEN ** 0]
            for k in unroll(1, CPLEN[j]):
                out_fs = out_fs * (1 + ris[GEN ** k])
        if CPBUF[j] == 3:
            for k in unroll(0, 7):
                if (CSLOT[j] // (2 ** k)) % 2 == 1:
                    out_fs = out_fs * ris[GEN ** k]
                else:
                    out_fs = out_fs * (1 + ris[GEN ** k])
            for k in unroll(0, CPLEN[j]):
                out_fs = out_fs * (1 + zeta[GEN ** (CPOFF[j] + k)] + ris[GEN ** (7 + k)])
        # selector part over the ris coords above the claim's low span (SELN
        # baked as max(0, LENRIS - n_low_vars); empty when the point overlaps y).
        n_low_vars = CPLEN[j]
        if CPBUF[j] == 3:
            n_low_vars = 7 + CPLEN[j]
        for k in unroll(0, SELN[j]):
            if (CSEL[j] // (2 ** k)) % 2 == 1:
                out_fs = out_fs * ris[GEN ** (n_low_vars + k)]
            else:
                out_fs = out_fs * (1 + ris[GEN ** (n_low_vars + k)])
        claim_weights[GEN ** j] = out_fs * gamma_pool[GEN ** j]
    # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
    # (the telescoped product formula; z powers evolve by squaring per k).
    one_plus_q = HeapBuf(QPKDV)
    for j in unroll(0, QPKDV):
        one_plus_q[GEN ** j] = 1 + ris[GEN ** j]
    for rs in unroll(0, 2):
        z_pows = HeapBuf(129 * QPKDV)
        for j in unroll(0, QPKDV):
            z_pows[GEN ** j] = z_vals[GEN ** (QPKDV * rs + j)]
        e_acc = HeapBuf(129)
        e_acc[GEN ** 0] = 0
        for xk in mul_range(1, GEN ** 128):
            z_row = z_pows * xk ** QPKDV
            z_row_next = z_row * GEN ** QPKDV
            prod = GEN ** 0
            for j in unroll(0, QPKDV):
                zv = z_row[GEN ** j]
                prod = prod * (zv + one_plus_q[GEN ** j])
                z_row_next[GEN ** j] = zv * zv
            e_acc[xk * GEN] = e_acc[xk] + c_table[xk] * prod
        rs_eq_vals[GEN ** rs] = e_acc[GEN ** 128]
    # ring-switch weight base over ris[QPKDV..LENRIS).
    rs_weight = gamma_ab * rs_eq_vals[GEN ** 0] + gamma_c * rs_eq_vals[GEN ** 1]
    for k in unroll(0, LENRIS - QPKDV):
        if (RSSEL // (2 ** k)) % 2 == 1:
            rs_weight = rs_weight * ris[GEN ** (QPKDV + k)]
        else:
            rs_weight = rs_weight * (1 + ris[GEN ** (QPKDV + k)])
    # inner_sum = sum_y yr[y] * eval_b[y] + the residual sums.
    inner_sum = inner_chain[GEN ** NLEVELS]
    for y in unroll(0, YR_LEN):
        slot_sum = 0
        if y == YRS:
            slot_sum = slot_sum + rs_weight
        for j in unroll(0, NCL):
            if (y // (2 ** NOVER[j])) == YTHI[j]:
                f = claim_weights[GEN ** j]
                for t in unroll(0, NOVER[j]):
                    if CPBUF[j] == 0:
                        overlap_coord = zeta[GEN ** (CPOFF[j] + CPLEN[j] - NOVER[j] + t)]
                    else:
                        overlap_coord = rho[GEN ** (CPOFF[j] + CPLEN[j] - NOVER[j] + t)]
                    if (y // (2 ** t)) % 2 == 1:
                        f = f * overlap_coord
                    else:
                        f = f * (1 + overlap_coord)
                slot_sum = slot_sum + f
        inner_sum = inner_sum + yr[GEN ** y] * slot_sum
    assert inner_sum == t_r


    # ---- export this sub-proof's deferred-claim data to the caller ----
    # dout layout: [0..2KBC) bytecode points | +0..3 sb | +3..5 wbc | +5 alpha
    # | +6 z_skip | +7.. zrho | +7+LCR.. lincheck rs | +7+2LCR.. z_partial
    # | +71+2LCR matpart.
    for k in unroll(0, KBC):
        dout[GEN ** k] = zeta[GEN ** k]
        dout[GEN ** (KBC + k)] = zeta[GEN ** (MUMAX + k)]
    for k in unroll(0, 3):
        dout[GEN ** (2 * KBC + k)] = sb[GEN ** k]
    dout[GEN ** (2 * KBC + 3)] = wbc[GEN ** 0]
    dout[GEN ** (2 * KBC + 4)] = wbc[GEN ** 1]
    dout[GEN ** (2 * KBC + 5)] = lincheck_alpha
    dout[GEN ** (2 * KBC + 6)] = zerocheck_z
    for k in unroll(0, LCR):
        dout[GEN ** (2 * KBC + 7 + k)] = zerocheck_rhos[GEN ** k]
        dout[GEN ** (2 * KBC + 7 + LCR + k)] = lincheck_rs[GEN ** k]
    for k in unroll(0, 64):
        dout[GEN ** (2 * KBC + 7 + 2 * LCR + k)] = z_partial[GEN ** k]
    dout[GEN ** (2 * KBC + 71 + 2 * LCR)] = matrix_eval[GEN ** 0]
    return


def main():
    sqz_tag = StackBuf(2)
    sqz_tag[0] = 0
    sqz_tag[1] = DS_SQ
    spi = HeapBuf(NSUB * 2)
    hint_witness(spi[0:NSUB * 2], "spi")
    bscr = HeapBuf(2 * KBCV)
    hint_witness(bscr[0:2 * KBCV], "bscr")
    mscr = HeapBuf(4 * KLOG)
    hint_witness(mscr[0:4 * KLOG], "mscr")
    bst = HeapBuf(1)
    hint_witness(bst[0:1], "bst")
    mst = HeapBuf(2)
    hint_witness(mst[0:2], "mst")
    # The dual-basis Frobenius powers delta_pows[128k + i] = DELTA[i]^(2^k) are claim-
    # and sub-independent: build the table once, read-only afterwards.
    delta_pows = HeapBuf(128 * 128)
    for i in unroll(0, 128):
        delta_pows[GEN ** i] = DELTA[i]
    for xk in mul_range(1, GEN ** 127):
        delta_row = delta_pows * xk ** 128
        nrowd = delta_row * GEN ** 128
        for i in unroll(0, 128):
            dv = delta_row[GEN ** i]
            nrowd[GEN ** i] = dv * dv

    # per-sub deferred-claim regions (layout: see verify_sub's dout)
    defer = HeapBuf(NSUB * DEFSZ)

    for sub in unroll(0, NSUB):
        verify_sub(spi[GEN ** (2 * sub)], spi[GEN ** (2 * sub + 1)], delta_pows, defer * GEN ** (sub * DEFSZ))

    # ================= aggregation: batch the deferred claims =================
    # A fresh transcript absorbs every deferred claim (points and values),
    # samples the RLC coefficients, and verifies the two batching sumchecks of
    # doc.tex §Deferred evaluation claims. Only the reduced claims (one per
    # fixed polynomial) reach the public input.
    agg_fs = StackBuf(2)
    agg_fs[0] = 0
    agg_fs[1] = 0
    for sub in unroll(0, NSUB):
        agg_fs = obs(agg_fs, spi[GEN ** (2 * sub)])
        agg_fs = obs(agg_fs, spi[GEN ** (2 * sub + 1)])
        for k in unroll(0, 2 * KBC):
            agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + k)])
        for k in unroll(0, 3):
            agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + k)])
        agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 3)])
        agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 4)])
        agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 5)])
        agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 6)])
        for k in unroll(0, LCR):
            agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 7 + k)])
        for k in unroll(0, LCR):
            agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 7 + LCR + k)])
        for k in unroll(0, 64):
            agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 7 + 2 * LCR + k)])
        agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFSZ + 2 * KBC + 71 + 2 * LCR)])

    # ---- bytecode batching sumcheck (KBCV variables, 2*NSUB claims) ----
    gamma_bc = HeapBuf(2 * NSUB)
    bc_running = 0
    for t in unroll(0, 2 * NSUB):
        agg_fs = squeeze(agg_fs, sqz_tag)
        gv = agg_fs[0]
        gamma_bc[GEN ** t] = gv
        bc_running = bc_running + gv * defer[GEN ** ((t // 2) * DEFSZ + 2 * KBC + 3 + t % 2)]
    bc_point = HeapBuf(KBCV)
    for rd in unroll(0, KBCV):
        msg_g1 = bscr[GEN ** (2 * rd)]
        msg_ginf = bscr[GEN ** (2 * rd + 1)]
        agg_fs = obs(agg_fs, msg_g1)
        agg_fs = obs(agg_fs, msg_ginf)
        agg_fs = squeeze(agg_fs, sqz_tag)
        rv = agg_fs[0]
        bc_point[GEN ** rd] = rv
        g_zero = bc_running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        bc_running = msg_ginf * rv * rv + c_one * rv + g_zero
    # terminal: W(r*) in-circuit; the reduced bytecode claim B(r*) is deferred.
    bc_weight = 0
    for t in unroll(0, 2 * NSUB):
        e = GEN ** 0
        for k in unroll(0, KBC):
            e = e * (1 + defer[GEN ** ((t // 2) * DEFSZ + (t % 2) * KBC + k)] + bc_point[GEN ** k])
        for k in unroll(0, 3):
            e = e * (1 + defer[GEN ** ((t // 2) * DEFSZ + 2 * KBC + k)] + bc_point[GEN ** (KBC + k)])
        bc_weight = bc_weight + gamma_bc[GEN ** t] * e
    bytecode_star = bst[GEN ** 0]
    bc_final = bytecode_star * bc_weight
    assert bc_running == bc_final

    # ---- matrix batching sumcheck (2*KLOG variables, NSUB weighted claims) ----
    gamma_mat = HeapBuf(NSUB)
    mat_running = 0
    for t in unroll(0, NSUB):
        agg_fs = squeeze(agg_fs, sqz_tag)
        gv = agg_fs[0]
        gamma_mat[GEN ** t] = gv
        mat_running = mat_running + gv * defer[GEN ** (t * DEFSZ + 2 * KBC + 71 + 2 * LCR)]
    mat_point = HeapBuf(2 * KLOG)
    for rd in unroll(0, 2 * KLOG):
        msg_g1 = mscr[GEN ** (2 * rd)]
        msg_ginf = mscr[GEN ** (2 * rd + 1)]
        agg_fs = obs(agg_fs, msg_g1)
        agg_fs = obs(agg_fs, msg_ginf)
        agg_fs = squeeze(agg_fs, sqz_tag)
        rv = agg_fs[0]
        mat_point[GEN ** rd] = rv
        g_zero = mat_running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        mat_running = msg_ginf * rv * rv + c_one * rv + g_zero
    # terminal weights: U_t(r*) = urow_t(r*_row) * wcol_t(r*_col), with
    # row_weight = (sum_i L_i(zz_t) eq(r*[0..6], i)) * eq(zrho_t, r*[6..KLOG]) and
    # col_weight = (sum_i z_partial_t[i] eq(r*[KLOG..KLOG+6], i)) * prod_j (1 + lrr_j
    # + r*[2*KLOG-1-j]) (the lincheck binds column variables top-down).
    eq_rows = HeapBuf(126)
    eqtree(mat_point, eq_rows, 6)
    eq_cols = HeapBuf(126)
    eqtree(mat_point * GEN ** KLOG, eq_cols, 6)
    weight_a = 0
    weight_b = 0
    for t in unroll(0, NSUB):
        z_skip_t = defer[GEN ** (t * DEFSZ + 2 * KBC + 6)]
        row_nums = StackBuf(64)
        lag64(z_skip_t, row_nums, 0)
        row_weight = 0
        for i in unroll(0, 64):
            row_weight = row_weight + row_nums[i] * ISDOM[i] * eq_rows[GEN ** (62 + i)]
        for k in unroll(0, LCR):
            row_weight = row_weight * (1 + defer[GEN ** (t * DEFSZ + 2 * KBC + 7 + k)] + mat_point[GEN ** (6 + k)])
        col_weight = 0
        for i in unroll(0, 64):
            col_weight = col_weight + defer[GEN ** (t * DEFSZ + 2 * KBC + 7 + 2 * LCR + i)] * eq_cols[GEN ** (62 + i)]
        for j in unroll(0, LCR):
            col_weight = col_weight * (1 + defer[GEN ** (t * DEFSZ + 2 * KBC + 7 + LCR + j)] + mat_point[GEN ** (2 * KLOG - 1 - j)])
        u = row_weight * col_weight
        weight_a = weight_a + gamma_mat[GEN ** t] * defer[GEN ** (t * DEFSZ + 2 * KBC + 5)] * u
        weight_b = weight_b + gamma_mat[GEN ** t] * u
    a_star = mst[GEN ** 0]
    b_star = mst[GEN ** 1]
    mat_final = a_star * weight_a + b_star * weight_b
    assert mat_running == mat_final

    # ---- bind the sub statements + the reduced claims to the public input ----
    out_fs = StackBuf(2)
    out_fs[0] = 0
    out_fs[1] = 0
    for sub in unroll(0, NSUB):
        out_fs = obs(out_fs, spi[GEN ** (2 * sub)])
        out_fs = obs(out_fs, spi[GEN ** (2 * sub + 1)])
    for k in unroll(0, KBCV):
        out_fs = obs(out_fs, bc_point[GEN ** k])
    out_fs = obs(out_fs, bytecode_star)
    for k in unroll(0, 2 * KLOG):
        out_fs = obs(out_fs, mat_point[GEN ** k])
    out_fs = obs(out_fs, a_star)
    out_fs = obs(out_fs, b_star)
    pub_ptr = GEN ** 0
    own_pi_0 = pub_ptr[1]
    own_pi_1 = pub_ptr[GEN]
    out_word_0 = out_fs[0]
    out_word_1 = out_fs[1]
    assert own_pi_0 == out_word_0
    assert own_pi_1 == out_word_1
    return
