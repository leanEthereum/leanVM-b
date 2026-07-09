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
# SOUNDNESS: every hint is untrusted prover input; each is bound one of five
# ways, and nothing else enters the computation:
#   - sponge-bound (observed/absorbed before any challenge that depends on it):
#     the stream scalars, zc_round1/zc_msgs/zc_finals, lincheck_msgs/z_partial,
#     s_hat_v, lig_sumcheck_msgs, final_msg, the level roots level_roots_0/level_roots_1, the fold nonces fold_nonces, the
#     aggregation round messages bc_sumcheck_msgs/mat_sumcheck_msgs, and the deferred bytecode values
#     bytecode_vals (absorbed by the stacked-bytecode reduction before its challenges);
#   - assert-checked: count_root_inv and zc_invs (hinted inverses, product
#     asserted 1), grind_bits/fold_grind_bits/query_grind_hint (grinding digest bits:
#     booleanity + reconstruction against the in-circuit digest + leading-zero
#     asserts), query_index_bits (query bits: booleanity + reconstruction equal to the
#     squeezed word), merkle_leaf_rows/merkle_paths (Merkle inclusion against the bound roots);
#   - shape-certified (the announced sizes are the ground truth): dims_g
#     with count_bits/count_min_inv (the count gadget pins g^tau_t = ceil_log2 of each
#     announced count, g^log_mem via the exponent-to-word table), block_kappa
#     (pinned per block to its structural source), annmus with musbits/musinv
#     (each side's g^mu = ceil_log2 of the side total, summed in the
#     exponent), annm with mbits/minv (the committed log-size m, same
#     pattern over the committed columns), bus_grind (max-mu ties + the
#     byte/bit split relation);
#   - identity-certified (well-formedness checked here — booleanity, range
#     checks, quotient ties — with the VALUE pinned by a protocol identity
#     against committed data): block_mu_quot (sel_len_g * kappa_g == g^mu), block_sel_bits
#     and block_pad_bits (balance + decompose identities against the GKR
#     roots), the terminal claim shapes claim_low_len/claim_sel_len/
#     claim_low_vars/claim_qpkd_slot_bits/claim_sel_bits/claim_overlap_mask/
#     claim_yslot_bits and rs_yslot_bits/rs_sel_len/rs_sel_bits (the eval_b
#     terminal identity against the opening-bound target);
#   - statement-bound (fed to the outer public-input hash): sub_pis (the sub
#     statements, which also derive the transcript seeds), matpart (with its
#     complete weight data), and the reduced claims bc_star_hint/mat_stars_hint with their points.
#   checkpoints (sponge checkpoints) is debug-only: self-asserts that localize a
#   divergence during development, no soundness role.
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

# The proof stream rides ONE padded witness hint (the guest walks only the
# prefix the shape dictates); binding always comes from the per-word absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
# Per-table tau floor: BLAKE3 is sized to flock's instance count (>= 2^3).
FLOORS = [0, 0, 0, 0, 0, 3]
GINV = GINV_PLACEHOLDER
GG = GG_PLACEHOLDER
ILD0 = ILD0_PLACEHOLDER
ILD1 = ILD1_PLACEHOLDER
ILD2 = ILD2_PLACEHOLDER

# GKR sides: 0=push, 1=pull, 2=count. The layer counts mu_s are hinted and
# certified from the block kappas; ZOFF places the per-side final points
# inside `zeta` at the fixed MU_CAP stride.
ZOFF = ZOFF_PLACEHOLDER
MU_CAP = MU_CAP_PLACEHOLDER
# GKR runtime-loop chain capacities: per-tree round positions (triangle
# rounds plus one slot per layer) and the point triangle (rows x MU_CAP).
GKR_ROUNDS_CAP = GKR_ROUNDS_CAP_PLACEHOLDER
GKR_POINTS_CAP = GKR_POINTS_CAP_PLACEHOLDER

# Bus blocks, flattened across the 3 sides (side s covers blocks
# [SIDE_BLOCK_START[s], SIDE_BLOCK_START[s+1])). The block STRUCTURE is
# protocol-fixed and baked: each block's coord range [BLOCK_COORD_OFF,
# +BLOCK_COORD_COUNT), per coord COORD_TYPE (0=const, 1=col, 2=gcol, 3=index,
# 4=public bytecode), COORD_CONST (the const value, else 0), COORD_PAD_VAL
# (its default-padding fingerprint value), and the kappa SOURCE map
# (BLOCK_KAPPA_SRC/ADJ: 0=const adj, 1=log_mem, 2+t=tau_t). The block
# SHAPES (kappa, selector bits, padding delta) are hinted at runtime:
# kappa pinned to its source, the rest identity-certified.
SIDE_BLOCK_START = SIDE_BLOCK_START_PLACEHOLDER
N_BLOCKS = N_BLOCKS_PLACEHOLDER
BLOCK_KAPPA_SRC = BLOCK_KAPPA_SRC_PLACEHOLDER
BLOCK_KAPPA_ADJ = BLOCK_KAPPA_ADJ_PLACEHOLDER
BLOCK_COORD_OFF = BLOCK_COORD_OFF_PLACEHOLDER
BLOCK_COORD_COUNT = BLOCK_COORD_COUNT_PLACEHOLDER
COORD_TYPE = COORD_TYPE_PLACEHOLDER
COORD_CONST = COORD_CONST_PLACEHOLDER
COORD_PAD_VAL = COORD_PAD_VAL_PLACEHOLDER
# index_mle factor constants: INDEX_MLE_FACTORS[i] = 1 + g^(2^i).
INDEX_MLE_FACTORS = INDEX_MLE_FACTORS_PLACEHOLDER
# Number of committed-coordinate claims (Col/GCol coords across all sides), the
# deferred bytecode values (Public coords), and the count-root inverse hint.
NCLAIMS = NCLAIMS_PLACEHOLDER
N_BYTECODE_VALS = N_BYTECODE_VALS_PLACEHOLDER
# Zerochecks: per-table constraint-column counts (round counts are the
# certified tau_t).
N_AIR_COLS = N_AIR_COLS_PLACEHOLDER
TAU_CAP = TAU_CAP_PLACEHOLDER
# Phase C: the public input (baked; the seed already binds it), the real BLAKE3
# count + pin-point location, and the three public pin constants.
PIN_ZETA_OFF = PIN_ZETA_OFF_PLACEHOLDER
PIN_VALUES = PIN_VALUES_PLACEHOLDER
# Phase D (flock reduction): the r1cs statement label/digest words, zerocheck +
# lincheck label words, the seven fixed inner challenges (+ inverses of 1+c),
# the phi8 node table + baked Lagrange inverse denominators (Lambda domain,
# combined domain, S domain). R1CS_M_CAP/R1CS_ROUNDS_CAP are buffer
# capacities (the runtime sizes are K_LOG + tau_5 and K_LOG + tau_5 - 6);
# LINCHECK_ROUNDS = k_log - k_skip is protocol-fixed, PIN_COLUMN the
# const-pin column.
R1CSLBL = R1CSLBL_PLACEHOLDER
# The flock r1cs statement digest, per candidate BLAKE3 log-instance-count
# (it hashes the matrices, whose size scales with the instance count): the
# guest reads row tau_5.
SD0_TAB = SD0_TAB_PLACEHOLDER
SD1_TAB = SD1_TAB_PLACEHOLDER
B3TABLEN = B3TABLEN_PLACEHOLDER
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
R1CS_M_CAP = R1CS_M_CAP_PLACEHOLDER
R1CS_ROUNDS_CAP = R1CS_ROUNDS_CAP_PLACEHOLDER
LINCHECK_ROUNDS = LINCHECK_ROUNDS_PLACEHOLDER
PIN_COLUMN = PIN_COLUMN_PLACEHOLDER
K_LOG = K_LOG_PLACEHOLDER
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
# Phase E2: the Ligerito opening over the stacked commitment, dispatched by
# the certified committed log-size m through match_range: the LIG_* tables
# below carry one row per candidate m in [LIG_MIN_LOG_SIZE, +LIG_N_CANDIDATES),
# emitted from the SAME derive_profile/level_shapes the prover uses.
# Scalars index as TBL[m_idx]; per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl];
# per-fold grind schedules with the LIG_MAX_TOTAL_FOLDS stride; the subspace
# vanishing constants with the LIG_MAX_VANISH_LEN stride. The eval_b terminal
# claim descriptors keep only the FIXED parts baked (CLAIM_POINT_BUF: 0=zeta,
# 1=rho, 2=pi, 3=qpkd pin; CLAIM_POINT_OFF into those buffers) — the
# shape-dependent lengths/selectors are hinted and identity-certified.
LIGLBLA = LIGLBLA_PLACEHOLDER
LIGLBLB = LIGLBLB_PLACEHOLDER
# Opening dispatch: baked committed log-size, candidate range, g^-LIG_MIN_LOG_SIZE.
LIG_MIN_LOG_SIZE = LIG_MIN_LOG_SIZE_PLACEHOLDER
# Committed-column kappa sources (0 = const COL_KAPPA_ADJ, 1 = log_mem, 2+t = tau_t)
# and the PCS floor for the stacked size.
N_COMMITTED_COLS = N_COMMITTED_COLS_PLACEHOLDER
COL_KAPPA_SRC = COL_KAPPA_SRC_PLACEHOLDER
COL_KAPPA_ADJ = COL_KAPPA_ADJ_PLACEHOLDER
PCS_MIN_MU = PCS_MIN_MU_PLACEHOLDER
# Per-candidate opening tables (P3b): row (m - LIG_MIN_LOG_SIZE) drives that arm.
LIG_MAX_LEVELS = LIG_MAX_LEVELS_PLACEHOLDER
LIG_MAX_TOTAL_FOLDS = LIG_MAX_TOTAL_FOLDS_PLACEHOLDER
LIG_MAX_VANISH_LEN = LIG_MAX_VANISH_LEN_PLACEHOLDER
# Global maxima (StackBuf frame sizes are parse-time).
LIG_LOG_MSG_COLS_CAP = LIG_LOG_MSG_COLS_CAP_PLACEHOLDER
YR_LOG_CAP = YR_LOG_CAP_PLACEHOLDER
LIG_N_LEVELS = LIG_N_LEVELS_PLACEHOLDER
LIG_YR_LEVEL = LIG_YR_LEVEL_PLACEHOLDER
LIG_YR_LOG_LEN = LIG_YR_LOG_LEN_PLACEHOLDER
LIG_YR_LEN = LIG_YR_LEN_PLACEHOLDER
LIG_TOTAL_FOLDS = LIG_TOTAL_FOLDS_PLACEHOLDER
LIG_MAX_QUERIES = LIG_MAX_QUERIES_PLACEHOLDER
LIG_MAX_SQUEEZES = LIG_MAX_SQUEEZES_PLACEHOLDER
LIG_MAX_LOG_MSG_COLS = LIG_MAX_LOG_MSG_COLS_PLACEHOLDER
LIG_MAX_INTERLEAVE = LIG_MAX_INTERLEAVE_PLACEHOLDER
LIG_POSITIONS_LEN = LIG_POSITIONS_LEN_PLACEHOLDER
LIG_SUMCHECK_LEN = LIG_SUMCHECK_LEN_PLACEHOLDER
LIG_ROWS_LEN = LIG_ROWS_LEN_PLACEHOLDER
LIG_PATHS_LEN = LIG_PATHS_LEN_PLACEHOLDER
LIG_QUERY_BITS_LEN = LIG_QUERY_BITS_LEN_PLACEHOLDER
LIG_FOLD_GRIND_LEN = LIG_FOLD_GRIND_LEN_PLACEHOLDER
LIG_QUERY_GRIND_BITS = LIG_QUERY_GRIND_BITS_PLACEHOLDER
LIG_QUERY_GRIND_BYTES = LIG_QUERY_GRIND_BYTES_PLACEHOLDER
LIG_QUERY_GRIND_EXTRA = LIG_QUERY_GRIND_EXTRA_PLACEHOLDER
LIG_QUERIES = LIG_QUERIES_PLACEHOLDER
LIG_FOLDS = LIG_FOLDS_PLACEHOLDER
LIG_INTERLEAVE = LIG_INTERLEAVE_PLACEHOLDER
LIG_LEAF_BYTES = LIG_LEAF_BYTES_PLACEHOLDER
LIG_LEAF_PAIRS = LIG_LEAF_PAIRS_PLACEHOLDER
LIG_TREE_DEPTH = LIG_TREE_DEPTH_PLACEHOLDER
LIG_POSITIONS_PER_WORD = LIG_POSITIONS_PER_WORD_PLACEHOLDER
LIG_SQUEEZES = LIG_SQUEEZES_PLACEHOLDER
LIG_POSITIONS_OFF = LIG_POSITIONS_OFF_PLACEHOLDER
LIG_LOG_QUERIES = LIG_LOG_QUERIES_PLACEHOLDER
LIG_LOG_MSG_COLS = LIG_LOG_MSG_COLS_PLACEHOLDER
LIG_RESIDUAL_FOLD_OFF = LIG_RESIDUAL_FOLD_OFF_PLACEHOLDER
LIG_RESIDUAL_PREFIX_LEN = LIG_RESIDUAL_PREFIX_LEN_PLACEHOLDER
LIG_FOLDS_OFF = LIG_FOLDS_OFF_PLACEHOLDER
LIG_ROWS_OFF = LIG_ROWS_OFF_PLACEHOLDER
LIG_PATHS_OFF = LIG_PATHS_OFF_PLACEHOLDER
LIG_QUERY_BITS_OFF = LIG_QUERY_BITS_OFF_PLACEHOLDER
LIG_VANISH_OFF = LIG_VANISH_OFF_PLACEHOLDER
LIG_FOLD_GRIND_BITS = LIG_FOLD_GRIND_BITS_PLACEHOLDER
LIG_FOLD_GRIND_BYTES = LIG_FOLD_GRIND_BYTES_PLACEHOLDER
LIG_FOLD_GRIND_EXTRA = LIG_FOLD_GRIND_EXTRA_PLACEHOLDER
LIG_VANISH_VALS = LIG_VANISH_VALS_PLACEHOLDER
LIG_VANISH_INVS = LIG_VANISH_INVS_PLACEHOLDER
LIG_N_CANDIDATES = LIG_N_CANDIDATES_PLACEHOLDER
LIG_MIN_SHIFT_INV = LIG_MIN_SHIFT_INV_PLACEHOLDER
# eval_b claim descriptors (fixed parts) + the qpkd capacity stride.
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_POINT_OFF = CLAIM_POINT_OFF_PLACEHOLDER
QPKD_VARS_CAP = QPKD_VARS_CAP_PLACEHOLDER
# Ring-switch trace-dual basis: bit_i(y) = Tr(DELTA[i] * y). Any eq-weighted
# bit-sum is then the linearized polynomial L_w(y) = sum_k c_k y^(2^k) with
# c_k = sum_i w_i DELTA[i]^(2^k); since squaring is one MUL, the tensor
# transpose and eval_rs_eq run in-circuit (doc.tex, ring-switch section).
DELTA = DELTA_PLACEHOLDER
# Phase F: log rows of the bytecode blocks (the deferred bytecode points).
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER
# One sub-proof's deferred-claim region: 2*BYTECODE_LOG + 2*LINCHECK_ROUNDS + 72 words.
DEFER_SIZE = DEFER_SIZE_PLACEHOLDER
# Aggregation: NSUB sub-proofs of the same program; per-sub proof data arrives
# as hints. The seed sponge state after the two byte-string absorbs is baked
# (SEEDB), then the hinted sub statement + the baked program digest are bound.
NSUB = NSUB_PLACEHOLDER
BYTECODE_VARS = BYTECODE_VARS_PLACEHOLDER
SEEDB0 = SEEDB0_PLACEHOLDER
SEEDB1 = SEEDB1_PLACEHOLDER
DIG0 = DIG0_PLACEHOLDER
DIG1 = DIG1_PLACEHOLDER

DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQ = 4
DS_POW = 5


def squeeze_step(state_0, state_1):
    # Non-inlined sponge ratchet exposing BOTH output words (challenge and the
    # next state), so a query-squeeze loop can chain the state through a heap
    # buffer. Returns (challenge, next_state_0, next_state_1).
    a = StackBuf(2)
    a[0] = state_0
    a[1] = state_1
    b = StackBuf(2)
    b[0] = 0
    b[1] = DS_SQ
    o = StackBuf(2)
    blake3(a, b, o)
    return o[0], o[0], o[1]


def dec128(bits_ptr, v):
    # Boolean-constrain 128 hinted bits and assert they reconstruct v.
    acc = 0
    for i in unroll(0, 128):
        b = bits_ptr[GEN ** i]
        sq = b * b
        assert sq == b
        acc += b * GEN ** i  # accumulate the g-power encoding: bit i contributes g^i
    assert acc == v
    return


def decode_query_bits(bits_ptr, v, positions_out, bit_ptrs_out, depth: Const, per_word: Const):
    # dec128 fused with query extraction: each depth-bit group also becomes a
    # query position (little-endian), with a pointer to its bit run.
    acc = 0
    for j in unroll(0, per_word):
        position = 0
        for b in unroll(0, depth):
            t = bits_ptr[GEN ** (j * depth + b)]
            sq = t * t
            assert sq == t
            position += t * GEN ** b
        positions_out[GEN ** j] = position
        bit_ptrs_out[GEN ** j] = bits_ptr * GEN ** (j * depth)
        acc += position * GEN ** (j * depth)
    for i in unroll(per_word * depth, 128):
        t = bits_ptr[GEN ** i]
        sq = t * t
        assert sq == t
        acc += t * GEN ** i
    assert acc == v
    return


def check_pow(state_0, state_1, nonce, bits_ptr, full_bytes: Const, extra_bits: Const):
    # Grinding check: digest = H(H(state, (0, POW)), (nonce, POW)); the hinted
    # digest bits must be boolean, reconstruct the digest word (dec128), and
    # lead with 8*full_bytes + extra_bits zero bits (full_bytes bytes, then the top bits of
    # the next byte). The caller absorbs the nonce afterwards.
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    tag = StackBuf(2)
    tag[0] = 0
    tag[1] = DS_POW
    base = StackBuf(2)
    blake3(st, tag, base)
    nz = StackBuf(2)
    nz[0] = nonce
    nz[1] = DS_POW
    out = StackBuf(2)
    blake3(base, nz, out)
    dec128(bits_ptr, out[0])
    for b in unroll(0, 8 * full_bytes):
        zero_lo = bits_ptr[GEN ** b]
        assert zero_lo == 0
    for b in unroll(8 * full_bytes + 8 - extra_bits, 8 * full_bytes + 8):
        zero_hi = bits_ptr[GEN ** b]
        assert zero_hi == 0
    return


def pin_ceil_log(bits_row, psum_row, pow_tab, sq_tab, g_log, min_inv, floor_e: Const, nbits: Const):
    # The ceil-log certification gadget (used for the per-table taus, the GKR
    # side depths, and the committed size m): `nbits` hinted bits are boolean-
    # constrained and folded into partial sums psum_row[j] = value of the low
    # j bits; the full reconstruction `word` is returned along with the
    # exponent-domain product prod g^(bit_j 2^j) (for callers that certify
    # against an exponent-summed total). The hinted g_log is then pinned to
    # ceil_log2(word): psum_row[g_log] == word gives word < 2^log (with the
    # word == 2^log case through pow_tab), and the hinted-inverse nonzero
    # check gives word > 2^(log-1), waived at the floor (a table or PCS
    # minimum) where the true log may sit below the count's ceil-log.
    psum_row[GEN ** 0] = 0
    word = 0
    exp_prod = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits_row[GEN ** j]
        assert bit * bit == bit
        exp_prod *= (1 + bit * (sq_tab[GEN ** j] + 1))
        word += bit * (2 ** j)
        psum_row[GEN ** (j + 1)] = word
    assert log(g_log) < 34
    low = psum_row[g_log]
    diff_low = low + word
    diff_pow = word + pow_tab[g_log]
    assert diff_low * low == 0  # word < 2^log: low==0 (bits >= log clear) OR low==word (word == 2^log)
    assert diff_low * diff_pow == 0  # ...the second factor pins the count==2^log branch via the g^j->2^j table
    if g_log != GEN ** floor_e:
        low_prev = psum_row[g_log * GINV]
        min_a = low_prev + word
        min_b = word + pow_tab[g_log * GINV]
        min_prod = min_a * min_b
        assert min_prod * min_inv == 1
    return word, exp_prod


def verify_merkle_path(leaf_0, leaf_1, path_ptr, direction_bits, depth: Const):
    # Walk a Merkle authentication path from a leaf digest to the root: at
    # each level the hinted sibling pair joins the running node, ordered by
    # the query index bit (bit = 0 puts the running node on the left). The
    # caller asserts the returned pair against the transcript-bound root.
    node_0 = leaf_0
    node_1 = leaf_1
    for level in unroll(0, depth):
        sibling_0 = path_ptr[GEN ** (2 * level)]
        sibling_1 = path_ptr[GEN ** (2 * level + 1)]
        dir_bit = direction_bits[GEN ** level]  # query index bit: 0 keeps the running node left, 1 swaps it right
        diff_0 = node_0 + sibling_0
        diff_1 = node_1 + sibling_1
        left = StackBuf(2)
        left[0] = node_0 + dir_bit * diff_0
        left[1] = node_1 + dir_bit * diff_1
        right = StackBuf(2)
        right[0] = diff_0 + left[0]
        right[1] = diff_1 + left[1]
        parent = StackBuf(2)  # parent = blake3(left, right), the running node one level up
        blake3(left, right, parent)
        node_0 = parent[0]
        node_1 = parent[1]
    return node_0, node_1


def sumcheck_round3(state_0, state_1, msg_cursor, claim, eq_acc, prev_challenge):
    # One eq_acc-trick sumcheck round: observe the three round messages off the
    # stream, check the running claim at the previous challenge, squeeze the
    # round challenge round_challenge, and evaluate the round polynomial at round_challenge through the
    # {0, 1, g} Lagrange basis (baked inverse denominators). Shared by the
    # GKR layers and the AIR zerocheck rounds.
    fs = StackBuf(2)
    fs[0] = state_0
    fs[1] = state_1
    m0 = msg_cursor[GEN ** 0]
    fs = obs(fs, m0)
    m1 = msg_cursor[GEN ** 1]
    fs = obs(fs, m1)
    m2 = msg_cursor[GEN ** 2]
    fs = obs(fs, m2)
    lhs = eq_acc * ((1 + prev_challenge) * m0 + prev_challenge * m1)
    assert lhs == claim
    fs = squeeze(fs)
    round_challenge = fs[0]
    new_eq = eq_acc * (1 + prev_challenge + round_challenge)
    l0 = (round_challenge + 1) * (round_challenge + GG) * ILD0
    l1 = round_challenge * (round_challenge + GG) * ILD1
    l2 = round_challenge * (round_challenge + 1) * ILD2
    new_claim = new_eq * (m0 * l0 + m1 * l1 + m2 * l2)
    return fs[0], fs[1], msg_cursor * GEN ** 3, new_claim, new_eq, round_challenge


@inline
def fold_final_msg(msg, weights, wbase: Const, log_len: Const):
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is the
    # candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(2 ** YR_LOG_CAP)
    for t in unroll(0, 2 ** log_len // 2):
        l0[t] = weights[wbase] * msg[GEN ** (2 * t)] + weights[wbase + 1] * msg[GEN ** (2 * t + 1)]
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        nxt = StackBuf(2 ** YR_LOG_CAP)
        for t in unroll(0, n // 2):
            nxt[t] = weights[wbase + 2 * j] * cursor[2 * t] + weights[wbase + 2 * j + 1] * cursor[2 * t + 1]
        cursor = nxt
        n = n // 2
    return cursor[0]


@inline
def obs(sel_bit, x):
    # Bind one scalar into the sponge chain: sel_bit <- compress(sel_bit, (x, SCALAR)).
    # Returns the successor StackBuf; the call site aliases it (zero copies).
    tg = StackBuf(2)
    tg[0] = x
    tg[1] = DS_SCALAR
    nb = StackBuf(2)
    blake3(sel_bit, tg, nb)
    return nb


@inline
def absorb(sel_bit, x, tag):
    # Tagged absorb (length frames, byte words, grinding nonces).
    tg = StackBuf(2)
    tg[0] = x
    tg[1] = tag
    nb = StackBuf(2)
    blake3(sel_bit, tg, nb)
    return nb


@inline
def squeeze(sel_bit):
    # Ratchet: the compress output is the new state; word 0 is the challenge.
    zt = StackBuf(2)
    zt[0] = 0
    zt[1] = DS_SQ
    nb = StackBuf(2)
    blake3(sel_bit, zt, nb)
    return nb


@inline
def lag64(z, out, node_base: Const):
    # The 64 phi8-domain Lagrange NUMERATORS at z, nodes PHI[node_base..node_base+64]:
    # out[i] = prod_{j != i} (z + PHI[node_base + j]). Callers multiply by their
    # baked inverse-denominator table (ISDOM / ILAM / ICMB).
    pre = StackBuf(65)
    pre[0] = 1
    for i in unroll(0, 64):
        pre[i + 1] = pre[i] * (z + PHI[node_base + i])
    suf = StackBuf(65)
    suf[64] = 1
    for i in unroll(0, 64):
        suf[63 - i] = suf[64 - i] * (z + PHI[node_base + 63 - i])
    for i in unroll(0, 64):
        out[i] = pre[i] * suf[i + 1]
    return


@inline
def eqtree(point_ptr, out, n_coords: Const):
    # The eq tensor of the n_coords challenges at point_ptr[0..n_coords], built by doubling into
    # out (size 2^(n_coords+1) - 2); the final 2^n_coords values start at offset 2^n_coords - 2.
    r0 = point_ptr[GEN ** 0]
    out[GEN ** 0] = 1 + r0
    out[GEN ** 1] = r0
    for t in unroll(1, n_coords):
        rt = point_ptr[GEN ** t]
        one_plus_rt = 1 + rt
        for i in unroll(0, 2 ** t):
            pw = out[GEN ** (2 ** t - 2 + i)]
            out[GEN ** (2 ** (t + 1) - 2 + i)] = pw * one_plus_rt
            out[GEN ** (2 ** (t + 1) - 2 + 2 ** t + i)] = pw * rt
    return


def open_stacked(m_idx: Const, fs0, fs1, target, commit_root_0, commit_root_1):
    # The stacked Ligerito opening. m_idx is the COMMITTED-LOG-SIZE CANDIDATE
    # INDEX: the certified size is m = LIG_MIN_LOG_SIZE + m_idx, and every
    # LIG_* table below reads row m_idx (the match_range dispatch bakes one
    # specialization of this function per candidate). All opening proof data is hinted HERE, so
    # hint lengths specialize per arm; only the executed arm pops its streams.
    #
    # Flow, per level:
    #   1. fold rounds: optional grinding (check_pow), squeeze the fold
    #      challenge, advance the sumcheck round polynomial;
    #   2. bind the next level's Merkle root (or, at the last level, the
    #      final message final_msg);
    #   3. query-phase grinding, then squeeze the packed query positions;
    #   4. per query: hash the leaf row (blake3 chain), accumulate the
    #      alpha-batched row dot against the fold eq weights, and verify the
    #      Merkle authentication path against the bound root
    #      (verify_merkle_path);
    #   5. sample beta, fold the query sums into the running target.
    # Then the per-level residuals (novel-basis prefix x final-message fold)
    # are combined; the caller's eval_b terminal asserts the grand total.
    #
    # Returns (sumcheck_target, fold_challenges, final_msg, residual_total).
    fs = StackBuf(2)
    fs[0] = fs0
    fs[1] = fs1
    lig_sumcheck_msgs = HeapBuf(GEN ** (LIG_SUMCHECK_LEN[m_idx]))
    hint_witness(lig_sumcheck_msgs[0:LIG_SUMCHECK_LEN[m_idx]], "lig_sumcheck_msgs")
    merkle_leaf_rows = HeapBuf(GEN ** (LIG_ROWS_LEN[m_idx]))
    hint_witness(merkle_leaf_rows[0:LIG_ROWS_LEN[m_idx]], "merkle_leaf_rows")
    merkle_paths = HeapBuf(GEN ** (LIG_PATHS_LEN[m_idx]))
    hint_witness(merkle_paths[0:LIG_PATHS_LEN[m_idx]], "merkle_paths")
    query_index_bits = HeapBuf(GEN ** (LIG_QUERY_BITS_LEN[m_idx]))
    hint_witness(query_index_bits[0:LIG_QUERY_BITS_LEN[m_idx]], "query_index_bits")
    fold_grind_bits = HeapBuf(GEN ** (LIG_FOLD_GRIND_LEN[m_idx]))
    hint_witness(fold_grind_bits[0:LIG_FOLD_GRIND_LEN[m_idx]], "fold_grind_bits")
    final_msg = HeapBuf(GEN ** (LIG_YR_LEN[m_idx]))
    hint_witness(final_msg[0:LIG_YR_LEN[m_idx]], "final_msg")
    level_roots_0 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    hint_witness(level_roots_0[0:LIG_N_LEVELS[m_idx]], "level_roots_0")
    level_roots_1 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    hint_witness(level_roots_1[0:LIG_N_LEVELS[m_idx]], "level_roots_1")
    fold_nonces = HeapBuf(GEN ** (LIG_TOTAL_FOLDS[m_idx]))
    hint_witness(fold_nonces[0:LIG_TOTAL_FOLDS[m_idx]], "fold_nonces")
    query_nonces = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    hint_witness(query_nonces[0:LIG_N_LEVELS[m_idx]], "query_nonces")
    query_grind_hint = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * 128))
    hint_witness(query_grind_hint[0:LIG_N_LEVELS[m_idx] * 128], "query_grind_hint")
    fold_challenges = HeapBuf(GEN ** (LIG_TOTAL_FOLDS[m_idx]))
    level_betas = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    level_query_sums = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    alpha_weights = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_QUERIES[m_idx]))
    query_positions = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    query_bit_ptrs = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))

    fs = absorb(fs, 23, DS_LEN)
    fs = absorb(fs, LIGLBLA, DS_BYTE)
    fs = absorb(fs, LIGLBLB, DS_BYTE)
    fs = obs(fs, target)
    fs = absorb(fs, 32, DS_LEN)
    fs = absorb(fs, commit_root_0, DS_BYTE)
    fs = absorb(fs, commit_root_1, DS_BYTE)

    msg_cursor = lig_sumcheck_msgs
    msg_u0 = msg_cursor[GEN ** 0]
    fs = obs(fs, msg_u0)
    msg_u2 = msg_cursor[GEN ** 1]
    fs = obs(fs, msg_u2)
    msg_cursor *= GEN ** 2
    round_quad_c = msg_u0
    round_quad_b = target + msg_u2
    round_quad_a = msg_u2
    sumcheck_target = target

    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        for j in unroll(0, LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl]):
            fold_idx = LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl] + j
            if LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx] != 0:
                check_pow(fs[0], fs[1], fold_nonces[GEN ** fold_idx], fold_grind_bits * GEN ** (128 * fold_idx), LIG_FOLD_GRIND_BYTES[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx], LIG_FOLD_GRIND_EXTRA[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx])
                nonce_v = fold_nonces[GEN ** fold_idx]
                fs = absorb(fs, nonce_v, DS_POW)
            fs = squeeze(fs)
            fold_challenge = fs[0]
            fold_challenges[GEN ** (LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl] + j)] = fold_challenge
            sumcheck_target = round_quad_c + fold_challenge * round_quad_b + fold_challenge * fold_challenge * round_quad_a  # evaluate this level's folded quadratic at the fold challenge
            msg_a = msg_cursor[GEN ** 0]
            fs = obs(fs, msg_a)
            msg_b = msg_cursor[GEN ** 1]
            fs = obs(fs, msg_b)
            msg_cursor *= GEN ** 2
            round_quad_c = msg_a
            round_quad_b = sumcheck_target + msg_b
            round_quad_a = msg_b

        if lvl == LIG_YR_LEVEL[m_idx]:
            for iy in unroll(0, LIG_YR_LEN[m_idx]):
                fs = obs(fs, final_msg[GEN ** iy])
        else:
            fs = absorb(fs, 32, DS_LEN)
            next_root_a = level_roots_0[GEN ** (lvl + 1)]
            next_root_b = level_roots_1[GEN ** (lvl + 1)]
            fs = absorb(fs, next_root_a, DS_BYTE)
            fs = absorb(fs, next_root_b, DS_BYTE)
        if LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl] != 0:
            check_pow(fs[0], fs[1], query_nonces[GEN ** lvl], query_grind_hint * GEN ** (128 * lvl), LIG_QUERY_GRIND_BYTES[m_idx * LIG_MAX_LEVELS + lvl], LIG_QUERY_GRIND_EXTRA[m_idx * LIG_MAX_LEVELS + lvl])
            q_nonce = query_nonces[GEN ** lvl]
            fs = absorb(fs, q_nonce, DS_POW)
        else:
            fs = absorb(fs, 0, DS_POW)

        sqz_chain_0 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_1 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_0[GEN ** 0] = fs[0]
        sqz_chain_1[GEN ** 0] = fs[1]
        for xs in mul_range(1, GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]):
            packed_word, next_c0, next_c1 = squeeze_step(sqz_chain_0[xs], sqz_chain_1[xs])
            sqz_chain_0[xs * GEN] = next_c0
            sqz_chain_1[xs * GEN] = next_c1
            bits_ptr = query_index_bits * GEN ** LIG_QUERY_BITS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xs ** 128
            query_ptr = xs ** LIG_POSITIONS_PER_WORD[m_idx * LIG_MAX_LEVELS + lvl]
            decode_query_bits(bits_ptr, packed_word, query_positions * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, query_bit_ptrs * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl], LIG_POSITIONS_PER_WORD[m_idx * LIG_MAX_LEVELS + lvl])
        fs = StackBuf(2)
        fs[0] = sqz_chain_0[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]]
        fs[1] = sqz_chain_1[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]]

        query_alphas = HeapBuf(GEN ** (LIG_MAX_INTERLEAVE[m_idx]))
        for t in unroll(0, LIG_LOG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            fs = squeeze(fs)
            alpha_v = fs[0]
            query_alphas[GEN ** t] = alpha_v
        row_eq_weights = HeapBuf(GEN ** (LIG_MAX_INTERLEAVE[m_idx]))
        for i in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
            lp = GEN ** 0
            for c in unroll(0, LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl]):
                fold_c = fold_challenges[GEN ** (LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl] + c)]
                if (i // (2 ** c)) % 2 == 1:
                    lp *= fold_c
                else:
                    lp *= (1 + fold_c)
            row_eq_weights[GEN ** i] = lp
        for i in unroll(0, LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            lp = GEN ** 0
            for c in unroll(0, LIG_LOG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
                lac = query_alphas[GEN ** c]
                if (i // (2 ** c)) % 2 == 1:
                    lp *= lac
                else:
                    lp *= (1 + lac)
            alpha_weights[GEN ** (lvl * LIG_MAX_QUERIES[m_idx] + i)] = lp

        query_sum_chain = HeapBuf(GEN ** (LIG_MAX_QUERIES[m_idx] + 1))
        query_sum_chain[GEN ** 0] = 0
        for xe in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            row_base = xe ** LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]
            row_ptr = merkle_leaf_rows * GEN ** LIG_ROWS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * row_base
            leaf_hash_state = StackBuf(2)
            leaf_hash_state[0] = GEN ** LIG_LEAF_BYTES[m_idx * LIG_MAX_LEVELS + lvl]
            leaf_hash_state[1] = 0
            row_dot = 0
            for jb in unroll(0, LIG_LEAF_PAIRS[m_idx * LIG_MAX_LEVELS + lvl]):
                row_pair = StackBuf(2)
                row_pair[0] = row_ptr[GEN ** (2 * jb)]
                row_pair[1] = row_ptr[GEN ** (2 * jb + 1)]
                leaf_digest = StackBuf(2)
                blake3(leaf_hash_state, row_pair, leaf_digest)  # hash-fold the queried leaf row into the running leaf digest
                leaf_hash_state = leaf_digest
                row_dot += row_pair[0] * row_eq_weights[GEN ** (2 * jb)] + row_pair[1] * row_eq_weights[GEN ** (2 * jb + 1)]
            node_0 = leaf_hash_state[0]
            node_1 = leaf_hash_state[1]
            query_sum_chain[xe * GEN] = query_sum_chain[xe] + alpha_weights[GEN ** (lvl * LIG_MAX_QUERIES[m_idx]) * xe] * row_dot
            direction_bits = query_bit_ptrs[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xe]
            path_base = xe ** (2 * LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            path_ptr = merkle_paths * GEN ** LIG_PATHS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * path_base
            root_0, root_1 = verify_merkle_path(node_0, node_1, path_ptr, direction_bits, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])  # walk the query's Merkle path to the level root
            if lvl == 0:
                assert root_0 == commit_root_0
                assert root_1 == commit_root_1
            else:
                want_root_0 = level_roots_0[GEN ** lvl]
                want_root_1 = level_roots_1[GEN ** lvl]
                assert root_0 == want_root_0
                assert root_1 == want_root_1
        level_query_sums[GEN ** lvl] = query_sum_chain[GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]]

        if lvl == LIG_YR_LEVEL[m_idx]:
            fs = squeeze(fs)
            beta_lvl = fs[0]
            level_betas[GEN ** lvl] = beta_lvl
            sumcheck_target += beta_lvl * level_query_sums[GEN ** lvl]
        else:
            intro_u0 = msg_cursor[GEN ** 0]
            fs = obs(fs, intro_u0)
            intro_u2 = msg_cursor[GEN ** 1]
            fs = obs(fs, intro_u2)
            msg_cursor *= GEN ** 2
            fs = squeeze(fs)
            beta_lvl = fs[0]
            level_betas[GEN ** lvl] = beta_lvl
            level_query_sum = level_query_sums[GEN ** lvl]
            round_quad_c += beta_lvl * intro_u0
            round_quad_b += beta_lvl * (level_query_sum + intro_u2)
            round_quad_a += beta_lvl * intro_u2
            sumcheck_target += beta_lvl * level_query_sum

    # ---- per-level residuals: novel-basis prefix x final-message fold ----
    inner_chain = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] + 1))
    inner_chain[GEN ** 0] = 0
    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        residual_chain = HeapBuf(GEN ** (LIG_MAX_QUERIES[m_idx] + 1))
        residual_chain[GEN ** 0] = 0
        for xr in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            basis_w = StackBuf(LIG_LOG_MSG_COLS_CAP)
            basis_chain = query_positions[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xr]
            basis_w[0] = basis_chain * LIG_VANISH_INVS[m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl]]
            for t in unroll(1, LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + lvl]):
                basis_chain *= (basis_chain + LIG_VANISH_VALS[m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t - 1])  # subspace-vanishing recurrence for the novel-basis point
                basis_w[t] = basis_chain * LIG_VANISH_INVS[m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t]
            prefix_eq = GEN ** 0
            for t in unroll(0, LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl]):
                fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t)]
                prefix_eq *= (1 + fold_c * (1 + basis_w[t]))
            fold_w = StackBuf(2 * YR_LOG_CAP)
            for j in unroll(0, LIG_YR_LOG_LEN[m_idx]):
                fold_w[2 * j] = GEN ** 0
                fold_w[2 * j + 1] = basis_w[LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl] + j]
            yr_eval = fold_final_msg(final_msg, fold_w, 0, LIG_YR_LOG_LEN[m_idx])
            residual_chain[xr * GEN] = residual_chain[xr] + alpha_weights[GEN ** (lvl * LIG_MAX_QUERIES[m_idx]) * xr] * prefix_eq * yr_eval
        inner_chain[GEN ** (lvl + 1)] = inner_chain[GEN ** lvl] + level_betas[GEN ** lvl] * residual_chain[GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]]  # accumulate beta_lvl * (per-level residual sum) into the grand residual
    return sumcheck_target, fold_challenges, final_msg, inner_chain[GEN ** LIG_N_LEVELS[m_idx]]


def verify_sub(pi_0, pi_1, delta_pows, defer_out):
    # In-circuit verification of ONE inner proof for the statement
    # (pi_0, pi_1). All proof data is hinted HERE: each call pops the next
    # sub-proof's entry of every witness stream, so the body lowers once and
    # main just calls it per statement. `delta_pows` is the shared dual-basis
    # Frobenius table; the deferred-claim data is written to `defer_out`.
    #
    # Flow (mirrors cpu::verify):
    #   1. seed the Fiat-Shamir sponge from the statement + program digest;
    #   2. announced sizes, then certify every structural log against them
    #      (count gadget pin_ceil_log: tau per table, log_mem);
    #   3. bind the commitment root; bus grinding (check_pow-style, runtime
    #      bit count); 3x GKR grand product at runtime depth
    #      (sumcheck_round3 per round);
    #   4. certify the block kappas + GKR side depths; balance check with
    #      hinted padding ladders; 3x leaf decomposition against the GKR
    #      claims (pooling the committed-coordinate claims); the
    #      stacked-bytecode reduction (deferred);
    #   5. six AIR zerochecks at the certified taus (sumcheck_round3);
    #   6. public-input claim + BLAKE3 pin claims (telescoped prefix MLE);
    #   7. flock reduction: univariate-skip zerocheck + lincheck (matrix
    #      evaluation deferred);
    #   8. ring-switch fronts (shared r'', linearized transpose in-circuit);
    #   9. gamma-combine everything, certify the committed size m, dispatch
    #      the stacked Ligerito opening (open_stacked), and assert its
    #      eval_b terminal;
    #  10. export the deferred-claim region for the aggregation.
    checkpoints = StackBuf(4)
    hint_witness(checkpoints[0:4], "checkpoints")
    stream = HeapBuf(STREAM_CAP)
    hint_witness(stream[0:STREAM_CAP], "stream")
    ann_mus = HeapBuf(3)
    hint_witness(ann_mus[0:3], "annmus")
    grind_bits = HeapBuf(128)
    hint_witness(grind_bits[0:128], "grind_bits")
    bytecode_vals = HeapBuf(N_BYTECODE_VALS)
    hint_witness(bytecode_vals[0:N_BYTECODE_VALS], "bytecode_vals")
    count_root_inv = HeapBuf(1)
    hint_witness(count_root_inv[0:1], "count_root_inv")
    zc_round1 = HeapBuf(128)
    hint_witness(zc_round1[0:128], "zc_round1")
    zc_msgs = HeapBuf(2 * R1CS_ROUNDS_CAP)
    hint_witness(zc_msgs[0:2 * R1CS_ROUNDS_CAP], "zc_msgs")
    zc_finals = StackBuf(2)
    hint_witness(zc_finals[0:2], "zc_finals")
    zc_invs = HeapBuf(R1CS_ROUNDS_CAP)
    hint_witness(zc_invs[0:R1CS_ROUNDS_CAP], "zc_invs")
    lincheck_msgs = HeapBuf(2 * LINCHECK_ROUNDS)
    hint_witness(lincheck_msgs[0:2 * LINCHECK_ROUNDS], "lincheck_msgs")
    z_partial = HeapBuf(64)
    hint_witness(z_partial[0:64], "z_partial")
    matrix_eval = StackBuf(1)
    hint_witness(matrix_eval[0:1], "matpart")
    s_hat_v = HeapBuf(256)
    hint_witness(s_hat_v[0:256], "s_hat_v")
    # Claim pool: values of every committed-coordinate claim, in decompose order
    # (their points are the GKR ζ's, resolvable from the baked block structure).
    claim_pool = HeapBuf(NCLAIMS)
    # The three GKR leaf points, stored side by side (ZOFF offsets).
    zeta = HeapBuf(3 * MU_CAP)

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    fs = StackBuf(2)
    fs[0] = SEEDB0  # SEEDB = sponge state after absorbing the b"leanvm-b" domain label
    fs[1] = SEEDB1
    fs = obs(fs, pi_0)  # bind the sub-proof's statement (its public input word 0)
    fs = obs(fs, pi_1)
    fs = obs(fs, DIG0)  # bind the inner PROGRAM digest (DIG0/DIG1 = blake3 of its bytecode)
    fs = obs(fs, DIG1)
    cursor = stream  # the proof stream is replayed word by word; cursor walks it (advance = * g)

    # ---- announced sizes: log_mem + 6 row counts (observed, then certified) ----
    sizes = StackBuf(7)
    for i in unroll(0, 7):
        x = cursor[GEN ** 0]
        fs = obs(fs, x)
        sizes[i] = x
        cursor *= GEN

    # ---- certify the hinted structural logs against the announced words ----
    # The stream announced the sizes as integer WORDS; the shape-generic
    # phases need them as G-POWERS (loop bounds, match_range scrutinees), so
    # the g-power forms arrive as hints and are pinned to the words here:
    #   dims_g[0]     = g^log_mem, dims_g[1 + t] = g^tau_t (t = table);
    #   count_bits       = the 33-bit decomposition of each announced count,
    #                      certifying tau_t = ceil_log2(count) (the gadget);
    #   count_min_inv    = the gadget's minimality-check inverses (count > 2^(tau-1)).
    dims_g = HeapBuf(7)
    hint_witness(dims_g[0:7], "dims_g")
    count_bits = HeapBuf(198)
    hint_witness(count_bits[0:198], "count_bits")
    count_min_inv = StackBuf(6)
    hint_witness(count_min_inv[0:6], "count_min_inv")
    # Baked tables over exponents: T[g^j] = j and W[g^j] = 2^j (words), the
    # exponent-doubling table g_squares[g^j] = g^(2^j) (integer sums of powers
    # of two become field products), and kappa_base mapping a kappa source
    # index to its certified announced log (source 0 = const, handled by the
    # baked adj shift alone).
    exp_word = HeapBuf(33)
    pow_word = HeapBuf(33)
    for j in unroll(0, 33):
        exp_word[GEN ** j] = j
        pow_word[GEN ** j] = 2 ** j
    g_squares = HeapBuf(34)
    sq_run = GEN
    for j in unroll(0, 34):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    # log_mem is announced AS a log (an integer word L): T[g^L] == L pins the
    # hinted g-power to it.
    g_log_mem = dims_g[GEN ** 0]
    assert log(g_log_mem) < 33
    lm_word = exp_word[g_log_mem]
    lm_ann = sizes[0]
    assert lm_word == lm_ann
    kappa_base = HeapBuf(8)
    kappa_base[GEN ** 0] = 1
    kappa_base[GEN ** 1] = g_log_mem
    for t in unroll(0, 6):
        kappa_base[GEN ** (2 + t)] = dims_g[GEN ** (t + 1)]
    # Per count: 32 hinted bits -> partial sums p[j] = value of the low j
    # bits; p[32] == count binds the bits to the announced word; then
    # p[g^tau] pins count < 2^tau (or count == 2^tau via W), and a
    # hinted-inverse nonzero check pins minimality, waived at the table's
    # floor (BLAKE3 sizes to flock's instance count, ceil_log2(max(n, 8))).
    psums = HeapBuf(6 * 35)
    for t in unroll(0, 6):
        gtau = dims_g[GEN ** (t + 1)]
        tau_word, tau_exp = pin_ceil_log(count_bits * GEN ** (33 * t), psums * GEN ** (35 * t), pow_word, g_squares, gtau, count_min_inv[t], FLOORS[t], 33)
        count = sizes[t + 1]
        assert tau_word == count

    # ---- commitment root (2 words), kept for the opening phase ----
    commit_root_0 = cursor[GEN ** 0]
    fs = obs(fs, commit_root_0)
    cursor *= GEN
    commit_root_1 = cursor[GEN ** 0]
    fs = obs(fs, commit_root_1)
    cursor *= GEN

    # ---- bus: α, grinding, γ ----
    fs = squeeze(fs)
    alpha = fs[0]
    # grinding nonce: raw stream word (NOT observed), PoW-checked, then bound.
    nonce = cursor[GEN ** 0]
    cursor *= GEN
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
    # Bus grind bits at runtime: bits = max(mu_0, mu_1, mu_2) + 1 +
    # SECURITY - 128 = maxmu - 7 (leaf::grand_product_grinding_bits: the
    # side totals are powers of two, so ceil_log2 of their sum is the max
    # plus one). The hinted max is tied to each mu by a quotient range
    # check and pinned to one of them by a product of differences; the
    # hinted byte/bit split ties via f^8 * e == g^bits.
    bus_grind = StackBuf(7)
    hint_witness(bus_grind[0:7], "bus_grind")
    max_mu = bus_grind[0]
    for s in unroll(0, 3):
        max_mu_quot = bus_grind[4 + s]
        assert log(max_mu_quot) < 34
        max_mu_tie = max_mu_quot * ann_mus[GEN ** s]
        assert max_mu_tie == max_mu
    max_mu_pin = (max_mu + ann_mus[GEN ** 0]) * (max_mu + ann_mus[GEN ** 1]) * (max_mu + ann_mus[GEN ** 2])  # max_mu must equal one of the three GKR side depths (a factor is 0)
    assert max_mu_pin == 0
    grind_bytes_g = bus_grind[1]
    assert log(grind_bytes_g) < 6
    grind_extra_g = bus_grind[2]
    assert log(grind_extra_g) < 9
    grind_tail_shift_g = bus_grind[3]
    assert log(grind_tail_shift_g) < 9
    grind_split_tie = grind_tail_shift_g * grind_extra_g  # tail_shift * extra == g^8: they partition the final byte's 8 bits
    assert grind_split_tie == GEN ** 8
    grind_full_bits_g = grind_bytes_g ** 8
    grind_total_tie = grind_full_bits_g * grind_extra_g * GEN ** 7  # 8*full + extra reconstructs the bus bit count, tied to max_mu
    assert grind_total_tie == max_mu
    for xb in mul_range(1, grind_full_bits_g):
        z0 = grind_bits[xb]
        assert z0 == 0
    tail_ptr = grind_bits * grind_full_bits_g * grind_tail_shift_g
    for xb in mul_range(1, grind_extra_g):
        z1 = tail_ptr[xb]
        assert z1 == 0
    fs = absorb(fs, nonce, DS_POW)
    fs = squeeze(fs)
    gamma = fs[0]

    # ---- 3× GKR grand product (push / pull / count), RUNTIME depth ----
    # The layer count mu_s is a hinted g-power, certified below (decompose
    # section) as ceil_log2 of the side's block total. Both loop levels are
    # runtime mul_range; the sponge, stream cursor, claim, and eq accumulator
    # thread through write-once heap chains: layer state indexed by the layer
    # cursor, round state by a per-tree position pointer advancing per round.
    gkr_roots = StackBuf(3)
    gkr_claims = StackBuf(3)
    gkr_layer_fs0 = HeapBuf(3 * (MU_CAP + 2))
    gkr_layer_fs1 = HeapBuf(3 * (MU_CAP + 2))
    gkr_layer_cursor = HeapBuf(3 * (MU_CAP + 2))
    gkr_layer_claim = HeapBuf(3 * (MU_CAP + 2))
    gkr_layer_row = HeapBuf(3 * (MU_CAP + 2))
    gkr_layer_round_pos = HeapBuf(3 * (MU_CAP + 2))
    gkr_round_fs0 = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_round_fs1 = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_round_cursor = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_round_claim = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_round_eq = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_pts = HeapBuf(3 * GKR_POINTS_CAP)
    for s in unroll(0, 3):
        mu_g = ann_mus[GEN ** s]
        assert log(mu_g) < 33
        gkr_root = cursor[GEN ** 0]
        fs = obs(fs, gkr_root)
        cursor *= GEN
        lfs0 = gkr_layer_fs0 * GEN ** (s * (MU_CAP + 2))
        lfs1 = gkr_layer_fs1 * GEN ** (s * (MU_CAP + 2))
        lcur = gkr_layer_cursor * GEN ** (s * (MU_CAP + 2))
        lclaim = gkr_layer_claim * GEN ** (s * (MU_CAP + 2))
        lrow = gkr_layer_row * GEN ** (s * (MU_CAP + 2))
        lrnd = gkr_layer_round_pos * GEN ** (s * (MU_CAP + 2))
        lfs0[GEN ** 0] = fs[0]
        lfs1[GEN ** 0] = fs[1]
        lcur[GEN ** 0] = cursor
        lclaim[GEN ** 0] = gkr_root
        lrow[GEN ** 0] = gkr_pts * GEN ** (s * GKR_POINTS_CAP)
        lrnd[GEN ** 0] = GEN ** (s * GKR_ROUNDS_CAP)
        for x_layer in mul_range(1, mu_g):
            layer_fs = StackBuf(2)
            layer_fs[0] = lfs0[x_layer]
            layer_fs[1] = lfs1[x_layer]
            layer_cursor = lcur[x_layer]
            claim_l = lclaim[x_layer]
            point_row = lrow[x_layer]
            round_pos = lrnd[x_layer]
            nextrow = point_row * GEN ** MU_CAP
            gkr_round_fs0[round_pos] = layer_fs[0]
            gkr_round_fs1[round_pos] = layer_fs[1]
            gkr_round_cursor[round_pos] = layer_cursor
            gkr_round_claim[round_pos] = claim_l
            gkr_round_eq[round_pos] = 1
            for x_round in mul_range(1, x_layer):
                ip = round_pos * x_round
                nfs0, nfs1, ncur, nclaim, neq, rk = sumcheck_round3(gkr_round_fs0[ip], gkr_round_fs1[ip], gkr_round_cursor[ip], gkr_round_claim[ip], gkr_round_eq[ip], point_row[x_round])
                nextrow[x_round * GEN] = rk
                pos_next = ip * GEN
                gkr_round_fs0[pos_next] = nfs0
                gkr_round_fs1[pos_next] = nfs1
                gkr_round_cursor[pos_next] = ncur
                gkr_round_claim[pos_next] = nclaim
                gkr_round_eq[pos_next] = neq
            final_pos = round_pos * x_layer
            tail_fs = StackBuf(2)
            tail_fs[0] = gkr_round_fs0[final_pos]
            tail_fs[1] = gkr_round_fs1[final_pos]
            tcur = gkr_round_cursor[final_pos]
            tclaim = gkr_round_claim[final_pos]
            teq = gkr_round_eq[final_pos]
            e0 = tcur[GEN ** 0]
            tail_fs = obs(tail_fs, e0)
            e1 = tcur[GEN ** 1]
            tail_fs = obs(tail_fs, e1)
            tcur *= GEN ** 2
            assert tclaim == teq * e0 * e1
            tail_fs = squeeze(tail_fs)
            layer_challenge = tail_fs[0]
            next_claim = e0 + layer_challenge * (e0 + e1)
            nextrow[GEN ** 0] = layer_challenge
            xln = x_layer * GEN
            lfs0[xln] = tail_fs[0]
            lfs1[xln] = tail_fs[1]
            lcur[xln] = tcur
            lclaim[xln] = next_claim
            lrow[xln] = nextrow
            lrnd[xln] = round_pos * x_layer * GEN
        fs = StackBuf(2)
        fs[0] = lfs0[mu_g]
        fs[1] = lfs1[mu_g]
        cursor = lcur[mu_g]
        final_point_row = lrow[mu_g]
        zeta_s = zeta * GEN ** ZOFF[s]
        for xt in mul_range(1, mu_g):
            zeta_s[xt] = final_point_row[xt]
        gkr_roots[s] = gkr_root
        gkr_claims[s] = lclaim[mu_g]

    # ---- count root nonzero (hinted inverse) ----
    count_product = gkr_roots[2] * count_root_inv[GEN ** 0]  # count-tree root != 0 via a hinted inverse (product == 1 below)
    assert count_product == 1

    # ---- per-block shape data (hinted; the identities certify it) ----
    # kappa and the side-quotient g^(mu_s - kappa) are range-checked and tied
    # to each other against the hinted mu_s; selector and padding-delta bits
    # are boolean-checked. Wrong values cannot satisfy the balance and
    # decompose identities against the committed bus (and, downstream, the
    # opening), so no further certification is needed.
    block_kappa = HeapBuf(N_BLOCKS)
    hint_witness(block_kappa[0:N_BLOCKS], "block_kappa")
    block_mu_quot = HeapBuf(N_BLOCKS)
    hint_witness(block_mu_quot[0:N_BLOCKS], "block_mu_quot")
    block_sel_bits = HeapBuf(N_BLOCKS * MU_CAP)
    hint_witness(block_sel_bits[0:N_BLOCKS * MU_CAP], "block_sel_bits")
    block_pad_bits = HeapBuf(N_BLOCKS * 33)
    hint_witness(block_pad_bits[0:N_BLOCKS * 33], "block_pad_bits")
    idxc_tab = HeapBuf(34)
    for t in unroll(0, 34):
        idxc_tab[GEN ** t] = INDEX_MLE_FACTORS[t]
    # Every hinted block kappa is pinned DIRECTLY to its structural source
    # (baked per block: the boundary consts, log_mem, the bytecode log, or
    # tau_t) — no identity-chaining needed for the block shapes.
    for b in unroll(0, N_BLOCKS):
        kappa_want = kappa_base[GEN ** BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]
        kappa_have = block_kappa[GEN ** b]
        assert kappa_have == kappa_want
    # And each side's mu is certified as ceil_log2(sum of the side's 2^kappa):
    # the side total rides the exponent as a product of g^(2^kappa) factors,
    # hinted bits reproduce it and reconstruct the total word, and the count
    # gadget tail pins the hinted g^mu (no floor: side totals are >= 2).
    mus_bits = HeapBuf(3 * 34)
    hint_witness(mus_bits[0:3 * 34], "musbits")
    mus_inv = StackBuf(3)
    hint_witness(mus_inv[0:3], "musinv")
    mus_psums = HeapBuf(3 * 35)
    for s in unroll(0, 3):
        side_total_g = GEN ** 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            side_total_g *= g_squares[block_kappa[GEN ** b]]
        side_word, side_exp = pin_ceil_log(mus_bits * GEN ** (34 * s), mus_psums * GEN ** (35 * s), pow_word, g_squares, ann_mus[GEN ** s], mus_inv[s], 0, 34)
        assert side_exp == side_total_g

    # ---- balance: push_root · d_pull == pull_root · d_push ----
    # d_side = Π_b (γ + Σ_i α^i·COORD_PAD_VAL[i])^DELTA_b; the delta exponent rides its
    # hinted bits through a square-and-multiply ladder (uniform over blocks:
    # unpadded blocks hint delta = 0 and the ladder is the identity).
    pad_products = HeapBuf(2)
    for s in unroll(0, 2):
        side_pad_product = GEN ** 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            pad_fp = 0
            alpha_pow = GEN ** 0
            for i in unroll(0, BLOCK_COORD_COUNT[b]):
                pad_fp += alpha_pow * COORD_PAD_VAL[BLOCK_COORD_OFF[b] + i]
                alpha_pow *= alpha
            ladder = GEN ** 0
            ladder_square = gamma + pad_fp
            for j in unroll(0, 33):
                pad_bit = block_pad_bits[GEN ** (b * 33 + j)]
                assert pad_bit * pad_bit == pad_bit
                ladder *= (1 + pad_bit * (ladder_square + 1))
                ladder_square *= ladder_square
            side_pad_product *= ladder
        pad_products[GEN ** s] = side_pad_product
    lhsb = gkr_roots[0] * pad_products[GEN ** 1]  # balance: push_root * d_pull == pull_root * d_push (padding cancels)
    rhsb = gkr_roots[1] * pad_products[GEN ** 0]
    assert lhsb == rhsb

    # ---- 3× leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); the Public
    # (bytecode) coordinate values are hinted (bytecode_vals) and exported as deferred
    # claims; Index coordinates use the factored index MLE.
    claim_idx = 0
    bytecode_idx = 0
    for s in unroll(0, 3):
        acc = 0
        selector_sum = 0
        smu_gs = ann_mus[GEN ** s]
        zeta_zs = zeta * GEN ** ZOFF[s]
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            # eq_hi over the ζ coords above κ, against the HINTED selector
            # bits (eq(s, z) = 1 + s + z in this field); the bound mu_s - κ
            # rides the hinted quotient, tied by sel_len_g · κg == g^mu_s.
            kappa_g = block_kappa[GEN ** b]
            assert log(kappa_g) < 34
            sel_len_g = block_mu_quot[GEN ** b]
            assert log(sel_len_g) < 34
            qk_prod = sel_len_g * kappa_g  # tie hinted quotient to kappa: q * g^kappa == g^mu (so q = g^(mu-kappa))
            assert qk_prod == smu_gs
            zeta_hi = zeta_zs * kappa_g
            selrow = block_sel_bits * GEN ** (b * MU_CAP)
            eq_chain = HeapBuf(MU_CAP + 2)
            eq_chain[GEN ** 0] = 1
            for xk in mul_range(1, sel_len_g):
                sbit = selrow[xk]
                assert sbit * sbit == sbit
                eq_chain[xk * GEN] = eq_chain[xk] * (1 + sbit + zeta_hi[xk])  # eq(sel_bit, zeta) = 1 + sel_bit + zeta over GF(2)
            eq_hi = eq_chain[sel_len_g]
            selector_sum += eq_hi
            # inner fingerprint Σ_i α^i · coord_i(ζ_lo); count side uses α=1,γ=0.
            inner_sum = 0
            alpha_pow = GEN ** 0
            for i in unroll(0, BLOCK_COORD_COUNT[b]):
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == 0:
                    coord_val = COORD_CONST[BLOCK_COORD_OFF[b] + i]
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == 1:
                    coord_val = cursor[GEN ** 0]
                    fs = obs(fs, coord_val)
                    cursor *= GEN
                    claim_pool[GEN ** claim_idx] = coord_val
                    claim_idx += 1
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == 2:
                    rawv = cursor[GEN ** 0]
                    fs = obs(fs, rawv)
                    cursor *= GEN
                    claim_pool[GEN ** claim_idx] = rawv
                    claim_idx += 1
                    coord_val = GG * rawv
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == 3:
                    idx_chain = HeapBuf(MU_CAP + 2)
                    idx_chain[GEN ** 0] = 1
                    for xt in mul_range(1, kappa_g):
                        idx_chain[xt * GEN] = idx_chain[xt] * (1 + zeta_zs[xt] * idxc_tab[xt])  # Index-coord MLE: prod_t (1 + zeta_t * (1 + g^(2^t)))
                    coord_val = idx_chain[kappa_g]
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == 4:
                    coord_val = bytecode_vals[GEN ** bytecode_idx]
                    bytecode_idx += 1
                if s == 2:
                    inner_sum += coord_val
                else:
                    inner_sum += alpha_pow * coord_val
                    alpha_pow *= alpha
            if s == 2:
                acc += eq_hi * inner_sum
            else:
                acc += eq_hi * (gamma + inner_sum)
        acc += 1 + selector_sum
        assert acc == gkr_claims[s]

    # ---- stacked-bytecode reduction (part of the native protocol) ----
    # The bytecode is ONE multilinear polynomial in BYTECODE_LOG + 3 variables (the six
    # encoding columns stacked along three selector bits). Absorb the twelve
    # per-column values, sample three eq challenges, and reduce each point's
    # six claims to B(zeta_lo, bytecode_sel) = sum_c eq(bytecode_sel, c) * v_c.
    for k in unroll(0, N_BYTECODE_VALS):
        fs = obs(fs, bytecode_vals[GEN ** k])
    bytecode_sel = StackBuf(3)
    for t in unroll(0, 3):
        fs = squeeze(fs)
        sv = fs[0]
        bytecode_sel[t] = sv
    bytecode_reduced = StackBuf(2)
    for s in unroll(0, 2):
        wv = 0
        for c in unroll(0, 6):
            e = GEN ** 0
            for t in unroll(0, 3):
                if (c // (2 ** t)) % 2 == 1:
                    e *= bytecode_sel[t]
                else:
                    e *= (1 + bytecode_sel[t])
            wv += e * bytecode_vals[GEN ** (6 * s + c)]
        bytecode_reduced[s] = wv

    # ---- checkpoint A: sponge state matches the recorded value (debug) ----
    assert fs[0] == checkpoints[0]

    # ---- 6x per-table zerocheck (XOR, MUL, SET, DEREF, JUMP, BLAKE3) ----
    # For each table: eta, the zerocheck point r (tau samples), tau eq-trick
    # rounds (claim starts at 0), then the involved-column evaluations (pooled)
    # and the final AIR check claim == eq_acc * C_t(eta, evals).
    # RUNTIME round counts: tau_t is the certified announced log height
    # (dims_g[1 + t], certified by the count gadget). Round state threads
    # through heap chains exactly like the GKR trees.
    rho = HeapBuf(6 * TAU_CAP)
    zc_point_fs0 = HeapBuf(6 * (TAU_CAP + 2))
    zc_point_fs1 = HeapBuf(6 * (TAU_CAP + 2))
    zc_round_fs0 = HeapBuf(6 * (TAU_CAP + 2))
    zc_round_fs1 = HeapBuf(6 * (TAU_CAP + 2))
    zc_round_cursor = HeapBuf(6 * (TAU_CAP + 2))
    zc_round_claim = HeapBuf(6 * (TAU_CAP + 2))
    zc_round_eq = HeapBuf(6 * (TAU_CAP + 2))
    for t in unroll(0, 6):
        tau_g = dims_g[GEN ** (t + 1)]
        fs = squeeze(fs)
        eta = fs[0]
        # the zerocheck point r: tau squeezes, sponge chained by round.
        eq_r = HeapBuf(TAU_CAP)
        point_fs0 = zc_point_fs0 * GEN ** (t * (TAU_CAP + 2))
        point_fs1 = zc_point_fs1 * GEN ** (t * (TAU_CAP + 2))
        point_fs0[GEN ** 0] = fs[0]
        point_fs1[GEN ** 0] = fs[1]
        for xk in mul_range(1, tau_g):
            point_fs = StackBuf(2)
            point_fs[0] = point_fs0[xk]
            point_fs[1] = point_fs1[xk]
            point_fs = squeeze(point_fs)
            eq_r[xk] = point_fs[0]
            xkn = xk * GEN
            point_fs0[xkn] = point_fs[0]
            point_fs1[xkn] = point_fs[1]
        fs = StackBuf(2)
        fs[0] = point_fs0[tau_g]
        fs[1] = point_fs1[tau_g]
        # tau eq-trick rounds (claim starts at 0, eq at 1).
        round_fs0 = zc_round_fs0 * GEN ** (t * (TAU_CAP + 2))
        round_fs1 = zc_round_fs1 * GEN ** (t * (TAU_CAP + 2))
        round_cursor = zc_round_cursor * GEN ** (t * (TAU_CAP + 2))
        round_claim = zc_round_claim * GEN ** (t * (TAU_CAP + 2))
        round_eq = zc_round_eq * GEN ** (t * (TAU_CAP + 2))
        rho_t = rho * GEN ** (t * TAU_CAP)
        round_fs0[GEN ** 0] = fs[0]
        round_fs1[GEN ** 0] = fs[1]
        round_cursor[GEN ** 0] = cursor
        round_claim[GEN ** 0] = 0
        round_eq[GEN ** 0] = 1
        for xk in mul_range(1, tau_g):
            nfs0, nfs1, ncur, nclaim, neq, rk = sumcheck_round3(round_fs0[xk], round_fs1[xk], round_cursor[xk], round_claim[xk], round_eq[xk], eq_r[xk])
            rho_t[xk] = rk
            xkn = xk * GEN
            round_fs0[xkn] = nfs0
            round_fs1[xkn] = nfs1
            round_cursor[xkn] = ncur
            round_claim[xkn] = nclaim
            round_eq[xkn] = neq
        fs = StackBuf(2)
        fs[0] = round_fs0[tau_g]
        fs[1] = round_fs1[tau_g]
        cursor = round_cursor[tau_g]
        claim = round_claim[tau_g]
        eq_acc = round_eq[tau_g]
        col_evals = StackBuf(16)
        for k in unroll(0, N_AIR_COLS[t]):
            e = cursor[GEN ** 0]
            fs = obs(fs, e)
            cursor *= GEN
            col_evals[k] = e
            claim_pool[GEN ** claim_idx] = e
            claim_idx += 1
        # the table's AIR constraint at the final point (ev order = the table's
        # constraint_columns order; formulas mirror tables.rs eval_constraint).
        if t == 0:
            constraint_eval = (col_evals[4] + col_evals[0] * col_evals[1]) + eta * (col_evals[5] + col_evals[0] * col_evals[2]) + eta * eta * (col_evals[6] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[9] + col_evals[7] + col_evals[8])
        if t == 1:
            constraint_eval = (col_evals[4] + col_evals[0] * col_evals[1]) + eta * (col_evals[5] + col_evals[0] * col_evals[2]) + eta * eta * (col_evals[6] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[9] + col_evals[7] * col_evals[8])
        if t == 2:
            constraint_eval = col_evals[2] + col_evals[0] * col_evals[1]
        if t == 3:
            src = (1 + col_evals[8] + col_evals[9]) * col_evals[11] + col_evals[8] * (GG * GG * col_evals[12]) + col_evals[9] * col_evals[0]
            constraint_eval = (col_evals[4] + col_evals[0] * col_evals[1]) + eta * (col_evals[5] + col_evals[7] * col_evals[2]) + eta * eta * (col_evals[6] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[10] + src)
        if t == 4:
            ft = GG * col_evals[0]
            addrs = (col_evals[7] + col_evals[1] * col_evals[4]) + eta * (col_evals[8] + col_evals[1] * col_evals[5]) + eta * eta * (col_evals[9] + col_evals[1] * col_evals[6])
            eta3 = eta * eta * eta
            ind_def = eta3 * (col_evals[14] + col_evals[10] * col_evals[13])
            ind_nz = eta3 * eta * (col_evals[10] * (col_evals[14] + 1))
            sel_pc = eta3 * eta * eta * (col_evals[2] + col_evals[14] * col_evals[11] + (col_evals[14] + 1) * ft)
            sel_fp = eta3 * eta * eta * eta * (col_evals[3] + col_evals[14] * col_evals[12] + (col_evals[14] + 1) * col_evals[1])
            constraint_eval = addrs + ind_def + ind_nz + sel_pc + sel_fp
        if t == 5:
            constraint_eval = (col_evals[6] + col_evals[0] * col_evals[1]) + eta * (col_evals[7] + col_evals[0] * col_evals[2]) + eta * eta * (col_evals[8] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[9] + col_evals[0] * col_evals[4]) + eta * eta * eta * eta * (col_evals[10] + col_evals[0] * col_evals[5])
        assert claim == eq_acc * constraint_eval

    # ---- checkpoint B (debug: sponge-state drift guard) ----
    assert fs[0] == checkpoints[1]

    # ---- public-input binding claim: MEM(r_m, 0..) = interp(pi0, pi1, r_m) ----
    fs = squeeze(fs)
    rm = fs[0]
    pi_interp = pi_0 + rm * (pi_0 + pi_1)  # MLE of the 2-cell public memory at the sampled point rm
    claim_pool[GEN ** claim_idx] = pi_interp
    claim_idx += 1

    # ---- BLAKE3 constant-pin claims (on q_pkd, at the pin bus point) ----
    # prefix = MLE of [1;NB3, 0;...] at the pin point (the first BLAKE3
    # value-column bus claim's ζ_lo: NLOGB3 coords starting at zeta[PIN_ZETA_OFF]):
    # one eq-term per set bit of NB3, over the aligned block's high bits.
    # Telescoping over the certified count bits, low to high: adding coord
    # z_k for bit b_k maps P -> (1+z)(b + (1+b)P) + z*b*P (b = 1 fills the
    # z_k = 0 half with the all-ones MLE 1); the top bit (count == 2^tau_5
    # exactly) forces the all-ones MLE.
    bits5 = count_bits * GEN ** (33 * 5)
    zeta_pin = zeta * GEN ** PIN_ZETA_OFF
    tau5_g = dims_g[GEN ** 6]
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
        claim_pool[GEN ** claim_idx] = PIN_VALUES[pk] * prefix
        claim_idx += 1

    # ---- checkpoint C (debug: sponge-state drift guard) ----
    assert fs[0] == checkpoints[2]

    # ---- flock reduction: bind_statement ----
    # The statement digest is selected by the certified tau_5 (BLAKE3
    # log-instance-count): read row tau5_g of the baked per-candidate tables.
    sd0_tab = HeapBuf(B3TABLEN)
    sd1_tab = HeapBuf(B3TABLEN)
    for n in unroll(0, B3TABLEN):
        sd0_tab[GEN ** n] = SD0_TAB[n]
        sd1_tab[GEN ** n] = SD1_TAB[n]
    tau5_g = dims_g[GEN ** 6]
    sd0 = sd0_tab[tau5_g]
    sd1 = sd1_tab[tau5_g]
    fs = absorb(fs, 13, DS_LEN)
    fs = absorb(fs, R1CSLBL, DS_BYTE)
    fs = absorb(fs, 32, DS_LEN)
    fs = absorb(fs, sd0, DS_BYTE)
    fs = absorb(fs, sd1, DS_BYTE)
    fs = absorb(fs, 32, DS_LEN)
    fs = absorb(fs, commit_root_0, DS_BYTE)
    fs = absorb(fs, commit_root_1, DS_BYTE)

    # ---- flock zerocheck (univariate skip, k_skip = 6) ----
    fs = absorb(fs, 18, DS_LEN)
    fs = absorb(fs, ZCLBLA, DS_BYTE)
    fs = absorb(fs, ZCLBLB, DS_BYTE)
    # the full r vector: 6 sampled skips, 7 fixed inner, R1CS_M_CAP-13 sampled outer.
    zerocheck_r = HeapBuf(R1CS_M_CAP)
    for i in unroll(0, 6):
        fs = squeeze(fs)
        rv = fs[0]
        zerocheck_r[GEN ** i] = rv
    for i in unroll(0, 7):
        zerocheck_r[GEN ** (6 + i)] = INNER7[i]
    # outer samples at runtime count: R1CS_M_CAP = K_LOG + tau_5 (certified).
    mr1cs_g = dims_g[GEN ** 6] * GEN ** K_LOG
    flock_point_fs0 = HeapBuf(R1CS_M_CAP + 2)
    flock_point_fs1 = HeapBuf(R1CS_M_CAP + 2)
    flock_point_fs0[GEN ** 13] = fs[0]
    flock_point_fs1[GEN ** 13] = fs[1]
    for xi in mul_range(GEN ** 13, mr1cs_g):
        point_fs = StackBuf(2)
        point_fs[0] = flock_point_fs0[xi]
        point_fs[1] = flock_point_fs1[xi]
        point_fs = squeeze(point_fs)
        zerocheck_r[xi] = point_fs[0]
        xin = xi * GEN
        flock_point_fs0[xin] = point_fs[0]
        flock_point_fs1[xin] = point_fs[1]
    fs = StackBuf(2)
    fs[0] = flock_point_fs0[mr1cs_g]
    fs[1] = flock_point_fs1[mr1cs_g]
    # observe round-1 messages (ab then c), sample z.
    for i in unroll(0, 128):
        fs = obs(fs, zc_round1[GEN ** i])
    fs = squeeze(fs)
    zerocheck_z = fs[0]
    # interpolate P^C(z) on the Lambda domain (phi8 nodes 64..128): prefix/
    # suffix numerator products with baked inverse denominators.
    lagrange_nums = StackBuf(64)
    lag64(zerocheck_z, lagrange_nums, 64)
    c_eval = 0  # P^C(z): Lagrange-interpolate the round-1 message over the Lambda nodes
    for i in unroll(0, 64):
        c_eval += lagrange_nums[i] * ILAM[i] * zc_round1[GEN ** (64 + i)]
    # combined interpolation at z over ALL 128 phi8 nodes (Lambda values only;
    # the S half is zero by the zerocheck identity). The Lambda-node numerators
    # reuse lagrange_nums: the full-domain product only adds the S-half factor.
    s_half_product = GEN ** 0  # the S-domain half of the combined interpolation (zero by the identity)
    for i in unroll(0, 64):
        s_half_product *= (zerocheck_z + PHI[i])
    combined_eval = 0
    for i in unroll(0, 64):
        combined_eval += lagrange_nums[i] * ICMB[i] * (zc_round1[GEN ** i] + zc_round1[GEN ** (64 + i)])
    combined_eval *= s_half_product
    zc_running = combined_eval + c_eval  # the zerocheck running claim entering the multilinear rounds
    # multilinear rounds.
    zerocheck_rhos = HeapBuf(R1CS_ROUNDS_CAP)
    for i in unroll(0, 7):
        gamma_c = zc_msgs[GEN ** (2 * i)]
        g_inf = zc_msgs[GEN ** (2 * i + 1)]
        r_eq = zerocheck_r[GEN ** (6 + i)]
        gamma_ab = (zc_running + r_eq * gamma_c) * I7INV[i]  # recover the g(alpha) evaluation from g(0)+g(1)=claim and the eq weight
        fs = obs(fs, gamma_c)
        fs = obs(fs, g_inf)
        fs = squeeze(fs)
        rho_v = fs[0]
        zerocheck_rhos[GEN ** i] = rho_v
        zc_running = gamma_ab * (1 + rho_v) + gamma_c * rho_v + g_inf * rho_v * (1 + rho_v)
    # rounds 7..R1CS_ROUNDS_CAP at runtime count: R1CS_ROUNDS_CAP = K_LOG + tau_5 - 6 (certified).
    nmlv_g = dims_g[GEN ** 6] * GEN ** (K_LOG - 6)
    flock_round_fs0 = HeapBuf(R1CS_ROUNDS_CAP + 2)
    flock_round_fs1 = HeapBuf(R1CS_ROUNDS_CAP + 2)
    flock_round_running = HeapBuf(R1CS_ROUNDS_CAP + 2)
    flock_round_fs0[GEN ** 7] = fs[0]
    flock_round_fs1[GEN ** 7] = fs[1]
    flock_round_running[GEN ** 7] = zc_running
    for xi in mul_range(GEN ** 7, nmlv_g):
        round_fs = StackBuf(2)
        round_fs[0] = flock_round_fs0[xi]
        round_fs[1] = flock_round_fs1[xi]
        round_running = flock_round_running[xi]
        gamma_c = zc_msgs[xi * xi]
        g_inf = zc_msgs[xi * xi * GEN]
        r_eq = zerocheck_r[GEN ** 6 * xi]
        inv_one_plus_r = zc_invs[xi]
        inv_check = (1 + r_eq) * inv_one_plus_r
        assert inv_check == 1
        gamma_ab = (round_running + r_eq * gamma_c) * inv_one_plus_r
        round_fs = obs(round_fs, gamma_c)
        round_fs = obs(round_fs, g_inf)
        round_fs = squeeze(round_fs)
        rho_v = round_fs[0]
        zerocheck_rhos[xi] = rho_v
        round_running = gamma_ab * (1 + rho_v) + gamma_c * rho_v + g_inf * rho_v * (1 + rho_v)
        xin = xi * GEN
        flock_round_fs0[xin] = round_fs[0]
        flock_round_fs1[xin] = round_fs[1]
        flock_round_running[xin] = round_running
    fs = StackBuf(2)
    fs[0] = flock_round_fs0[nmlv_g]
    fs[1] = flock_round_fs1[nmlv_g]
    zc_running = flock_round_running[nmlv_g]
    # final: zc_running == a_eval * b_eval; observe both.
    a_eval = zc_finals[0]
    b_eval = zc_finals[1]
    ab_product = a_eval * b_eval  # zerocheck closes: running claim == a(r) * b(r)
    assert zc_running == ab_product
    fs = obs(fs, a_eval)
    fs = obs(fs, b_eval)

    # ---- flock lincheck (matrix evaluation DEFERRED) ----
    fs = absorb(fs, 17, DS_LEN)
    fs = absorb(fs, LCLBLA, DS_BYTE)
    fs = absorb(fs, LCLBLB, DS_BYTE)
    fs = squeeze(fs)
    lincheck_alpha = fs[0]
    fs = squeeze(fs)
    lincheck_beta = fs[0]
    lc_running = lincheck_alpha * a_eval + b_eval + lincheck_beta  # lincheck seed: alpha*a + b + beta (batches the two matrix claims)
    lincheck_rs = HeapBuf(LINCHECK_ROUNDS)
    for i in unroll(0, LINCHECK_ROUNDS):
        e1 = lincheck_msgs[GEN ** (2 * i)]
        ei = lincheck_msgs[GEN ** (2 * i + 1)]
        fs = obs(fs, e1)
        fs = obs(fs, ei)
        fs = squeeze(fs)
        rv = fs[0]
        lincheck_rs[GEN ** i] = rv
        e0 = lc_running + e1
        c1q = e0 + e1 + ei
        lc_running = ei * rv * rv + c1q * rv + e0  # fold the degree-2 round poly at the challenge rv
    for i in unroll(0, 64):
        fs = obs(fs, z_partial[GEN ** i])
    # final consistency: running == matpart (DEFERRED) + beta * pin term. The
    # const-pin column folds through the top-variable bindings: weight =
    # prod_j (bit_{klog-1-j}(PIN_COLUMN) ? r_j : 1+r_j), surviving z_partial index
    # = PIN_COLUMN low 6 bits.
    pin_term = lincheck_beta
    for j in unroll(0, LINCHECK_ROUNDS):
        if (PIN_COLUMN // (2 ** (K_LOG - 1 - j))) % 2 == 1:
            pin_term *= lincheck_rs[GEN ** j]
        else:
            pin_term *= (1 + lincheck_rs[GEN ** j])
    pin_term *= z_partial[GEN ** (PIN_COLUMN % 64)]
    matrix_part = matrix_eval[0]
    lincheck_final = matrix_part + pin_term  # running == deferred matrix eval + the const-pin column contribution
    assert lc_running == lincheck_final
    # fresh z_skip; w = <lagrange_S(r_inner_skip), z_partial> (phi8 nodes 0..64).
    fs = squeeze(fs)
    lincheck_z_skip = fs[0]
    skip_nums = StackBuf(64)
    lag64(lincheck_z_skip, skip_nums, 0)
    lincheck_w = 0
    for i in unroll(0, 64):
        lincheck_w += skip_nums[i] * ISDOM[i] * z_partial[GEN ** i]

    # ---- checkpoint D (debug: sponge-state drift guard) ----
    assert fs[0] == checkpoints[3]

    # ---- stacked mixed opening: ring-switch fronts + claim combination ----
    fs = absorb(fs, 23, DS_LEN)
    fs = absorb(fs, OBLBLA, DS_BYTE)
    fs = absorb(fs, OBLBLB, DS_BYTE)
    # Ring-switch claim 0 (ab): value lincheck_w, z_skip = lincheck_z_skip, x_outer[0] = lincheck_rs[LINCHECK_ROUNDS-1]
    # (x_inner_rest is the REVERSED lincheck round vector). Claim 1 (c): value
    # c_eval, z_skip = zerocheck_z, x_outer[0] = zerocheck_r[6].
    transposed_claims = StackBuf(2)
    rs_eq_vals = StackBuf(2)
    c_table = HeapBuf(128)
    z_vals = HeapBuf(2 * QPKD_VARS_CAP)
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
            claim_x_outer_0 = lincheck_rs[GEN ** (LINCHECK_ROUNDS - 1)]
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
            claim_check += lagrange_w * ((1 + claim_x_outer_0) * s_hat_v[GEN ** (128 * rs + i)] + claim_x_outer_0 * s_hat_v[GEN ** (128 * rs + 64 + i)])  # claim = sum_i lambda_i(z_skip) * eq(x_outer0, i>>6) * s_hat_v[i]
        assert claim_check == claim_val
    # ONE r'' shared by both claims (each slice was absorbed before the
    # sample), so one eq tensor and one linearized coefficient table
    # serve the whole batch.
    for i in unroll(0, 7):
        fs = squeeze(fs)
        rv = fs[0]
        r_dprime[GEN ** i] = rv
    w_eq = HeapBuf(254)
    eqtree(r_dprime, w_eq, 7)  # w = eq tensor of the 7 shared r'' coords (one batch challenge, both claims)
    # c_k = sum_i w_i * delta_pows[k][i], one runtime loop over the levels k.
    for xk in mul_range(1, GEN ** 128):
        delta_row = delta_pows * xk ** 128
        c_acc = 0
        for i in unroll(0, 128):
            c_acc += w_eq[GEN ** (126 + i)] * delta_row[GEN ** i]  # c_k = sum_i w_i * delta_i^(2^k): the linearized-poly coefficient table
        c_table[xk] = c_acc
    for rs in unroll(0, 2):
        # transposed claim T = sum_j x^j * L_w(shv_j): one runtime pass over
        # the observed values; per value the Frobenius powers evolve as a
        # scalar against the c table, and x^j chains through a heap cell.
        s_hat_row = s_hat_v * GEN ** (128 * rs)
        x_pow_chain = HeapBuf(129)
        x_pow_chain[GEN ** 0] = GEN ** 0
        t_chain = HeapBuf(129)
        t_chain[GEN ** 0] = 0
        for x_round in mul_range(1, GEN ** 128):
            x_cell = StackBuf(1)
            x_cell[0] = 2
            y_pow = s_hat_row[x_round]
            lin_eval = 0
            for k in unroll(0, 128):  # L_w(y) = sum_k c_k y^(2^k); y^(2^k) squares once per step
                lin_eval += c_table[GEN ** k] * y_pow
                y_pow *= y_pow
            t_chain[x_round * GEN] = t_chain[x_round] + x_pow_chain[x_round] * lin_eval
            x_pow_chain[x_round * GEN] = x_pow_chain[x_round] * x_cell[0]
        transposed_claims[rs] = t_chain[GEN ** 128]
        # z_vals for eval_rs_eq (the x_outer tail), used at the opening terminal.
        if rs == 0:
            for t in unroll(0, LINCHECK_ROUNDS - 1):
                z_vals[GEN ** t] = lincheck_rs[GEN ** (LINCHECK_ROUNDS - 2 - t)]
            zv_lo = z_vals * GEN ** (LINCHECK_ROUNDS - 1)
            zr_hi = zerocheck_rhos * GEN ** LINCHECK_ROUNDS
            for xt in mul_range(1, dims_g[GEN ** 6]):
                zv_lo[xt] = zr_hi[xt]
        else:
            # row 1 lives at the CAPACITY stride (QPKD_VARS_CAP); its length is the
            # runtime qpkdv.
            zv_hi = z_vals * GEN ** QPKD_VARS_CAP
            zcr7 = zerocheck_r * GEN ** 7
            for xt in mul_range(1, dims_g[GEN ** 6] * GEN ** (K_LOG - 7)):
                zv_hi[xt] = zcr7[xt]
    # gamma-combine the two transposed sumcheck claims (computed in-circuit).
    fs = squeeze(fs)
    gamma_ab = fs[0]
    fs = squeeze(fs)
    gamma_c = fs[0]
    target = gamma_ab * transposed_claims[0] + gamma_c * transposed_claims[1]  # gamma-batch the two ring-switch claims into the opening's target
    # ...then every pooled point claim, each labeled and observed.
    for j in unroll(0, NCL):
        fs = absorb(fs, 26, DS_LEN)
        fs = absorb(fs, PDLBLA, DS_BYTE)
        fs = absorb(fs, PDLBLB, DS_BYTE)
        fs = obs(fs, claim_pool[GEN ** j])
    gamma_pool = HeapBuf(NCL)
    for j in unroll(0, NCL):
        fs = squeeze(fs)
        gv = fs[0]
        gamma_pool[GEN ** j] = gv
        target += gv * claim_pool[GEN ** j]

    # ================= the Ligerito opening core (stacked, m = STACK) ========

    # ---- stacked Ligerito opening: dispatch on the committed log-size ----
    # g^m arrives as a witness hint, certified just below; the opening arm is
    # Const-specialized per candidate m.
    g_m = StackBuf(1)
    hint_witness(g_m[0:1], "annm")
    gmv = g_m[0]
    # ---- certify g^m: m = max(ceil_log2(sum_cols 2^kappa), PCS_MIN_MU) ----
    # Integer addition rides the exponent: g^total is a PRODUCT of g^(2^k)
    # factors over the committed columns (kappas from the certified
    # announced logs via the baked source map). Hinted total bits reproduce
    # g^total through the squares-of-g table, and the count-gadget tail
    # pins g^m against the reconstructed total word, with the PCS_MIN_MU floor
    # waiving minimality exactly like the per-table tau floors.
    m_bits = HeapBuf(34)
    hint_witness(m_bits[0:34], "mbits")
    m_inv = StackBuf(1)
    hint_witness(m_inv[0:1], "minv")
    g_total = GEN ** 0
    for c in unroll(0, N_COMMITTED_COLS):
        kg_c = kappa_base[GEN ** COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]
        g_total *= g_squares[kg_c]  # sum of 2^kappa over committed cols, done as a product in the exponent
    tw_psum = HeapBuf(35)
    m_word, m_exp = pin_ceil_log(m_bits, tw_psum, pow_word, g_squares, gmv, m_inv[0], PCS_MIN_MU, 34)
    assert m_exp == g_total
    sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN): the match_range arm index selecting the opening candidate
    assert log(sel) < LIG_N_CANDIDATES
    sumcheck_target, fold_challenges, final_msg, inner_total = match_range(log(sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], target, commit_root_0, commit_root_1))

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    # Per-claim lengths, selector bits, and slot data are HINTED; the final
    # identity inner_sum == sumcheck_target against the opening-bound target certifies
    # them (the P4a argument), so only range checks and booleanity are
    # level_query_sum here. All selector products use eq(b, r) = 1 + b + r.
    claim_low_len = HeapBuf(NCL)
    hint_witness(claim_low_len[0:NCL], "claim_low_len")
    claim_sel_len = HeapBuf(NCL)
    hint_witness(claim_sel_len[0:NCL], "claim_sel_len")
    claim_low_vars = HeapBuf(NCL)
    hint_witness(claim_low_vars[0:NCL], "claim_low_vars")
    claim_qpkd_slot_bits = HeapBuf(7 * NCL)
    hint_witness(claim_qpkd_slot_bits[0:7 * NCL], "claim_qpkd_slot_bits")
    claim_sel_bits = HeapBuf(33 * NCL)
    hint_witness(claim_sel_bits[0:33 * NCL], "claim_sel_bits")
    claim_overlap_mask = HeapBuf(8 * NCL)
    hint_witness(claim_overlap_mask[0:8 * NCL], "claim_overlap_mask")
    claim_yslot_bits = HeapBuf(8 * NCL)
    hint_witness(claim_yslot_bits[0:8 * NCL], "claim_yslot_bits")
    rs_yslot_bits = HeapBuf(8)
    hint_witness(rs_yslot_bits[0:8], "rs_yslot_bits")
    rs_sel_len = StackBuf(1)
    hint_witness(rs_sel_len[0:1], "rs_sel_len")
    rs_sel_bits = HeapBuf(33)
    hint_witness(rs_sel_bits[0:33], "rs_sel_bits")
    claim_weights = HeapBuf(NCL)
    for j in unroll(0, NCL):
        low_len_g = claim_low_len[GEN ** j]
        assert log(low_len_g) < 34
        low_chain = HeapBuf(35)
        if CLAIM_POINT_BUF[j] == 0:
            zptr = zeta * GEN ** CLAIM_POINT_OFF[j]
            low_chain[GEN ** 0] = 1
            for xk in mul_range(1, low_len_g):
                low_chain[xk * GEN] = low_chain[xk] * (1 + zptr[xk] + fold_challenges[xk])
        if CLAIM_POINT_BUF[j] == 1:
            rptr = rho * GEN ** CLAIM_POINT_OFF[j]
            low_chain[GEN ** 0] = 1
            for xk in mul_range(1, low_len_g):
                low_chain[xk * GEN] = low_chain[xk] * (1 + rptr[xk] + fold_challenges[xk])
        if CLAIM_POINT_BUF[j] == 2:
            low_chain[GEN ** 1] = 1 + rm + fold_challenges[GEN ** 0]
            for xk in mul_range(GEN, low_len_g):
                low_chain[xk * GEN] = low_chain[xk] * (1 + fold_challenges[xk])
        if CLAIM_POINT_BUF[j] == 3:
            qpkd_slot_eq = GEN ** 0
            for k in unroll(0, 7):
                sb3 = claim_qpkd_slot_bits[GEN ** (7 * j + k)]
                assert sb3 * sb3 == sb3
                qpkd_slot_eq *= (1 + sb3 + fold_challenges[GEN ** k])
            zptr = zeta * GEN ** CLAIM_POINT_OFF[j]
            ris7 = fold_challenges * GEN ** 7
            low_chain[GEN ** 0] = qpkd_slot_eq
            for xk in mul_range(1, low_len_g):
                low_chain[xk * GEN] = low_chain[xk] * (1 + zptr[xk] + ris7[xk])
        out_fs = low_chain[low_len_g]
        seln = claim_sel_len[GEN ** j]
        assert log(seln) < 34
        nlow = claim_low_vars[GEN ** j]
        assert log(nlow) < 40
        ris_hi = fold_challenges * nlow
        selrow = claim_sel_bits * GEN ** (33 * j)
        sel_chain = HeapBuf(35)
        sel_chain[GEN ** 0] = out_fs
        for xk in mul_range(1, seln):
            sel_bit = selrow[xk]
            assert sel_bit * sel_bit == sel_bit
            sel_chain[xk * GEN] = sel_chain[xk] * (1 + sel_bit + ris_hi[xk])
        claim_weights[GEN ** j] = sel_chain[seln] * gamma_pool[GEN ** j]
    # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
    # (the telescoped product formula; z powers evolve by squaring per k).
    # QPKD_VARS_CAP = tau_5 + (K_LOG - 7), exponent-additive from the certified
    # announced log; the per-k z-power rows chain by a runtime g^qpkdv
    # stride, and the inner passes are runtime loops with product/square
    # state chained per row.
    qpkdv_g = dims_g[GEN ** 6] * GEN ** (K_LOG - 7)
    one_plus_q = HeapBuf(GEN ** (QPKD_VARS_CAP))
    for x_round in mul_range(1, qpkdv_g):
        one_plus_q[x_round] = 1 + fold_challenges[x_round]
    for rs in unroll(0, 2):
        z_pows = HeapBuf(129 * QPKD_VARS_CAP)
        z_row_src = z_vals * GEN ** (QPKD_VARS_CAP * rs)
        for x_round in mul_range(1, qpkdv_g):
            z_pows[x_round] = z_row_src[x_round]
        e_acc = HeapBuf(129)
        e_acc[GEN ** 0] = 0
        row_ptr = HeapBuf(129)
        row_ptr[GEN ** 0] = z_pows
        for xk in mul_range(1, GEN ** 128):
            z_row = row_ptr[xk]
            z_row_next = z_row * qpkdv_g
            prod_chain = HeapBuf(GEN ** (QPKD_VARS_CAP + 1))
            prod_chain[GEN ** 0] = 1
            for x_round in mul_range(1, qpkdv_g):
                zv = z_row[x_round]
                prod_chain[x_round * GEN] = prod_chain[x_round] * (zv + one_plus_q[x_round])
                z_row_next[x_round] = zv * zv
            e_acc[xk * GEN] = e_acc[xk] + c_table[xk] * prod_chain[qpkdv_g]
            row_ptr[xk * GEN] = z_row_next
        rs_eq_vals[rs] = e_acc[GEN ** 128]
    # ring-switch weight base over the fold_challenges coords above qpkdv (hinted
    # length and selector bits, identity-certified).
    rs_weight = gamma_ab * rs_eq_vals[0] + gamma_c * rs_eq_vals[1]
    rs_len_g = rs_sel_len[0]
    assert log(rs_len_g) < 34
    ris_q = fold_challenges * qpkdv_g
    rsw_chain = HeapBuf(35)
    rsw_chain[GEN ** 0] = rs_weight
    for xk in mul_range(1, rs_len_g):
        rs_bit = rs_sel_bits[xk]
        assert rs_bit * rs_bit == rs_bit
        rsw_chain[xk * GEN] = rsw_chain[xk] * (1 + rs_bit + ris_q[xk])
    rs_weight = rsw_chain[rs_len_g]
    # inner_sum = sum_y final_msg[y] * eval_b[y]: reordered per claim. Claim j's
    # y-contribution is cw_j times the final_msg MLE at the point (overlap coords
    # || hinted slot bits): coord_k = m_k * ov_k + (1 + m_k) * bit_k with
    # hinted mask bits m_k = [k < NOVER]. Point bits beyond the shape's
    # yr_log_n are hinted zero, so the eq tensor zero-pads itself and the
    # dot over the FULL 2^YR_LOG_CAP range reads deferred zeros past final_msg's end:
    # everything unrolls at compile time. The ring-switch slot is the same
    # form with no overlaps and the hinted YRS bits.
    inner_sum = inner_total
    for j in unroll(0, NCL):
        slot_point = HeapBuf(YR_LOG_CAP)
        if CLAIM_POINT_BUF[j] == 0:
            overlap_ptr = zeta * GEN ** CLAIM_POINT_OFF[j] * claim_low_len[GEN ** j]
        else:
            overlap_ptr = rho * GEN ** CLAIM_POINT_OFF[j] * claim_low_len[GEN ** j]
        for k in unroll(0, YR_LOG_CAP):
            mask_bit = claim_overlap_mask[GEN ** (8 * j + k)]
            assert mask_bit * mask_bit == mask_bit
            slot_bit = claim_yslot_bits[GEN ** (8 * j + k)]
            assert slot_bit * slot_bit == slot_bit
            slot_point[GEN ** k] = mask_bit * overlap_ptr[GEN ** k] + (1 + mask_bit) * slot_bit
        slot_eq = HeapBuf(2 ** (YR_LOG_CAP + 1) - 2)
        eqtree(slot_point, slot_eq, YR_LOG_CAP)
        final_msg_dot = 0
        for y in unroll(0, 2 ** YR_LOG_CAP):
            final_msg_dot += final_msg[GEN ** y] * slot_eq[GEN ** (2 ** YR_LOG_CAP - 2 + y)]
        inner_sum += claim_weights[GEN ** j] * final_msg_dot
    rs_slot_point = HeapBuf(YR_LOG_CAP)
    for k in unroll(0, YR_LOG_CAP):
        yb = rs_yslot_bits[GEN ** k]
        assert yb * yb == yb
        rs_slot_point[GEN ** k] = yb
    rs_slot_eq = HeapBuf(2 ** (YR_LOG_CAP + 1) - 2)
    eqtree(rs_slot_point, rs_slot_eq, YR_LOG_CAP)
    rs_msg_dot = 0
    for y in unroll(0, 2 ** YR_LOG_CAP):
        rs_msg_dot += final_msg[GEN ** y] * rs_slot_eq[GEN ** (2 ** YR_LOG_CAP - 2 + y)]
    inner_sum += rs_weight * rs_msg_dot
    assert inner_sum == sumcheck_target


    # ---- export this sub-proof's deferred-claim data to the caller ----
    # defer_out layout: [0..2KBC) bytecode points | +0..3 bytecode_sel | +3..5 bytecode_reduced | +5 alpha
    # | +6 z_skip | +7.. zrho | +7+LINCHECK_ROUNDS.. lincheck rs | +7+2LCR.. z_partial
    # | +71+2LCR matpart.
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = zeta[GEN ** k]
        defer_out[GEN ** (BYTECODE_LOG + k)] = zeta[GEN ** (MU_CAP + k)]
    for k in unroll(0, 3):
        defer_out[GEN ** (2 * BYTECODE_LOG + k)] = bytecode_sel[k]
    defer_out[GEN ** (2 * BYTECODE_LOG + 3)] = bytecode_reduced[0]
    defer_out[GEN ** (2 * BYTECODE_LOG + 4)] = bytecode_reduced[1]
    defer_out[GEN ** (2 * BYTECODE_LOG + 5)] = lincheck_alpha
    defer_out[GEN ** (2 * BYTECODE_LOG + 6)] = zerocheck_z
    for k in unroll(0, LINCHECK_ROUNDS):
        defer_out[GEN ** (2 * BYTECODE_LOG + 7 + k)] = zerocheck_rhos[GEN ** k]
        defer_out[GEN ** (2 * BYTECODE_LOG + 7 + LINCHECK_ROUNDS + k)] = lincheck_rs[GEN ** k]
    for k in unroll(0, 64):
        defer_out[GEN ** (2 * BYTECODE_LOG + 7 + 2 * LINCHECK_ROUNDS + k)] = z_partial[GEN ** k]
    defer_out[GEN ** (2 * BYTECODE_LOG + 71 + 2 * LINCHECK_ROUNDS)] = matrix_eval[0]
    return


def main():
    # NSUB sub-proofs of the fixed inner program: verify each (verify_sub),
    # then aggregate their deferred claims. The fresh aggregation transcript
    # RLC-batches the bytecode and matrix claims through two sumchecks; only
    # the three reduced claims (evaluated natively by the outer verifier)
    # reach this guest's public input.
    sub_pis = HeapBuf(NSUB * 2)
    hint_witness(sub_pis[0:NSUB * 2], "sub_pis")
    bc_sumcheck_msgs = HeapBuf(2 * BYTECODE_VARS)
    hint_witness(bc_sumcheck_msgs[0:2 * BYTECODE_VARS], "bc_sumcheck_msgs")
    mat_sumcheck_msgs = HeapBuf(4 * K_LOG)
    hint_witness(mat_sumcheck_msgs[0:4 * K_LOG], "mat_sumcheck_msgs")
    bc_star_hint = StackBuf(1)
    hint_witness(bc_star_hint[0:1], "bc_star_hint")
    mat_stars_hint = StackBuf(2)
    hint_witness(mat_stars_hint[0:2], "mat_stars_hint")
    # The dual-basis Frobenius powers delta_pows[128k + i] = DELTA[i]^(2^k) are claim-
    # and sub-independent: build the table once, read-only afterwards.
    delta_pows = HeapBuf(128 * 128)
    for i in unroll(0, 128):
        delta_pows[GEN ** i] = DELTA[i]
    for xk in mul_range(1, GEN ** 127):
        delta_row = delta_pows * xk ** 128
        next_delta_row = delta_row * GEN ** 128
        for i in unroll(0, 128):
            delta_v = delta_row[GEN ** i]
            next_delta_row[GEN ** i] = delta_v * delta_v

    # per-sub deferred-claim regions (layout: see verify_sub's defer_out)
    defer = HeapBuf(NSUB * DEFER_SIZE)

    for sub in unroll(0, NSUB):
        verify_sub(sub_pis[GEN ** (2 * sub)], sub_pis[GEN ** (2 * sub + 1)], delta_pows, defer * GEN ** (sub * DEFER_SIZE))

    # ================= aggregation: batch the deferred claims =================
    # A fresh transcript absorbs every deferred claim (points and values),
    # samples the RLC coefficients, and verifies the two batching sumchecks of
    # doc.tex §Deferred evaluation claims. Only the reduced claims (one per
    # fixed polynomial) reach the public input.
    agg_fs = StackBuf(2)
    agg_fs[0] = 0
    agg_fs[1] = 0
    for sub in unroll(0, NSUB):
        agg_fs = obs(agg_fs, sub_pis[GEN ** (2 * sub)])
        agg_fs = obs(agg_fs, sub_pis[GEN ** (2 * sub + 1)])
        # the deferred-claim region is one contiguous run in absorb order.
        for k in unroll(0, DEFER_SIZE):
            agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFER_SIZE + k)])

    # ---- bytecode batching sumcheck (BYTECODE_VARS variables, 2*NSUB claims) ----
    gamma_bc = StackBuf(2 * NSUB)
    bc_running = 0
    for t in unroll(0, 2 * NSUB):
        agg_fs = squeeze(agg_fs)
        gv = agg_fs[0]
        gamma_bc[t] = gv
        bc_running += gv * defer[GEN ** ((t // 2) * DEFER_SIZE + 2 * BYTECODE_LOG + 3 + t % 2)]
    bc_point = HeapBuf(BYTECODE_VARS)
    for rd in unroll(0, BYTECODE_VARS):
        msg_g1 = bc_sumcheck_msgs[GEN ** (2 * rd)]
        msg_ginf = bc_sumcheck_msgs[GEN ** (2 * rd + 1)]
        agg_fs = obs(agg_fs, msg_g1)
        agg_fs = obs(agg_fs, msg_ginf)
        agg_fs = squeeze(agg_fs)
        rv = agg_fs[0]
        bc_point[GEN ** rd] = rv
        g_zero = bc_running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        bc_running = msg_ginf * rv * rv + c_one * rv + g_zero  # fold the degree-2 batching-sumcheck round at rv
    # terminal: W(r*) in-circuit; the reduced bytecode claim B(r*) is deferred.
    bc_weight = 0
    for t in unroll(0, 2 * NSUB):
        e = GEN ** 0
        for k in unroll(0, BYTECODE_LOG):
            e *= (1 + defer[GEN ** ((t // 2) * DEFER_SIZE + (t % 2) * BYTECODE_LOG + k)] + bc_point[GEN ** k])
        for k in unroll(0, 3):
            e *= (1 + defer[GEN ** ((t // 2) * DEFER_SIZE + 2 * BYTECODE_LOG + k)] + bc_point[GEN ** (BYTECODE_LOG + k)])
        bc_weight += gamma_bc[t] * e
    bytecode_star = bc_star_hint[0]
    bc_final = bytecode_star * bc_weight  # terminal: claim == B(r*) * W(r*); B(r*) (bytecode_star) is deferred
    assert bc_running == bc_final

    # ---- matrix batching sumcheck (2*K_LOG variables, NSUB weighted claims) ----
    gamma_mat = StackBuf(NSUB)
    mat_running = 0
    for t in unroll(0, NSUB):
        agg_fs = squeeze(agg_fs)
        gv = agg_fs[0]
        gamma_mat[t] = gv
        mat_running += gv * defer[GEN ** (t * DEFER_SIZE + 2 * BYTECODE_LOG + 71 + 2 * LINCHECK_ROUNDS)]
    mat_point = HeapBuf(2 * K_LOG)
    for rd in unroll(0, 2 * K_LOG):
        msg_g1 = mat_sumcheck_msgs[GEN ** (2 * rd)]
        msg_ginf = mat_sumcheck_msgs[GEN ** (2 * rd + 1)]
        agg_fs = obs(agg_fs, msg_g1)
        agg_fs = obs(agg_fs, msg_ginf)
        agg_fs = squeeze(agg_fs)
        rv = agg_fs[0]
        mat_point[GEN ** rd] = rv
        g_zero = mat_running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        mat_running = msg_ginf * rv * rv + c_one * rv + g_zero
    # terminal weights: U_t(r*) = urow_t(r*_row) * wcol_t(r*_col), with
    # row_weight = (sum_i L_i(zz_t) eq(r*[0..6], i)) * eq(zrho_t, r*[6..K_LOG]) and
    # col_weight = (sum_i z_partial_t[i] eq(r*[K_LOG..K_LOG+6], i)) * prod_j (1 + lrr_j
    # + r*[2*K_LOG-1-j]) (the lincheck binds column variables top-down).
    eq_rows = HeapBuf(126)
    eqtree(mat_point, eq_rows, 6)
    eq_cols = HeapBuf(126)
    eqtree(mat_point * GEN ** K_LOG, eq_cols, 6)
    weight_a = 0
    weight_b = 0
    for t in unroll(0, NSUB):
        z_skip_t = defer[GEN ** (t * DEFER_SIZE + 2 * BYTECODE_LOG + 6)]
        row_nums = StackBuf(64)
        lag64(z_skip_t, row_nums, 0)
        row_weight = 0
        for i in unroll(0, 64):
            row_weight += row_nums[i] * ISDOM[i] * eq_rows[GEN ** (62 + i)]
        for k in unroll(0, LINCHECK_ROUNDS):
            row_weight *= (1 + defer[GEN ** (t * DEFER_SIZE + 2 * BYTECODE_LOG + 7 + k)] + mat_point[GEN ** (6 + k)])
        col_weight = 0
        for i in unroll(0, 64):
            col_weight += defer[GEN ** (t * DEFER_SIZE + 2 * BYTECODE_LOG + 7 + 2 * LINCHECK_ROUNDS + i)] * eq_cols[GEN ** (62 + i)]
        for j in unroll(0, LINCHECK_ROUNDS):
            col_weight *= (1 + defer[GEN ** (t * DEFER_SIZE + 2 * BYTECODE_LOG + 7 + LINCHECK_ROUNDS + j)] + mat_point[GEN ** (2 * K_LOG - 1 - j)])
        weight_u = row_weight * col_weight
        weight_a += gamma_mat[t] * defer[GEN ** (t * DEFER_SIZE + 2 * BYTECODE_LOG + 5)] * weight_u
        weight_b += gamma_mat[t] * weight_u
    a_star = mat_stars_hint[0]
    b_star = mat_stars_hint[1]
    mat_final = a_star * weight_a + b_star * weight_b
    assert mat_running == mat_final

    # ---- bind the sub statements + the reduced claims to the public input ----
    out_fs = StackBuf(2)
    out_fs[0] = 0
    out_fs[1] = 0
    for sub in unroll(0, NSUB):
        out_fs = obs(out_fs, sub_pis[GEN ** (2 * sub)])
        out_fs = obs(out_fs, sub_pis[GEN ** (2 * sub + 1)])
    for k in unroll(0, BYTECODE_VARS):
        out_fs = obs(out_fs, bc_point[GEN ** k])
    out_fs = obs(out_fs, bytecode_star)
    for k in unroll(0, 2 * K_LOG):
        out_fs = obs(out_fs, mat_point[GEN ** k])
    out_fs = obs(out_fs, a_star)
    out_fs = obs(out_fs, b_star)
    pub_ptr = GEN ** 0
    own_pi_0 = pub_ptr[1]
    own_pi_1 = pub_ptr[GEN]
    out_word_0 = out_fs[0]
    out_word_1 = out_fs[1]
    assert own_pi_0 == out_word_0  # the guest's OWN public input == blake3 of (sub statements | reduced claims)
    assert own_pi_1 == out_word_1
    return
