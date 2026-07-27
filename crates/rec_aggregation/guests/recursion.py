# CREDIT: The Jagged PCS branching-program evaluator is adapted from Succinct
# Labs SP1's `slop/crates/jagged` implementation (MIT OR Apache-2.0):
# https://github.com/succinctlabs/sp1
from snark_lib import *

# The proof stream rides ONE padded witness hint (the guest walks only the
# prefix the shape dictates); binding always comes from the per-word absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
# Per-table tau floor: BLAKE3 is sized to flock's instance count (>= 2^3).
FLOORS = [0, 0, 0, 0, 0, 3]
INV_GEN = INV_GEN_PLACEHOLDER
LAGRANGE_INV_0 = LAGRANGE_INV_0_PLACEHOLDER
LAGRANGE_INV_1 = LAGRANGE_INV_1_PLACEHOLDER
LAGRANGE_INV_2 = LAGRANGE_INV_2_PLACEHOLDER

# GKR sides. The layer counts mu_s are hinted and certified from the block
# kappas.
PUSH_SIDE = 0
PULL_SIDE = 1
COUNT_SIDE = 2
N_GKR_SIDES = 3
# GKR runtime-loop chain capacities: per-tree round positions (triangle
# rounds plus one slot per layer) and the point triangle (rows x MU_CAP).
GKR_ROUNDS_CAP = GKR_ROUNDS_CAP_PLACEHOLDER
MU_CAP = MU_CAP_PLACEHOLDER
GKR_POINTS_CAP = GKR_POINTS_CAP_PLACEHOLDER
# The bus PoW window is g^(push.mu - BUS_GRIND_SHIFT), BUS_GRIND_SHIFT =
# 126 - SECURITY_BITS (see leaf::grand_product_grinding_bits).
BUS_GRIND_SHIFT = BUS_GRIND_SHIFT_PLACEHOLDER

# Bus blocks, flattened across the 3 sides (side s covers blocks
# [SIDE_BLOCK_START[s], SIDE_BLOCK_START[s+1])). The block STRUCTURE is
# protocol-fixed and baked: each block's coord range [BLOCK_COORD_OFF,
# +BLOCK_COORD_COUNT), per coord COORD_TYPE (0=const, 1=col, 2=gcol, 3=index,
# 4=public bytecode; named COORD_KIND_* below), COORD_CONST (the const value,
# else 0), and the kappa SOURCE map
# (BLOCK_KAPPA_SRC/ADJ: 0=const adj, 1=log_mem, 2+t=tau_t). The block SHAPES
# are all reconstructed at runtime from the certified logs: the logical kappa
# and the exact number of real rows.
# Coord kinds (COORD_TYPE codes, mirroring leaf.rs::Coord):
COORD_KIND_CONST = 0
COORD_KIND_COL = 1
COORD_KIND_GCOL = 2
COORD_KIND_INDEX = 3
COORD_KIND_PUBLIC = 4
# BLOCK_REAL_TABLE: the table whose count is the block's real row count,
# a full structural cube, the used-memory prefix, or the public bytecode prefix.
REAL_IS_FULL_CUBE = 6
REAL_IS_MEMORY_PREFIX = 7
REAL_IS_BYTECODE_PREFIX = 8
SIDE_BLOCK_START = SIDE_BLOCK_START_PLACEHOLDER
N_BLOCKS = N_BLOCKS_PLACEHOLDER
BLOCK_KAPPA_SRC = BLOCK_KAPPA_SRC_PLACEHOLDER
BLOCK_KAPPA_ADJ = BLOCK_KAPPA_ADJ_PLACEHOLDER
BLOCK_REAL_TABLE = BLOCK_REAL_TABLE_PLACEHOLDER
BLOCK_HAS_COMMITTED = BLOCK_HAS_COMMITTED_PLACEHOLDER
N_HEIGHT_GROUPS = N_HEIGHT_GROUPS_PLACEHOLDER
BLOCK_HEIGHT_GROUP = BLOCK_HEIGHT_GROUP_PLACEHOLDER
HEIGHT_GROUP_KIND = HEIGHT_GROUP_KIND_PLACEHOLDER
HEIGHT_GROUP_KAPPA_SRC = HEIGHT_GROUP_KAPPA_SRC_PLACEHOLDER
HEIGHT_GROUP_KAPPA_ADJ = HEIGHT_GROUP_KAPPA_ADJ_PLACEHOLDER
BLOCK_COORD_OFF = BLOCK_COORD_OFF_PLACEHOLDER
BLOCK_COORD_COUNT = BLOCK_COORD_COUNT_PLACEHOLDER
COORD_TYPE = COORD_TYPE_PLACEHOLDER
COORD_CONST = COORD_CONST_PLACEHOLDER
# The tight-layout reduction deduplicates committed columns at a shared row
# point; the first occurrence of each (column, kappa) receives one pool slot.
COORD_FRESH = COORD_FRESH_PLACEHOLDER
COORD_CLAIM_SLOT = COORD_CLAIM_SLOT_PLACEHOLDER
N_BUS_CLAIMS = N_BUS_CLAIMS_PLACEHOLDER
# index_mle factor constants: INDEX_MLE_FACTORS[i] = 1 + g^(2^i).
INDEX_MLE_FACTORS = INDEX_MLE_FACTORS_PLACEHOLDER
# Committed-coordinate claims (Col/GCol coords across all sides) and the
# deferred bytecode values (Public coords).
N_CLAIMS = N_CLAIMS_PLACEHOLDER
# The stacked bytecode: BYTECODE_COLS encoding columns, stacked along
# LOG2_BYTECODE_COLS selector bits into ONE multilinear. Push and pull share
# their GKR point, so the columns are opened ONCE (BYTECODE_COLS values).
BYTECODE_COLS = BYTECODE_COLS_PLACEHOLDER
LOG2_BYTECODE_COLS = LOG2_BYTECODE_COLS_PLACEHOLDER
# Zerochecks: per-table constraint-column counts (round counts are the
# certified tau_t); AIR_COLS_CAP caps the evaluation frame.
N_AIR_COLS = N_AIR_COLS_PLACEHOLDER
AIR_COLS_CAP = AIR_COLS_CAP_PLACEHOLDER
TAU_CAP = TAU_CAP_PLACEHOLDER
# The instruction tables, in schema order:
TABLE_XOR = 0
TABLE_MUL = 1
TABLE_SET = 2
TABLE_DEREF = 3
TABLE_JUMP = 4
TABLE_BLAKE3 = 5
N_TABLES = N_TABLES_PLACEHOLDER
MIN_LOG_MEM = MIN_LOG_MEM_PLACEHOLDER
# Phase D (flock reduction): the seven fixed inner challenges (+ inverses of 1+c),
# the phi8 node table + baked Lagrange inverse denominators (Lambda domain,
# combined domain, S domain). The zerocheck point/round buffers are sized at
# runtime in the exponent (m = K_LOG + tau_5 and m - 6, both certified);
# LINCHECK_ROUNDS = k_log - k_skip is protocol-fixed, PIN_COLUMN the
# const-pin column.
# Flock univariate skip: K_SKIP variables fold in one skip round (half-domain
# 2^K_SKIP nodes), then N_FIXED_CHALLENGE_ROUNDS fixed inner rounds (FIXED_CHALLENGES).
K_SKIP = K_SKIP_PLACEHOLDER
N_FIXED_CHALLENGE_ROUNDS = N_FIXED_CHALLENGE_ROUNDS_PLACEHOLDER
FIXED_CHALLENGES = FIXED_CHALLENGES_PLACEHOLDER
ONE_PLUS_CHALLENGE_INV = ONE_PLUS_CHALLENGE_INV_PLACEHOLDER
PHI8_NODES = PHI8_NODES_PLACEHOLDER
LAGRANGE_INV_LAMBDA = LAGRANGE_INV_LAMBDA_PLACEHOLDER
LAGRANGE_INV_COMBINED = LAGRANGE_INV_COMBINED_PLACEHOLDER
LAGRANGE_INV_S = LAGRANGE_INV_S_PLACEHOLDER
LINCHECK_ROUNDS = LINCHECK_ROUNDS_PLACEHOLDER
PIN_COLUMN = PIN_COLUMN_PLACEHOLDER
K_LOG = K_LOG_PLACEHOLDER
# Phase E: the dense Jagged opening, with q_pkd retained as an aligned prefix.
# The two ring-switch fronts (claim check, tensor transpose, and eval_rs_eq all
# in-circuit), followed by the
# gamma-combination of the two ring-switch claims and the N_CLAIMS pool claims.
# Phase E2: the Ligerito opening over the dense commitment, dispatched by
# the certified committed log-size m through match_range: the LIG_* tables
# below carry one row per candidate m in [LIG_MIN_LOG_SIZE, +LIG_N_CANDIDATES),
# emitted from the SAME derive_profile/level_shapes the prover uses.
# Scalars index as TBL[m_idx]; per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl];
# per-fold grind schedules with the LIG_MAX_TOTAL_FOLDS stride; the subspace
# vanishing constants with the LIG_MAX_VANISH_LEN stride. The eval_b terminal
# claim descriptors bake the point source, dense column, fixed padding, and
# q_pkd slot. Runtime dimensions and intervals are derived from public counts.
# Opening dispatch: baked committed log-size, candidate range, g^-LIG_MIN_LOG_SIZE.
LIG_MIN_LOG_SIZE = LIG_MIN_LOG_SIZE_PLACEHOLDER
# Committed-column real-height sources, in dense Jagged order: KIND 0 is the
# full cube 2^(kappa_base[SRC] + ADJ), KIND 1 an announced table row count,
# KIND 2 the announced used-memory prefix, and KIND 3 the program-bound
# bytecode prefix. Their width-adjusted sum determines the packed area.
N_COMMITTED_COLS = N_COMMITTED_COLS_PLACEHOLDER
COL_HEIGHT_KIND = COL_HEIGHT_KIND_PLACEHOLDER
COL_HEIGHT_SRC = COL_HEIGHT_SRC_PLACEHOLDER
COL_HEIGHT_ADJ = COL_HEIGHT_ADJ_PLACEHOLDER
COL_BLOCK_LOG = COL_BLOCK_LOG_PLACEHOLDER
BYTECODE_USED_BITS = BYTECODE_USED_BITS_PLACEHOLDER
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
LIG_FOLD_GRIND_LEN = LIG_FOLD_GRIND_LEN_PLACEHOLDER
LIG_QUERY_GRIND_BITS = LIG_QUERY_GRIND_BITS_PLACEHOLDER
LIG_QUERIES = LIG_QUERIES_PLACEHOLDER
LIG_FOLDS = LIG_FOLDS_PLACEHOLDER
LIG_INTERLEAVE = LIG_INTERLEAVE_PLACEHOLDER
LIG_LEAF_PAIRS = LIG_LEAF_PAIRS_PLACEHOLDER
LIG_LEAF_BLOCKS = LIG_LEAF_BLOCKS_PLACEHOLDER
LIG_TREE_DEPTH = LIG_TREE_DEPTH_PLACEHOLDER
LIG_SQUEEZES = LIG_SQUEEZES_PLACEHOLDER
LIG_POSITIONS_OFF = LIG_POSITIONS_OFF_PLACEHOLDER
LIG_LOG_QUERIES = LIG_LOG_QUERIES_PLACEHOLDER
LIG_LOG_MSG_COLS = LIG_LOG_MSG_COLS_PLACEHOLDER
LIG_RESIDUAL_FOLD_OFF = LIG_RESIDUAL_FOLD_OFF_PLACEHOLDER
LIG_RESIDUAL_PREFIX_LEN = LIG_RESIDUAL_PREFIX_LEN_PLACEHOLDER
LIG_FOLDS_OFF = LIG_FOLDS_OFF_PLACEHOLDER
LIG_ROWS_OFF = LIG_ROWS_OFF_PLACEHOLDER
LIG_PATHS_OFF = LIG_PATHS_OFF_PLACEHOLDER
LIG_VANISH_OFF = LIG_VANISH_OFF_PLACEHOLDER
LIG_FOLD_GRIND_BITS = LIG_FOLD_GRIND_BITS_PLACEHOLDER
LIG_VANISH_VALS = LIG_VANISH_VALS_PLACEHOLDER
LIG_VANISH_INVS = LIG_VANISH_INVS_PLACEHOLDER
LIG_N_CANDIDATES = LIG_N_CANDIDATES_PLACEHOLDER
LIG_MIN_SHIFT_INV = LIG_MIN_SHIFT_INV_PLACEHOLDER
# eval_b claim descriptors (fixed parts) + the qpkd capacity stride.
# Which point buffer a pooled claim's x-part lives in (CLAIM_POINT_BUF codes):
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QPKD = 3
POINT_BUF_BUS_RHO = 4
POINT_BUF_QPKD_BUS_RHO = 5
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_POINT_OFF = CLAIM_POINT_OFF_PLACEHOLDER
# Dense Jagged column index and fixed public pad value for each pooled claim.
CLAIM_COL = CLAIM_COL_PLACEHOLDER
CLAIM_PAD = CLAIM_PAD_PLACEHOLDER
CLAIM_QPKD_SLOT = CLAIM_QPKD_SLOT_PLACEHOLDER
CLAIM_BLOCK_SLOT = CLAIM_BLOCK_SLOT_PLACEHOLDER
CLAIM_BLOCK_LOG = CLAIM_BLOCK_LOG_PLACEHOLDER
CLAIM_GAMMA_RANK = CLAIM_GAMMA_RANK_PLACEHOLDER
N_CLAIM_ROWS = N_CLAIM_ROWS_PLACEHOLDER
CLAIM_ROW_GROUP = CLAIM_ROW_GROUP_PLACEHOLDER
CLAIM_ROW_REP = CLAIM_ROW_REP_PLACEHOLDER
N_PAD_PREFIXES = N_PAD_PREFIXES_PLACEHOLDER
PAD_PREFIX_ROW = PAD_PREFIX_ROW_PLACEHOLDER
PAD_PREFIX_COL = PAD_PREFIX_COL_PLACEHOLDER
CLAIM_PAD_PREFIX = CLAIM_PAD_PREFIX_PLACEHOLDER
N_JAGGED_BATCHES = N_JAGGED_BATCHES_PLACEHOLDER
JAGGED_BATCH_REP = JAGGED_BATCH_REP_PLACEHOLDER
JAGGED_BATCH_ROW = JAGGED_BATCH_ROW_PLACEHOLDER
JAGGED_BATCH_COL = JAGGED_BATCH_COL_PLACEHOLDER
JAGGED_BATCH_LOG = JAGGED_BATCH_LOG_PLACEHOLDER
JAGGED_BATCH_BASE = JAGGED_BATCH_BASE_PLACEHOLDER
QPKD_VARS_CAP = QPKD_VARS_CAP_PLACEHOLDER
# Ring-switch coefficient factorization for the GHASH power basis. Each
# 15-value row contains d^(-2^k)*x^(127*2^k), then
# 1+x^(-2^(k+t)) for t=0..6, then d^(-2^k)*epsilon_i^(2^k) for i=0..6.
RS_COEFF_ORBIT_WIDTH = 15
RS_COEFF_ORBITS = RS_COEFF_ORBITS_PLACEHOLDER
# Phase F: log rows of the bytecode blocks (the deferred bytecode points).
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER
# One sub-proof's deferred-claim region: 2*BYTECODE_LOG + LOG2_BYTECODE_COLS
# + 2*LINCHECK_ROUNDS + 69 words (see verify_sub's defer_out layout).
DEFER_SIZE = DEFER_SIZE_PLACEHOLDER
# Aggregation: NSUB sub-proofs of the same program; per-sub proof data arrives
# as hints. The seed sponge state after the two byte-string absorbs is baked
# (TRANSCRIPT_SEED), then the hinted sub statement + the inner PROGRAM DIGEST are bound.
# The seed is NOT baked into the guest: it rides the recursion's PUBLIC INPUT
# (the fs_seed hint folded into own_pi in main), so ONE compiled guest verifies
# proofs of any inner program of this VM — the outer statement fixes the whole
# proving environment (circuit family + program), via own_pi.
NSUB = NSUB_PLACEHOLDER
BYTECODE_VARS = BYTECODE_VARS_PLACEHOLDER
TRANSCRIPT_SEED_0 = TRANSCRIPT_SEED_0_PLACEHOLDER
TRANSCRIPT_SEED_1 = TRANSCRIPT_SEED_1_PLACEHOLDER

DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQ = 4
DS_POW = 5

# Field structure: GF(2^128). Its 128 bits pack into LOG2_FIELD_BITS = 7
# ring-switch coordinates (the q_pkd slot length, r'' length).
FIELD_BITS = 128
LOG2_FIELD_BITS = 7
# Exponent bit-widths: an announced 32-bit count decomposes into COUNT_BITS
# bits (count == 2^32 tops); any structural size (sums of 2^kappa, packing
# offsets) fits SIZE_BITS bits.
COUNT_BITS = 33
SIZE_BITS = 34


def squeeze_step(state_0, state_1):
    # Non-inlined sponge ratchet exposing BOTH output words (challenge and the
    # next state), so a query-squeeze loop can chain the state through a heap
    # buffer. Returns (challenge, next_state_0, next_state_1).
    a = [state_0, state_1]
    b = [0, DS_SQ]
    o = StackBuf(2)
    blake3(a, b, o)
    return o[0], o[0], o[1]


def check_128_bits_decomposition(bits_ptr, v):
    # Boolean-constrain FIELD_BITS hinted bits and assert they reconstruct v.
    acc = 0
    for i in unroll(0, FIELD_BITS):
        b = bits_ptr[GEN ** i]
        assert b * b == b
        acc += b * GEN ** i  # accumulate the g-power encoding: bit i contributes g^i
    assert acc == v
    return


def decode_query_bits(v, positions_out, bit_ptrs_out, depth: Const):
    # The squeezed word's bits are advice-decomposed HERE, boolean-constrained,
    # and tied back by reconstruction; each depth-bit group also becomes a query
    # position (little-endian), with a pointer to its bit run (the Merkle
    # direction bits). Each 128-bit word packs FIELD_BITS // depth positions.
    per_word = FIELD_BITS // depth
    bits_ptr = HeapBuf(GEN ** FIELD_BITS)
    hint_decompose_bits(bits_ptr, v, FIELD_BITS)
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
    for i in unroll(per_word * depth, FIELD_BITS):
        t = bits_ptr[GEN ** i]
        sq = t * t
        assert sq == t
        acc += t * GEN ** i
    assert acc == v
    return


def grind_check(state_0, state_1, nonce, nbits_g):
    # The one grinding check, shared by the bus grind and the Ligerito fold /
    # query grinds: digest = H(H(state, (0, POW)), (nonce, POW)); the digest's
    # bits are advice-decomposed HERE and verified (booleanity + reconstruction,
    # check_128_bits_decomposition), and the low nbits (nbits_g = g^nbits) must
    # be zero — the CONTIGUOUS PoW window of transcript::pow_bits_ok. The
    # caller absorbs the nonce afterwards.
    st = [state_0, state_1]
    tag = [0, DS_POW]
    base = StackBuf(2)
    blake3(st, tag, base)
    nz = [nonce, DS_POW]
    out = StackBuf(2)
    blake3(base, nz, out)
    digest_bits = HeapBuf(GEN ** FIELD_BITS)
    hint_decompose_bits(digest_bits, out[0], FIELD_BITS)
    check_128_bits_decomposition(digest_bits, out[0])
    for xb in mul_range(1, nbits_g):
        assert digest_bits[xb] == 0
    return


def verify_log2_ceil(bits_buf, g_logs_pow2, g_squares, floor: Const, nbits: Const, need_exp: Const):
    # Given `nbits` bits already in bits_buf, return (g_log, word, exp_prod):
    # word = Σ bit_j 2^j, exp_prod = g^word, g_log = g^max(log2_ceil(word), floor).
    # g_log is prover advice, pinned to log2_ceil(word) by psum[g_log] == word
    # (word < 2^log; the == 2^log case via g_logs_pow2) and word > 2^(log-1)
    # (waived at floor). Callers fill the bits (hint_decompose_bits / hint_decompose_bits_exponent)
    # and tie word or exp_prod to their value. NB: log2 here is base-2 log of the
    # integer word, not the discrete log base g that `log(...)` means.
    psum_buf = HeapBuf(GEN ** (nbits + 1))  # psum_buf[g^j] = value of bits [0, j)
    psum_buf[GEN ** 0] = 0
    word = 0
    exp_prod = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits_buf[GEN ** j]
        assert bit * bit == bit
        if need_exp == 1:
            exp_prod *= (1 + bit * (g_squares[GEN ** j] + 1))
        word += bit * (2 ** j)
        psum_buf[GEN ** (j + 1)] = word
    g_log = hint_log2_ceil(bits_buf, nbits, floor)  # prover advice; verified below
    assert log(g_log) < SIZE_BITS
    low_bits = psum_buf[g_log]                 # value of bits [0, log)
    high_bits = low_bits + word                # value of bits [log, nbits)
    word_vs_2log = word + g_logs_pow2[g_log]    # 0 iff word == 2^log
    assert high_bits * low_bits == 0     # word < 2^log (high bits clear) OR word == 2^log
    assert high_bits * word_vs_2log == 0  # ...the second factor pins the word == 2^log branch
    if g_log != GEN ** floor:
        # minimality (word > 2^(log-1)); skip at g_log == g^0 (word is in {0,1},
        # its ceil-log 0 is already minimal, and psum_buf[g^-1] is out of range).
        if g_log != GEN ** 0:
            low_bits_prev = psum_buf[g_log * INV_GEN]              # bits [0, log-1)
            high_bits_prev = low_bits_prev + word               # bits [log-1, nbits)
            word_vs_2logprev = word + g_logs_pow2[g_log * INV_GEN]  # 0 iff word == 2^(log-1)
            assert high_bits_prev * word_vs_2logprev != 0  # word > 2^(log-1): minimal
    return g_log, word, exp_prod


def log2_ceil_word(value, bits, g_logs_pow2, g_squares, floor: Const, nbits: Const, need_exp: Const):
    # g^log2_ceil(value) for a concrete integer `value`. The bits are hinted HERE
    # into caller-owned storage (so later phases can reuse them), then tied back
    # to `value`. Returns (g_log, g^value).
    hint_decompose_bits(bits, value, nbits)
    g_log, word, g_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits, need_exp)
    assert word == value  # the hinted bits are exactly value's bits (so value < 2^nbits)
    return g_log, g_value


def log2_ceil_in_the_exponent(g_N, g_logs_pow2, g_squares, floor: Const, nbits: Const):
    # Return g^log2_ceil(N) given g_N = g^N (N < 2^nbits). There is no in-circuit
    # log, so the prover hints N's bits (hint_decompose_bits_exponent); they are
    # verified and tied back: g^(the value the bits decode to) must equal g_N.
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits_exponent(bits, g_N, nbits)
    g_log, word, g_bits_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits, 1)
    assert g_bits_value == g_N  # the hinted bits decode to N
    return g_log


def verify_merkle_path(leaf_0, leaf_1, path_ptr, direction_bits, depth: Const):
    node_0 = leaf_0
    node_1 = leaf_1
    for level in unroll(0, depth):
        sibling_0 = path_ptr[GEN ** (2 * level)]
        sibling_1 = path_ptr[GEN ** (2 * level + 1)]
        dir_bit = direction_bits[GEN ** level]  # query index bit: 0 keeps the running node left, 1 swaps it right
        diff_0 = node_0 + sibling_0
        diff_1 = node_1 + sibling_1
        left = [node_0 + dir_bit * diff_0, node_1 + dir_bit * diff_1]
        right = [diff_0 + left[0], diff_1 + left[1]]
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
    fs = [state_0, state_1]
    fs, m0, msg_cursor = fs_next(fs, msg_cursor)
    fs, m1, msg_cursor = fs_next(fs, msg_cursor)
    fs, m2, msg_cursor = fs_next(fs, msg_cursor)
    lhs = eq_acc * ((1 + prev_challenge) * m0 + prev_challenge * m1)
    assert lhs == claim
    fs = squeeze(fs)
    round_challenge = fs[0]
    new_eq = eq_acc * (1 + prev_challenge + round_challenge)
    l0 = (round_challenge + 1) * (round_challenge + GEN) * LAGRANGE_INV_0
    l1 = round_challenge * (round_challenge + GEN) * LAGRANGE_INV_1
    l2 = round_challenge * (round_challenge + 1) * LAGRANGE_INV_2
    new_claim = new_eq * (m0 * l0 + m1 * l1 + m2 * l2)
    return fs[0], fs[1], msg_cursor, new_claim, new_eq, round_challenge


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
def obs(state, x):
    # Bind one scalar into the sponge chain: state <- compress(state, (x, SCALAR)).
    # Returns the successor StackBuf; the call site aliases it (zero copies).
    tg = [x, DS_SCALAR]
    nb = StackBuf(2)
    blake3(state, tg, nb)
    return nb


@inline
def fs_next(state, cursor):
    # Fetch + observe + advance, in one act: read the word under `cursor`, fold it
    # into the sponge, and hand back the successor state, the word, AND the cursor
    # stepped one word on. Reading and absorbing are inseparable here, so no
    # proof-stream word can enter the computation unbound — the soundness invariant
    # the whole guest rests on. All three returns alias into the caller at zero
    # cost (state a StackBuf run, cursor a folded g-address), so the usual walk is
    # just `fs, x, cursor = fs_next(fs, cursor)` with no manual cursor arithmetic.
    x = cursor[GEN ** 0]
    tg = [x, DS_SCALAR]
    nb = StackBuf(2)
    blake3(state, tg, nb)
    return nb, x, cursor * GEN


@inline
def absorb(state, x, tag):
    # Tagged absorb (length frames, byte words, grinding nonces).
    tg = [x, tag]
    nb = StackBuf(2)
    blake3(state, tg, nb)
    return nb


@inline
def squeeze(state):
    # Ratchet: the compress output is the new state; word 0 is the challenge.
    zt = [0, DS_SQ]
    nb = StackBuf(2)
    blake3(state, zt, nb)
    return nb


@inline
def lag64(z, out, node_base: Const):
    # The 64 phi8-domain Lagrange NUMERATORS at z, nodes PHI8_NODES[node_base..node_base+64]:
    # out[i] = prod_{j != i} (z + PHI8_NODES[node_base + j]). Callers multiply by their
    # baked inverse-denominator table (LAGRANGE_INV_S / LAGRANGE_INV_LAMBDA / LAGRANGE_INV_COMBINED).
    pre = StackBuf(65)
    pre[0] = 1
    for i in unroll(0, 64):
        pre[i + 1] = pre[i] * (z + PHI8_NODES[node_base + i])
    suf = StackBuf(65)
    suf[64] = 1
    for i in unroll(0, 64):
        suf[63 - i] = suf[64 - i] * (z + PHI8_NODES[node_base + 63 - i])
    for i in unroll(0, 64):
        out[i] = pre[i] * suf[i + 1]
    return


@inline
def eq_weight(ch, count: Const, idx: Const, msb_span: Const):
    # The eq-tensor weight of compile-time index `idx` against the challenge
    # run ch[0..count): prod_c eq(bit(idx), ch[c]), where the bit is bit c of
    # idx (msb_span == 0) or bit (msb_span - 1 - c) (MSB-first walk over an
    # msb_span-bit index).
    w = GEN ** 0
    for c in unroll(0, count):
        cv = ch[GEN ** c]
        if msb_span == 0:
            if (idx // (2 ** c)) % 2 == 1:
                w *= cv
            else:
                w *= (1 + cv)
        else:
            if (idx // (2 ** (msb_span - 1 - c))) % 2 == 1:
                w *= cv
            else:
                w *= (1 + cv)
    return w


@inline
def point_weight_fixed(point, bits, nbits: Const):
    weight = GEN ** 0
    for bit in unroll(0, nbits):
        weight *= 1 + point[GEN ** bit] + bits[GEN ** bit]
    return weight


@inline
def offset_step_fixed(current_bits, height_bits, next_bits, start_point, start_nbits: Const):
    weight = GEN ** 0
    carry = 0
    for bit in unroll(0, start_nbits):
        a = current_bits[GEN ** bit]
        b = height_bits[GEN ** bit]
        weight *= 1 + start_point[GEN ** bit] + a
        xor_ab = a + b
        next_bits[GEN ** bit] = xor_ab + carry
        carry = a * b + carry * xor_ab
    assert carry == 0
    return weight


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


def prefix_indicator(point, height_bits):
    # MLE of [row < height], MSB first. `point` is zero above the logical
    # column dimension and `height_bits` may therefore also encode the full
    # power-of-two height.
    states = StackBuf(2 * (SIZE_BITS + 1))
    states[0] = 0  # already less
    states[1] = 1  # equal so far
    for rev in unroll(0, SIZE_BITS):
        bit = SIZE_BITS - 1 - rev
        less = states[2 * rev]
        equal = states[2 * rev + 1]
        x = point[GEN ** bit]
        h = height_bits[GEN ** bit]
        equal_zero = equal * (1 + x)
        states[2 * (rev + 1)] = less + h * equal_zero
        states[2 * (rev + 1) + 1] = equal * (1 + h + x)
    return states[2 * SIZE_BITS]


def prefix_indicator_fixed(point, height_bits, nbits: Const):
    # Prefix MLE on an nbits-coordinate cube. One fixed-zero top coordinate
    # represents the exact-full endpoint 2^nbits.
    states = StackBuf(2 * (SIZE_BITS + 2))
    states[0] = 0
    states[1] = 1
    for rev in unroll(0, nbits + 1):
        bit = nbits - rev
        less = states[2 * rev]
        equal = states[2 * rev + 1]
        if bit == nbits:
            x = 0
        else:
            x = point[GEN ** bit]
        h = height_bits[GEN ** bit]
        equal_zero = equal * (1 + x)
        states[2 * (rev + 1)] = less + h * equal_zero
        states[2 * (rev + 1) + 1] = equal * (1 + h + x)
    return states[2 * (nbits + 1)]


def prefix_geometric(point, height_bits, geometric_powers):
    # Σ_{i<height} G^i eq(point,i), evaluated MSB first with the same
    # less/equal digit DP as prefix_indicator. geometric_powers[g^b]=G^(2^b).
    states = StackBuf(2 * (SIZE_BITS + 1))
    states[0] = 0
    states[1] = 1
    for rev in unroll(0, SIZE_BITS):
        bit = SIZE_BITS - 1 - rev
        less = states[2 * rev]
        equal = states[2 * rev + 1]
        x = point[GEN ** bit]
        zero = 1 + x
        one = geometric_powers[GEN ** bit] * x
        free = zero + one
        h = height_bits[GEN ** bit]
        states[2 * (rev + 1)] = less * free + h * equal * zero
        states[2 * (rev + 1) + 1] = equal * (zero + h * free)
    return states[2 * SIZE_BITS]


@inline
def jagged_step(s0, s1, s2, s3, w0, w1, w2, w3, start_bit_point, end_bit_point):
    # Endpoint bits are Boolean-constrained public interval data, so select one
    # of the four fixed transition matrices instead of evaluating a redundant
    # four-variable tensor. The row/index eq tensor is shared by row groups.
    out = StackBuf(4)
    if start_bit_point == 0:
        if end_bit_point == 0:
            out[0] = s0 * (w0 + w3) + (s1 + s3) * w2 + s2 * w3
            out[1] = s1 * w1
            out[2] = s2 * w0
            out[3] = s3 * w1
        else:
            out[0] = s0 * w3 + s1 * w2
            out[1] = 0
            out[2] = s0 * w0 + s2 * (w0 + w3) + s3 * w2
            out[3] = (s1 + s3) * w1
    else:
        if end_bit_point == 0:
            out[0] = (s0 + s2) * w2
            out[1] = s0 * w1 + s1 * (w0 + w3) + s3 * w3
            out[2] = 0
            out[3] = s2 * w1 + s3 * w0
        else:
            out[0] = s0 * w2
            out[1] = s1 * w3
            out[2] = s2 * w2
            out[3] = (s0 + s2) * w1 + s1 * w0 + s3 * (w0 + w3)
    return out[0], out[1], out[2], out[3]

def tight_overlap_eval(row_point, index_point, start_bits, end_bits):
    # Σ_{r<end-start} eq(row_point,r)·eq(index_point,start+r).
    # This is the public terminal weight in the tight-layout reduction.
    s0 = 1
    s1 = 0
    s2 = 0
    s3 = 0
    for bit in unroll(0, SIZE_BITS):
        r = row_point[GEN ** bit]
        x = index_point[GEN ** bit]
        rx = r * x
        s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, 1 + r + x + rx, r + rx, x + rx, rx, start_bits[GEN ** bit], end_bits[GEN ** bit])
    s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, 1, 0, 0, 0, 0, 0)
    return s2


@inline
def jagged_step_row_zero(s0, s1, s2, s3, x, start_bit, end_bit):
    # jagged_step specialized to a logical row bit fixed to zero.
    zero = 1 + x
    out = StackBuf(4)
    if start_bit == 0:
        if end_bit == 0:
            out[0] = s0 * zero + (s1 + s3) * x
            out[1] = 0
            out[2] = s2 * zero
            out[3] = 0
        else:
            out[0] = s1 * x
            out[1] = 0
            out[2] = (s0 + s2) * zero + s3 * x
            out[3] = 0
    else:
        if end_bit == 0:
            out[0] = (s0 + s2) * x
            out[1] = s1 * zero
            out[2] = 0
            out[3] = s3 * zero
        else:
            out[0] = s0 * x
            out[1] = 0
            out[2] = s2 * x
            out[3] = (s1 + s3) * zero
    return out[0], out[1], out[2], out[3]


def tight_overlap_eval_fixed(row_point, index_point, start_bits, end_bits, row_bits: Const, index_bits: Const):
    # The same overlap, specialized to the certified logical-row and target
    # cubes. Above row_bits the logical row is fixed to zero.
    s0 = 1
    s1 = 0
    s2 = 0
    s3 = 0
    for bit in unroll(0, row_bits):
        r = row_point[GEN ** bit]
        x = index_point[GEN ** bit]
        rx = r * x
        s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, 1 + r + x + rx, r + rx, x + rx, rx, start_bits[GEN ** bit], end_bits[GEN ** bit])
    for bit in unroll(row_bits, index_bits):
        x = index_point[GEN ** bit]
        s0, s1, s2, s3 = jagged_step_row_zero(s0, s1, s2, s3, x, start_bits[GEN ** bit], end_bits[GEN ** bit])
    s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, 1, 0, 0, 0, 0, 0)
    return s2


@inline
def jagged_step_start_length(s0, s1, s2, s3, w0, w1, w2, w3, start_bit, length_bit):
    out = StackBuf(4)
    if start_bit == 0:
        if length_bit == 0:
            out[0] = s0 * (w0 + w3) + s1 * w2 + s2 * w3
            out[1] = (s1 + s3) * w1
            out[2] = s2 * w0 + s3 * w2
            out[3] = 0
        else:
            out[0] = s0 * w3
            out[1] = s1 * w1
            out[2] = (s0 + s2) * w0 + s1 * w2 + s2 * w3 + s3 * w2
            out[3] = s3 * w1
    else:
        if length_bit == 0:
            out[0] = s0 * w2
            out[1] = s0 * w1 + s1 * (w0 + w3) + s2 * w1 + s3 * w3
            out[2] = s2 * w2
            out[3] = s3 * w0
        else:
            out[0] = 0
            out[1] = s0 * w1 + s1 * w3
            out[2] = (s0 + s2) * w2
            out[3] = s1 * w0 + s2 * w1 + s3 * (w0 + w3)
    return out[0], out[1], out[2], out[3]


def jagged_step_start_length_points(s0, s1, s2, s3, w0, w1, w2, w3, start, length):
    a00, a01, a02, a03 = jagged_step_start_length(s0, s1, s2, s3, w0, w1, w2, w3, 0, 0)
    b00, b01, b02, b03 = jagged_step_start_length(s0, s1, s2, s3, w0, w1, w2, w3, 0, 1)
    a10, a11, a12, a13 = jagged_step_start_length(s0, s1, s2, s3, w0, w1, w2, w3, 1, 0)
    b10, b11, b12, b13 = jagged_step_start_length(s0, s1, s2, s3, w0, w1, w2, w3, 1, 1)
    z0 = a00 + length * (a00 + b00)
    z1 = a01 + length * (a01 + b01)
    z2 = a02 + length * (a02 + b02)
    z3 = a03 + length * (a03 + b03)
    o0 = a10 + length * (a10 + b10)
    o1 = a11 + length * (a11 + b11)
    o2 = a12 + length * (a12 + b12)
    o3 = a13 + length * (a13 + b13)
    return z0 + start * (z0 + o0), z1 + start * (z1 + o1), z2 + start * (z2 + o2), z3 + start * (z3 + o3)


def jagged_step_start_point_length_zero(s0, s1, s2, s3, w0, w1, w2, w3, start):
    z0, z1, z2, z3 = jagged_step_start_length(s0, s1, s2, s3, w0, w1, w2, w3, 0, 0)
    o0, o1, o2, o3 = jagged_step_start_length(s0, s1, s2, s3, w0, w1, w2, w3, 1, 0)
    return z0 + start * (z0 + o0), z1 + start * (z1 + o1), z2 + start * (z2 + o2), z3 + start * (z3 + o3)


def tight_overlap_start_length_points(row_point, index_point, start_point, length_point):
    s0 = 1
    s1 = 0
    s2 = 0
    s3 = 0
    for bit in unroll(0, SIZE_BITS):
        r = row_point[GEN ** bit]
        x = index_point[GEN ** bit]
        rx = r * x
        s0, s1, s2, s3 = jagged_step_start_length_points(s0, s1, s2, s3, 1 + r + x + rx, r + rx, x + rx, rx, start_point[GEN ** bit], length_point[GEN ** bit])
    s0, s1, s2, s3 = jagged_step_start_length(s0, s1, s2, s3, 1, 0, 0, 0, 0, 0)
    return s2


def tight_overlap_start_length_points_fixed(row_point, index_point, start_point, length_point, row_bits: Const, index_bits: Const, length_bits: Const):
    s0 = 1
    s1 = 0
    s2 = 0
    s3 = 0
    for bit in unroll(0, row_bits):
        r = row_point[GEN ** bit]
        x = index_point[GEN ** bit]
        rx = r * x
        s0, s1, s2, s3 = jagged_step_start_length_points(s0, s1, s2, s3, 1 + r + x + rx, r + rx, x + rx, rx, start_point[GEN ** bit], length_point[GEN ** bit])
    for bit in unroll(row_bits, length_bits):
        x = index_point[GEN ** bit]
        s0, s1, s2, s3 = jagged_step_start_length_points(s0, s1, s2, s3, 1 + x, 0, x, 0, start_point[GEN ** bit], length_point[GEN ** bit])
    for bit in unroll(length_bits, index_bits):
        x = index_point[GEN ** bit]
        s0, s1, s2, s3 = jagged_step_start_point_length_zero(s0, s1, s2, s3, 1 + x, 0, x, 0, start_point[GEN ** bit])
    s0, s1, s2, s3 = jagged_step_start_length(s0, s1, s2, s3, 1, 0, 0, 0, 0, 0)
    return s2


def product_sumcheck_round(state_0, state_1, msg_cursor, claim):
    fs = [state_0, state_1]
    fs, m0, msg_cursor = fs_next(fs, msg_cursor)
    fs, m1, msg_cursor = fs_next(fs, msg_cursor)
    fs, m2, msg_cursor = fs_next(fs, msg_cursor)
    assert m0 + m1 == claim
    fs = squeeze(fs)
    challenge = fs[0]
    l0 = (challenge + 1) * (challenge + GEN) * LAGRANGE_INV_0
    l1 = challenge * (challenge + GEN) * LAGRANGE_INV_1
    l2 = challenge * (challenge + 1) * LAGRANGE_INV_2
    new_claim = m0 * l0 + m1 * l1 + m2 * l2
    return fs[0], fs[1], msg_cursor, new_claim, challenge


def product_sumcheck_round2(state_0, state_1, msg_cursor, claim):
    fs = [state_0, state_1]
    fs, m0, msg_cursor = fs_next(fs, msg_cursor)
    fs, mg, msg_cursor = fs_next(fs, msg_cursor)
    m1 = claim + m0
    fs = squeeze(fs)
    challenge = fs[0]
    l0 = (challenge + 1) * (challenge + GEN) * LAGRANGE_INV_0
    l1 = challenge * (challenge + GEN) * LAGRANGE_INV_1
    l2 = challenge * (challenge + 1) * LAGRANGE_INV_2
    new_claim = m0 * l0 + m1 * l1 + mg * l2
    return fs[0], fs[1], msg_cursor, new_claim, challenge

def qpkd_plain_weight(fold_challenges, point, cplen_g, point_len_g, slot: Const, qpkdv_g, fold_cap_g):
    weight = GEN ** 0
    for bit in unroll(0, LOG2_FIELD_BITS):
        if (slot // (2 ** bit)) % 2 == 1:
            weight *= fold_challenges[GEN ** bit]
        else:
            weight *= 1 + fold_challenges[GEN ** bit]
    ris7 = fold_challenges * GEN ** LOG2_FIELD_BITS
    point_chain = HeapBuf(SIZE_BITS + 1)
    point_chain[GEN ** 0] = weight
    for xk in mul_range(1, point_len_g):
        point_chain[xk * GEN] = point_chain[xk] * (1 + point[xk] + ris7[xk])
    weight = point_chain[point_len_g]
    zero_len_g = cplen_g / point_len_g
    ris_zero = ris7 * point_len_g
    zero_chain = HeapBuf(SIZE_BITS + 1)
    zero_chain[GEN ** 0] = weight
    for xk in mul_range(1, zero_len_g):
        zero_chain[xk * GEN] = zero_chain[xk] * (1 + ris_zero[xk])
    weight = zero_chain[zero_len_g]
    q_hi_len_g = fold_cap_g / qpkdv_g
    q_hi = fold_challenges * qpkdv_g
    selector_chain = HeapBuf(SIZE_BITS + 1)
    selector_chain[GEN ** 0] = weight
    for xk in mul_range(1, q_hi_len_g):
        selector_chain[xk * GEN] = selector_chain[xk] * (1 + q_hi[xk])
    return selector_chain[q_hi_len_g]

def jagged_prefix_fixed(row_point, index_point, gamma, selector_len: Const, start_bits, end_bits, nbits: Const):
    # Candidate-specialized straight-line prefix. Generate the four equality
    # weights immediately before their transition instead of materializing and
    # reloading a 4 * nbits heap table for every block.
    s0 = 1
    s1 = 0
    s2 = 0
    s3 = 0
    gamma_bit = gamma
    for bit in unroll(0, selector_len):
        index_bit = index_point[GEN ** bit]
        rx = gamma_bit * index_bit
        s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, 1 + index_bit, gamma_bit + rx, index_bit, rx, start_bits[GEN ** bit], end_bits[GEN ** bit])
        gamma_bit *= gamma_bit
    for bit in unroll(selector_len, nbits):
        row_bit = row_point[GEN ** (bit - selector_len)]
        index_bit = index_point[GEN ** bit]
        rx = row_bit * index_bit
        s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, 1 + row_bit + index_bit + rx, row_bit + rx, index_bit + rx, rx, start_bits[GEN ** bit], end_bits[GEN ** bit])
    return s0, s1, s2, s3


def jagged_reverse_step(v0, v1, v2, v3, w0, w1, w2, w3, row_bit, start_bit, end_bit):
    # General residual transition, retained for row points whose residual
    # coordinates are not all zero.
    if row_bit == 0:
        if start_bit == 0:
            if end_bit == 0:
                return v0, w0, v2, w0
            return v2, w0, v2, w2
        if end_bit == 0:
            return w0, v1, w0, v3
        return w0, v3, w2, v3
    if row_bit == 1:
        if start_bit == 0:
            if end_bit == 0:
                return w0, v1, w0, v3
            return w0, v3, w2, v3
        if end_bit == 0:
            return v1, w1, v3, w1
        return v3, w1, v3, w3
    one_plus_row = 1 + row_bit
    if start_bit == 0:
        if end_bit == 0:
            return one_plus_row * v0 + row_bit * w0, row_bit * v1 + one_plus_row * w0, one_plus_row * v2 + row_bit * w0, row_bit * v3 + one_plus_row * w0
        return one_plus_row * v2 + row_bit * w0, row_bit * v3 + one_plus_row * w0, one_plus_row * v2 + row_bit * w2, row_bit * v3 + one_plus_row * w2
    if end_bit == 0:
        return row_bit * v1 + one_plus_row * w0, one_plus_row * v1 + row_bit * w1, row_bit * v3 + one_plus_row * w0, one_plus_row * v3 + row_bit * w1
    return row_bit * v3 + one_plus_row * w0, one_plus_row * v3 + row_bit * w1, row_bit * v3 + one_plus_row * w2, one_plus_row * v3 + row_bit * w3


def jagged_contract_zero(final_msg, start_bits, end_bits, fold_bits: Const, log_len: Const, init0, init1, init2, init3):
    # With every residual logical-row coordinate fixed to zero, each prefix
    # state reaches exactly one message index: start_hi for carry 0, or
    # start_hi + 1 for carry 1. The comparison state accepts equality only
    # when its low-bit comparison is already strict. `final_msg` has one
    # explicit zero sentinel after its 2^log_len real entries, so a carry from
    # the last message index is rejected without an out-of-range read.
    assert start_bits[GEN ** (fold_bits + log_len)] == 0
    start_plus_one = StackBuf(YR_LOG_CAP + 1)
    start_ptr = GEN ** 0
    carry = 1
    for bit in unroll(0, log_len):
        start_bit = start_bits[GEN ** (fold_bits + bit)]
        start_plus_one[bit] = start_bit + carry
        carry *= start_bit
        start_ptr *= 1 + start_bit * (1 + GEN ** (2 ** bit))
    start_plus_one[log_len] = carry

    # Compute start_hi < end_hi and start_hi == end_hi, including the extra
    # endpoint bit that represents an interval ending exactly at 2^M. At the
    # same time, test whether end_hi == start_hi + 1.
    less = 0
    equal = 1
    adjacent = 1
    for rev in unroll(0, log_len + 1):
        bit = log_len - rev
        end_bit = end_bits[GEN ** (fold_bits + bit)]
        if bit == log_len:
            start_bit = 0
        else:
            start_bit = start_bits[GEN ** (fold_bits + bit)]
        equal_start_zero = equal * (1 + start_bit)
        less += end_bit * equal_start_zero
        equal *= 1 + start_bit + end_bit
        adjacent *= 1 + start_plus_one[bit] + end_bit
    start_plus_one_less = less * (1 + adjacent)

    at_start = less * (init0 + init2) + equal * init2
    at_start_plus_one = start_plus_one_less * init1 + less * init3
    return final_msg[start_ptr] * at_start + final_msg[start_ptr * GEN] * at_start_plus_one


def jagged_contract_general(final_msg, row_point, start_bits, end_bits, fold_bits: Const, log_len: Const, row_shift: Const, init0, init1, init2, init3):
    layers = StackBuf(8 * 2 ** YR_LOG_CAP)
    for y in unroll(0, 2 ** log_len):
        layers[4 * y] = 0
        layers[4 * y + 1] = 0
        layers[4 * y + 2] = final_msg[GEN ** y]
        layers[4 * y + 3] = 0
    layer_off = 0
    layer_len = 2 ** log_len
    next_off = 4 * layer_len
    for stage in unroll(0, log_len):
        bit = log_len - 1 - stage
        next_len = 2 ** bit
        for t in unroll(0, next_len):
            v = layer_off + 4 * t
            w = layer_off + 4 * (t + next_len)
            o0, o1, o2, o3 = jagged_reverse_step(layers[v], layers[v + 1], layers[v + 2], layers[v + 3], layers[w], layers[w + 1], layers[w + 2], layers[w + 3], row_point[GEN ** (fold_bits + bit - row_shift)], start_bits[GEN ** (fold_bits + bit)], end_bits[GEN ** (fold_bits + bit)])
            out = next_off + 4 * t
            layers[out] = o0
            layers[out + 1] = o1
            layers[out + 2] = o2
            layers[out + 3] = o3
        layer_off = next_off
        layer_len = next_len
        next_off = next_off + 4 * next_len
    return init0 * layers[layer_off] + init1 * layers[layer_off + 1] + init2 * layers[layer_off + 2] + init3 * layers[layer_off + 3]

def jagged_terminal(m_idx: Const, fold_challenges, final_msg, claim_rows, col_bound_bits, gamma, gamma_powers):
    # One automaton per complete row-major column block, rather than one per
    # physical column. For selector bit b, unnormalized row weights (1,
    # gamma^(2^b)) absorb the geometric batch scale Π(1+gamma^(2^b)) without
    # any field inversions; the remaining coordinates are the shared row point.
    # The closed-form zero-residual terminal may address entry 2^log_len when
    # the last real entry carries. Make that rejection an explicit shared zero.
    terminal_msg = HeapBuf(2 ** YR_LOG_CAP + 1)
    for y in unroll(0, 2 ** LIG_YR_LOG_LEN[m_idx]):
        terminal_msg[GEN ** y] = final_msg[GEN ** y]
    terminal_msg[GEN ** (2 ** LIG_YR_LOG_LEN[m_idx])] = 0
    residual_zero = HeapBuf(N_JAGGED_BATCHES)
    total = 0
    for batch in unroll(0, N_JAGGED_BATCHES):
        row = claim_rows * GEN ** (SIZE_BITS * JAGGED_BATCH_ROW[batch])
        start_bits = col_bound_bits * GEN ** (SIZE_BITS * JAGGED_BATCH_COL[batch])
        end_bits = col_bound_bits * GEN ** (SIZE_BITS * (JAGGED_BATCH_COL[batch] + 1))
        p0, p1, p2, p3 = jagged_prefix_fixed(row, fold_challenges, gamma, JAGGED_BATCH_LOG[batch], start_bits, end_bits, LIG_TOTAL_FOLDS[m_idx])
        folded_out = StackBuf(1)
        if LIG_YR_LOG_LEN[m_idx] == 3:
            if row[GEN ** (LIG_TOTAL_FOLDS[m_idx] - JAGGED_BATCH_LOG[batch])] == 0:
                if row[GEN ** (LIG_TOTAL_FOLDS[m_idx] + 1 - JAGGED_BATCH_LOG[batch])] == 0:
                    if row[GEN ** (LIG_TOTAL_FOLDS[m_idx] + 2 - JAGGED_BATCH_LOG[batch])] == 0:
                        residual_zero[GEN ** batch] = 1
                    else:
                        residual_zero[GEN ** batch] = 0
                else:
                    residual_zero[GEN ** batch] = 0
            else:
                residual_zero[GEN ** batch] = 0
        elif LIG_YR_LOG_LEN[m_idx] == 4:
            if row[GEN ** (LIG_TOTAL_FOLDS[m_idx] - JAGGED_BATCH_LOG[batch])] == 0:
                if row[GEN ** (LIG_TOTAL_FOLDS[m_idx] + 1 - JAGGED_BATCH_LOG[batch])] == 0:
                    if row[GEN ** (LIG_TOTAL_FOLDS[m_idx] + 2 - JAGGED_BATCH_LOG[batch])] == 0:
                        if row[GEN ** (LIG_TOTAL_FOLDS[m_idx] + 3 - JAGGED_BATCH_LOG[batch])] == 0:
                            residual_zero[GEN ** batch] = 1
                        else:
                            residual_zero[GEN ** batch] = 0
                    else:
                        residual_zero[GEN ** batch] = 0
                else:
                    residual_zero[GEN ** batch] = 0
            else:
                residual_zero[GEN ** batch] = 0
        else:
            residual_zero[GEN ** batch] = 0
        if residual_zero[GEN ** batch] == 1:
            folded_out[0] = jagged_contract_zero(terminal_msg, start_bits, end_bits, LIG_TOTAL_FOLDS[m_idx], LIG_YR_LOG_LEN[m_idx], p0, p1, p2, p3)
        else:
            folded_out[0] = jagged_contract_general(final_msg, row, start_bits, end_bits, LIG_TOTAL_FOLDS[m_idx], LIG_YR_LOG_LEN[m_idx], JAGGED_BATCH_LOG[batch], p0, p1, p2, p3)
        folded = folded_out[0]
        total += gamma_powers[GEN ** JAGGED_BATCH_BASE[batch]] * folded
    return total


def open_stacked(m_idx: Const, fs0, fs1, target, commit_root_0, commit_root_1, cursor):
    # The stacked Ligerito opening. m_idx is the COMMITTED-LOG-SIZE CANDIDATE
    # INDEX: the certified size is m = LIG_MIN_LOG_SIZE + m_idx, and every
    # LIG_* table below reads row m_idx (the match_range dispatch bakes one
    # specialization of this function per candidate). All opening proof data is hinted HERE, so
    # hint lengths specialize per arm; only the executed arm pops its streams.
    #
    # Flow, per level:
    #   1. fold rounds: optional grinding (grind_check), squeeze the fold
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
    # Returns (sumcheck_target, fold_challenges, final_msg, residual_total,
    # yr_log_n_g = g^yr_log_n, fold_cap_g = g^lenris). The latter two describe
    # the final-message and folded-coordinate partitions of the dense point.
    fs = [fs0, fs1]

    fs = obs(fs, target)
    fs = absorb(fs, 32, DS_LEN)
    fs = absorb(fs, commit_root_0, DS_BYTE)
    fs = absorb(fs, commit_root_1, DS_BYTE)

    # The opening's scalars (sumcheck messages, level roots, nonces, final
    # message) ride the SHARED stream: msg_cursor is just the main stream
    # cursor, walked on in protocol order.
    msg_cursor = cursor
    fs, msg_u0, msg_cursor = fs_next(fs, msg_cursor)
    fs, msg_u2, msg_cursor = fs_next(fs, msg_cursor)
    round_quad_c = msg_u0
    round_quad_b = target + msg_u2
    round_quad_a = msg_u2
    sumcheck_target = target

    # Opening data for every level, all consumed by the level loop below (each
    # buffer is one flat run indexed by the baked LIG_*_OFF[lvl] offsets). It
    # lives here, before the loop, because the loop is unrolled per level, so a
    # per-level decl inside would be replicated. Hinted proof data:
    merkle_leaf_rows = HeapBuf(GEN ** (LIG_ROWS_LEN[m_idx]))
    hint_witness(merkle_leaf_rows[0:LIG_ROWS_LEN[m_idx]], "merkle_leaf_rows")
    merkle_paths = HeapBuf(GEN ** (LIG_PATHS_LEN[m_idx]))
    hint_witness(merkle_paths[0:LIG_PATHS_LEN[m_idx]], "merkle_paths")
    final_msg = HeapBuf(GEN ** (LIG_YR_LEN[m_idx]))  # filled from the stream at the last level
    # Stream-bound level roots (filled as each root is read; index = level).
    level_roots_0 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    level_roots_1 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    # ...and guest-filled accumulators (one slot per fold / per level / per query):
    fold_challenges = HeapBuf(GEN ** (LIG_TOTAL_FOLDS[m_idx]))
    level_betas = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    alpha_weights = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_QUERIES[m_idx]))
    query_positions = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    query_bit_ptrs = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))

    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        for j in unroll(0, LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl]):
            fold_idx = LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl] + j
            if LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx] != 0:
                nonce_v = msg_cursor[GEN ** 0]  # raw transport word: bound by the DS_POW absorb below
                msg_cursor = msg_cursor * GEN
                grind_check(fs[0], fs[1], nonce_v, GEN ** LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx])
                fs = absorb(fs, nonce_v, DS_POW)
            fs = squeeze(fs)
            fold_challenge = fs[0]
            fold_challenges[GEN ** fold_idx] = fold_challenge
            sumcheck_target = round_quad_c + fold_challenge * round_quad_b + fold_challenge * fold_challenge * round_quad_a  # evaluate this level's folded quadratic at the fold challenge
            fs, msg_a, msg_cursor = fs_next(fs, msg_cursor)
            fs, msg_b, msg_cursor = fs_next(fs, msg_cursor)
            round_quad_c = msg_a
            round_quad_b = sumcheck_target + msg_b
            round_quad_a = msg_b

        if lvl == LIG_YR_LEVEL[m_idx]:
            for iy in unroll(0, LIG_YR_LEN[m_idx]):
                fs, yv, msg_cursor = fs_next(fs, msg_cursor)
                final_msg[GEN ** iy] = yv
        else:
            fs, next_root_a, msg_cursor = fs_next(fs, msg_cursor)
            fs, next_root_b, msg_cursor = fs_next(fs, msg_cursor)
            level_roots_0[GEN ** (lvl + 1)] = next_root_a
            level_roots_1[GEN ** (lvl + 1)] = next_root_b
        q_nonce = msg_cursor[GEN ** 0]  # raw transport word: bound by the DS_POW absorb below
        msg_cursor = msg_cursor * GEN
        if LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl] != 0:
            grind_check(fs[0], fs[1], q_nonce, GEN ** LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl])
        fs = absorb(fs, q_nonce, DS_POW)

        sqz_chain_0 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_1 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_0[GEN ** 0] = fs[0]
        sqz_chain_1[GEN ** 0] = fs[1]
        for xs in mul_range(1, GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]):
            packed_word, next_c0, next_c1 = squeeze_step(sqz_chain_0[xs], sqz_chain_1[xs])
            sqz_chain_0[xs * GEN] = next_c0
            sqz_chain_1[xs * GEN] = next_c1
            query_ptr = xs ** (FIELD_BITS // LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            decode_query_bits(packed_word, query_positions * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, query_bit_ptrs * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
        fs = [sqz_chain_0[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]], sqz_chain_1[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]]]

        query_alphas = HeapBuf(GEN ** (LIG_MAX_INTERLEAVE[m_idx]))
        for t in unroll(0, LIG_LOG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            fs = squeeze(fs)
            alpha_v = fs[0]
            query_alphas[GEN ** t] = alpha_v
        row_eq_weights = HeapBuf(GEN ** (LIG_MAX_INTERLEAVE[m_idx]))
        for i in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
            row_eq_weights[GEN ** i] = eq_weight(fold_challenges * GEN ** LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl], LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl], i, 0)
        for i in unroll(0, LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            alpha_weights[GEN ** (lvl * LIG_MAX_QUERIES[m_idx] + i)] = eq_weight(query_alphas, LIG_LOG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl], i, 0)

        query_sum_chain = HeapBuf(GEN ** (LIG_MAX_QUERIES[m_idx] + 1))
        query_sum_chain[GEN ** 0] = 0
        for xe in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            row_base = xe ** LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]
            row_ptr = merkle_leaf_rows * GEN ** LIG_ROWS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * row_base
            row_dot = 0
            for jb in unroll(0, LIG_LEAF_PAIRS[m_idx * LIG_MAX_LEVELS + lvl]):
                row_pair = [row_ptr[GEN ** (2 * jb)], row_ptr[GEN ** (2 * jb + 1)]]
                row_dot += row_pair[0] * row_eq_weights[GEN ** (2 * jb)] + row_pair[1] * row_eq_weights[GEN ** (2 * jb + 1)]
            # Standard BLAKE3 of the complete row. Ligerito row widths are
            # powers of two no larger than one 1024-byte BLAKE3 chunk.
            leaf_hash_state = StackBuf(2)
            blake3(row_ptr[0:2], row_ptr[2:4], leaf_hash_state, step=0, end=1 // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl], root=1 // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl])
            for jb in unroll(1, LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl]):
                leaf_digest = StackBuf(2)
                blake3(row_ptr[4 * jb:4 * jb + 2], row_ptr[4 * jb + 2:4 * jb + 4], leaf_digest, cv=leaf_hash_state, step=jb, end=(jb + 1) // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl], root=(jb + 1) // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl])
                leaf_hash_state = leaf_digest
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
                assert root_0 == level_roots_0[GEN ** lvl]
                assert root_1 == level_roots_1[GEN ** lvl]
        level_query_sum = query_sum_chain[GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]]

        if lvl == LIG_YR_LEVEL[m_idx]:
            fs = squeeze(fs)
            beta_lvl = fs[0]
            level_betas[GEN ** lvl] = beta_lvl
            sumcheck_target += beta_lvl * level_query_sum
        else:
            fs, intro_u0, msg_cursor = fs_next(fs, msg_cursor)
            fs, intro_u2, msg_cursor = fs_next(fs, msg_cursor)
            fs = squeeze(fs)
            beta_lvl = fs[0]
            level_betas[GEN ** lvl] = beta_lvl
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
    return sumcheck_target, fold_challenges, final_msg, inner_chain[GEN ** LIG_N_LEVELS[m_idx]], GEN ** LIG_YR_LOG_LEN[m_idx], GEN ** LIG_TOTAL_FOLDS[m_idx]


def exponent_tables():
    # Read-only lookup tables over the exponent domain, indexed at runtime
    # g-powers (so they must be heap, not stack): g_logs_pow2[g^j] = 2^j is 2
    # raised to a g-power's log, and g_squares[g^j] = g^(2^j) turns integer
    # sums of powers of two into field products. Returns the 2 pointers.
    g_logs_pow2 = HeapBuf(COUNT_BITS)
    for j in unroll(0, COUNT_BITS):
        g_logs_pow2[GEN ** j] = 2 ** j
    g_squares = HeapBuf(SIZE_BITS)
    sq_run = GEN
    for j in unroll(0, SIZE_BITS):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    return g_logs_pow2, g_squares


def verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement
    # (pi_0, pi_1). All proof data is hinted HERE: each call pops the next
    # sub-proof's entry of every witness stream, so the body lowers once and
    # main just calls it per statement. The g_logs_pow2/g_squares lookup
    # tables are shared read-only tables built once in main; the
    # deferred-claim data is written to `defer_out`.
    #
    # Flow (mirrors cpu::verify):
    #   1. seed the Fiat-Shamir sponge from the statement + program digest;
    #   2. announced sizes, then certify every structural log against them
    #      (count gadget log2_ceil: tau per table, log_mem);
    #   3. bind the commitment root; bus grinding (grind_check, runtime
    #      bit count); ONE RLC-batched GKR for all three trees (count padded
    #      to the pair's depth) at runtime depth, ONE shared point zeta;
    #   4. derive exact block heights and the common GKR depth; check the
    #      push/pull roots, then reduce all three tight leaf claims through one
    #      quadratic start/length sumcheck (pooling committed-column claims);
    #      reduce the public bytecode columns to one deferred stacked claim;
    #   5. six AIR zerochecks at the certified taus (sumcheck_round3);
    #   6. public-input claim + BLAKE3 pin claims (telescoped prefix MLE);
    #   7. flock reduction: univariate-skip zerocheck + lincheck (matrix
    #      evaluation deferred);
    #   8. ring-switch fronts (shared r'', linearized transpose in-circuit);
    #   9. gamma-combine everything, certify the committed size m, dispatch
    #      the stacked Ligerito opening (open_stacked), and assert its
    #      eval_b terminal;
    #  10. export the deferred-claim region for the aggregation.
    # Claim pool: values of every committed-coordinate claim in structural
    # order. Their row points are derived from the shared reduction point.
    claim_pool = HeapBuf(N_CLAIMS)
    # certified low dimension (cplen) per pooled claim, filled as the pool is
    # built (from the in-scope certified kappa/tau); the terminal pins each
    # claim's hinted lengths against it.
    claim_cplen_g = HeapBuf(N_CLAIMS)
    # Bus-reduction claims use only the coordinates required by their real row
    # prefix; logical source coordinates above that prefix are fixed to zero.
    claim_bus_nu_g = HeapBuf(N_CLAIMS)
    # The ONE shared GKR leaf point (all three trees reduce to it).

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    fs = [TRANSCRIPT_SEED_0, TRANSCRIPT_SEED_1]  # the sponge state after the b"leanvm-b" domain label
    fs = obs(fs, seed_0)  # the FS seed: H(flock circuit family, inner program
    fs = obs(fs, seed_1)  # bytecode, ...) — from the recursion's public input
    fs = obs(fs, pi_0)   # bind the sub-proof's statement (its public input)
    fs = obs(fs, pi_1)
    stream = HeapBuf(STREAM_CAP)
    hint_witness(stream[0:STREAM_CAP], "stream")
    cursor = stream  # the proof stream is replayed word by word; cursor walks it (advance = * g)

    # ---- announced sizes: used-memory prefix + 6 row counts ----
    sizes = StackBuf(N_TABLES + 1)
    for i in unroll(0, N_TABLES + 1):
        fs, x, cursor = fs_next(fs, cursor)
        sizes[i] = x

    # ---- structural logs: derive g^log_mem, compute the taus ----
    # The stream announced the sizes as integer WORDS; the shape-generic phases
    # need them as G-POWERS (loop bounds, match_range scrutinees). dims_g[0] is
    # derived from mem_used; dims_g[1 + t] = g^tau_t comes from the count gadget.
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_5], all computed
    # One exact decomposition drives both MEM/MFCNT Jagged heights and derives
    # the canonical logical log_mem = max(MIN_LOG_MEM, ceil_log2(mem_used)).
    memory_bits = HeapBuf(COUNT_BITS)
    g_log_mem, g_memory_used = log2_ceil_word(sizes[0], memory_bits, g_logs_pow2, g_squares, MIN_LOG_MEM, COUNT_BITS, 1)
    assert sizes[0] != 0
    assert sizes[0] != 1
    assert log(g_log_mem) < COUNT_BITS
    dims_g[GEN ** 0] = g_log_mem
    # count gadget: g^tau_t = log2_ceil_word(count_t), which also returns
    # g^count_t for the tight block heights and endpoints.
    count_gpows = HeapBuf(N_TABLES)
    count_bits = HeapBuf(N_TABLES * COUNT_BITS)
    for t in unroll(0, N_TABLES):
        table_count_bits = count_bits * GEN ** (COUNT_BITS * t)
        g_tau, g_count = log2_ceil_word(sizes[t + 1], table_count_bits, g_logs_pow2, g_squares, FLOORS[t], COUNT_BITS, 1)
        dims_g[GEN ** (t + 1)] = g_tau
        count_gpows[GEN ** t] = g_count
    # kappa_base maps a kappa source index to its certified announced log
    # (source 0 = const via the baked adj); the taus are now in dims_g.
    kappa_base = HeapBuf(N_TABLES + 2)
    kappa_base[GEN ** 0] = 1
    kappa_base[GEN ** 1] = g_log_mem
    for t in unroll(0, N_TABLES):
        kappa_base[GEN ** (2 + t)] = dims_g[GEN ** (t + 1)]
    # Each block's kappa DERIVES from its structural source (baked per block:
    # the boundary consts, log_mem, the bytecode log, or tau_t) as a
    # compile-time offset off a certified log — no hint, nothing left free.
    block_kappa = HeapBuf(N_BLOCKS)
    for b in unroll(0, N_BLOCKS):
        block_kappa[GEN ** b] = kappa_base[GEN ** BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]
    # Each block contributes only its real rows. The ONE bus depth is
    # mu = ceil(log2 Σ_b real_b) over PUSH; pull is paired, and count is padded
    # only once at the end to the same tree depth.
    block_height_g = HeapBuf(N_BLOCKS)
    table_real_kappa = HeapBuf(N_TABLES)
    for t in unroll(0, N_TABLES):
        table_real_kappa[GEN ** t] = log2_ceil_in_the_exponent(count_gpows[GEN ** t], g_logs_pow2, g_squares, 0, COUNT_BITS)
    memory_real_kappa = log2_ceil_in_the_exponent(g_memory_used, g_logs_pow2, g_squares, 0, COUNT_BITS)
    g_bytecode_used = GEN ** 0
    for bit in unroll(0, SIZE_BITS):
        g_bytecode_used *= 1 + BYTECODE_USED_BITS[bit] * (g_squares[GEN ** bit] + 1)
    block_real_kappa = HeapBuf(N_BLOCKS)
    for b in unroll(0, N_BLOCKS):
        if BLOCK_REAL_TABLE[b] == REAL_IS_FULL_CUBE:
            block_height_g[GEN ** b] = g_squares[block_kappa[GEN ** b]]
            block_real_kappa[GEN ** b] = block_kappa[GEN ** b]
        elif BLOCK_REAL_TABLE[b] == REAL_IS_MEMORY_PREFIX:
            block_height_g[GEN ** b] = g_memory_used
            block_real_kappa[GEN ** b] = memory_real_kappa
        elif BLOCK_REAL_TABLE[b] == REAL_IS_BYTECODE_PREFIX:
            block_height_g[GEN ** b] = g_bytecode_used
            block_real_kappa[GEN ** b] = block_kappa[GEN ** b]
        else:
            block_height_g[GEN ** b] = count_gpows[GEN ** BLOCK_REAL_TABLE[b]]
            block_real_kappa[GEN ** b] = table_real_kappa[GEN ** BLOCK_REAL_TABLE[b]]
    # The prover points to a block of maximum real height. Membership plus the
    # exponent-range checks certify that its ceil-log dominates every block:
    # if m < k, g^(m-k) wraps around the full multiplicative group and cannot
    # pass the small bounded-log check.
    reduction_max = HeapBuf(1)
    hint_witness(reduction_max[0:1], "reduction_max")
    reduction_max_idx = reduction_max[GEN ** 0]
    assert log(reduction_max_idx) < N_BLOCKS
    block_has_committed = HeapBuf(N_BLOCKS)
    for b in unroll(0, N_BLOCKS):
        block_has_committed[GEN ** b] = BLOCK_HAS_COMMITTED[b]
    assert block_has_committed[reduction_max_idx] == 1
    g_reduction_nu = block_real_kappa[reduction_max_idx]
    for b in unroll(0, N_BLOCKS):
        if BLOCK_HAS_COMMITTED[b] == 1:
            assert log(g_reduction_nu / block_real_kappa[GEN ** b]) < SIZE_BITS
    push_total = GEN ** 0
    for b in unroll(SIDE_BLOCK_START[PUSH_SIDE], SIDE_BLOCK_START[PUSH_SIDE + 1]):
        push_total *= block_height_g[GEN ** b]
    g_bus_mu = log2_ceil_in_the_exponent(push_total, g_logs_pow2, g_squares, 0, SIZE_BITS)
    zeta = HeapBuf(g_bus_mu)  # the ONE shared GKR point: exactly mu coords

    # ---- commitment root (2 words), kept for the opening phase ----
    fs, commit_root_0, cursor = fs_next(fs, cursor)
    fs, commit_root_1, cursor = fs_next(fs, cursor)

    # ---- bus: grinding FIRST, then α and γ (the PoW covers both) ----
    # grinding nonce: raw stream word (NOT observed), PoW-checked, then bound.
    nonce = cursor[GEN ** 0]
    cursor *= GEN
    # Bus grind bits = SECURITY + push.mu + 2 - 128; the extra unit accounts
    # for the degree-two batching challenge in the tight-layout reduction.
    bus_grind_window = g_bus_mu * INV_GEN ** BUS_GRIND_SHIFT  # g^(push.mu - shift): the bus PoW bit count
    grind_check(fs[0], fs[1], nonce, bus_grind_window)
    fs = absorb(fs, nonce, DS_POW)
    fs = squeeze(fs)
    alpha = fs[0]
    fs = squeeze(fs)
    gamma = fs[0]

    # ---- ONE GKR grand product: push, pull, and count RLC-batched ----
    # Push and pull have equal depth (matched blocks) and the count tree is
    # PADDED with identity leaves up to it (product unchanged), so a single
    # sumcheck serves all three trees: the prover combines their round
    # messages with weights 1, λ, λ². Each layer binds the six tail
    # evaluations, checks the combined product identity, samples the line
    # challenge, then a FRESH λ — pinning the individual values inside the
    # bound combination (the last layer's are pinned by the decompose
    # identities). All three trees reduce to claims at ONE shared point zeta.
    # State threads through write-once heap chains: layer state indexed by the
    # layer cursor, round state by a position pointer advancing per round.
    gkr_roots = StackBuf(N_GKR_SIDES)
    gkr_claims = StackBuf(N_GKR_SIDES)
    gkr_layer_size = g_bus_mu * GEN ** 2  # runtime size in the exponent: mu + 2 slots
    gkr_layer_fs0 = HeapBuf(gkr_layer_size)
    gkr_layer_fs1 = HeapBuf(gkr_layer_size)
    gkr_layer_cursor = HeapBuf(gkr_layer_size)
    gkr_layer_claim = HeapBuf(gkr_layer_size)    # push's running value
    gkr_layer_claim_b = HeapBuf(gkr_layer_size)  # pull's
    gkr_layer_claim_c = HeapBuf(gkr_layer_size)  # count's
    gkr_layer_lambda = HeapBuf(gkr_layer_size)   # the layer's combiner
    gkr_layer_row = HeapBuf(gkr_layer_size)
    gkr_layer_round_pos = HeapBuf(gkr_layer_size)
    gkr_round_fs0 = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_fs1 = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_cursor = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_claim = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_eq = HeapBuf(GKR_ROUNDS_CAP)
    gkr_pts = HeapBuf(GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    fs, root_push, cursor = fs_next(fs, cursor)
    fs, root_pull, cursor = fs_next(fs, cursor)
    fs, root_count, cursor = fs_next(fs, cursor)
    fs = squeeze(fs)
    gkr_layer_lambda[GEN ** 0] = fs[0]  # λ over the three roots
    gkr_layer_fs0[GEN ** 0] = fs[0]
    gkr_layer_fs1[GEN ** 0] = fs[1]
    gkr_layer_cursor[GEN ** 0] = cursor
    gkr_layer_claim[GEN ** 0] = root_push
    gkr_layer_claim_b[GEN ** 0] = root_pull
    gkr_layer_claim_c[GEN ** 0] = root_count
    gkr_layer_row[GEN ** 0] = gkr_pts
    gkr_layer_round_pos[GEN ** 0] = GEN ** 0
    for x_layer in mul_range(1, g_bus_mu):
        layer_fs = [gkr_layer_fs0[x_layer], gkr_layer_fs1[x_layer]]
        lam = gkr_layer_lambda[x_layer]
        claim_l = gkr_layer_claim[x_layer] + lam * (gkr_layer_claim_b[x_layer] + lam * gkr_layer_claim_c[x_layer])
        point_row = gkr_layer_row[x_layer]
        round_pos = gkr_layer_round_pos[x_layer]
        nextrow = point_row * GEN ** MU_CAP
        gkr_round_fs0[round_pos] = layer_fs[0]
        gkr_round_fs1[round_pos] = layer_fs[1]
        gkr_round_cursor[round_pos] = gkr_layer_cursor[x_layer]
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
        tail_fs = [gkr_round_fs0[final_pos], gkr_round_fs1[final_pos]]
        tcur = gkr_round_cursor[final_pos]
        tclaim = gkr_round_claim[final_pos]
        teq = gkr_round_eq[final_pos]
        tail_fs, e0_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_count, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_count, tcur = fs_next(tail_fs, tcur)
        assert tclaim == teq * (e0_push * e1_push + lam * (e0_pull * e1_pull + lam * (e0_count * e1_count)))
        tail_fs = squeeze(tail_fs)
        layer_challenge = tail_fs[0]
        nextrow[GEN ** 0] = layer_challenge
        xln = x_layer * GEN
        gkr_layer_claim[xln] = e0_push + layer_challenge * (e0_push + e1_push)
        gkr_layer_claim_b[xln] = e0_pull + layer_challenge * (e0_pull + e1_pull)
        gkr_layer_claim_c[xln] = e0_count + layer_challenge * (e0_count + e1_count)
        tail_fs = squeeze(tail_fs)  # fresh λ pins the tail individuals
        gkr_layer_lambda[xln] = tail_fs[0]
        gkr_layer_fs0[xln] = tail_fs[0]
        gkr_layer_fs1[xln] = tail_fs[1]
        gkr_layer_cursor[xln] = tcur
        gkr_layer_row[xln] = nextrow
        gkr_layer_round_pos[xln] = round_pos * x_layer * GEN
    fs = [gkr_layer_fs0[g_bus_mu], gkr_layer_fs1[g_bus_mu]]
    cursor = gkr_layer_cursor[g_bus_mu]
    final_point_row = gkr_layer_row[g_bus_mu]
    for xt in mul_range(1, g_bus_mu):
        zeta[xt] = final_point_row[xt]  # the ONE shared point
    gkr_roots[PUSH_SIDE] = root_push
    gkr_roots[PULL_SIDE] = root_pull
    gkr_roots[COUNT_SIDE] = root_count
    gkr_claims[PUSH_SIDE] = gkr_layer_claim[g_bus_mu]
    gkr_claims[PULL_SIDE] = gkr_layer_claim_b[g_bus_mu]
    gkr_claims[COUNT_SIDE] = gkr_layer_claim_c[g_bus_mu]

    # ---- count root nonzero ----
    assert gkr_roots[COUNT_SIDE] != 0  # count-tree root nonzero: no read count self-cancels

    # ---- tight bus-leaf offsets ----
    # Blocks are concatenated in their canonical declaration order. Offsets
    # advance by each block's certified REAL height, so there are no internal
    # padding leaves. Pull mirrors push block-for-block.
    # Height bits come from size data already certified above. Sharing them by
    # symbolic height avoids both duplicate work and unconstrained bit advice.
    height_group_bits = HeapBuf(SIZE_BITS * N_HEIGHT_GROUPS)
    for group in unroll(0, N_HEIGHT_GROUPS):
        height_bits = height_group_bits * GEN ** (SIZE_BITS * group)
        if HEIGHT_GROUP_KIND[group] == REAL_IS_FULL_CUBE:
            kappa_g = kappa_base[GEN ** HEIGHT_GROUP_KAPPA_SRC[group]] * GEN ** HEIGHT_GROUP_KAPPA_ADJ[group]
            for bit in unroll(0, SIZE_BITS):
                if kappa_g == GEN ** bit:
                    height_bits[GEN ** bit] = 1
                else:
                    height_bits[GEN ** bit] = 0
        elif HEIGHT_GROUP_KIND[group] == REAL_IS_MEMORY_PREFIX:
            for bit in unroll(0, COUNT_BITS):
                height_bits[GEN ** bit] = memory_bits[GEN ** bit]
            for bit in unroll(COUNT_BITS, SIZE_BITS):
                height_bits[GEN ** bit] = 0
        elif HEIGHT_GROUP_KIND[group] == REAL_IS_BYTECODE_PREFIX:
            for bit in unroll(0, SIZE_BITS):
                height_bits[GEN ** bit] = BYTECODE_USED_BITS[bit]
        else:
            for bit in unroll(0, COUNT_BITS):
                height_bits[GEN ** bit] = count_bits[GEN ** (COUNT_BITS * HEIGHT_GROUP_KIND[group] + bit)]
            for bit in unroll(COUNT_BITS, SIZE_BITS):
                height_bits[GEN ** bit] = 0

    push_count = SIDE_BLOCK_START[PUSH_SIDE + 1] - SIDE_BLOCK_START[PUSH_SIDE]

    # With internal padding removed, the two real tuple products agree directly.
    assert gkr_roots[PUSH_SIDE] == gkr_roots[PULL_SIDE]

    # ---- tight leaf reduction ----
    # Since the final GKR pad is 1,
    #   claim_s + 1 = sum_real_rows (fingerprint_s(row) + 1) eq(zeta, target).
    # Batch all three complete identities before reducing them. This brings
    # constants, indices, and public bytecode into the same sumcheck and avoids
    # evaluating a separate prefix mass for every block.
    bytecode_vals = HeapBuf(BYTECODE_COLS)
    hint_witness(bytecode_vals[0:BYTECODE_COLS], "bytecode_vals")
    zeta_full = HeapBuf(SIZE_BITS)
    for xk in mul_range(1, g_bus_mu):
        zeta_full[xk] = zeta[xk]
    zeta_zero = zeta_full * g_bus_mu
    zeta_zero_len_g = GEN ** SIZE_BITS / g_bus_mu
    for xk in mul_range(1, zeta_zero_len_g):
        zeta_zero[xk] = 0
    fs = squeeze(fs)
    bus_eta = fs[0]
    reduction_claim = gkr_claims[0] + 1 + bus_eta * (gkr_claims[1] + 1 + bus_eta * (gkr_claims[2] + 1))
    bus_rho = HeapBuf(SIZE_BITS)
    red_fs0 = HeapBuf(MU_CAP + 2)
    red_fs1 = HeapBuf(MU_CAP + 2)
    red_cursor = HeapBuf(MU_CAP + 2)
    red_claim = HeapBuf(MU_CAP + 2)
    red_fs0[GEN ** 0] = fs[0]
    red_fs1[GEN ** 0] = fs[1]
    red_cursor[GEN ** 0] = cursor
    red_claim[GEN ** 0] = reduction_claim
    for xk in mul_range(1, g_reduction_nu):
        nfs0, nfs1, ncursor, nclaim, challenge = product_sumcheck_round(red_fs0[xk], red_fs1[xk], red_cursor[xk], red_claim[xk])
        bus_rho[xk] = challenge
        xkn = xk * GEN
        red_fs0[xkn] = nfs0
        red_fs1[xkn] = nfs1
        red_cursor[xkn] = ncursor
        red_claim[xkn] = nclaim
    fs = [red_fs0[g_reduction_nu], red_fs1[g_reduction_nu]]
    cursor = red_cursor[g_reduction_nu]
    reduction_claim = red_claim[g_reduction_nu]
    bus_rho_zero = bus_rho * g_reduction_nu
    bus_rho_zero_len_g = GEN ** SIZE_BITS / g_reduction_nu
    for xk in mul_range(1, bus_rho_zero_len_g):
        bus_rho_zero[xk] = 0

    # The prover streams one evaluation per first (column,kappa) occurrence.
    for s in unroll(0, N_GKR_SIDES):
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            for i in unroll(0, BLOCK_COORD_COUNT[b]):
                coord = BLOCK_COORD_OFF[b] + i
                if COORD_FRESH[coord] == 1:
                    fs, column_value, cursor = fs_next(fs, cursor)
                    slot = COORD_CLAIM_SLOT[coord]
                    claim_pool[GEN ** slot] = column_value
                    claim_cplen_g[GEN ** slot] = block_kappa[GEN ** b]
                    claim_bus_nu_g[GEN ** slot] = block_real_kappa[GEN ** b]

    # Public bytecode is another source polynomial in the reduction. Its eight
    # evaluations are fixed by the program, absorbed now, and later collapsed
    # to the existing single deferred bytecode claim.
    for k in unroll(0, BYTECODE_COLS):
        fs = obs(fs, bytecode_vals[GEN ** k])

    # Evaluate each block's source fingerprint at bus_rho. Push and pull twins
    # share one target interval and are combined before the overlap assist.
    index_mle_factors = HeapBuf(SIZE_BITS)
    for bit in unroll(0, SIZE_BITS):
        index_mle_factors[GEN ** bit] = INDEX_MLE_FACTORS[bit]
    block_source_eval = HeapBuf(N_BLOCKS)
    for s in unroll(0, N_GKR_SIDES):
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            if s == COUNT_SIDE:
                source_eval = 1
            else:
                source_eval = gamma + 1
            alpha_pow = 1
            block_public_idx = 0
            for i in unroll(0, BLOCK_COORD_COUNT[b]):
                coord = BLOCK_COORD_OFF[b] + i
                if COORD_TYPE[coord] == COORD_KIND_CONST:
                    source_eval += alpha_pow * COORD_CONST[coord]
                elif COORD_TYPE[coord] == COORD_KIND_INDEX:
                    index_chain = HeapBuf(SIZE_BITS + 1)
                    index_chain[GEN ** 0] = 1
                    row_nu_g = block_real_kappa[GEN ** b]
                    for xk in mul_range(1, row_nu_g):
                        index_chain[xk * GEN] = index_chain[xk] * (1 + bus_rho[xk] * index_mle_factors[xk])
                    source_eval += alpha_pow * index_chain[row_nu_g]
                elif COORD_TYPE[coord] == COORD_KIND_COL:
                    source_eval += alpha_pow * claim_pool[GEN ** COORD_CLAIM_SLOT[coord]]
                elif COORD_TYPE[coord] == COORD_KIND_GCOL:
                    source_eval += alpha_pow * GEN * claim_pool[GEN ** COORD_CLAIM_SLOT[coord]]
                else:
                    assert COORD_TYPE[coord] == COORD_KIND_PUBLIC
                    source_eval += alpha_pow * bytecode_vals[GEN ** block_public_idx]
                    block_public_idx += 1
                if s != COUNT_SIDE:
                    alpha_pow *= alpha
            block_source_eval[GEN ** b] = source_eval

    assist_coeff = HeapBuf(N_BLOCKS)
    for i in unroll(0, push_count):
        push_block = SIDE_BLOCK_START[PUSH_SIDE] + i
        pull_block = SIDE_BLOCK_START[PULL_SIDE] + i
        assist_coeff[GEN ** push_block] = block_source_eval[GEN ** push_block] + bus_eta * block_source_eval[GEN ** pull_block]
    count_count = SIDE_BLOCK_START[COUNT_SIDE + 1] - SIDE_BLOCK_START[COUNT_SIDE]
    for i in unroll(0, count_count):
        count_block = SIDE_BLOCK_START[COUNT_SIDE] + i
        assist_coeff[GEN ** count_block] = bus_eta * bus_eta * block_source_eval[GEN ** count_block]

    # Jagged assist: prove the weighted sum of all interval overlaps with one
    # sumcheck over the start and length bits. Starts need mu bits; lengths need
    # nu+1 bits to represent a full 2^nu block. This replaces one width-four
    # automaton per block by mu+nu+1 cheap rounds and one final automaton.
    assist_start_len_g = g_bus_mu
    assist_length_len_g = g_reduction_nu * GEN
    assist_start = HeapBuf(SIZE_BITS)
    assist_length = HeapBuf(SIZE_BITS)
    assist_fs0 = HeapBuf(MU_CAP + 2)
    assist_fs1 = HeapBuf(MU_CAP + 2)
    assist_cursor = HeapBuf(MU_CAP + 2)
    assist_claim = HeapBuf(MU_CAP + 2)
    assist2_fs0 = HeapBuf(MU_CAP + 2)
    assist2_fs1 = HeapBuf(MU_CAP + 2)
    assist2_cursor = HeapBuf(MU_CAP + 2)
    assist2_claim = HeapBuf(MU_CAP + 2)
    assist_fs0[GEN ** 0] = fs[0]
    assist_fs1[GEN ** 0] = fs[1]
    assist_cursor[GEN ** 0] = cursor
    assist_claim[GEN ** 0] = reduction_claim
    for xk in mul_range(1, assist_start_len_g):
        nfs0, nfs1, ncursor, nclaim, challenge = product_sumcheck_round2(assist_fs0[xk], assist_fs1[xk], assist_cursor[xk], assist_claim[xk])
        assist_start[xk] = challenge
        xkn = xk * GEN
        assist_fs0[xkn] = nfs0
        assist_fs1[xkn] = nfs1
        assist_cursor[xkn] = ncursor
        assist_claim[xkn] = nclaim
    assist2_fs0[GEN ** 0] = assist_fs0[assist_start_len_g]
    assist2_fs1[GEN ** 0] = assist_fs1[assist_start_len_g]
    assist2_cursor[GEN ** 0] = assist_cursor[assist_start_len_g]
    assist2_claim[GEN ** 0] = assist_claim[assist_start_len_g]
    for xk in mul_range(1, assist_length_len_g):
        nfs0, nfs1, ncursor, nclaim, challenge = product_sumcheck_round2(assist2_fs0[xk], assist2_fs1[xk], assist2_cursor[xk], assist2_claim[xk])
        assist_length[xk] = challenge
        xkn = xk * GEN
        assist2_fs0[xkn] = nfs0
        assist2_fs1[xkn] = nfs1
        assist2_cursor[xkn] = ncursor
        assist2_claim[xkn] = nclaim
    fs = [assist2_fs0[assist_length_len_g], assist2_fs1[assist_length_len_g]]
    cursor = assist2_cursor[assist_length_len_g]
    assist_terminal = assist2_claim[assist_length_len_g]
    assist_start_zero = assist_start * assist_start_len_g
    assist_start_zero_len_g = GEN ** SIZE_BITS / assist_start_len_g
    for xk in mul_range(1, assist_start_zero_len_g):
        assist_start_zero[xk] = 0
    assist_length_zero = assist_length * assist_length_len_g
    assist_length_zero_len_g = GEN ** SIZE_BITS / assist_length_len_g
    for xk in mul_range(1, assist_length_zero_len_g):
        assist_length_zero[xk] = 0

    # Certify the tight offsets and evaluate their equality weights in the same
    # binary-prefix pass. The standard shape specializes the 23 live start
    # coordinates; the generic path multiplies harmless fixed-zero factors.
    prefix_off_bits = HeapBuf(SIZE_BITS * (N_BLOCKS + 1))
    block_start_weight = HeapBuf(N_BLOCKS)
    for cert in unroll(0, 2):
        s = COUNT_SIDE * cert
        first = SIDE_BLOCK_START[s]
        first_bits = prefix_off_bits * GEN ** (SIZE_BITS * first)
        for bit in unroll(0, SIZE_BITS):
            first_bits[GEN ** bit] = 0
        for block in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            current_bits = prefix_off_bits * GEN ** (SIZE_BITS * block)
            next_bits = prefix_off_bits * GEN ** (SIZE_BITS * (block + 1))
            height_bits = height_group_bits * GEN ** (SIZE_BITS * BLOCK_HEIGHT_GROUP[block])
            if g_bus_mu == GEN ** 23:
                block_start_weight[GEN ** block] = offset_step_fixed(current_bits, height_bits, next_bits, assist_start, 23)
            else:
                block_start_weight[GEN ** block] = offset_step_fixed(current_bits, height_bits, next_bits, assist_start, SIZE_BITS)

    # The standard recursive shape has 21 length bits. There are far fewer
    # distinct symbolic heights than blocks, so evaluate each length weight
    # once and reuse it for every block in the group.
    height_group_weight = HeapBuf(N_HEIGHT_GROUPS)
    height_group_chain = HeapBuf((MU_CAP + 2) * N_HEIGHT_GROUPS)
    if g_bus_mu == GEN ** 23:
        if g_reduction_nu == GEN ** 20:
            for group in unroll(0, N_HEIGHT_GROUPS):
                length_bits = height_group_bits * GEN ** (SIZE_BITS * group)
                height_group_weight[GEN ** group] = point_weight_fixed(assist_length, length_bits, 21)
        else:
            for group in unroll(0, N_HEIGHT_GROUPS):
                length_bits = height_group_bits * GEN ** (SIZE_BITS * group)
                chain = height_group_chain * GEN ** ((MU_CAP + 2) * group)
                chain[GEN ** 0] = 1
                for xk in mul_range(1, assist_length_len_g):
                    chain[xk * GEN] = chain[xk] * (1 + assist_length[xk] + length_bits[xk])
                height_group_weight[GEN ** group] = chain[assist_length_len_g]
    else:
        for group in unroll(0, N_HEIGHT_GROUPS):
            length_bits = height_group_bits * GEN ** (SIZE_BITS * group)
            chain = height_group_chain * GEN ** ((MU_CAP + 2) * group)
            chain[GEN ** 0] = 1
            for xk in mul_range(1, assist_length_len_g):
                chain[xk * GEN] = chain[xk] * (1 + assist_length[xk] + length_bits[xk])
            height_group_weight[GEN ** group] = chain[assist_length_len_g]

    assist_batch_chain = HeapBuf(N_BLOCKS + 1)
    assist_batch_chain[GEN ** 0] = 0
    for i in unroll(0, push_count):
        block = SIDE_BLOCK_START[PUSH_SIDE] + i
        assist_batch_chain[GEN ** (i + 1)] = assist_batch_chain[GEN ** i] + assist_coeff[GEN ** block] * block_start_weight[GEN ** block] * height_group_weight[GEN ** BLOCK_HEIGHT_GROUP[block]]
    for i in unroll(0, count_count):
        block = SIDE_BLOCK_START[COUNT_SIDE] + i
        assist_batch_chain[GEN ** (push_count + i + 1)] = assist_batch_chain[GEN ** (push_count + i)] + assist_coeff[GEN ** block] * block_start_weight[GEN ** block] * height_group_weight[GEN ** BLOCK_HEIGHT_GROUP[block]]
    assist_overlap_out = StackBuf(1)
    if g_bus_mu == GEN ** 23:
        if g_reduction_nu == GEN ** 20:
            assist_overlap_out[0] = tight_overlap_start_length_points_fixed(bus_rho, zeta_full, assist_start, assist_length, 20, 23, 21)
        else:
            assist_overlap_out[0] = tight_overlap_start_length_points(bus_rho, zeta_full, assist_start, assist_length)
    else:
        assist_overlap_out[0] = tight_overlap_start_length_points(bus_rho, zeta_full, assist_start, assist_length)
    assert assist_terminal == assist_batch_chain[GEN ** (push_count + count_count)] * assist_overlap_out[0]
    claim_idx = N_BUS_CLAIMS

    # ---- stacked-bytecode reduction ----
    # The bytecode is ONE multilinear in BYTECODE_LOG + LOG2_BYTECODE_COLS
    # variables (BYTECODE_COLS encoding columns stacked along the selector
    # bits), with one source-row point shared by all eight columns.
    bytecode_sel = HeapBuf(LOG2_BYTECODE_COLS)
    for t in unroll(0, LOG2_BYTECODE_COLS):
        fs = squeeze(fs)
        sv = fs[0]
        bytecode_sel[GEN ** t] = sv
    bytecode_reduced = 0
    for c in unroll(0, BYTECODE_COLS):
        bytecode_reduced += eq_weight(bytecode_sel, LOG2_BYTECODE_COLS, c, 0) * bytecode_vals[GEN ** c]

    # ---- 6x per-table zerocheck (XOR, MUL, SET, DEREF, JUMP, BLAKE3) ----
    # For each table: eta, the zerocheck point r (tau samples), tau eq-trick
    # rounds (claim starts at 0), then the involved-column evaluations (pooled)
    # and the final AIR check claim == eq_acc * C_t(eta, evals).
    # RUNTIME round counts: tau_t is the certified announced log height
    # (dims_g[1 + t], certified by the count gadget). Round state threads
    # through heap chains exactly like the GKR trees.
    rho = HeapBuf(N_TABLES * TAU_CAP)
    zc_point_fs0 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_point_fs1 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_fs0 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_fs1 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_cursor = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_claim = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_eq = HeapBuf(N_TABLES * (TAU_CAP + 2))
    for t in unroll(0, N_TABLES):
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
            point_fs = [point_fs0[xk], point_fs1[xk]]
            point_fs = squeeze(point_fs)
            eq_r[xk] = point_fs[0]
            xkn = xk * GEN
            point_fs0[xkn] = point_fs[0]
            point_fs1[xkn] = point_fs[1]
        fs = [point_fs0[tau_g], point_fs1[tau_g]]
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
        fs = [round_fs0[tau_g], round_fs1[tau_g]]
        cursor = round_cursor[tau_g]
        claim = round_claim[tau_g]
        eq_acc = round_eq[tau_g]
        col_evals = StackBuf(AIR_COLS_CAP)
        for k in unroll(0, N_AIR_COLS[t]):
            fs, e, cursor = fs_next(fs, cursor)
            col_evals[k] = e
            claim_pool[GEN ** claim_idx] = e
            claim_cplen_g[GEN ** claim_idx] = tau_g  # cplen = tau_t
            claim_idx += 1
        # the table's AIR constraint at the final point (ev order = the table's
        # constraint_columns order; formulas mirror tables.rs eval_constraint).
        if t == TABLE_XOR:
            constraint_eval = (col_evals[4] + col_evals[0] * col_evals[1]) + eta * (col_evals[5] + col_evals[0] * col_evals[2]) + eta * eta * (col_evals[6] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[9] + col_evals[7] + col_evals[8])
        if t == TABLE_MUL:
            constraint_eval = (col_evals[4] + col_evals[0] * col_evals[1]) + eta * (col_evals[5] + col_evals[0] * col_evals[2]) + eta * eta * (col_evals[6] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[9] + col_evals[7] * col_evals[8])
        if t == TABLE_SET:
            constraint_eval = col_evals[2] + col_evals[0] * col_evals[1]
        if t == TABLE_DEREF:
            src = (1 + col_evals[8] + col_evals[9]) * col_evals[11] + col_evals[8] * (GEN * GEN * col_evals[12]) + col_evals[9] * col_evals[0]
            constraint_eval = (col_evals[4] + col_evals[0] * col_evals[1]) + eta * (col_evals[5] + col_evals[7] * col_evals[2]) + eta * eta * (col_evals[6] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[10] + src)
        if t == TABLE_JUMP:
            ft = GEN * col_evals[0]
            addrs = (col_evals[7] + col_evals[1] * col_evals[4]) + eta * (col_evals[8] + col_evals[1] * col_evals[5]) + eta * eta * (col_evals[9] + col_evals[1] * col_evals[6])
            eta3 = eta * eta * eta
            ind_def = eta3 * (col_evals[14] + col_evals[10] * col_evals[13])
            ind_nz = eta3 * eta * (col_evals[10] * (col_evals[14] + 1))
            sel_pc = eta3 * eta * eta * (col_evals[2] + col_evals[14] * col_evals[11] + (col_evals[14] + 1) * ft)
            sel_fp = eta3 * eta * eta * eta * (col_evals[3] + col_evals[14] * col_evals[12] + (col_evals[14] + 1) * col_evals[1])
            constraint_eval = addrs + ind_def + ind_nz + sel_pc + sel_fp
        if t == TABLE_BLAKE3:
            constraint_eval = (col_evals[7] + col_evals[0] * col_evals[1]) + eta * (col_evals[8] + col_evals[0] * col_evals[2]) + eta * eta * (col_evals[9] + col_evals[0] * col_evals[3]) + eta * eta * eta * (col_evals[10] + col_evals[0] * col_evals[4]) + eta * eta * eta * eta * (col_evals[11] + col_evals[0] * col_evals[5]) + eta * eta * eta * eta * eta * (col_evals[12] + col_evals[0] * col_evals[6])
        assert claim == eq_acc * constraint_eval

    # ---- public-input binding claim: MEM(r_m, 0..) = interp(pi0, pi1, r_m) ----
    fs = squeeze(fs)
    rm = fs[0]
    pi_interp = pi_0 + rm * (pi_0 + pi_1)  # MLE of the 2-cell public memory at the sampled point rm
    claim_pool[GEN ** claim_idx] = pi_interp
    claim_idx += 1

    # ---- flock zerocheck (univariate skip, k_skip = 6) ----
    tau_blake3_g = dims_g[GEN ** N_TABLES]  # the BLAKE3 table's certified tau
    # tau's reach is bounded: the count gadget gives tau < 34 (all flock
    # buffers are sized for that), and q_pkd's committed kappa =
    # LOG2_FIELD_BITS + tau feeds the certified size m, whose opening
    # dispatch bound caps tau well below any baked structure.
    # flock's sub-proof scalars are ordinary stream words (add_scalar on the
    # native side); the cursor walks them, fetching and observing each in one
    # step (fs_next) at the point the transcript binds it.
    # the full r vector: K_SKIP sampled skips, N_FIXED_CHALLENGE_ROUNDS fixed inner,
    # the rest sampled outer. r is the zerocheck eq-randomness the prover builds
    # round-1 FROM, so it is squeezed BEFORE round-1 is fetched (and round-1 before
    # z, which evaluates it).
    mr1cs_g = tau_blake3_g * GEN ** K_LOG  # runtime m = K_LOG + tau_5 (certified) in the exponent
    zerocheck_r = HeapBuf(mr1cs_g)
    for i in unroll(0, K_SKIP):
        fs = squeeze(fs)
        rv = fs[0]
        zerocheck_r[GEN ** i] = rv
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        zerocheck_r[GEN ** (K_SKIP + i)] = FIXED_CHALLENGES[i]
    # outer samples at runtime count: m = K_LOG + tau_5 (certified).
    flock_point_fs0 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs1 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs0[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[0]
    flock_point_fs1[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[1]
    for xi in mul_range(GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS), mr1cs_g):
        point_fs = [flock_point_fs0[xi], flock_point_fs1[xi]]
        point_fs = squeeze(point_fs)
        zerocheck_r[xi] = point_fs[0]
        xin = xi * GEN
        flock_point_fs0[xin] = point_fs[0]
        flock_point_fs1[xin] = point_fs[1]
    fs = [flock_point_fs0[mr1cs_g], flock_point_fs1[mr1cs_g]]
    # round-1 message (ab ‖ c, 2 * 2^K_SKIP words): fetch + observe each word as
    # it comes off the stream, then sample z.
    zc_round1 = HeapBuf(2 * 2 ** K_SKIP)
    for i in unroll(0, 2 * 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        zc_round1[GEN ** i] = w
    fs = squeeze(fs)  # cursor now sits at the multilinear round messages, walked below
    zerocheck_z = fs[0]
    # interpolate P^C(z) on the Lambda domain (phi8 nodes 64..128): prefix/
    # suffix numerator products with baked inverse denominators.
    lagrange_nums = StackBuf(2 ** K_SKIP)
    lag64(zerocheck_z, lagrange_nums, 2 ** K_SKIP)
    c_eval = 0  # P^C(z): Lagrange-interpolate the round-1 message over the Lambda nodes
    for i in unroll(0, 2 ** K_SKIP):
        c_eval += lagrange_nums[i] * LAGRANGE_INV_LAMBDA[i] * zc_round1[GEN ** (2 ** K_SKIP + i)]
    # combined interpolation at z over ALL 128 phi8 nodes (Lambda values only;
    # the S half is zero by the zerocheck identity). The Lambda-node numerators
    # reuse lagrange_nums: the full-domain product only adds the S-half factor.
    s_half_product = GEN ** 0  # the S-domain half of the combined interpolation (zero by the identity)
    for i in unroll(0, 2 ** K_SKIP):
        s_half_product *= (zerocheck_z + PHI8_NODES[i])
    combined_eval = 0
    for i in unroll(0, 2 ** K_SKIP):
        combined_eval += lagrange_nums[i] * LAGRANGE_INV_COMBINED[i] * (zc_round1[GEN ** i] + zc_round1[GEN ** (2 ** K_SKIP + i)])
    combined_eval *= s_half_product
    zc_running = combined_eval + c_eval  # the zerocheck running claim entering the multilinear rounds
    # multilinear rounds.
    mr1cs_rounds_g = mr1cs_g * INV_GEN ** 6  # runtime zerocheck mlv rounds: m - 6
    zerocheck_rhos = HeapBuf(mr1cs_rounds_g)
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        r_eq = zerocheck_r[GEN ** (K_SKIP + i)]
        fs, gamma_c, cursor = fs_next(fs, cursor)  # (gamma_c, g_inf) per round, walked in order
        fs, g_inf, cursor = fs_next(fs, cursor)
        gamma_ab = (zc_running + r_eq * gamma_c) * ONE_PLUS_CHALLENGE_INV[i]  # recover the g(alpha) evaluation from g(0)+g(1)=claim and the eq weight
        fs = squeeze(fs)
        rho_v = fs[0]
        zerocheck_rhos[GEN ** i] = rho_v
        zc_running = gamma_ab * (1 + rho_v) + gamma_c * rho_v + g_inf * rho_v * (1 + rho_v)
    # rounds N_FIXED_CHALLENGE_ROUNDS.. at runtime count: K_LOG + tau_5 - K_SKIP rounds total (certified).
    nmlv_g = tau_blake3_g * GEN ** (K_LOG - K_SKIP)
    flock_round_size = mr1cs_rounds_g * GEN ** 2
    flock_round_fs0 = HeapBuf(flock_round_size)
    flock_round_fs1 = HeapBuf(flock_round_size)
    flock_round_running = HeapBuf(flock_round_size)
    flock_round_cursor = HeapBuf(flock_round_size)  # the walking cursor, threaded like the fs state
    flock_round_fs0[GEN ** N_FIXED_CHALLENGE_ROUNDS] = fs[0]
    flock_round_fs1[GEN ** N_FIXED_CHALLENGE_ROUNDS] = fs[1]
    flock_round_running[GEN ** N_FIXED_CHALLENGE_ROUNDS] = zc_running
    flock_round_cursor[GEN ** N_FIXED_CHALLENGE_ROUNDS] = cursor
    for xi in mul_range(GEN ** N_FIXED_CHALLENGE_ROUNDS, nmlv_g):
        round_fs = [flock_round_fs0[xi], flock_round_fs1[xi]]
        round_running = flock_round_running[xi]
        r_eq = zerocheck_r[GEN ** K_SKIP * xi]
        cur_i = flock_round_cursor[xi]
        round_fs, gamma_c, cur_i = fs_next(round_fs, cur_i)
        round_fs, g_inf, cur_i = fs_next(round_fs, cur_i)
        gamma_ab = (round_running + r_eq * gamma_c) / (1 + r_eq)
        round_fs = squeeze(round_fs)
        rho_v = round_fs[0]
        zerocheck_rhos[xi] = rho_v
        round_running = gamma_ab * (1 + rho_v) + gamma_c * rho_v + g_inf * rho_v * (1 + rho_v)
        xin = xi * GEN
        flock_round_fs0[xin] = round_fs[0]
        flock_round_fs1[xin] = round_fs[1]
        flock_round_running[xin] = round_running
        flock_round_cursor[xin] = cur_i
    fs = [flock_round_fs0[nmlv_g], flock_round_fs1[nmlv_g]]
    zc_running = flock_round_running[nmlv_g]
    cursor = flock_round_cursor[nmlv_g]  # walked past all 2*n_mlv round words, now at a_eval
    # final: zc_running == a_eval * b_eval; observe both.
    fs, a_eval, cursor = fs_next(fs, cursor)
    fs, b_eval, cursor = fs_next(fs, cursor)
    ab_product = a_eval * b_eval  # zerocheck closes: running claim == a(r) * b(r)
    assert zc_running == ab_product

    # ---- flock lincheck (matrix evaluation DEFERRED) ----
    matrix_eval = StackBuf(1)
    hint_witness(matrix_eval[0:1], "matpart")
    fs = squeeze(fs)
    lincheck_alpha = fs[0]
    fs = squeeze(fs)
    lincheck_beta = fs[0]
    lc_running = lincheck_alpha * a_eval + b_eval + lincheck_beta  # lincheck seed: alpha*a + b + beta (batches the two matrix claims)
    lincheck_rs = HeapBuf(LINCHECK_ROUNDS)
    for i in unroll(0, LINCHECK_ROUNDS):
        fs, e1, cursor = fs_next(fs, cursor)  # (e1, e_inf) per round, walked in order
        fs, ei, cursor = fs_next(fs, cursor)
        fs = squeeze(fs)
        rv = fs[0]
        lincheck_rs[GEN ** i] = rv
        e0 = lc_running + e1
        c1q = e0 + e1 + ei
        lc_running = ei * rv * rv + c1q * rv + e0  # fold the degree-2 round poly at the challenge rv
    z_partial = HeapBuf(2 ** K_SKIP)  # post-sumcheck collapse: fetch + observe each word
    for i in unroll(0, 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        z_partial[GEN ** i] = w
    # final consistency: running == matpart (DEFERRED) + beta * pin term. The
    # const-pin column folds through the top-variable bindings: weight =
    # prod_j (bit_{klog-1-j}(PIN_COLUMN) ? r_j : 1+r_j), surviving z_partial index
    # = PIN_COLUMN low 6 bits.
    pin_term = lincheck_beta * eq_weight(lincheck_rs, LINCHECK_ROUNDS, PIN_COLUMN, K_LOG)
    pin_term *= z_partial[GEN ** (PIN_COLUMN % 2 ** K_SKIP)]
    matrix_part = matrix_eval[0]
    lincheck_final = matrix_part + pin_term  # running == deferred matrix eval + the const-pin column contribution
    assert lc_running == lincheck_final
    # fresh z_skip; w = <lagrange_S(r_inner_skip), z_partial> (phi8 nodes 0..64).
    fs = squeeze(fs)
    lincheck_z_skip = fs[0]
    skip_nums = StackBuf(2 ** K_SKIP)
    lag64(lincheck_z_skip, skip_nums, 0)
    lincheck_w = 0
    for i in unroll(0, 2 ** K_SKIP):
        lincheck_w += skip_nums[i] * LAGRANGE_INV_S[i] * z_partial[GEN ** i]

    # ---- dense Jagged opening: ring-switch fronts + claim combination ----
    s_hat_v = StackBuf(2 * FIELD_BITS)  # the two ring-switch slices (end the stream), fetched + observed in the loop below
    # Ring-switch claim 0 (ab): value lincheck_w, z_skip = lincheck_z_skip, x_outer[0] = lincheck_rs[LINCHECK_ROUNDS-1]
    # (x_inner_rest is the REVERSED lincheck round vector). Claim 1 (c): value
    # c_eval, z_skip = zerocheck_z, x_outer[0] = zerocheck_r[6].
    transposed_claims = StackBuf(2)
    rs_eq_vals = StackBuf(2)
    c_table = StackBuf(FIELD_BITS)
    z_vals = HeapBuf(2 * QPKD_VARS_CAP)
    r_dprime = StackBuf(LOG2_FIELD_BITS)
    for rs in unroll(0, 2):
        for i in unroll(0, FIELD_BITS):
            fs, w, cursor = fs_next(fs, cursor)
            s_hat_v[FIELD_BITS * rs + i] = w
        # claim check: weights[i] = lambda_{i&63}(z_skip) * eq(x_outer0, i>>6).
        if rs == 0:
            claim_z_skip = lincheck_z_skip
            claim_x_outer_0 = lincheck_rs[GEN ** (LINCHECK_ROUNDS - 1)]
            claim_val = lincheck_w
        else:
            claim_z_skip = zerocheck_z
            claim_x_outer_0 = zerocheck_r[GEN ** K_SKIP]
            claim_val = c_eval
        claim_nums = StackBuf(2 ** K_SKIP)
        lag64(claim_z_skip, claim_nums, 0)
        claim_check = 0
        for i in unroll(0, 2 ** K_SKIP):
            lagrange_w = claim_nums[i] * LAGRANGE_INV_S[i]
            claim_check += lagrange_w * ((1 + claim_x_outer_0) * s_hat_v[FIELD_BITS * rs + i] + claim_x_outer_0 * s_hat_v[FIELD_BITS * rs + 2 ** K_SKIP + i])  # claim = sum_i lambda_i(z_skip) * eq(x_outer0, i>>6) * s_hat_v[i]
        assert claim_check == claim_val
    # ONE r'' shared by both claims (each slice was absorbed before the
    # sample), so one eq tensor and one linearized coefficient table
    # serve the whole batch.
    for i in unroll(0, LOG2_FIELD_BITS):
        fs = squeeze(fs)
        rv = fs[0]
        r_dprime[i] = rv
    # Only eq(r'', i), i=0..6, is needed by the sparse correction to the
    # reversed-monomial trace-dual basis. These indices share four zero high
    # bits, so their common factor is computed once.
    correction_weights = StackBuf(LOG2_FIELD_BITS)
    correction_high = GEN ** 0
    for t in unroll(3, LOG2_FIELD_BITS):
        correction_high *= 1 + r_dprime[t]
    for i in unroll(0, LOG2_FIELD_BITS):
        correction_weight = correction_high
        for t in unroll(0, 3):
            if (i // (2 ** t)) % 2 == 1:
                correction_weight *= r_dprime[t]
            else:
                correction_weight *= 1 + r_dprime[t]
        correction_weights[i] = correction_weight
    # Factored c_k. The 128-term reversed-monomial sum is a seven-factor MLE
    # product; only the first seven dual-basis elements add corrections.
    for k in unroll(0, FIELD_BITS):
        c_main = RS_COEFF_ORBITS[RS_COEFF_ORBIT_WIDTH * k]
        for t in unroll(0, LOG2_FIELD_BITS):
            c_main *= 1 + r_dprime[t] * RS_COEFF_ORBITS[RS_COEFF_ORBIT_WIDTH * k + 1 + t]
        c_correction = 0
        for i in unroll(0, LOG2_FIELD_BITS):
            c_correction += correction_weights[i] * RS_COEFF_ORBITS[RS_COEFF_ORBIT_WIDTH * k + 1 + LOG2_FIELD_BITS + i]
        c_table[k] = c_main + c_correction
    for rs in unroll(0, 2):
        # Transposed claim T = sum_j x^j * L_w(shv_j). Both fixed 128-step
        # dimensions are unrolled; only proof-size-dependent loops remain
        # runtime loops in this verifier.
        x_pow = GEN ** 0
        transposed_claim = 0
        for j in unroll(0, FIELD_BITS):
            y_pow = s_hat_v[FIELD_BITS * rs + j]
            lin_eval = 0
            for k in unroll(0, FIELD_BITS):  # L_w(y) = sum_k c_k y^(2^k); y^(2^k) squares once per step
                lin_eval += c_table[k] * y_pow
                if k != FIELD_BITS - 1:
                    y_pow *= y_pow
            transposed_claim += x_pow * lin_eval
            if j != FIELD_BITS - 1:
                x_pow *= 2  # x = the field element 2 (the polynomial x)
        transposed_claims[rs] = transposed_claim
        # z_vals for eval_rs_eq (the x_outer tail), used at the opening terminal.
        if rs == 0:
            for t in unroll(0, LINCHECK_ROUNDS - 1):
                z_vals[GEN ** t] = lincheck_rs[GEN ** (LINCHECK_ROUNDS - 2 - t)]
            zv_lo = z_vals * GEN ** (LINCHECK_ROUNDS - 1)
            zr_hi = zerocheck_rhos * GEN ** LINCHECK_ROUNDS
            for xt in mul_range(1, tau_blake3_g):
                zv_lo[xt] = zr_hi[xt]
        else:
            # row 1 lives at the CAPACITY stride (QPKD_VARS_CAP); its length is the
            # runtime qpkdv.
            zv_hi = z_vals * GEN ** QPKD_VARS_CAP
            zcr7 = zerocheck_r * GEN ** (K_SKIP + 1)
            for xt in mul_range(1, tau_blake3_g * GEN ** (K_LOG - LOG2_FIELD_BITS)):
                zv_hi[xt] = zcr7[xt]
    # gamma-combine the two transposed sumcheck claims (computed in-circuit).
    fs = squeeze(fs)
    gamma_ab = fs[0]
    fs = squeeze(fs)
    gamma_c = fs[0]
    target = gamma_ab * transposed_claims[0] + gamma_c * transposed_claims[1]  # gamma-batch the two ring-switch claims into the opening's target

    # ---- Jagged dense layout: derive one cumulative boundary-bit chain ----
    # Table-row and used-memory bits were already Boolean-constrained and tied
    # to their announced words by log2_ceil_word.  The bytecode prefix is fixed
    # by the program.  A width-2^b block shifts its row count by b.
    # Power-of-two structural blocks use a one-hot height pinned to kappa.
    # Starting from zero, a Boolean full-adder derives every interval endpoint.
    col_bound_bits = HeapBuf(SIZE_BITS * (N_COMMITTED_COLS + 1))
    col_block_height_bits = HeapBuf(SIZE_BITS * N_COMMITTED_COLS)
    col_row_height_bits = HeapBuf(SIZE_BITS * N_COMMITTED_COLS)
    for bit in unroll(0, SIZE_BITS):
        col_bound_bits[GEN ** bit] = 0
    for c in unroll(0, N_COMMITTED_COLS):
        height_bits = col_block_height_bits * GEN ** (SIZE_BITS * c)
        row_height_bits = col_row_height_bits * GEN ** (SIZE_BITS * c)
        if COL_HEIGHT_KIND[c] == 0:
            # height = 2^kappa. The advice must be a Boolean one-hot vector,
            # whose decoded word is the certified power 2^kappa.
            kappa_g = kappa_base[GEN ** COL_HEIGHT_SRC[c]] * GEN ** COL_HEIGHT_ADJ[c]
            assert log(kappa_g) < SIZE_BITS
            hint_decompose_bits_exponent(height_bits, g_squares[kappa_g], SIZE_BITS)
            height_word = 0
            for bit in unroll(0, SIZE_BITS):
                hb = height_bits[GEN ** bit]
                assert hb * hb == hb
                height_word += hb * (2 ** bit)
            assert height_word == g_logs_pow2[kappa_g]
        elif COL_HEIGHT_KIND[c] == 1:
            table_bits = count_bits * GEN ** (COUNT_BITS * COL_HEIGHT_SRC[c])
            for bit in unroll(0, COL_BLOCK_LOG[c]):
                height_bits[GEN ** bit] = 0
            if COL_BLOCK_LOG[c] == 0:
                for bit in unroll(0, COUNT_BITS):
                    height_bits[GEN ** bit] = table_bits[GEN ** bit]
                for bit in unroll(COUNT_BITS, SIZE_BITS):
                    height_bits[GEN ** bit] = 0
            else:
                for bit in unroll(COL_BLOCK_LOG[c], SIZE_BITS):
                    height_bits[GEN ** bit] = table_bits[GEN ** (bit - COL_BLOCK_LOG[c])]
        elif COL_HEIGHT_KIND[c] == 2:
            for bit in unroll(0, COL_BLOCK_LOG[c]):
                height_bits[GEN ** bit] = 0
            if COL_BLOCK_LOG[c] == 0:
                for bit in unroll(0, COUNT_BITS):
                    height_bits[GEN ** bit] = memory_bits[GEN ** bit]
                for bit in unroll(COUNT_BITS, SIZE_BITS):
                    height_bits[GEN ** bit] = 0
            else:
                for bit in unroll(COL_BLOCK_LOG[c], SIZE_BITS):
                    height_bits[GEN ** bit] = memory_bits[GEN ** (bit - COL_BLOCK_LOG[c])]
        else:
            # BFCNT is a singleton with a program-bound bytecode prefix.
            for bit in unroll(0, SIZE_BITS):
                height_bits[GEN ** bit] = BYTECODE_USED_BITS[bit]

        # Padding correction uses the per-column row height (block height / width).
        for bit in unroll(0, SIZE_BITS - COL_BLOCK_LOG[c]):
            row_height_bits[GEN ** bit] = height_bits[GEN ** (bit + COL_BLOCK_LOG[c])]
        for bit in unroll(SIZE_BITS - COL_BLOCK_LOG[c], SIZE_BITS):
            row_height_bits[GEN ** bit] = 0

        start_bits = col_bound_bits * GEN ** (SIZE_BITS * c)
        end_bits = col_bound_bits * GEN ** (SIZE_BITS * (c + 1))
        carry = 0
        for bit in unroll(0, SIZE_BITS):
            sb = start_bits[GEN ** bit]
            hb = height_bits[GEN ** bit]
            end_bits[GEN ** bit] = sb + hb + carry
            # Majority(sb, hb, carry) over F_2, factored to one MUL:
            # sb*hb + sb*carry + hb*carry = (sb+carry)(sb+hb)+sb.
            carry = (sb + carry) * (sb + hb) + sb
        assert carry == 0  # the dense witness area fits in SIZE_BITS

    total_bits = col_bound_bits * GEN ** (SIZE_BITS * N_COMMITTED_COLS)
    # LIG_MIN_LOG_SIZE includes the PCS floor and the fixed structural floors
    # max(MIN_LOG_MEM, BYTECODE_LOG).  Above the memory floor, the two committed
    # memory prefixes already make the packed area large enough to embed their
    # logical row point.
    gmv, total_word, g_total = verify_log2_ceil(total_bits, g_logs_pow2, g_squares, LIG_MIN_LOG_SIZE, SIZE_BITS, 0)

    # Claims share only a handful of logical row points. Materialize each
    # distinct source/length once, with explicit zero high coordinates.
    claim_rows = HeapBuf(SIZE_BITS * N_CLAIM_ROWS)
    for group in unroll(0, N_CLAIM_ROWS):
        rep = CLAIM_ROW_REP[group]
        row = claim_rows * GEN ** (SIZE_BITS * group)
        if CLAIM_POINT_BUF[rep] == POINT_BUF_ZETA:
            cplen_g = claim_cplen_g[GEN ** rep]
            src = zeta * GEN ** CLAIM_POINT_OFF[rep]
            for xk in mul_range(1, cplen_g):
                row[xk] = src[xk]
            zero_ptr = row * cplen_g
            zero_len_g = GEN ** SIZE_BITS / cplen_g
            for xk in mul_range(1, zero_len_g):
                zero_ptr[xk] = 0
        elif CLAIM_POINT_BUF[rep] == POINT_BUF_RHO:
            cplen_g = claim_cplen_g[GEN ** rep]
            src = rho * GEN ** CLAIM_POINT_OFF[rep]
            for xk in mul_range(1, cplen_g):
                row[xk] = src[xk]
            zero_ptr = row * cplen_g
            zero_len_g = GEN ** SIZE_BITS / cplen_g
            for xk in mul_range(1, zero_len_g):
                zero_ptr[xk] = 0
        elif CLAIM_POINT_BUF[rep] == POINT_BUF_PI:
            row[GEN ** 0] = rm
            for bit in unroll(1, SIZE_BITS):
                row[GEN ** bit] = 0
        else:
            assert CLAIM_POINT_BUF[rep] == POINT_BUF_BUS_RHO
            row_nu_g = claim_bus_nu_g[GEN ** rep]
            for xk in mul_range(1, row_nu_g):
                row[xk] = bus_rho[xk]
            zero_ptr = row * row_nu_g
            zero_len_g = GEN ** SIZE_BITS / row_nu_g
            for xk in mul_range(1, zero_len_g):
                zero_ptr[xk] = 0
    # Compute the public-padding correction: Jagged commits only the real
    # prefix, while the arithmetization's claim includes its fixed pad suffix.
    pad_prefixes = HeapBuf(N_PAD_PREFIXES)
    for prefix in unroll(0, N_PAD_PREFIXES):
        row = claim_rows * GEN ** (SIZE_BITS * PAD_PREFIX_ROW[prefix])
        height_bits = col_row_height_bits * GEN ** (SIZE_BITS * PAD_PREFIX_COL[prefix])
        pad_prefixes[GEN ** prefix] = prefix_indicator(row, height_bits)

    opening_claim_values = HeapBuf(N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
            opening_claim_values[GEN ** j] = claim_pool[GEN ** j]
        elif CLAIM_POINT_BUF[j] == POINT_BUF_QPKD_BUS_RHO:
            # q_pkd remains the one aligned subcube for flock's ring-switch and
            # its strided VM-value claims; it has no public padding correction.
            opening_claim_values[GEN ** j] = claim_pool[GEN ** j]
        else:
            if CLAIM_PAD[j] == 0:
                opening_claim_values[GEN ** j] = claim_pool[GEN ** j]
            else:
                real_prefix = pad_prefixes[GEN ** CLAIM_PAD_PREFIX[j]]
                opening_claim_values[GEN ** j] = claim_pool[GEN ** j] + CLAIM_PAD[j] * (1 + real_prefix)
    # Every adjusted Jagged claim value is observed before its batching scalar,
    # exactly as in the native verifier.
    for j in unroll(0, N_CLAIMS):
        fs = obs(fs, opening_claim_values[GEN ** j])
    gamma_pool = HeapBuf(N_CLAIMS)
    fs = squeeze(fs)
    gamma = fs[0]
    gamma_powers = HeapBuf(N_CLAIMS)
    gv = 1
    for rank in unroll(0, N_CLAIMS):
        gamma_powers[GEN ** rank] = gv
        gv *= gamma
    for j in unroll(0, N_CLAIMS):
        weight = gamma_powers[GEN ** CLAIM_GAMMA_RANK[j]]
        gamma_pool[GEN ** j] = weight
        target += weight * opening_claim_values[GEN ** j]

    # ================= the Ligerito opening core (Jagged dense q) ===========

    # Dispatch on m = max(log2_ceil(total real area), LIG_MIN_LOG_SIZE).
    sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN): the match_range arm index selecting the opening candidate
    assert log(sel) < LIG_N_CANDIDATES
    sumcheck_target, fold_challenges, final_msg, inner_total, yr_log_n_g, fold_cap_g = match_range(log(sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], target, commit_root_0, commit_root_1, cursor))
    # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
    # (the telescoped product formula; z powers evolve by squaring per k).
    # QPKD_VARS_CAP = tau_5 + (K_LOG - LOG2_FIELD_BITS), exponent-additive from the certified announced log. Walk the runtime coordinates outside and the fixed 128 Frobenius powers inside: each coordinate loads its opening challenge once, evolves z by squaring in registers, and advances one contiguous 128-product row. This is the same product formula as the k-major form, without 128 separate runtime loops or a stored z-power table.
    qpkdv_g = tau_blake3_g * GEN ** (K_LOG - LOG2_FIELD_BITS)
    for rs in unroll(0, 2):
        prod_chains = HeapBuf((qpkdv_g * GEN) ** FIELD_BITS)
        z_row_src = z_vals * GEN ** (QPKD_VARS_CAP * rs)
        for k in unroll(0, FIELD_BITS):
            prod_chains[GEN ** k] = 1
        for x_round in mul_range(1, qpkdv_g):
            zv = z_row_src[x_round]
            oq = 1 + fold_challenges[x_round]
            prod_row = prod_chains * x_round ** FIELD_BITS
            prod_row_next = prod_row * GEN ** FIELD_BITS
            for k in unroll(0, FIELD_BITS):
                prod_row_next[GEN ** k] = prod_row[GEN ** k] * (zv + oq)
                if k != FIELD_BITS - 1:
                    zv *= zv
        prod_final = prod_chains * qpkdv_g ** FIELD_BITS
        e_acc = 0
        for k in unroll(0, FIELD_BITS):
            e_acc += c_table[k] * prod_final[GEN ** k]
        rs_eq_vals[rs] = e_acc
    # q_pkd is deliberately the first dense Jagged column, so its selector is
    # all-zero. Extend the ring-switch weight across the remaining ris coords.
    rs_weight = gamma_ab * rs_eq_vals[0] + gamma_c * rs_eq_vals[1]
    rs_len_g = fold_cap_g / qpkdv_g
    assert log(rs_len_g) < SIZE_BITS
    ris_q = fold_challenges * qpkdv_g
    rsw_chain = HeapBuf(SIZE_BITS + 1)
    rsw_chain[GEN ** 0] = rs_weight
    for xk in mul_range(1, rs_len_g):
        rsw_chain[xk * GEN] = rsw_chain[xk] * (1 + ris_q[xk])
    rs_weight = rsw_chain[rs_len_g]

    # The VM value claims routed into fixed q_pkd slots use the same aligned
    # offset-zero subcube. Evaluate their ris part directly; their residual-y
    # selector is also zero, so they multiply final_msg[0] below.
    qpkd_claim_weight = 0
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
            zptr = zeta * GEN ** CLAIM_POINT_OFF[j]
            cplen_g = claim_cplen_g[GEN ** j]
            qpkd_claim_weight += gamma_pool[GEN ** j] * qpkd_plain_weight(fold_challenges, zptr, cplen_g, cplen_g, CLAIM_QPKD_SLOT[j], qpkdv_g, fold_cap_g)
        elif CLAIM_POINT_BUF[j] == POINT_BUF_QPKD_BUS_RHO:
            cplen_g = claim_cplen_g[GEN ** j]
            qpkd_claim_weight += gamma_pool[GEN ** j] * qpkd_plain_weight(fold_challenges, bus_rho, cplen_g, claim_bus_nu_g[GEN ** j], CLAIM_QPKD_SLOT[j], qpkdv_g, fold_cap_g)

    # Contract every Basic Jagged indicator with the final Ligerito message.
    # A second dispatch on the already-certified commitment size bakes both
    # the folded prefix length and the residual-message shape into straight-
    # line width-four contractions.
    jagged_sum = match_range(log(sel), range(0, LIG_N_CANDIDATES), lambda m_idx: jagged_terminal(m_idx, fold_challenges, final_msg, claim_rows, col_bound_bits, gamma, gamma_powers))
    # q_pkd occupies [0, 2^qpkdv), hence its residual y selector is zero.
    inner_sum = inner_total + jagged_sum + (rs_weight + qpkd_claim_weight) * final_msg[GEN ** 0]
    assert inner_sum == sumcheck_target


    # ---- export this sub-proof's deferred-claim data to the caller ----
    # defer_out layout, offsets after the [0..KBC) shared bytecode point
    # (SEL = LOG2_BYTECODE_COLS, LCR = LINCHECK_ROUNDS):
    #   +0..SEL bytecode_sel | +SEL bytecode_reduced | +SEL+1 alpha
    #   | +SEL+2 z_skip | +SEL+3.. zrho | +SEL+3+LCR.. lincheck rs
    #   | +SEL+3+2*LCR.. z_partial (2^K_SKIP) | +SEL+3+2^K_SKIP+2*LCR matpart.
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = bus_rho[GEN ** k]
    for k in unroll(0, LOG2_BYTECODE_COLS):
        defer_out[GEN ** (BYTECODE_LOG + k)] = bytecode_sel[GEN ** k]
    defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS)] = bytecode_reduced
    defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 1)] = lincheck_alpha
    defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 2)] = zerocheck_z
    for k in unroll(0, LINCHECK_ROUNDS):
        defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + k)] = zerocheck_rhos[GEN ** k]
        defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + LINCHECK_ROUNDS + k)] = lincheck_rs[GEN ** k]
    for k in unroll(0, 2 ** K_SKIP):
        defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 * LINCHECK_ROUNDS + k)] = z_partial[GEN ** k]
    defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 ** K_SKIP + 2 * LINCHECK_ROUNDS)] = matrix_eval[0]
    return


def main():
    # NSUB sub-proofs of the fixed inner program: verify each (verify_sub),
    # then aggregate their deferred claims. The fresh aggregation transcript
    # RLC-batches the bytecode and matrix claims through two sumchecks; only
    # the three reduced claims (evaluated natively by the outer verifier)
    # reach this guest's public input.
    sub_pis = HeapBuf(NSUB * 2)
    hint_witness(sub_pis[0:NSUB * 2], "sub_pis")
    # The FS seed — ONE digest of everything fixed about the inner environment
    # (the flock circuit family, the inner program bytecode) — rides the
    # recursion's public input: hinted here, it leads every sub's transcript
    # and is folded into own_pi below, so the outer statement fixes the whole
    # proving environment with one word pair.
    fs_seed = StackBuf(2)
    hint_witness(fs_seed[0:2], "fs_seed")
    bc_sumcheck_msgs = HeapBuf(2 * BYTECODE_VARS)
    hint_witness(bc_sumcheck_msgs[0:2 * BYTECODE_VARS], "bc_sumcheck_msgs")
    mat_sumcheck_msgs = HeapBuf(4 * K_LOG)
    hint_witness(mat_sumcheck_msgs[0:4 * K_LOG], "mat_sumcheck_msgs")
    bc_star_hint = StackBuf(1)
    hint_witness(bc_star_hint[0:1], "bc_star_hint")
    mat_stars_hint = StackBuf(2)
    hint_witness(mat_stars_hint[0:2], "mat_stars_hint")
    # exponent-domain lookup tables, shared read-only across every sub-proof.
    g_logs_pow2, g_squares = exponent_tables()

    # per-sub deferred-claim regions (layout: see verify_sub's defer_out)
    defer = HeapBuf(NSUB * DEFER_SIZE)

    for sub in unroll(0, NSUB):
        verify_sub(sub_pis[GEN ** (2 * sub)], sub_pis[GEN ** (2 * sub + 1)], fs_seed[0], fs_seed[1], g_logs_pow2, g_squares, defer * GEN ** (sub * DEFER_SIZE))

    # ================= aggregation: batch the deferred claims =================
    # A fresh transcript absorbs every deferred claim (points and values),
    # samples the RLC coefficients, and verifies the two batching sumchecks of
    # doc.tex §Deferred evaluation claims. Only the reduced claims (one per
    # fixed polynomial) reach the public input.
    agg_fs = [0, 0]
    for sub in unroll(0, NSUB):
        agg_fs = obs(agg_fs, sub_pis[GEN ** (2 * sub)])
        agg_fs = obs(agg_fs, sub_pis[GEN ** (2 * sub + 1)])
        # the deferred-claim region is one contiguous run in absorb order.
        for k in unroll(0, DEFER_SIZE):
            agg_fs = obs(agg_fs, defer[GEN ** (sub * DEFER_SIZE + k)])

    # ---- bytecode batching sumcheck (BYTECODE_VARS variables, NSUB claims) ----
    gamma_bc = StackBuf(NSUB)
    bc_running = 0
    for t in unroll(0, NSUB):
        agg_fs = squeeze(agg_fs)
        gv = agg_fs[0]
        gamma_bc[t] = gv
        bc_running += gv * defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS)]
    bc_point = HeapBuf(BYTECODE_VARS)
    for rd in unroll(0, BYTECODE_VARS):
        agg_fs, msg_g1, c = fs_next(agg_fs, bc_sumcheck_msgs * GEN ** (2 * rd))
        agg_fs, msg_ginf, c = fs_next(agg_fs, c)
        agg_fs = squeeze(agg_fs)
        rv = agg_fs[0]
        bc_point[GEN ** rd] = rv
        g_zero = bc_running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        bc_running = msg_ginf * rv * rv + c_one * rv + g_zero  # fold the degree-2 batching-sumcheck round at rv
    # terminal: W(r*) in-circuit; the reduced bytecode claim B(r*) is deferred.
    bc_weight = 0
    for t in unroll(0, NSUB):
        e = GEN ** 0
        for k in unroll(0, BYTECODE_LOG):
            e *= (1 + defer[GEN ** (t * DEFER_SIZE + k)] + bc_point[GEN ** k])
        for k in unroll(0, LOG2_BYTECODE_COLS):
            e *= (1 + defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + k)] + bc_point[GEN ** (BYTECODE_LOG + k)])
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
        mat_running += gv * defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 ** K_SKIP + 2 * LINCHECK_ROUNDS)]
    mat_point = HeapBuf(2 * K_LOG)
    for rd in unroll(0, 2 * K_LOG):
        agg_fs, msg_g1, c = fs_next(agg_fs, mat_sumcheck_msgs * GEN ** (2 * rd))
        agg_fs, msg_ginf, c = fs_next(agg_fs, c)
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
    eq_rows = HeapBuf(2 ** (K_SKIP + 1) - 2)
    eqtree(mat_point, eq_rows, K_SKIP)
    eq_cols = HeapBuf(2 ** (K_SKIP + 1) - 2)
    eqtree(mat_point * GEN ** K_LOG, eq_cols, K_SKIP)
    weight_a = 0
    weight_b = 0
    for t in unroll(0, NSUB):
        z_skip_t = defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 2)]
        row_nums = StackBuf(2 ** K_SKIP)
        lag64(z_skip_t, row_nums, 0)
        row_weight = 0
        for i in unroll(0, 2 ** K_SKIP):
            row_weight += row_nums[i] * LAGRANGE_INV_S[i] * eq_rows[GEN ** (2 ** K_SKIP - 2 + i)]
        for k in unroll(0, LINCHECK_ROUNDS):
            row_weight *= (1 + defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + k)] + mat_point[GEN ** (K_SKIP + k)])
        col_weight = 0
        for i in unroll(0, 2 ** K_SKIP):
            col_weight += defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 * LINCHECK_ROUNDS + i)] * eq_cols[GEN ** (2 ** K_SKIP - 2 + i)]
        for j in unroll(0, LINCHECK_ROUNDS):
            col_weight *= (1 + defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + LINCHECK_ROUNDS + j)] + mat_point[GEN ** (2 * K_LOG - 1 - j)])
        weight_u = row_weight * col_weight
        weight_a += gamma_mat[t] * defer[GEN ** (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 1)] * weight_u
        weight_b += gamma_mat[t] * weight_u
    a_star = mat_stars_hint[0]
    b_star = mat_stars_hint[1]
    mat_final = a_star * weight_a + b_star * weight_b
    assert mat_running == mat_final

    # ---- bind the FS seed + sub statements + reduced claims to the PI ----
    out_fs = [0, 0]
    out_fs = obs(out_fs, fs_seed[0])  # the inner proving environment is part of the public statement
    out_fs = obs(out_fs, fs_seed[1])
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
    assert own_pi_0 == out_word_0  # the guest's OWN public input == blake3 of (inner digest | sub statements | reduced claims)
    assert own_pi_1 == out_word_1
    return
