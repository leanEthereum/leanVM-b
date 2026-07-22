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
# 127 - SECURITY_BITS (see leaf::grand_product_grinding_bits).
BUS_GRIND_SHIFT = BUS_GRIND_SHIFT_PLACEHOLDER

# Bus blocks, flattened across the 3 sides (side s covers blocks
# [SIDE_BLOCK_START[s], SIDE_BLOCK_START[s+1])). The block STRUCTURE is
# protocol-fixed and baked: each block's coord range [BLOCK_COORD_OFF,
# +BLOCK_COORD_COUNT), per coord COORD_TYPE (0=const, 1=col, 2=gcol, 3=index,
# 4=public bytecode; named COORD_KIND_* below), COORD_CONST (the const value, else 0), COORD_PAD_VAL
# (its default-padding fingerprint value), and the kappa SOURCE map
# (BLOCK_KAPPA_SRC/ADJ: 0=const adj, 1=log_mem, 2+t=tau_t). The block SHAPES
# are all reconstructed at runtime from the certified logs: kappa directly,
# the padding delta and selector bits by pinned advice-decompositions.
# Coord kinds (COORD_TYPE codes, mirroring leaf.rs::Coord):
COORD_KIND_CONST = 0
COORD_KIND_COL = 1
COORD_KIND_GCOL = 2
COORD_KIND_INDEX = 3
COORD_KIND_PUBLIC = 4
# BLOCK_REAL_TABLE: the table whose count is the block's real row count, or
# REAL_IS_FULL_CUBE for the shared blocks (real = 2^kappa, no padding).
REAL_IS_FULL_CUBE = 6
SIDE_BLOCK_START = SIDE_BLOCK_START_PLACEHOLDER
N_BLOCKS = N_BLOCKS_PLACEHOLDER
BLOCK_KAPPA_SRC = BLOCK_KAPPA_SRC_PLACEHOLDER
BLOCK_KAPPA_ADJ = BLOCK_KAPPA_ADJ_PLACEHOLDER
BLOCK_REAL_TABLE = BLOCK_REAL_TABLE_PLACEHOLDER
BLOCK_SIDE = BLOCK_SIDE_PLACEHOLDER
BLOCK_COORD_OFF = BLOCK_COORD_OFF_PLACEHOLDER
BLOCK_COORD_COUNT = BLOCK_COORD_COUNT_PLACEHOLDER
COORD_TYPE = COORD_TYPE_PLACEHOLDER
COORD_CONST = COORD_CONST_PLACEHOLDER
COORD_PAD_VAL = COORD_PAD_VAL_PLACEHOLDER
# Claim dedup: push/pull share their GKR point, so a column read by two blocks
# with the same kappa (across OR within the sides) is streamed and opened ONCE.
# Per coord: COORD_FRESH = 1 on the first occurrence (read the stream, fill
# pool slot COORD_CLAIM_SLOT), 0 on a duplicate (reuse that slot). The count
# side has its own point, so its claims never dedup against the pair's.
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
# The two ring-switch fronts
# (claim check in-circuit; the tensor transpose + eval_rs_eq DEFERRED); the
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
# Committed-column real-height sources, in dense Jagged order. KIND 0 is the
# full cube 2^(kappa_base[SRC] + ADJ); KIND 1 is the announced row count of
# table SRC. Their sum determines the dense PCS size.
N_COMMITTED_COLS = N_COMMITTED_COLS_PLACEHOLDER
COL_HEIGHT_KIND = COL_HEIGHT_KIND_PLACEHOLDER
COL_HEIGHT_SRC = COL_HEIGHT_SRC_PLACEHOLDER
COL_HEIGHT_ADJ = COL_HEIGHT_ADJ_PLACEHOLDER
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
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_POINT_OFF = CLAIM_POINT_OFF_PLACEHOLDER
# Dense Jagged column index and fixed public pad value for each pooled claim.
CLAIM_COL = CLAIM_COL_PLACEHOLDER
CLAIM_PAD = CLAIM_PAD_PLACEHOLDER
CLAIM_QPKD_SLOT = CLAIM_QPKD_SLOT_PLACEHOLDER
N_CLAIM_ROWS = N_CLAIM_ROWS_PLACEHOLDER
CLAIM_ROW_GROUP = CLAIM_ROW_GROUP_PLACEHOLDER
CLAIM_ROW_REP = CLAIM_ROW_REP_PLACEHOLDER
QPKD_VARS_CAP = QPKD_VARS_CAP_PLACEHOLDER
# Ring-switch trace-dual basis: bit_i(y) = Tr(TRACE_DUAL_BASIS[i] * y). Any eq-weighted
# bit-sum is then the linearized polynomial L_w(y) = sum_k c_k y^(2^k) with
# c_k = sum_i w_i TRACE_DUAL_BASIS[i]^(2^k); since squaring is one MUL, the tensor
# transpose and eval_rs_eq run in-circuit (doc.tex, ring-switch section).
TRACE_DUAL_BASIS = TRACE_DUAL_BASIS_PLACEHOLDER
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


def verify_log2_ceil(bits_buf, g_logs_pow2, g_squares, floor: Const, nbits: Const):
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


def log2_ceil_word(value, g_logs_pow2, g_squares, floor: Const, nbits: Const):
    # g^log2_ceil(value) for a concrete integer `value`. The bits are hinted HERE
    # (hint_decompose_bits), not by the caller, then tied back to `value`. Returns
    # (g_log, g^value).
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits(bits, value, nbits)
    g_log, word, g_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits)
    assert word == value  # the hinted bits are exactly value's bits (so value < 2^nbits)
    return g_log, g_value


def g_power_of_word(value, g_squares, nbits: Const):
    # g^value for a concrete integer `value` < 2^nbits: advice-decompose its
    # bits, tie them back to the word, and assemble Π g^(bit_j·2^j).
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits(bits, value, nbits)
    word = 0
    g_value = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits[GEN ** j]
        assert bit * bit == bit
        word += bit * (2 ** j)
        g_value *= (1 + bit * (g_squares[GEN ** j] + 1))
    assert word == value
    return g_value


def log2_ceil_in_the_exponent(g_N, g_logs_pow2, g_squares, floor: Const, nbits: Const):
    # Return g^log2_ceil(N) given g_N = g^N (N < 2^nbits). There is no in-circuit
    # log, so the prover hints N's bits (hint_decompose_bits_exponent); they are
    # verified and tied back: g^(the value the bits decode to) must equal g_N.
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits_exponent(bits, g_N, nbits)
    g_log, word, g_bits_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits)
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


def jagged_prefix_fixed(row_index_weights, start_bits, end_bits, nbits: Const):
    # Candidate-specialized straight-line prefix. Keeping the four states in a
    # scalar chain avoids both recursive VM frames and intermediate memory.
    s0 = 1
    s1 = 0
    s2 = 0
    s3 = 0
    for bit in unroll(0, nbits):
        weights = row_index_weights * GEN ** (4 * bit)
        s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, weights[GEN ** 0], weights[GEN ** 1], weights[GEN ** 2], weights[GEN ** 3], start_bits[GEN ** bit], end_bits[GEN ** bit])
    return s0, s1, s2, s3


def jagged_reverse_step(v0, v1, v2, v3, w0, w1, w2, w3, row_bit, start_bit, end_bit):
    # Contract both Boolean choices of one index coordinate at once. `v` is
    # the continuation for index bit zero and `w` for index bit one; the output
    # is the continuation as seen by each of the four incoming ROBP states.
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


def jagged_contract(final_msg, row_point, start_bits, end_bits, fold_bits: Const, log_len: Const, init0, init1, init2, init3):
    # Reverse-contract the residual Boolean-index ROBP against final_msg. The
    # layers contain fewer than 2 * 2^log_len width-four vectors in total.
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
            o0, o1, o2, o3 = jagged_reverse_step(layers[v], layers[v + 1], layers[v + 2], layers[v + 3], layers[w], layers[w + 1], layers[w + 2], layers[w + 3], row_point[GEN ** (fold_bits + bit)], start_bits[GEN ** (fold_bits + bit)], end_bits[GEN ** (fold_bits + bit)])
            out = next_off + 4 * t
            layers[out] = o0
            layers[out + 1] = o1
            layers[out + 2] = o2
            layers[out + 3] = o3
        layer_off = next_off
        layer_len = next_len
        next_off = next_off + 4 * next_len
    return init0 * layers[layer_off] + init1 * layers[layer_off + 1] + init2 * layers[layer_off + 2] + init3 * layers[layer_off + 3]


def jagged_terminal(m_idx: Const, fold_challenges, final_msg, claim_rows, col_start_bits, col_end_bits, gamma_pool):
    row_index_weights = HeapBuf(4 * N_CLAIM_ROWS * SIZE_BITS)
    for group in unroll(0, N_CLAIM_ROWS):
        row = claim_rows * GEN ** (SIZE_BITS * group)
        weights = row_index_weights * GEN ** (4 * SIZE_BITS * group)
        for bit in unroll(0, LIG_TOTAL_FOLDS[m_idx]):
            row_bit = row[GEN ** bit]
            index_bit = fold_challenges[GEN ** bit]
            rx = row_bit * index_bit
            weights[GEN ** (4 * bit)] = 1 + row_bit + index_bit + rx
            weights[GEN ** (4 * bit + 1)] = row_bit + rx
            weights[GEN ** (4 * bit + 2)] = index_bit + rx
            weights[GEN ** (4 * bit + 3)] = rx
    total = 0
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] != POINT_BUF_QPKD:
            row = claim_rows * GEN ** (SIZE_BITS * CLAIM_ROW_GROUP[j])
            start_bits = col_start_bits * GEN ** (SIZE_BITS * CLAIM_COL[j])
            end_bits = col_end_bits * GEN ** (SIZE_BITS * CLAIM_COL[j])
            weights = row_index_weights * GEN ** (4 * SIZE_BITS * CLAIM_ROW_GROUP[j])
            p0, p1, p2, p3 = jagged_prefix_fixed(weights, start_bits, end_bits, LIG_TOTAL_FOLDS[m_idx])
            folded = jagged_contract(final_msg, row, start_bits, end_bits, LIG_TOTAL_FOLDS[m_idx], LIG_YR_LOG_LEN[m_idx], p0, p1, p2, p3)
            total += gamma_pool[GEN ** j] * folded
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


def verify_sub(pi_0, pi_1, seed_0, seed_1, delta_pows, g_logs_pow2, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement
    # (pi_0, pi_1). All proof data is hinted HERE: each call pops the next
    # sub-proof's entry of every witness stream, so the body lowers once and
    # main just calls it per statement. `delta_pows` (the dual-basis Frobenius
    # table) and the g_logs_pow2/g_squares lookup tables are shared
    # read-only tables built once in main; the deferred-claim data is written
    # to `defer_out`.
    #
    # Flow (mirrors cpu::verify):
    #   1. seed the Fiat-Shamir sponge from the statement + program digest;
    #   2. announced sizes, then certify every structural log against them
    #      (count gadget log2_ceil: tau per table, log_mem);
    #   3. bind the commitment root; bus grinding (grind_check, runtime
    #      bit count); ONE RLC-batched GKR for all three trees (count padded
    #      to the pair's depth) at runtime depth, ONE shared point zeta;
    #   4. derive the block kappas, certify the GKR side depths; balance check
    #      with advice-decomposed padding ladders; 3x leaf decomposition
    #      against the GKR claims (pooling the committed-coordinate claims);
    #      the stacked-bytecode reduction (deferred);
    #   5. six AIR zerochecks at the certified taus (sumcheck_round3);
    #   6. public-input claim + BLAKE3 pin claims (telescoped prefix MLE);
    #   7. flock reduction: univariate-skip zerocheck + lincheck (matrix
    #      evaluation deferred);
    #   8. ring-switch fronts (shared r'', linearized transpose in-circuit);
    #   9. gamma-combine everything, certify the committed size m, dispatch
    #      the stacked Ligerito opening (open_stacked), and assert its
    #      eval_b terminal;
    #  10. export the deferred-claim region for the aggregation.
    # Claim pool: values of every committed-coordinate claim, in decompose order
    # (their points are the GKR ζ's, resolvable from the baked block structure).
    claim_pool = HeapBuf(N_CLAIMS)
    # certified low dimension (cplen) per pooled claim, filled as the pool is
    # built (from the in-scope certified kappa/tau); the terminal pins each
    # claim's hinted lengths against it.
    claim_cplen_g = HeapBuf(N_CLAIMS)
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

    # ---- announced sizes: log_mem + 6 row counts (observed, then certified) ----
    sizes = StackBuf(N_TABLES + 1)
    for i in unroll(0, N_TABLES + 1):
        fs, x, cursor = fs_next(fs, cursor)
        sizes[i] = x

    # ---- structural logs: certify g^log_mem, compute the taus ----
    # The stream announced the sizes as integer WORDS; the shape-generic phases
    # need them as G-POWERS (loop bounds, match_range scrutinees). dims_g[0] =
    # g^log_mem arrives as a hint pinned to the word; dims_g[1 + t] = g^tau_t
    # is computed by the count gadget.
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_5], all computed
    # log_mem is announced AS a log (an integer word L): g^L is assembled from
    # L's advice-decomposed bits — no hint, no g^j -> j lookup table.
    g_log_mem = g_power_of_word(sizes[0], g_squares, COUNT_BITS)
    assert log(g_log_mem) < COUNT_BITS
    dims_g[GEN ** 0] = g_log_mem
    # count gadget: g^tau_t = log2_ceil_word(count_t), which also returns
    # g^count_t (for the padding-surplus certification).
    count_gpows = HeapBuf(N_TABLES)
    for t in unroll(0, N_TABLES):
        g_tau, g_count = log2_ceil_word(sizes[t + 1], g_logs_pow2, g_squares, FLOORS[t], COUNT_BITS)
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
    # The ONE bus depth, COMPUTED (not hinted): mu = log2_ceil(Σ_b 2^κ_b) over
    # PUSH's blocks — pull matches by pairing, the count tree is padded to it.
    push_total = GEN ** 0
    for b in unroll(SIDE_BLOCK_START[PUSH_SIDE], SIDE_BLOCK_START[PUSH_SIDE + 1]):
        push_total *= g_squares[block_kappa[GEN ** b]]  # g^(sum of 2^kappa)
    g_bus_mu = log2_ceil_in_the_exponent(push_total, g_logs_pow2, g_squares, 0, SIZE_BITS)
    zeta = HeapBuf(g_bus_mu)  # the ONE shared GKR point: exactly mu coords

    # ---- commitment root (2 words), kept for the opening phase ----
    fs, commit_root_0, cursor = fs_next(fs, cursor)
    fs, commit_root_1, cursor = fs_next(fs, cursor)

    # ---- bus: grinding FIRST, then α and γ (the PoW covers both) ----
    # grinding nonce: raw stream word (NOT observed), PoW-checked, then bound.
    nonce = cursor[GEN ** 0]
    cursor *= GEN
    # Bus grind bits = push.mu - 7 (= SECURITY + push.mu + 1 - 128; see
    # leaf::grand_product_grinding_bits), with g_bus_mu computed above from the
    # derived block kappas.
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

    # ---- per-block shape data ----
    # kappa and the bus depth were derived above; the padding-surplus and
    # selector bits are advice-decomposed at their use sites (balance and
    # decompose sections) and pinned there — never left to a single aggregate
    # identity, which does not bind a high-entropy hint in this smooth field.
    idxc_tab = HeapBuf(SIZE_BITS)
    for t in unroll(0, SIZE_BITS):
        idxc_tab[GEN ** t] = INDEX_MLE_FACTORS[t]

    # ---- bus-leaf packing offsets (for the selector certification) ----
    # Each side's blocks tile its leaf cube; block b sits at offset_b. The
    # hinted order (sort_order) is only PERMUTATION-checked; offsets then
    # accumulate as g^offset = Π_{earlier} g^(2^κ). The decompose section pins
    # each block's selector bits against this offset, forcing κ-alignment — no
    # sort/tie-break check needed: alignment + consecutive offsets force a
    # valid tiling, and the grand product is position-independent, so any
    # tiling is sound.
    sort_order = HeapBuf(N_BLOCKS)
    hint_witness(sort_order[0:N_BLOCKS], "sort_order")
    block_side_tab = HeapBuf(N_BLOCKS)  # global block -> its side
    for b in unroll(0, N_BLOCKS):
        block_side_tab[GEN ** b] = BLOCK_SIDE[b]
    block_off_g = HeapBuf(N_BLOCKS)  # g^offset per block, keyed by global index
    # Pull's blocks mirror push's and share zeta, so the decompose reuses push's
    # per-block eq_hi outright: only push and count need offsets here (pull's
    # sort_order slots go unread).
    for cert in unroll(0, 2):
        s = COUNT_SIDE * cert  # PUSH_SIDE (0), then COUNT_SIDE (2)
        g_off = GEN ** 0
        for r in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            global_g = sort_order[GEN ** r]      # g^{global block index at this rank}
            assert log(global_g) < N_BLOCKS      # a valid block index
            assert block_side_tab[global_g] == s  # ...belonging to THIS side
            block_off_g[global_g] = g_off        # write-once: a repeat collides;
            g_off *= g_squares[block_kappa[global_g]]  # an omission fails the
    #                                              # decompose's offset read.

    # ---- balance: push_root · d_pull == pull_root · d_push ----
    # Each side's grand product includes its padding rows: block b contributes
    # (γ + fp_b)^DELTA_b, where fp_b is the padding row's fingerprint and
    # DELTA_b = 2^κ − real its row count. Multiplying each root by the OTHER
    # side's padding product cancels the padding, so the REAL rows must balance.
    # DELTA's bits (advice-decomposed from g^DELTA = g^(2^κ) / g^real) drive the
    # (γ+fp)^DELTA ladder and are pinned by g^real · g^DELTA == g^(2^κ); real is
    # count_t for table blocks, 2^κ for shared blocks (DELTA = 0). An unpinned
    # DELTA would forge the balance (dlog is cheap in this field).
    pad_products = HeapBuf(2)
    for s in unroll(0, 2):
        side_pad_product = GEN ** 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            pad_fp = 0
            alpha_pow = GEN ** 0
            for i in unroll(0, BLOCK_COORD_COUNT[b]):
                pad_fp += alpha_pow * COORD_PAD_VAL[BLOCK_COORD_OFF[b] + i]
                alpha_pow *= alpha
            g_two_kappa = g_squares[block_kappa[GEN ** b]]  # g^(2^κ_b)
            if BLOCK_REAL_TABLE[b] == REAL_IS_FULL_CUBE:
                g_real = g_two_kappa  # shared block: real = 2^κ, so DELTA = 0
            else:
                g_real = count_gpows[GEN ** BLOCK_REAL_TABLE[b]]  # g^count_t
            g_delta_want = g_two_kappa / g_real  # g^DELTA (feeds the advice below)
            pad_bits = HeapBuf(GEN ** COUNT_BITS)
            hint_decompose_bits_exponent(pad_bits, g_delta_want, COUNT_BITS)
            ladder = GEN ** 0
            ladder_square = gamma + pad_fp
            g_delta = GEN ** 0
            for j in unroll(0, COUNT_BITS):
                pad_bit = pad_bits[GEN ** j]
                assert pad_bit * pad_bit == pad_bit
                ladder *= (1 + pad_bit * (ladder_square + 1))
                g_delta *= (1 + pad_bit * (g_squares[GEN ** j] + 1))  # g^DELTA
                ladder_square *= ladder_square
            assert g_real * g_delta == g_two_kappa  # real_b + DELTA_b == 2^κ_b
            side_pad_product *= ladder
        pad_products[GEN ** s] = side_pad_product
    lhsb = gkr_roots[PUSH_SIDE] * pad_products[GEN ** PULL_SIDE]  # balance: push_root * d_pull == pull_root * d_push (padding cancels)
    rhsb = gkr_roots[PULL_SIDE] * pad_products[GEN ** PUSH_SIDE]
    assert lhsb == rhsb

    # ---- 3× leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    bytecode_vals = HeapBuf(BYTECODE_COLS)
    hint_witness(bytecode_vals[0:BYTECODE_COLS], "bytecode_vals")
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); the Public
    # (bytecode) coordinate values are hinted (bytecode_vals) and exported as deferred
    # claims; Index coordinates use the factored index MLE.
    # Pull's blocks mirror push's (same kappas, same offsets — generator-
    # asserted pairing) and share zeta, so each pull block REUSES its push
    # twin's eq_hi and Index-MLE value instead of recomputing them; its column
    # values are mostly deduped pool reads (COORD_FRESH). The identity check
    # against pull's own GKR claim still binds everything.
    block_eq_hi = HeapBuf(N_BLOCKS)      # per push block, reused by its pull twin
    block_index_mle = HeapBuf(N_BLOCKS)  # per push block with an Index coord
    for s in unroll(0, N_GKR_SIDES):
        acc = 0
        selector_sum = 0
        zeta_zs = zeta
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_public_idx = 0
            kappa_g = block_kappa[GEN ** b]
            assert log(kappa_g) < SIZE_BITS
            if s == PULL_SIDE:
                eq_hi = block_eq_hi[GEN ** (b - SIDE_BLOCK_START[PULL_SIDE])]
            else:
                # eq_hi over the ζ coords above κ against the selector bits
                # derived below; the selector length is mu_s − κ = g^mu_s / g^κ.
                sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                assert log(sel_len_g) < SIZE_BITS
                zeta_hi = zeta_zs * kappa_g
                # selector bits = offset >> κ: advice-decompose the offset's bits
                # and read them shifted by κ. Rebuilding g^offset from those high
                # bits alone (weights g^(2^(κ+k))) and asserting it equals
                # block_off_g pins the bits AND the κ-alignment in one shot.
                # The low κ bit cells are written but never read.
                offset_bits = HeapBuf(GEN ** SIZE_BITS)
                hint_decompose_bits_exponent(offset_bits, block_off_g[GEN ** b], SIZE_BITS)
                sel_bits = offset_bits * kappa_g  # bits of sel = offset >> κ
                eq_chain = HeapBuf(MU_CAP + 2)
                goff_chain = HeapBuf(MU_CAP + 2)  # rebuild g^offset from the high bits
                eq_chain[GEN ** 0] = 1
                goff_chain[GEN ** 0] = 1
                for xk in mul_range(1, sel_len_g):
                    sbit = sel_bits[xk]
                    assert sbit * sbit == sbit
                    eq_chain[xk * GEN] = eq_chain[xk] * (1 + sbit + zeta_hi[xk])  # eq(sel_bit, zeta) = 1 + sel_bit + zeta over GF(2)
                    goff_chain[xk * GEN] = goff_chain[xk] * (1 + sbit * (g_squares[kappa_g * xk] + 1))  # weight g^(2^(κ+k))
                eq_hi = eq_chain[sel_len_g]
                assert goff_chain[sel_len_g] == block_off_g[GEN ** b]  # bits == offset >> κ, κ-aligned
                if s == PUSH_SIDE:
                    block_eq_hi[GEN ** b] = eq_hi
            selector_sum += eq_hi
            # inner fingerprint Σ_i α^i · coord_i(ζ_lo); count side uses α=1,γ=0.
            inner_sum = 0
            alpha_pow = GEN ** 0
            for i in unroll(0, BLOCK_COORD_COUNT[b]):
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_CONST:
                    coord_val = COORD_CONST[BLOCK_COORD_OFF[b] + i]
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_COL:
                    if COORD_FRESH[BLOCK_COORD_OFF[b] + i] == 1:
                        fs, coord_val, cursor = fs_next(fs, cursor)
                        claim_pool[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]] = coord_val
                        claim_cplen_g[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]] = kappa_g  # cplen = block kappa
                    else:
                        coord_val = claim_pool[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]]
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_GCOL:
                    if COORD_FRESH[BLOCK_COORD_OFF[b] + i] == 1:
                        fs, rawv, cursor = fs_next(fs, cursor)
                        claim_pool[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]] = rawv
                        claim_cplen_g[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]] = kappa_g  # cplen = block kappa
                    else:
                        rawv = claim_pool[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]]
                    coord_val = GEN * rawv
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_INDEX:
                    if s == PULL_SIDE:
                        coord_val = block_index_mle[GEN ** (b - SIDE_BLOCK_START[PULL_SIDE])]
                    else:
                        idx_chain = HeapBuf(MU_CAP + 2)
                        idx_chain[GEN ** 0] = 1
                        for xt in mul_range(1, kappa_g):
                            idx_chain[xt * GEN] = idx_chain[xt] * (1 + zeta_zs[xt] * idxc_tab[xt])  # Index-coord MLE: prod_t (1 + zeta_t * (1 + g^(2^t)))
                        coord_val = idx_chain[kappa_g]
                        if s == PUSH_SIDE:
                            block_index_mle[GEN ** b] = coord_val
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_PUBLIC:
                    # push and pull share zeta, so BOTH bytecode blocks read the
                    # same six evaluations (indexed per block, not globally).
                    coord_val = bytecode_vals[GEN ** block_public_idx]
                    block_public_idx += 1
                if s == COUNT_SIDE:
                    inner_sum += coord_val
                else:
                    inner_sum += alpha_pow * coord_val
                    alpha_pow *= alpha
            if s == COUNT_SIDE:
                acc += eq_hi * inner_sum
            else:
                acc += eq_hi * (gamma + inner_sum)
        acc += 1 + selector_sum
        assert acc == gkr_claims[s]
    claim_idx = N_BUS_CLAIMS  # AIR/PI/pin claims pool after the deduped bus claims

    # ---- stacked-bytecode reduction ----
    # The bytecode is ONE multilinear in BYTECODE_LOG + LOG2_BYTECODE_COLS
    # variables (BYTECODE_COLS encoding columns stacked along the selector
    # bits), and push/pull share zeta, so there is ONE opening point: absorb
    # the values, sample the selector challenges, and reduce to the single
    # claim B(zeta_lo, sel) = sum_c eq(sel, c) * v_c.
    for k in unroll(0, BYTECODE_COLS):
        fs = obs(fs, bytecode_vals[GEN ** k])
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
    s_hat_v = HeapBuf(2 * FIELD_BITS)  # the two ring-switch slices (end the stream), fetched + observed in the loop below
    # Ring-switch claim 0 (ab): value lincheck_w, z_skip = lincheck_z_skip, x_outer[0] = lincheck_rs[LINCHECK_ROUNDS-1]
    # (x_inner_rest is the REVERSED lincheck round vector). Claim 1 (c): value
    # c_eval, z_skip = zerocheck_z, x_outer[0] = zerocheck_r[6].
    transposed_claims = StackBuf(2)
    rs_eq_vals = StackBuf(2)
    c_table = HeapBuf(FIELD_BITS)
    z_vals = HeapBuf(2 * QPKD_VARS_CAP)
    r_dprime = HeapBuf(LOG2_FIELD_BITS)
    for rs in unroll(0, 2):
        for i in unroll(0, FIELD_BITS):
            fs, w, cursor = fs_next(fs, cursor)
            s_hat_v[GEN ** (FIELD_BITS * rs + i)] = w
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
            claim_check += lagrange_w * ((1 + claim_x_outer_0) * s_hat_v[GEN ** (FIELD_BITS * rs + i)] + claim_x_outer_0 * s_hat_v[GEN ** (FIELD_BITS * rs + 2 ** K_SKIP + i)])  # claim = sum_i lambda_i(z_skip) * eq(x_outer0, i>>6) * s_hat_v[i]
        assert claim_check == claim_val
    # ONE r'' shared by both claims (each slice was absorbed before the
    # sample), so one eq tensor and one linearized coefficient table
    # serve the whole batch.
    for i in unroll(0, LOG2_FIELD_BITS):
        fs = squeeze(fs)
        rv = fs[0]
        r_dprime[GEN ** i] = rv
    w_eq = HeapBuf(2 ** (LOG2_FIELD_BITS + 1) - 2)
    eqtree(r_dprime, w_eq, LOG2_FIELD_BITS)  # w = eq tensor of the 7 shared r'' coords (one batch challenge, both claims)
    # c_k = sum_i w_i * delta_pows[k][i], one runtime loop over the levels k.
    for xk in mul_range(1, GEN ** FIELD_BITS):
        delta_row = delta_pows * xk ** FIELD_BITS
        c_acc = 0
        for i in unroll(0, FIELD_BITS):
            c_acc += w_eq[GEN ** (2 ** LOG2_FIELD_BITS - 2 + i)] * delta_row[GEN ** i]  # c_k = sum_i w_i * delta_i^(2^k): the linearized-poly coefficient table
        c_table[xk] = c_acc
    for rs in unroll(0, 2):
        # transposed claim T = sum_j x^j * L_w(shv_j): one runtime pass over
        # the observed values; per value the Frobenius powers evolve as a
        # scalar against the c table, and x^j chains through a heap cell.
        s_hat_row = s_hat_v * GEN ** (FIELD_BITS * rs)
        x_pow_chain = HeapBuf(FIELD_BITS + 1)
        x_pow_chain[GEN ** 0] = GEN ** 0
        t_chain = HeapBuf(FIELD_BITS + 1)
        t_chain[GEN ** 0] = 0
        for x_round in mul_range(1, GEN ** FIELD_BITS):
            y_pow = s_hat_row[x_round]
            lin_eval = 0
            for k in unroll(0, FIELD_BITS):  # L_w(y) = sum_k c_k y^(2^k); y^(2^k) squares once per step
                lin_eval += c_table[GEN ** k] * y_pow
                y_pow *= y_pow
            t_chain[x_round * GEN] = t_chain[x_round] + x_pow_chain[x_round] * lin_eval
            x_pow_chain[x_round * GEN] = x_pow_chain[x_round] * 2  # x = the field element 2 (the polynomial x)
        transposed_claims[rs] = t_chain[GEN ** FIELD_BITS]
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

    # ---- Jagged dense layout: certify every cumulative column height ----
    # Integer addition rides the exponent. `col_bounds[g^c] = g^t_c`; multiplying
    # by g^height advances to the next cumulative height without an integer-add
    # gadget. Bit decompositions are advice but are pinned back to these g-powers.
    col_bounds = HeapBuf(N_COMMITTED_COLS + 1)
    col_heights = HeapBuf(N_COMMITTED_COLS)
    col_bounds[GEN ** 0] = GEN ** 0
    for c in unroll(0, N_COMMITTED_COLS):
        if COL_HEIGHT_KIND[c] == 0:
            g_height = g_squares[kappa_base[GEN ** COL_HEIGHT_SRC[c]] * GEN ** COL_HEIGHT_ADJ[c]]
        else:
            g_height = count_gpows[GEN ** COL_HEIGHT_SRC[c]]
        col_heights[GEN ** c] = g_height
        col_bounds[GEN ** (c + 1)] = col_bounds[GEN ** c] * g_height
    g_total = col_bounds[GEN ** N_COMMITTED_COLS]
    gmv = log2_ceil_in_the_exponent(g_total, g_logs_pow2, g_squares, PCS_MIN_MU, SIZE_BITS)  # g^m

    col_start_bits = HeapBuf(SIZE_BITS * N_COMMITTED_COLS)
    col_height_bits = HeapBuf(SIZE_BITS * N_COMMITTED_COLS)
    col_end_bits = HeapBuf(SIZE_BITS * N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        start_bits = col_start_bits * GEN ** (SIZE_BITS * c)
        height_bits = col_height_bits * GEN ** (SIZE_BITS * c)
        end_bits = col_end_bits * GEN ** (SIZE_BITS * c)
        hint_decompose_bits_exponent(start_bits, col_bounds[GEN ** c], SIZE_BITS)
        hint_decompose_bits_exponent(height_bits, col_heights[GEN ** c], SIZE_BITS)
        hint_decompose_bits_exponent(end_bits, col_bounds[GEN ** (c + 1)], SIZE_BITS)
        start_g = GEN ** 0
        height_g = GEN ** 0
        end_g = GEN ** 0
        for bit in unroll(0, SIZE_BITS):
            sb = start_bits[GEN ** bit]
            hb = height_bits[GEN ** bit]
            eb = end_bits[GEN ** bit]
            assert sb * sb == sb
            assert hb * hb == hb
            assert eb * eb == eb
            start_g *= (1 + sb * (g_squares[GEN ** bit] + 1))
            height_g *= (1 + hb * (g_squares[GEN ** bit] + 1))
            end_g *= (1 + eb * (g_squares[GEN ** bit] + 1))
        assert start_g == col_bounds[GEN ** c]
        assert height_g == col_heights[GEN ** c]
        assert end_g == col_bounds[GEN ** (c + 1)]

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
        if CLAIM_POINT_BUF[rep] == POINT_BUF_RHO:
            cplen_g = claim_cplen_g[GEN ** rep]
            src = rho * GEN ** CLAIM_POINT_OFF[rep]
            for xk in mul_range(1, cplen_g):
                row[xk] = src[xk]
            zero_ptr = row * cplen_g
            zero_len_g = GEN ** SIZE_BITS / cplen_g
            for xk in mul_range(1, zero_len_g):
                zero_ptr[xk] = 0
        if CLAIM_POINT_BUF[rep] == POINT_BUF_PI:
            row[GEN ** 0] = rm
            for bit in unroll(1, SIZE_BITS):
                row[GEN ** bit] = 0

    # Compute the public-padding correction: Jagged commits only the real
    # prefix, while the arithmetization's claim includes its fixed pad suffix.
    opening_claim_values = HeapBuf(N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
            # q_pkd remains the one aligned subcube for flock's ring-switch and
            # its strided VM-value claims; it has no public padding correction.
            opening_claim_values[GEN ** j] = claim_pool[GEN ** j]
        else:
            if CLAIM_PAD[j] == 0:
                opening_claim_values[GEN ** j] = claim_pool[GEN ** j]
            else:
                row = claim_rows * GEN ** (SIZE_BITS * CLAIM_ROW_GROUP[j])
                height_bits = col_height_bits * GEN ** (SIZE_BITS * CLAIM_COL[j])
                real_prefix = prefix_indicator(row, height_bits)
                opening_claim_values[GEN ** j] = claim_pool[GEN ** j] + CLAIM_PAD[j] * (1 + real_prefix)

    # Every adjusted Jagged claim value is observed before its batching scalar,
    # exactly as in the native verifier.
    for j in unroll(0, N_CLAIMS):
        fs = obs(fs, opening_claim_values[GEN ** j])
    gamma_pool = HeapBuf(N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        fs = squeeze(fs)
        gv = fs[0]
        gamma_pool[GEN ** j] = gv
        target += gv * opening_claim_values[GEN ** j]

    # ================= the Ligerito opening core (Jagged dense q) ===========

    # Dispatch on m = max(log2_ceil(total real area), PCS_MIN_MU).
    sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN): the match_range arm index selecting the opening candidate
    assert log(sel) < LIG_N_CANDIDATES
    sumcheck_target, fold_challenges, final_msg, inner_total, yr_log_n_g, fold_cap_g = match_range(log(sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], target, commit_root_0, commit_root_1, cursor))
    # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
    # (the telescoped product formula; z powers evolve by squaring per k).
    # QPKD_VARS_CAP = tau_5 + (K_LOG - LOG2_FIELD_BITS), exponent-additive from the certified
    # announced log; the per-k z-power rows chain by a runtime g^qpkdv
    # stride, and the inner passes are runtime loops with product/square
    # state chained per row.
    qpkdv_g = tau_blake3_g * GEN ** (K_LOG - LOG2_FIELD_BITS)
    one_plus_q = HeapBuf(GEN ** (QPKD_VARS_CAP))
    for x_round in mul_range(1, qpkdv_g):
        one_plus_q[x_round] = 1 + fold_challenges[x_round]
    for rs in unroll(0, 2):
        z_pows = HeapBuf((FIELD_BITS + 1) * QPKD_VARS_CAP)
        z_row_src = z_vals * GEN ** (QPKD_VARS_CAP * rs)
        for x_round in mul_range(1, qpkdv_g):
            z_pows[x_round] = z_row_src[x_round]
        e_acc = HeapBuf(FIELD_BITS + 1)
        e_acc[GEN ** 0] = 0
        row_ptr = HeapBuf(FIELD_BITS + 1)
        row_ptr[GEN ** 0] = z_pows
        for xk in mul_range(1, GEN ** FIELD_BITS):
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
        rs_eq_vals[rs] = e_acc[GEN ** FIELD_BITS]
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
            weight = GEN ** 0
            for bit in unroll(0, LOG2_FIELD_BITS):
                if (CLAIM_QPKD_SLOT[j] // (2 ** bit)) % 2 == 1:
                    weight *= fold_challenges[GEN ** bit]
                else:
                    weight *= 1 + fold_challenges[GEN ** bit]
            zptr = zeta * GEN ** CLAIM_POINT_OFF[j]
            ris7 = fold_challenges * GEN ** LOG2_FIELD_BITS
            cplen_g = claim_cplen_g[GEN ** j]
            point_chain = HeapBuf(SIZE_BITS + 1)
            point_chain[GEN ** 0] = weight
            for xk in mul_range(1, cplen_g):
                point_chain[xk * GEN] = point_chain[xk] * (1 + zptr[xk] + ris7[xk])
            weight = point_chain[cplen_g]
            q_hi_len_g = fold_cap_g / qpkdv_g
            q_hi = fold_challenges * qpkdv_g
            selector_chain = HeapBuf(SIZE_BITS + 1)
            selector_chain[GEN ** 0] = weight
            for xk in mul_range(1, q_hi_len_g):
                selector_chain[xk * GEN] = selector_chain[xk] * (1 + q_hi[xk])
            qpkd_claim_weight += gamma_pool[GEN ** j] * selector_chain[q_hi_len_g]

    # Contract every Basic Jagged indicator with the final Ligerito message.
    # A second dispatch on the already-certified commitment size bakes both
    # the folded prefix length and the residual-message shape into straight-
    # line width-four contractions.
    jagged_sum = match_range(log(sel), range(0, LIG_N_CANDIDATES), lambda m_idx: jagged_terminal(m_idx, fold_challenges, final_msg, claim_rows, col_start_bits, col_end_bits, gamma_pool))
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
        defer_out[GEN ** k] = zeta[GEN ** k]
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
    # The dual-basis Frobenius powers delta_pows[128k + i] = TRACE_DUAL_BASIS[i]^(2^k) are claim-
    # and sub-independent: build the table once, read-only afterwards.
    delta_pows = HeapBuf(FIELD_BITS * FIELD_BITS)
    for i in unroll(0, FIELD_BITS):
        delta_pows[GEN ** i] = TRACE_DUAL_BASIS[i]
    for xk in mul_range(1, GEN ** (FIELD_BITS - 1)):
        delta_row = delta_pows * xk ** FIELD_BITS
        next_delta_row = delta_row * GEN ** FIELD_BITS
        for i in unroll(0, FIELD_BITS):
            delta_v = delta_row[GEN ** i]
            next_delta_row[GEN ** i] = delta_v * delta_v

    # exponent-domain lookup tables, shared read-only across every sub-proof.
    g_logs_pow2, g_squares = exponent_tables()

    # per-sub deferred-claim regions (layout: see verify_sub's defer_out)
    defer = HeapBuf(NSUB * DEFER_SIZE)

    for sub in unroll(0, NSUB):
        verify_sub(sub_pis[GEN ** (2 * sub)], sub_pis[GEN ** (2 * sub + 1)], fs_seed[0], fs_seed[1], delta_pows, g_logs_pow2, g_squares, defer * GEN ** (sub * DEFER_SIZE))

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
