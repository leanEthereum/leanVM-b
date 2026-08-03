# CREDIT: The Jagged PCS branching-program evaluator is adapted from Succinct
# Labs SP1's `slop/crates/jagged` implementation (MIT OR Apache-2.0):
# https://github.com/succinctlabs/sp1
from snark_lib import *

# The proof stream rides ONE padded witness hint (the guest walks only the
# prefix the shape dictates); binding always comes from the per-word absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
# Per-table tau floor: BLAKE3 is sized to flock's instance count (>= 2^3).
FLOORS = [0, 0, 0, 0, 0, 0, 0, 0, 3]
INV_GEN = INV_GEN_PLACEHOLDER
LAGRANGE_INV_0 = LAGRANGE_INV_0_PLACEHOLDER
LAGRANGE_INV_1 = LAGRANGE_INV_1_PLACEHOLDER
LAGRANGE_INV_2 = LAGRANGE_INV_2_PLACEHOLDER
# The batched zerocheck's round polynomial arrives WHOLE, as a cubic at {0,1,g,g^2}:
# one baked inverse denominator per node.
LAG4_INV_0 = LAG4_INV_0_PLACEHOLDER
LAG4_INV_1 = LAG4_INV_1_PLACEHOLDER
LAG4_INV_2 = LAG4_INV_2_PLACEHOLDER
LAG4_INV_3 = LAG4_INV_3_PLACEHOLDER

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
# REAL_IS_FULL_CUBE for the framework blocks (real = 2^kappa, no padding). It is
# also what marks a block as owned: an owned block's fingerprint is settled by the
# batched zerocheck, off its table's column evaluations.
REAL_IS_FULL_CUBE = REAL_IS_FULL_CUBE_PLACEHOLDER
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
# For a coord of a TABLE's block: its column's local index inside that table. Those
# coords raise no claim (the zerocheck settles them), so they use this instead.
COORD_COL_LOCAL = COORD_COL_LOCAL_PLACEHOLDER
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
# Zerocheck: the batch carries EVERY committed column of a table, because its bus
# forms read the flushed ones and its constraint the rest; TABLE_COLS_CAP caps the
# evaluation frame. ETA_OFFSET[t] starts table t's disjoint range of eta-powers.
N_TABLE_COLS = N_TABLE_COLS_PLACEHOLDER
TABLE_COLS_CAP = TABLE_COLS_CAP_PLACEHOLDER
# ETA_OFFSET[t] starts table t's disjoint range of identity powers; the three bus
# forms take ETA_FORM_BASE + side, the SAME three powers for every table. That
# sharing is what makes the batch's target derivable from the three leaf claims.
ETA_OFFSET = ETA_OFFSET_PLACEHOLDER
ETA_FORM_BASE = ETA_FORM_BASE_PLACEHOLDER
N_ETA_POWS = N_ETA_POWS_PLACEHOLDER
# The instruction tables, in schema order:
TABLE_ADD = 0
TABLE_MUL = 1
TABLE_ADD_EXT = 2
TABLE_MUL_EXT = 3
TABLE_SET = 4
TABLE_DEREF = 5
TABLE_DEREF_EXT = 6
TABLE_JUMP = 7
TABLE_BLAKE3 = 8
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
# Tower F192 = F64[Y]/(Y^3+Y+1). Y_TOWER embeds Y for reassembling
# e192(lo,hi,top)=lo+hi*Y+top*Y². Y_INV is also used at the opening boundary
# to deduce the top-limb evaluation after the low and high limbs are transmitted.
Y_TOWER = Y_TOWER_PLACEHOLDER
Y_INV = Y_INV_PLACEHOLDER
# Coordinate basis e_i of F192 (spans the whole field). hint_decompose_bits
# emits a word's coordinate bits, so a value reconstructs as Σ b_i·COORD_BASIS[i]
# = v. (NOT the g-power basis GEN**i, which spans only F64 in the tower.)
COORD_BASIS = COORD_BASIS_PLACEHOLDER
LAGRANGE_INV_LAMBDA = LAGRANGE_INV_LAMBDA_PLACEHOLDER
LAGRANGE_INV_COMBINED = LAGRANGE_INV_COMBINED_PLACEHOLDER
LAGRANGE_INV_S = LAGRANGE_INV_S_PLACEHOLDER
LINCHECK_ROUNDS = LINCHECK_ROUNDS_PLACEHOLDER
PIN_COLUMN = PIN_COLUMN_PLACEHOLDER
K_LOG = K_LOG_PLACEHOLDER
SLOT_STRIDE_LOG = SLOT_STRIDE_LOG_PLACEHOLDER  # = K_LOG - LOG_PACKING (=8); the q_pkd slot stride
# Phase E: the dense Jagged opening, with q_pkd retained as an aligned prefix.
# The two ring-switch fronts (claim check, tensor transpose, and eval_rs_eq all
# in-circuit), followed by the
# gamma-combination of the two ring-switch claims and the N_CLAIMS pool claims.
# Phase E2: the Ligerito opening over the dense commitment, dispatched by
# the certified committed log-size m through match_range: the LIG_* tables
# below carry one row per (rate, m), with rate in 1..=4 and m in the
# supported committed-size interval,
# emitted from the SAME derive_profile/level_shapes the prover uses.
# Scalars index as TBL[m_idx]; per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl],
# where m_idx is the flattened (rate, size) configuration index;
# per-fold grind schedules with the LIG_MAX_TOTAL_FOLDS stride; the subspace
# vanishing constants with the LIG_MAX_VANISH_LEN stride. The eval_b terminal
# claim descriptors bake the point source, dense column, fixed padding, and
# q_pkd slot. Runtime dimensions and intervals are derived from public counts.
# Opening dispatch: baked committed log-size, candidate range, g^-LIG_MIN_LOG_SIZE.
LIG_MIN_LOG_SIZE = LIG_MIN_LOG_SIZE_PLACEHOLDER
LIG_N_LOG_SIZES = LIG_N_LOG_SIZES_PLACEHOLDER
LIG_N_RATES = LIG_N_RATES_PLACEHOLDER
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
LIG_MAX_OOD_SAMPLES = LIG_MAX_OOD_SAMPLES_PLACEHOLDER
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
LIG_QUERY_GRIND_BITS = LIG_QUERY_GRIND_BITS_PLACEHOLDER
LIG_OOD_SAMPLES = LIG_OOD_SAMPLES_PLACEHOLDER
LIG_QUERIES = LIG_QUERIES_PLACEHOLDER
LIG_FOLDS = LIG_FOLDS_PLACEHOLDER
LIG_INTERLEAVE = LIG_INTERLEAVE_PLACEHOLDER
LIG_LEAF_PAIRS = LIG_LEAF_PAIRS_PLACEHOLDER
LIG_LEAF_BLOCKS = LIG_LEAF_BLOCKS_PLACEHOLDER
LIG_PACKED_ROW_CAP = LIG_PACKED_ROW_CAP_PLACEHOLDER
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
POINT_BUF_QPKD_RHO = 4
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_POINT_OFF = CLAIM_POINT_OFF_PLACEHOLDER
# Dense Jagged column index and fixed public pad value for each pooled claim.
CLAIM_PAD = CLAIM_PAD_PLACEHOLDER
CLAIM_QPKD_SLOT = CLAIM_QPKD_SLOT_PLACEHOLDER
CLAIM_GAMMA_RANK = CLAIM_GAMMA_RANK_PLACEHOLDER
N_CLAIM_ROWS = N_CLAIM_ROWS_PLACEHOLDER
CLAIM_ROW_REP = CLAIM_ROW_REP_PLACEHOLDER
N_JAGGED_BATCHES = N_JAGGED_BATCHES_PLACEHOLDER
JAGGED_BATCH_ROW = JAGGED_BATCH_ROW_PLACEHOLDER
JAGGED_BATCH_COL = JAGGED_BATCH_COL_PLACEHOLDER
JAGGED_BATCH_LOG = JAGGED_BATCH_LOG_PLACEHOLDER
JAGGED_BATCH_BASE = JAGGED_BATCH_BASE_PLACEHOLDER
QPKD_VARS_CAP = QPKD_VARS_CAP_PLACEHOLDER
# Phase F: log rows of the bytecode blocks (the deferred bytecode points).
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER
# One sub-proof's deferred-claim region: one bytecode point and the Flock
# lincheck data (see verify_sub's defer_out layout).
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
TRANSCRIPT_SEED_2 = TRANSCRIPT_SEED_2_PLACEHOLDER
TRANSCRIPT_SEED_3 = TRANSCRIPT_SEED_3_PLACEHOLDER
AGG_SEED_0 = AGG_SEED_0_PLACEHOLDER
AGG_SEED_1 = AGG_SEED_1_PLACEHOLDER
AGG_SEED_2 = AGG_SEED_2_PLACEHOLDER
AGG_SEED_3 = AGG_SEED_3_PLACEHOLDER
STATEMENT_SEED_0 = STATEMENT_SEED_0_PLACEHOLDER
STATEMENT_SEED_1 = STATEMENT_SEED_1_PLACEHOLDER
STATEMENT_SEED_2 = STATEMENT_SEED_2_PLACEHOLDER
STATEMENT_SEED_3 = STATEMENT_SEED_3_PLACEHOLDER

DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQ = 4
DS_POW = 5

# Field structure: GF(2^192), represented as three GF(2^64) tower limbs.
# Six challenges define the F2-linear map that batches the 192 transposed
# ring-switch coordinates.
FIELD_BITS = 192
BASE_FIELD_BITS = 64
RING_MAP_SHIFTS = [32, 16, 8, 4, 2, 1]
# Exponent bit-widths: an announced 32-bit count decomposes into COUNT_BITS
# bits, with its top bit constrained to zero so the native strict 32-bit bound
# holds; any structural size (sums of 2^kappa, packing offsets) fits SIZE_BITS
# bits.
COUNT_BITS = 33
SIZE_BITS = 34


@inline
def ebase(x):
    out = [x, 0, 0]
    return out


@inline
def eadd(a: Ext, b: Ext):
    out = StackBuf(3)
    xor_192(a, b, out)
    return out


@inline
def emul(a: Ext, b: Ext):
    out = StackBuf(3)
    mul_192(a, b, out)
    return out


@inline
def emul_base(x, value: Ext):
    # The shared MUL_192 table has a base-scalar mode: one row scales all three
    # limbs without materializing [x, 0, 0].
    out = StackBuf(3)
    mul_192_base(x, value, out)
    return out


@inline
def eadd_base(x, value: Ext):
    # Addition by the embedded F64 value [x, 0, 0] only changes the low tower
    # limb. Write the result as one contiguous run without materializing the
    # temporary embedded extension operand.
    out = StackBuf(3)
    out[0] = x + value[0]
    out[1] = value[1]
    out[2] = value[2]
    return out


@inline
def ediv(a: Ext, b: Ext):
    out = StackBuf(3)
    div_192(a, b, out)
    return out


@inline
def epoly4(x: Ext, c0: Ext, c1: Ext, c2: Ext, c3: Ext):
    return eadd(c0, emul(x, eadd(c1, emul(x, eadd(c2, emul(x, c3))))))


@inline
def epoly5(x: Ext, c0: Ext, c1: Ext, c2: Ext, c3: Ext, c4: Ext):
    return eadd(c0, emul(x, eadd(c1, emul(x, eadd(c2, emul(x, eadd(c3, emul(x, c4))))))))


@inline
def epoly6(x: Ext, c0: Ext, c1: Ext, c2: Ext, c3: Ext, c4: Ext, c5: Ext):
    return eadd(c0, emul(x, eadd(c1, emul(x, eadd(c2, emul(x, eadd(c3, emul(x, eadd(c4, emul(x, c5))))))))))


@inline
def epoly7(x: Ext, c0: Ext, c1: Ext, c2: Ext, c3: Ext, c4: Ext, c5: Ext, c6: Ext):
    return eadd(c0, emul(x, eadd(c1, emul(x, eadd(c2, emul(x, eadd(c3, emul(x, eadd(c4, emul(x, eadd(c5, emul(x, c6))))))))))))


@inline
def combine_tower_limbs(c0: Ext, c1: Ext, c2: Ext):
    y = [Y_TOWER[0], Y_TOWER[1], Y_TOWER[2]]
    return eadd(c0, emul(y, eadd(c1, emul(y, c2))))


@inline
def base_air_constraint(col_evals, eta: Ext, is_mul: Const):
    fp = sload(col_evals, 1)
    c0 = eadd(sload(col_evals, 5), emul(fp, sload(col_evals, 2)))
    c1 = eadd(sload(col_evals, 6), emul(fp, sload(col_evals, 3)))
    c2 = eadd(sload(col_evals, 7), emul(fp, sload(col_evals, 4)))
    if is_mul == 0:
        result = eadd(sload(col_evals, 8), sload(col_evals, 9))
    else:
        result = emul(sload(col_evals, 8), sload(col_evals, 9))
    c3 = eadd(sload(col_evals, 10), result)
    return epoly4(eta, c0, c1, c2, c3)


@inline
def ext_air_constraint(col_evals, eta: Ext, is_mul: Const):
    fp = sload(col_evals, 1)
    c0 = eadd(sload(col_evals, 5), emul(fp, sload(col_evals, 2)))
    c1 = eadd(sload(col_evals, 6), emul(fp, sload(col_evals, 3)))
    c2 = eadd(sload(col_evals, 7), emul(fp, sload(col_evals, 4)))
    va = combine_tower_limbs(sload(col_evals, 8), sload(col_evals, 9), sload(col_evals, 10))
    vb = combine_tower_limbs(sload(col_evals, 11), sload(col_evals, 12), sload(col_evals, 13))
    vc = combine_tower_limbs(sload(col_evals, 14), sload(col_evals, 15), sload(col_evals, 16))
    if is_mul == 0:
        result = eadd(va, vb)
    else:
        result = emul(va, vb)
    c3 = eadd(vc, result)
    if is_mul == 0:
        out = epoly4(eta, c0, c1, c2, c3)
    else:
        full_a = eadd([1, 0, 0], sload(col_evals, 29))
        c4 = eadd(sload(col_evals, 9), emul(full_a, sload(col_evals, 27)))
        c5 = eadd(sload(col_evals, 10), emul(full_a, sload(col_evals, 28)))
        out = epoly6(eta, c0, c1, c2, c3, c4, c5)
    return out


@inline
def ext_assert_eq(a: Ext, b: Ext):
    # In characteristic two, a == b iff a + b == 0. Binding ADD_EXT's output
    # to the pooled zero run checks all three limbs in one VM row.
    zero = [0, 0, 0]
    xor_192(a, b, zero)
    return


@inline
def ext_is_zero(value: Ext):
    out = StackBuf(1)
    if value[0] == 0:
        if value[1] == 0:
            if value[2] == 0:
                out[0] = 1
            else:
                out[0] = 0
        else:
            out[0] = 0
    else:
        out[0] = 0
    return out[0]


@inline
def eload(ptr):
    out = StackBuf(3)
    deref_192(ptr, out)
    return out


@inline
def estore(ptr, value: Ext):
    deref_192(ptr, value)
    return


@inline
def challenge_from_state(state):
    out = [state[0], state[1], state[2]]
    return out


@inline
def sponge_compress(state, scalar: Ext, tail, out):
    block = [scalar[0], scalar[1], scalar[2], tail]
    blake3(state[0:4], block, out[0:4])
    return


@inline
def hash_state_to_words(state):
    a = [state[0], state[1], state[2]]
    b = [state[3], 0, 0]
    return a, b


@inline
def hash_words_to_state(word_0: Ext, word_1: Ext):
    assert word_1[1] == 0
    assert word_1[2] == 0
    out = [word_0[0], word_0[1], word_0[2], word_1[0]]
    return out


def squeeze_step(state_0, state_1, state_2, state_3):
    a = [state_0, state_1, state_2, state_3]
    o = StackBuf(4)
    tag = [0, 0, DS_SQ]
    sponge_compress(a, tag, 0, o)
    challenge = challenge_from_state(o)
    return challenge, o[0], o[1], o[2], o[3]


def check_base_word_bits_decomposition(bits_ptr, value):
    # Boolean-constrain a hinted F64 decomposition and bind it to the word in
    # the same pass, so each heap bit is loaded exactly once.
    acc = 0
    for i in unroll(0, 64):
        b = bits_ptr[GEN ** i]
        bits_ptr[GEN ** i] = b * b
        acc += b * COORD_BASIS[3 * i]
    assert acc == value
    return


def decode_query_bits(v: Ext, positions_out, bit_ptrs_out, depth: Const):
    # The squeezed word's bits are advice-decomposed HERE, boolean-constrained,
    # and tied back by reconstruction; each depth-bit group also becomes a query
    # position (little-endian), with a pointer to its bit run (the Merkle
    # direction bits). Each field word packs FIELD_BITS // depth positions.
    per_word = FIELD_BITS // depth
    bits_ptr = HeapBuf(GEN ** FIELD_BITS)
    hint_decompose_bits(bits_ptr, v[0], 64)
    hint_decompose_bits(bits_ptr * GEN ** 64, v[1], 64)
    hint_decompose_bits(bits_ptr * GEN ** 128, v[2], 64)
    # The position groups below already form the polynomial-basis value of
    # every run of bits. Accumulate those runs into their F64 tower limbs while
    # they are live, instead of rereading all 192 heap bits afterwards.
    acc0 = 0
    acc1 = 0
    acc2 = 0
    for j in unroll(0, per_word):
        base_bit = j * depth  # this group's first coordinate of v
        # A group that stays inside one 64-bit limb shifts as a WHOLE: the
        # coordinate basis is the polynomial basis there, so
        # COORD_BASIS[base_bit + b] == COORD_BASIS[base_bit] * COORD_BASIS[b]
        # (exponents below 64, no reduction). The group's contribution to the
        # reconstruction is then one multiply by the position value it already
        # forms, instead of a constant multiply per bit. A group straddling the
        # boundary splits into the two runs that do stay inside a limb.
        cut = 64 - base_bit % 64  # bits of this group below the next limb
        p_lo = 0
        p_hi = 0
        for b in unroll(0, depth):
            t = bits_ptr[GEN ** (base_bit + b)]
            # Booleanity as a write-once pin: the cell already holds t, so
            # storing t*t back IS the assert t*t == t, one instruction shorter
            # (a Cell deref unifies the two sides).
            bits_ptr[GEN ** (base_bit + b)] = t * t
            # `b // cut == 0` IS `b < cut`, in compile-time integer arithmetic
            # (the DSL's `if` compares for equality only).
            if b // cut == 0:
                p_lo += t * (2 ** b)
            else:
                p_hi += t * (2 ** (b - cut))
        # position = p_lo + 2^cut * p_hi: multiplying by X^cut concatenates the
        # two runs, since both degrees stay below 64.
        if cut // depth == 0:  # `cut < depth`: this group straddles the boundary
            positions_out[GEN ** j] = p_lo + (2 ** cut) * p_hi
        else:
            positions_out[GEN ** j] = p_lo
        limb_shift = base_bit % 64
        if base_bit // 64 == 0:
            acc0 += (2 ** limb_shift) * p_lo
            if cut // depth == 0:
                acc1 += p_hi
        if base_bit // 64 == 1:
            acc1 += (2 ** limb_shift) * p_lo
            if cut // depth == 0:
                acc2 += p_hi
        if base_bit // 64 == 2:
            acc2 += (2 ** limb_shift) * p_lo
        bit_ptrs_out[GEN ** j] = bits_ptr * GEN ** base_bit
    for i in unroll(per_word * depth, FIELD_BITS):
        t = bits_ptr[GEN ** i]
        bits_ptr[GEN ** i] = t * t
        if i // 64 == 0:
            acc0 += t * (2 ** (i % 64))
        if i // 64 == 1:
            acc1 += t * (2 ** (i % 64))
        if i // 64 == 2:
            acc2 += t * (2 ** (i % 64))
    # Every bit was pinned exactly once, and the three disjoint accumulators
    # bind exactly the three F192 coordinate limbs of the squeezed challenge.
    assert acc0 == v[0]
    assert acc1 == v[1]
    assert acc2 == v[2]
    return


def grind_check(state_0, state_1, state_2, state_3, nonce: Ext, nbits_g):
    # Ligerito fold/query grinding: digest = H(H(state, (0, POW)), (nonce, POW)); the digest's
    # low digest word's bits are advice-decomposed HERE and verified (booleanity
    # + reconstruction), and the low nbits (nbits_g = g^nbits) must be zero —
    # the CONTIGUOUS PoW window of transcript::pow_bits_ok. That native predicate
    # is defined entirely on out[0] and always uses fewer than 64 bits, so the
    # other independently constrained BLAKE output words need no decomposition.
    # The caller absorbs the full field nonce afterwards. The honest prover searches
    # the deterministic u64 subset, while verification permits the full field:
    # each candidate still costs one hash and succeeds with probability 2^-bits.
    if nbits_g == GEN ** 0:
        ext_assert_eq(nonce, [0, 0, 0])  # native canonical zero-work nonce
    st = [state_0, state_1, state_2, state_3]
    base = StackBuf(4)
    sponge_compress(st, [0, 0, DS_POW], 0, base)
    out = StackBuf(4)
    # nonce's three F64 limbs followed by DS_POW, exactly as the native sponge.
    sponge_compress(base, nonce, DS_POW, out)
    digest_bits = HeapBuf(GEN ** 64)
    hint_decompose_bits(digest_bits, out[0], 64)
    check_base_word_bits_decomposition(digest_bits, out[0])
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
    # g^log2_ceil(value) for a concrete integer `value` < 2^(nbits - 1). The
    # bits are hinted into caller-owned storage, so later phases can reuse them.
    # The zero top bit mirrors the native strict 32-bit row-count bound.
    hint_decompose_bits(bits, value, nbits)
    g_log, word, g_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits, need_exp)
    assert word == value  # the hinted bits are exactly value's bits (so value < 2^nbits)
    assert bits[GEN ** (nbits - 1)] == 0
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
    g_log, word, g_bits_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits, 1)
    assert g_bits_value == g_N  # the hinted bits decode to N
    return g_log


@inline
def verify_merkle_path(leaf_0, leaf_1, leaf_2, leaf_3, path_ptr, direction_bits, depth: Const):
    node_prefix = [leaf_0, leaf_1, leaf_2]
    node_3 = leaf_3
    for level in unroll(0, depth):
        # A hash is four base words. Load its contiguous three-word prefix with
        # DEREF_192 and only the tail with scalar DEREF (two VM rows instead of
        # four); the packed extension equality still binds each F64 limb.
        sibling_prefix = eload(path_ptr * GEN ** (4 * level))
        sibling_3 = path_ptr[GEN ** (4 * level + 3)]
        dir_bit = direction_bits[GEN ** level]  # query index bit: 0 keeps the running node left, 1 swaps it right
        # Select the first three words as one extension-vector operation. Since
        # dir_bit is boolean and embedded in the base field, this is exactly the
        # same coordinate-wise conditional swap as three scalar copies.
        diff_prefix = eadd(node_prefix, sibling_prefix)
        left_prefix = eadd(node_prefix, emul_base(dir_bit, diff_prefix))
        right_prefix = eadd(diff_prefix, left_prefix)
        diff_3 = node_3 + sibling_3
        left_3 = node_3 + dir_bit * diff_3
        left = [left_prefix[0], left_prefix[1], left_prefix[2], left_3]
        right = [right_prefix[0], right_prefix[1], right_prefix[2], diff_3 + left_3]
        parent = StackBuf(4)
        blake3(left, right, parent[0:4])
        node_prefix = [parent[0], parent[1], parent[2]]
        node_3 = parent[3]
    return node_prefix[0], node_prefix[1], node_prefix[2], node_3


def sumcheck_round3(state_0, state_1, state_2, state_3, msg_cursor, claim: Ext, eq_acc: Ext, prev_challenge: Ext):
    # One eq_acc-trick sumcheck round: observe the three round messages off the
    # stream, check the running claim at the previous challenge, squeeze the
    # round challenge round_challenge, and evaluate the round polynomial at round_challenge through the
    # {0, 1, g} Lagrange basis (baked inverse denominators). Shared by the
    # GKR layers and the AIR zerocheck rounds.
    fs = [state_0, state_1, state_2, state_3]
    fs, m0, msg_cursor = fs_next(fs, msg_cursor)
    fs, m1, msg_cursor = fs_next(fs, msg_cursor)
    fs, m2, msg_cursor = fs_next(fs, msg_cursor)
    one = [1, 0, 0]
    one_plus_prev = eadd(one, prev_challenge)
    lhs_inner = eadd(emul(one_plus_prev, m0), emul(prev_challenge, m1))
    lhs = emul(eq_acc, lhs_inner)
    ext_assert_eq(lhs, claim)
    fs, round_challenge = squeeze(fs)
    new_eq = emul(eq_acc, eadd(one_plus_prev, round_challenge))
    gen = [GEN, 0, 0]
    l0 = emul(emul(eadd(round_challenge, one), eadd(round_challenge, gen)), [LAGRANGE_INV_0, 0, 0])
    lag1 = [LAGRANGE_INV_1[0], LAGRANGE_INV_1[1], LAGRANGE_INV_1[2]]
    lag2 = [LAGRANGE_INV_2[0], LAGRANGE_INV_2[1], LAGRANGE_INV_2[2]]
    l1 = emul(emul(round_challenge, eadd(round_challenge, gen)), lag1)
    l2 = emul(emul(round_challenge, eadd(round_challenge, one)), lag2)
    weighted = eadd(eadd(emul(m0, l0), emul(m1, l1)), emul(m2, l2))
    new_claim = emul(new_eq, weighted)
    return fs[0], fs[1], fs[2], fs[3], msg_cursor, new_claim, new_eq, round_challenge


@inline
def quartic_eval_from_eq(claim: Ext, eq_point: Ext, difference: Ext, c2: Ext, c3: Ext, c4: Ext, challenge: Ext):
    c0 = eadd(claim, emul(eq_point, difference))
    c1 = eadd(eadd(difference, c2), eadd(c3, c4))
    return epoly5(challenge, c0, c1, c2, c3, c4)


def sumcheck_round5(state_0, state_1, state_2, state_3, msg_cursor, claim: Ext, prev_challenge: Ext):
    fs = [state_0, state_1, state_2, state_3]
    fs, difference, msg_cursor = fs_next(fs, msg_cursor)
    fs, c2, msg_cursor = fs_next(fs, msg_cursor)
    fs, c3, msg_cursor = fs_next(fs, msg_cursor)
    fs, c4, msg_cursor = fs_next(fs, msg_cursor)
    fs, round_challenge = squeeze(fs)
    new_claim = quartic_eval_from_eq(claim, prev_challenge, difference, c2, c3, c4, round_challenge)
    return fs[0], fs[1], fs[2], fs[3], msg_cursor, new_claim, round_challenge


def sumcheck_round4(state_0, state_1, state_2, state_3, msg_cursor, claim: Ext):
    # One PLAIN sumcheck round. The prover sends the round polynomial itself at
    # {0, 1, g, g^2}, so the verifier does only the two textbook steps: check
    # h(0) + h(1) == claim, then evaluate h at the challenge through the baked
    # Lagrange basis. Nothing is reapplied: no eq factor, no separate term for the
    # tables still waiting, and the eq point is not read here at all.
    fs = [state_0, state_1, state_2, state_3]
    fs, h0, msg_cursor = fs_next(fs, msg_cursor)
    fs, h1, msg_cursor = fs_next(fs, msg_cursor)
    fs, h2, msg_cursor = fs_next(fs, msg_cursor)
    fs, h3, msg_cursor = fs_next(fs, msg_cursor)
    ext_assert_eq(eadd(h0, h1), claim)
    fs, y = squeeze(fs)
    one = [1, 0, 0]
    gen = [GEN, 0, 0]
    gen2 = [GEN * GEN, 0, 0]
    l0 = emul(emul(emul(eadd(y, one), eadd(y, gen)), eadd(y, gen2)), [LAG4_INV_0[0], LAG4_INV_0[1], LAG4_INV_0[2]])
    l1 = emul(emul(emul(y, eadd(y, gen)), eadd(y, gen2)), [LAG4_INV_1[0], LAG4_INV_1[1], LAG4_INV_1[2]])
    l2 = emul(emul(emul(y, eadd(y, one)), eadd(y, gen2)), [LAG4_INV_2[0], LAG4_INV_2[1], LAG4_INV_2[2]])
    l3 = emul(emul(emul(y, eadd(y, one)), eadd(y, gen)), [LAG4_INV_3[0], LAG4_INV_3[1], LAG4_INV_3[2]])
    folded = eadd(eadd(emul(h0, l0), emul(h1, l1)), eadd(emul(h2, l2), emul(h3, l3)))
    return fs[0], fs[1], fs[2], fs[3], msg_cursor, folded, y


@inline
def fold_final_msg(msg, weights, wbase: Const, log_len: Const):
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is the
    # candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(3 * (2 ** YR_LOG_CAP))
    for t in unroll(0, 2 ** log_len // 2):
        w0 = sload(weights, wbase)
        w1 = sload(weights, wbase + 1)
        m0 = eload(msg * GEN ** (3 * (2 * t)))
        m1 = eload(msg * GEN ** (3 * (2 * t + 1)))
        sstore(l0, t, eadd(emul(w0, m0), emul(w1, m1)))
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        nxt = StackBuf(3 * (2 ** YR_LOG_CAP))
        for t in unroll(0, n // 2):
            w0 = sload(weights, wbase + 2 * j)
            w1 = sload(weights, wbase + 2 * j + 1)
            m0 = sload(cursor, 2 * t)
            m1 = sload(cursor, 2 * t + 1)
            sstore(nxt, t, eadd(emul(w0, m0), emul(w1, m1)))
        cursor = nxt
        n = n // 2
    out = sload(cursor, 0)
    return out


@inline
def obs(state, x: Ext):
    # Bind one scalar into the sponge chain: state <- compress(state, (x, SCALAR)).
    # Returns the successor StackBuf; the call site aliases it (zero copies).
    nb = StackBuf(4)
    sponge_compress(state, x, DS_SCALAR, nb)
    return nb


@inline
def obs_base(state, x):
    value = [x, 0, 0]
    out = obs(state, value)
    return out


@inline
def fs_next(state, cursor):
    # Fetch + observe + advance, in one act: read the word under `cursor`, fold it
    # into the sponge, and hand back the successor state, the word, AND the cursor
    # stepped one word on. Reading and absorbing are inseparable here, so no
    # proof-stream word can enter the computation unbound — the soundness invariant
    # the whole guest rests on. All three returns alias into the caller at zero
    # cost (state a StackBuf run, cursor a folded g-address), so the usual walk is
    # just `fs, x, cursor = fs_next(fs, cursor)` with no manual cursor arithmetic.
    # Load the three-word field element directly into the four-word BLAKE3
    # block. Keeping its tag in the adjacent tail cell avoids rebuilding the
    # second 128-bit chunk as two MUL-by-one copies on every transcript word.
    block = StackBuf(4)
    deref_192(cursor, block[0:3])
    block[3] = DS_SCALAR
    x = [block[0], block[1], block[2]]
    nb = StackBuf(4)
    blake3(state[0:4], block[0:4], nb[0:4])
    return nb, x, cursor * GEN ** 3


@inline
def absorb_nonce(state, x: Ext):
    # Full-field grinding nonce absorb: [x.c0, x.c1, x.c2, DS_POW].
    nb = StackBuf(4)
    sponge_compress(state, x, DS_POW, nb)
    return nb


@inline
def squeeze(state):
    # Ratchet: the canonical 128+128 digest is the new state; its first three
    # K lanes are reassembled as the F192 challenge.
    nb = StackBuf(4)
    tag = [0, 0, DS_SQ]
    sponge_compress(state, tag, 0, nb)
    challenge = challenge_from_state(nb)
    return nb, challenge


@inline
def sload(buf, index: Const):
    out = [buf[3 * index], buf[3 * index + 1], buf[3 * index + 2]]
    return out


@inline
def sstore(buf, index: Const, value: Ext):
    buf[3 * index] = value[0]
    buf[3 * index + 1] = value[1]
    buf[3 * index + 2] = value[2]
    return


@inline
def phi8(index: Const):
    out = [PHI8_NODES[3 * index], PHI8_NODES[3 * index + 1], PHI8_NODES[3 * index + 2]]
    return out


@inline
def lagrange_inv_s(index: Const):
    out = [LAGRANGE_INV_S[3 * index], LAGRANGE_INV_S[3 * index + 1], LAGRANGE_INV_S[3 * index + 2]]
    return out


@inline
def coord_basis(index: Const):
    out = [COORD_BASIS[3 * index], COORD_BASIS[3 * index + 1], COORD_BASIS[3 * index + 2]]
    return out


@inline
def lag64(z: Ext, node_base: Const):
    # The 64 phi8-domain Lagrange NUMERATORS at z, nodes PHI8_NODES[node_base..node_base+64]:
    # out[i] = prod_{j != i} (z + PHI8_NODES[node_base + j]). Callers multiply by their
    # baked inverse-denominator table (LAGRANGE_INV_S / LAGRANGE_INV_LAMBDA / LAGRANGE_INV_COMBINED).
    out = StackBuf(3 * 64)
    pre = StackBuf(3 * 65)
    one = [1, 0, 0]
    sstore(pre, 0, one)
    for i in unroll(0, 64):
        p = sload(pre, i)
        node = phi8(node_base + i)
        factor = eadd(z, node)
        product = emul(p, factor)
        sstore(pre, i + 1, product)
    suf = StackBuf(3 * 65)
    sstore(suf, 64, one)
    for i in unroll(0, 64):
        p = sload(suf, 64 - i)
        node = phi8(node_base + 63 - i)
        factor = eadd(z, node)
        product = emul(p, factor)
        sstore(suf, 63 - i, product)
    for i in unroll(0, 64):
        a = sload(pre, i)
        b = sload(suf, i + 1)
        product = emul(a, b)
        out[3 * i] = product[0]
        out[3 * i + 1] = product[1]
        out[3 * i + 2] = product[2]
    return out


@inline
def eq_weight(ch, count: Const, idx: Const, msb_span: Const):
    # The eq-tensor weight of compile-time index `idx` against the challenge
    # run ch[0..count): prod_c eq(bit(idx), ch[c]), where the bit is bit c of
    # idx (msb_span == 0) or bit (msb_span - 1 - c) (MSB-first walk over an
    # msb_span-bit index).
    w = [1, 0, 0]
    one = [1, 0, 0]
    for c in unroll(0, count):
        cv = eload(ch * GEN ** (3 * c))
        if msb_span == 0:
            if (idx // (2 ** c)) % 2 == 1:
                w = emul(w, cv)
            else:
                factor = eadd(one, cv)
                w = emul(w, factor)
        else:
            if (idx // (2 ** (msb_span - 1 - c))) % 2 == 1:
                w = emul(w, cv)
            else:
                factor = eadd(one, cv)
                w = emul(w, factor)
    return w


@inline
def eqtree(point_ptr, out, n_coords: Const):
    # The eq tensor of the n_coords challenges at point_ptr[0..n_coords], built by doubling into
    # out (size 2^(n_coords+1) - 2); the final 2^n_coords values start at offset 2^n_coords - 2.
    one = [1, 0, 0]
    r0 = eload(point_ptr)
    one_plus_r0 = eadd(one, r0)
    estore(out, one_plus_r0)
    estore(out * GEN ** 3, r0)
    for t in unroll(1, n_coords):
        rt = eload(point_ptr * GEN ** (3 * t))
        one_plus_rt = eadd(one, rt)
        for i in unroll(0, 2 ** t):
            pw = eload(out * GEN ** (3 * (2 ** t - 2 + i)))
            lo = emul(pw, one_plus_rt)
            hi = emul(pw, rt)
            estore(out * GEN ** (3 * (2 ** (t + 1) - 2 + i)), lo)
            estore(out * GEN ** (3 * (2 ** (t + 1) - 2 + 2 ** t + i)), hi)
    return


@inline
def jagged_step(s0: Ext, s1: Ext, s2: Ext, s3: Ext, w0: Ext, w1: Ext, w2: Ext, w3: Ext, start_bit_point, end_bit_point):
    # Endpoint bits are Boolean-constrained public interval data, so select one
    # of the four fixed transition matrices instead of evaluating a redundant
    # four-variable tensor. The row/index eq tensor is shared by row groups.
    out = StackBuf(12)
    if start_bit_point == 0:
        if end_bit_point == 0:
            sstore(out, 0, eadd(eadd(emul(s0, eadd(w0, w3)), emul(eadd(s1, s3), w2)), emul(s2, w3)))
            sstore(out, 1, emul(s1, w1))
            sstore(out, 2, emul(s2, w0))
            sstore(out, 3, emul(s3, w1))
        else:
            sstore(out, 0, eadd(emul(s0, w3), emul(s1, w2)))
            sstore(out, 1, [0, 0, 0])
            sstore(out, 2, eadd(eadd(emul(s0, w0), emul(s2, eadd(w0, w3))), emul(s3, w2)))
            sstore(out, 3, emul(eadd(s1, s3), w1))
    else:
        if end_bit_point == 0:
            sstore(out, 0, emul(eadd(s0, s2), w2))
            sstore(out, 1, eadd(eadd(emul(s0, w1), emul(s1, eadd(w0, w3))), emul(s3, w3)))
            sstore(out, 2, [0, 0, 0])
            sstore(out, 3, eadd(emul(s2, w1), emul(s3, w0)))
        else:
            sstore(out, 0, emul(s0, w2))
            sstore(out, 1, emul(s1, w3))
            sstore(out, 2, emul(s2, w2))
            sstore(out, 3, eadd(eadd(emul(eadd(s0, s2), w1), emul(s1, w0)), emul(s3, eadd(w0, w3))))
    return sload(out, 0), sload(out, 1), sload(out, 2), sload(out, 3)


def jagged_prefix_fixed(row_point, index_point, gamma: Ext, selector_len: Const, start_bits, end_bits, nbits: Const):
    # Candidate-specialized straight-line prefix. Generate the four equality
    # weights immediately before their transition instead of materializing and
    # reloading a 4 * nbits heap table for every block.
    s0 = [1, 0, 0]
    s1 = [0, 0, 0]
    s2 = [0, 0, 0]
    s3 = [0, 0, 0]
    gamma_bit = gamma
    for bit in unroll(0, selector_len):
        index_bit = eload(index_point * GEN ** (3 * bit))
        rx = emul(gamma_bit, index_bit)
        s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, eadd([1, 0, 0], index_bit), eadd(gamma_bit, rx), index_bit, rx, start_bits[GEN ** bit], end_bits[GEN ** bit])
        gamma_bit = emul(gamma_bit, gamma_bit)
    for bit in unroll(selector_len, nbits):
        row_bit = eload(row_point * GEN ** (3 * (bit - selector_len)))
        index_bit = eload(index_point * GEN ** (3 * bit))
        rx = emul(row_bit, index_bit)
        s0, s1, s2, s3 = jagged_step(s0, s1, s2, s3, eadd([1, 0, 0], eadd(eadd(row_bit, index_bit), rx)), eadd(row_bit, rx), eadd(index_bit, rx), rx, start_bits[GEN ** bit], end_bits[GEN ** bit])
    return s0, s1, s2, s3


def jagged_eval_terminal(m_idx: Const, fold_challenges, tail_challenges, claim_rows, col_bound_bits, gamma: Ext, gamma_powers, out):
    # Evaluate every complete row-major Jagged block at the single terminal
    # point (fold_challenges || tail_challenges). Selector coordinates use the
    # same unnormalized geometric weights as the native verifier. After the
    # committed coordinates, one fixed-zero top bit rejects an overflow carry
    # and handles an interval ending exactly at the cube boundary.
    total = [0, 0, 0]
    for batch in unroll(0, N_JAGGED_BATCHES):
        row = claim_rows * GEN ** (3 * SIZE_BITS * JAGGED_BATCH_ROW[batch])
        start_bits = col_bound_bits * GEN ** (SIZE_BITS * JAGGED_BATCH_COL[batch])
        end_bits = col_bound_bits * GEN ** (SIZE_BITS * (JAGGED_BATCH_COL[batch] + 1))
        p0, p1, p2, p3 = jagged_prefix_fixed(row, fold_challenges, gamma, JAGGED_BATCH_LOG[batch], start_bits, end_bits, LIG_TOTAL_FOLDS[m_idx])
        for bit in unroll(0, LIG_YR_LOG_LEN[m_idx]):
            row_bit = eload(row * GEN ** (3 * (LIG_TOTAL_FOLDS[m_idx] + bit - JAGGED_BATCH_LOG[batch])))
            index_bit = eload(tail_challenges * GEN ** (3 * bit))
            rx = emul(row_bit, index_bit)
            p0, p1, p2, p3 = jagged_step(p0, p1, p2, p3, eadd([1, 0, 0], eadd(eadd(row_bit, index_bit), rx)), eadd(row_bit, rx), eadd(index_bit, rx), rx, start_bits[GEN ** (LIG_TOTAL_FOLDS[m_idx] + bit)], end_bits[GEN ** (LIG_TOTAL_FOLDS[m_idx] + bit)])
        top = LIG_TOTAL_FOLDS[m_idx] + LIG_YR_LOG_LEN[m_idx]
        p0, p1, p2, p3 = jagged_step(p0, p1, p2, p3, [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], start_bits[GEN ** top], end_bits[GEN ** top])
        gamma_weight = eload(gamma_powers * GEN ** (3 * JAGGED_BATCH_BASE[batch]))
        total = eadd(total, emul(gamma_weight, p2))
    estore(out, total)
    return GEN ** 0


def eval_qpkd_claim_weight(point, point_len_g, slot: Const, fold_challenges, fold_cap_g, qpkdv_g):
    # q_pkd is the aligned first block of the dense Jagged witness. Its low
    # SLOT_STRIDE_LOG coordinates select the packed lane, the next coordinates
    # evaluate the table point, and every remaining committed coordinate is zero.
    weight = [1, 0, 0]
    for bit in unroll(0, SLOT_STRIDE_LOG):
        if (slot // (2 ** bit)) % 2 == 1:
            weight = emul(weight, eload(fold_challenges * GEN ** (3 * bit)))
        else:
            weight = emul(weight, eadd([1, 0, 0], eload(fold_challenges * GEN ** (3 * bit))))
    point_chain = HeapBuf(3 * (SIZE_BITS + 1))
    estore(point_chain, weight)
    ris_point = fold_challenges * GEN ** (3 * SLOT_STRIDE_LOG)
    for xk in mul_range(1, point_len_g):
        xk3 = xk ** 3
        factor = eadd([1, 0, 0], eadd(eload(point * xk3), eload(ris_point * xk3)))
        estore(point_chain * xk3 * GEN ** 3, emul(eload(point_chain * xk3), factor))
    q_hi_len_g = fold_cap_g / qpkdv_g
    assert log(q_hi_len_g) < SIZE_BITS
    q_hi = fold_challenges * qpkdv_g ** 3
    selector_chain = HeapBuf(3 * (SIZE_BITS + 1))
    estore(selector_chain, eload(point_chain * point_len_g ** 3))
    for xk in mul_range(1, q_hi_len_g):
        xk3 = xk ** 3
        estore(selector_chain * xk3 * GEN ** 3, emul(eload(selector_chain * xk3), eadd([1, 0, 0], eload(q_hi * xk3))))
    out = StackBuf(3)
    sstore(out, 0, eload(selector_chain * q_hi_len_g ** 3))
    return out


def open_stacked(m_idx: Const, fs0, fs1, fs2, fs3, target: Ext, commit_root_0, commit_root_1, commit_root_2, commit_root_3, cursor, sumcheck_out, inner_out, yr_at_tail_out):
    # The stacked Ligerito opening. m_idx is the flattened (rate, committed
    # log-size) configuration index, and every LIG_* table below reads row
    # m_idx (the match_range dispatch bakes one
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
    #   5. read the level's intro message, sample beta, and fold the query sum
    #      into the running target.
    # Then finish the tail sumcheck and evaluate every transparent basis once
    # at its terminal point; the final-message MLE enters as one multiplier.
    #
    # Returns (sumcheck_target, fold_challenges, final_msg, residual_total,
    # yr_log_n_g = g^yr_log_n, yr_pad_g = g^(YR_LOG_CAP - yr_log_n),
    # fold_cap_g = g^lenris, tail_challenges); the sumcheck target, inner total,
    # and yr_at_tail are written to the caller's out-buffers. yr_log_n_g/yr_pad_g
    # let the terminal zero-pin residual-slot coordinates beyond final_msg's
    # 2^yr_log_n cells (positions yr_log_n .. YR_LOG_CAP-1); fold_cap_g is the
    # certified total fold count the terminal pins its hinted claim lengths against.
    fs = [fs0, fs1, fs2, fs3]

    # The K opener binds the initial Merkle root as two transcript F192 scalars:
    # the first carries three raw F64 words and the second carries the fourth.
    # Level roots are likewise scalar-observed (via fs_next below).
    commit_root = [commit_root_0, commit_root_1, commit_root_2, commit_root_3]
    commit_root_word_0, commit_root_word_1 = hash_state_to_words(commit_root)
    fs = obs(fs, target)
    fs = obs(fs, commit_root_word_0)
    fs = obs(fs, commit_root_word_1)

    # The opening's scalars (sumcheck messages, level roots, nonces, final
    # message) ride the SHARED stream: msg_cursor is just the main stream
    # cursor, walked on in protocol order.
    msg_cursor = cursor
    fs, msg_u0, msg_cursor = fs_next(fs, msg_cursor)
    fs, msg_u2, msg_cursor = fs_next(fs, msg_cursor)
    round_quad_c = msg_u0
    round_quad_b = eadd(target, msg_u2)
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
    final_msg = HeapBuf(GEN ** (3 * LIG_YR_LEN[m_idx]))  # filled from the stream at the last level
    # Stream-bound level roots (filled as each root is read; index = level).
    level_roots = HeapBuf(GEN ** (4 * LIG_N_LEVELS[m_idx]))
    # ...and guest-filled accumulators (one slot per fold / per level / per query):
    fold_challenges = HeapBuf(GEN ** (3 * LIG_TOTAL_FOLDS[m_idx]))
    level_betas = HeapBuf(GEN ** (3 * LIG_N_LEVELS[m_idx]))
    alpha_weights = HeapBuf(GEN ** (3 * LIG_N_LEVELS[m_idx] * LIG_MAX_QUERIES[m_idx]))
    query_positions = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    query_bit_ptrs = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    # Explicit OOD claims bind every recursive Johnson-list commitment. L0
    # needs none: the opening claim itself is its post-commit binding value.
    ood_z = HeapBuf(GEN ** (3 * LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES * LIG_LOG_MSG_COLS_CAP))
    ood_betas = HeapBuf(GEN ** (3 * LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES))

    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        for j in unroll(0, LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl]):
            fold_idx = LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl] + j
            if LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx] != 0:
                nonce_v = eload(msg_cursor)
                msg_cursor = msg_cursor * GEN ** 3
                grind_check(fs[0], fs[1], fs[2], fs[3], nonce_v, GEN ** LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx])
                fs = absorb_nonce(fs, nonce_v)
            fs, fold_challenge = squeeze(fs)
            estore(fold_challenges * GEN ** (3 * fold_idx), fold_challenge)
            sumcheck_target = eadd(emul(eadd(emul(round_quad_a, fold_challenge), round_quad_b), fold_challenge), round_quad_c)
            fs, msg_a, msg_cursor = fs_next(fs, msg_cursor)
            fs, msg_b, msg_cursor = fs_next(fs, msg_cursor)
            round_quad_c = msg_a
            round_quad_b = eadd(sumcheck_target, msg_b)
            round_quad_a = msg_b

        if lvl == LIG_YR_LEVEL[m_idx]:
            for iy in unroll(0, LIG_YR_LEN[m_idx]):
                fs, yv, msg_cursor = fs_next(fs, msg_cursor)
                estore(final_msg * GEN ** (3 * iy), yv)
        else:
            fs, next_root_a, msg_cursor = fs_next(fs, msg_cursor)
            fs, next_root_b, msg_cursor = fs_next(fs, msg_cursor)
            next_root = hash_words_to_state(next_root_a, next_root_b)
            next_root_ptr = level_roots * GEN ** (4 * (lvl + 1))
            deref_192(next_root_ptr, next_root[0:3])
            next_root_ptr[GEN ** 3] = next_root[3]
            # OOD binding for the newly observed level-(lvl+1) commitment.
            # The random point has the just-folded witness dimension, namely
            # this level's message-column dimension.
            for os in unroll(0, LIG_OOD_SAMPLES[m_idx * LIG_MAX_LEVELS + lvl + 1]):
                oz = ood_z * GEN ** (3 * ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
                for t in unroll(0, LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + lvl]):
                    fs, oz_challenge = squeeze(fs)
                    estore(oz * GEN ** (3 * t), oz_challenge)
                fs, ood_y, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_u0, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_u2, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_beta = squeeze(fs)
                estore(ood_betas * GEN ** (3 * ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)), ood_beta)
                round_quad_c = eadd(round_quad_c, emul(ood_beta, ood_u0))
                round_quad_b = eadd(round_quad_b, emul(ood_beta, eadd(ood_y, ood_u2)))
                round_quad_a = eadd(round_quad_a, emul(ood_beta, ood_u2))
                sumcheck_target = eadd(sumcheck_target, emul(ood_beta, ood_y))
        q_nonce_words = eload(msg_cursor)
        q_nonce = q_nonce_words[0]
        assert q_nonce_words[1] == 0
        assert q_nonce_words[2] == 0
        msg_cursor = msg_cursor * GEN ** 3
        if LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl] != 0:
            grind_check(fs[0], fs[1], fs[2], fs[3], q_nonce_words, GEN ** LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl])
        else:
            assert q_nonce == 0
        fs = absorb_nonce(fs, q_nonce_words)

        sqz_chain_prefix = HeapBuf(GEN ** (3 * (LIG_MAX_SQUEEZES[m_idx] + 1)))
        sqz_chain_3 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        deref_192(sqz_chain_prefix, fs[0:3])
        sqz_chain_3[GEN ** 0] = fs[3]
        for xs in mul_range(1, GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]):
            xs3 = xs ** 3
            sqz_prefix = eload(sqz_chain_prefix * xs3)
            packed_word, next_c0, next_c1, next_c2, next_c3 = squeeze_step(sqz_prefix[0], sqz_prefix[1], sqz_prefix[2], sqz_chain_3[xs])
            next_prefix = [next_c0, next_c1, next_c2]
            estore(sqz_chain_prefix * xs3 * GEN ** 3, next_prefix)
            sqz_chain_3[xs * GEN] = next_c3
            query_ptr = xs ** (FIELD_BITS // LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            decode_query_bits(packed_word, query_positions * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, query_bit_ptrs * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
        sqz_final_prefix = eload(sqz_chain_prefix * GEN ** (3 * LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]))
        fs = [sqz_final_prefix[0], sqz_final_prefix[1], sqz_final_prefix[2], sqz_chain_3[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]]]

        query_alphas = HeapBuf(GEN ** (3 * LIG_MAX_INTERLEAVE[m_idx]))
        for t in unroll(0, LIG_LOG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            fs, alpha_v = squeeze(fs)
            estore(query_alphas * GEN ** (3 * t), alpha_v)
        row_eq_weights = HeapBuf(GEN ** (3 * LIG_MAX_INTERLEAVE[m_idx]))
        for i in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
            row_weight = eq_weight(fold_challenges * GEN ** (3 * LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl]), LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl], i, 0)
            estore(row_eq_weights * GEN ** (3 * i), row_weight)
        for i in unroll(0, LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            alpha_weight = eq_weight(query_alphas, LIG_LOG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl], i, 0)
            estore(alpha_weights * GEN ** (3 * (lvl * LIG_MAX_QUERIES[m_idx] + i)), alpha_weight)

        query_sum_chain = HeapBuf(GEN ** (3 * (LIG_MAX_QUERIES[m_idx] + 1)))
        estore(query_sum_chain, [0, 0, 0])
        for xe in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            xe3 = xe ** 3
            if lvl == 0:
                row_base = xe ** LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]
            else:
                row_base = xe ** (3 * LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl])
            row_ptr = merkle_leaf_rows * GEN ** LIG_ROWS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * row_base
            row_dot = [0, 0, 0]
            packed_row = StackBuf(LIG_PACKED_ROW_CAP)
            if lvl == 0:
                # Level zero stores independent F64 lanes contiguously. Fetch
                # complete three-word runs with DEREF_192, then handle the
                # (at most two-word) tail scalarly. This is pure transport: the
                # dot product below still treats every lane independently.
                row_width = LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]
                row_triplets = row_width // 3
                for jt in unroll(0, row_triplets):
                    j0 = 3 * jt
                    deref_192(row_ptr * GEN ** j0, packed_row[j0:j0 + 3])
                    for jj in unroll(0, 3):
                        jw = j0 + jj
                        lane = packed_row[jw]
                        weight = eload(row_eq_weights * GEN ** (3 * jw))
                        row_dot = eadd(row_dot, emul_base(lane, weight))
                for jw in unroll(3 * row_triplets, row_width):
                    lane = row_ptr[GEN ** jw]
                    packed_row[jw] = lane
                    weight = eload(row_eq_weights * GEN ** (3 * jw))
                    row_dot = eadd(row_dot, emul_base(lane, weight))
            else:
                for jw in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
                    # Higher levels consist of contiguous F192 values. Load one
                    # complete value per row lane instead of three scalar words.
                    deref_192(row_ptr * GEN ** (3 * jw), packed_row[3 * jw:3 * jw + 3])
                    row_word = [packed_row[3 * jw], packed_row[3 * jw + 1], packed_row[3 * jw + 2]]
                    weight = eload(row_eq_weights * GEN ** (3 * jw))
                    row_dot = eadd(row_dot, emul(row_word, weight))
            # Standard BLAKE3 of the packed row (a power of two of full 64-byte
            # blocks, within one 1024-byte chunk).
            leaf_hash_state = StackBuf(4)
            blake3(packed_row[0:4], packed_row[4:8], leaf_hash_state, step=0, end=1 // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl], root=1 // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl])
            for jb in unroll(1, LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl]):
                leaf_digest = StackBuf(4)
                blake3(packed_row[8 * jb:8 * jb + 4], packed_row[8 * jb + 4:8 * jb + 8], leaf_digest, cv=leaf_hash_state, step=jb, end=(jb + 1) // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl], root=(jb + 1) // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl])
                leaf_hash_state = leaf_digest
            node_0 = leaf_hash_state[0]
            node_1 = leaf_hash_state[1]
            node_2 = leaf_hash_state[2]
            node_3 = leaf_hash_state[3]
            prev_query_sum = eload(query_sum_chain * xe3)
            alpha_weight = eload(alpha_weights * GEN ** (3 * lvl * LIG_MAX_QUERIES[m_idx]) * xe3)
            estore(query_sum_chain * xe3 * GEN ** 3, eadd(prev_query_sum, emul(alpha_weight, row_dot)))
            direction_bits = query_bit_ptrs[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xe]
            path_base = xe ** (4 * LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            path_ptr = merkle_paths * GEN ** LIG_PATHS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * path_base
            root_0, root_1, root_2, root_3 = verify_merkle_path(node_0, node_1, node_2, node_3, path_ptr, direction_bits, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            if lvl == 0:
                ext_assert_eq([root_0, root_1, root_2], [commit_root_0, commit_root_1, commit_root_2])
                assert root_3 == commit_root_3
            else:
                # Heap stores unify the four computed digest words with the
                # transcript-bound root written when this level was introduced.
                root_ptr = level_roots * GEN ** (4 * lvl)
                estore(root_ptr, [root_0, root_1, root_2])
                root_ptr[GEN ** 3] = root_3
        level_query_sum = eload(query_sum_chain * GEN ** (3 * LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]))

        # Every level, including the last, ties its commitment in through an
        # intro message before drawing its separation challenge.
        fs, intro_u0, msg_cursor = fs_next(fs, msg_cursor)
        fs, intro_u2, msg_cursor = fs_next(fs, msg_cursor)
        fs, beta_lvl = squeeze(fs)
        estore(level_betas * GEN ** (3 * lvl), beta_lvl)
        round_quad_c = eadd(round_quad_c, emul(beta_lvl, intro_u0))
        round_quad_b = eadd(round_quad_b, emul(beta_lvl, eadd(level_query_sum, intro_u2)))
        round_quad_a = eadd(round_quad_a, emul(beta_lvl, intro_u2))
        sumcheck_target = eadd(sumcheck_target, emul(beta_lvl, level_query_sum))

    # ---- finish the sumcheck over the tail coordinates ----
    tail_challenges = HeapBuf(GEN ** (3 * YR_LOG_CAP))
    for j in unroll(0, LIG_YR_LOG_LEN[m_idx] - 1):
        fs, tail_c = squeeze(fs)
        estore(tail_challenges * GEN ** (3 * j), tail_c)
        sumcheck_target = eadd(round_quad_c, eadd(emul(tail_c, round_quad_b), emul(emul(tail_c, tail_c), round_quad_a)))
        fs, msg_a, msg_cursor = fs_next(fs, msg_cursor)
        fs, msg_b, msg_cursor = fs_next(fs, msg_cursor)
        round_quad_c = msg_a
        round_quad_b = eadd(sumcheck_target, msg_b)
        round_quad_a = msg_b
    # The closing round sends no following message.
    fs, tail_last = squeeze(fs)
    estore(tail_challenges * GEN ** (3 * (LIG_YR_LOG_LEN[m_idx] - 1)), tail_last)
    sumcheck_target = eadd(round_quad_c, eadd(emul(tail_last, round_quad_b), emul(emul(tail_last, tail_last), round_quad_a)))
    for j in unroll(LIG_YR_LOG_LEN[m_idx], YR_LOG_CAP):
        estore(tail_challenges * GEN ** (3 * j), [0, 0, 0])

    tail_w = StackBuf(3 * 2 * YR_LOG_CAP)
    for j in unroll(0, LIG_YR_LOG_LEN[m_idx]):
        sstore(tail_w, 2 * j, eadd([1, 0, 0], eload(tail_challenges * GEN ** (3 * j))))
        sstore(tail_w, 2 * j + 1, eload(tail_challenges * GEN ** (3 * j)))
    yr_at_tail = fold_final_msg(final_msg, tail_w, 0, LIG_YR_LOG_LEN[m_idx])

    # ---- per-level induced bases at the single terminal point ----
    inner_chain = HeapBuf(GEN ** (3 * (LIG_N_LEVELS[m_idx] + 1)))
    estore(inner_chain, [0, 0, 0])
    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        residual_chain = HeapBuf(GEN ** (3 * (LIG_MAX_QUERIES[m_idx] + 1)))
        estore(residual_chain, [0, 0, 0])
        for xr in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            xr3 = xr ** 3
            basis_w = StackBuf(3 * LIG_LOG_MSG_COLS_CAP)
            basis_scalar = query_positions[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xr]
            inv_idx = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl]
            vanish_inv = [LIG_VANISH_INVS[3 * inv_idx], LIG_VANISH_INVS[3 * inv_idx + 1], LIG_VANISH_INVS[3 * inv_idx + 2]]
            sstore(basis_w, 0, emul_base(basis_scalar, vanish_inv))
            for t in unroll(1, LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + lvl]):
                val_idx = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t - 1
                vanish_val = [LIG_VANISH_VALS[3 * val_idx], LIG_VANISH_VALS[3 * val_idx + 1], LIG_VANISH_VALS[3 * val_idx + 2]]
                if t == 1:
                    basis_chain = emul_base(basis_scalar, eadd_base(basis_scalar, vanish_val))
                else:
                    basis_chain = emul(basis_chain, eadd(basis_chain, vanish_val))
                inv_idx = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t
                vanish_inv = [LIG_VANISH_INVS[3 * inv_idx], LIG_VANISH_INVS[3 * inv_idx + 1], LIG_VANISH_INVS[3 * inv_idx + 2]]
                sstore(basis_w, t, emul(basis_chain, vanish_inv))
            prefix_eq = [1, 0, 0]
            for t in unroll(0, LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl]):
                fold_c = eload(fold_challenges * GEN ** (3 * (LIG_RESIDUAL_FOLD_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t)))
                basis = sload(basis_w, t)
                prefix_eq = emul(prefix_eq, eadd([1, 0, 0], emul(fold_c, eadd([1, 0, 0], basis))))
            for j in unroll(0, LIG_YR_LOG_LEN[m_idx]):
                tail_c = eload(tail_challenges * GEN ** (3 * j))
                prefix_eq = emul(prefix_eq, eadd([1, 0, 0], emul(tail_c, eadd([1, 0, 0], sload(basis_w, LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl] + j)))))
            prev_residual = eload(residual_chain * xr3)
            alpha_weight = eload(alpha_weights * GEN ** (3 * lvl * LIG_MAX_QUERIES[m_idx]) * xr3)
            estore(residual_chain * xr3 * GEN ** 3, eadd(prev_residual, emul(alpha_weight, prefix_eq)))
        prior_inner = eload(inner_chain * GEN ** (3 * lvl))
        beta_lvl = eload(level_betas * GEN ** (3 * lvl))
        residual_total = eload(residual_chain * GEN ** (3 * LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]))
        estore(inner_chain * GEN ** (3 * (lvl + 1)), eadd(prior_inner, emul(beta_lvl, residual_total)))

    # Explicit OOD eq bases at the same terminal point.
    ood_inner = [0, 0, 0]
    for ood_lvl in unroll(1, LIG_N_LEVELS[m_idx]):
        z_len = LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + ood_lvl - 1]
        z_folded = z_len - LIG_YR_LOG_LEN[m_idx]
        ris_start = LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + ood_lvl]
        for os in unroll(0, LIG_OOD_SAMPLES[m_idx * LIG_MAX_LEVELS + ood_lvl]):
            oz = ood_z * GEN ** (3 * (ood_lvl * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
            scalar = eload(ood_betas * GEN ** (3 * (ood_lvl * LIG_MAX_OOD_SAMPLES + os)))
            for t in unroll(0, z_folded):
                zt = eload(oz * GEN ** (3 * t))
                fold_c = eload(fold_challenges * GEN ** (3 * (ris_start + t)))
                scalar = emul(scalar, eadd(eadd([1, 0, 0], zt), fold_c))
            for t in unroll(0, LIG_YR_LOG_LEN[m_idx]):
                zt = eload(oz * GEN ** (3 * (z_folded + t)))
                scalar = emul(scalar, eadd(eadd([1, 0, 0], zt), eload(tail_challenges * GEN ** (3 * t))))
            ood_inner = eadd(ood_inner, scalar)
    inner_total = eadd(eload(inner_chain * GEN ** (3 * LIG_N_LEVELS[m_idx])), ood_inner)
    estore(sumcheck_out, sumcheck_target)
    estore(inner_out, inner_total)
    estore(yr_at_tail_out, yr_at_tail)
    return fold_challenges, final_msg, GEN ** LIG_YR_LOG_LEN[m_idx], GEN ** (YR_LOG_CAP - LIG_YR_LOG_LEN[m_idx]), GEN ** LIG_TOTAL_FOLDS[m_idx], tail_challenges


def exponent_tables():
    # Read-only lookup tables over the exponent domain, indexed at runtime
    # g-powers (so they must be heap, not stack): g_logs_pow2[g^j] = 2^j is 2
    # raised to a g-power's log, and g_squares[g^j] = g^(2^j) turns integer
    # sums of powers of two into field products. Returns the 2 pointers.
    # Both tables span SIZE_BITS: verify_log2_ceil bounds its result by
    # SIZE_BITS (assert log(g_log) < SIZE_BITS), so g_log reaches g^(SIZE_BITS-1)
    # and indexes g_logs_pow2 there; sizing to COUNT_BITS would leave that lookup
    # reading an unwritten (prover-chosen) cell.
    g_logs_pow2 = HeapBuf(SIZE_BITS)
    for j in unroll(0, SIZE_BITS):
        g_logs_pow2[GEN ** j] = 2 ** j
    g_squares = HeapBuf(SIZE_BITS)
    sq_run = GEN
    for j in unroll(0, SIZE_BITS):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    return g_logs_pow2, g_squares


def verify_sub(pi_0, pi_1, pi_2, pi_3, seed_0, seed_1, seed_2, seed_3, g_logs_pow2, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement
    # (pi_0, pi_1). All proof data is hinted HERE: each call pops the next
    # sub-proof's entry of every witness stream, so the body lowers once and
    # main just calls it per statement. The exponent lookup tables are shared
    # read-only across calls; the deferred-claim data is written to
    # `defer_out`.
    #
    # Flow (mirrors cpu::verify):
    #   1. seed the Fiat-Shamir sponge from the statement + program digest;
    #   2. announced sizes, then certify every structural log against them
    #      (count gadget log2_ceil: tau per table, log_mem);
    #   3. bind the commitment root; ONE RLC-batched GKR for all three trees (count padded
    #      to the pair's depth) at runtime depth, ONE shared point zeta;
    #   4. derive the block kappas, certify the GKR side depths; balance check
    #      with advice-decomposed padding ladders; 3x leaf decomposition, DERIVING
    #      each side's table share from its GKR claim (pooling the
    #      committed-coordinate claims); the stacked-bytecode reduction (deferred);
    #   5. ONE batched zerocheck for all seven tables, n = max_t tau_t rounds at the
    #      shared point zeta, target derived from the leaf claims (sumcheck_round4);
    #   6. public-input claim + BLAKE3 pin claims (telescoped prefix MLE);
    #   7. flock reduction: univariate-skip zerocheck + lincheck (matrix
    #      evaluation deferred);
    #   8. ring-switch fronts (shared linear map, transpose in-circuit);
    #   9. gamma-combine everything, certify the committed size m, dispatch
    #      the stacked Ligerito opening (open_stacked), and assert its
    #      eval_b terminal;
    #  10. export the deferred-claim region for the aggregation.
    # Claim pool: values of every committed-coordinate claim, in decompose order
    # (their points are the GKR ζ's, resolvable from the baked block structure).
    # `1 + g^(2^k)` per bit position, in FRAME cells: the bit-ladder rebuilds
    # below (padding surplus, placement offsets) each need this factor once per
    # bit, and a StackBuf entry is an instruction operand, where the g_squares
    # HeapBuf costs a load and an add every time.
    gsq_plus = StackBuf(SIZE_BITS)
    for k in unroll(0, SIZE_BITS):
        gsq_plus[k] = 1 + g_squares[GEN ** k]
    claim_pool = HeapBuf(3 * N_CLAIMS)
    # certified low dimension (cplen) per pooled claim, filled as the pool is
    # built (from the in-scope certified kappa/tau); the terminal pins each
    # claim's hinted lengths against it.
    claim_cplen_g = HeapBuf(N_CLAIMS)
    # The ONE shared GKR leaf point (all three trees reduce to it).

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    fs = [TRANSCRIPT_SEED_0, TRANSCRIPT_SEED_1, TRANSCRIPT_SEED_2, TRANSCRIPT_SEED_3]
    fs = obs_base(fs, seed_0)
    fs = obs_base(fs, seed_1)
    fs = obs_base(fs, seed_2)
    fs = obs_base(fs, seed_3)
    fs = obs_base(fs, pi_0)
    fs = obs_base(fs, pi_1)
    fs = obs_base(fs, pi_2)
    fs = obs_base(fs, pi_3)
    stream = HeapBuf(3 * STREAM_CAP)
    hint_witness(stream[0:3 * STREAM_CAP], "stream")
    cursor = stream  # the proof stream is replayed word by word; cursor walks it (advance = * g)

    # ---- announced sizes: used-memory prefix + row counts, then the PCS rate ----
    sizes = StackBuf(N_TABLES + 1)
    for i in unroll(0, N_TABLES + 1):
        fs, x, cursor = fs_next(fs, cursor)
        assert x[1] == 0
        assert x[2] == 0
        sizes[i] = x[0]
    fs, log_inv_rate_ext, cursor = fs_next(fs, cursor)
    assert log_inv_rate_ext[1] == 0
    assert log_inv_rate_ext[2] == 0
    log_inv_rate = log_inv_rate_ext[0]
    g_log_inv_rate = g_power_of_word(log_inv_rate, g_squares, COUNT_BITS)
    rate_sel = g_log_inv_rate / GEN  # g^(log_inv_rate - 1)
    assert log(rate_sel) < LIG_N_RATES

    # ---- structural logs: derive g^log_mem, compute the taus ----
    # The stream announced the sizes as integer WORDS; the shape-generic phases
    # need them as G-POWERS (loop bounds, match_range scrutinees). dims_g[0] is
    # derived from mem_used; dims_g[1 + t] = g^tau_t comes from the count gadget.
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_5], all computed
    # One exact decomposition drives both MEM/MFCNT Jagged heights and derives
    # the canonical logical log_mem = max(MIN_LOG_MEM, ceil_log2(mem_used)).
    memory_bits = HeapBuf(COUNT_BITS)
    g_log_mem, g_memory_used = log2_ceil_word(sizes[0], memory_bits, g_logs_pow2, g_squares, MIN_LOG_MEM, COUNT_BITS, 0)
    assert sizes[0] != 0
    assert sizes[0] != 1
    assert log(g_log_mem) < COUNT_BITS
    dims_g[GEN ** 0] = g_log_mem
    # count gadget: g^tau_t = log2_ceil_word(count_t), which also returns
    # g^count_t (for the padding-surplus certification).
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
    # The ONE bus depth, COMPUTED (not hinted): mu = log2_ceil(Σ_b 2^κ_b) over
    # PUSH's blocks — pull matches by pairing, the count tree is padded to it.
    push_total = GEN ** 0
    for b in unroll(SIDE_BLOCK_START[PUSH_SIDE], SIDE_BLOCK_START[PUSH_SIDE + 1]):
        push_total *= g_squares[block_kappa[GEN ** b]]  # g^(sum of 2^kappa)
    g_bus_mu = log2_ceil_in_the_exponent(push_total, g_logs_pow2, g_squares, 0, SIZE_BITS)
    g_bus_mu3 = g_bus_mu ** 3
    zeta = HeapBuf(g_bus_mu3)  # the ONE shared GKR point: three words per coordinate

    # ---- commitment root (two extension scalars / four raw words) ----
    fs, commit_root_word_0, cursor = fs_next(fs, cursor)
    fs, commit_root_word_1, cursor = fs_next(fs, cursor)
    commit_root = hash_words_to_state(commit_root_word_0, commit_root_word_1)
    commit_root_0 = commit_root[0]
    commit_root_1 = commit_root[1]
    commit_root_2 = commit_root[2]
    commit_root_3 = commit_root[3]

    # ---- bus challenges (F192 provides the soundness margin without grinding) ----
    fs, alpha = squeeze(fs)
    fs, gamma = squeeze(fs)

    # ---- ONE GKR grand product: push, pull, and count RLC-batched ----
    # Push and pull have equal depth (matched blocks) and the count tree is
    # padded with identity leaves up to it (product unchanged), so a single
    # sumcheck serves all three trees. Radix four contracts two binary levels
    # per layer; after checking the combined product identity, a fresh λ pins
    # the individual values. All three trees reduce to one shared point zeta.
    # State threads through write-once heap chains: layer state indexed by the
    # layer cursor, round state by a position pointer advancing per round.
    gkr_roots = StackBuf(3 * N_GKR_SIDES)
    gkr_claims = StackBuf(3 * N_GKR_SIDES)
    gkr_layer_size = g_bus_mu * GEN ** 2  # runtime size in the exponent: mu + 2 slots
    gkr_layer_size3 = gkr_layer_size ** 3
    gkr_layer_fs_prefix = HeapBuf(gkr_layer_size3)
    gkr_layer_fs3 = HeapBuf(gkr_layer_size)
    gkr_layer_cursor = HeapBuf(gkr_layer_size)
    gkr_layer_claim = HeapBuf(gkr_layer_size3)    # push's running value
    gkr_layer_claim_b = HeapBuf(gkr_layer_size3)  # pull's
    gkr_layer_claim_c = HeapBuf(gkr_layer_size3)  # count's
    gkr_layer_lambda = HeapBuf(gkr_layer_size3)   # the layer's combiner
    gkr_layer_row = HeapBuf(gkr_layer_size)
    gkr_layer_round_pos = HeapBuf(gkr_layer_size)
    gkr_round_fs_prefix = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_round_fs3 = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_cursor = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_claim = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_pts = HeapBuf(3 * GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    fs, root_push, cursor = fs_next(fs, cursor)
    fs, root_pull, cursor = fs_next(fs, cursor)
    fs, root_count, cursor = fs_next(fs, cursor)
    fs, initial_layer_lambda = squeeze(fs)
    estore(gkr_layer_lambda, initial_layer_lambda)
    deref_192(gkr_layer_fs_prefix, fs[0:3])
    gkr_layer_fs3[GEN ** 0] = fs[3]
    gkr_layer_cursor[GEN ** 0] = cursor
    estore(gkr_layer_claim, root_push)
    estore(gkr_layer_claim_b, root_pull)
    estore(gkr_layer_claim_c, root_count)
    gkr_layer_row[GEN ** 0] = gkr_pts
    gkr_layer_round_pos[GEN ** 0] = GEN ** 0

    # Contract two binary product levels at a time. An odd-depth tree starts
    # with its root-most binary layer.
    gkr_pair_bounds = HeapBuf(COUNT_BITS)
    gkr_depth_odd = HeapBuf(COUNT_BITS)
    gkr_depth_shift = HeapBuf(COUNT_BITS)
    for depth in unroll(0, COUNT_BITS):
        gkr_pair_bounds[GEN ** depth] = GEN ** (depth // 2)
        if (depth // 2) * 2 == depth:
            gkr_depth_odd[GEN ** depth] = 0
            gkr_depth_shift[GEN ** depth] = 1
        else:
            gkr_depth_odd[GEN ** depth] = 1
            gkr_depth_shift[GEN ** depth] = GEN

    if gkr_depth_odd[g_bus_mu] == 1:
        x_layer = GEN ** 0
        layer_prefix = eload(gkr_layer_fs_prefix * x_layer ** 3)
        layer_fs = [layer_prefix[0], layer_prefix[1], layer_prefix[2], gkr_layer_fs3[x_layer]]
        lam = eload(gkr_layer_lambda * x_layer ** 3)
        claim_l = eadd(eload(gkr_layer_claim * x_layer ** 3), emul(lam, eadd(eload(gkr_layer_claim_b * x_layer ** 3), emul(lam, eload(gkr_layer_claim_c * x_layer ** 3)))))
        point_row = gkr_layer_row[x_layer]
        round_pos = gkr_layer_round_pos[x_layer]
        nextrow = point_row * GEN ** (3 * MU_CAP)
        round_pos3 = round_pos ** 3
        deref_192(gkr_round_fs_prefix * round_pos3, layer_fs[0:3])
        gkr_round_fs3[round_pos] = layer_fs[3]
        gkr_round_cursor[round_pos] = gkr_layer_cursor[x_layer]
        estore(gkr_round_claim * round_pos3, claim_l)
        final_pos = round_pos * x_layer
        final_pos3 = final_pos ** 3
        tail_fs_prefix = eload(gkr_round_fs_prefix * final_pos3)
        tail_fs = [tail_fs_prefix[0], tail_fs_prefix[1], tail_fs_prefix[2], gkr_round_fs3[final_pos]]
        tcur = gkr_round_cursor[final_pos]
        tclaim = eload(gkr_round_claim * final_pos3)
        tail_fs, e0_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_count, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_count, tcur = fs_next(tail_fs, tcur)
        product_claim = eadd(emul(e0_push, e1_push), emul(lam, eadd(emul(e0_pull, e1_pull), emul(lam, emul(e0_count, e1_count)))))
        ext_assert_eq(tclaim, product_claim)
        tail_fs, layer_challenge = squeeze(tail_fs)
        estore(nextrow, layer_challenge)
        xln = x_layer * GEN
        xln3 = xln ** 3
        estore(gkr_layer_claim * xln3, eadd(e0_push, emul(layer_challenge, eadd(e0_push, e1_push))))
        estore(gkr_layer_claim_b * xln3, eadd(e0_pull, emul(layer_challenge, eadd(e0_pull, e1_pull))))
        estore(gkr_layer_claim_c * xln3, eadd(e0_count, emul(layer_challenge, eadd(e0_count, e1_count))))
        tail_fs, tail_lambda = squeeze(tail_fs)  # fresh λ pins the tail individuals
        estore(gkr_layer_lambda * xln3, tail_lambda)
        deref_192(gkr_layer_fs_prefix * xln3, tail_fs[0:3])
        gkr_layer_fs3[xln] = tail_fs[3]
        gkr_layer_cursor[xln] = tcur
        gkr_layer_row[xln] = nextrow
        gkr_layer_round_pos[xln] = round_pos * x_layer * GEN

    pair_bound = gkr_pair_bounds[g_bus_mu]
    for x_pair in mul_range(1, pair_bound):
        x_layer = x_pair * x_pair * gkr_depth_shift[g_bus_mu]
        x_layer3 = x_layer ** 3
        layer_prefix = eload(gkr_layer_fs_prefix * x_layer3)
        layer_fs = [layer_prefix[0], layer_prefix[1], layer_prefix[2], gkr_layer_fs3[x_layer]]
        lam = eload(gkr_layer_lambda * x_layer3)
        claim_l = eadd(eload(gkr_layer_claim * x_layer3), emul(lam, eadd(eload(gkr_layer_claim_b * x_layer3), emul(lam, eload(gkr_layer_claim_c * x_layer3)))))
        point_row = gkr_layer_row[x_layer]
        round_pos = gkr_layer_round_pos[x_layer]
        nextrow = point_row * GEN ** (3 * MU_CAP)
        round_pos3 = round_pos ** 3
        deref_192(gkr_round_fs_prefix * round_pos3, layer_fs[0:3])
        gkr_round_fs3[round_pos] = layer_fs[3]
        gkr_round_cursor[round_pos] = gkr_layer_cursor[x_layer]
        estore(gkr_round_claim * round_pos3, claim_l)
        for x_round in mul_range(1, x_layer):
            ip = round_pos * x_round
            ip3 = ip ** 3
            round_prefix = eload(gkr_round_fs_prefix * ip3)
            nfs0, nfs1, nfs2, nfs3, ncur, nclaim, rk = sumcheck_round5(round_prefix[0], round_prefix[1], round_prefix[2], gkr_round_fs3[ip], gkr_round_cursor[ip], eload(gkr_round_claim * ip3), eload(point_row * x_round ** 3))
            estore(nextrow * x_round ** 3 * GEN ** 6, rk)
            pos_next = ip * GEN
            pos_next3 = pos_next ** 3
            next_prefix = [nfs0, nfs1, nfs2]
            estore(gkr_round_fs_prefix * pos_next3, next_prefix)
            gkr_round_fs3[pos_next] = nfs3
            gkr_round_cursor[pos_next] = ncur
            estore(gkr_round_claim * pos_next3, nclaim)
        final_pos = round_pos * x_layer
        final_pos3 = final_pos ** 3
        tail_prefix = eload(gkr_round_fs_prefix * final_pos3)
        tail_fs = [tail_prefix[0], tail_prefix[1], tail_prefix[2], gkr_round_fs3[final_pos]]
        tcur = gkr_round_cursor[final_pos]
        tclaim = eload(gkr_round_claim * final_pos3)
        tail_fs, e0_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e2_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e3_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e2_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e3_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_count, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_count, tcur = fs_next(tail_fs, tcur)
        tail_fs, e2_count, tcur = fs_next(tail_fs, tcur)
        tail_fs, e3_count, tcur = fs_next(tail_fs, tcur)
        push_product = emul(emul(e0_push, e1_push), emul(e2_push, e3_push))
        pull_product = emul(emul(e0_pull, e1_pull), emul(e2_pull, e3_pull))
        count_product = emul(emul(e0_count, e1_count), emul(e2_count, e3_count))
        ext_assert_eq(tclaim, eadd(push_product, emul(lam, eadd(pull_product, emul(lam, count_product)))))
        tail_fs, c0 = squeeze(tail_fs)
        tail_fs, c1 = squeeze(tail_fs)
        estore(nextrow, c0)
        estore(nextrow * GEN ** 3, c1)
        push_lo = eadd(e0_push, emul(c0, eadd(e0_push, e1_push)))
        push_hi = eadd(e2_push, emul(c0, eadd(e2_push, e3_push)))
        pull_lo = eadd(e0_pull, emul(c0, eadd(e0_pull, e1_pull)))
        pull_hi = eadd(e2_pull, emul(c0, eadd(e2_pull, e3_pull)))
        count_lo = eadd(e0_count, emul(c0, eadd(e0_count, e1_count)))
        count_hi = eadd(e2_count, emul(c0, eadd(e2_count, e3_count)))
        xln = x_layer * GEN ** 2
        xln3 = xln ** 3
        estore(gkr_layer_claim * xln3, eadd(push_lo, emul(c1, eadd(push_lo, push_hi))))
        estore(gkr_layer_claim_b * xln3, eadd(pull_lo, emul(c1, eadd(pull_lo, pull_hi))))
        estore(gkr_layer_claim_c * xln3, eadd(count_lo, emul(c1, eadd(count_lo, count_hi))))
        tail_fs, tail_lambda = squeeze(tail_fs)
        estore(gkr_layer_lambda * xln3, tail_lambda)
        deref_192(gkr_layer_fs_prefix * xln3, tail_fs[0:3])
        gkr_layer_fs3[xln] = tail_fs[3]
        gkr_layer_cursor[xln] = tcur
        gkr_layer_row[xln] = nextrow
        gkr_layer_round_pos[xln] = round_pos * x_layer * GEN
    final_prefix = eload(gkr_layer_fs_prefix * g_bus_mu3)
    fs = [final_prefix[0], final_prefix[1], final_prefix[2], gkr_layer_fs3[g_bus_mu]]
    cursor = gkr_layer_cursor[g_bus_mu]
    final_point_row = gkr_layer_row[g_bus_mu]
    for xt in mul_range(1, g_bus_mu):
        xt3 = xt ** 3
        estore(zeta * xt3, eload(final_point_row * xt3))
    sstore(gkr_roots, PUSH_SIDE, root_push)
    sstore(gkr_roots, PULL_SIDE, root_pull)
    sstore(gkr_roots, COUNT_SIDE, root_count)
    sstore(gkr_claims, PUSH_SIDE, eload(gkr_layer_claim * g_bus_mu3))
    sstore(gkr_claims, PULL_SIDE, eload(gkr_layer_claim_b * g_bus_mu3))
    sstore(gkr_claims, COUNT_SIDE, eload(gkr_layer_claim_c * g_bus_mu3))

    # ---- count root nonzero ----
    count_root = sload(gkr_roots, COUNT_SIDE)
    count_root_inv = ediv([1, 0, 0], count_root)

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
    # ONE ladder per (side, table), not per block: every flush block of table t
    # takes its kappa from the same certified source (tau_t) and its real row
    # count from the same count_t, so the whole group shares one DELTA, and
    #     prod_b (gamma + fp_b)^DELTA == (prod_b (gamma + fp_b))^DELTA.
    # The framework blocks are REAL_IS_FULL_CUBE (= N_TABLES, so the table loop
    # skips them): real = 2^kappa makes DELTA = 0 by construction, and the ladder
    # they run today is forced to return 1 anyway -- g^DELTA == g^(2^kappa)/g^real
    # == 1 with COUNT_BITS bits far below the group order pins every bit to zero.
    # Dropping it removes a hint, not a constraint.
    pad_products = HeapBuf(3 * 2)
    for s in unroll(0, 2):
        side_pad_product = [1, 0, 0]
        for t in unroll(0, N_TABLES):
            group_base = [1, 0, 0]
            for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
                if BLOCK_REAL_TABLE[b] == t:
                    pad_fp = [0, 0, 0]
                    alpha_pow = [1, 0, 0]
                    for i in unroll(0, BLOCK_COORD_COUNT[b]):
                        pad_fp = eadd(pad_fp, emul_base(COORD_PAD_VAL[BLOCK_COORD_OFF[b] + i], alpha_pow))
                        alpha_pow = emul(alpha_pow, alpha)
                    group_base = emul(group_base, eadd(gamma, pad_fp))
            g_two_kappa = g_squares[dims_g[GEN ** (t + 1)]]  # g^(2^tau_t), the group's kappa
            g_real = count_gpows[GEN ** t]                   # g^count_t
            g_delta_want = g_two_kappa / g_real  # g^DELTA (feeds the advice below)
            pad_bits = HeapBuf(GEN ** COUNT_BITS)
            hint_decompose_bits_exponent(pad_bits, g_delta_want, COUNT_BITS)
            ladder = [1, 0, 0]
            ladder_square = group_base
            g_delta = GEN ** 0
            for j in unroll(0, COUNT_BITS):
                pad_bit = pad_bits[GEN ** j]
                assert pad_bit * pad_bit == pad_bit
                ladder = emul(ladder, eadd([1, 0, 0], emul_base(pad_bit, eadd(ladder_square, [1, 0, 0]))))
                g_delta *= (1 + pad_bit * gsq_plus[j])  # g^DELTA
                ladder_square = emul(ladder_square, ladder_square)
            assert g_real * g_delta == g_two_kappa  # count_t + DELTA_t == 2^tau_t
            side_pad_product = emul(side_pad_product, ladder)
        estore(pad_products * GEN ** (3 * s), side_pad_product)
    lhsb = emul(sload(gkr_roots, PUSH_SIDE), eload(pad_products * GEN ** (3 * PULL_SIDE)))
    rhsb = emul(sload(gkr_roots, PULL_SIDE), eload(pad_products * GEN ** (3 * PUSH_SIDE)))
    ext_assert_eq(lhsb, rhsb)

    # ---- 3× leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    bytecode_vals = HeapBuf(3 * BYTECODE_COLS)
    hint_witness(bytecode_vals[0:3 * BYTECODE_COLS], "bytecode_vals")
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); the Public
    # (bytecode) coordinate values are hinted (bytecode_vals) and exported as deferred
    # claims; Index coordinates use the factored index MLE.
    # Pull's blocks mirror push's (same kappas, same offsets — generator-
    # asserted pairing) and share zeta, so each pull block REUSES its push
    # twin's eq_hi and Index-MLE value instead of recomputing them; its column
    # values are mostly deduped pool reads (COORD_FRESH). The identity check
    # against pull's own GKR claim still binds everything.
    bus_table_total = HeapBuf(3 * N_GKR_SIDES)  # per side, what its tables' blocks owe
    block_eq_hi = HeapBuf(3 * N_BLOCKS)      # per push block, reused by its pull twin
    block_eq_all = HeapBuf(3 * N_BLOCKS)     # every block's eq_hi, for the bus forms below
    block_index_mle = HeapBuf(3 * N_BLOCKS)  # per push block with an Index coord
    for s in unroll(0, N_GKR_SIDES):
        acc = [0, 0, 0]
        selector_sum = [0, 0, 0]
        zeta_zs = zeta
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_public_idx = 0
            kappa_g = block_kappa[GEN ** b]
            kappa_g3 = kappa_g ** 3
            assert log(kappa_g) < SIZE_BITS
            if s == PULL_SIDE:
                eq_hi = eload(block_eq_hi * GEN ** (3 * (b - SIDE_BLOCK_START[PULL_SIDE])))
            else:
                # eq_hi over the ζ coords above κ against the selector bits
                # derived below; the selector length is mu_s − κ = g^mu_s / g^κ.
                sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                assert log(sel_len_g) < SIZE_BITS
                zeta_hi = zeta_zs * kappa_g3
                # selector bits = offset >> κ: advice-decompose the offset's bits
                # and read them shifted by κ. Rebuilding g^offset from those high
                # bits alone (weights g^(2^(κ+k))) and asserting it equals
                # block_off_g pins the bits AND the κ-alignment in one shot.
                # The low κ bit cells are written but never read.
                offset_bits = HeapBuf(GEN ** SIZE_BITS)
                hint_decompose_bits_exponent(offset_bits, block_off_g[GEN ** b], SIZE_BITS)
                sel_bits = offset_bits * kappa_g  # bits of sel = offset >> κ
                eq_chain = HeapBuf(3 * (MU_CAP + 2))
                goff_chain = HeapBuf(MU_CAP + 2)  # rebuild g^offset from the high bits
                estore(eq_chain, [1, 0, 0])
                goff_chain[GEN ** 0] = 1
                for xk in mul_range(1, sel_len_g):
                    xk3 = xk ** 3
                    sbit = sel_bits[xk]
                    assert sbit * sbit == sbit
                    prev_eq = eload(eq_chain * xk3)
                    zeta_v = eload(zeta_hi * xk3)
                    estore(eq_chain * xk3 * GEN ** 3, emul(prev_eq, eadd_base(1 + sbit, zeta_v)))
                    goff_chain[xk * GEN] = goff_chain[xk] * (1 + sbit * (g_squares[kappa_g * xk] + 1))  # weight g^(2^(κ+k))
                eq_hi = eload(eq_chain * sel_len_g ** 3)
                assert goff_chain[sel_len_g] == block_off_g[GEN ** b]  # bits == offset >> κ, κ-aligned
                if s == PUSH_SIDE:
                    estore(block_eq_hi * GEN ** (3 * b), eq_hi)
            selector_sum = eadd(selector_sum, eq_hi)
            estore(block_eq_all * GEN ** (3 * b), eq_hi)
            # A TABLE's block contributes only its padding mass here: the batched
            # zerocheck settles its fingerprint from that table's column evaluations,
            # so no value is streamed for it. Only the framework blocks (boundary,
            # memory, bytecode) still decompose.
            if BLOCK_REAL_TABLE[b] == REAL_IS_FULL_CUBE:
                # inner fingerprint Σ_i α^i · coord_i(ζ_lo); count side uses α=1,γ=0.
                inner_sum = [0, 0, 0]
                alpha_pow = [1, 0, 0]
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_CONST:
                        coord_val = ebase(COORD_CONST[BLOCK_COORD_OFF[b] + i])
                    if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_COL:
                        if COORD_FRESH[BLOCK_COORD_OFF[b] + i] == 1:
                            fs, coord_val, cursor = fs_next(fs, cursor)
                            estore(claim_pool * GEN ** (3 * COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]), coord_val)
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]] = kappa_g  # cplen = block kappa
                        else:
                            coord_val = eload(claim_pool * GEN ** (3 * COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]))
                    if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_GCOL:
                        if COORD_FRESH[BLOCK_COORD_OFF[b] + i] == 1:
                            fs, rawv, cursor = fs_next(fs, cursor)
                            estore(claim_pool * GEN ** (3 * COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]), rawv)
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]] = kappa_g  # cplen = block kappa
                        else:
                            rawv = eload(claim_pool * GEN ** (3 * COORD_CLAIM_SLOT[BLOCK_COORD_OFF[b] + i]))
                        coord_val = emul_base(COORD_CONST[BLOCK_COORD_OFF[b] + i], rawv)
                    if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_INDEX:
                        if s == PULL_SIDE:
                            coord_val = eload(block_index_mle * GEN ** (3 * (b - SIDE_BLOCK_START[PULL_SIDE])))
                        else:
                            idx_chain = HeapBuf(3 * (MU_CAP + 2))
                            estore(idx_chain, [1, 0, 0])
                            for xt in mul_range(1, kappa_g):
                                xt3 = xt ** 3
                                idx_prev = eload(idx_chain * xt3)
                                zeta_v = eload(zeta_zs * xt3)
                                idx_factor = eadd([1, 0, 0], emul_base(idxc_tab[xt], zeta_v))
                                estore(idx_chain * xt3 * GEN ** 3, emul(idx_prev, idx_factor))
                            coord_val = eload(idx_chain * kappa_g3)
                            if s == PUSH_SIDE:
                                estore(block_index_mle * GEN ** (3 * b), coord_val)
                    if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_PUBLIC:
                        # push and pull share zeta, so BOTH bytecode blocks read the
                        # same public evaluations (indexed per block, not globally).
                        coord_val = eload(bytecode_vals * GEN ** (3 * block_public_idx))
                        block_public_idx += 1
                    if s == COUNT_SIDE:
                        inner_sum = eadd(inner_sum, coord_val)
                    else:
                        inner_sum = eadd(inner_sum, emul(alpha_pow, coord_val))
                        alpha_pow = emul(alpha_pow, alpha)
                if s == COUNT_SIDE:
                    acc = eadd(acc, emul(eq_hi, inner_sum))
                else:
                    acc = eadd(acc, emul(eq_hi, eadd(gamma, inner_sum)))
        acc = eadd(acc, eadd([1, 0, 0], selector_sum))
        # What the tables' blocks owe this side: its GKR leaf value less the
        # framework decomposition. DERIVED, not read: a transmitted total would be a
        # free value in its own check. The batched zerocheck's target pins it below.
        estore(bus_table_total * GEN ** (3 * s), eadd(acc, sload(gkr_claims, s)))
    claim_idx = N_BUS_CLAIMS  # AIR/PI/pin claims pool after the deduped bus claims

    # ---- stacked-bytecode reduction ----
    # The bytecode is ONE multilinear in BYTECODE_LOG + LOG2_BYTECODE_COLS
    # variables (BYTECODE_COLS encoding columns stacked along the selector
    # bits), and push/pull share zeta, so there is ONE opening point: absorb
    # the values, sample the selector challenges, and reduce to the single
    # claim B(zeta_lo, sel) = sum_c eq(sel, c) * v_c.
    for k in unroll(0, BYTECODE_COLS):
        fs = obs(fs, eload(bytecode_vals * GEN ** (3 * k)))
    bytecode_sel = HeapBuf(3 * LOG2_BYTECODE_COLS)
    for t in unroll(0, LOG2_BYTECODE_COLS):
        fs, sv = squeeze(fs)
        estore(bytecode_sel * GEN ** (3 * t), sv)
    bytecode_reduced = [0, 0, 0]
    for c in unroll(0, BYTECODE_COLS):
        selector_weight = eq_weight(bytecode_sel, LOG2_BYTECODE_COLS, c, 0)
        bytecode_reduced = eadd(bytecode_reduced, emul(selector_weight, eload(bytecode_vals * GEN ** (3 * c))))

    # ---- ONE batched zerocheck for all seven tables ----
    # Mirrors lean_vm::constraints::verify. eta ONCE, each table folding its own
    # identities with a DISJOINT range of its powers (ETA_OFFSET[t]); one shared
    # point zeta (the bus GKR's); n = max_t tau_t rounds. Rounds bind the HIGHEST
    # variable first, so a 2^tau table sits out the first n - tau of them and joins
    # carrying the challenges it sat out. Per table the weight is then
    #   cprod[n - tau] * peq[tau],
    # the challenges drawn before it joined times peq[tau] = eq(zeta[..tau],
    # rho[..tau]); the eta-powers are already inside constraint_eval.
    #
    # g^n for n = max_t tau_t, the batch's round count. Hinted, then pinned
    # exactly: the product identity forces it to BE one of the certified taus, and
    # the range-checked division slacks force it to dominate every one of them.
    zc_n_hint = StackBuf(1)
    hint_witness(zc_n_hint[0:1], "zc_tau_max")
    g_zc_n = zc_n_hint[0]
    zc_is_a_tau = 1
    for t in unroll(0, N_TABLES):
        zc_is_a_tau *= g_zc_n + dims_g[GEN ** (t + 1)]
    assert zc_is_a_tau == 0
    for t in unroll(0, N_TABLES):
        zc_dominates = g_zc_n / dims_g[GEN ** (t + 1)]
        assert log(zc_dominates) < COUNT_BITS
    fs, eta = squeeze(fs)
    eta_pows = StackBuf(3 * N_ETA_POWS)
    sstore(eta_pows, 0, [1, 0, 0])
    for k in unroll(1, N_ETA_POWS):
        sstore(eta_pows, k, emul(sload(eta_pows, k - 1), eta))
    # The eq point is the bus GKR's zeta, NOT a fresh one: that is what lets the
    # batch settle the bus forms alongside the constraints.
    #
    # THE tie to the bus, and the reason no target is read: what the three sides'
    # tables owe, each in its own shared power of eta, IS the sum the batch must
    # reach. Since eta is squeezed after those totals are fixed, hitting one number
    # forces all three side equations.
    bus_target = [0, 0, 0]
    for sd in unroll(0, N_GKR_SIDES):
        bus_target = eadd(bus_target, emul(sload(eta_pows, ETA_FORM_BASE + sd), eload(bus_table_total * GEN ** (3 * sd))))
    # n vanilla sumcheck rounds: the round polynomial arrives whole, so a round is
    # `h(0) + h(1) == claim` and a fold, with no eq to reapply. The tables still
    # waiting ride inside h, so nothing here is indexed by height; the heights enter
    # only the per-table weights below.
    rho = HeapBuf(g_zc_n ** 3)   # rho[i] = the challenge that bound variable i
    zc_round_fs_prefix = HeapBuf((g_zc_n * GEN) ** 3)
    zc_round_fs3 = HeapBuf(g_zc_n * GEN)
    zc_round_cursor = HeapBuf(g_zc_n * GEN)
    zc_round_claim = HeapBuf((g_zc_n * GEN) ** 3)
    zc_round_cprod = HeapBuf((g_zc_n * GEN) ** 3)  # the challenges bound so far, multiplied
    deref_192(zc_round_fs_prefix, fs[0:3])
    zc_round_fs3[GEN ** 0] = fs[3]
    zc_round_cursor[GEN ** 0] = cursor
    estore(zc_round_claim, bus_target)
    estore(zc_round_cprod, [1, 0, 0])
    for xk in mul_range(1, g_zc_n):
        d = g_zc_n * INV_GEN / xk  # g^(n-1-j): the variable round j binds
        xk3 = xk ** 3
        round_prefix = eload(zc_round_fs_prefix * xk3)
        nfs0, nfs1, nfs2, nfs3, ncur, nclaim, rk = sumcheck_round4(round_prefix[0], round_prefix[1], round_prefix[2], zc_round_fs3[xk], zc_round_cursor[xk], eload(zc_round_claim * xk3))
        estore(rho * d ** 3, rk)
        xkn = xk * GEN
        xkn3 = xkn ** 3
        next_prefix = [nfs0, nfs1, nfs2]
        estore(zc_round_fs_prefix * xkn3, next_prefix)
        zc_round_fs3[xkn] = nfs3
        zc_round_cursor[xkn] = ncur
        # cprod is the weight of a table that joins here; peq below is the rest
        estore(zc_round_cprod * xkn3, emul(eload(zc_round_cprod * xk3), rk))
        estore(zc_round_claim * xkn3, nclaim)
    g_zc_n3 = g_zc_n ** 3
    final_round_prefix = eload(zc_round_fs_prefix * g_zc_n3)
    fs = [final_round_prefix[0], final_round_prefix[1], final_round_prefix[2], zc_round_fs3[g_zc_n]]
    cursor = zc_round_cursor[g_zc_n]
    claim = eload(zc_round_claim * g_zc_n3)
    # peq[g^tau] = eq(zeta[..tau], rho[..tau]), as a prefix chain.
    zc_peq = HeapBuf((g_zc_n * GEN) ** 3)
    estore(zc_peq, [1, 0, 0])
    for xi in mul_range(1, g_zc_n):
        xi3 = xi ** 3
        estore(zc_peq * xi3 * GEN ** 3, emul(eload(zc_peq * xi3), eadd([1, 0, 0], eadd(eload(zeta * xi3), eload(rho * xi3)))))
    # Per table: every committed column's evaluation (pooled), its AIR constraint
    # at its own reduced point rho[..tau_t], weighted into the batch's final claim.
    air_acc = [0, 0, 0]
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        col_evals = StackBuf(3 * TABLE_COLS_CAP)
        for k in unroll(0, N_TABLE_COLS[t]):
            fs, e, cursor = fs_next(fs, cursor)
            sstore(col_evals, k, e)
            estore(claim_pool * GEN ** (3 * claim_idx), e)
            claim_cplen_g[GEN ** claim_idx] = tau_g  # cplen = tau_t
            claim_idx += 1
        # the table's AIR constraint at the final point (col_evals is indexed by
        # local column index; the formulas mirror tables.rs eval_constraint).
        if t == TABLE_ADD:
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), base_air_constraint(col_evals, eta, 0))
        if t == TABLE_MUL:
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), base_air_constraint(col_evals, eta, 1))
        if t == TABLE_ADD_EXT:
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), ext_air_constraint(col_evals, eta, 0))
        if t == TABLE_MUL_EXT:
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), ext_air_constraint(col_evals, eta, 1))
        if t == TABLE_SET:
            set_constraint = eadd(sload(col_evals, 4), emul(sload(col_evals, 1), sload(col_evals, 2)))
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), set_constraint)
        if t == TABLE_DEREF:
            fp = sload(col_evals, 1)
            fpc = sload(col_evals, 5)
            ffp = sload(col_evals, 6)
            v3 = sload(col_evals, 12)
            src = eadd(emul(eadd(eadd([1, 0, 0], fpc), ffp), v3), eadd(emul(fpc, emul([GEN * GEN, 0, 0], sload(col_evals, 0))), emul(ffp, fp)))
            c0 = eadd(sload(col_evals, 7), emul(fp, sload(col_evals, 2)))
            c1 = eadd(sload(col_evals, 8), emul(sload(col_evals, 10), sload(col_evals, 3)))
            c2 = eadd(sload(col_evals, 9), emul(fp, sload(col_evals, 4)))
            c3 = eadd(sload(col_evals, 11), src)
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), epoly4(eta, c0, c1, c2, c3))
        if t == TABLE_DEREF_EXT:
            fp = sload(col_evals, 1)
            c0 = eadd(sload(col_evals, 5), emul(fp, sload(col_evals, 2)))
            c1 = eadd(sload(col_evals, 6), emul(sload(col_evals, 8), sload(col_evals, 3)))
            c2 = eadd(sload(col_evals, 7), emul(fp, sload(col_evals, 4)))
            width3 = sload(col_evals, 23)
            v2 = combine_tower_limbs(sload(col_evals, 9), sload(col_evals, 10), emul(width3, sload(col_evals, 11)))
            v3 = combine_tower_limbs(sload(col_evals, 12), sload(col_evals, 13), emul(width3, sload(col_evals, 14)))
            c3 = eadd(v2, v3)
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), epoly4(eta, c0, c1, c2, c3))
        if t == TABLE_JUMP:
            pc = sload(col_evals, 0)
            fp = sload(col_evals, 1)
            bval = sload(col_evals, 18)
            one_plus_b = eadd(bval, [1, 0, 0])
            fall_through = emul([GEN, 0, 0], pc)
            c0 = eadd(sload(col_evals, 7), emul(fp, sload(col_evals, 4)))
            c1 = eadd(sload(col_evals, 8), emul(fp, sload(col_evals, 5)))
            c2 = eadd(sload(col_evals, 9), emul(fp, sload(col_evals, 6)))
            c3 = eadd(bval, emul(sload(col_evals, 10), sload(col_evals, 17)))
            c4 = emul(sload(col_evals, 10), one_plus_b)
            c5 = eadd(sload(col_evals, 2), eadd(emul(bval, sload(col_evals, 11)), emul(one_plus_b, fall_through)))
            c6 = eadd(sload(col_evals, 3), eadd(emul(bval, sload(col_evals, 12)), emul(one_plus_b, fp)))
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), epoly7(eta, c0, c1, c2, c3, c4, c5, c6))
        if t == TABLE_BLAKE3:
            fp = sload(col_evals, 1)
            c0 = eadd(sload(col_evals, 8), emul(fp, sload(col_evals, 2)))
            c1 = eadd(sload(col_evals, 9), emul(fp, sload(col_evals, 3)))
            c2 = eadd(sload(col_evals, 10), emul(fp, sload(col_evals, 4)))
            c3 = eadd(sload(col_evals, 11), emul(fp, sload(col_evals, 5)))
            c4 = eadd(sload(col_evals, 12), emul(fp, sload(col_evals, 6)))
            c5 = eadd(sload(col_evals, 13), emul(fp, sload(col_evals, 7)))
            constraint_eval = emul(sload(eta_pows, ETA_OFFSET[t]), epoly6(eta, c0, c1, c2, c3, c4, c5))
        # The table's three bus forms, evaluated at the SAME column evaluations:
        # Σ_b eq_hi(b) · (γ + Σ_i α^i · coord_i), the coords read off col_evals at
        # their local index. This is what replaces opening those columns at ζ.
        for sd in unroll(0, N_GKR_SIDES):
            form = [0, 0, 0]
            for b in unroll(0, N_BLOCKS):
                if BLOCK_SIDE[b] == sd:
                    if BLOCK_REAL_TABLE[b] == t:
                        inner = [0, 0, 0]
                        apow = [1, 0, 0]
                        for i in unroll(0, BLOCK_COORD_COUNT[b]):
                            if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_CONST:
                                cv = ebase(COORD_CONST[BLOCK_COORD_OFF[b] + i])
                            if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_COL:
                                cv = sload(col_evals, COORD_COL_LOCAL[BLOCK_COORD_OFF[b] + i])
                            if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_GCOL:
                                cv = emul_base(COORD_CONST[BLOCK_COORD_OFF[b] + i], sload(col_evals, COORD_COL_LOCAL[BLOCK_COORD_OFF[b] + i]))
                            if sd == COUNT_SIDE:
                                inner = eadd(inner, cv)
                            else:
                                inner = eadd(inner, emul(apow, cv))
                                apow = emul(apow, alpha)
                        if sd == COUNT_SIDE:
                            form = eadd(form, emul(eload(block_eq_all * GEN ** (3 * b)), inner))
                        else:
                            form = eadd(form, emul(eload(block_eq_all * GEN ** (3 * b)), eadd(gamma, inner)))
            constraint_eval = eadd(constraint_eval, emul(sload(eta_pows, ETA_FORM_BASE + sd), form))
        table_weight = emul(eload(zc_round_cprod * (g_zc_n / tau_g) ** 3), eload(zc_peq * tau_g ** 3))
        air_acc = eadd(air_acc, emul(table_weight, constraint_eval))
    ext_assert_eq(air_acc, claim)

    # ---- public-input binding claim: one base-word MEM column ----
    # The first four memory words are evaluated at a random two-variable point;
    # all higher memory coordinates are fixed to zero.
    fs, rm0 = squeeze(fs)
    fs, rm1 = squeeze(fs)
    pi_lo = eadd_base(pi_0, emul_base(pi_0 + pi_1, rm0))
    pi_hi = eadd_base(pi_2, emul_base(pi_2 + pi_3, rm0))
    mem = eadd(pi_lo, emul(rm1, eadd(pi_lo, pi_hi)))
    estore(claim_pool * GEN ** (3 * claim_idx), mem)
    claim_cplen_g[GEN ** claim_idx] = GEN ** 2
    claim_idx += 1

    # ---- flock zerocheck (univariate skip, k_skip = 6) ----
    tau_blake3_g = dims_g[GEN ** (TABLE_BLAKE3 + 1)]  # the BLAKE3 table's certified tau
    # tau's reach is bounded: the count gadget gives tau < 34 (all flock
    # buffers are sized for that), and q_pkd's committed kappa =
    # K_LOG + tau feeds the certified size m, whose opening
    # dispatch bound caps tau well below any baked structure.
    # flock's sub-proof scalars are ordinary stream words (add_scalar on the
    # native side); the cursor walks them, fetching and observing each in one
    # step (fs_next) at the point the transcript binds it.
    # the full r vector: K_SKIP sampled skips, N_FIXED_CHALLENGE_ROUNDS fixed inner,
    # the rest sampled outer. r is the zerocheck eq-randomness the prover builds
    # round-1 FROM, so it is squeezed BEFORE round-1 is fetched (and round-1 before
    # z, which evaluates it).
    mr1cs_g = tau_blake3_g * GEN ** K_LOG  # runtime m = K_LOG + tau_5 (certified) in the exponent
    mr1cs_g3 = mr1cs_g ** 3
    zerocheck_r = HeapBuf(mr1cs_g3)
    for i in unroll(0, K_SKIP):
        fs, rv = squeeze(fs)
        estore(zerocheck_r * GEN ** (3 * i), rv)
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        fixed_challenge = [FIXED_CHALLENGES[3 * i], FIXED_CHALLENGES[3 * i + 1], FIXED_CHALLENGES[3 * i + 2]]
        estore(zerocheck_r * GEN ** (3 * (K_SKIP + i)), fixed_challenge)
    # outer samples at runtime count: m = K_LOG + tau_5 (certified).
    flock_point_fs_prefix = HeapBuf(mr1cs_g3 * GEN ** 6)
    flock_point_fs3 = HeapBuf(mr1cs_g * GEN ** 2)
    deref_192(flock_point_fs_prefix * GEN ** (3 * (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)), fs[0:3])
    flock_point_fs3[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[3]
    for xi in mul_range(GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS), mr1cs_g):
        xi3 = xi ** 3
        point_prefix = eload(flock_point_fs_prefix * xi3)
        point_fs = [point_prefix[0], point_prefix[1], point_prefix[2], flock_point_fs3[xi]]
        point_fs, zerocheck_challenge = squeeze(point_fs)
        estore(zerocheck_r * xi3, zerocheck_challenge)
        xin = xi * GEN
        deref_192(flock_point_fs_prefix * xi3 * GEN ** 3, point_fs[0:3])
        flock_point_fs3[xin] = point_fs[3]
    flock_point_final_prefix = eload(flock_point_fs_prefix * mr1cs_g3)
    fs = [flock_point_final_prefix[0], flock_point_final_prefix[1], flock_point_final_prefix[2], flock_point_fs3[mr1cs_g]]
    # round-1 message (ab ‖ c, 2 * 2^K_SKIP words): fetch + observe each word as
    # it comes off the stream, then sample z.
    zc_round1 = HeapBuf(384)
    for i in unroll(0, 2 * 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        estore(zc_round1 * GEN ** (3 * i), w)
    fs, zerocheck_z = squeeze(fs)  # cursor now sits at the multilinear round messages, walked below
    # interpolate P^C(z) on the Lambda domain (phi8 nodes 64..128): prefix/
    # suffix numerator products with baked inverse denominators.
    lagrange_nums = lag64(zerocheck_z, 2 ** K_SKIP)
    c_eval = [0, 0, 0]
    for i in unroll(0, 2 ** K_SKIP):
        inv = [LAGRANGE_INV_LAMBDA[3 * i], LAGRANGE_INV_LAMBDA[3 * i + 1], LAGRANGE_INV_LAMBDA[3 * i + 2]]
        term = emul(emul(sload(lagrange_nums, i), inv), eload(zc_round1 * GEN ** (3 * (2 ** K_SKIP + i))))
        c_eval = eadd(c_eval, term)
    # combined interpolation at z over ALL 128 phi8 nodes (Lambda values only;
    # the S half is zero by the zerocheck identity). The Lambda-node numerators
    # reuse lagrange_nums: the full-domain product only adds the S-half factor.
    s_half_product = [1, 0, 0]
    for i in unroll(0, 2 ** K_SKIP):
        s_half_product = emul(s_half_product, eadd(zerocheck_z, phi8(i)))
    combined_eval = [0, 0, 0]
    for i in unroll(0, 2 ** K_SKIP):
        inv = [LAGRANGE_INV_COMBINED[3 * i], LAGRANGE_INV_COMBINED[3 * i + 1], LAGRANGE_INV_COMBINED[3 * i + 2]]
        values = eadd(eload(zc_round1 * GEN ** (3 * i)), eload(zc_round1 * GEN ** (3 * (2 ** K_SKIP + i))))
        combined_eval = eadd(combined_eval, emul(emul(sload(lagrange_nums, i), inv), values))
    combined_eval = emul(combined_eval, s_half_product)
    zc_running = eadd(combined_eval, c_eval)
    # multilinear rounds.
    mr1cs_rounds_g = mr1cs_g * INV_GEN ** 6  # runtime zerocheck mlv rounds: m - 6
    zerocheck_rhos = HeapBuf(mr1cs_rounds_g ** 3)
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        r_eq = eload(zerocheck_r * GEN ** (3 * (K_SKIP + i)))
        fs, gamma_c, cursor = fs_next(fs, cursor)  # (gamma_c, g_inf) per round, walked in order
        fs, g_inf, cursor = fs_next(fs, cursor)
        one_plus_inv = [ONE_PLUS_CHALLENGE_INV[3 * i], ONE_PLUS_CHALLENGE_INV[3 * i + 1], ONE_PLUS_CHALLENGE_INV[3 * i + 2]]
        gamma_ab = emul(eadd(zc_running, emul(r_eq, gamma_c)), one_plus_inv)
        fs, rho_v = squeeze(fs)
        estore(zerocheck_rhos * GEN ** (3 * i), rho_v)
        zc_running = eadd(gamma_ab, emul(rho_v, eadd(eadd(gamma_ab, gamma_c), emul(eadd([1, 0, 0], rho_v), g_inf))))
    # rounds N_FIXED_CHALLENGE_ROUNDS.. at runtime count: K_LOG + tau_5 - K_SKIP rounds total (certified).
    nmlv_g = tau_blake3_g * GEN ** (K_LOG - K_SKIP)
    flock_round_size = mr1cs_rounds_g * GEN ** 2
    flock_round_size3 = flock_round_size ** 3
    flock_round_fs_prefix = HeapBuf(flock_round_size3)
    flock_round_fs3 = HeapBuf(flock_round_size)
    flock_round_running = HeapBuf(flock_round_size3)
    flock_round_cursor = HeapBuf(flock_round_size)  # the walking cursor, threaded like the fs state
    deref_192(flock_round_fs_prefix * GEN ** (3 * N_FIXED_CHALLENGE_ROUNDS), fs[0:3])
    flock_round_fs3[GEN ** N_FIXED_CHALLENGE_ROUNDS] = fs[3]
    estore(flock_round_running * GEN ** (3 * N_FIXED_CHALLENGE_ROUNDS), zc_running)
    flock_round_cursor[GEN ** N_FIXED_CHALLENGE_ROUNDS] = cursor
    for xi in mul_range(GEN ** N_FIXED_CHALLENGE_ROUNDS, nmlv_g):
        xi3 = xi ** 3
        round_prefix = eload(flock_round_fs_prefix * xi3)
        round_fs = [round_prefix[0], round_prefix[1], round_prefix[2], flock_round_fs3[xi]]
        round_running = eload(flock_round_running * xi3)
        r_eq = eload(zerocheck_r * GEN ** (3 * K_SKIP) * xi3)
        cur_i = flock_round_cursor[xi]
        round_fs, gamma_c, cur_i = fs_next(round_fs, cur_i)
        round_fs, g_inf, cur_i = fs_next(round_fs, cur_i)
        gamma_ab = ediv(eadd(round_running, emul(r_eq, gamma_c)), eadd([1, 0, 0], r_eq))
        round_fs, rho_v = squeeze(round_fs)
        estore(zerocheck_rhos * xi3, rho_v)
        round_running = eadd(gamma_ab, emul(rho_v, eadd(eadd(gamma_ab, gamma_c), emul(eadd([1, 0, 0], rho_v), g_inf))))
        xin = xi * GEN
        xin3 = xi3 * GEN ** 3
        deref_192(flock_round_fs_prefix * xin3, round_fs[0:3])
        flock_round_fs3[xin] = round_fs[3]
        estore(flock_round_running * xin3, round_running)
        flock_round_cursor[xin] = cur_i
    nmlv_g3 = nmlv_g ** 3
    flock_round_final_prefix = eload(flock_round_fs_prefix * nmlv_g3)
    fs = [flock_round_final_prefix[0], flock_round_final_prefix[1], flock_round_final_prefix[2], flock_round_fs3[nmlv_g]]
    zc_running = eload(flock_round_running * nmlv_g3)
    cursor = flock_round_cursor[nmlv_g]  # walked past all 2*n_mlv round words, now at a_eval
    # final: zc_running == a_eval * b_eval; observe both.
    fs, a_eval, cursor = fs_next(fs, cursor)
    fs, b_eval, cursor = fs_next(fs, cursor)
    ab_product = emul(a_eval, b_eval)
    ext_assert_eq(zc_running, ab_product)

    # ---- flock lincheck (matrix evaluation DEFERRED) ----
    matrix_eval = StackBuf(3)
    hint_witness(matrix_eval[0:3], "matpart")
    fs, lincheck_alpha = squeeze(fs)
    fs, lincheck_beta = squeeze(fs)
    lc_running = eadd(eadd(emul(lincheck_alpha, a_eval), b_eval), lincheck_beta)
    lincheck_rs = HeapBuf(3 * LINCHECK_ROUNDS)
    for i in unroll(0, LINCHECK_ROUNDS):
        fs, e1, cursor = fs_next(fs, cursor)  # (e1, e_inf) per round, walked in order
        fs, ei, cursor = fs_next(fs, cursor)
        fs, rv = squeeze(fs)
        estore(lincheck_rs * GEN ** (3 * i), rv)
        e0 = eadd(lc_running, e1)
        c1q = eadd(eadd(e0, e1), ei)
        lc_running = eadd(emul(eadd(emul(ei, rv), c1q), rv), e0)
    z_partial = HeapBuf(192)
    for i in unroll(0, 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        estore(z_partial * GEN ** (3 * i), w)
    # final consistency: running == matpart (DEFERRED) + beta * pin term. The
    # const-pin column folds through the top-variable bindings: weight =
    # prod_j (bit_{klog-1-j}(PIN_COLUMN) ? r_j : 1+r_j), surviving z_partial index
    # = PIN_COLUMN low 6 bits.
    pin_term = emul(lincheck_beta, eq_weight(lincheck_rs, LINCHECK_ROUNDS, PIN_COLUMN, K_LOG))
    pin_term = emul(pin_term, eload(z_partial * GEN ** (3 * (PIN_COLUMN % 2 ** K_SKIP))))
    matrix_part = sload(matrix_eval, 0)
    lincheck_final = eadd(matrix_part, pin_term)
    ext_assert_eq(lc_running, lincheck_final)
    # fresh z_skip; w = <lagrange_S(r_inner_skip), z_partial> (phi8 nodes 0..64).
    fs, lincheck_z_skip = squeeze(fs)
    skip_nums = lag64(lincheck_z_skip, 0)
    lincheck_w = [0, 0, 0]
    for i in unroll(0, 2 ** K_SKIP):
        inv = lagrange_inv_s(i)
        lincheck_w = eadd(lincheck_w, emul(emul(sload(skip_nums, i), inv), eload(z_partial * GEN ** (3 * i))))

    # ---- dense Jagged opening: ring-switch fronts + claim combination ----
    # The two ring-switch slices (ab, c) each carry PACKING = 2^LOG_PACKING = 64
    # entries (one per packing bit) and live in the opening STRUCT
    # (RingSwitchProof), observed into the sponge HERE (never on the stream).
    # Claim 0 (ab): value lincheck_w, z_skip = lincheck_z_skip. Claim 1 (c):
    # value c_eval, z_skip = zerocheck_z. (The 128->64 half-fold the prover does
    # in blake3_flock::ring_claim is already baked into the transmitted 64 values,
    # so the verifier just checks the plain prefix-weighted inner product.)
    s_hat_v = HeapBuf(3 * 2 * (2 ** K_SKIP))
    hint_witness(s_hat_v[0 : 3 * 2 * (2 ** K_SKIP)], "rs_shatv")
    transposed_claims = StackBuf(3 * 2)
    rs_eq_vals = StackBuf(3 * 2)
    map_challenges = HeapBuf(3 * 6)
    c_table = HeapBuf(3 * BASE_FIELD_BITS)
    z_vals = HeapBuf(3 * 2 * QPKD_VARS_CAP)
    for rs in unroll(0, 2):
        # observe this claim's 64 s_hat_v entries (mirror of verify_observe /
        # observe_ext_slice) before the claim check and the shared map.
        for i in unroll(0, (2 ** K_SKIP)):
            fs = obs(fs, eload(s_hat_v * GEN ** (3 * ((2 ** K_SKIP) * rs + i))))
        # claim check: value == sum_i prefix_weights[i] * s_hat_v[i], where
        # prefix_weights[i] = lambda_i(z_skip) = lag numerator * LAGRANGE_INV_S[i].
        if rs == 0:
            claim_z_skip = lincheck_z_skip
            claim_val = lincheck_w
        else:
            claim_z_skip = zerocheck_z
            claim_val = c_eval
        claim_nums = lag64(claim_z_skip, 0)
        claim_check = [0, 0, 0]
        for i in unroll(0, (2 ** K_SKIP)):
            shat = eload(s_hat_v * GEN ** (3 * ((2 ** K_SKIP) * rs + i)))
            claim_check = eadd(claim_check, emul(emul(sload(claim_nums, i), lagrange_inv_s(i)), shat))
        ext_assert_eq(claim_check, claim_val)
    # Compose six two-term F2-linear maps with shifts 32,16,8,4,2,1. Their
    # expansion has all 64 Frobenius terms required for soundness, while direct
    # application costs 63 squarings and only six general multiplications.
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        fs, map_challenge = squeeze(fs)
        estore(map_challenges * GEN ** (3 * stage), map_challenge)
    # Expand the same composition once for the later transparent-weight
    # evaluation. Before shift d, the populated coefficients are exactly at
    # multiples of 2d; the new branch fills the adjacent d-offset entries.
    estore(c_table, [1, 0, 0])
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        shift = RING_MAP_SHIFTS[stage]
        map_challenge = eload(map_challenges * GEN ** (3 * stage))
        for slot in unroll(0, BASE_FIELD_BITS // (2 * shift)):
            coefficient = eload(c_table * GEN ** (3 * slot * 2 * shift))
            for k in unroll(0, shift):
                coefficient = emul(coefficient, coefficient)
            estore(c_table * GEN ** (3 * (slot * 2 * shift + shift)), emul(map_challenge, coefficient))
    # Evaluate both claims together and combine their 64 packing rows.
    s_hat_row_0 = s_hat_v
    s_hat_row_1 = s_hat_v * GEN ** (3 * (2 ** K_SKIP))
    x_pow_chain = HeapBuf(3 * ((2 ** K_SKIP) + 1))
    estore(x_pow_chain, [1, 0, 0])
    t_chain_0 = HeapBuf(3 * ((2 ** K_SKIP) + 1))
    t_chain_1 = HeapBuf(3 * ((2 ** K_SKIP) + 1))
    estore(t_chain_0, [0, 0, 0])
    estore(t_chain_1, [0, 0, 0])
    for x_round in mul_range(1, GEN ** (2 ** K_SKIP)):
        x_round3 = x_round ** 3
        lin_eval_0 = eload(s_hat_row_0 * x_round3)
        lin_eval_1 = eload(s_hat_row_1 * x_round3)
        for stage in unroll(0, len(RING_MAP_SHIFTS)):
            frobenius_0 = lin_eval_0
            frobenius_1 = lin_eval_1
            for k in unroll(0, RING_MAP_SHIFTS[stage]):
                frobenius_0 = emul(frobenius_0, frobenius_0)
                frobenius_1 = emul(frobenius_1, frobenius_1)
            map_challenge = eload(map_challenges * GEN ** (3 * stage))
            lin_eval_0 = eadd(lin_eval_0, emul(map_challenge, frobenius_0))
            lin_eval_1 = eadd(lin_eval_1, emul(map_challenge, frobenius_1))
        x_pow = eload(x_pow_chain * x_round3)
        estore(t_chain_0 * x_round3 * GEN ** 3, eadd(eload(t_chain_0 * x_round3), emul(x_pow, lin_eval_0)))
        estore(t_chain_1 * x_round3 * GEN ** 3, eadd(eload(t_chain_1 * x_round3), emul(x_pow, lin_eval_1)))
        estore(x_pow_chain * x_round3 * GEN ** 3, emul_base(2, x_pow))
    sstore(transposed_claims, 0, eload(t_chain_0 * GEN ** (3 * (2 ** K_SKIP))))
    sstore(transposed_claims, 1, eload(t_chain_1 * GEN ** (3 * (2 ** K_SKIP))))
    # Suffix points for the two transparent weights.
    for t in unroll(0, LINCHECK_ROUNDS):
        estore(z_vals * GEN ** (3 * t), eload(lincheck_rs * GEN ** (3 * (LINCHECK_ROUNDS - 1 - t))))
    zv_lo = z_vals * GEN ** (3 * LINCHECK_ROUNDS)
    zr_hi = zerocheck_rhos * GEN ** (3 * LINCHECK_ROUNDS)
    for xt in mul_range(1, tau_blake3_g):
        xt3 = xt ** 3
        estore(zv_lo * xt3, eload(zr_hi * xt3))
    zv_hi = z_vals * GEN ** 123
    zcr7 = zerocheck_r * GEN ** (3 * K_SKIP)
    for xt in mul_range(1, tau_blake3_g * GEN ** SLOT_STRIDE_LOG):
        xt3 = xt ** 3
        estore(zv_hi * xt3, eload(zcr7 * xt3))
    # gamma-combine the two transposed sumcheck claims (computed in-circuit).
    fs, gamma_ab = squeeze(fs)
    fs, gamma_c = squeeze(fs)
    target = eadd(emul(gamma_ab, sload(transposed_claims, 0)), emul(gamma_c, sload(transposed_claims, 1)))

    # ---- Jagged dense layout: derive one cumulative boundary-bit chain ----
    # Table-row and used-memory bits were already Boolean-constrained and tied
    # to their announced words by log2_ceil_word.  The bytecode prefix is fixed
    # by the program.  A width-2^b block shifts its row count by b.
    # Power-of-two structural blocks use a one-hot height pinned to kappa.
    # Starting from zero, a Boolean full-adder derives every interval endpoint.
    col_bound_bits = HeapBuf(SIZE_BITS * (N_COMMITTED_COLS + 1))
    col_block_height_bits = HeapBuf(SIZE_BITS * N_COMMITTED_COLS)
    for bit in unroll(0, SIZE_BITS):
        col_bound_bits[GEN ** bit] = 0
    for c in unroll(0, N_COMMITTED_COLS):
        height_bits = col_block_height_bits * GEN ** (SIZE_BITS * c)
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
    claim_rows = HeapBuf(3 * SIZE_BITS * N_CLAIM_ROWS)
    for group in unroll(0, N_CLAIM_ROWS):
        rep = CLAIM_ROW_REP[group]
        row = claim_rows * GEN ** (3 * SIZE_BITS * group)
        if CLAIM_POINT_BUF[rep] == POINT_BUF_ZETA:
            cplen_g = claim_cplen_g[GEN ** rep]
            src = zeta * GEN ** (3 * CLAIM_POINT_OFF[rep])
            for xk in mul_range(1, cplen_g):
                xk3 = xk ** 3
                estore(row * xk3, eload(src * xk3))
            zero_ptr = row * cplen_g ** 3
            zero_len_g = GEN ** SIZE_BITS / cplen_g
            for xk in mul_range(1, zero_len_g):
                estore(zero_ptr * xk ** 3, [0, 0, 0])
        if CLAIM_POINT_BUF[rep] == POINT_BUF_RHO:
            cplen_g = claim_cplen_g[GEN ** rep]
            src = rho * GEN ** (3 * CLAIM_POINT_OFF[rep])
            for xk in mul_range(1, cplen_g):
                xk3 = xk ** 3
                estore(row * xk3, eload(src * xk3))
            zero_ptr = row * cplen_g ** 3
            zero_len_g = GEN ** SIZE_BITS / cplen_g
            for xk in mul_range(1, zero_len_g):
                estore(zero_ptr * xk ** 3, [0, 0, 0])
        if CLAIM_POINT_BUF[rep] == POINT_BUF_PI:
            estore(row, rm0)
            estore(row * GEN ** 3, rm1)
            for bit in unroll(2, SIZE_BITS):
                estore(row * GEN ** (3 * bit), [0, 0, 0])

    # The committed real prefix is offset by its public pad value, so the
    # logical evaluation is the committed one plus that constant at every
    # point. q_pkd is exempt because its pad is zero.
    opening_claim_values = HeapBuf(3 * N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
            # q_pkd remains the one aligned subcube for flock's ring-switch and
            # its strided VM-value claims; it has no public padding correction.
            estore(opening_claim_values * GEN ** (3 * j), eload(claim_pool * GEN ** (3 * j)))
        else:
            if CLAIM_PAD[j] == 0:
                estore(opening_claim_values * GEN ** (3 * j), eload(claim_pool * GEN ** (3 * j)))
            else:
                estore(opening_claim_values * GEN ** (3 * j), eadd_base(CLAIM_PAD[j], eload(claim_pool * GEN ** (3 * j))))

    # Every adjusted Jagged claim value is observed before its batching scalar,
    # exactly as in the native verifier.
    for j in unroll(0, N_CLAIMS):
        fs = obs(fs, eload(opening_claim_values * GEN ** (3 * j)))
    gamma_pool = HeapBuf(3 * N_CLAIMS)
    fs, gamma = squeeze(fs)
    gamma_powers = HeapBuf(3 * N_CLAIMS)
    gv = [1, 0, 0]
    for rank in unroll(0, N_CLAIMS):
        estore(gamma_powers * GEN ** (3 * rank), gv)
        gv = emul(gv, gamma)
    for j in unroll(0, N_CLAIMS):
        weight = eload(gamma_powers * GEN ** (3 * CLAIM_GAMMA_RANK[j]))
        estore(gamma_pool * GEN ** (3 * j), weight)
        target = eadd(target, emul(weight, eload(opening_claim_values * GEN ** (3 * j))))

    # ================= the Ligerito opening core (Jagged dense q) ===========

    # Dispatch on m = max(log2_ceil(total real area), LIG_MIN_LOG_SIZE).
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES
    # Flatten (rate-1, m-MIN) in rate-major order. Both coordinates are
    # transcript-bound and range-checked above, so a single compiled guest can
    # dispatch independently for every inner proof in a mixed-rate batch.
    config_sel = size_sel * rate_sel ** LIG_N_LOG_SIZES
    assert log(config_sel) < LIG_N_CANDIDATES
    sumcheck_out = HeapBuf(3)
    inner_out = HeapBuf(3)
    yr_at_tail_out = HeapBuf(3)
    # The opening now runs the tail sumcheck to one terminal point and returns
    # both that point (tail_challenges) and the final-message evaluation there
    # (yr_at_tail, written to its out-buffer).
    fold_challenges, final_msg, yr_log_n_g, yr_pad_g, fold_cap_g, tail_challenges = match_range(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], fs[2], fs[3], target, commit_root_0, commit_root_1, commit_root_2, commit_root_3, cursor, sumcheck_out, inner_out, yr_at_tail_out))
    sumcheck_target = eload(sumcheck_out)
    inner_total = eload(inner_out)
    yr_at_tail = eload(yr_at_tail_out)
    # `stream` is a fixed-capacity witness transport. The shape fixes the exact
    # consumed prefix, whose every word is transcript-bound; the unused suffix
    # is outside the recursively verified proof and intentionally unconstrained.


    # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
    # (the telescoped product formula; z powers evolve by squaring per k).
    # QPKD_VARS_CAP = tau_5 + SLOT_STRIDE_LOG, exponent-additive from the
    # certified announced log. Walk the runtime coordinates OUTSIDE and the
    # fixed FIELD_BITS Frobenius powers inside: each coordinate loads its
    # opening challenge once and evolves z by squaring in registers, advancing
    # one contiguous FIELD_BITS-wide product row. Same product formula as the
    # k-major form, but with no stored z-power table (the dominant memory
    # traffic) and no per-level buffer.
    qpkdv_g = tau_blake3_g * GEN ** SLOT_STRIDE_LOG
    # Evaluate both transparent weights in lockstep, sharing c_k and the
    # verifier-point factor in every inner iteration.
    z_row_src_1 = z_vals * GEN ** 123
    prod_chains_0 = HeapBuf(8064)
    prod_chains_1 = HeapBuf(8064)
    for k in unroll(0, BASE_FIELD_BITS):
        estore(prod_chains_0 * GEN ** (3 * k), [1, 0, 0])
        estore(prod_chains_1 * GEN ** (3 * k), [1, 0, 0])
    for x_round in mul_range(1, qpkdv_g):
        x_round3 = x_round ** 3
        zv_0 = eload(z_vals * x_round3)
        zv_1 = eload(z_row_src_1 * x_round3)
        one_plus = eadd([1, 0, 0], eload(fold_challenges * x_round3))
        prod_row_0 = prod_chains_0 * x_round ** (3 * BASE_FIELD_BITS)
        prod_row_1 = prod_chains_1 * x_round ** (3 * BASE_FIELD_BITS)
        prod_row_next_0 = prod_row_0 * GEN ** (3 * BASE_FIELD_BITS)
        prod_row_next_1 = prod_row_1 * GEN ** (3 * BASE_FIELD_BITS)
        for k in unroll(0, BASE_FIELD_BITS):
            koff = GEN ** (3 * k)
            estore(prod_row_next_0 * koff, emul(eload(prod_row_0 * koff), eadd(zv_0, one_plus)))
            estore(prod_row_next_1 * koff, emul(eload(prod_row_1 * koff), eadd(zv_1, one_plus)))
            if k != BASE_FIELD_BITS - 1:
                zv_0 = emul(zv_0, zv_0)
                zv_1 = emul(zv_1, zv_1)
    prod_final_0 = prod_chains_0 * qpkdv_g ** (3 * BASE_FIELD_BITS)
    prod_final_1 = prod_chains_1 * qpkdv_g ** (3 * BASE_FIELD_BITS)
    e_acc_0 = [0, 0, 0]
    e_acc_1 = [0, 0, 0]
    for k in unroll(0, BASE_FIELD_BITS):
        koff = GEN ** (3 * k)
        ck = eload(c_table * koff)
        e_acc_0 = eadd(e_acc_0, emul(ck, eload(prod_final_0 * koff)))
        e_acc_1 = eadd(e_acc_1, emul(ck, eload(prod_final_1 * koff)))
    sstore(rs_eq_vals, 0, e_acc_0)
    sstore(rs_eq_vals, 1, e_acc_1)
    # q_pkd is deliberately the first dense Jagged column, so its selector is
    # all-zero. Extend the ring-switch weight across the remaining ris coords.
    rs_weight = eadd(emul(gamma_ab, sload(rs_eq_vals, 0)), emul(gamma_c, sload(rs_eq_vals, 1)))
    rs_len_g = fold_cap_g / qpkdv_g
    assert log(rs_len_g) < SIZE_BITS
    ris_q = fold_challenges * qpkdv_g ** 3
    rsw_chain = HeapBuf(3 * (SIZE_BITS + 1))
    estore(rsw_chain, rs_weight)
    for xk in mul_range(1, rs_len_g):
        xk3 = xk ** 3
        estore(rsw_chain * xk3 * GEN ** 3, emul(eload(rsw_chain * xk3), eadd([1, 0, 0], eload(ris_q * xk3))))
    rs_weight = eload(rsw_chain * rs_len_g ** 3)

    # The VM value claims routed into fixed q_pkd slots use the same aligned
    # offset-zero subcube. Framework claims use zeta; the BLAKE3 columns absorbed
    # by the shared AIR sumcheck use rho. Both have residual-y selector zero.
    qpkd_claim_weight = [0, 0, 0]
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
            cplen_g = claim_cplen_g[GEN ** j]
            weight = eval_qpkd_claim_weight(zeta, cplen_g, CLAIM_QPKD_SLOT[j], fold_challenges, fold_cap_g, qpkdv_g)
            qpkd_claim_weight = eadd(qpkd_claim_weight, emul(eload(gamma_pool * GEN ** (3 * j)), weight))
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD_RHO:
            cplen_g = claim_cplen_g[GEN ** j]
            weight = eval_qpkd_claim_weight(rho, cplen_g, CLAIM_QPKD_SLOT[j], fold_challenges, fold_cap_g, qpkdv_g)
            qpkd_claim_weight = eadd(qpkd_claim_weight, emul(eload(gamma_pool * GEN ** (3 * j)), weight))

    # Evaluate the dense Jagged weights at the tail-sumcheck point. q_pkd is
    # the aligned offset-zero subcube, so its residual selector is all zero.
    jagged_out = HeapBuf(3)
    jagged_dispatch = match_range(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: jagged_eval_terminal(m_idx, fold_challenges, tail_challenges, claim_rows, col_bound_bits, gamma, gamma_powers, jagged_out))
    assert jagged_dispatch == GEN ** 0
    jagged_sum = eload(jagged_out)
    tail_zero_eq = [1, 0, 0]
    for k in unroll(0, YR_LOG_CAP):
        tail_zero_eq = emul(tail_zero_eq, eadd([1, 0, 0], eload(tail_challenges * GEN ** (3 * k))))
    inner_sum = eadd(eadd(inner_total, jagged_sum), emul(eadd(rs_weight, qpkd_claim_weight), tail_zero_eq))
    ext_assert_eq(emul(inner_sum, yr_at_tail), sumcheck_target)


    # ---- export this sub-proof's deferred-claim data to the caller ----
    # defer_out layout, offsets after the [0..KBC) shared bytecode point
    # (SEL = LOG2_BYTECODE_COLS, LCR = LINCHECK_ROUNDS):
    #   +0..SEL bytecode_sel | +SEL bytecode_reduced | +SEL+1 alpha
    #   | +SEL+2 z_skip | +SEL+3.. zrho | +SEL+3+LCR.. lincheck rs
    #   | +SEL+3+2*LCR.. z_partial (2^K_SKIP) | +SEL+3+2^K_SKIP+2*LCR matpart.
    for k in unroll(0, BYTECODE_LOG):
        estore(defer_out * GEN ** (3 * k), eload(zeta * GEN ** (3 * k)))
    for k in unroll(0, LOG2_BYTECODE_COLS):
        estore(defer_out * GEN ** (3 * (BYTECODE_LOG + k)), eload(bytecode_sel * GEN ** (3 * k)))
    estore(defer_out * GEN ** (3 * (BYTECODE_LOG + LOG2_BYTECODE_COLS)), bytecode_reduced)
    estore(defer_out * GEN ** (3 * (BYTECODE_LOG + LOG2_BYTECODE_COLS + 1)), lincheck_alpha)
    estore(defer_out * GEN ** (3 * (BYTECODE_LOG + LOG2_BYTECODE_COLS + 2)), zerocheck_z)
    for k in unroll(0, LINCHECK_ROUNDS):
        estore(defer_out * GEN ** (3 * (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + k)), eload(zerocheck_rhos * GEN ** (3 * k)))
        estore(defer_out * GEN ** (3 * (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + LINCHECK_ROUNDS + k)), eload(lincheck_rs * GEN ** (3 * k)))
    for k in unroll(0, 2 ** K_SKIP):
        estore(defer_out * GEN ** (3 * (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 * LINCHECK_ROUNDS + k)), eload(z_partial * GEN ** (3 * k)))
    estore(defer_out * GEN ** (3 * (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 ** K_SKIP + 2 * LINCHECK_ROUNDS)), matrix_part)
    return


def main():
    # NSUB sub-proofs of the fixed inner program: verify each (verify_sub),
    # then aggregate their deferred claims. The fresh aggregation transcript
    # RLC-batches the bytecode and matrix claims through two sumchecks; only
    # the three reduced claims (evaluated natively by the outer verifier)
    # reach this guest's public input.
    sub_pis = HeapBuf(NSUB * 4)
    hint_witness(sub_pis[0:NSUB * 4], "sub_pis")
    # The FS seed — ONE digest of everything fixed about the inner environment
    # (the flock circuit family, the inner program bytecode) — rides the
    # recursion's public input: hinted here, it leads every sub's transcript
    # and is folded into own_pi below, so the outer statement fixes the whole
    # proving environment with one word pair.
    fs_seed = StackBuf(4)
    hint_witness(fs_seed[0:4], "fs_seed")
    bc_sumcheck_msgs = HeapBuf(6 * BYTECODE_VARS)
    hint_witness(bc_sumcheck_msgs[0:6 * BYTECODE_VARS], "bc_sumcheck_msgs")
    mat_sumcheck_msgs = HeapBuf(12 * K_LOG)
    hint_witness(mat_sumcheck_msgs[0:12 * K_LOG], "mat_sumcheck_msgs")
    bc_star_hint = StackBuf(3)
    hint_witness(bc_star_hint[0:3], "bc_star_hint")
    mat_stars_hint = StackBuf(6)
    hint_witness(mat_stars_hint[0:6], "mat_stars_hint")
    # exponent-domain lookup tables, shared read-only across every sub-proof.
    g_logs_pow2, g_squares = exponent_tables()

    # per-sub deferred-claim regions (layout: see verify_sub's defer_out)
    defer = HeapBuf(NSUB * DEFER_SIZE * 3)

    for sub in unroll(0, NSUB):
        sub_pi = sub_pis * GEN ** (4 * sub)
        verify_sub(sub_pi[GEN ** 0], sub_pi[GEN ** 1], sub_pi[GEN ** 2], sub_pi[GEN ** 3], fs_seed[0], fs_seed[1], fs_seed[2], fs_seed[3], g_logs_pow2, g_squares, defer * GEN ** (3 * sub * DEFER_SIZE))

    # ================= aggregation: batch the deferred claims =================
    # A fresh transcript absorbs every deferred claim (points and values),
    # samples the RLC coefficients, and verifies the two batching sumchecks of
    # doc.tex §Deferred evaluation claims. Only the reduced claims (one per
    # fixed polynomial) reach the public input.
    agg_fs = [AGG_SEED_0, AGG_SEED_1, AGG_SEED_2, AGG_SEED_3]
    agg_fs = obs_base(agg_fs, NSUB)
    for sub in unroll(0, NSUB):
        sub_pi_ptr = sub_pis * GEN ** (4 * sub)
        sub_pi_prefix = eload(sub_pi_ptr)
        agg_fs = obs_base(agg_fs, sub_pi_prefix[0])
        agg_fs = obs_base(agg_fs, sub_pi_prefix[1])
        agg_fs = obs_base(agg_fs, sub_pi_prefix[2])
        agg_fs = obs_base(agg_fs, sub_pi_ptr[GEN ** 3])
        # the deferred-claim region is one contiguous run in absorb order.
        for k in unroll(0, DEFER_SIZE):
            defer_value = eload(defer * GEN ** (3 * (sub * DEFER_SIZE + k)))
            agg_fs = obs(agg_fs, defer_value)

    # ---- bytecode batching sumcheck (BYTECODE_VARS variables, NSUB claims) ----
    one_ext = [1, 0, 0]
    gamma_bc = HeapBuf(3 * NSUB)
    bc_running = [0, 0, 0]
    for t in unroll(0, NSUB):
        agg_fs, gv = squeeze(agg_fs)
        estore(gamma_bc * GEN ** (3 * t), gv)
        defer_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS)))
        weighted = emul(gv, defer_value)
        bc_running = eadd(bc_running, weighted)
    bc_point = HeapBuf(3 * BYTECODE_VARS)
    for rd in unroll(0, BYTECODE_VARS):
        agg_fs, msg_g1, c = fs_next(agg_fs, bc_sumcheck_msgs * GEN ** (6 * rd))
        agg_fs, msg_ginf, c = fs_next(agg_fs, c)
        agg_fs, rv = squeeze(agg_fs)
        estore(bc_point * GEN ** (3 * rd), rv)
        g_zero = eadd(bc_running, msg_g1)
        c_one_0 = eadd(g_zero, msg_g1)
        c_one = eadd(c_one_0, msg_ginf)
        term_0 = emul(msg_ginf, rv)
        term_1 = eadd(term_0, c_one)
        term_2 = emul(term_1, rv)
        bc_running = eadd(term_2, g_zero)
    # terminal: W(r*) in-circuit; the reduced bytecode claim B(r*) is deferred.
    bc_weight = [0, 0, 0]
    for t in unroll(0, NSUB):
        e = [1, 0, 0]
        for k in unroll(0, BYTECODE_LOG):
            defer_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + k)))
            point_value = eload(bc_point * GEN ** (3 * k))
            factor_0 = eadd(one_ext, defer_value)
            factor = eadd(factor_0, point_value)
            e = emul(e, factor)
        for k in unroll(0, LOG2_BYTECODE_COLS):
            defer_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + k)))
            point_value = eload(bc_point * GEN ** (3 * (BYTECODE_LOG + k)))
            factor_0 = eadd(one_ext, defer_value)
            factor = eadd(factor_0, point_value)
            e = emul(e, factor)
        gamma_value = eload(gamma_bc * GEN ** (3 * t))
        weighted = emul(gamma_value, e)
        bc_weight = eadd(bc_weight, weighted)
    bytecode_star = [bc_star_hint[0], bc_star_hint[1], bc_star_hint[2]]
    bc_final = emul(bytecode_star, bc_weight)
    ext_assert_eq(bc_running, bc_final)

    # ---- matrix batching sumcheck (2*K_LOG variables, NSUB weighted claims) ----
    gamma_mat = HeapBuf(3 * NSUB)
    mat_running = [0, 0, 0]
    for t in unroll(0, NSUB):
        agg_fs, gv = squeeze(agg_fs)
        estore(gamma_mat * GEN ** (3 * t), gv)
        defer_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 ** K_SKIP + 2 * LINCHECK_ROUNDS)))
        weighted = emul(gv, defer_value)
        mat_running = eadd(mat_running, weighted)
    mat_point = HeapBuf(6 * K_LOG)
    for rd in unroll(0, 2 * K_LOG):
        agg_fs, msg_g1, c = fs_next(agg_fs, mat_sumcheck_msgs * GEN ** (6 * rd))
        agg_fs, msg_ginf, c = fs_next(agg_fs, c)
        agg_fs, rv = squeeze(agg_fs)
        estore(mat_point * GEN ** (3 * rd), rv)
        g_zero = eadd(mat_running, msg_g1)
        c_one_0 = eadd(g_zero, msg_g1)
        c_one = eadd(c_one_0, msg_ginf)
        term_0 = emul(msg_ginf, rv)
        term_1 = eadd(term_0, c_one)
        term_2 = emul(term_1, rv)
        mat_running = eadd(term_2, g_zero)
    # terminal weights: U_t(r*) = urow_t(r*_row) * wcol_t(r*_col), with
    # row_weight = (sum_i L_i(zz_t) eq(r*[0..6], i)) * eq(zrho_t, r*[6..K_LOG]) and
    # col_weight = (sum_i z_partial_t[i] eq(r*[K_LOG..K_LOG+6], i)) * prod_j (1 + lrr_j
    # + r*[2*K_LOG-1-j]) (the lincheck binds column variables top-down).
    eq_rows = HeapBuf(3 * (2 ** (K_SKIP + 1) - 2))
    eqtree(mat_point, eq_rows, K_SKIP)
    eq_cols = HeapBuf(3 * (2 ** (K_SKIP + 1) - 2))
    eqtree(mat_point * GEN ** (3 * K_LOG), eq_cols, K_SKIP)
    weight_a = [0, 0, 0]
    weight_b = [0, 0, 0]
    for t in unroll(0, NSUB):
        z_skip_t = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 2)))
        row_nums = lag64(z_skip_t, 0)
        row_weight = [0, 0, 0]
        for i in unroll(0, 2 ** K_SKIP):
            row_num = sload(row_nums, i)
            inv = lagrange_inv_s(i)
            eq_value = eload(eq_rows * GEN ** (3 * (2 ** K_SKIP - 2 + i)))
            term_0 = emul(row_num, inv)
            term = emul(term_0, eq_value)
            row_weight = eadd(row_weight, term)
        for k in unroll(0, LINCHECK_ROUNDS):
            defer_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + k)))
            point_value = eload(mat_point * GEN ** (3 * (K_SKIP + k)))
            factor_0 = eadd(one_ext, defer_value)
            factor = eadd(factor_0, point_value)
            row_weight = emul(row_weight, factor)
        col_weight = [0, 0, 0]
        for i in unroll(0, 2 ** K_SKIP):
            defer_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 * LINCHECK_ROUNDS + i)))
            eq_value = eload(eq_cols * GEN ** (3 * (2 ** K_SKIP - 2 + i)))
            term = emul(defer_value, eq_value)
            col_weight = eadd(col_weight, term)
        for j in unroll(0, LINCHECK_ROUNDS):
            defer_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + LINCHECK_ROUNDS + j)))
            point_value = eload(mat_point * GEN ** (3 * (2 * K_LOG - 1 - j)))
            factor_0 = eadd(one_ext, defer_value)
            factor = eadd(factor_0, point_value)
            col_weight = emul(col_weight, factor)
        weight_u = emul(row_weight, col_weight)
        gamma_value = eload(gamma_mat * GEN ** (3 * t))
        alpha_value = eload(defer * GEN ** (3 * (t * DEFER_SIZE + BYTECODE_LOG + LOG2_BYTECODE_COLS + 1)))
        weighted_0 = emul(gamma_value, alpha_value)
        weighted_1 = emul(weighted_0, weight_u)
        weight_a = eadd(weight_a, weighted_1)
        weighted_b = emul(gamma_value, weight_u)
        weight_b = eadd(weight_b, weighted_b)
    a_star = [mat_stars_hint[0], mat_stars_hint[1], mat_stars_hint[2]]
    b_star = [mat_stars_hint[3], mat_stars_hint[4], mat_stars_hint[5]]
    final_a = emul(a_star, weight_a)
    final_b = emul(b_star, weight_b)
    mat_final = eadd(final_a, final_b)
    ext_assert_eq(mat_running, mat_final)

    # ---- bind the FS seed + sub statements + reduced claims to the PI ----
    out_fs = [STATEMENT_SEED_0, STATEMENT_SEED_1, STATEMENT_SEED_2, STATEMENT_SEED_3]
    out_fs = obs_base(out_fs, NSUB)
    out_fs = obs_base(out_fs, fs_seed[0])
    out_fs = obs_base(out_fs, fs_seed[1])
    out_fs = obs_base(out_fs, fs_seed[2])
    out_fs = obs_base(out_fs, fs_seed[3])
    for sub in unroll(0, NSUB):
        sub_pi_ptr = sub_pis * GEN ** (4 * sub)
        sub_pi_prefix = eload(sub_pi_ptr)
        out_fs = obs_base(out_fs, sub_pi_prefix[0])
        out_fs = obs_base(out_fs, sub_pi_prefix[1])
        out_fs = obs_base(out_fs, sub_pi_prefix[2])
        out_fs = obs_base(out_fs, sub_pi_ptr[GEN ** 3])
    for k in unroll(0, BYTECODE_VARS):
        point_value = eload(bc_point * GEN ** (3 * k))
        out_fs = obs(out_fs, point_value)
    out_fs = obs(out_fs, bytecode_star)
    for k in unroll(0, 2 * K_LOG):
        point_value = eload(mat_point * GEN ** (3 * k))
        out_fs = obs(out_fs, point_value)
    out_fs = obs(out_fs, a_star)
    out_fs = obs(out_fs, b_star)
    pub_ptr = GEN ** 0
    own_pi_prefix = eload(pub_ptr)
    own_pi_0 = own_pi_prefix[0]
    own_pi_1 = own_pi_prefix[1]
    own_pi_2 = own_pi_prefix[2]
    own_pi_3 = pub_ptr[GEN ** 3]
    out_word_0 = out_fs[0]
    out_word_1 = out_fs[1]
    out_word_2 = out_fs[2]
    out_word_3 = out_fs[3]
    assert own_pi_0 == out_word_0  # the guest's OWN public input == blake3 of (inner digest | sub statements | reduced claims)
    assert own_pi_1 == out_word_1
    assert own_pi_2 == out_word_2
    assert own_pi_3 == out_word_3
    return
