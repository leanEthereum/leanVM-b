from snark_lib import *

# The proof stream rides ONE padded witness hint (the guest walks only the
# prefix the shape dictates); binding always comes from the per-word absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
# Per-table tau floor: BLAKE3 is sized to flock's instance count (>= 2^3).
FLOORS = [0, 0, 0, 0, 0, 0, 0, 3]
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
COORD_GCOL_POW = COORD_GCOL_POW_PLACEHOLDER
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
TABLE_ADD = 0
TABLE_MUL = 1
TABLE_ADD_EXT = 2
TABLE_MUL_EXT = 3
TABLE_SET = 4
TABLE_DEREF = 5
TABLE_JUMP = 6
TABLE_BLAKE3 = 7
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
# Phase E: the stacked mixed opening. The two ring-switch fronts
# (claim check in-circuit; the tensor transpose + eval_rs_eq DEFERRED); the
# gamma-combination of the two ring-switch claims and the N_CLAIMS pool claims.
# Phase E2: the Ligerito opening over the stacked commitment, dispatched by
# the certified committed log-size m through match_range: the LIG_* tables
# below carry one row per (rate, m), with rate in 1..=4 and m in the
# supported committed-size interval,
# emitted from the SAME derive_profile/level_shapes the prover uses.
# Scalars index as TBL[m_idx]; per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl],
# where m_idx is the flattened (rate, size) configuration index;
# per-fold grind schedules with the LIG_MAX_TOTAL_FOLDS stride; the subspace
# vanishing constants with the LIG_MAX_VANISH_LEN stride. The eval_b terminal
# claim descriptors keep only the FIXED parts baked (CLAIM_POINT_BUF, named
# POINT_BUF_* below; CLAIM_POINT_OFF into those buffers) — the
# shape-dependent lengths/selectors are hinted and identity-certified.
# Opening dispatch: baked committed log-size, candidate range, g^-LIG_MIN_LOG_SIZE.
LIG_MIN_LOG_SIZE = LIG_MIN_LOG_SIZE_PLACEHOLDER
LIG_N_LOG_SIZES = LIG_N_LOG_SIZES_PLACEHOLDER
LIG_N_RATES = LIG_N_RATES_PLACEHOLDER
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
LIG_LEAF_BYTES = LIG_LEAF_BYTES_PLACEHOLDER
LIG_LEAF_PAIRS = LIG_LEAF_PAIRS_PLACEHOLDER
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
# Per-claim y-slot hint stride (overlap mask / slot bits rows).
YR_SLOT_STRIDE = YR_SLOT_STRIDE_PLACEHOLDER
# Which point buffer a pooled claim's x-part lives in (CLAIM_POINT_BUF codes):
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QPKD = 3
POINT_BUF_QPKD_RHO = 4
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_POINT_OFF = CLAIM_POINT_OFF_PLACEHOLDER
QPKD_VARS_CAP = QPKD_VARS_CAP_PLACEHOLDER
# The trace-dual basis factors across F2 < K < E:
# dual[64*j+i] = TRACE_DUAL_BASE[i] * TRACE_DUAL_TOWER[j].
# This reduces its Frobenius/coefficient tables from 192x192 to 64x64 + 192x3.
TRACE_DUAL_BASE = TRACE_DUAL_BASE_PLACEHOLDER
TRACE_DUAL_TOWER = TRACE_DUAL_TOWER_PLACEHOLDER
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
TRANSCRIPT_SEED_2 = TRANSCRIPT_SEED_2_PLACEHOLDER
TRANSCRIPT_SEED_3 = TRANSCRIPT_SEED_3_PLACEHOLDER

DS_SCALAR = 1
DS_BYTE = 2
DS_LEN = 3
DS_SQ = 4
DS_POW = 5

# Field structure: GF(2^192), represented as three GF(2^64) tower limbs.
# One GF192 challenge batches the 192 transposed ring-switch coordinates with
# univariate powers (1, rho, ..., rho^191).
FIELD_BITS = 192
BASE_FIELD_BITS = 64
# Exponent bit-widths: an announced 32-bit count decomposes into COUNT_BITS
# bits (count == 2^32 tops); any structural size (sums of 2^kappa, packing
# offsets) fits SIZE_BITS bits.
COUNT_BITS = 33
SIZE_BITS = 34


@inline
def f192_from_limbs(c0, c1, c2):
    out = [c0, c1, c2]
    return out


@inline
def ebase(x):
    out = [x, 0, 0]
    return out


@inline
def eadd(a: Ext, b: Ext):
    out = StackBuf(3)
    add_ext(a, b, out)
    return out


@inline
def emul(a: Ext, b: Ext):
    out = StackBuf(3)
    mul_ext(a, b, out)
    return out


@inline
def ediv(a: Ext, b: Ext):
    out = StackBuf(3)
    div_ext(a, b, out)
    return out


@inline
def epoly3(x: Ext, c0: Ext, c1: Ext, c2: Ext):
    return eadd(c0, emul(x, eadd(c1, emul(x, c2))))


@inline
def epoly4(x: Ext, c0: Ext, c1: Ext, c2: Ext, c3: Ext):
    return eadd(c0, emul(x, eadd(c1, emul(x, eadd(c2, emul(x, c3))))))


@inline
def epoly7(x: Ext, c0: Ext, c1: Ext, c2: Ext, c3: Ext, c4: Ext, c5: Ext, c6: Ext):
    return eadd(c0, emul(x, eadd(c1, emul(x, eadd(c2, emul(x, eadd(c3, emul(x, eadd(c4, emul(x, eadd(c5, emul(x, c6))))))))))))


@inline
def combine_tower_limbs(c0: Ext, c1: Ext, c2: Ext):
    y = [Y_TOWER[0], Y_TOWER[1], Y_TOWER[2]]
    return eadd(c0, emul(y, eadd(c1, emul(y, c2))))


@inline
def base_air_constraint(col_evals, eta: Ext, is_mul: Const):
    fp = sload(col_evals, 0)
    c0 = eadd(sload(col_evals, 4), emul(fp, sload(col_evals, 1)))
    c1 = eadd(sload(col_evals, 5), emul(fp, sload(col_evals, 2)))
    c2 = eadd(sload(col_evals, 6), emul(fp, sload(col_evals, 3)))
    if is_mul == 0:
        result = eadd(sload(col_evals, 7), sload(col_evals, 8))
    else:
        result = emul(sload(col_evals, 7), sload(col_evals, 8))
    c3 = eadd(sload(col_evals, 9), result)
    return epoly4(eta, c0, c1, c2, c3)


@inline
def ext_air_constraint(col_evals, eta: Ext, is_mul: Const):
    fp = sload(col_evals, 0)
    c0 = eadd(sload(col_evals, 4), emul(fp, sload(col_evals, 1)))
    c1 = eadd(sload(col_evals, 5), emul(fp, sload(col_evals, 2)))
    c2 = eadd(sload(col_evals, 6), emul(fp, sload(col_evals, 3)))
    va = combine_tower_limbs(sload(col_evals, 7), sload(col_evals, 8), sload(col_evals, 9))
    vb = combine_tower_limbs(sload(col_evals, 10), sload(col_evals, 11), sload(col_evals, 12))
    vc = combine_tower_limbs(sload(col_evals, 13), sload(col_evals, 14), sload(col_evals, 15))
    if is_mul == 0:
        result = eadd(va, vb)
    else:
        result = emul(va, vb)
    return epoly4(eta, c0, c1, c2, eadd(vc, result))


@inline
def ext_assert_eq(a: Ext, b: Ext):
    assert a[0] == b[0]
    assert a[1] == b[1]
    assert a[2] == b[2]
    return


@inline
def eload(ptr):
    out = [ptr[GEN ** 0], ptr[GEN ** 1], ptr[GEN ** 2]]
    return out


@inline
def estore(ptr, value: Ext):
    ptr[GEN ** 0] = value[0]
    ptr[GEN ** 1] = value[1]
    ptr[GEN ** 2] = value[2]
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


def check_field_bits_decomposition(bits_ptr, v: Ext):
    # Boolean-constrain FIELD_BITS hinted bits and assert they reconstruct v in
    # the F192 COORDINATE basis (hint_decompose_bits emits coordinate bits).
    acc = [0, 0, 0]
    for i in unroll(0, FIELD_BITS):
        b = bits_ptr[GEN ** i]
        assert b * b == b
        basis = coord_basis(i)
        term = [b * basis[0], b * basis[1], b * basis[2]]
        acc = eadd(acc, term)
    ext_assert_eq(acc, v)
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
    acc = [0, 0, 0]
    for j in unroll(0, per_word):
        position = 0
        for b in unroll(0, depth):
            t = bits_ptr[GEN ** (j * depth + b)]
            sq = t * t
            assert sq == t
            # position: the query index (integer). COORD_BASIS[b] = new(2^b, 0)
            # for b < depth < 64, so position = new(Σ t_b 2^b, 0).
            position += t * (2 ** b)
            # reconstruction of v in the coordinate basis (bit j*depth+b).
            basis = coord_basis(j * depth + b)
            term = [t * basis[0], t * basis[1], t * basis[2]]
            acc = eadd(acc, term)
        positions_out[GEN ** j] = position
        bit_ptrs_out[GEN ** j] = bits_ptr * GEN ** (j * depth)
    for i in unroll(per_word * depth, FIELD_BITS):
        t = bits_ptr[GEN ** i]
        sq = t * t
        assert sq == t
        basis = coord_basis(i)
        term = [t * basis[0], t * basis[1], t * basis[2]]
        acc = eadd(acc, term)
    ext_assert_eq(acc, v)
    return


def grind_check(state_0, state_1, state_2, state_3, nonce, nbits_g):
    # Ligerito fold/query grinding: digest = H(H(state, (0, POW)), (nonce, POW)); the digest's
    # bits are advice-decomposed HERE and verified (booleanity + reconstruction,
    # check_field_bits_decomposition), and the low nbits (nbits_g = g^nbits) must
    # be zero — the CONTIGUOUS PoW window of transcript::pow_bits_ok. The
    # caller absorbs the nonce afterwards.
    st = [state_0, state_1, state_2, state_3]
    base = StackBuf(4)
    pow_tag = [0, 0, DS_POW]
    sponge_compress(st, pow_tag, 0, base)
    out = StackBuf(4)
    nonce_tag = [nonce, 0, DS_POW]
    sponge_compress(base, nonce_tag, 0, out)
    digest_bits = HeapBuf(GEN ** FIELD_BITS)
    hint_decompose_bits(digest_bits, out[0], 64)
    hint_decompose_bits(digest_bits * GEN ** 64, out[1], 64)
    hint_decompose_bits(digest_bits * GEN ** 128, out[2], 64)
    digest = challenge_from_state(out)
    check_field_bits_decomposition(digest_bits, digest)
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


def verify_merkle_path(leaf_0, leaf_1, leaf_2, leaf_3, path_ptr, direction_bits, depth: Const):
    node_0 = leaf_0
    node_1 = leaf_1
    node_2 = leaf_2
    node_3 = leaf_3
    for level in unroll(0, depth):
        sibling_0 = path_ptr[GEN ** (4 * level)]
        sibling_1 = path_ptr[GEN ** (4 * level + 1)]
        sibling_2 = path_ptr[GEN ** (4 * level + 2)]
        sibling_3 = path_ptr[GEN ** (4 * level + 3)]
        dir_bit = direction_bits[GEN ** level]  # query index bit: 0 keeps the running node left, 1 swaps it right
        diff_0 = node_0 + sibling_0
        diff_1 = node_1 + sibling_1
        diff_2 = node_2 + sibling_2
        diff_3 = node_3 + sibling_3
        left = [node_0 + dir_bit * diff_0, node_1 + dir_bit * diff_1, node_2 + dir_bit * diff_2, node_3 + dir_bit * diff_3]
        right = [diff_0 + left[0], diff_1 + left[1], diff_2 + left[2], diff_3 + left[3]]
        parent = StackBuf(4)
        blake3(left, right, parent[0:4])
        node_0 = parent[0]
        node_1 = parent[1]
        node_2 = parent[2]
        node_3 = parent[3]
    return node_0, node_1, node_2, node_3


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
    x = [cursor[GEN ** 0], cursor[GEN ** 1], cursor[GEN ** 2]]
    nb = StackBuf(4)
    sponge_compress(state, x, DS_SCALAR, nb)
    return nb, x, cursor * GEN ** 3


@inline
def absorb(state, x, tag):
    # Tagged absorb (length frames, byte words, grinding nonces).
    nb = StackBuf(4)
    value = [x, 0, tag]
    sponge_compress(state, value, 0, nb)
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


def open_stacked(m_idx: Const, fs0, fs1, fs2, fs3, target: Ext, commit_root_0, commit_root_1, commit_root_2, commit_root_3, cursor, sumcheck_out, inner_out):
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
    #   5. sample beta, fold the query sums into the running target.
    # Then the per-level residuals (novel-basis prefix x final-message fold)
    # are combined; the caller's eval_b terminal asserts the grand total.
    #
    # Returns (sumcheck_target, fold_challenges, final_msg, residual_total,
    # yr_log_n_g = g^yr_log_n, yr_pad_g = g^(YR_LOG_CAP - yr_log_n),
    # fold_cap_g = g^lenris). yr_log_n_g/yr_pad_g let the terminal zero-pin
    # residual-slot coordinates beyond final_msg's 2^yr_log_n cells (positions
    # yr_log_n .. YR_LOG_CAP-1); fold_cap_g is the certified total fold count
    # the terminal pins its hinted claim lengths against.
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
    level_roots_0 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    level_roots_1 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    level_roots_2 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    level_roots_3 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
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
                nonce_v = msg_cursor[GEN ** 0]  # raw transport word: bound by the DS_POW absorb below
                assert msg_cursor[GEN ** 1] == 0
                assert msg_cursor[GEN ** 2] == 0
                msg_cursor = msg_cursor * GEN ** 3
                grind_check(fs[0], fs[1], fs[2], fs[3], nonce_v, GEN ** LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx])
                fs = absorb(fs, nonce_v, DS_POW)
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
            level_roots_0[GEN ** (lvl + 1)] = next_root[0]
            level_roots_1[GEN ** (lvl + 1)] = next_root[1]
            level_roots_2[GEN ** (lvl + 1)] = next_root[2]
            level_roots_3[GEN ** (lvl + 1)] = next_root[3]
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
        q_nonce = msg_cursor[GEN ** 0]  # raw transport word: bound by the DS_POW absorb below
        assert msg_cursor[GEN ** 1] == 0
        assert msg_cursor[GEN ** 2] == 0
        msg_cursor = msg_cursor * GEN ** 3
        if LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl] != 0:
            grind_check(fs[0], fs[1], fs[2], fs[3], q_nonce, GEN ** LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl])
        fs = absorb(fs, q_nonce, DS_POW)

        sqz_chain_0 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_1 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_2 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_3 = HeapBuf(GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1))
        sqz_chain_0[GEN ** 0] = fs[0]
        sqz_chain_1[GEN ** 0] = fs[1]
        sqz_chain_2[GEN ** 0] = fs[2]
        sqz_chain_3[GEN ** 0] = fs[3]
        for xs in mul_range(1, GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]):
            packed_word, next_c0, next_c1, next_c2, next_c3 = squeeze_step(sqz_chain_0[xs], sqz_chain_1[xs], sqz_chain_2[xs], sqz_chain_3[xs])
            sqz_chain_0[xs * GEN] = next_c0
            sqz_chain_1[xs * GEN] = next_c1
            sqz_chain_2[xs * GEN] = next_c2
            sqz_chain_3[xs * GEN] = next_c3
            query_ptr = xs ** (FIELD_BITS // LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            decode_query_bits(packed_word, query_positions * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, query_bit_ptrs * GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * query_ptr, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
        fs = [sqz_chain_0[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]], sqz_chain_1[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]], sqz_chain_2[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]], sqz_chain_3[GEN ** LIG_SQUEEZES[m_idx * LIG_MAX_LEVELS + lvl]]]

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
            if lvl == 0:
                row_base = xe ** LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]
            else:
                row_base = xe ** (3 * LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl])
            row_ptr = merkle_leaf_rows * GEN ** LIG_ROWS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * row_base
            leaf_hash_state = [GEN ** LIG_LEAF_BYTES[m_idx * LIG_MAX_LEVELS + lvl], 0, 0, 0]
            row_dot = [0, 0, 0]
            if lvl == 0:
                # Level-0 rows are base-field F64, four words per BLAKE3 input.
                for jb in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl] // 4):
                    e0 = row_ptr[GEN ** (4 * jb)]
                    e1 = row_ptr[GEN ** (4 * jb + 1)]
                    e2 = row_ptr[GEN ** (4 * jb + 2)]
                    e3 = row_ptr[GEN ** (4 * jb + 3)]
                    row_pair = [e0, e1, e2, e3]
                    leaf_digest = StackBuf(4)
                    blake3(leaf_hash_state, row_pair, leaf_digest[0:4])
                    leaf_hash_state = leaf_digest
                    w0 = eload(row_eq_weights * GEN ** (3 * (4 * jb)))
                    w1 = eload(row_eq_weights * GEN ** (3 * (4 * jb + 1)))
                    w2 = eload(row_eq_weights * GEN ** (3 * (4 * jb + 2)))
                    w3 = eload(row_eq_weights * GEN ** (3 * (4 * jb + 3)))
                    row_dot = eadd(row_dot, eadd(eadd(emul(ebase(e0), w0), emul(ebase(e1), w1)), eadd(emul(ebase(e2), w2), emul(ebase(e3), w3))))
            else:
                for jb in unroll(0, LIG_LEAF_PAIRS[m_idx * LIG_MAX_LEVELS + lvl]):
                    e0 = row_ptr[GEN ** (4 * jb)]
                    e1 = row_ptr[GEN ** (4 * jb + 1)]
                    e2 = row_ptr[GEN ** (4 * jb + 2)]
                    e3 = row_ptr[GEN ** (4 * jb + 3)]
                    # Higher-level F192 rows arrive as flat F64 tower limbs;
                    # constrain every serialized limb before reassembly.
                    row_pair = [e0, e1, e2, e3]
                    leaf_digest = StackBuf(4)
                    blake3(leaf_hash_state, row_pair, leaf_digest[0:4])
                    leaf_hash_state = leaf_digest
                for jw in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
                    row_word = f192_from_limbs(row_ptr[GEN ** (3 * jw)], row_ptr[GEN ** (3 * jw + 1)], row_ptr[GEN ** (3 * jw + 2)])
                    row_weight = eload(row_eq_weights * GEN ** (3 * jw))
                    row_dot = eadd(row_dot, emul(row_word, row_weight))
            node_0 = leaf_hash_state[0]
            node_1 = leaf_hash_state[1]
            node_2 = leaf_hash_state[2]
            node_3 = leaf_hash_state[3]
            prev_query_sum = eload(query_sum_chain * xe ** 3)
            alpha_weight = eload(alpha_weights * GEN ** (3 * lvl * LIG_MAX_QUERIES[m_idx]) * xe ** 3)
            estore(query_sum_chain * xe ** 3 * GEN ** 3, eadd(prev_query_sum, emul(alpha_weight, row_dot)))
            direction_bits = query_bit_ptrs[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xe]
            path_base = xe ** (4 * LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            path_ptr = merkle_paths * GEN ** LIG_PATHS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * path_base
            root_0, root_1, root_2, root_3 = verify_merkle_path(node_0, node_1, node_2, node_3, path_ptr, direction_bits, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            if lvl == 0:
                assert root_0 == commit_root_0
                assert root_1 == commit_root_1
                assert root_2 == commit_root_2
                assert root_3 == commit_root_3
            else:
                assert root_0 == level_roots_0[GEN ** lvl]
                assert root_1 == level_roots_1[GEN ** lvl]
                assert root_2 == level_roots_2[GEN ** lvl]
                assert root_3 == level_roots_3[GEN ** lvl]
        level_query_sum = eload(query_sum_chain * GEN ** (3 * LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]))

        if lvl == LIG_YR_LEVEL[m_idx]:
            fs, beta_lvl = squeeze(fs)
            estore(level_betas * GEN ** (3 * lvl), beta_lvl)
            sumcheck_target = eadd(sumcheck_target, emul(beta_lvl, level_query_sum))
        else:
            fs, intro_u0, msg_cursor = fs_next(fs, msg_cursor)
            fs, intro_u2, msg_cursor = fs_next(fs, msg_cursor)
            fs, beta_lvl = squeeze(fs)
            estore(level_betas * GEN ** (3 * lvl), beta_lvl)
            round_quad_c = eadd(round_quad_c, emul(beta_lvl, intro_u0))
            round_quad_b = eadd(round_quad_b, emul(beta_lvl, eadd(level_query_sum, intro_u2)))
            round_quad_a = eadd(round_quad_a, emul(beta_lvl, intro_u2))
            sumcheck_target = eadd(sumcheck_target, emul(beta_lvl, level_query_sum))

    # ---- per-level residuals: novel-basis prefix x final-message fold ----
    inner_chain = HeapBuf(GEN ** (3 * (LIG_N_LEVELS[m_idx] + 1)))
    estore(inner_chain, [0, 0, 0])
    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        residual_chain = HeapBuf(GEN ** (3 * (LIG_MAX_QUERIES[m_idx] + 1)))
        estore(residual_chain, [0, 0, 0])
        for xr in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            basis_w = StackBuf(3 * LIG_LOG_MSG_COLS_CAP)
            basis_chain = ebase(query_positions[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xr])
            inv_idx = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl]
            vanish_inv = [LIG_VANISH_INVS[3 * inv_idx], LIG_VANISH_INVS[3 * inv_idx + 1], LIG_VANISH_INVS[3 * inv_idx + 2]]
            sstore(basis_w, 0, emul(basis_chain, vanish_inv))
            for t in unroll(1, LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + lvl]):
                val_idx = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t - 1
                vanish_val = [LIG_VANISH_VALS[3 * val_idx], LIG_VANISH_VALS[3 * val_idx + 1], LIG_VANISH_VALS[3 * val_idx + 2]]
                basis_chain = emul(basis_chain, eadd(basis_chain, vanish_val))
                inv_idx = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t
                vanish_inv = [LIG_VANISH_INVS[3 * inv_idx], LIG_VANISH_INVS[3 * inv_idx + 1], LIG_VANISH_INVS[3 * inv_idx + 2]]
                sstore(basis_w, t, emul(basis_chain, vanish_inv))
            prefix_eq = [1, 0, 0]
            for t in unroll(0, LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl]):
                fold_c = eload(fold_challenges * GEN ** (3 * (LIG_RESIDUAL_FOLD_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t)))
                bw = sload(basis_w, t)
                prefix_eq = emul(prefix_eq, eadd([1, 0, 0], emul(fold_c, eadd([1, 0, 0], bw))))
            fold_w = StackBuf(3 * 2 * YR_LOG_CAP)
            for j in unroll(0, LIG_YR_LOG_LEN[m_idx]):
                sstore(fold_w, 2 * j, [1, 0, 0])
                sstore(fold_w, 2 * j + 1, sload(basis_w, LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl] + j))
            yr_eval = fold_final_msg(final_msg, fold_w, 0, LIG_YR_LOG_LEN[m_idx])
            prev_residual = eload(residual_chain * xr ** 3)
            alpha_weight = eload(alpha_weights * GEN ** (3 * lvl * LIG_MAX_QUERIES[m_idx]) * xr ** 3)
            residual = emul(emul(alpha_weight, prefix_eq), yr_eval)
            estore(residual_chain * xr ** 3 * GEN ** 3, eadd(prev_residual, residual))
        prev_inner = eload(inner_chain * GEN ** (3 * lvl))
        beta_lvl = eload(level_betas * GEN ** (3 * lvl))
        residual_total = eload(residual_chain * GEN ** (3 * LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]))
        estore(inner_chain * GEN ** (3 * (lvl + 1)), eadd(prev_inner, emul(beta_lvl, residual_total)))

    # Explicit OOD bases are eq(z, ·). Fold their prefixes at all subsequent
    # sumcheck challenges and evaluate the remaining yr_log_n-coordinate tail
    # directly against the final message.
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
            ood_fold_w = StackBuf(3 * 2 * YR_LOG_CAP)
            for t in unroll(0, LIG_YR_LOG_LEN[m_idx]):
                zt = eload(oz * GEN ** (3 * (z_folded + t)))
                sstore(ood_fold_w, 2 * t, eadd([1, 0, 0], zt))
                sstore(ood_fold_w, 2 * t + 1, zt)
            ood_eval = fold_final_msg(final_msg, ood_fold_w, 0, LIG_YR_LOG_LEN[m_idx])
            ood_inner = eadd(ood_inner, emul(scalar, ood_eval))
    inner_total = eadd(eload(inner_chain * GEN ** (3 * LIG_N_LEVELS[m_idx])), ood_inner)
    estore(sumcheck_out, sumcheck_target)
    estore(inner_out, inner_total)
    return fold_challenges, final_msg, GEN ** LIG_YR_LOG_LEN[m_idx], GEN ** (YR_LOG_CAP - LIG_YR_LOG_LEN[m_idx]), GEN ** LIG_TOTAL_FOLDS[m_idx]


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


def verify_sub(pi_0, pi_1, pi_2, pi_3, seed_0, seed_1, seed_2, seed_3, base_delta_pows, tower_delta_pows, g_logs_pow2, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement
    # (pi_0, pi_1). All proof data is hinted HERE: each call pops the next
    # sub-proof's entry of every witness stream, so the body lowers once and
    # main just calls it per statement. The factored dual-basis Frobenius tables
    # and the exponent lookup tables are shared read-only across calls; the
    # deferred-claim data is written to `defer_out`.
    #
    # Flow (mirrors cpu::verify):
    #   1. seed the Fiat-Shamir sponge from the statement + program digest;
    #   2. announced sizes, then certify every structural log against them
    #      (count gadget log2_ceil: tau per table, log_mem);
    #   3. bind the commitment root; ONE RLC-batched GKR for all three trees (count padded
    #      to the pair's depth) at runtime depth, ONE shared point zeta;
    #   4. derive the block kappas, certify the GKR side depths; balance check
    #      with advice-decomposed padding ladders; 3x leaf decomposition
    #      against the GKR claims (pooling the committed-coordinate claims);
    #      the stacked-bytecode reduction (deferred);
    #   5. one AIR zerocheck per instruction table at the certified taus;
    #   6. public-input claim + BLAKE3 pin claims (telescoped prefix MLE);
    #   7. flock reduction: univariate-skip zerocheck + lincheck (matrix
    #      evaluation deferred);
    #   8. ring-switch fronts (shared rho, linearized transpose in-circuit);
    #   9. gamma-combine everything, certify the committed size m, dispatch
    #      the stacked Ligerito opening (open_stacked), and assert its
    #      eval_b terminal;
    #  10. export the deferred-claim region for the aggregation.
    # Claim pool: values of every committed-coordinate claim, in decompose order
    # (their points are the GKR ζ's, resolvable from the baked block structure).
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

    # ---- announced layout and PCS rate (observed, then certified) ----
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

    # ---- structural logs: certify g^log_mem, compute the taus ----
    # The stream announced the sizes as integer WORDS; the shape-generic phases
    # need them as G-POWERS (loop bounds, match_range scrutinees). dims_g[0] =
    # g^log_mem arrives as a hint pinned to the word; dims_g[1 + t] = g^tau_t
    # is computed by the count gadget.
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_{N_TABLES-1}]
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
    zeta = HeapBuf(g_bus_mu ** 3)  # the ONE shared GKR point: three words per coordinate

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
    # PADDED with identity leaves up to it (product unchanged), so a single
    # sumcheck serves all three trees: the prover combines their round
    # messages with weights 1, λ, λ². Each layer binds the six tail
    # evaluations, checks the combined product identity, samples the line
    # challenge, then a FRESH λ — pinning the individual values inside the
    # bound combination (the last layer's are pinned by the decompose
    # identities). All three trees reduce to claims at ONE shared point zeta.
    # State threads through write-once heap chains: layer state indexed by the
    # layer cursor, round state by a position pointer advancing per round.
    gkr_roots = StackBuf(3 * N_GKR_SIDES)
    gkr_claims = StackBuf(3 * N_GKR_SIDES)
    gkr_layer_size = g_bus_mu * GEN ** 2  # runtime size in the exponent: mu + 2 slots
    gkr_layer_fs0 = HeapBuf(gkr_layer_size)
    gkr_layer_fs1 = HeapBuf(gkr_layer_size)
    gkr_layer_fs2 = HeapBuf(gkr_layer_size)
    gkr_layer_fs3 = HeapBuf(gkr_layer_size)
    gkr_layer_cursor = HeapBuf(gkr_layer_size)
    gkr_layer_claim = HeapBuf(gkr_layer_size ** 3)    # push's running value
    gkr_layer_claim_b = HeapBuf(gkr_layer_size ** 3)  # pull's
    gkr_layer_claim_c = HeapBuf(gkr_layer_size ** 3)  # count's
    gkr_layer_lambda = HeapBuf(gkr_layer_size ** 3)   # the layer's combiner
    gkr_layer_row = HeapBuf(gkr_layer_size)
    gkr_layer_round_pos = HeapBuf(gkr_layer_size)
    gkr_round_fs0 = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_fs1 = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_fs2 = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_fs3 = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_cursor = HeapBuf(GKR_ROUNDS_CAP)
    gkr_round_claim = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_round_eq = HeapBuf(3 * GKR_ROUNDS_CAP)
    gkr_pts = HeapBuf(3 * GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    fs, root_push, cursor = fs_next(fs, cursor)
    fs, root_pull, cursor = fs_next(fs, cursor)
    fs, root_count, cursor = fs_next(fs, cursor)
    fs, initial_layer_lambda = squeeze(fs)
    estore(gkr_layer_lambda, initial_layer_lambda)
    gkr_layer_fs0[GEN ** 0] = fs[0]
    gkr_layer_fs1[GEN ** 0] = fs[1]
    gkr_layer_fs2[GEN ** 0] = fs[2]
    gkr_layer_fs3[GEN ** 0] = fs[3]
    gkr_layer_cursor[GEN ** 0] = cursor
    estore(gkr_layer_claim, root_push)
    estore(gkr_layer_claim_b, root_pull)
    estore(gkr_layer_claim_c, root_count)
    gkr_layer_row[GEN ** 0] = gkr_pts
    gkr_layer_round_pos[GEN ** 0] = GEN ** 0
    for x_layer in mul_range(1, g_bus_mu):
        layer_fs = [gkr_layer_fs0[x_layer], gkr_layer_fs1[x_layer], gkr_layer_fs2[x_layer], gkr_layer_fs3[x_layer]]
        lam = eload(gkr_layer_lambda * x_layer ** 3)
        claim_a = eload(gkr_layer_claim * x_layer ** 3)
        claim_b = eload(gkr_layer_claim_b * x_layer ** 3)
        claim_c = eload(gkr_layer_claim_c * x_layer ** 3)
        claim_l = eadd(claim_a, emul(lam, eadd(claim_b, emul(lam, claim_c))))
        point_row = gkr_layer_row[x_layer]
        round_pos = gkr_layer_round_pos[x_layer]
        nextrow = point_row * GEN ** (3 * MU_CAP)
        gkr_round_fs0[round_pos] = layer_fs[0]
        gkr_round_fs1[round_pos] = layer_fs[1]
        gkr_round_fs2[round_pos] = layer_fs[2]
        gkr_round_fs3[round_pos] = layer_fs[3]
        gkr_round_cursor[round_pos] = gkr_layer_cursor[x_layer]
        estore(gkr_round_claim * round_pos ** 3, claim_l)
        estore(gkr_round_eq * round_pos ** 3, [1, 0, 0])
        for x_round in mul_range(1, x_layer):
            ip = round_pos * x_round
            round_claim_v = eload(gkr_round_claim * ip ** 3)
            round_eq_v = eload(gkr_round_eq * ip ** 3)
            point_v = eload(point_row * x_round ** 3)
            nfs0, nfs1, nfs2, nfs3, ncur, nclaim, neq, rk = sumcheck_round3(gkr_round_fs0[ip], gkr_round_fs1[ip], gkr_round_fs2[ip], gkr_round_fs3[ip], gkr_round_cursor[ip], round_claim_v, round_eq_v, point_v)
            estore(nextrow * x_round ** 3 * GEN ** 3, rk)
            pos_next = ip * GEN
            gkr_round_fs0[pos_next] = nfs0
            gkr_round_fs1[pos_next] = nfs1
            gkr_round_fs2[pos_next] = nfs2
            gkr_round_fs3[pos_next] = nfs3
            gkr_round_cursor[pos_next] = ncur
            estore(gkr_round_claim * pos_next ** 3, nclaim)
            estore(gkr_round_eq * pos_next ** 3, neq)
        final_pos = round_pos * x_layer
        tail_fs = [gkr_round_fs0[final_pos], gkr_round_fs1[final_pos], gkr_round_fs2[final_pos], gkr_round_fs3[final_pos]]
        tcur = gkr_round_cursor[final_pos]
        tclaim = eload(gkr_round_claim * final_pos ** 3)
        teq = eload(gkr_round_eq * final_pos ** 3)
        tail_fs, e0_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_count, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_count, tcur = fs_next(tail_fs, tcur)
        tail_product_push = emul(e0_push, e1_push)
        tail_product_pull = emul(e0_pull, e1_pull)
        tail_product_count = emul(e0_count, e1_count)
        tail_combined = eadd(tail_product_push, emul(lam, eadd(tail_product_pull, emul(lam, tail_product_count))))
        ext_assert_eq(tclaim, emul(teq, tail_combined))
        tail_fs, layer_challenge = squeeze(tail_fs)
        estore(nextrow, layer_challenge)
        xln = x_layer * GEN
        estore(gkr_layer_claim * xln ** 3, eadd(e0_push, emul(layer_challenge, eadd(e0_push, e1_push))))
        estore(gkr_layer_claim_b * xln ** 3, eadd(e0_pull, emul(layer_challenge, eadd(e0_pull, e1_pull))))
        estore(gkr_layer_claim_c * xln ** 3, eadd(e0_count, emul(layer_challenge, eadd(e0_count, e1_count))))
        tail_fs, tail_lambda = squeeze(tail_fs)  # fresh λ pins the tail individuals
        estore(gkr_layer_lambda * xln ** 3, tail_lambda)
        gkr_layer_fs0[xln] = tail_fs[0]
        gkr_layer_fs1[xln] = tail_fs[1]
        gkr_layer_fs2[xln] = tail_fs[2]
        gkr_layer_fs3[xln] = tail_fs[3]
        gkr_layer_cursor[xln] = tcur
        gkr_layer_row[xln] = nextrow
        gkr_layer_round_pos[xln] = round_pos * x_layer * GEN
    fs = [gkr_layer_fs0[g_bus_mu], gkr_layer_fs1[g_bus_mu], gkr_layer_fs2[g_bus_mu], gkr_layer_fs3[g_bus_mu]]
    cursor = gkr_layer_cursor[g_bus_mu]
    final_point_row = gkr_layer_row[g_bus_mu]
    for xt in mul_range(1, g_bus_mu):
        estore(zeta * xt ** 3, eload(final_point_row * xt ** 3))
    sstore(gkr_roots, PUSH_SIDE, root_push)
    sstore(gkr_roots, PULL_SIDE, root_pull)
    sstore(gkr_roots, COUNT_SIDE, root_count)
    sstore(gkr_claims, PUSH_SIDE, eload(gkr_layer_claim * g_bus_mu ** 3))
    sstore(gkr_claims, PULL_SIDE, eload(gkr_layer_claim_b * g_bus_mu ** 3))
    sstore(gkr_claims, COUNT_SIDE, eload(gkr_layer_claim_c * g_bus_mu ** 3))

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
    pad_products = HeapBuf(3 * 2)
    for s in unroll(0, 2):
        side_pad_product = [1, 0, 0]
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            pad_fp = [0, 0, 0]
            alpha_pow = [1, 0, 0]
            for i in unroll(0, BLOCK_COORD_COUNT[b]):
                pad_fp = eadd(pad_fp, emul(alpha_pow, ebase(COORD_PAD_VAL[BLOCK_COORD_OFF[b] + i])))
                alpha_pow = emul(alpha_pow, alpha)
            g_two_kappa = g_squares[block_kappa[GEN ** b]]  # g^(2^κ_b)
            if BLOCK_REAL_TABLE[b] == REAL_IS_FULL_CUBE:
                g_real = g_two_kappa  # shared block: real = 2^κ, so DELTA = 0
            else:
                g_real = count_gpows[GEN ** BLOCK_REAL_TABLE[b]]  # g^count_t
            g_delta_want = g_two_kappa / g_real  # g^DELTA (feeds the advice below)
            pad_bits = HeapBuf(GEN ** COUNT_BITS)
            hint_decompose_bits_exponent(pad_bits, g_delta_want, COUNT_BITS)
            ladder = [1, 0, 0]
            ladder_square = eadd(gamma, pad_fp)
            g_delta = GEN ** 0
            for j in unroll(0, COUNT_BITS):
                pad_bit = pad_bits[GEN ** j]
                assert pad_bit * pad_bit == pad_bit
                ladder = emul(ladder, eadd([1, 0, 0], emul(ebase(pad_bit), eadd(ladder_square, [1, 0, 0]))))
                g_delta *= (1 + pad_bit * (g_squares[GEN ** j] + 1))  # g^DELTA
                ladder_square = emul(ladder_square, ladder_square)
            assert g_real * g_delta == g_two_kappa  # real_b + DELTA_b == 2^κ_b
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
    block_eq_hi = HeapBuf(3 * N_BLOCKS)      # per push block, reused by its pull twin
    block_index_mle = HeapBuf(3 * N_BLOCKS)  # per push block with an Index coord
    for s in unroll(0, N_GKR_SIDES):
        acc = [0, 0, 0]
        selector_sum = [0, 0, 0]
        zeta_zs = zeta
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_public_idx = 0
            kappa_g = block_kappa[GEN ** b]
            assert log(kappa_g) < SIZE_BITS
            if s == PULL_SIDE:
                eq_hi = eload(block_eq_hi * GEN ** (3 * (b - SIDE_BLOCK_START[PULL_SIDE])))
            else:
                # eq_hi over the ζ coords above κ against the selector bits
                # derived below; the selector length is mu_s − κ = g^mu_s / g^κ.
                sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                assert log(sel_len_g) < SIZE_BITS
                zeta_hi = zeta_zs * kappa_g ** 3
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
                    sbit = sel_bits[xk]
                    assert sbit * sbit == sbit
                    prev_eq = eload(eq_chain * xk ** 3)
                    zeta_v = eload(zeta_hi * xk ** 3)
                    estore(eq_chain * xk ** 3 * GEN ** 3, emul(prev_eq, eadd(ebase(1 + sbit), zeta_v)))
                    goff_chain[xk * GEN] = goff_chain[xk] * (1 + sbit * (g_squares[kappa_g * xk] + 1))  # weight g^(2^(κ+k))
                eq_hi = eload(eq_chain * sel_len_g ** 3)
                assert goff_chain[sel_len_g] == block_off_g[GEN ** b]  # bits == offset >> κ, κ-aligned
                if s == PUSH_SIDE:
                    estore(block_eq_hi * GEN ** (3 * b), eq_hi)
            selector_sum = eadd(selector_sum, eq_hi)
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
                    coord_val = emul([GEN ** COORD_GCOL_POW[BLOCK_COORD_OFF[b] + i], 0, 0], rawv)
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_INDEX:
                    if s == PULL_SIDE:
                        coord_val = eload(block_index_mle * GEN ** (3 * (b - SIDE_BLOCK_START[PULL_SIDE])))
                    else:
                        idx_chain = HeapBuf(3 * (MU_CAP + 2))
                        estore(idx_chain, [1, 0, 0])
                        for xt in mul_range(1, kappa_g):
                            idx_prev = eload(idx_chain * xt ** 3)
                            zeta_v = eload(zeta_zs * xt ** 3)
                            idx_factor = eadd([1, 0, 0], emul(zeta_v, ebase(idxc_tab[xt])))
                            estore(idx_chain * xt ** 3 * GEN ** 3, emul(idx_prev, idx_factor))
                        coord_val = eload(idx_chain * kappa_g ** 3)
                        if s == PUSH_SIDE:
                            estore(block_index_mle * GEN ** (3 * b), coord_val)
                if COORD_TYPE[BLOCK_COORD_OFF[b] + i] == COORD_KIND_PUBLIC:
                    # push and pull share zeta, so BOTH bytecode blocks read the
                    # same six evaluations (indexed per block, not globally).
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
        ext_assert_eq(acc, sload(gkr_claims, s))
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

    # ---- per-table zerochecks ------------------------------------------------
    # For each table: eta, the zerocheck point r (tau samples), tau eq-trick
    # rounds (claim starts at 0), then the involved-column evaluations (pooled)
    # and the final AIR check claim == eq_acc * C_t(eta, evals).
    # RUNTIME round counts: tau_t is the certified announced log height
    # (dims_g[1 + t], certified by the count gadget). Round state threads
    # through heap chains exactly like the GKR trees.
    rho = HeapBuf(3 * N_TABLES * TAU_CAP)
    zc_point_fs0 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_point_fs1 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_point_fs2 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_point_fs3 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_fs0 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_fs1 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_fs2 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_fs3 = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_cursor = HeapBuf(N_TABLES * (TAU_CAP + 2))
    zc_round_claim = HeapBuf(3 * N_TABLES * (TAU_CAP + 2))
    zc_round_eq = HeapBuf(3 * N_TABLES * (TAU_CAP + 2))
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        fs, eta = squeeze(fs)
        # the zerocheck point r: tau squeezes, sponge chained by round.
        eq_r = HeapBuf(3 * TAU_CAP)
        point_fs0 = zc_point_fs0 * GEN ** (t * (TAU_CAP + 2))
        point_fs1 = zc_point_fs1 * GEN ** (t * (TAU_CAP + 2))
        point_fs2 = zc_point_fs2 * GEN ** (t * (TAU_CAP + 2))
        point_fs3 = zc_point_fs3 * GEN ** (t * (TAU_CAP + 2))
        point_fs0[GEN ** 0] = fs[0]
        point_fs1[GEN ** 0] = fs[1]
        point_fs2[GEN ** 0] = fs[2]
        point_fs3[GEN ** 0] = fs[3]
        for xk in mul_range(1, tau_g):
            point_fs = [point_fs0[xk], point_fs1[xk], point_fs2[xk], point_fs3[xk]]
            point_fs, point_challenge = squeeze(point_fs)
            estore(eq_r * xk ** 3, point_challenge)
            xkn = xk * GEN
            point_fs0[xkn] = point_fs[0]
            point_fs1[xkn] = point_fs[1]
            point_fs2[xkn] = point_fs[2]
            point_fs3[xkn] = point_fs[3]
        fs = [point_fs0[tau_g], point_fs1[tau_g], point_fs2[tau_g], point_fs3[tau_g]]
        # tau eq-trick rounds (claim starts at 0, eq at 1).
        round_fs0 = zc_round_fs0 * GEN ** (t * (TAU_CAP + 2))
        round_fs1 = zc_round_fs1 * GEN ** (t * (TAU_CAP + 2))
        round_fs2 = zc_round_fs2 * GEN ** (t * (TAU_CAP + 2))
        round_fs3 = zc_round_fs3 * GEN ** (t * (TAU_CAP + 2))
        round_cursor = zc_round_cursor * GEN ** (t * (TAU_CAP + 2))
        round_claim = zc_round_claim * GEN ** (3 * t * (TAU_CAP + 2))
        round_eq = zc_round_eq * GEN ** (3 * t * (TAU_CAP + 2))
        rho_t = rho * GEN ** (3 * t * TAU_CAP)
        round_fs0[GEN ** 0] = fs[0]
        round_fs1[GEN ** 0] = fs[1]
        round_fs2[GEN ** 0] = fs[2]
        round_fs3[GEN ** 0] = fs[3]
        round_cursor[GEN ** 0] = cursor
        estore(round_claim, [0, 0, 0])
        estore(round_eq, [1, 0, 0])
        for xk in mul_range(1, tau_g):
            nfs0, nfs1, nfs2, nfs3, ncur, nclaim, neq, rk = sumcheck_round3(round_fs0[xk], round_fs1[xk], round_fs2[xk], round_fs3[xk], round_cursor[xk], eload(round_claim * xk ** 3), eload(round_eq * xk ** 3), eload(eq_r * xk ** 3))
            estore(rho_t * xk ** 3, rk)
            xkn = xk * GEN
            round_fs0[xkn] = nfs0
            round_fs1[xkn] = nfs1
            round_fs2[xkn] = nfs2
            round_fs3[xkn] = nfs3
            round_cursor[xkn] = ncur
            estore(round_claim * xkn ** 3, nclaim)
            estore(round_eq * xkn ** 3, neq)
        fs = [round_fs0[tau_g], round_fs1[tau_g], round_fs2[tau_g], round_fs3[tau_g]]
        cursor = round_cursor[tau_g]
        claim = eload(round_claim * tau_g ** 3)
        eq_acc = eload(round_eq * tau_g ** 3)
        col_evals = StackBuf(3 * AIR_COLS_CAP)
        for k in unroll(0, N_AIR_COLS[t]):
            fs, e, cursor = fs_next(fs, cursor)
            sstore(col_evals, k, e)
            estore(claim_pool * GEN ** (3 * claim_idx), e)
            claim_cplen_g[GEN ** claim_idx] = tau_g  # cplen = tau_t
            claim_idx += 1
        # The table's AIR constraint at the final point. Every committed base
        # column evaluates to an extension scalar at the random point.
        if t == TABLE_ADD:
            constraint_eval = base_air_constraint(col_evals, eta, 0)
        if t == TABLE_MUL:
            constraint_eval = base_air_constraint(col_evals, eta, 1)
        if t == TABLE_ADD_EXT:
            constraint_eval = ext_air_constraint(col_evals, eta, 0)
        if t == TABLE_MUL_EXT:
            constraint_eval = ext_air_constraint(col_evals, eta, 1)
        if t == TABLE_SET:
            constraint_eval = eadd(sload(col_evals, 2), emul(sload(col_evals, 0), sload(col_evals, 1)))
        if t == TABLE_DEREF:
            fp = sload(col_evals, 0)
            fpc = sload(col_evals, 8)
            ffp = sload(col_evals, 9)
            v3 = sload(col_evals, 11)
            src = eadd(emul(eadd(eadd([1, 0, 0], fpc), ffp), v3), eadd(emul(fpc, emul([GEN * GEN, 0, 0], sload(col_evals, 12))), emul(ffp, fp)))
            c0 = eadd(sload(col_evals, 4), emul(fp, sload(col_evals, 1)))
            c1 = eadd(sload(col_evals, 5), emul(sload(col_evals, 7), sload(col_evals, 2)))
            c2 = eadd(sload(col_evals, 6), emul(fp, sload(col_evals, 3)))
            c3 = eadd(sload(col_evals, 10), src)
            constraint_eval = epoly4(eta, c0, c1, c2, c3)
        if t == TABLE_JUMP:
            pc = sload(col_evals, 0)
            fp = sload(col_evals, 1)
            b = sload(col_evals, 14)
            one_plus_b = eadd(b, [1, 0, 0])
            fall_through = emul([GEN, 0, 0], pc)
            c0 = eadd(sload(col_evals, 7), emul(fp, sload(col_evals, 4)))
            c1 = eadd(sload(col_evals, 8), emul(fp, sload(col_evals, 5)))
            c2 = eadd(sload(col_evals, 9), emul(fp, sload(col_evals, 6)))
            c3 = eadd(b, emul(sload(col_evals, 10), sload(col_evals, 13)))
            c4 = emul(sload(col_evals, 10), one_plus_b)
            c5 = eadd(sload(col_evals, 2), eadd(emul(b, sload(col_evals, 11)), emul(one_plus_b, fall_through)))
            c6 = eadd(sload(col_evals, 3), eadd(emul(b, sload(col_evals, 12)), emul(one_plus_b, fp)))
            constraint_eval = epoly7(eta, c0, c1, c2, c3, c4, c5, c6)
        if t == TABLE_BLAKE3:
            fp = sload(col_evals, 0)
            c0 = eadd(sload(col_evals, 4), emul(fp, sload(col_evals, 1)))
            c1 = eadd(sload(col_evals, 5), emul(fp, sload(col_evals, 2)))
            c2 = eadd(sload(col_evals, 6), emul(fp, sload(col_evals, 3)))
            constraint_eval = epoly3(eta, c0, c1, c2)
        ext_assert_eq(claim, emul(eq_acc, constraint_eval))

    # ---- public-input binding claim: one base-word MEM column ----
    # The first four memory words are evaluated at a random two-variable point;
    # all higher memory coordinates are fixed to zero.
    fs, rm0 = squeeze(fs)
    fs, rm1 = squeeze(fs)
    pi_lo = eadd(ebase(pi_0), emul(rm0, ebase(pi_0 + pi_1)))
    pi_hi = eadd(ebase(pi_2), emul(rm0, ebase(pi_2 + pi_3)))
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
    zerocheck_r = HeapBuf(mr1cs_g ** 3)
    for i in unroll(0, K_SKIP):
        fs, rv = squeeze(fs)
        estore(zerocheck_r * GEN ** (3 * i), rv)
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        fixed_challenge = [FIXED_CHALLENGES[3 * i], FIXED_CHALLENGES[3 * i + 1], FIXED_CHALLENGES[3 * i + 2]]
        estore(zerocheck_r * GEN ** (3 * (K_SKIP + i)), fixed_challenge)
    # outer samples at runtime count: m = K_LOG + tau_5 (certified).
    flock_point_fs0 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs1 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs2 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs3 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs0[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[0]
    flock_point_fs1[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[1]
    flock_point_fs2[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[2]
    flock_point_fs3[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[3]
    for xi in mul_range(GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS), mr1cs_g):
        point_fs = [flock_point_fs0[xi], flock_point_fs1[xi], flock_point_fs2[xi], flock_point_fs3[xi]]
        point_fs, zerocheck_challenge = squeeze(point_fs)
        estore(zerocheck_r * xi ** 3, zerocheck_challenge)
        xin = xi * GEN
        flock_point_fs0[xin] = point_fs[0]
        flock_point_fs1[xin] = point_fs[1]
        flock_point_fs2[xin] = point_fs[2]
        flock_point_fs3[xin] = point_fs[3]
    fs = [flock_point_fs0[mr1cs_g], flock_point_fs1[mr1cs_g], flock_point_fs2[mr1cs_g], flock_point_fs3[mr1cs_g]]
    # round-1 message (ab ‖ c, 2 * 2^K_SKIP words): fetch + observe each word as
    # it comes off the stream, then sample z.
    zc_round1 = HeapBuf(3 * 2 * 2 ** K_SKIP)
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
    flock_round_fs0 = HeapBuf(flock_round_size)
    flock_round_fs1 = HeapBuf(flock_round_size)
    flock_round_fs2 = HeapBuf(flock_round_size)
    flock_round_fs3 = HeapBuf(flock_round_size)
    flock_round_running = HeapBuf(flock_round_size ** 3)
    flock_round_cursor = HeapBuf(flock_round_size)  # the walking cursor, threaded like the fs state
    flock_round_fs0[GEN ** N_FIXED_CHALLENGE_ROUNDS] = fs[0]
    flock_round_fs1[GEN ** N_FIXED_CHALLENGE_ROUNDS] = fs[1]
    flock_round_fs2[GEN ** N_FIXED_CHALLENGE_ROUNDS] = fs[2]
    flock_round_fs3[GEN ** N_FIXED_CHALLENGE_ROUNDS] = fs[3]
    estore(flock_round_running * GEN ** (3 * N_FIXED_CHALLENGE_ROUNDS), zc_running)
    flock_round_cursor[GEN ** N_FIXED_CHALLENGE_ROUNDS] = cursor
    for xi in mul_range(GEN ** N_FIXED_CHALLENGE_ROUNDS, nmlv_g):
        round_fs = [flock_round_fs0[xi], flock_round_fs1[xi], flock_round_fs2[xi], flock_round_fs3[xi]]
        round_running = eload(flock_round_running * xi ** 3)
        r_eq = eload(zerocheck_r * GEN ** (3 * K_SKIP) * xi ** 3)
        cur_i = flock_round_cursor[xi]
        round_fs, gamma_c, cur_i = fs_next(round_fs, cur_i)
        round_fs, g_inf, cur_i = fs_next(round_fs, cur_i)
        gamma_ab = ediv(eadd(round_running, emul(r_eq, gamma_c)), eadd([1, 0, 0], r_eq))
        round_fs, rho_v = squeeze(round_fs)
        estore(zerocheck_rhos * xi ** 3, rho_v)
        round_running = eadd(gamma_ab, emul(rho_v, eadd(eadd(gamma_ab, gamma_c), emul(eadd([1, 0, 0], rho_v), g_inf))))
        xin = xi * GEN
        flock_round_fs0[xin] = round_fs[0]
        flock_round_fs1[xin] = round_fs[1]
        flock_round_fs2[xin] = round_fs[2]
        flock_round_fs3[xin] = round_fs[3]
        estore(flock_round_running * xin ** 3, round_running)
        flock_round_cursor[xin] = cur_i
    fs = [flock_round_fs0[nmlv_g], flock_round_fs1[nmlv_g], flock_round_fs2[nmlv_g], flock_round_fs3[nmlv_g]]
    zc_running = eload(flock_round_running * nmlv_g ** 3)
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
    z_partial = HeapBuf(3 * 2 ** K_SKIP)
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

    # ---- stacked mixed opening: ring-switch fronts + claim combination ----
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
    c_table = HeapBuf(3 * FIELD_BITS)
    z_vals = HeapBuf(3 * 2 * QPKD_VARS_CAP)
    for rs in unroll(0, 2):
        # observe this claim's 64 s_hat_v entries (mirror of verify_observe /
        # observe_ext_slice) before the claim check and the shared rho.
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
    # One rho is shared by both claims after both slices have been absorbed.
    # The coordinate weights are (1, rho, ..., rho^191). Construct each
    # linearized coefficient directly by Horner evaluation, so neither the
    # powers nor an equality tree need to be materialized.
    fs, rs_batch = squeeze(fs)
    # dual[64*j+i] = base[i] * tower[j], hence
    #   c_k = (sum_i rho^i base[i]^(2^k))
    #         * (sum_j rho^(64j) tower[j]^(2^k)).
    # The base factor has period 64 under Frobenius. Computing the two factors
    # costs 64^2 + 3*192 products instead of 192^2.
    rho_64 = rs_batch
    for i in unroll(0, 6):
        rho_64 = emul(rho_64, rho_64)
    base_coeffs = HeapBuf(3 * BASE_FIELD_BITS)
    for xk in mul_range(1, GEN ** BASE_FIELD_BITS):
        delta_row = base_delta_pows * xk ** (3 * BASE_FIELD_BITS)
        c_acc = eload(delta_row * GEN ** (3 * (BASE_FIELD_BITS - 1)))
        for i in unroll(1, BASE_FIELD_BITS):
            c_acc = eadd(emul(c_acc, rs_batch), eload(delta_row * GEN ** (3 * (BASE_FIELD_BITS - 1 - i))))
        estore(base_coeffs * xk ** 3, c_acc)
    for block in unroll(0, 3):
        for xr in mul_range(1, GEN ** BASE_FIELD_BITS):
            xk = xr * GEN ** (block * BASE_FIELD_BITS)
            tower_row = tower_delta_pows * xk ** 9
            tower_coeff = eadd(emul(eadd(emul(eload(tower_row * GEN ** 6), rho_64), eload(tower_row * GEN ** 3)), rho_64), eload(tower_row))
            estore(c_table * xk ** 3, emul(eload(base_coeffs * xr ** 3), tower_coeff))
    # Evaluate both claims together: they share c_k and x^i, so each is loaded
    # or advanced once rather than once per claim.
    s_hat_row_0 = s_hat_v
    s_hat_row_1 = s_hat_v * GEN ** (3 * (2 ** K_SKIP))
    x_pow_chain = HeapBuf(3 * ((2 ** K_SKIP) + 1))
    estore(x_pow_chain, [1, 0, 0])
    t_chain_0 = HeapBuf(3 * ((2 ** K_SKIP) + 1))
    t_chain_1 = HeapBuf(3 * ((2 ** K_SKIP) + 1))
    estore(t_chain_0, [0, 0, 0])
    estore(t_chain_1, [0, 0, 0])
    for x_round in mul_range(1, GEN ** (2 ** K_SKIP)):
        y_pow_0 = eload(s_hat_row_0 * x_round ** 3)
        y_pow_1 = eload(s_hat_row_1 * x_round ** 3)
        lin_eval_0 = [0, 0, 0]
        lin_eval_1 = [0, 0, 0]
        for k in unroll(0, FIELD_BITS):
            ck = eload(c_table * GEN ** (3 * k))
            lin_eval_0 = eadd(lin_eval_0, emul(ck, y_pow_0))
            lin_eval_1 = eadd(lin_eval_1, emul(ck, y_pow_1))
            y_pow_0 = emul(y_pow_0, y_pow_0)
            y_pow_1 = emul(y_pow_1, y_pow_1)
        x_pow = eload(x_pow_chain * x_round ** 3)
        estore(t_chain_0 * x_round ** 3 * GEN ** 3, eadd(eload(t_chain_0 * x_round ** 3), emul(x_pow, lin_eval_0)))
        estore(t_chain_1 * x_round ** 3 * GEN ** 3, eadd(eload(t_chain_1 * x_round ** 3), emul(x_pow, lin_eval_1)))
        estore(x_pow_chain * x_round ** 3 * GEN ** 3, emul(x_pow, [2, 0, 0]))
    sstore(transposed_claims, 0, eload(t_chain_0 * GEN ** (3 * (2 ** K_SKIP))))
    sstore(transposed_claims, 1, eload(t_chain_1 * GEN ** (3 * (2 ** K_SKIP))))
    # Suffix points for the two transparent weights.
    for t in unroll(0, LINCHECK_ROUNDS):
        estore(z_vals * GEN ** (3 * t), eload(lincheck_rs * GEN ** (3 * (LINCHECK_ROUNDS - 1 - t))))
    zv_lo = z_vals * GEN ** (3 * LINCHECK_ROUNDS)
    zr_hi = zerocheck_rhos * GEN ** (3 * LINCHECK_ROUNDS)
    for xt in mul_range(1, tau_blake3_g):
        estore(zv_lo * xt ** 3, eload(zr_hi * xt ** 3))
    zv_hi = z_vals * GEN ** (3 * QPKD_VARS_CAP)
    zcr7 = zerocheck_r * GEN ** (3 * K_SKIP)
    for xt in mul_range(1, tau_blake3_g * GEN ** SLOT_STRIDE_LOG):
        estore(zv_hi * xt ** 3, eload(zcr7 * xt ** 3))
    # gamma-combine the two transposed sumcheck claims (computed in-circuit).
    fs, gamma_ab = squeeze(fs)
    fs, gamma_c = squeeze(fs)
    target = eadd(emul(gamma_ab, sload(transposed_claims, 0)), emul(gamma_c, sload(transposed_claims, 1)))
    # ...then every pooled point claim, each observed.
    for j in unroll(0, N_CLAIMS):
        fs = obs(fs, eload(claim_pool * GEN ** (3 * j)))
    gamma_pool = HeapBuf(3 * N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        fs, gv = squeeze(fs)
        estore(gamma_pool * GEN ** (3 * j), gv)
        target = eadd(target, emul(gv, eload(claim_pool * GEN ** (3 * j))))

    # ================= the Ligerito opening core (stacked, m = STACK) ========

    # ---- stacked Ligerito opening: dispatch on the committed log-size ----
    # ---- certify g^m: m = max(log2_ceil(sum_cols 2^kappa), PCS_MIN_MU) ----
    # Integer addition rides the exponent: g^total = Π g^(2^kappa) over the
    # committed columns (kappas from the certified announced logs via the baked
    # source map); log2_ceil_in_the_exponent does the rest, with the PCS_MIN_MU
    # floor waiving minimality exactly like the per-table tau floors.
    g_total = GEN ** 0
    for c in unroll(0, N_COMMITTED_COLS):
        g_total *= g_squares[kappa_base[GEN ** COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]]
    gmv = log2_ceil_in_the_exponent(g_total, g_logs_pow2, g_squares, PCS_MIN_MU, SIZE_BITS)  # g^m
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES
    # Flatten (rate-1, m-MIN) in rate-major order. Both coordinates are
    # transcript-bound and range-checked above, so a single compiled guest can
    # dispatch independently for every inner proof in a mixed-rate batch.
    config_sel = size_sel * rate_sel ** LIG_N_LOG_SIZES
    sumcheck_out = HeapBuf(3)
    inner_out = HeapBuf(3)
    fold_challenges, final_msg, yr_log_n_g, yr_pad_g, fold_cap_g = match_range(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], fs[2], fs[3], target, commit_root_0, commit_root_1, commit_root_2, commit_root_3, cursor, sumcheck_out, inner_out))
    sumcheck_target = eload(sumcheck_out)
    inner_total = eload(inner_out)

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    # Per-claim lengths, selector bits, and slot data are HINTED; the closing
    # identity inner_sum == sumcheck_target (against the opening-bound target)
    # pins their VALUES, so only range checks and booleanity are enforced here.
    # All selector products use eq(b, r) = 1 + b + r.
    claim_low_len = HeapBuf(N_CLAIMS)  # computed low_len per claim (the y-slot
    #                             # overlap pointers below re-read it)
    claim_nover = HeapBuf(N_CLAIMS)
    hint_witness(claim_nover[0:N_CLAIMS], "claim_nover")
    pi_cplen = StackBuf(1)
    hint_witness(pi_cplen[0:1], "pi_cplen")
    claim_qpkd_slot_bits = HeapBuf(SLOT_STRIDE_LOG * N_CLAIMS)
    hint_witness(claim_qpkd_slot_bits[0:SLOT_STRIDE_LOG * N_CLAIMS], "claim_qpkd_slot_bits")
    claim_sel_bits = HeapBuf(COUNT_BITS * N_CLAIMS)
    hint_witness(claim_sel_bits[0:COUNT_BITS * N_CLAIMS], "claim_sel_bits")
    # baked prefix-mask table replacing the hinted overlap mask: row t holds
    # [k < t] for k in [0, YR_LOG_CAP); the y-slot loop below selects row nover
    # by pointer arithmetic, so the mask is a prefix of exactly nover ones BY
    # CONSTRUCTION (no hint, no booleanity/monotone/popcount pins).
    prefix_mask_table = HeapBuf((YR_LOG_CAP + 1) * YR_LOG_CAP)
    for t in unroll(0, YR_LOG_CAP + 1):
        for k in unroll(0, t):
            prefix_mask_table[GEN ** (t * YR_LOG_CAP + k)] = 1
        for k in unroll(t, YR_LOG_CAP):
            prefix_mask_table[GEN ** (t * YR_LOG_CAP + k)] = 0
    claim_yslot_bits = HeapBuf(YR_SLOT_STRIDE * N_CLAIMS)
    hint_witness(claim_yslot_bits[0:YR_SLOT_STRIDE * N_CLAIMS], "claim_yslot_bits")
    rs_yslot_bits = HeapBuf(YR_SLOT_STRIDE)
    hint_witness(rs_yslot_bits[0:YR_SLOT_STRIDE], "rs_yslot_bits")
    rs_sel_bits = HeapBuf(COUNT_BITS)
    hint_witness(rs_sel_bits[0:COUNT_BITS], "rs_sel_bits")
    claim_weights = HeapBuf(3 * N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        # EXACT lengths: cplen is certified, nover (the residual-overlap count)
        # is the ONE hinted branch choice; low_len = cplen - nover and
        # seln = lenris + nover - nlow are divisions off it, and the range
        # checks + the product pins below reject any wrong nover.
        if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
            # pi: cplen = min(log_mem, lenris), certified as a min (<= both via
            # the range-checked division slacks, == one via the product).
            cplen_g = pi_cplen[0]
            mem_slack = g_log_mem / cplen_g
            assert log(mem_slack) < SIZE_BITS
            fold_slack = fold_cap_g / cplen_g
            assert log(fold_slack) < SIZE_BITS
            assert (cplen_g + g_log_mem) * (cplen_g + fold_cap_g) == 0  # == one of them
            nlow = cplen_g                             # delta = 0 for pi
        else:
            cplen_g = claim_cplen_g[GEN ** j]
            nlow = cplen_g
            if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
                nlow = cplen_g * GEN ** SLOT_STRIDE_LOG  # nlow = cplen + the qpkd slot coords
            if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD_RHO:
                nlow = cplen_g * GEN ** SLOT_STRIDE_LOG
        nover_g = claim_nover[GEN ** j]
        # nover <= YR_LOG_CAP: honest nover <= yr_log_n <= cap, and the y-slot
        # loop below selects prefix_mask_table row nover, so its log must be
        # pinned to the table (subsumes the SIZE_BITS check the division
        # pins need).
        assert log(nover_g) < YR_LOG_CAP + 1
        low_len_g = cplen_g / nover_g              # low_len = cplen - nover
        assert log(low_len_g) < SIZE_BITS
        claim_low_len[GEN ** j] = low_len_g
        seln = fold_cap_g * nover_g / nlow         # seln = lenris + nover - nlow
        assert log(seln) < SIZE_BITS
        assert (nover_g + 1) * (seln + 1) == 0      # nover == 0 OR seln == 0
        # selector loop reads fold_challenges[nlow .. nlow+seln); pin the reach
        # so it stays in [0, lenris): either seln == 0 (empty loop) or
        # nlow + seln == lenris (the honest overlap-free case).
        assert (nlow * seln + fold_cap_g) * (seln + 1) == 0
        low_chain = HeapBuf(3 * (SIZE_BITS + 1))
        if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
            zptr = zeta * GEN ** (3 * CLAIM_POINT_OFF[j])
            estore(low_chain, [1, 0, 0])
            for xk in mul_range(1, low_len_g):
                factor = eadd(eadd([1, 0, 0], eload(zptr * xk ** 3)), eload(fold_challenges * xk ** 3))
                estore(low_chain * xk ** 3 * GEN ** 3, emul(eload(low_chain * xk ** 3), factor))
        if CLAIM_POINT_BUF[j] == POINT_BUF_RHO:
            rptr = rho * GEN ** (3 * CLAIM_POINT_OFF[j])
            estore(low_chain, [1, 0, 0])
            for xk in mul_range(1, low_len_g):
                factor = eadd(eadd([1, 0, 0], eload(rptr * xk ** 3)), eload(fold_challenges * xk ** 3))
                estore(low_chain * xk ** 3 * GEN ** 3, emul(eload(low_chain * xk ** 3), factor))
        if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
            estore(low_chain, [1, 0, 0])
            estore(low_chain * GEN ** 3, eadd(eadd([1, 0, 0], rm0), eload(fold_challenges)))
            second = emul(eload(low_chain * GEN ** 3), eadd(eadd([1, 0, 0], rm1), eload(fold_challenges * GEN ** 3)))
            estore(low_chain * GEN ** 6, second)
            for xk in mul_range(GEN ** 2, low_len_g):
                factor = eadd([1, 0, 0], eload(fold_challenges * xk ** 3))
                estore(low_chain * xk ** 3 * GEN ** 3, emul(eload(low_chain * xk ** 3), factor))
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
            qpkd_slot_eq = [1, 0, 0]
            for k in unroll(0, SLOT_STRIDE_LOG):
                sb3 = claim_qpkd_slot_bits[GEN ** (SLOT_STRIDE_LOG * j + k)]
                assert sb3 * sb3 == sb3
                qpkd_slot_eq = emul(qpkd_slot_eq, eadd(ebase(1 + sb3), eload(fold_challenges * GEN ** (3 * k))))
            zptr = zeta * GEN ** (3 * CLAIM_POINT_OFF[j])
            ris7 = fold_challenges * GEN ** (3 * SLOT_STRIDE_LOG)
            estore(low_chain, qpkd_slot_eq)
            for xk in mul_range(1, low_len_g):
                factor = eadd(eadd([1, 0, 0], eload(zptr * xk ** 3)), eload(ris7 * xk ** 3))
                estore(low_chain * xk ** 3 * GEN ** 3, emul(eload(low_chain * xk ** 3), factor))
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD_RHO:
            qpkd_slot_eq = [1, 0, 0]
            for k in unroll(0, SLOT_STRIDE_LOG):
                sb3 = claim_qpkd_slot_bits[GEN ** (SLOT_STRIDE_LOG * j + k)]
                assert sb3 * sb3 == sb3
                qpkd_slot_eq = emul(qpkd_slot_eq, eadd(ebase(1 + sb3), eload(fold_challenges * GEN ** (3 * k))))
            zptr = rho * GEN ** (3 * CLAIM_POINT_OFF[j])
            ris7 = fold_challenges * GEN ** (3 * SLOT_STRIDE_LOG)
            estore(low_chain, qpkd_slot_eq)
            for xk in mul_range(1, low_len_g):
                factor = eadd(eadd([1, 0, 0], eload(zptr * xk ** 3)), eload(ris7 * xk ** 3))
                estore(low_chain * xk ** 3 * GEN ** 3, emul(eload(low_chain * xk ** 3), factor))
        low_eq = eload(low_chain * low_len_g ** 3)
        ris_hi = fold_challenges * nlow ** 3
        selrow = claim_sel_bits * GEN ** (COUNT_BITS * j)
        sel_chain = HeapBuf(3 * (SIZE_BITS + 1))
        estore(sel_chain, low_eq)
        for xk in mul_range(1, seln):
            sel_bit = selrow[xk]
            assert sel_bit * sel_bit == sel_bit
            factor = eadd(ebase(1 + sel_bit), eload(ris_hi * xk ** 3))
            estore(sel_chain * xk ** 3 * GEN ** 3, emul(eload(sel_chain * xk ** 3), factor))
        claim_weight = emul(eload(sel_chain * seln ** 3), eload(gamma_pool * GEN ** (3 * j)))
        estore(claim_weights * GEN ** (3 * j), claim_weight)
    # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
    # (the telescoped product formula; z powers evolve by squaring per k).
    # QPKD_VARS_CAP = tau_5 + SLOT_STRIDE_LOG, exponent-additive from the certified
    # announced log; the per-k z-power rows chain by a runtime g^qpkdv
    # stride, and the inner passes are runtime loops with product/square
    # state chained per row.
    qpkdv_g = tau_blake3_g * GEN ** SLOT_STRIDE_LOG
    one_plus_q = HeapBuf(GEN ** (3 * QPKD_VARS_CAP))
    for x_round in mul_range(1, qpkdv_g):
        estore(one_plus_q * x_round ** 3, eadd([1, 0, 0], eload(fold_challenges * x_round ** 3)))
    # Evaluate both transparent weights in lockstep, sharing c_k and the
    # verifier-point factor in every inner iteration.
    z_pows_0 = HeapBuf(3 * (FIELD_BITS + 1) * QPKD_VARS_CAP)
    z_pows_1 = HeapBuf(3 * (FIELD_BITS + 1) * QPKD_VARS_CAP)
    z_row_src_1 = z_vals * GEN ** (3 * QPKD_VARS_CAP)
    for x_round in mul_range(1, qpkdv_g):
        estore(z_pows_0 * x_round ** 3, eload(z_vals * x_round ** 3))
        estore(z_pows_1 * x_round ** 3, eload(z_row_src_1 * x_round ** 3))
    e_acc_0 = HeapBuf(3 * (FIELD_BITS + 1))
    e_acc_1 = HeapBuf(3 * (FIELD_BITS + 1))
    estore(e_acc_0, [0, 0, 0])
    estore(e_acc_1, [0, 0, 0])
    row_ptr_0 = HeapBuf(FIELD_BITS + 1)
    row_ptr_1 = HeapBuf(FIELD_BITS + 1)
    row_ptr_0[GEN ** 0] = z_pows_0
    row_ptr_1[GEN ** 0] = z_pows_1
    for xk in mul_range(1, GEN ** FIELD_BITS):
        z_row_0 = row_ptr_0[xk]
        z_row_1 = row_ptr_1[xk]
        z_row_next_0 = z_row_0 * qpkdv_g ** 3
        z_row_next_1 = z_row_1 * qpkdv_g ** 3
        prod_chain_0 = HeapBuf(GEN ** (3 * (QPKD_VARS_CAP + 1)))
        prod_chain_1 = HeapBuf(GEN ** (3 * (QPKD_VARS_CAP + 1)))
        estore(prod_chain_0, [1, 0, 0])
        estore(prod_chain_1, [1, 0, 0])
        for x_round in mul_range(1, qpkdv_g):
            one_plus = eload(one_plus_q * x_round ** 3)
            zv_0 = eload(z_row_0 * x_round ** 3)
            zv_1 = eload(z_row_1 * x_round ** 3)
            estore(prod_chain_0 * x_round ** 3 * GEN ** 3, emul(eload(prod_chain_0 * x_round ** 3), eadd(zv_0, one_plus)))
            estore(prod_chain_1 * x_round ** 3 * GEN ** 3, emul(eload(prod_chain_1 * x_round ** 3), eadd(zv_1, one_plus)))
            estore(z_row_next_0 * x_round ** 3, emul(zv_0, zv_0))
            estore(z_row_next_1 * x_round ** 3, emul(zv_1, zv_1))
        ck = eload(c_table * xk ** 3)
        estore(e_acc_0 * xk ** 3 * GEN ** 3, eadd(eload(e_acc_0 * xk ** 3), emul(ck, eload(prod_chain_0 * qpkdv_g ** 3))))
        estore(e_acc_1 * xk ** 3 * GEN ** 3, eadd(eload(e_acc_1 * xk ** 3), emul(ck, eload(prod_chain_1 * qpkdv_g ** 3))))
        row_ptr_0[xk * GEN] = z_row_next_0
        row_ptr_1[xk * GEN] = z_row_next_1
    sstore(rs_eq_vals, 0, eload(e_acc_0 * GEN ** (3 * FIELD_BITS)))
    sstore(rs_eq_vals, 1, eload(e_acc_1 * GEN ** (3 * FIELD_BITS)))
    # ring-switch weight: extend by the selector bits over the fold_challenges
    # coords [qpkdv, lenris).
    rs_weight = eadd(emul(gamma_ab, sload(rs_eq_vals, 0)), emul(gamma_c, sload(rs_eq_vals, 1)))
    # rs_len = lenris - qpkdv, DERIVED as g^lenris / g^qpkdv (not hinted). The
    # selector loop then reads fold_challenges[qpkdv .. qpkdv+rs_len) = [qpkdv ..
    # lenris), inside its written [0, lenris) extent; a qpkdv > lenris would make
    # rs_len a huge exponent and blow the range check below.
    rs_len_g = fold_cap_g / qpkdv_g
    assert log(rs_len_g) < SIZE_BITS
    ris_q = fold_challenges * qpkdv_g ** 3
    rsw_chain = HeapBuf(3 * (SIZE_BITS + 1))
    estore(rsw_chain, rs_weight)
    for xk in mul_range(1, rs_len_g):
        rs_bit = rs_sel_bits[xk]
        assert rs_bit * rs_bit == rs_bit
        factor = eadd(ebase(1 + rs_bit), eload(ris_q * xk ** 3))
        estore(rsw_chain * xk ** 3 * GEN ** 3, emul(eload(rsw_chain * xk ** 3), factor))
    rs_weight = eload(rsw_chain * rs_len_g ** 3)
    # inner_sum = sum_y final_msg[y] * eval_b[y]: reordered per claim. Claim j's
    # y-contribution is cw_j times the final_msg MLE at the point (overlap coords
    # || hinted slot bits): coord_k = m_k * ov_k + (1 + m_k) * bit_k with
    # mask bits m_k = [k < NOVER], read from the baked prefix-mask row nover.
    # The dot unrolls over the global cap 2^YR_LOG_CAP, but final_msg only has
    # 2^yr_log_n cells, so the slot coordinates at k >= yr_log_n are ASSERTED
    # zero (below): the eq tensor then puts zero weight on every index
    # >= 2^yr_log_n, so the over-cap dot terms vanish and never depend on
    # out-of-buffer cells. The ring-switch slot is the same, with no overlaps
    # and the hinted YRS bits.
    inner_sum = inner_total
    for j in unroll(0, N_CLAIMS):
        slot_point = HeapBuf(3 * YR_LOG_CAP)
        overlap_ptr = rho * GEN ** (3 * CLAIM_POINT_OFF[j]) * claim_low_len[GEN ** j] ** 3
        if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
            overlap_ptr = zeta * GEN ** (3 * CLAIM_POINT_OFF[j]) * claim_low_len[GEN ** j] ** 3
        if CLAIM_POINT_BUF[j] == POINT_BUF_QPKD:
            overlap_ptr = zeta * GEN ** (3 * CLAIM_POINT_OFF[j]) * claim_low_len[GEN ** j] ** 3
        # overlap_ptr[g^k] reads the claim point at low_len + k, which is written
        # only for k < nover (the [low_len, cplen) span); at k >= nover it points
        # into the unwritten point-buffer gap (prover-chosen free cells). The
        # mask row IS the baked prefix of exactly nover ones (selected by the
        # pinned nover), so no overlap coord can read past cplen by construction;
        # a mask with a stray 1 at k >= nover would read a free cell and hand
        # the sumcheck a linear knob (a full opening forgery) - the point-reuse
        # analog of the hole b7b470c closed on the direct y-slot path.
        mask_row = prefix_mask_table * claim_nover[GEN ** j] ** YR_LOG_CAP  # row nover: g^(nover * cap)
        for k in unroll(0, YR_LOG_CAP):
            mask_bit = mask_row[GEN ** k]
            slot_bit = claim_yslot_bits[GEN ** (YR_SLOT_STRIDE * j + k)]
            assert slot_bit * slot_bit == slot_bit
            overlap = eload(overlap_ptr * GEN ** (3 * k))
            slot_coord = eadd(emul(ebase(mask_bit), overlap), ebase((1 + mask_bit) * slot_bit))
            estore(slot_point * GEN ** (3 * k), slot_coord)
        # zero-pin coords beyond final_msg's log-length (no over-cap weight): the
        # pointers start at yr_log_n. The zero asserts double as the
        # nover <= yr_log_n pin: a larger nover selects a row whose prefix
        # reaches into [yr_log_n, cap), failing here. So the mask is 0 in this
        # span, slot_point is 0, and no eq weight lands on the unwritten
        # final_msg cells past 2^yr_log_n.
        hi_mask = mask_row * yr_log_n_g
        hi_slot = claim_yslot_bits * GEN ** (YR_SLOT_STRIDE * j) * yr_log_n_g
        for xk in mul_range(1, yr_pad_g):
            assert hi_mask[xk] == 0
            assert hi_slot[xk] == 0
        slot_eq = HeapBuf(3 * (2 ** (YR_LOG_CAP + 1) - 2))
        eqtree(slot_point, slot_eq, YR_LOG_CAP)
        final_msg_dot = [0, 0, 0]
        for y in unroll(0, 2 ** YR_LOG_CAP):
            msg_value = eload(final_msg * GEN ** (3 * y))
            eq_value = eload(slot_eq * GEN ** (3 * (2 ** YR_LOG_CAP - 2 + y)))
            final_msg_dot = eadd(final_msg_dot, emul(msg_value, eq_value))
        point_term = emul(eload(claim_weights * GEN ** (3 * j)), final_msg_dot)
        inner_sum = eadd(inner_sum, point_term)
    rs_slot_point = HeapBuf(3 * YR_LOG_CAP)
    for k in unroll(0, YR_LOG_CAP):
        yb = rs_yslot_bits[GEN ** k]
        assert yb * yb == yb
        estore(rs_slot_point * GEN ** (3 * k), ebase(yb))
    rs_hi = rs_yslot_bits * yr_log_n_g
    for xk in mul_range(1, yr_pad_g):
        assert rs_hi[xk] == 0  # zero-pin coords beyond final_msg's log-length
    rs_slot_eq = HeapBuf(3 * (2 ** (YR_LOG_CAP + 1) - 2))
    eqtree(rs_slot_point, rs_slot_eq, YR_LOG_CAP)
    rs_msg_dot = [0, 0, 0]
    for y in unroll(0, 2 ** YR_LOG_CAP):
        msg_value = eload(final_msg * GEN ** (3 * y))
        eq_value = eload(rs_slot_eq * GEN ** (3 * (2 ** YR_LOG_CAP - 2 + y)))
        rs_msg_dot = eadd(rs_msg_dot, emul(msg_value, eq_value))
    rs_term = emul(rs_weight, rs_msg_dot)
    inner_sum = eadd(inner_sum, rs_term)
    ext_assert_eq(inner_sum, sumcheck_target)


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
    # Frobenius powers of the factored trace-dual basis. These tables are
    # claim- and sub-independent, so build them once.
    base_delta_pows = HeapBuf(3 * BASE_FIELD_BITS * BASE_FIELD_BITS)
    for i in unroll(0, BASE_FIELD_BITS):
        delta = [TRACE_DUAL_BASE[3 * i], TRACE_DUAL_BASE[3 * i + 1], TRACE_DUAL_BASE[3 * i + 2]]
        estore(base_delta_pows * GEN ** (3 * i), delta)
    for xk in mul_range(1, GEN ** (BASE_FIELD_BITS - 1)):
        delta_row = base_delta_pows * xk ** (3 * BASE_FIELD_BITS)
        next_delta_row = delta_row * GEN ** (3 * BASE_FIELD_BITS)
        for i in unroll(0, BASE_FIELD_BITS):
            delta_v = eload(delta_row * GEN ** (3 * i))
            estore(next_delta_row * GEN ** (3 * i), emul(delta_v, delta_v))
    tower_delta_pows = HeapBuf(3 * 3 * FIELD_BITS)
    for i in unroll(0, 3):
        delta = [TRACE_DUAL_TOWER[3 * i], TRACE_DUAL_TOWER[3 * i + 1], TRACE_DUAL_TOWER[3 * i + 2]]
        estore(tower_delta_pows * GEN ** (3 * i), delta)
    for xk in mul_range(1, GEN ** (FIELD_BITS - 1)):
        delta_row = tower_delta_pows * xk ** 9
        next_delta_row = delta_row * GEN ** 9
        for i in unroll(0, 3):
            delta_v = eload(delta_row * GEN ** (3 * i))
            estore(next_delta_row * GEN ** (3 * i), emul(delta_v, delta_v))

    # exponent-domain lookup tables, shared read-only across every sub-proof.
    g_logs_pow2, g_squares = exponent_tables()

    # per-sub deferred-claim regions (layout: see verify_sub's defer_out)
    defer = HeapBuf(NSUB * DEFER_SIZE * 3)

    for sub in unroll(0, NSUB):
        verify_sub(sub_pis[GEN ** (4 * sub)], sub_pis[GEN ** (4 * sub + 1)], sub_pis[GEN ** (4 * sub + 2)], sub_pis[GEN ** (4 * sub + 3)], fs_seed[0], fs_seed[1], fs_seed[2], fs_seed[3], base_delta_pows, tower_delta_pows, g_logs_pow2, g_squares, defer * GEN ** (sub * DEFER_SIZE * 3))

    # ================= aggregation: batch the deferred claims =================
    # A fresh transcript absorbs every deferred claim (points and values),
    # samples the RLC coefficients, and verifies the two batching sumchecks of
    # doc.tex §Deferred evaluation claims. Only the reduced claims (one per
    # fixed polynomial) reach the public input.
    agg_fs = [0, 0, 0, 0]
    for sub in unroll(0, NSUB):
        agg_fs = obs_base(agg_fs, sub_pis[GEN ** (4 * sub)])
        agg_fs = obs_base(agg_fs, sub_pis[GEN ** (4 * sub + 1)])
        agg_fs = obs_base(agg_fs, sub_pis[GEN ** (4 * sub + 2)])
        agg_fs = obs_base(agg_fs, sub_pis[GEN ** (4 * sub + 3)])
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
    out_fs = [0, 0, 0, 0]
    out_fs = obs_base(out_fs, fs_seed[0])
    out_fs = obs_base(out_fs, fs_seed[1])
    out_fs = obs_base(out_fs, fs_seed[2])
    out_fs = obs_base(out_fs, fs_seed[3])
    for sub in unroll(0, NSUB):
        out_fs = obs_base(out_fs, sub_pis[GEN ** (4 * sub)])
        out_fs = obs_base(out_fs, sub_pis[GEN ** (4 * sub + 1)])
        out_fs = obs_base(out_fs, sub_pis[GEN ** (4 * sub + 2)])
        out_fs = obs_base(out_fs, sub_pis[GEN ** (4 * sub + 3)])
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
    own_pi_0 = pub_ptr[1]
    own_pi_1 = pub_ptr[GEN]
    own_pi_2 = pub_ptr[GEN ** 2]
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
