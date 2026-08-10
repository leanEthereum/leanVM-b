from snark_lib import *

# The proof stream rides ONE padded witness hint (the guest walks only the
# prefix the shape dictates); binding always comes from the per-word absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
# Per-table tau floor: BLAKE3 is sized to flock's instance count (>= 2^3).
FLOORS = [0, 0, 0, 0, 0, 3, 0]
MIN_LOG_MEM = MIN_LOG_MEM_PLACEHOLDER
INV_GEN = INV_GEN_PLACEHOLDER
# The table sumcheck's round polynomial arrives WHOLE, as a cubic at {0,1,g,g^2}:
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
# 4=public bytecode, 5=product; named COORD_KIND_* below), COORD_CONST (the const
# value, a product's or gcol's g^k, else 0), and the kappa SOURCE map
# (BLOCK_KAPPA_SRC/ADJ: 0=const adj, 1=log_mem, 2+t=tau_t). The block SHAPES are all
# reconstructed at runtime from the certified logs: kappa directly, the selector bits
# by pinned advice-decompositions.
# Coord kinds (COORD_TYPE / TERM_TYPE codes, mirroring leaf.rs::Coord):
COORD_KIND_CONST = 0
COORD_KIND_COL = 1
COORD_KIND_GCOL = 2
COORD_KIND_INDEX = 3
COORD_KIND_PUBLIC = 4
COORD_KIND_PROD = 5
# BLOCK_TABLE: the table a block's flush belongs to, or NO_TABLE for the framework
# blocks (boundary, memory seed/finalize, bytecode seed/finalize). It is
# also what marks a block as owned: an owned block's fingerprint is settled by the
# table sumcheck, off its table's column evaluations.
NO_TABLE = NO_TABLE_PLACEHOLDER
SIDE_BLOCK_START = SIDE_BLOCK_START_PLACEHOLDER
N_BLOCKS = N_BLOCKS_PLACEHOLDER
BLOCK_KAPPA_SRC = BLOCK_KAPPA_SRC_PLACEHOLDER
BLOCK_KAPPA_ADJ = BLOCK_KAPPA_ADJ_PLACEHOLDER
BLOCK_TABLE = BLOCK_TABLE_PLACEHOLDER
BLOCK_SIDE = BLOCK_SIDE_PLACEHOLDER
BLOCK_COORD_OFF = BLOCK_COORD_OFF_PLACEHOLDER
BLOCK_COORD_COUNT = BLOCK_COORD_COUNT_PLACEHOLDER
COORD_TYPE = COORD_TYPE_PLACEHOLDER
COORD_CONST = COORD_CONST_PLACEHOLDER
# Claim dedup: push/pull share their GKR point, so a column read by two blocks
# with the same kappa (across OR within the sides) is streamed and opened ONCE.
# Per coord: COORD_FRESH = 1 on the first occurrence (read the stream, fill
# pool slot COORD_CLAIM_SLOT), 0 on a duplicate (reuse that slot). The count
# side has its own point, so its claims never dedup against the pair's.
COORD_FRESH = COORD_FRESH_PLACEHOLDER
COORD_CLAIM_SLOT = COORD_CLAIM_SLOT_PLACEHOLDER
# A TABLE block's coordinates, flattened into TERMS: coord c is
# Σ_{j < COORD_TERM_COUNT[c]} term(COORD_TERM_OFF[c] + j), each term a
# TERM_TYPE kind over that table's LOCAL column indices TERM_COL_A/TERM_COL_B,
# scaled by TERM_CONST. Those coords raise no claim (the table sumcheck settles them),
# which is what lets one carry a value the row DERIVES from its columns: an
# XOR/MUL result, a DEREF store, a JUMP successor. A framework coord has no terms.
COORD_TERM_OFF = COORD_TERM_OFF_PLACEHOLDER
COORD_TERM_COUNT = COORD_TERM_COUNT_PLACEHOLDER
TERM_TYPE = TERM_TYPE_PLACEHOLDER
TERM_CONST = TERM_CONST_PLACEHOLDER
TERM_COL_A = TERM_COL_A_PLACEHOLDER
TERM_COL_B = TERM_COL_B_PLACEHOLDER
N_BUS_CLAIMS = N_BUS_CLAIMS_PLACEHOLDER
# index_mle factor constants: INDEX_MLE_FACTORS[i] = 1 + g^(2^i).
INDEX_MLE_FACTORS = INDEX_MLE_FACTORS_PLACEHOLDER
# Committed-coordinate claims (Col/GCol coords across all sides) and the
# deferred bytecode values (Public coords).
N_CLAIMS = N_CLAIMS_PLACEHOLDER
# The stacked bytecode: BYTECODE_COLS encoding columns, stacked along
# LOG2_BYTECODE_COLS selector bits into ONE multilinear. Push and pull share
# their GKR point, so the columns are opened ONCE (BYTECODE_COLS values).
# A bus tuple's coordinates index the 2^N_TUPLE_BITS fingerprint slots (doc sec:gp).
N_TUPLE_BITS = 4
N_TUPLE_SLOTS = 16
BYTECODE_COLS = BYTECODE_COLS_PLACEHOLDER
LOG2_BYTECODE_COLS = LOG2_BYTECODE_COLS_PLACEHOLDER
# Table sumcheck: the batch carries EVERY committed column of a table, because its bus
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
TABLE_XOR = 0
TABLE_MUL = 1
TABLE_SET = 2
TABLE_DEREF = 3
TABLE_JUMP = 4
TABLE_BLAKE3 = 5
TABLE_PACK64X2 = 6
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
SLOT_STRIDE_LOG = SLOT_STRIDE_LOG_PLACEHOLDER  # = K_LOG - LOG_PACKING (=8); the q_flock slot stride
# Phase E: the stacked mixed opening. The two ring-switch fronts
# (claim check in-circuit; the tensor transpose + eval_rs_eq DEFERRED); the
# gamma-combination of the two ring-switch claims and the N_CLAIMS pool claims.
# Phase E2: the WHIR opening over the stacked commitment, dispatched by
# the certified committed log-size m through match_range: the LIG_* tables
# below carry one row per (rate, m), with rate in 1..=4 and m in the
# supported committed-size interval,
# emitted from the SAME derive_profile/level_shapes the prover uses.
# Scalars index as TBL[m_idx]; per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl],
# where m_idx is the flattened (rate, size) configuration index;
# per-fold grind schedules with the LIG_MAX_TOTAL_FOLDS stride; the subspace
# vanishing constants with the LIG_MAX_VANISH_LEN stride. The eval_b terminal
# claim descriptors keep the fixed point-buffer and committed-column identities
# baked. Shape-dependent lengths are certified below; selectors are derived from
# the native largest-first committed-column placement reconstructed in-circuit.
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
# The committed size is dispatch-bounded: m <= LIG_MIN_LOG_SIZE + LIG_N_LOG_SIZES - 1,
# certified by the range check that picks the opening arm. So a placement offset
# (< 2^m) fits MAX_STACK_LOG bits, which is what the offset rows below decompose
# and certify; their YR_LOG_CAP extra cells cover the residual coordinates at and
# above m, which every reader zero-pins.
MAX_STACK_LOG = LIG_MIN_LOG_SIZE + LIG_N_LOG_SIZES - 1
COL_BITS_STRIDE = MAX_STACK_LOG + YR_LOG_CAP
LIG_N_LEVELS = LIG_N_LEVELS_PLACEHOLDER
LIG_YR_LEVEL = LIG_YR_LEVEL_PLACEHOLDER
LIG_YR_LOG_LEN = LIG_YR_LOG_LEN_PLACEHOLDER
LIG_YR_LEN = LIG_YR_LEN_PLACEHOLDER
LIG_TOTAL_FOLDS = LIG_TOTAL_FOLDS_PLACEHOLDER
LIG_MAX_QUERIES = LIG_MAX_QUERIES_PLACEHOLDER
LIG_MAX_SQUEEZES = LIG_MAX_SQUEEZES_PLACEHOLDER
LIG_MAX_INTERLEAVE = LIG_MAX_INTERLEAVE_PLACEHOLDER
LIG_POSITIONS_LEN = LIG_POSITIONS_LEN_PLACEHOLDER
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
# eval_b claim descriptors (fixed parts) + the qflock capacity stride.
# CLAIM_COMMITTED_COL maps each pooled logical claim to the compact index of the
# committed column it must open. Virtual BLAKE3 value claims map to QFLOCK.
# CLAIM_QFLOCK_SLOT_BITS contains the fixed packed-slot bits for every logical
# claim (zero for non-virtual claims), and QFLOCK_COMMITTED_COL identifies the
# ring-switch target.
# Which point buffer a pooled claim's x-part lives in (CLAIM_POINT_BUF codes):
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QFLOCK_RHO = 3
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_COMMITTED_COL = CLAIM_COMMITTED_COL_PLACEHOLDER
CLAIM_QFLOCK_SLOT_BITS = CLAIM_QFLOCK_SLOT_BITS_PLACEHOLDER
QFLOCK_COMMITTED_COL = QFLOCK_COMMITTED_COL_PLACEHOLDER
QFLOCK_VARS_CAP = QFLOCK_VARS_CAP_PLACEHOLDER
# Phase F: log rows of the bytecode blocks (the deferred bytecode points).
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER
# One sub-proof's deferred-claim region: one bytecode point and the Flock
# lincheck data (see verify_sub's defer_out layout).
DEFER_SIZE = DEFER_SIZE_PLACEHOLDER
# Aggregation: a RUNTIME number of sub-proofs of the same program; per-sub proof
# data arrives as hints. The seed sponge state after the two byte-string absorbs is baked
# (TRANSCRIPT_SEED), then the hinted sub statement + the inner PROGRAM DIGEST are bound.
# The seed is NOT baked into the guest: it rides the recursion's PUBLIC INPUT
# (the fs_seed hint folded into own_pi in main), so ONE compiled guest verifies
# proofs of any inner program of this VM — the outer statement fixes the whole
# proving environment (circuit family + program), via own_pi.
# The arity is hinted too, as g^nsub, and absorbed by both aggregation transcripts
# ahead of every variable-length sequence, so the outer statement fixes it as well.
# NSUB_BOUND (nsub < NSUB_BOUND) is the compile-time range-check bound that makes
# the count a bounded exponent, hence every sub-walk below terminate.
NSUB_BOUND = NSUB_BOUND_PLACEHOLDER
BYTECODE_VARS = BYTECODE_VARS_PLACEHOLDER
TRANSCRIPT_SEED_0 = TRANSCRIPT_SEED_0_PLACEHOLDER
TRANSCRIPT_SEED_1 = TRANSCRIPT_SEED_1_PLACEHOLDER
AGG_SEED_0 = AGG_SEED_0_PLACEHOLDER
AGG_SEED_1 = AGG_SEED_1_PLACEHOLDER
STATEMENT_SEED_0 = STATEMENT_SEED_0_PLACEHOLDER
STATEMENT_SEED_1 = STATEMENT_SEED_1_PLACEHOLDER

DS_SCALAR = 1
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
# A structural LOG (log_mem, tau_t, log_inv_rate) is announced as an integer word
# and raised to a g-power by decomposing it (g_power_of_word). Every one of them is
# below SIZE_BITS, so LOG_WORD_BITS bits are enough, and the reconstruction IS the
# bound: a larger announced log cannot reproduce itself from this many bits.
LOG_WORD_BITS = 6


@inline
def f192_from_limbs(c0, c1, c2):
    # Horner form saves one multiplication over c0 + c1*Y + c2*Y^2.
    return c0 + Y_TOWER * (c1 + Y_TOWER * c2)


@inline
def challenge_from_state(state):
    # `hash_state_to_words` with the second word dropped, written out because a
    # tuple-unpacking call is not inlinable and `squeeze` is @inline.
    # Exact lowering for state = [(d0,d1,0), (d2,d3,0)]:
    #   hints lo=[d0,d1], hi=[d2,d3]
    #   PACK64X2(lo[0],lo[1]) -> state[0]  (in-place equality check)
    #   PACK64X2(hi[0],hi[1]) -> state[1]  (in-place equality check)
    #   return d0 + d1*Y + d2*Y^2
    # Write-once memory makes both PACK rows assertions, so all four digest
    # lanes are proven to be in K; d3 is constrained but not used.
    lo = StackBuf(2)
    hi = StackBuf(2)
    hint_f192_limbs(lo, state[0])
    hint_f192_limbs(hi, state[1])
    pack64x2_into(lo[0], lo[1], state[0])
    pack64x2_into(hi[0], hi[1], state[1])
    # state[0] IS lo[0] + Y·lo[1], pinned by the pack just above, so the low two
    # lanes need no reassembly: only the top lane is weighted in.
    return state[0] + Y_TOWER * Y_TOWER * hi[0]


@inline
def sponge_compress(state, scalar, tail, out):
    # Serialize scalar.c0, scalar.c1, scalar.c2, tail as two canonical cells.
    # Only the two LOW limbs are advice: PACK64X2 proves they are in K and makes
    # block[0] their packing lo + Y·hi, which leaves the top limb determined,
    # (scalar + block[0])·Y⁻², with the second pack proving that is in K as well.
    # Three limbs in K that weight to scalar ARE its limbs, the tower
    # representation being unique, so the serialization is canonical with no
    # equality check to make and one less hint to distrust.
    lo = StackBuf(2)
    hint_f192_limbs(lo, scalar)
    block = StackBuf(2)
    pack64x2_into(lo[0], lo[1], block[0])
    top = (scalar + block[0]) * (Y_INV * Y_INV)
    pack64x2_into(top, tail, block[1])
    blake3(state, block, out)
    return


def canonical_cell(word, out_cell):
    # Prove a transcript word is a canonical BLAKE3 cell (d, d', 0): PACK64X2
    # writes the pack of two hinted K limbs, and the equality pins the word to
    # it, so a nonzero top lane cannot slip through.
    limbs = StackBuf(3)
    hint_f192_limbs(limbs, word)
    pack64x2_into(limbs[0], limbs[1], out_cell)
    assert word == out_cell


def squeeze_step(state_0, state_1):
    # Non-inlined sponge ratchet exposing BOTH output words (challenge and the
    # next state), so a query-squeeze loop can chain the state through a heap
    # buffer. Returns (challenge, next_state_0, next_state_1).
    state = [state_0, state_1]
    next_state, challenge = squeeze(state)
    return challenge, next_state[0], next_state[1]


def decode_query_bits(v, positions_out, bit_ptrs_out, depth: Const):
    # The squeezed word's bits are advice-decomposed HERE, boolean-constrained,
    # and tied back by reconstruction; each depth-bit group also becomes a query
    # position (little-endian), with a pointer to its bit run (the Merkle
    # direction bits). Each field word packs FIELD_BITS // depth positions.
    per_word = FIELD_BITS // depth
    bits_ptr = HeapBuf(GEN ** FIELD_BITS)
    hint_decompose_bits(bits_ptr, v, FIELD_BITS)
    acc = 0
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
                p_lo += t * COORD_BASIS[b]
            else:
                p_hi += t * COORD_BASIS[b - cut]
        # position = p_lo + 2^cut * p_hi: multiplying by X^cut concatenates the
        # two runs, since both degrees stay below 64.
        if cut // depth == 0:  # `cut < depth`: this group straddles the boundary
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            acc += COORD_BASIS[base_bit] * p_lo + COORD_BASIS[base_bit + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            acc += COORD_BASIS[base_bit] * p_lo
        bit_ptrs_out[GEN ** j] = bits_ptr * GEN ** base_bit
    for i in unroll(per_word * depth, FIELD_BITS):
        t = bits_ptr[GEN ** i]
        bits_ptr[GEN ** i] = t * t
        acc += t * COORD_BASIS[i]
    assert acc == v
    return


def grind_check(state_0, state_1, nonce, nbits_g):
    # WHIR fold/query grinding: digest = H(H(state, (0, POW)), (nonce, POW)), whose
    # low nbits (nbits_g = g^nbits) must be zero. The PoW window of
    # transcript::pow_bits_ok is `digest.0 & ((1 << bits) - 1)`, nbits < 64, so it
    # lives entirely in the digest's FIRST 64-bit lane: one PACK64X2 pins the
    # digest cell's two lanes (both proven to be in K, the third zero), and only
    # that lane's BASE_FIELD_BITS coordinates are advice-decomposed and verified
    # (booleanity + reconstruction), not all FIELD_BITS of the cell. The caller
    # absorbs the full field nonce afterwards. The honest prover searches the
    # deterministic u64 subset, while verification permits the full field: each
    # candidate still costs one hash and succeeds with probability 2^-bits.
    if nbits_g == GEN ** 0:
        assert nonce == 0  # native canonical zero-work nonce
    st = [state_0, state_1]
    base = StackBuf(2)
    sponge_compress(st, f192_from_limbs(0, 0, DS_POW), 0, base)
    out = StackBuf(2)
    # nonce's three F64 limbs followed by DS_POW, exactly as the native sponge.
    sponge_compress(base, nonce, DS_POW, out)
    lanes = StackBuf(2)
    hint_f192_limbs(lanes, out[0])
    pack64x2_into(lanes[0], lanes[1], out[0])  # out[0] == (lanes[0], lanes[1], 0), both in K
    lane_bits = HeapBuf(GEN ** BASE_FIELD_BITS)
    hint_decompose_bits(lane_bits, lanes[0], BASE_FIELD_BITS)
    acc = 0
    for i in unroll(0, BASE_FIELD_BITS):
        b = lane_bits[GEN ** i]
        # Booleanity as a write-once pin: the cell already holds b, so storing b*b
        # back IS the assert, one instruction shorter (as in decode_query_bits).
        lane_bits[GEN ** i] = b * b
        acc += b * COORD_BASIS[i]  # bit i contributes the i-th coordinate basis vector
    assert acc == lanes[0]  # the bits ARE the lane's coordinates, so the pins below bind it
    for xb in mul_range(1, nbits_g):
        assert lane_bits[xb] == 0
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
    return g_log, exp_prod


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
    g_log, g_bits_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits)
    assert g_bits_value == g_N  # the hinted bits decode to N
    return g_log


@inline
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
        parent = StackBuf(2)
        blake3(left, right, parent)
        node_0 = parent[0]
        node_1 = parent[1]
    return node_0, node_1


@inline
def quartic_eval_from_eq(claim, eq_point, difference, c2, c3, c4, challenge):
    c0 = claim + eq_point * difference
    c1 = difference + c2 + c3 + c4
    return c0 + challenge * (c1 + challenge * (c2 + challenge * (c3 + challenge * c4)))


def sumcheck_round5(state_0, state_1, msg_cursor, claim, prev_challenge):
    fs = [state_0, state_1]
    fs, difference, msg_cursor = fs_next(fs, msg_cursor)
    fs, c2, msg_cursor = fs_next(fs, msg_cursor)
    fs, c3, msg_cursor = fs_next(fs, msg_cursor)
    fs, c4, msg_cursor = fs_next(fs, msg_cursor)
    fs, round_challenge = squeeze(fs)
    new_claim = quartic_eval_from_eq(claim, prev_challenge, difference, c2, c3, c4, round_challenge)
    return fs[0], fs[1], msg_cursor, new_claim, round_challenge


def sumcheck_round4(state_0, state_1, msg_cursor, claim):
    # One PLAIN sumcheck round. The prover sends the round polynomial itself at
    # {0, 1, g, g^2}, so the verifier does only the two textbook steps: check
    # h(0) + h(1) == claim, then evaluate h at the challenge through the baked
    # Lagrange basis. Nothing is reapplied: no eq factor, no separate term for the
    # tables still waiting, and the eq point is not read here at all.
    fs = [state_0, state_1]
    fs, h0, msg_cursor = fs_next(fs, msg_cursor)
    fs, h1, msg_cursor = fs_next(fs, msg_cursor)
    fs, h2, msg_cursor = fs_next(fs, msg_cursor)
    fs, h3, msg_cursor = fs_next(fs, msg_cursor)
    assert h0 + h1 == claim
    fs, y = squeeze(fs)
    l0 = (y + 1) * (y + GEN) * (y + GEN * GEN) * LAG4_INV_0
    l1 = y * (y + GEN) * (y + GEN * GEN) * LAG4_INV_1
    l2 = y * (y + 1) * (y + GEN * GEN) * LAG4_INV_2
    l3 = y * (y + 1) * (y + GEN) * LAG4_INV_3
    return fs[0], fs[1], msg_cursor, h0 * l0 + h1 * l1 + h2 * l2 + h3 * l3, y


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
    nb = StackBuf(2)
    sponge_compress(state, x, DS_SCALAR, nb)
    return nb



@inline
def fs_next(state, cursor):
    # Fetch + observe + advance, in one act: read the word under `cursor`, fold it
    # into the sponge, and hand back the successor state, the word, AND the cursor
    # stepped one word on. Reading and absorbing are inseparable here, so no
    # proof-stream word can enter the computation unbound. This is the soundness invariant
    # the whole guest rests on. All three returns alias into the caller at zero
    # cost (state a StackBuf run, cursor a folded g-address), so the usual walk is
    # just `fs, x, cursor = fs_next(fs, cursor)` with no manual cursor arithmetic.
    x = cursor[GEN ** 0]
    nb = obs(state, x)
    return nb, x, cursor * GEN

@inline
def absorb_nonce(state, x):
    # Full-field grinding nonce absorb: [x.c0, x.c1, x.c2, DS_POW].
    nb = StackBuf(2)
    sponge_compress(state, x, DS_POW, nb)
    return nb


@inline
def squeeze(state):
    # Ratchet: the canonical 128+128 digest is the new state; its first three
    # K lanes are reassembled as the F192 challenge.
    nb = StackBuf(2)
    sponge_compress(state, f192_from_limbs(0, 0, DS_SQ), 0, nb)
    challenge = challenge_from_state(nb)
    return nb, challenge


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


def open_stacked(m_idx: Const, fs0, fs1, target, commit_root_0, commit_root_1, cursor):
    # The stacked WHIR opening. m_idx is the flattened (rate, committed
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
    #   4. squeeze the level's one batching challenge, then per query: hash
    #      the leaf row (blake3 chain), accumulate the lam-weighted row dot
    #      against the fold eq weights, and verify the Merkle authentication
    #      path against the bound root (verify_merkle_path);
    #   5. read the level's intro message and fold every claim of the level
    #      (its OOD claims, then the query sum) into the running target with
    #      powers of lam.
    # Then finish the tail sumcheck and evaluate every transparent basis once
    # at its terminal point; the final-message MLE enters as one multiplier.
    #
    # Returns (sumcheck_target, fold_challenges, final_msg, residual_total,
    # yr_log_n_g = g^yr_log_n, yr_pad_g = g^(YR_LOG_CAP - yr_log_n),
    # fold_cap_g = g^lenris), tail_challenges, and yr_at_tail.
    # yr_log_n_g/yr_pad_g let the terminal zero-pin
    # residual-slot coordinates beyond final_msg's 2^yr_log_n cells (positions
    # yr_log_n .. YR_LOG_CAP-1); fold_cap_g is the certified total fold count
    # the terminal pins its hinted claim lengths against.
    fs = [fs0, fs1]

    # The K opener binds the initial Merkle root as its two F192 scalars, not as
    # a byte string, and every digest uses ONE 128/128 encoding, so those scalars
    # are exactly the root's two cells. Level roots are likewise scalar-observed.
    fs = obs(fs, target)
    fs = obs(fs, commit_root_0)
    fs = obs(fs, commit_root_1)

    # The opening's scalars (sumcheck messages, level roots, nonces, final
    # message) ride the SHARED stream: msg_cursor is just the main stream
    # cursor, walked on in protocol order.
    msg_cursor = cursor
    fs, msg_h0, msg_cursor = fs_next(fs, msg_cursor)
    fs, msg_h1, msg_cursor = fs_next(fs, msg_cursor)
    fs, msg_hinf, msg_cursor = fs_next(fs, msg_cursor)
    assert msg_h0 + msg_h1 == target
    round_quad_c = msg_h0
    round_quad_b = msg_h0 + msg_h1 + msg_hinf
    round_quad_a = msg_hinf
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
    # Level roots by level: slot 0 is the commitment root (bound above), the rest
    # are filled as each root is read off the stream. Every query then checks its
    # walk with ONE heap store per digest cell, the write-once equality, with no
    # level-0 special case.
    level_roots_0 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    level_roots_1 = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    level_roots_0[GEN ** 0] = commit_root_0
    level_roots_1[GEN ** 0] = commit_root_1
    # ...and guest-filled accumulators (one slot per fold / per level / per query):
    fold_challenges = HeapBuf(GEN ** (LIG_TOTAL_FOLDS[m_idx]))
    level_betas = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx]))
    query_weights = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_QUERIES[m_idx]))
    query_positions = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    query_bit_ptrs = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    # Explicit OOD claims bind every recursive Johnson-list commitment. L0
    # needs none: the opening claim itself is its post-commit binding value.
    # An OOD claim is read before its level's query positions but batched after
    # them (one challenge per level), so its value and intro message wait here.
    ood_z = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES * LIG_LOG_MSG_COLS_CAP))
    ood_betas = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES))
    ood_ys = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES))
    ood_h0s = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES))
    ood_h1s = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES))
    ood_hinfs = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_MAX_OOD_SAMPLES))

    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        for j in unroll(0, LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl]):
            fold_idx = LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl] + j
            if LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx] != 0:
                nonce_v = msg_cursor[GEN ** 0]  # raw transport word: bound by the DS_POW absorb below
                msg_cursor = msg_cursor * GEN
                grind_check(fs[0], fs[1], nonce_v, GEN ** LIG_FOLD_GRIND_BITS[m_idx * LIG_MAX_TOTAL_FOLDS + fold_idx])
                fs = absorb_nonce(fs, nonce_v)
            fs, fold_challenge = squeeze(fs)
            fold_challenges[GEN ** fold_idx] = fold_challenge
            sumcheck_target = (round_quad_a * fold_challenge + round_quad_b) * fold_challenge + round_quad_c  # evaluate this level's folded quadratic at the fold challenge
            fs, msg_h0, msg_cursor = fs_next(fs, msg_cursor)  # the round polynomial at 0, 1, infinity
            fs, msg_h1, msg_cursor = fs_next(fs, msg_cursor)
            fs, msg_hinf, msg_cursor = fs_next(fs, msg_cursor)
            assert msg_h0 + msg_h1 == sumcheck_target  # vanilla sumcheck: the round must answer the running claim
            round_quad_c = msg_h0
            round_quad_b = msg_h0 + msg_h1 + msg_hinf
            round_quad_a = msg_hinf

        if lvl == LIG_YR_LEVEL[m_idx]:
            for iy in unroll(0, LIG_YR_LEN[m_idx]):
                fs, yv, msg_cursor = fs_next(fs, msg_cursor)
                final_msg[GEN ** iy] = yv
        else:
            fs, next_root_a, msg_cursor = fs_next(fs, msg_cursor)
            fs, next_root_b, msg_cursor = fs_next(fs, msg_cursor)
            next_root = StackBuf(2)
            canonical_cell(next_root_a, next_root[0])
            canonical_cell(next_root_b, next_root[1])
            level_roots_0[GEN ** (lvl + 1)] = next_root[0]
            level_roots_1[GEN ** (lvl + 1)] = next_root[1]
            # OOD binding for the newly observed level-(lvl+1) commitment.
            # The random point has the just-folded witness dimension, namely
            # this level's message-column dimension.
            for os in unroll(0, LIG_OOD_SAMPLES[m_idx * LIG_MAX_LEVELS + lvl + 1]):
                oz = ood_z * GEN ** (((lvl + 1) * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
                for t in unroll(0, LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + lvl]):
                    fs, oz_challenge = squeeze(fs)
                    oz[GEN ** t] = oz_challenge
                fs, ood_y, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_h0, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_h1, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_hinf, msg_cursor = fs_next(fs, msg_cursor)
                assert ood_h0 + ood_h1 == ood_y
                ood_ys[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)] = ood_y
                ood_h0s[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)] = ood_h0
                ood_h1s[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)] = ood_h1
                ood_hinfs[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)] = ood_hinf
        q_nonce = msg_cursor[GEN ** 0]  # raw transport word: bound by the DS_POW absorb below
        msg_cursor = msg_cursor * GEN
        if LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl] != 0:
            grind_check(fs[0], fs[1], q_nonce, GEN ** LIG_QUERY_GRIND_BITS[m_idx * LIG_MAX_LEVELS + lvl])
        else:
            assert q_nonce == 0
        fs = absorb_nonce(fs, q_nonce)

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

        # One batching challenge for the level, drawn once every claim it
        # batches is fixed: its OOD claims above and these query positions.
        # Claim tau of the level is weighted lam^tau, the running claim
        # keeping lam^0 (Annex B, Protocol 1 step 1): query i is claim
        # n_ood + 1 + i, so its weight splits into lam^i here and the level
        # scalar lam^(n_ood+1) below.
        fs, lam = squeeze(fs)
        lam_pow = 1
        for i in unroll(0, LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            query_weights[GEN ** (lvl * LIG_MAX_QUERIES[m_idx] + i)] = lam_pow
            lam_pow = lam_pow * lam
        row_eq_weights = HeapBuf(GEN ** (LIG_MAX_INTERLEAVE[m_idx]))
        for i in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
            row_eq_weights[GEN ** i] = eq_weight(fold_challenges * GEN ** LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + lvl], LIG_FOLDS[m_idx * LIG_MAX_LEVELS + lvl], i, 0)

        query_sum_chain = HeapBuf(GEN ** (LIG_MAX_QUERIES[m_idx] + 1))
        query_sum_chain[GEN ** 0] = 0
        for xe in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            if lvl == 0:
                row_base = xe ** LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]
            else:
                row_base = xe ** (3 * LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl])
            row_ptr = merkle_leaf_rows * GEN ** LIG_ROWS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * row_base
            row_dot = 0
            packed_row = StackBuf(LIG_PACKED_ROW_CAP)
            if lvl == 0:
                # Level-0 rows are base-field F64, embedded one-per word. Pack
                # the lanes into a contiguous run of canonical 128-bit cells for
                # the standard leaf hash; the dot consumes the individual lanes.
                # PACK64X2 reads both source cells through the memory bus as
                # `(lo, 0, 0)`, so the packs also prove every hinted lane is
                # genuinely F64 before it enters the hash or row_dot.
                for jb in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl] // 4):
                    e0 = row_ptr[GEN ** (4 * jb)]
                    e1 = row_ptr[GEN ** (4 * jb + 1)]
                    e2 = row_ptr[GEN ** (4 * jb + 2)]
                    e3 = row_ptr[GEN ** (4 * jb + 3)]
                    pack64x2_into(e0, e1, packed_row[2 * jb])
                    pack64x2_into(e2, e3, packed_row[2 * jb + 1])
                    row_dot += e0 * row_eq_weights[GEN ** (4 * jb)] + e1 * row_eq_weights[GEN ** (4 * jb + 1)] + e2 * row_eq_weights[GEN ** (4 * jb + 2)] + e3 * row_eq_weights[GEN ** (4 * jb + 3)]
            else:
                # Higher-level F192 rows arrive as flat F64 tower limbs (three
                # per word); constrain every serialized limb before reassembly
                # and pack them into the contiguous 24-byte-per-word byte image
                # the committed leaf hashes.
                # Load each serialized limb ONCE into frame cells, then read the
                # words back off the PACKED cells: a pack holds
                # `lane(2k) + Y*lane(2k+1)` exactly, so word w (limbs 3w..3w+2)
                # is one multiply-add away from the pack that covers its even
                # limb pair. The old form re-read all three limbs per word and
                # rebuilt it with two multiplies.
                lanes = StackBuf(LIG_PACKED_ROW_CAP)  # >= 3 limbs per word for every candidate
                for jl in unroll(0, 3 * LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
                    lanes[jl] = row_ptr[GEN ** jl]
                for jb in unroll(0, LIG_LEAF_PAIRS[m_idx * LIG_MAX_LEVELS + lvl]):
                    pack64x2_into(lanes[4 * jb], lanes[4 * jb + 1], packed_row[2 * jb])
                    pack64x2_into(lanes[4 * jb + 2], lanes[4 * jb + 3], packed_row[2 * jb + 1])
                for jw in unroll(0, LIG_INTERLEAVE[m_idx * LIG_MAX_LEVELS + lvl]):
                    if 3 * jw % 2 == 0:
                        # limbs (3w, 3w+1) are a pack; add Y^2 * limb(3w+2).
                        row_word = packed_row[3 * jw // 2] + Y_TOWER * Y_TOWER * lanes[3 * jw + 2]
                    else:
                        # limbs (3w+1, 3w+2) are a pack; shift it by Y and add limb(3w).
                        row_word = lanes[3 * jw] + Y_TOWER * packed_row[(3 * jw + 1) // 2]
                    row_dot += row_word * row_eq_weights[GEN ** jw]
            # Standard BLAKE3 of the packed row (a power of two of full 64-byte
            # blocks, within one 1024-byte chunk).
            leaf_hash_state = StackBuf(2)
            blake3(packed_row[0:2], packed_row[2:4], leaf_hash_state, step=0, end=1 // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl], root=1 // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl])
            for jb in unroll(1, LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl]):
                leaf_digest = StackBuf(2)
                blake3(packed_row[4 * jb:4 * jb + 2], packed_row[4 * jb + 2:4 * jb + 4], leaf_digest, cv=leaf_hash_state, step=jb, end=(jb + 1) // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl], root=(jb + 1) // LIG_LEAF_BLOCKS[m_idx * LIG_MAX_LEVELS + lvl])
                leaf_hash_state = leaf_digest
            node_0 = leaf_hash_state[0]
            node_1 = leaf_hash_state[1]
            query_sum_chain[xe * GEN] = query_sum_chain[xe] + query_weights[GEN ** (lvl * LIG_MAX_QUERIES[m_idx]) * xe] * row_dot
            direction_bits = query_bit_ptrs[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xe]
            path_base = xe ** (2 * LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])
            path_ptr = merkle_paths * GEN ** LIG_PATHS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * path_base
            root_0, root_1 = verify_merkle_path(node_0, node_1, path_ptr, direction_bits, LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl])  # walk the query's Merkle path to the level root
            # A heap store IS the equality assert here (`DerefMode::Cell` unifies
            # the two cells, and the slot holds this level's bound root already),
            # at one instruction instead of three.
            level_roots_0[GEN ** lvl] = root_0
            level_roots_1[GEN ** lvl] = root_1
        level_query_sum = query_sum_chain[GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]]

        # Every level, including the last, ties its commitment in through an
        # intro message. The level's claims then enter the running one with
        # powers of `lam`: the OOD claims held above first, then this query
        # batch.
        fs, intro_h0, msg_cursor = fs_next(fs, msg_cursor)
        fs, intro_h1, msg_cursor = fs_next(fs, msg_cursor)
        fs, intro_hinf, msg_cursor = fs_next(fs, msg_cursor)
        assert intro_h0 + intro_h1 == level_query_sum
        if lvl == LIG_YR_LEVEL[m_idx]:
            beta_lvl = lam  # no OOD claim at the last level: no new oracle
        else:
            ood_scalar = lam
            for os in unroll(0, LIG_OOD_SAMPLES[m_idx * LIG_MAX_LEVELS + lvl + 1]):
                ood_y = ood_ys[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)]
                ood_h0 = ood_h0s[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)]
                ood_h1 = ood_h1s[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)]
                ood_hinf = ood_hinfs[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)]
                ood_betas[GEN ** ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os)] = ood_scalar
                round_quad_c += ood_scalar * ood_h0
                round_quad_b += ood_scalar * (ood_h0 + ood_h1 + ood_hinf)
                round_quad_a += ood_scalar * ood_hinf
                sumcheck_target += ood_scalar * ood_y
                ood_scalar = ood_scalar * lam
            beta_lvl = ood_scalar
        level_betas[GEN ** lvl] = beta_lvl
        round_quad_c += beta_lvl * intro_h0
        round_quad_b += beta_lvl * (intro_h0 + intro_h1 + intro_hinf)
        round_quad_a += beta_lvl * intro_hinf
        sumcheck_target += beta_lvl * level_query_sum

    # ---- finish the sumcheck over the tail coordinates ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, LIG_YR_LOG_LEN[m_idx] - 1):
        fs, tail_c = squeeze(fs)
        tail_challenges[GEN ** j] = tail_c
        sumcheck_target = round_quad_c + tail_c * round_quad_b + tail_c * tail_c * round_quad_a
        fs, msg_h0, msg_cursor = fs_next(fs, msg_cursor)
        fs, msg_h1, msg_cursor = fs_next(fs, msg_cursor)
        fs, msg_hinf, msg_cursor = fs_next(fs, msg_cursor)
        assert msg_h0 + msg_h1 == sumcheck_target
        round_quad_c = msg_h0
        round_quad_b = msg_h0 + msg_h1 + msg_hinf
        round_quad_a = msg_hinf
    # The closing round sends no following message.
    fs, tail_last = squeeze(fs)
    tail_challenges[GEN ** (LIG_YR_LOG_LEN[m_idx] - 1)] = tail_last
    sumcheck_target = round_quad_c + tail_last * round_quad_b + tail_last * tail_last * round_quad_a
    for j in unroll(LIG_YR_LOG_LEN[m_idx], YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    tail_w = StackBuf(2 * YR_LOG_CAP)
    for j in unroll(0, LIG_YR_LOG_LEN[m_idx]):
        tail_w[2 * j] = 1 + tail_challenges[GEN ** j]
        tail_w[2 * j + 1] = tail_challenges[GEN ** j]
    yr_at_tail = fold_final_msg(final_msg, tail_w, 0, LIG_YR_LOG_LEN[m_idx])

    # ---- per-level induced bases at the single terminal point ----
    # Every query of a level runs the SAME product shape over the level's
    # message-column coordinates, and only the novel-basis chain (the query
    # position's subspace-vanishing walk) differs. The coordinate's factor
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # so its two coefficients depend on the challenge and the baked vanishing
    # inverse alone: hoist them out of the query loop (one row per level, the
    # fold coords then the tail coords), and each query multiplies in one
    # multiply-add per coordinate with no stored basis vector at all.
    basis_a = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_LOG_MSG_COLS_CAP))
    basis_b = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] * LIG_LOG_MSG_COLS_CAP))
    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        for t in unroll(0, LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl]):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t)]
            basis_a[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] = 1 + fold_c
            basis_b[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] = fold_c * LIG_VANISH_INVS[m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t]
        for j in unroll(0, LIG_YR_LOG_LEN[m_idx]):
            tail_c = tail_challenges[GEN ** j]
            basis_a[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl] + j)] = 1 + tail_c
            basis_b[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl] + j)] = tail_c * LIG_VANISH_INVS[m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + LIG_RESIDUAL_PREFIX_LEN[m_idx * LIG_MAX_LEVELS + lvl] + j]
    inner_chain = HeapBuf(GEN ** (LIG_N_LEVELS[m_idx] + 1))
    inner_chain[GEN ** 0] = 0
    for lvl in unroll(0, LIG_N_LEVELS[m_idx]):
        residual_chain = HeapBuf(GEN ** (LIG_MAX_QUERIES[m_idx] + 1))
        residual_chain[GEN ** 0] = 0
        for xr in mul_range(1, GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]):
            basis_chain = query_positions[GEN ** LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl] * xr]
            prefix_eq = basis_a[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP)] + basis_b[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP)] * basis_chain
            for t in unroll(1, LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + lvl]):
                basis_chain *= (basis_chain + LIG_VANISH_VALS[m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[m_idx * LIG_MAX_LEVELS + lvl] + t - 1])  # subspace-vanishing recurrence for the novel-basis point
                prefix_eq *= basis_a[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] + basis_b[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] * basis_chain
            residual_chain[xr * GEN] = residual_chain[xr] + query_weights[GEN ** (lvl * LIG_MAX_QUERIES[m_idx]) * xr] * prefix_eq
        inner_chain[GEN ** (lvl + 1)] = inner_chain[GEN ** lvl] + level_betas[GEN ** lvl] * residual_chain[GEN ** LIG_QUERIES[m_idx * LIG_MAX_LEVELS + lvl]]  # accumulate beta_lvl * (per-level residual sum) into the grand residual

    # Explicit OOD eq bases at the same terminal point.
    ood_inner = 0
    for ood_lvl in unroll(1, LIG_N_LEVELS[m_idx]):
        z_len = LIG_LOG_MSG_COLS[m_idx * LIG_MAX_LEVELS + ood_lvl - 1]
        z_folded = z_len - LIG_YR_LOG_LEN[m_idx]
        ris_start = LIG_FOLDS_OFF[m_idx * LIG_MAX_LEVELS + ood_lvl]
        for os in unroll(0, LIG_OOD_SAMPLES[m_idx * LIG_MAX_LEVELS + ood_lvl]):
            oz = ood_z * GEN ** ((ood_lvl * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
            scalar = ood_betas[GEN ** (ood_lvl * LIG_MAX_OOD_SAMPLES + os)]
            for t in unroll(0, z_folded):
                scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
            for t in unroll(0, LIG_YR_LOG_LEN[m_idx]):
                zt = oz[GEN ** (z_folded + t)]
                scalar *= (1 + zt + tail_challenges[GEN ** t])
            ood_inner += scalar
    return sumcheck_target, fold_challenges, inner_chain[GEN ** LIG_N_LEVELS[m_idx]] + ood_inner, GEN ** LIG_YR_LOG_LEN[m_idx], GEN ** (YR_LOG_CAP - LIG_YR_LOG_LEN[m_idx]), GEN ** LIG_TOTAL_FOLDS[m_idx], tail_challenges, yr_at_tail


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


def verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out):
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
    #      (announced as logs: tau per table, log_mem);
    #   3. bind the commitment root; ONE RLC-batched GKR for all three trees (count padded
    #      to the pair's depth) at runtime depth, ONE shared point zeta;
    #   4. derive the block kappas, certify the GKR side depths; balance check (the two
    #      roots outright); 3x leaf decomposition, DERIVING
    #      each side's table share from its GKR claim (pooling the
    #      committed-coordinate claims); the stacked-bytecode reduction (deferred);
    #   5. ONE table sumcheck for all seven tables, n = max_t tau_t rounds at the
    #      shared point zeta, target derived from the leaf claims (sumcheck_round4);
    #   6. public-input claim + BLAKE3 pin claims (telescoped prefix MLE);
    #   7. flock reduction: univariate-skip zerocheck + lincheck (matrix
    #      evaluation deferred);
    #   8. ring-switch fronts (shared linear map, transpose in-circuit);
    #   9. gamma-combine everything, certify the committed size m, dispatch
    #      the stacked WHIR opening (open_stacked), and assert its
    #      eval_b terminal;
    #  10. export the deferred-claim region for the aggregation.
    # Claim pool: values of every committed-coordinate claim, in decompose order
    # (their points are the GKR ζ's, resolvable from the baked block structure).
    # `1 + g^(2^k)` per bit position, in FRAME cells: the bit-ladder rebuilds
    # below (placement offsets, the bus depth) each need this factor once per
    # bit, and a StackBuf entry is an instruction operand, where the g_squares
    # HeapBuf costs a load and an add every time.
    gsq_plus = StackBuf(SIZE_BITS)
    for k in unroll(0, SIZE_BITS):
        gsq_plus[k] = 1 + g_squares[GEN ** k]
    claim_pool = HeapBuf(N_CLAIMS)
    # certified low dimension (cplen) per pooled claim, filled as the pool is
    # built (from the in-scope certified kappa/tau); the terminal pins each
    # claim's hinted lengths against it.
    claim_cplen_g = HeapBuf(N_CLAIMS)
    # The ONE shared GKR leaf point (all three trees reduce to it).

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    fs = [TRANSCRIPT_SEED_0, TRANSCRIPT_SEED_1]
    fs = obs(fs, seed_0)  # the FS seed: H(flock circuit family, inner program
    fs = obs(fs, seed_1)  # bytecode, ...) — from the recursion's public input
    fs = obs(fs, pi_0)   # bind the sub-proof's statement (its public input)
    fs = obs(fs, pi_1)
    stream = HeapBuf(STREAM_CAP)
    hint_witness(stream[0:STREAM_CAP], "stream")
    cursor = stream  # the proof stream is replayed word by word; cursor walks it (advance = * g)

    # ---- announced layout and PCS rate (observed, then certified) ----
    sizes = StackBuf(N_TABLES + 1)
    for i in unroll(0, N_TABLES + 1):
        fs, x, cursor = fs_next(fs, cursor)
        sizes[i] = x
    fs, log_inv_rate, cursor = fs_next(fs, cursor)
    g_log_inv_rate = g_power_of_word(log_inv_rate, g_squares, LOG_WORD_BITS)
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
    g_log_mem = g_power_of_word(sizes[0], g_squares, LOG_WORD_BITS)
    assert log(g_log_mem) < COUNT_BITS
    mem_floor_slack = g_log_mem / GEN ** MIN_LOG_MEM
    assert log(mem_floor_slack) < COUNT_BITS  # native MIN_LOG_MEM <= log_mem
    dims_g[GEN ** 0] = g_log_mem
    # Each tau is announced AS a log, like log_mem: g^tau from the word's
    # advice-decomposed bits, with no hint and no g^j -> j lookup. Every table's rows
    # are real rows (the prover's fill blocks bring each count up to a power of two),
    # so a height is all there is to announce, and the log2_ceil gadget
    # that used to turn a count into one is gone from here.
    for t in unroll(0, N_TABLES):
        g_tau = g_power_of_word(sizes[t + 1], g_squares, LOG_WORD_BITS)
        assert log(g_tau) < COUNT_BITS
        # A table's floor: flock sizes its BLAKE3 argument to at least 2^3 instances.
        assert log(g_tau / GEN ** FLOORS[t]) < COUNT_BITS
        dims_g[GEN ** (t + 1)] = g_tau
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

    # ---- bus challenges (F192 provides the soundness margin without grinding) ----
    # A tuple is fingerprinted multilinearly: slot x weighs eq(alphas, x), so a leaf
    # factor has total degree N_TUPLE_BITS in the challenges and the aligned bytecode
    # polynomial is read off at the challenge vector itself (doc sec:gp, sec:e2e-bc).
    bus_alpha = HeapBuf(N_TUPLE_BITS)
    for t in unroll(0, N_TUPLE_BITS):
        fs, av = squeeze(fs)
        bus_alpha[GEN ** t] = av
    fp_w = HeapBuf(N_TUPLE_SLOTS)
    for x in unroll(0, N_TUPLE_SLOTS):
        fp_w[GEN ** x] = eq_weight(bus_alpha, N_TUPLE_BITS, x, 0)
    fs, gamma = squeeze(fs)

    # ---- ONE GKR grand product: push, pull, and count RLC-batched ----
    # Push and pull have equal depth (matched blocks) and the count tree is
    # padded with identity leaves up to it (product unchanged), so a single
    # sumcheck serves all three trees. Radix four contracts two binary levels
    # per layer; after checking the combined product identity, a fresh λ pins
    # the individual values. All three trees reduce to one shared point zeta.
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
    gkr_pts = HeapBuf(GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    fs, root_push, cursor = fs_next(fs, cursor)
    fs, root_pull, cursor = fs_next(fs, cursor)
    fs, root_count, cursor = fs_next(fs, cursor)
    fs, initial_layer_lambda = squeeze(fs)
    gkr_layer_lambda[GEN ** 0] = initial_layer_lambda  # λ over the three roots
    gkr_layer_fs0[GEN ** 0] = fs[0]
    gkr_layer_fs1[GEN ** 0] = fs[1]
    gkr_layer_cursor[GEN ** 0] = cursor
    gkr_layer_claim[GEN ** 0] = root_push
    gkr_layer_claim_b[GEN ** 0] = root_pull
    gkr_layer_claim_c[GEN ** 0] = root_count
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
        final_pos = round_pos * x_layer
        tail_fs = [gkr_round_fs0[final_pos], gkr_round_fs1[final_pos]]
        tcur = gkr_round_cursor[final_pos]
        tclaim = gkr_round_claim[final_pos]
        tail_fs, e0_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_push, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_pull, tcur = fs_next(tail_fs, tcur)
        tail_fs, e0_count, tcur = fs_next(tail_fs, tcur)
        tail_fs, e1_count, tcur = fs_next(tail_fs, tcur)
        assert tclaim == e0_push * e1_push + lam * (e0_pull * e1_pull + lam * (e0_count * e1_count))
        tail_fs, layer_challenge = squeeze(tail_fs)
        nextrow[GEN ** 0] = layer_challenge
        xln = x_layer * GEN
        gkr_layer_claim[xln] = e0_push + layer_challenge * (e0_push + e1_push)
        gkr_layer_claim_b[xln] = e0_pull + layer_challenge * (e0_pull + e1_pull)
        gkr_layer_claim_c[xln] = e0_count + layer_challenge * (e0_count + e1_count)
        tail_fs, tail_lambda = squeeze(tail_fs)  # fresh λ pins the tail individuals
        gkr_layer_lambda[xln] = tail_lambda
        gkr_layer_fs0[xln] = tail_fs[0]
        gkr_layer_fs1[xln] = tail_fs[1]
        gkr_layer_cursor[xln] = tcur
        gkr_layer_row[xln] = nextrow
        gkr_layer_round_pos[xln] = round_pos * x_layer * GEN

    pair_bound = gkr_pair_bounds[g_bus_mu]
    for x_pair in mul_range(1, pair_bound):
        x_layer = x_pair * x_pair * gkr_depth_shift[g_bus_mu]
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
        for x_round in mul_range(1, x_layer):
            ip = round_pos * x_round
            nfs0, nfs1, ncur, nclaim, rk = sumcheck_round5(gkr_round_fs0[ip], gkr_round_fs1[ip], gkr_round_cursor[ip], gkr_round_claim[ip], point_row[x_round])
            nextrow[x_round * GEN ** 2] = rk
            pos_next = ip * GEN
            gkr_round_fs0[pos_next] = nfs0
            gkr_round_fs1[pos_next] = nfs1
            gkr_round_cursor[pos_next] = ncur
            gkr_round_claim[pos_next] = nclaim
        final_pos = round_pos * x_layer
        tail_fs = [gkr_round_fs0[final_pos], gkr_round_fs1[final_pos]]
        tcur = gkr_round_cursor[final_pos]
        tclaim = gkr_round_claim[final_pos]
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
        push_product = e0_push * e1_push * e2_push * e3_push
        pull_product = e0_pull * e1_pull * e2_pull * e3_pull
        count_product = e0_count * e1_count * e2_count * e3_count
        assert tclaim == push_product + lam * (pull_product + lam * count_product)
        tail_fs, c0 = squeeze(tail_fs)
        tail_fs, c1 = squeeze(tail_fs)
        nextrow[GEN ** 0] = c0
        nextrow[GEN ** 1] = c1
        push_lo = e0_push + c0 * (e0_push + e1_push)
        push_hi = e2_push + c0 * (e2_push + e3_push)
        pull_lo = e0_pull + c0 * (e0_pull + e1_pull)
        pull_hi = e2_pull + c0 * (e2_pull + e3_pull)
        count_lo = e0_count + c0 * (e0_count + e1_count)
        count_hi = e2_count + c0 * (e2_count + e3_count)
        xln = x_layer * GEN ** 2
        gkr_layer_claim[xln] = push_lo + c1 * (push_lo + push_hi)
        gkr_layer_claim_b[xln] = pull_lo + c1 * (pull_lo + pull_hi)
        gkr_layer_claim_c[xln] = count_lo + c1 * (count_lo + count_hi)
        tail_fs, tail_lambda = squeeze(tail_fs)
        gkr_layer_lambda[xln] = tail_lambda
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
    # kappa and the bus depth were derived above; the selector bits are
    # advice-decomposed at their use site (the decompose section) and pinned there —
    # never left to a single aggregate identity, which does not bind a high-entropy
    # hint in this smooth field.
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

    # ---- balance: push_root == pull_root ----
    # Every row of every table is a real row, so the two sides balance outright:
    # there is no padding surplus to divide back out, and with it went a bit-ladder
    # per side and table, each pinning a padding delta against an advice-decomposed
    # exponent.
    assert gkr_roots[PUSH_SIDE] == gkr_roots[PULL_SIDE]

    # ---- 3× leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    # The program's whole share of a bytecode leaf is ONE evaluation of the stacked
    # polynomial: its slots are aligned with the tuple and the weights are eq(α⃗, ·),
    # so the share IS that polynomial at (ζ_lo, α⃗) (doc sec:e2e-bc). One hinted
    # value, no per-coordinate values and no selector challenge.
    bytecode_hint = StackBuf(1)
    hint_witness(bytecode_hint[0:1], "bytecode_val")
    bc_share = bytecode_hint[0]
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); the Public
    # (bytecode) coordinate values are hinted (bytecode_vals) and exported as deferred
    # claims; Index coordinates use the factored index MLE.
    # Pull's blocks mirror push's (same kappas, same offsets — generator-
    # asserted pairing) and share zeta, so each pull block REUSES its push
    # twin's eq_hi and Index-MLE value instead of recomputing them; its column
    # values are mostly deduped pool reads (COORD_FRESH). The identity check
    # against pull's own GKR claim still binds everything.
    bus_table_total = HeapBuf(N_GKR_SIDES)  # per side, what its tables' blocks owe
    block_eq_hi = HeapBuf(N_BLOCKS)      # per push block, reused by its pull twin
    block_eq_all = HeapBuf(N_BLOCKS)     # every block's eq_hi, for the bus forms below
    block_index_mle = HeapBuf(N_BLOCKS)  # per push block with an Index coord
    for s in unroll(0, N_GKR_SIDES):
        acc = 0
        selector_sum = 0
        zeta_zs = zeta
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_has_public = 0
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
                    sel_bits[xk] = sbit * sbit  # booleanity as a write-once pin
                    eq_chain[xk * GEN] = eq_chain[xk] * (1 + sbit + zeta_hi[xk])  # eq(sel_bit, zeta) = 1 + sel_bit + zeta over GF(2)
                    goff_chain[xk * GEN] = goff_chain[xk] * (1 + sbit * (g_squares[kappa_g * xk] + 1))  # weight g^(2^(κ+k))
                eq_hi = eq_chain[sel_len_g]
                assert goff_chain[sel_len_g] == block_off_g[GEN ** b]  # bits == offset >> κ, κ-aligned
                if s == PUSH_SIDE:
                    block_eq_hi[GEN ** b] = eq_hi
            selector_sum += eq_hi
            block_eq_all[GEN ** b] = eq_hi
            # A TABLE's block streams no value here: the table sumcheck settles its
            # fingerprint from that table's column evaluations. Only the framework blocks
            # (boundary, memory, bytecode) still decompose.
            if BLOCK_TABLE[b] == NO_TABLE:
                # inner fingerprint Σ_i w_i · coord_i(ζ_lo); the count side weighs
                # slot 0 alone (α⃗ = 0), γ = 0.
                inner_sum = 0
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                    if COORD_TYPE[ci] == COORD_KIND_CONST:
                        coord_val = COORD_CONST[ci]
                    if COORD_TYPE[ci] == COORD_KIND_COL:
                        if COORD_FRESH[ci] == 1:
                            fs, coord_val, cursor = fs_next(fs, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = coord_val
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g  # cplen = block kappa
                        else:
                            coord_val = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                    if COORD_TYPE[ci] == COORD_KIND_GCOL:
                        if COORD_FRESH[ci] == 1:
                            fs, rawv, cursor = fs_next(fs, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = rawv
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g  # cplen = block kappa
                        else:
                            rawv = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                        coord_val = COORD_CONST[ci] * rawv
                    if COORD_TYPE[ci] == COORD_KIND_INDEX:
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
                    if COORD_TYPE[ci] == COORD_KIND_PUBLIC:
                        # The public slots carry no value of their own here: their
                        # alpha-weighted sum IS bc_share, added once per block below
                        # (push and pull share zeta, so both get the same one).
                        coord_val = 0
                        block_has_public = 1
                    if s == COUNT_SIDE:
                        inner_sum += coord_val
                    else:
                        inner_sum += fp_w[GEN ** i] * coord_val
                # The bytecode blocks' public slots, all of them at once.
                inner_sum += block_has_public * bc_share
                if s == COUNT_SIDE:
                    acc += eq_hi * inner_sum
                else:
                    acc += eq_hi * (gamma + inner_sum)
        acc += 1 + selector_sum
        # What the tables' blocks owe this side: its GKR leaf value less the
        # framework decomposition. DERIVED, not read: a transmitted total would be a
        # free value in its own check. The table sumcheck's target pins it below.
        bus_table_total[GEN ** s] = acc + gkr_claims[s]
    claim_idx = N_BUS_CLAIMS  # AIR/PI/pin claims pool after the deduped bus claims

    # ---- ONE table sumcheck for all seven tables ----
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
    eta_pows = StackBuf(N_ETA_POWS)
    eta_pows[0] = 1
    for k in unroll(1, N_ETA_POWS):
        eta_pows[k] = eta_pows[k - 1] * eta
    # The eq point is the bus GKR's zeta, NOT a fresh one: that is what lets the
    # batch settle the bus forms alongside the constraints.
    #
    # THE tie to the bus, and the reason no target is read: what the three sides'
    # tables owe, each in its own shared power of eta, IS the sum the batch must
    # reach. Since eta is squeezed after those totals are fixed, hitting one number
    # forces all three side equations.
    bus_target = 0
    for sd in unroll(0, N_GKR_SIDES):
        bus_target += eta_pows[ETA_FORM_BASE + sd] * bus_table_total[GEN ** sd]
    # n vanilla sumcheck rounds: the round polynomial arrives whole, so a round is
    # `h(0) + h(1) == claim` and a fold, with no eq to reapply. The tables still
    # waiting ride inside h, so nothing here is indexed by height; the heights enter
    # only the per-table weights below.
    rho = HeapBuf(g_zc_n)   # rho[i] = the challenge that bound variable i
    zc_round_fs0 = HeapBuf(g_zc_n * GEN)
    zc_round_fs1 = HeapBuf(g_zc_n * GEN)
    zc_round_cursor = HeapBuf(g_zc_n * GEN)
    zc_round_claim = HeapBuf(g_zc_n * GEN)
    zc_round_cprod = HeapBuf(g_zc_n * GEN)  # the challenges bound so far, multiplied
    zc_round_fs0[GEN ** 0] = fs[0]
    zc_round_fs1[GEN ** 0] = fs[1]
    zc_round_cursor[GEN ** 0] = cursor
    zc_round_claim[GEN ** 0] = bus_target
    zc_round_cprod[GEN ** 0] = 1
    for xk in mul_range(1, g_zc_n):
        d = g_zc_n * INV_GEN / xk  # g^(n-1-j): the variable round j binds
        nfs0, nfs1, ncur, nclaim, rk = sumcheck_round4(zc_round_fs0[xk], zc_round_fs1[xk], zc_round_cursor[xk], zc_round_claim[xk])
        rho[d] = rk
        xkn = xk * GEN
        zc_round_fs0[xkn] = nfs0
        zc_round_fs1[xkn] = nfs1
        zc_round_cursor[xkn] = ncur
        # cprod is the weight of a table that joins here; peq below is the rest
        zc_round_cprod[xkn] = zc_round_cprod[xk] * rk
        zc_round_claim[xkn] = nclaim
    fs = [zc_round_fs0[g_zc_n], zc_round_fs1[g_zc_n]]
    cursor = zc_round_cursor[g_zc_n]
    claim = zc_round_claim[g_zc_n]
    # peq[g^tau] = eq(zeta[..tau], rho[..tau]), as a prefix chain.
    zc_peq = HeapBuf(g_zc_n * GEN)
    zc_peq[GEN ** 0] = 1
    for xi in mul_range(1, g_zc_n):
        zc_peq[xi * GEN] = zc_peq[xi] * (1 + zeta[xi] + rho[xi])
    # Per table: every committed column's evaluation (pooled), its AIR constraint
    # at its own reduced point rho[..tau_t], weighted into the batch's final claim.
    air_acc = 0
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        col_evals = StackBuf(TABLE_COLS_CAP)
        for k in unroll(0, N_TABLE_COLS[t]):
            fs, e, cursor = fs_next(fs, cursor)
            col_evals[k] = e
            claim_pool[GEN ** claim_idx] = e
            claim_cplen_g[GEN ** claim_idx] = tau_g  # cplen = tau_t
            claim_idx += 1
        # the table's AIR constraint at the final point (col_evals is indexed by
        # local column index; the formulas mirror tables.rs eval_constraint).
        # Every value relation now rides the bus as a degree-2 coordinate, so only
        # JUMP's is-nonzero indicator is left with an identity of its own.
        if t == TABLE_XOR:
            constraint_eval = 0
        if t == TABLE_MUL:
            constraint_eval = 0
        if t == TABLE_SET:
            constraint_eval = 0
        if t == TABLE_DEREF:
            constraint_eval = 0
        if t == TABLE_JUMP:
            # `b = c*w` and `c*(b+1) = 0`. The condition is K-valued, its memory read
            # carrying literal zeros above the low limb, so both identities are
            # single-lane (tables.rs jump_identity). Local columns: c at 5, w at 12,
            # the indicator b at 13.
            c = col_evals[5]
            w = col_evals[12]
            b = col_evals[13]
            b1 = b + 1
            constraint_eval = eta_pows[ETA_OFFSET[t] + 0] * (b + c * w)
            constraint_eval += eta_pows[ETA_OFFSET[t] + 1] * (c * b1)
        if t == TABLE_BLAKE3:
            constraint_eval = 0
        if t == TABLE_PACK64X2:
            constraint_eval = 0
        # The table's three bus forms, evaluated at the SAME column evaluations:
        # Σ_b eq_hi(b) · (γ + Σ_i α^i · coord_i), the coords read off col_evals at
        # their local index. This is what replaces opening those columns at ζ.
        for sd in unroll(0, N_GKR_SIDES):
            form = 0
            for b in unroll(0, N_BLOCKS):
                if BLOCK_SIDE[b] == sd:
                    if BLOCK_TABLE[b] == t:
                        inner = 0
                        apow = GEN ** 0
                        for i in unroll(0, BLOCK_COORD_COUNT[b]):
                            # Each coord is the sum of its terms, over this table's
                            # column evaluations. A product term (an address, an
                            # arithmetic result) is degree 2, which the batch's
                            # round polynomial already allows.
                            ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                            cv = 0
                            for j in unroll(0, COORD_TERM_COUNT[ci]):
                                tj = COORD_TERM_OFF[ci] + j
                                if TERM_TYPE[tj] == COORD_KIND_CONST:
                                    cv += TERM_CONST[tj]
                                if TERM_TYPE[tj] == COORD_KIND_COL:
                                    cv += col_evals[TERM_COL_A[tj]]
                                if TERM_TYPE[tj] == COORD_KIND_GCOL:
                                    cv += TERM_CONST[tj] * col_evals[TERM_COL_A[tj]]
                                if TERM_TYPE[tj] == COORD_KIND_PROD:
                                    cv += TERM_CONST[tj] * (col_evals[TERM_COL_A[tj]] * col_evals[TERM_COL_B[tj]])
                            if sd == COUNT_SIDE:
                                inner += cv
                            else:
                                inner += fp_w[GEN ** i] * cv
                        if sd == COUNT_SIDE:
                            form += block_eq_all[GEN ** b] * inner
                        else:
                            form += block_eq_all[GEN ** b] * (gamma + inner)
            constraint_eval += eta_pows[ETA_FORM_BASE + sd] * form
        air_acc += zc_round_cprod[g_zc_n / tau_g] * zc_peq[tau_g] * constraint_eval  # cprod[n - tau] * peq[tau]
    assert air_acc == claim

    # ---- public-input binding claim: MEM as ONE logical E-column ----
    # The VM's bind_pi_claim makes a SINGLE E-claim at [rm, 0..]:
    #   MEM(rm) = interp(pi_0, pi_1, rm) = pi_0 + rm*(pi_0 + pi_1)
    # over the E-valued public input (no lane splitting, no Frobenius). One
    # evaluation per limb rides the stream and the three must reassemble it:
    # MEM = v_lo + Y*v_hi + Y²*v_top (doc sec:e2e-pi).
    fs, rm = squeeze(fs)
    mem = pi_0 + rm * (pi_0 + pi_1)
    fs, mem_lo, cursor = fs_next(fs, cursor)
    fs, mem_hi, cursor = fs_next(fs, cursor)
    fs, mem_top, cursor = fs_next(fs, cursor)
    assert mem == mem_lo + mem_hi * Y_TOWER + mem_top * Y_TOWER * Y_TOWER
    claim_pool[GEN ** claim_idx] = mem_lo
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = mem_hi
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = mem_top
    claim_idx += 1

    # ---- flock zerocheck (univariate skip, k_skip = 6) ----
    tau_blake3_g = dims_g[GEN ** (TABLE_BLAKE3 + 1)]  # the BLAKE3 table's certified tau
    # tau's reach is bounded: the count gadget gives tau < 34 (all flock
    # buffers are sized for that), and q_flock's committed kappa =
    # K_LOG + tau feeds the certified size m, whose opening
    # dispatch bound caps tau well below any baked structure.
    # flock's sub-proof scalars are ordinary stream words (add_scalar on the
    # native side); the cursor walks them, fetching and observing each in one
    # step (fs_next) at the point the transcript binds it.
    # The first K_SKIP Boolean rounds are replaced by the univariate skip and
    # consume no equality challenges. The remaining r coordinates are
    # N_FIXED_CHALLENGE_ROUNDS fixed inner values followed by sampled outer values.
    # The prover builds round 1 from this equality tail, so its sampled part is
    # squeezed before round 1 is fetched (and round 1 before z, which evaluates it).
    mr1cs_g = tau_blake3_g * GEN ** K_LOG  # runtime m = K_LOG + tau_5 (certified) in the exponent
    zerocheck_r = HeapBuf(mr1cs_g)
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        zerocheck_r[GEN ** (K_SKIP + i)] = FIXED_CHALLENGES[i]
    # outer samples at runtime count: m = K_LOG + tau_5 (certified).
    flock_point_fs0 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs1 = HeapBuf(mr1cs_g * GEN ** 2)
    flock_point_fs0[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[0]
    flock_point_fs1[GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)] = fs[1]
    for xi in mul_range(GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS), mr1cs_g):
        point_fs = [flock_point_fs0[xi], flock_point_fs1[xi]]
        point_fs, zerocheck_challenge = squeeze(point_fs)
        zerocheck_r[xi] = zerocheck_challenge
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
    fs, zerocheck_z = squeeze(fs)  # cursor now sits at the multilinear round messages, walked below
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
        fs, gamma_ab, cursor = fs_next(fs, cursor)  # G at 0, 1, infinity per round, walked in order
        fs, gamma_c, cursor = fs_next(fs, cursor)
        fs, g_inf, cursor = fs_next(fs, cursor)
        assert (1 + r_eq) * gamma_ab + r_eq * gamma_c == zc_running  # vanilla: the round answers the eq-split claim
        fs, rho_v = squeeze(fs)
        zerocheck_rhos[GEN ** i] = rho_v
        zc_running = gamma_ab + rho_v * (gamma_ab + gamma_c + (1 + rho_v) * g_inf)
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
        round_fs, gamma_ab, cur_i = fs_next(round_fs, cur_i)
        round_fs, gamma_c, cur_i = fs_next(round_fs, cur_i)
        round_fs, g_inf, cur_i = fs_next(round_fs, cur_i)
        assert (1 + r_eq) * gamma_ab + r_eq * gamma_c == round_running
        round_fs, rho_v = squeeze(round_fs)
        zerocheck_rhos[xi] = rho_v
        round_running = gamma_ab + rho_v * (gamma_ab + gamma_c + (1 + rho_v) * g_inf)
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
    fs, lincheck_alpha = squeeze(fs)
    fs, lincheck_beta = squeeze(fs)
    lc_running = lincheck_alpha * a_eval + b_eval + lincheck_beta  # lincheck seed: alpha*a + b + beta (batches the two matrix claims)
    lincheck_rs = HeapBuf(LINCHECK_ROUNDS)
    for i in unroll(0, LINCHECK_ROUNDS):
        fs, e0, cursor = fs_next(fs, cursor)  # q at 0, 1, infinity per round, walked in order
        fs, e1, cursor = fs_next(fs, cursor)
        fs, ei, cursor = fs_next(fs, cursor)
        assert e0 + e1 == lc_running  # vanilla: the round answers the running claim
        fs, rv = squeeze(fs)
        lincheck_rs[GEN ** i] = rv
        c1q = e0 + e1 + ei
        lc_running = (ei * rv + c1q) * rv + e0  # fold the degree-2 round poly at the challenge rv
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
    fs, lincheck_z_skip = squeeze(fs)
    skip_nums = StackBuf(2 ** K_SKIP)
    lag64(lincheck_z_skip, skip_nums, 0)
    lincheck_w = 0
    for i in unroll(0, 2 ** K_SKIP):
        lincheck_w += skip_nums[i] * LAGRANGE_INV_S[i] * z_partial[GEN ** i]

    # ---- stacked mixed opening: ring-switch fronts + claim combination ----
    # The two ring-switch slices (ab, c) each have PACKING = 2^LOG_PACKING = 64
    # entries. AB is lincheck's z_partial, already read; only C is sent, as the
    # next 64 stream words.
    # Claim 0 (ab): value lincheck_w, z_skip = lincheck_z_skip. Claim 1 (c):
    # value c_eval, z_skip = zerocheck_z. (The 128->64 half-fold the prover does
    # in blake3_flock::ring_claim is already baked into the transmitted 64 values,
    # so the verifier just checks the plain prefix-weighted inner product.)
    transposed_claims = StackBuf(2)
    rs_eq_vals = StackBuf(2)
    map_challenges = HeapBuf(6)
    c_table = HeapBuf(BASE_FIELD_BITS)
    z_vals = HeapBuf(2 * QFLOCK_VARS_CAP)
    claim_nums = StackBuf(2 ** K_SKIP)
    lag64(zerocheck_z, claim_nums, 0)
    claim_check = 0
    s_hat_v_c = HeapBuf(2 ** K_SKIP)  # C's row: fetch + observe each word
    for i in unroll(0, 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        s_hat_v_c[GEN ** i] = w
        claim_check += claim_nums[i] * LAGRANGE_INV_S[i] * w
    assert claim_check == c_eval
    # Compose six two-term F2-linear maps with shifts 32,16,8,4,2,1. Their
    # expansion has all 64 Frobenius terms required for soundness, while direct
    # application costs 63 squarings and only six general multiplications.
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        fs, map_challenge = squeeze(fs)
        map_challenges[GEN ** stage] = map_challenge
    # Expand the same composition once for the later transparent-weight
    # evaluation. Before shift d, the populated coefficients are exactly at
    # multiples of 2d; the new branch fills the adjacent d-offset entries.
    c_table[GEN ** 0] = 1
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        shift = RING_MAP_SHIFTS[stage]
        map_challenge = map_challenges[GEN ** stage]
        for slot in unroll(0, BASE_FIELD_BITS // (2 * shift)):
            coefficient = c_table[GEN ** (slot * 2 * shift)]
            for k in unroll(0, shift):
                coefficient *= coefficient
            c_table[GEN ** (slot * 2 * shift + shift)] = map_challenge * coefficient
    # Evaluate both claims together and combine their 64 packing rows.
    s_hat_row_0 = z_partial
    s_hat_row_1 = s_hat_v_c
    x_pow_chain = HeapBuf((2 ** K_SKIP) + 1)
    x_pow_chain[GEN ** 0] = GEN ** 0
    t_chain_0 = HeapBuf((2 ** K_SKIP) + 1)
    t_chain_1 = HeapBuf((2 ** K_SKIP) + 1)
    t_chain_0[GEN ** 0] = 0
    t_chain_1[GEN ** 0] = 0
    for x_round in mul_range(1, GEN ** (2 ** K_SKIP)):
        lin_eval_0 = s_hat_row_0[x_round]
        lin_eval_1 = s_hat_row_1[x_round]
        for stage in unroll(0, len(RING_MAP_SHIFTS)):
            frobenius_0 = lin_eval_0
            frobenius_1 = lin_eval_1
            for k in unroll(0, RING_MAP_SHIFTS[stage]):
                frobenius_0 *= frobenius_0
                frobenius_1 *= frobenius_1
            map_challenge = map_challenges[GEN ** stage]
            lin_eval_0 += map_challenge * frobenius_0
            lin_eval_1 += map_challenge * frobenius_1
        x_pow = x_pow_chain[x_round]
        t_chain_0[x_round * GEN] = t_chain_0[x_round] + x_pow * lin_eval_0
        t_chain_1[x_round * GEN] = t_chain_1[x_round] + x_pow * lin_eval_1
        x_pow_chain[x_round * GEN] = x_pow * 2
    transposed_claims[0] = t_chain_0[GEN ** (2 ** K_SKIP)]
    transposed_claims[1] = t_chain_1[GEN ** (2 ** K_SKIP)]
    # Suffix points for the two transparent weights.
    for t in unroll(0, LINCHECK_ROUNDS):
        z_vals[GEN ** t] = lincheck_rs[GEN ** (LINCHECK_ROUNDS - 1 - t)]
    zv_lo = z_vals * GEN ** LINCHECK_ROUNDS
    zr_hi = zerocheck_rhos * GEN ** LINCHECK_ROUNDS
    for xt in mul_range(1, tau_blake3_g):
        zv_lo[xt] = zr_hi[xt]
    zv_hi = z_vals * GEN ** QFLOCK_VARS_CAP
    zcr7 = zerocheck_r * GEN ** K_SKIP
    for xt in mul_range(1, tau_blake3_g * GEN ** SLOT_STRIDE_LOG):
        zv_hi[xt] = zcr7[xt]
    # gamma-combine the two transposed sumcheck claims (computed in-circuit).
    fs, gamma_rs = squeeze(fs)  # ONE challenge; the two claims take its powers 1, gamma_rs
    target = transposed_claims[0] + gamma_rs * transposed_claims[1]  # gamma-batch the two ring-switch claims into the opening's target
    # ...then every pooled point claim, each observed.
    for j in unroll(0, N_CLAIMS):
        fs = obs(fs, claim_pool[GEN ** j])
    fs, gamma = squeeze(fs)  # ONE challenge for the whole pool: N_CLAIMS - 1 fewer sponge compressions
    gamma_pool = HeapBuf(N_CLAIMS)
    gamma_pool[GEN ** 0] = 1  # powers of one challenge, as for the eta-powers above
    target += claim_pool[GEN ** 0]
    gv = 1
    for j in unroll(1, N_CLAIMS):
        gv *= gamma
        gamma_pool[GEN ** j] = gv
        target += gv * claim_pool[GEN ** j]

    # ================= the WHIR opening core (stacked, m = STACK) ========

    # ---- stacked WHIR opening: dispatch on the committed log-size ----
    # ---- reconstruct the native committed-column placement ----
    # placements_of sorts committed columns by descending kappa and then by
    # ascending column index. The hinted order is only transport: range checks,
    # write-once dynamic stores, the descending-kappa slack, and the tie-break
    # check certify that it is exactly that canonical permutation. Offsets then
    # accumulate as g^offset *= g^(2^kappa).
    col_kappa_g = HeapBuf(N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        col_kappa_g[GEN ** c] = kappa_base[GEN ** COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]
    col_sort_order = HeapBuf(N_COMMITTED_COLS)
    hint_witness(col_sort_order[0:N_COMMITTED_COLS], "col_sort_order")
    col_off_g = HeapBuf(N_COMMITTED_COLS)
    g_total = GEN ** 0
    prev_col = GEN ** 0
    prev_kappa = GEN ** 0
    for rank in unroll(0, N_COMMITTED_COLS):
        col = col_sort_order[GEN ** rank]
        assert log(col) < N_COMMITTED_COLS
        kappa_g = col_kappa_g[col]
        if rank != 0:
            # A negative exponent wraps around the order of GEN and cannot pass
            # this small range check, hence prev_kappa >= kappa.
            kappa_slack = prev_kappa / kappa_g
            assert log(kappa_slack) < SIZE_BITS
            if prev_kappa == kappa_g:
                # Equal-sized columns use their compact (native column-order)
                # index as the deterministic ascending tie-break.
                tie_slack = col / prev_col
                assert log(tie_slack) < N_COMMITTED_COLS
        col_off_g[col] = g_total  # write-once: a duplicate permutation entry collides
        g_total *= g_squares[kappa_g]
        prev_col = col
        prev_kappa = kappa_g

    # Exact bit decompositions of every certified offset, over the MAX_STACK_LOG
    # bits an offset can have. The window is tight in both directions: an offset is
    # < 2^m <= 2^MAX_STACK_LOG, so the rebuild below pins it exactly, and conversely
    # the rebuild IS a range check (only one exponent below the generator's order
    # reproduces g^offset). Every coordinate a reader touches is therefore either
    # rebuilt here or, being at or above m, zero-pinned at its use site. Extra zero
    # cells cover residual coordinates beyond the bound, which arise when dispatch
    # candidates have different residual caps.
    col_offset_bits = HeapBuf(N_COMMITTED_COLS * COL_BITS_STRIDE)
    for c in unroll(0, N_COMMITTED_COLS):
        offset_row = col_offset_bits * GEN ** (COL_BITS_STRIDE * c)
        hint_decompose_bits_exponent(offset_row, col_off_g[GEN ** c], MAX_STACK_LOG)
        rebuilt_offset = GEN ** 0
        for k in unroll(0, MAX_STACK_LOG):
            offset_bit = offset_row[GEN ** k]
            # Booleanity as a write-once pin: the cell already holds the bit, so
            # storing bit*bit back IS the assert (one instruction shorter than a
            # separate equality, as in decode_query_bits).
            offset_row[GEN ** k] = offset_bit * offset_bit
            rebuilt_offset *= (1 + offset_bit * gsq_plus[k])
        assert rebuilt_offset == col_off_g[GEN ** c]
        for k in unroll(MAX_STACK_LOG, COL_BITS_STRIDE):
            offset_row[GEN ** k] = 0

    # ---- certify g^m: m = max(log2_ceil(sum_cols 2^kappa), PCS_MIN_MU) ----
    # g_total is g^(sum 2^kappa) from the certified placement walk above.
    gmv = log2_ceil_in_the_exponent(g_total, g_logs_pow2, g_squares, PCS_MIN_MU, SIZE_BITS)  # g^m
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES
    # Flatten (rate-1, m-MIN) in rate-major order. Both coordinates are
    # transcript-bound and range-checked above, so a single compiled guest can
    # dispatch independently for every inner proof in a mixed-rate batch.
    config_sel = size_sel * rate_sel ** LIG_N_LOG_SIZES
    assert log(config_sel) < LIG_N_CANDIDATES
    sumcheck_target, fold_challenges, inner_total, yr_log_n_g, yr_pad_g, fold_cap_g, tail_challenges, yr_at_tail = match_range(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], target, commit_root_0, commit_root_1, cursor))
    # `stream` is a fixed-capacity witness transport. The shape fixes the exact
    # consumed prefix, whose every word is transcript-bound; the unused suffix
    # is outside the recursively verified proof and intentionally unconstrained.

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    # Per-claim lengths remain certified below. Every stack selector comes from
    # the certified offset of CLAIM_COMMITTED_COL[j]; it is not prover advice.
    # QFLOCK value-slot IDs are baked per logical claim. All selector products use
    # eq(b, r) = 1 + b + r.
    claim_low_len = HeapBuf(N_CLAIMS)  # computed low_len per claim (the y-slot
    #                             # overlap pointers below re-read it)
    claim_nover = HeapBuf(N_CLAIMS)
    hint_witness(claim_nover[0:N_CLAIMS], "claim_nover")
    pi_cplen = StackBuf(1)
    hint_witness(pi_cplen[0:1], "pi_cplen")
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
    # ---- shared low-coordinate eq chains ----
    # A claim's low_eq is the prefix product prod_{k < low_len} (1 + p_k + ris_k)
    # over its point buffer p: the FACTORS depend only on which buffer the claim
    # reads (and, for the qflock slots, on the ris shift), never on the claim, so
    # every claim on one buffer multiplies the same factors in the same order and
    # differs only in where it stops. Build one prefix-product chain per buffer
    # and let each claim read the partial product at its own certified length.
    # Chain entry t is written from inputs with index < t only, so a garbage tail
    # (past a buffer's written extent) cannot corrupt any shorter prefix; the
    # length pins below keep every claim's read inside the written span
    # (low_len <= cplen <= the point buffer's extent, and nlow <= lenris).
    zeta_eq_chain = HeapBuf(SIZE_BITS + 1)
    zeta_eq_chain[GEN ** 0] = 1
    for xk in mul_range(1, g_bus_mu):
        zeta_eq_chain[xk * GEN] = zeta_eq_chain[xk] * (1 + zeta[xk] + fold_challenges[xk])
    rho_eq_chain = HeapBuf(SIZE_BITS + 1)
    rho_eq_chain[GEN ** 0] = 1
    for xk in mul_range(1, g_zc_n):
        rho_eq_chain[xk * GEN] = rho_eq_chain[xk] * (1 + rho[xk] + fold_challenges[xk])
    # The qflock variant reads rho against ris shifted past the slot coordinates,
    # so it needs its own chain. There is no zeta counterpart: a virtual value
    # column is referenced only by its own table's bus blocks, which the zerocheck
    # settles, so no framework block can raise one (asserted while the placeholder
    # map is built).
    ris_slot = fold_challenges * GEN ** SLOT_STRIDE_LOG
    rho_slot_eq_chain = HeapBuf(SIZE_BITS + 1)
    rho_slot_eq_chain[GEN ** 0] = 1
    for xk in mul_range(1, g_zc_n):
        rho_slot_eq_chain[xk * GEN] = rho_slot_eq_chain[xk] * (1 + rho[xk] + ris_slot[xk])
    claim_weights = HeapBuf(N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        claim_offset_bits = col_offset_bits * GEN ** (COL_BITS_STRIDE * CLAIM_COMMITTED_COL[j])
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
            if CLAIM_POINT_BUF[j] == POINT_BUF_QFLOCK_RHO:
                nlow = cplen_g * GEN ** SLOT_STRIDE_LOG  # nlow = cplen + the qflock slot coords
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
        # low_eq: the shared chain's partial product at this claim's certified
        # length, times the qflock slot factors (the only per-claim part).
        if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
            low_eq = zeta_eq_chain[low_len_g]
        if CLAIM_POINT_BUF[j] == POINT_BUF_RHO:
            low_eq = rho_eq_chain[low_len_g]
        if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
            low_chain = HeapBuf(SIZE_BITS + 1)
            low_chain[GEN ** 0] = 1
            low_chain[GEN ** 1] = 1 + rm + fold_challenges[GEN ** 0]
            for xk in mul_range(GEN, low_len_g):
                low_chain[xk * GEN] = low_chain[xk] * (1 + fold_challenges[xk])
            low_eq = low_chain[low_len_g]
        if CLAIM_POINT_BUF[j] == POINT_BUF_QFLOCK_RHO:
            qflock_slot_eq = GEN ** 0
            for k in unroll(0, SLOT_STRIDE_LOG):
                sb3 = CLAIM_QFLOCK_SLOT_BITS[SLOT_STRIDE_LOG * j + k]
                qflock_slot_eq *= (1 + sb3 + fold_challenges[GEN ** k])
            low_eq = qflock_slot_eq * rho_slot_eq_chain[low_len_g]
        ris_hi = fold_challenges * nlow
        # Selector coordinates [nlow, lenris) are exactly the corresponding
        # certified placement-offset bits.
        selrow = claim_offset_bits * nlow
        sel_chain = HeapBuf(SIZE_BITS + 1)
        sel_chain[GEN ** 0] = low_eq
        for xk in mul_range(1, seln):
            sel_bit = selrow[xk]
            sel_chain[xk * GEN] = sel_chain[xk] * (1 + sel_bit + ris_hi[xk])
        claim_weights[GEN ** j] = sel_chain[seln] * gamma_pool[GEN ** j]
    # eval_rs_eq per claim: E = sum_k c_k * prod_j (z_j^(2^k) + 1 + ris_j)
    # (the telescoped product formula; z powers evolve by squaring per k).
    # QFLOCK_VARS_CAP = tau_5 + SLOT_STRIDE_LOG, exponent-additive from the
    # certified announced log. Walk the runtime coordinates OUTSIDE and the
    # fixed FIELD_BITS Frobenius powers inside: each coordinate loads its
    # opening challenge once and evolves z by squaring in registers, advancing
    # one contiguous FIELD_BITS-wide product row. Same product formula as the
    # k-major form, but with no stored z-power table (the dominant memory
    # traffic) and no per-level buffer.
    qflockv_g = tau_blake3_g * GEN ** SLOT_STRIDE_LOG
    # Evaluate both transparent weights in lockstep, sharing c_k and the
    # verifier-point factor in every inner iteration.
    z_row_src_1 = z_vals * GEN ** QFLOCK_VARS_CAP
    prod_chains_0 = HeapBuf((qflockv_g * GEN) ** BASE_FIELD_BITS)
    prod_chains_1 = HeapBuf((qflockv_g * GEN) ** BASE_FIELD_BITS)
    for k in unroll(0, BASE_FIELD_BITS):
        prod_chains_0[GEN ** k] = 1
        prod_chains_1[GEN ** k] = 1
    for x_round in mul_range(1, qflockv_g):
        zv_0 = z_vals[x_round]
        zv_1 = z_row_src_1[x_round]
        one_plus = 1 + fold_challenges[x_round]
        prod_row_0 = prod_chains_0 * x_round ** BASE_FIELD_BITS
        prod_row_1 = prod_chains_1 * x_round ** BASE_FIELD_BITS
        prod_row_next_0 = prod_row_0 * GEN ** BASE_FIELD_BITS
        prod_row_next_1 = prod_row_1 * GEN ** BASE_FIELD_BITS
        for k in unroll(0, BASE_FIELD_BITS):
            prod_row_next_0[GEN ** k] = prod_row_0[GEN ** k] * (zv_0 + one_plus)
            prod_row_next_1[GEN ** k] = prod_row_1[GEN ** k] * (zv_1 + one_plus)
            if k != BASE_FIELD_BITS - 1:
                zv_0 *= zv_0
                zv_1 *= zv_1
    prod_final_0 = prod_chains_0 * qflockv_g ** BASE_FIELD_BITS
    prod_final_1 = prod_chains_1 * qflockv_g ** BASE_FIELD_BITS
    e_acc_0 = 0
    e_acc_1 = 0
    for k in unroll(0, BASE_FIELD_BITS):
        ck = c_table[GEN ** k]
        e_acc_0 += ck * prod_final_0[GEN ** k]
        e_acc_1 += ck * prod_final_1[GEN ** k]
    rs_eq_vals[0] = e_acc_0
    rs_eq_vals[1] = e_acc_1
    # ring-switch weight: extend by the selector bits over the fold_challenges
    # coords [qflockv, lenris).
    rs_weight = rs_eq_vals[0] + gamma_rs * rs_eq_vals[1]
    # rs_len = lenris - qflockv, DERIVED as g^lenris / g^qflockv (not hinted). The
    # selector loop then reads fold_challenges[qflockv .. qflockv+rs_len) = [qflockv ..
    # lenris), inside its written [0, lenris) extent; a qflockv > lenris would make
    # rs_len a huge exponent and blow the range check below.
    rs_len_g = fold_cap_g / qflockv_g
    assert log(rs_len_g) < SIZE_BITS
    ris_q = fold_challenges * qflockv_g
    qflock_offset_bits = col_offset_bits * GEN ** (COL_BITS_STRIDE * QFLOCK_COMMITTED_COL)
    rs_sel_bits = qflock_offset_bits * qflockv_g
    rsw_chain = HeapBuf(SIZE_BITS + 1)
    rsw_chain[GEN ** 0] = rs_weight
    for xk in mul_range(1, rs_len_g):
        rs_bit = rs_sel_bits[xk]
        rsw_chain[xk * GEN] = rsw_chain[xk] * (1 + rs_bit + ris_q[xk])
    rs_weight = rsw_chain[rs_len_g]
    # Evaluate every transparent weight at the one terminal fold point. Claim
    # j contributes cw_j * eq(slot_point_j, tail_challenges); the transmitted
    # final message is evaluated once and multiplied into their combined weight.
    inner_sum = inner_total
    for j in unroll(0, N_CLAIMS):
        overlap_ptr = rho * claim_low_len[GEN ** j]
        if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
            overlap_ptr = zeta * claim_low_len[GEN ** j]
        # overlap_ptr[g^k] reads the claim point at low_len + k, which is written
        # only for k < nover (the [low_len, cplen) span); at k >= nover it points
        # into the unwritten point-buffer gap (prover-chosen free cells). The
        # mask row IS the baked prefix of exactly nover ones (selected by the
        # pinned nover), so no overlap coord can read past cplen by construction;
        # a mask with a stray 1 at k >= nover would read a free cell and hand
        # the sumcheck a linear knob (a full opening forgery) - the point-reuse
        # analog of the hole b7b470c closed on the direct y-slot path.
        mask_row = prefix_mask_table * claim_nover[GEN ** j] ** YR_LOG_CAP  # row nover: g^(nover * cap)
        claim_offset_bits = col_offset_bits * GEN ** (COL_BITS_STRIDE * CLAIM_COMMITTED_COL[j])
        residual_offset_bits = claim_offset_bits * fold_cap_g
        tail_eq = GEN ** 0
        for k in unroll(0, YR_LOG_CAP):
            mask_bit = mask_row[GEN ** k]
            slot_bit = residual_offset_bits[GEN ** k]
            slot_coord = mask_bit * overlap_ptr[GEN ** k] + (1 + mask_bit) * slot_bit
            tail_eq *= (1 + slot_coord + tail_challenges[GEN ** k])
        # zero-pin coords beyond final_msg's log-length (no over-cap weight): the
        # pointers start at yr_log_n. The zero asserts double as the
        # nover <= yr_log_n pin: a larger nover selects a row whose prefix
        # reaches into [yr_log_n, cap), failing here. So the mask is 0 in this
        # span, slot_point is 0, and no eq weight lands on the unwritten
        # final_msg cells past 2^yr_log_n.
        hi_mask = mask_row * yr_log_n_g
        hi_slot = residual_offset_bits * yr_log_n_g
        for xk in mul_range(1, yr_pad_g):
            assert hi_mask[xk] == 0
            assert hi_slot[xk] == 0
        inner_sum += claim_weights[GEN ** j] * tail_eq
    rs_yslot_bits = qflock_offset_bits * fold_cap_g
    rs_tail_eq = GEN ** 0
    for k in unroll(0, YR_LOG_CAP):
        yb = rs_yslot_bits[GEN ** k]
        rs_tail_eq *= (1 + yb + tail_challenges[GEN ** k])
    rs_hi = rs_yslot_bits * yr_log_n_g
    for xk in mul_range(1, yr_pad_g):
        assert rs_hi[xk] == 0  # zero-pin coords beyond final_msg's log-length
    inner_sum += rs_weight * rs_tail_eq
    assert inner_sum * yr_at_tail == sumcheck_target


    # ---- export this sub-proof's deferred-claim data to the caller ----
    # defer_out layout, offsets after the [0..KBC) shared bytecode point
    # (SEL = LOG2_BYTECODE_COLS, LCR = LINCHECK_ROUNDS):
    #   +0..SEL bytecode_sel | +SEL bytecode_reduced | +SEL+1 alpha
    #   | +SEL+2 z_skip | +SEL+3.. zrho | +SEL+3+LCR.. lincheck rs
    #   | +SEL+3+2*LCR.. z_partial (2^K_SKIP) | +SEL+3+2^K_SKIP+2*LCR matpart.
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = zeta[GEN ** k]
    for k in unroll(0, LOG2_BYTECODE_COLS):
        defer_out[GEN ** (BYTECODE_LOG + k)] = bus_alpha[GEN ** k]
    defer_out[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS)] = bc_share
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
    # nsub sub-proofs of the fixed inner program: verify each (verify_sub),
    # then aggregate their deferred claims. The fresh aggregation transcript
    # RLC-batches the bytecode and matrix claims through two sumchecks; only
    # the three reduced claims (evaluated natively by the outer verifier)
    # reach this guest's public input.
    # The arity is prover advice, hinted in the exponent as nsub_g = g^nsub. It
    # sizes every buffer and bounds every sub-walk below, and both transcripts
    # absorb it first, so a wrong count changes own_pi and is rejected there.
    nsub_hint = StackBuf(1)
    hint_witness(nsub_hint[0:1], "nsub")
    nsub_g = nsub_hint[0]
    assert log(nsub_g) < NSUB_BOUND
    sub_pis = HeapBuf(nsub_g * nsub_g)  # 2 statement words per sub
    # The FS seed — ONE digest of everything fixed about the inner environment
    # (the flock circuit family, the inner program bytecode) — rides the
    # recursion's public input: hinted here, it leads every sub's transcript
    # and is folded into own_pi below, so the outer statement fixes the whole
    # proving environment with one word pair.
    fs_seed = StackBuf(2)
    hint_witness(fs_seed[0:2], "fs_seed")
    seed_0 = fs_seed[0]  # scalars: a StackBuf cannot cross into a runtime loop body
    seed_1 = fs_seed[1]
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

    # per-sub deferred-claim regions (layout: see verify_sub's defer_out) and
    # the per-sub base pointer into them, so the walks below never redo g^(t*DEFER_SIZE).
    defer = HeapBuf(nsub_g ** DEFER_SIZE)
    defer_row = HeapBuf(nsub_g)

    for xs in mul_range(1, nsub_g):
        x2 = xs * xs  # g^(2t): this sub's statement pair
        hint_witness(sub_pis[x2:x2 + 2], "sub_pis")
        row = defer * xs ** DEFER_SIZE
        defer_row[xs] = row
        verify_sub(sub_pis[x2], sub_pis[x2 * GEN], seed_0, seed_1, g_logs_pow2, g_squares, row)

    # ================= aggregation: batch the deferred claims =================
    # A fresh transcript absorbs every deferred claim (points and values),
    # samples the RLC coefficients, and verifies the two batching sumchecks of
    # doc/main.tex §Deferred evaluation claims. Only the reduced claims (one per
    # fixed polynomial) reach the public input.
    # Every per-sub walk below is a runtime loop, so its loop-carried state (the
    # sponge, the running claim, the accumulated weight) rides a chain buffer
    # indexed by the counter, the guest's standard idiom.
    agg_fs = [AGG_SEED_0, AGG_SEED_1]
    agg_fs = obs(agg_fs, nsub_g)
    abs_fs0 = HeapBuf(nsub_g * GEN)
    abs_fs1 = HeapBuf(nsub_g * GEN)
    abs_fs0[GEN ** 0] = agg_fs[0]
    abs_fs1[GEN ** 0] = agg_fs[1]
    for xs in mul_range(1, nsub_g):
        x2 = xs * xs
        st = [abs_fs0[xs], abs_fs1[xs]]
        st = obs(st, sub_pis[x2])
        st = obs(st, sub_pis[x2 * GEN])
        # the deferred-claim region is one contiguous run in absorb order.
        row = defer_row[xs]
        for k in unroll(0, DEFER_SIZE):
            st = obs(st, row[GEN ** k])
        abs_fs0[xs * GEN] = st[0]
        abs_fs1[xs * GEN] = st[1]
    agg_fs = [abs_fs0[nsub_g], abs_fs1[nsub_g]]

    # ---- bytecode batching sumcheck (BYTECODE_VARS variables, nsub claims) ----
    gamma_bc = HeapBuf(nsub_g)
    bc_fs0 = HeapBuf(nsub_g * GEN)
    bc_fs1 = HeapBuf(nsub_g * GEN)
    bc_claim = HeapBuf(nsub_g * GEN)
    bc_fs0[GEN ** 0] = agg_fs[0]
    bc_fs1[GEN ** 0] = agg_fs[1]
    bc_claim[GEN ** 0] = 0
    for xs in mul_range(1, nsub_g):
        st = [bc_fs0[xs], bc_fs1[xs]]
        st, gv = squeeze(st)
        gamma_bc[xs] = gv
        row = defer_row[xs]
        xsn = xs * GEN
        bc_fs0[xsn] = st[0]
        bc_fs1[xsn] = st[1]
        bc_claim[xsn] = bc_claim[xs] + gv * row[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS)]
    agg_fs = [bc_fs0[nsub_g], bc_fs1[nsub_g]]
    bc_running = bc_claim[nsub_g]
    bc_point = HeapBuf(BYTECODE_VARS)
    for rd in unroll(0, BYTECODE_VARS):
        agg_fs, msg_g1, c = fs_next(agg_fs, bc_sumcheck_msgs * GEN ** (2 * rd))
        agg_fs, msg_ginf, c = fs_next(agg_fs, c)
        agg_fs, rv = squeeze(agg_fs)
        bc_point[GEN ** rd] = rv
        g_zero = bc_running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        bc_running = (msg_ginf * rv + c_one) * rv + g_zero  # fold the degree-2 batching-sumcheck round at rv
    # terminal: W(r*) in-circuit; the reduced bytecode claim B(r*) is deferred.
    bc_wsum = HeapBuf(nsub_g * GEN)
    bc_wsum[GEN ** 0] = 0
    for xs in mul_range(1, nsub_g):
        row = defer_row[xs]
        e = GEN ** 0
        for k in unroll(0, BYTECODE_LOG):
            e *= (1 + row[GEN ** k] + bc_point[GEN ** k])
        for k in unroll(0, LOG2_BYTECODE_COLS):
            e *= (1 + row[GEN ** (BYTECODE_LOG + k)] + bc_point[GEN ** (BYTECODE_LOG + k)])
        bc_wsum[xs * GEN] = bc_wsum[xs] + gamma_bc[xs] * e
    bc_weight = bc_wsum[nsub_g]
    bytecode_star = bc_star_hint[0]
    bc_final = bytecode_star * bc_weight  # terminal: claim == B(r*) * W(r*); B(r*) (bytecode_star) is deferred
    assert bc_running == bc_final

    # ---- matrix batching sumcheck (2*K_LOG variables, nsub weighted claims) ----
    gamma_mat = HeapBuf(nsub_g)
    mat_fs0 = HeapBuf(nsub_g * GEN)
    mat_fs1 = HeapBuf(nsub_g * GEN)
    mat_claim = HeapBuf(nsub_g * GEN)
    mat_fs0[GEN ** 0] = agg_fs[0]
    mat_fs1[GEN ** 0] = agg_fs[1]
    mat_claim[GEN ** 0] = 0
    for xs in mul_range(1, nsub_g):
        st = [mat_fs0[xs], mat_fs1[xs]]
        st, gv = squeeze(st)
        gamma_mat[xs] = gv
        row = defer_row[xs]
        xsn = xs * GEN
        mat_fs0[xsn] = st[0]
        mat_fs1[xsn] = st[1]
        mat_claim[xsn] = mat_claim[xs] + gv * row[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 ** K_SKIP + 2 * LINCHECK_ROUNDS)]
    agg_fs = [mat_fs0[nsub_g], mat_fs1[nsub_g]]
    mat_running = mat_claim[nsub_g]
    mat_point = HeapBuf(2 * K_LOG)
    for rd in unroll(0, 2 * K_LOG):
        agg_fs, msg_g1, c = fs_next(agg_fs, mat_sumcheck_msgs * GEN ** (2 * rd))
        agg_fs, msg_ginf, c = fs_next(agg_fs, c)
        agg_fs, rv = squeeze(agg_fs)
        mat_point[GEN ** rd] = rv
        g_zero = mat_running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        mat_running = (msg_ginf * rv + c_one) * rv + g_zero
    # terminal weights: U_t(r*) = urow_t(r*_row) * wcol_t(r*_col), with
    # row_weight = (sum_i L_i(zz_t) eq(r*[0..6], i)) * eq(zrho_t, r*[6..K_LOG]) and
    # col_weight = (sum_i z_partial_t[i] eq(r*[K_LOG..K_LOG+6], i)) * prod_j (1 + lrr_j
    # + r*[2*K_LOG-1-j]) (the lincheck binds column variables top-down).
    eq_rows = HeapBuf(2 ** (K_SKIP + 1) - 2)
    eqtree(mat_point, eq_rows, K_SKIP)
    eq_cols = HeapBuf(2 ** (K_SKIP + 1) - 2)
    eqtree(mat_point * GEN ** K_LOG, eq_cols, K_SKIP)
    wa_sum = HeapBuf(nsub_g * GEN)
    wb_sum = HeapBuf(nsub_g * GEN)
    wa_sum[GEN ** 0] = 0
    wb_sum[GEN ** 0] = 0
    for xs in mul_range(1, nsub_g):
        row = defer_row[xs]
        z_skip_t = row[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 2)]
        row_nums = StackBuf(2 ** K_SKIP)
        lag64(z_skip_t, row_nums, 0)
        row_weight = 0
        for i in unroll(0, 2 ** K_SKIP):
            row_weight += row_nums[i] * LAGRANGE_INV_S[i] * eq_rows[GEN ** (2 ** K_SKIP - 2 + i)]
        for k in unroll(0, LINCHECK_ROUNDS):
            row_weight *= (1 + row[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + k)] + mat_point[GEN ** (K_SKIP + k)])
        col_weight = 0
        for i in unroll(0, 2 ** K_SKIP):
            col_weight += row[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + 2 * LINCHECK_ROUNDS + i)] * eq_cols[GEN ** (2 ** K_SKIP - 2 + i)]
        for j in unroll(0, LINCHECK_ROUNDS):
            col_weight *= (1 + row[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 3 + LINCHECK_ROUNDS + j)] + mat_point[GEN ** (2 * K_LOG - 1 - j)])
        weight_u = row_weight * col_weight
        gm = gamma_mat[xs]
        xsn = xs * GEN
        wa_sum[xsn] = wa_sum[xs] + gm * row[GEN ** (BYTECODE_LOG + LOG2_BYTECODE_COLS + 1)] * weight_u
        wb_sum[xsn] = wb_sum[xs] + gm * weight_u
    weight_a = wa_sum[nsub_g]
    weight_b = wb_sum[nsub_g]
    a_star = mat_stars_hint[0]
    b_star = mat_stars_hint[1]
    mat_final = a_star * weight_a + b_star * weight_b
    assert mat_running == mat_final

    # ---- bind the FS seed + sub statements + reduced claims to the PI ----
    out_fs = [STATEMENT_SEED_0, STATEMENT_SEED_1]
    out_fs = obs(out_fs, nsub_g)
    out_fs = obs(out_fs, seed_0)  # the inner proving environment is part of the public statement
    out_fs = obs(out_fs, seed_1)
    out_fs0 = HeapBuf(nsub_g * GEN)
    out_fs1 = HeapBuf(nsub_g * GEN)
    out_fs0[GEN ** 0] = out_fs[0]
    out_fs1[GEN ** 0] = out_fs[1]
    for xs in mul_range(1, nsub_g):
        x2 = xs * xs
        st = [out_fs0[xs], out_fs1[xs]]
        st = obs(st, sub_pis[x2])
        st = obs(st, sub_pis[x2 * GEN])
        out_fs0[xs * GEN] = st[0]
        out_fs1[xs * GEN] = st[1]
    out_fs = [out_fs0[nsub_g], out_fs1[nsub_g]]
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
