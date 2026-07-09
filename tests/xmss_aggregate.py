# The in-VM XMSS aggregation verifier. The public input is the first 16 bytes
# (two 64-bit words) of the 32-byte Merkle-Damgard state (IV = g^{num_bytes} |
# 0^24) of
#     message | tweaks | merkle_bits | public keys,
# num_bytes = FIXED_BYTES + 32·n, with n (the signature count) hinted in the
# exponent and range checked. The fixed part (FIXED_BLOCKS blocks) is hinted,
# absorbed, and stored into buffers — so everything a verification later reads
# is bound by the hash the outer verifier recomputes. One runtime loop absorbs
# each public key block and verifies its signature (same message and slot for
# all). The IV size element is computed from n directly (the loop absorbs
# exactly n pk blocks, so it needs no separate hint or consistency check).
#
# Every 16-byte native value (tweak, digest, chain tip, sibling, pp) spans TWO
# 64-bit cells; a 32-byte hash block spans FOUR. Tweak table layout (tweak
# index t at cells g^{2t}, g^{2t+1}):
#     0                        : encoding tweak
#     1 + CHAIN_STEPS·i + s    : chain tweak, chain i < V, step s < CHAIN_STEPS
#     WOTS_PK_TWEAK_IDX        : wots-pk tweak
#     MERKLE_TWEAK_IDX + l     : merkle tweak, level l < LOG_LIFETIME
from snark_lib import *

# ---- XMSS instance parameters (host-supplied via placeholders) ----
V = V_PLACEHOLDER                        # number of WOTS hash chains
W = W_PLACEHOLDER                        # log2 of the Winternitz chain length
TARGET_SUM = TARGET_SUM_PLACEHOLDER      # fixed encoding digit sum (Σ e_i)
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER  # Merkle tree height

# ---- derived structural sizes (compile-time integer arithmetic) ----
CHAIN_LENGTH = 2 ** W               # Winternitz digit base (each e_i < this)
CHAIN_STEPS = CHAIN_LENGTH - 1      # hash steps / tweaks per chain
WOTS_PK_PAIRS = V / 2               # tip pairs hashed into the WOTS leaf

WORDS_PER_VALUE = 2                 # a 16-byte native value = two 64-bit cells …
WORDS_PER_BLOCK = 4                 # … and a 32-byte Merkle-Damgard block = four
BYTES_PER_BLOCK = 32

# Tweak table (one 2-cell tweak per index): encoding | V·CHAIN_STEPS chain |
# wots-pk | merkle.
N_TWEAKS = 1 + V * CHAIN_STEPS + 1 + LOG_LIFETIME
N_TWEAK_CELLS = WORDS_PER_VALUE * N_TWEAKS
N_TWEAK_BLOCKS = N_TWEAKS / 2                # two tweaks per absorbed block
WOTS_PK_TWEAK_IDX = 1 + V * CHAIN_STEPS      # tweak index of the wots-pk tweak
MERKLE_TWEAK_IDX = WOTS_PK_TWEAK_IDX + 1     # tweak index of merkle level 0

MERKLE_BIT_CELLS = WORDS_PER_VALUE * LOG_LIFETIME  # one 2-cell bit word per level
MERKLE_BIT_BLOCKS = LOG_LIFETIME / 2

# Absorbed fixed preamble = message (1 block) | tweaks | merkle bits.
FIXED_BLOCKS = 1 + N_TWEAK_BLOCKS + MERKLE_BIT_BLOCKS
FIXED_BYTES = FIXED_BLOCKS * BYTES_PER_BLOCK

# Sub-hash IV byte counts (num_bytes = #blocks · 32).
ENC_IV_BYTES = 3 * BYTES_PER_BLOCK                        # tweak | msg | rand
WOTS_PK_IV_BYTES = (1 + WOTS_PK_PAIRS) * BYTES_PER_BLOCK  # pk-tweak | V/2 tip pairs

# Digits packed per digest word: W bits each in GF(2^64)'s monomial budget
# (the word's leftover top bits are ground to zero by the signer).
DIGITS_PER_WORD = V / 2

TIP_CELLS = WORDS_PER_VALUE * V    # the V chain tips, two cells each

N_SIGS_BOUND = 2 ** 16             # range cap for the hinted batch count


def main():
    # n_sigs = number of signatures, hinted in the exponent (g^{n_sigs});
    # range-checked below N_SIGS_BOUND (ample). The per-signature buffers are
    # sized to fit at runtime, so there is no fixed batch cap.
    n_sigs_hint = StackBuf(1)
    hint_witness(n_sigs_hint[0:1], "n_pks")
    n_sigs = n_sigs_hint[0]
    assert log(n_sigs) < N_SIGS_BOUND

    # IV of the top-level Merkle-Damgard hash: g^{num_bytes} | 0, with
    # num_bytes = FIXED_BYTES + 32·n_sigs computed straight from n_sigs — the
    # loop absorbs exactly n_sigs 32-byte pk blocks, so ×32 in the exponent is
    # n_sigs squared five times (n_sigs^32); no hint, no separate check.
    pk_bytes = n_sigs * n_sigs  # g^{2·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{4·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{8·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{16·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{32·n_sigs}
    iv = StackBuf(WORDS_PER_BLOCK)
    iv[0] = GEN ** FIXED_BYTES * pk_bytes  # g^{FIXED_BYTES + 32·n_sigs}
    iv[1] = 0
    iv[2] = 0
    iv[3] = 0

    # Buffers for the common (per-batch) data — message, the tweak table (2
    # cells per tweak), the merkle-bit decomposition (2 cells per level). Each
    # block below is hinted, absorbed into the hash, AND stored, which binds it
    # to the public input.
    message = HeapBuf(WORDS_PER_BLOCK)
    tweak_table = HeapBuf(N_TWEAK_CELLS)
    merkle_bits = HeapBuf(MERKLE_BIT_CELLS)

    msg_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(msg_block, "msg")
    message[1] = msg_block[0]
    message[GEN] = msg_block[1]
    message[GEN ** 2] = msg_block[2]
    message[GEN ** 3] = msg_block[3]
    state = StackBuf(WORDS_PER_BLOCK)
    blake3(iv, msg_block, state)

    # Block t fills cells g^{4t}..g^{4t+3}: compile-time indexes, so every
    # store is a single DEREF (the offset rides the beta immediate).
    for t in unroll(0, N_TWEAK_BLOCKS):
        block = StackBuf(WORDS_PER_BLOCK)
        hint_witness(block, "tweaks")
        tweak_table[GEN ** (WORDS_PER_BLOCK * t)] = block[0]
        tweak_table[GEN ** (WORDS_PER_BLOCK * t + 1)] = block[1]
        tweak_table[GEN ** (WORDS_PER_BLOCK * t + 2)] = block[2]
        tweak_table[GEN ** (WORDS_PER_BLOCK * t + 3)] = block[3]
        next_state = StackBuf(WORDS_PER_BLOCK)
        blake3(state, block, next_state)
        state = next_state

    for u in unroll(0, MERKLE_BIT_BLOCKS):
        block = StackBuf(WORDS_PER_BLOCK)
        hint_witness(block, "merkle_bits")
        merkle_bits[GEN ** (WORDS_PER_BLOCK * u)] = block[0]
        merkle_bits[GEN ** (WORDS_PER_BLOCK * u + 1)] = block[1]
        merkle_bits[GEN ** (WORDS_PER_BLOCK * u + 2)] = block[2]
        merkle_bits[GEN ** (WORDS_PER_BLOCK * u + 3)] = block[3]
        next_state = StackBuf(WORDS_PER_BLOCK)
        blake3(state, block, next_state)
        state = next_state

    # Per-signature buffers, sized in the exponent from n_sigs (see HeapBuf
    # docs): the MD state and each pk block take a 4-cell slot per signature
    # (slot k at g^{4k}..g^{4k+3}), so n_sigs^4·g^4 cells.
    n_sigs_4 = n_sigs * n_sigs * n_sigs * n_sigs  # g^{4·n_sigs}
    agg_states = HeapBuf(n_sigs_4 * GEN ** WORDS_PER_BLOCK)
    pubkeys = HeapBuf(n_sigs_4 * GEN ** WORDS_PER_BLOCK)
    agg_states[1] = state[0]
    agg_states[GEN] = state[1]
    agg_states[GEN ** 2] = state[2]
    agg_states[GEN ** 3] = state[3]
    for j in mul_range(1, n_sigs):
        j2 = j * j
        slot = j2 * j2  # signature k occupies cells g^{4k}..g^{4k+3}
        # Name the two slot pointers once; the slices off them are then
        # compile-time (beta) offsets, with no per-operand pointer MUL.
        sig_state = agg_states * slot
        sig_pk = pubkeys * slot
        hint_witness(sig_pk[0:4], "pks")
        blake3(sig_state[0:4], sig_pk[0:4], sig_state[4:8])
        verify_sig(message, tweak_table, merkle_bits, sig_pk)

    # Publish the first two words of the final MD state = the aggregation
    # public input.
    final_ptr = agg_states * n_sigs_4
    public_input = GEN ** 0
    public_input[1] = final_ptr[1]
    public_input[GEN] = final_ptr[GEN]
    return


def verify_sig(message, tweak_table, merkle_bits, pk_ptr):
    # pk_ptr[g^0..g^1] is the signer's merkle root, pk_ptr[g^2..g^3] its
    # public parameter (two 64-bit words each).
    pp0 = pk_ptr[GEN ** 2]
    pp1 = pk_ptr[GEN ** 3]

    # Encoding digest D = MD(tweak|pp, msg, randomness): IV = g^ENC_IV_BYTES | 0.
    enc_iv = StackBuf(WORDS_PER_BLOCK)
    enc_iv[0] = GEN ** ENC_IV_BYTES
    enc_iv[1] = 0
    enc_iv[2] = 0
    enc_iv[3] = 0
    tweak_pp = StackBuf(WORDS_PER_BLOCK)
    tweak_pp[0] = tweak_table[1]
    tweak_pp[1] = tweak_table[GEN]
    tweak_pp[2] = pp0
    tweak_pp[3] = pp1
    after_tweak = StackBuf(WORDS_PER_BLOCK)
    blake3(enc_iv, tweak_pp, after_tweak)
    msg_block = StackBuf(WORDS_PER_BLOCK)
    msg_block[0] = message[1]
    msg_block[1] = message[GEN]
    msg_block[2] = message[GEN ** 2]
    msg_block[3] = message[GEN ** 3]
    after_msg = StackBuf(WORDS_PER_BLOCK)
    blake3(after_tweak, msg_block, after_msg)
    rand_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(rand_block, "rand")
    digest = StackBuf(WORDS_PER_BLOCK)
    blake3(after_msg, rand_block, digest)

    # V WOTS chains. Per chain: the digit is hinted in the exponent (g^{e_i}),
    # range checked, and dispatched once — arm k walks the remaining
    # CHAIN_STEPS-k steps and returns the two tip words plus the digit literal.
    # The product of the digits is the target sum (g^{Σe_i}); the digits,
    # weighted by CHAIN_LENGTH^i inside each 64-bit word (DIGITS_PER_WORD
    # digits per word, GF(2^64)'s monomial budget, with each word's leftover
    # top bits ground to zero by the signer), reconstruct D's two words.
    tips = StackBuf(TIP_CELLS)
    digit_product = 1
    chain_tweaks = tweak_table * GEN ** WORDS_PER_VALUE  # chain i's tweaks start at cell 2·(1+CHAIN_STEPS·i)
    acc_lo = 0
    weight = 1
    for i in unroll(0, DIGITS_PER_WORD):
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < CHAIN_LENGTH
        chain_start = StackBuf(2)
        hint_witness(chain_start, "chain_starts")
        t0, t1, e = match_range(log(digit[0]), range(0, CHAIN_LENGTH), lambda k: walk(chain_start[0], chain_start[1], chain_tweaks, pp0, pp1, k))
        tips[2 * i] = t0
        tips[2 * i + 1] = t1
        digit_product = digit_product * digit[0]
        acc_lo = acc_lo + e * weight  # e_i in its monomial subspace of word 0
        weight = weight * CHAIN_LENGTH
        chain_tweaks = chain_tweaks * GEN ** (WORDS_PER_VALUE * CHAIN_STEPS)
    acc_hi = 0
    weight = 1
    for i in unroll(DIGITS_PER_WORD, V):
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < CHAIN_LENGTH
        chain_start = StackBuf(2)
        hint_witness(chain_start, "chain_starts")
        t0, t1, e = match_range(log(digit[0]), range(0, CHAIN_LENGTH), lambda k: walk(chain_start[0], chain_start[1], chain_tweaks, pp0, pp1, k))
        tips[2 * i] = t0
        tips[2 * i + 1] = t1
        digit_product = digit_product * digit[0]
        acc_hi = acc_hi + e * weight  # e_i in its monomial subspace of word 1
        weight = weight * CHAIN_LENGTH
        chain_tweaks = chain_tweaks * GEN ** (WORDS_PER_VALUE * CHAIN_STEPS)
    assert digit_product == GEN ** TARGET_SUM
    assert acc_lo == digest[0]
    assert acc_hi == digest[1]

    # WOTS public-key hash: MD over the V tips, IV = g^WOTS_PK_IV_BYTES | 0 —
    # the leaf.
    leaf_iv = StackBuf(WORDS_PER_BLOCK)
    leaf_iv[0] = GEN ** WOTS_PK_IV_BYTES
    leaf_iv[1] = 0
    leaf_iv[2] = 0
    leaf_iv[3] = 0
    pk_tweak_pp = StackBuf(WORDS_PER_BLOCK)
    pk_tweak_pp[0] = tweak_table[GEN ** (WORDS_PER_VALUE * WOTS_PK_TWEAK_IDX)]
    pk_tweak_pp[1] = tweak_table[GEN ** (WORDS_PER_VALUE * WOTS_PK_TWEAK_IDX + 1)]
    pk_tweak_pp[2] = pp0
    pk_tweak_pp[3] = pp1
    leaf = StackBuf(WORDS_PER_BLOCK)
    blake3(leaf_iv, pk_tweak_pp, leaf)
    for q in unroll(0, WOTS_PK_PAIRS):
        next_leaf = StackBuf(WORDS_PER_BLOCK)
        blake3(leaf, tips[WORDS_PER_BLOCK * q:WORDS_PER_BLOCK * q + WORDS_PER_BLOCK], next_leaf)
        leaf = next_leaf

    # Merkle path from the leaf to the root: the hinted slot bit orders the
    # two children at each level; the tweak comes from the bound table. Level
    # l reads bit word 2l and tweak word 2·(MERKLE_TWEAK_IDX+l): compile-time
    # (beta) indexes, one DEREF each.
    node0 = leaf[0]
    node1 = leaf[1]
    for l in unroll(0, LOG_LIFETIME):
        bit = merkle_bits[GEN ** (WORDS_PER_VALUE * l)]
        sibling = StackBuf(2)
        hint_witness(sibling, "siblings")
        # Branchless child ordering: bit ∈ {0,1} (bound by the hash), so the
        # swap is a select, not a branch. m = bit·(node⊕sibling) is 0 when
        # bit=0 and node⊕sibling when bit=1, so children[0..2] = node⊕m is
        # node for bit=0 and sibling for bit=1 (and children[2..4] the
        # complement), per 64-bit word.
        diff0 = node0 + sibling[0]
        diff1 = node1 + sibling[1]
        m0 = bit * diff0
        m1 = bit * diff1
        children = StackBuf(WORDS_PER_BLOCK)
        children[0] = node0 + m0
        children[1] = node1 + m1
        children[2] = sibling[0] + m0
        children[3] = sibling[1] + m1
        merkle_tweak_pp = StackBuf(WORDS_PER_BLOCK)
        merkle_tweak_pp[0] = tweak_table[GEN ** (WORDS_PER_VALUE * (MERKLE_TWEAK_IDX + l))]
        merkle_tweak_pp[1] = tweak_table[GEN ** (WORDS_PER_VALUE * (MERKLE_TWEAK_IDX + l) + 1)]
        merkle_tweak_pp[2] = pp0
        merkle_tweak_pp[3] = pp1
        parent = StackBuf(WORDS_PER_BLOCK)
        blake3(merkle_tweak_pp, children, parent)
        node0 = parent[0]
        node1 = parent[1]
    assert node0 == pk_ptr[1]
    assert node1 == pk_ptr[GEN]
    return


def walk(value0, value1, chain_tweaks, pp0, pp1, k: Const):
    # Walk WOTS chain steps k..CHAIN_STEPS-1: value' = H(tweak|pp, value|0).
    # Step s reads its tweak at cells 2s, 2s+1 off the chain's subtable:
    # compile-time (beta) offsets, one DEREF each; no cursor to advance.
    block = StackBuf(WORDS_PER_BLOCK)
    block[0] = value0
    block[1] = value1
    block[2] = 0
    block[3] = 0
    for s in unroll(k, CHAIN_STEPS):
        step_tweak = StackBuf(WORDS_PER_BLOCK)
        step_tweak[0] = chain_tweaks[GEN ** (WORDS_PER_VALUE * s)]
        step_tweak[1] = chain_tweaks[GEN ** (WORDS_PER_VALUE * s + 1)]
        step_tweak[2] = pp0
        step_tweak[3] = pp1
        out = StackBuf(WORDS_PER_BLOCK)
        blake3(step_tweak, block, out)
        block = StackBuf(WORDS_PER_BLOCK)
        block[0] = out[0]
        block[1] = out[1]
        block[2] = 0
        block[3] = 0
    return block[0], block[1], k
