# The in-VM XMSS aggregation verifier. The public input is the first 32-byte
# Merkle-Damgard state (IV = g^{num_bytes} | 0^24) of
#     message | tweaks | merkle_bits | public keys,
# num_bytes = FIXED_BYTES + 32·n, with n (the signature count) hinted in the
# exponent and range checked. The fixed part (FIXED_BLOCKS blocks) is hinted,
# absorbed, and stored into buffers — so everything a verification later reads
# is bound by the hash the outer verifier recomputes. One runtime loop absorbs
# each public key block and verifies its signature (same message and slot for
# all). The IV size element is computed from n directly (the loop absorbs
# exactly n pk blocks, so it needs no separate hint or consistency check).
#
# Machine words are 128-bit, so every 16-byte native value (tweak, digest word
# pair, chain tip, sibling, pp) is ONE cell, and a 32-byte hash block is TWO.
# Tweak table layout (tweak index t at cell g^{t}):
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

WORDS_PER_VALUE = 1                 # a 16-byte native value = ONE 128-bit cell …
WORDS_PER_BLOCK = 2                 # … and a 32-byte Merkle-Damgard block = two
BYTES_PER_BLOCK = 32

# The tower generator y = new(0, 1): the 128-bit word whose bit pattern is 2^64.
# `acc_lo + acc_hi·Y` packs two 64-bit lanes into one 128-bit cell.
Y = 18446744073709551616

# Tweak table (one 1-cell tweak per index): encoding | V·CHAIN_STEPS chain |
# wots-pk | merkle.
N_TWEAKS = 1 + V * CHAIN_STEPS + 1 + LOG_LIFETIME
N_TWEAK_CELLS = WORDS_PER_VALUE * N_TWEAKS
N_TWEAK_BLOCKS = N_TWEAKS / 2                # two tweaks per absorbed block
WOTS_PK_TWEAK_IDX = 1 + V * CHAIN_STEPS      # tweak index of the wots-pk tweak
MERKLE_TWEAK_IDX = WOTS_PK_TWEAK_IDX + 1     # tweak index of merkle level 0

MERKLE_BIT_CELLS = WORDS_PER_VALUE * LOG_LIFETIME  # one 1-cell bit word per level
MERKLE_BIT_BLOCKS = LOG_LIFETIME / 2

# Absorbed fixed preamble = message (1 block) | tweaks | merkle bits.
FIXED_BLOCKS = 1 + N_TWEAK_BLOCKS + MERKLE_BIT_BLOCKS
FIXED_BYTES = FIXED_BLOCKS * BYTES_PER_BLOCK

# Sub-hash IV byte counts (num_bytes = #blocks · 32).
ENC_IV_BYTES = 3 * BYTES_PER_BLOCK                        # tweak | msg | rand
WOTS_PK_IV_BYTES = (1 + WOTS_PK_PAIRS) * BYTES_PER_BLOCK  # pk-tweak | V/2 tip pairs

# Digits packed per digest lane: W bits each in GF(2^64)'s monomial budget
# (the lane's leftover top bits are ground to zero by the signer).
DIGITS_PER_WORD = V / 2

TIP_CELLS = WORDS_PER_VALUE * V    # the V chain tips, one cell each

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
    iv[0] = GEN ** FIXED_BYTES * pk_bytes  # cell 0 = g^{FIXED_BYTES + 32·n_sigs} | 0
    iv[1] = 0

    # Buffers for the common (per-batch) data — message, the tweak table (1
    # cell per tweak), the merkle-bit decomposition (1 cell per level). Each
    # block below is hinted, absorbed into the hash, AND stored, which binds it
    # to the public input.
    message = HeapBuf(WORDS_PER_BLOCK)
    tweak_table = HeapBuf(N_TWEAK_CELLS)
    merkle_bits = HeapBuf(MERKLE_BIT_CELLS)

    msg_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(msg_block, "msg")
    message[1] = msg_block[0]
    message[GEN] = msg_block[1]
    state = StackBuf(WORDS_PER_BLOCK)
    blake3(iv, msg_block, state)

    # Block t fills cells g^{2t}..g^{2t+1}: compile-time indexes, so every
    # store is a single DEREF (the offset rides the beta immediate).
    for t in unroll(0, N_TWEAK_BLOCKS):
        block = StackBuf(WORDS_PER_BLOCK)
        hint_witness(block, "tweaks")
        tweak_table[GEN ** (WORDS_PER_BLOCK * t)] = block[0]
        tweak_table[GEN ** (WORDS_PER_BLOCK * t + 1)] = block[1]
        next_state = StackBuf(WORDS_PER_BLOCK)
        blake3(state, block, next_state)
        state = next_state

    for u in unroll(0, MERKLE_BIT_BLOCKS):
        block = StackBuf(WORDS_PER_BLOCK)
        hint_witness(block, "merkle_bits")
        merkle_bits[GEN ** (WORDS_PER_BLOCK * u)] = block[0]
        merkle_bits[GEN ** (WORDS_PER_BLOCK * u + 1)] = block[1]
        next_state = StackBuf(WORDS_PER_BLOCK)
        blake3(state, block, next_state)
        state = next_state

    # Per-signature buffers, sized in the exponent from n_sigs (see HeapBuf
    # docs): the MD state and each pk block take a 2-cell slot per signature
    # (slot k at g^{2k}..g^{2k+1}), so n_sigs^2·g^2 cells.
    n_sigs_2 = n_sigs * n_sigs  # g^{2·n_sigs}
    agg_states = HeapBuf(n_sigs_2 * GEN ** WORDS_PER_BLOCK)
    pubkeys = HeapBuf(n_sigs_2 * GEN ** WORDS_PER_BLOCK)
    agg_states[1] = state[0]
    agg_states[GEN] = state[1]
    for j in mul_range(1, n_sigs):
        slot = j * j  # signature k occupies cells g^{2k}..g^{2k+1}
        # Name the two slot pointers once; the slices off them are then
        # compile-time (beta) offsets, with no per-operand pointer MUL.
        sig_state = agg_states * slot
        sig_pk = pubkeys * slot
        hint_witness(sig_pk[0:2], "pks")
        blake3(sig_state[0:2], sig_pk[0:2], sig_state[2:4])
        verify_sig(message, tweak_table, merkle_bits, sig_pk)

    # Publish the final MD state (two 128-bit cells) = the aggregation public input.
    final_ptr = agg_states * n_sigs_2
    public_input = GEN ** 0
    public_input[1] = final_ptr[1]
    public_input[GEN] = final_ptr[GEN]
    return


def verify_sig(message, tweak_table, merkle_bits, pk_ptr):
    # pk_ptr[g^0] is the signer's merkle root, pk_ptr[g^1] its public parameter
    # (one 128-bit cell each).
    pp = pk_ptr[GEN]

    # Encoding digest D = MD(tweak|pp, msg, randomness): IV = g^ENC_IV_BYTES | 0.
    enc_iv = StackBuf(WORDS_PER_BLOCK)
    enc_iv[0] = GEN ** ENC_IV_BYTES
    enc_iv[1] = 0
    tweak_pp = StackBuf(WORDS_PER_BLOCK)
    tweak_pp[0] = tweak_table[1]
    tweak_pp[1] = pp
    after_tweak = StackBuf(WORDS_PER_BLOCK)
    blake3(enc_iv, tweak_pp, after_tweak)
    msg_block = StackBuf(WORDS_PER_BLOCK)
    msg_block[0] = message[1]
    msg_block[1] = message[GEN]
    after_msg = StackBuf(WORDS_PER_BLOCK)
    blake3(after_tweak, msg_block, after_msg)
    rand_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(rand_block, "rand")
    digest = StackBuf(WORDS_PER_BLOCK)
    blake3(after_msg, rand_block, digest)

    # V WOTS chains. Per chain: the digit is hinted in the exponent (g^{e_i}),
    # range checked, and dispatched once — arm k walks the remaining
    # CHAIN_STEPS-k steps and returns the tip cell plus the digit literal. The
    # product of the digits is the target sum (g^{Σe_i}); the digits, weighted
    # by CHAIN_LENGTH^i inside each 64-bit lane (DIGITS_PER_WORD digits per
    # lane, GF(2^64)'s monomial budget, with each lane's leftover top bits
    # ground to zero by the signer), reconstruct the two lanes of D's first
    # cell, combined as `acc_lo + acc_hi·Y`.
    tips = StackBuf(TIP_CELLS)
    digit_product = 1
    chain_tweaks = tweak_table * GEN ** WORDS_PER_VALUE  # chain i's tweaks start at cell (1+CHAIN_STEPS·i)
    acc_lo = 0
    weight = 1
    for i in unroll(0, DIGITS_PER_WORD):
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < CHAIN_LENGTH
        chain_start = StackBuf(1)
        hint_witness(chain_start, "chain_starts")
        t, e = match_range(log(digit[0]), range(0, CHAIN_LENGTH), lambda k: walk(chain_start[0], chain_tweaks, pp, k))
        tips[i] = t
        digit_product = digit_product * digit[0]
        acc_lo = acc_lo + e * weight  # e_i in its monomial subspace of lane 0
        weight = weight * CHAIN_LENGTH
        chain_tweaks = chain_tweaks * GEN ** (WORDS_PER_VALUE * CHAIN_STEPS)
    acc_hi = 0
    weight = 1
    for i in unroll(DIGITS_PER_WORD, V):
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < CHAIN_LENGTH
        chain_start = StackBuf(1)
        hint_witness(chain_start, "chain_starts")
        t, e = match_range(log(digit[0]), range(0, CHAIN_LENGTH), lambda k: walk(chain_start[0], chain_tweaks, pp, k))
        tips[i] = t
        digit_product = digit_product * digit[0]
        acc_hi = acc_hi + e * weight  # e_i in its monomial subspace of lane 1
        weight = weight * CHAIN_LENGTH
        chain_tweaks = chain_tweaks * GEN ** (WORDS_PER_VALUE * CHAIN_STEPS)
    assert digit_product == GEN ** TARGET_SUM
    # Both lanes packed into D's first 128-bit cell.
    assert acc_lo + acc_hi * Y == digest[0]

    # WOTS public-key hash: MD over the V tips, IV = g^WOTS_PK_IV_BYTES | 0 —
    # the leaf.
    leaf_iv = StackBuf(WORDS_PER_BLOCK)
    leaf_iv[0] = GEN ** WOTS_PK_IV_BYTES
    leaf_iv[1] = 0
    pk_tweak_pp = StackBuf(WORDS_PER_BLOCK)
    pk_tweak_pp[0] = tweak_table[GEN ** (WORDS_PER_VALUE * WOTS_PK_TWEAK_IDX)]
    pk_tweak_pp[1] = pp
    leaf = StackBuf(WORDS_PER_BLOCK)
    blake3(leaf_iv, pk_tweak_pp, leaf)
    for q in unroll(0, WOTS_PK_PAIRS):
        next_leaf = StackBuf(WORDS_PER_BLOCK)
        blake3(leaf, tips[WORDS_PER_BLOCK * q:WORDS_PER_BLOCK * q + WORDS_PER_BLOCK], next_leaf)
        leaf = next_leaf

    # Merkle path from the leaf to the root: the hinted slot bit orders the
    # two children at each level; the tweak comes from the bound table. Level
    # l reads bit cell l and tweak cell (MERKLE_TWEAK_IDX+l): compile-time
    # (beta) indexes, one DEREF each.
    node = leaf[0]
    for l in unroll(0, LOG_LIFETIME):
        bit = merkle_bits[GEN ** (WORDS_PER_VALUE * l)]
        sibling = StackBuf(1)
        hint_witness(sibling, "siblings")
        # Branchless child ordering: bit ∈ {0,1} (bound by the hash), so the
        # swap is a select, not a branch. m = bit·(node⊕sibling) is 0 when
        # bit=0 and node⊕sibling when bit=1, so children[0] = node⊕m is node
        # for bit=0 and sibling for bit=1 (and children[1] the complement).
        diff = node + sibling[0]
        m = bit * diff
        children = StackBuf(WORDS_PER_BLOCK)
        children[0] = node + m
        children[1] = sibling[0] + m
        merkle_tweak_pp = StackBuf(WORDS_PER_BLOCK)
        merkle_tweak_pp[0] = tweak_table[GEN ** (WORDS_PER_VALUE * (MERKLE_TWEAK_IDX + l))]
        merkle_tweak_pp[1] = pp
        parent = StackBuf(WORDS_PER_BLOCK)
        blake3(merkle_tweak_pp, children, parent)
        node = parent[0]
    assert node == pk_ptr[1]
    return


def walk(value, chain_tweaks, pp, k: Const):
    # Walk WOTS chain steps k..CHAIN_STEPS-1: value' = H(tweak|pp, value|0).
    # Step s reads its tweak at cell s off the chain's subtable: a compile-time
    # (beta) offset, one DEREF each; no cursor to advance.
    block = StackBuf(WORDS_PER_BLOCK)
    block[0] = value
    block[1] = 0
    for s in unroll(k, CHAIN_STEPS):
        step_tweak = StackBuf(WORDS_PER_BLOCK)
        step_tweak[0] = chain_tweaks[GEN ** (WORDS_PER_VALUE * s)]
        step_tweak[1] = pp
        out = StackBuf(WORDS_PER_BLOCK)
        blake3(step_tweak, block, out)
        block = StackBuf(WORDS_PER_BLOCK)
        block[0] = out[0]
        block[1] = 0
    return block[0], k
