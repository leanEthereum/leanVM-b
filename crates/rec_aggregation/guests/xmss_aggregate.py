# The in-VM XMSS aggregation verifier. The public input is the full 32-byte
# protocol-specific streaming accumulator (IV = g^{num_bytes} | 0^16) of
#     message | tweaks | merkle_bits | public keys,
# num_bytes = FIXED_BYTES + 32·n, with n (the signature count) hinted in the
# exponent and range checked. The fixed part (FIXED_BLOCKS blocks) is hinted,
# absorbed, and stored into buffers — so everything a verification later reads
# is bound by the hash the outer verifier recomputes. One runtime loop absorbs
# each public key block and verifies its signature (same message and slot for
# all). The IV size element is computed from n directly (the loop absorbs
# exactly n pk blocks, so it needs no separate hint or consistency check).
#
# Tweak table layout (word index in `tweak_table`):
#     0                        : encoding tweak
#     1 + CHAIN_STEPS·i + s    : chain tweak, chain i < V, step s < CHAIN_STEPS
#     WOTS_PK_TWEAK_IDX        : wots-pk tweak
#     MERKLE_TWEAK_IDX + l     : merkle tweak, quaternary level l < MERKLE_HEIGHT
from snark_lib import *

# ---- XMSS instance parameters (host-supplied via placeholders) ----
V = V_PLACEHOLDER                        # number of WOTS hash chains
W = W_PLACEHOLDER                        # log2 of the Winternitz chain length
TARGET_SUM = TARGET_SUM_PLACEHOLDER      # fixed encoding digit sum (Σ e_i)
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER  # log2 of the number of lifetime slots
MERKLE_HEIGHT = LOG_LIFETIME / 2          # same 2^32 leaves, four children per level

# ---- derived structural sizes (compile-time integer arithmetic) ----
CHAIN_LENGTH = 2 ** W               # Winternitz digit base (each e_i < this)
CHAIN_STEPS = CHAIN_LENGTH - 1      # hash steps / tweaks per chain
WOTS_PK_PAIRS = V / 2               # tip pairs hashed into the WOTS leaf

WORDS_PER_BLOCK = 2                 # a 256-bit value = two field words …
BYTES_PER_BLOCK = 32               # … = 32 bytes (one accumulator block)

# Tweak table (word layout): encoding | V·CHAIN_STEPS chain | wots-pk | merkle.
N_TWEAK_WORDS = 1 + V * CHAIN_STEPS + 1 + MERKLE_HEIGHT
N_TWEAK_BLOCKS = N_TWEAK_WORDS / WORDS_PER_BLOCK
WOTS_PK_TWEAK_IDX = 1 + V * CHAIN_STEPS      # word index of the wots-pk tweak
MERKLE_TWEAK_IDX = WOTS_PK_TWEAK_IDX + 1     # word index of merkle level 0

MERKLE_BIT_WORDS = LOG_LIFETIME              # two bit words per quaternary level
MERKLE_BIT_BLOCKS = LOG_LIFETIME / WORDS_PER_BLOCK

# Absorbed fixed preamble = message (1 block) | tweaks | merkle bits.
FIXED_BLOCKS = 1 + N_TWEAK_BLOCKS + MERKLE_BIT_BLOCKS
FIXED_BYTES = FIXED_BLOCKS * BYTES_PER_BLOCK

# Keyed WOTS-leaf blocks: 42 tips occupy ten full blocks and one 32-byte tail.
WOTS_PK_BLOCKS = (V + 3) / 4

N_SIGS_BOUND = 2 ** 16             # range cap for the hinted batch count


def main():
    # n_sigs = number of signatures, hinted in the exponent (g^{n_sigs});
    # range-checked below N_SIGS_BOUND (ample). The per-signature buffers are
    # sized to fit at runtime, so there is no fixed batch cap.
    n_sigs_hint = StackBuf(1)
    hint_witness(n_sigs_hint[0:1], "n_pks")
    n_sigs = n_sigs_hint[0]
    assert log(n_sigs) < N_SIGS_BOUND

    # IV of the top-level runtime-length accumulator: g^{num_bytes} | 0, with
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

    # Buffers for the common (per-batch) data — message, the tweak table, the
    # merkle-bit decomposition. Each block below is hinted, absorbed into the
    # hash, AND stored, which binds it to the public input.
    message = HeapBuf(WORDS_PER_BLOCK)
    tweak_table = HeapBuf(N_TWEAK_WORDS)
    merkle_bits = HeapBuf(MERKLE_BIT_WORDS)

    msg_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(msg_block, "msg")
    message[1] = msg_block[0]
    message[GEN] = msg_block[1]
    state = StackBuf(WORDS_PER_BLOCK)
    blake3(iv, msg_block, state)

    tweak_slot = 1  # tweak_table word cursor: g^0, g^2, g^4, … (2 words / block)
    for t in unroll(0, N_TWEAK_BLOCKS):
        block = StackBuf(WORDS_PER_BLOCK)
        hint_witness(block, "tweaks")
        tweak_table[tweak_slot] = block[0]
        tweak_table[tweak_slot * GEN] = block[1]
        tweak_slot = tweak_slot * GEN ** WORDS_PER_BLOCK
        next_state = StackBuf(WORDS_PER_BLOCK)
        blake3(state, block, next_state)
        state = next_state

    bit_slot = 1
    for u in unroll(0, MERKLE_BIT_BLOCKS):
        block = StackBuf(WORDS_PER_BLOCK)
        hint_witness(block, "merkle_bits")
        merkle_bits[bit_slot] = block[0]
        merkle_bits[bit_slot * GEN] = block[1]
        bit_slot = bit_slot * GEN ** WORDS_PER_BLOCK
        next_state = StackBuf(WORDS_PER_BLOCK)
        blake3(state, block, next_state)
        state = next_state

    # Per-signature buffers, sized in the exponent from n_sigs (see HeapBuf
    # docs): the MD state and each pk pair take a 2-cell slot per signature
    # (slot k at g^{2k}, g^{2k+1}), so n_sigs·n_sigs·g^2 cells.
    agg_states = HeapBuf(n_sigs * n_sigs * GEN ** WORDS_PER_BLOCK)
    pubkeys = HeapBuf(n_sigs * n_sigs * GEN ** WORDS_PER_BLOCK)
    agg_states[1] = state[0]
    agg_states[GEN] = state[1]
    for j in mul_range(1, n_sigs):
        slot = j * j  # signature k occupies cells g^{2k}, g^{2k+1}
        hint_witness(pubkeys[slot:slot + WORDS_PER_BLOCK], "pks")
        blake3(agg_states[slot:slot + WORDS_PER_BLOCK], pubkeys[slot:slot + WORDS_PER_BLOCK], agg_states[slot * GEN ** WORDS_PER_BLOCK:slot * GEN ** WORDS_PER_BLOCK + WORDS_PER_BLOCK])
        verify_sig(message, tweak_table, merkle_bits, pubkeys * slot)

    # Publish the final MD state = the aggregation public input.
    final_slot = n_sigs * n_sigs
    public_input = GEN ** 0
    public_input[1] = agg_states[final_slot]
    public_input[GEN] = agg_states[final_slot * GEN]
    return


def verify_sig(message, tweak_table, merkle_bits, pk_ptr):
    # pk_ptr[1] is the signer's merkle root, pk_ptr[GEN] its public parameter.
    pp = pk_ptr[GEN]

    # Encoding digest D = keyed_BLAKE3(msg | randomness | zero-pad), one
    # 64-byte block. The key is public_parameter | encoding_tweak.
    encoding_key = StackBuf(WORDS_PER_BLOCK)
    encoding_key[0] = pp
    encoding_key[1] = tweak_table[1]
    msg_block = StackBuf(WORDS_PER_BLOCK)
    msg_block[0] = message[1]
    msg_block[1] = message[GEN]
    rand_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(rand_block, "rand")
    digest = StackBuf(WORDS_PER_BLOCK)
    blake3(msg_block, rand_block, digest, cv=encoding_key, step=0, end=1, root=1, keyed=1)

    # V WOTS chains. Per chain: the digit is hinted in the exponent (g^{e_i}),
    # range checked, and dispatched once — arm k walks the remaining
    # CHAIN_STEPS-k steps and returns the tip plus the digit literal. The
    # product of the digits is the target sum (g^{Σe_i}); the digits, weighted
    # by CHAIN_LENGTH^i, reconstruct D.
    tips = StackBuf(V)
    digit_product = 1
    encoding_acc = 0
    weight = 1
    chain_tweaks = tweak_table * GEN  # chain i's tweaks start at g^{1+CHAIN_STEPS·i}
    for i in unroll(0, V):
        # The encoding digit e_i for chain i, hinted in the exponent (g^{e_i});
        # log(digit[0]) = e_i, which the match dispatches on.
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < CHAIN_LENGTH
        # The signature's chain value for chain i — the start of the walk the
        # arm hashes forward (CHAIN_STEPS-k steps) to the public-key tip.
        chain_start = StackBuf(1)
        hint_witness(chain_start[0:1], "chain_starts")
        tip, e = match_range(log(digit[0]), range(0, CHAIN_LENGTH), lambda k: walk(chain_start[0], chain_tweaks, pp, k))
        tips[i] = tip
        digit_product = digit_product * digit[0]
        encoding_acc = encoding_acc + e * weight  # e_i in its monomial subspace
        weight = weight * CHAIN_LENGTH
        chain_tweaks = chain_tweaks * GEN ** CHAIN_STEPS
    assert digit_product == GEN ** TARGET_SUM
    assert encoding_acc == digest[0]

    # WOTS public-key leaf = keyed BLAKE3 over 42 tips (672 bytes): ten full
    # blocks and one 32-byte tail, with key public_parameter | wots-pk tweak.
    pk_key = StackBuf(WORDS_PER_BLOCK)
    pk_key[0] = pp
    pk_key[1] = tweak_table[GEN ** WOTS_PK_TWEAK_IDX]
    leaf = StackBuf(WORDS_PER_BLOCK)
    blake3(tips[0:2], tips[2:4], leaf, cv=pk_key, step=0, keyed=1)
    for q in unroll(1, WOTS_PK_BLOCKS - 1):
        next_leaf = StackBuf(WORDS_PER_BLOCK)
        blake3(tips[4 * q:4 * q + 2], tips[4 * q + 2:4 * q + 4], next_leaf, cv=leaf, step=q, keyed=1)
        leaf = next_leaf
    zero_block = StackBuf(WORDS_PER_BLOCK)
    zero_block[0] = 0
    zero_block[1] = 0
    final_leaf = StackBuf(WORDS_PER_BLOCK)
    blake3(tips[V - 2:V], zero_block, final_leaf, cv=leaf, step=WOTS_PK_BLOCKS - 1, end=1, root=1, keyed=1, block_len=32)
    leaf = final_leaf

    # Quaternary Merkle path: two bound slot bits select the current node's
    # position among four children; three hinted siblings fill the other
    # positions in ascending child order. Four 16-byte children are one block.
    node = leaf[0]
    bit_slot = 1
    tweak_slot = 1
    merkle_tweaks = tweak_table * GEN ** MERKLE_TWEAK_IDX
    for l in unroll(0, MERKLE_HEIGHT):
        bit0 = merkle_bits[bit_slot]
        bit1 = merkle_bits[bit_slot * GEN]
        not0 = 1 + bit0
        not1 = 1 + bit1
        at0 = not0 * not1
        at1 = bit0 * not1
        at2 = not0 * bit1
        at3 = bit0 * bit1
        sibling0 = StackBuf(1)
        sibling1 = StackBuf(1)
        sibling2 = StackBuf(1)
        hint_witness(sibling0[0:1], "siblings")
        hint_witness(sibling1[0:1], "siblings")
        hint_witness(sibling2[0:1], "siblings")
        children = StackBuf(4)
        children[0] = sibling0[0] + at0 * (sibling0[0] + node)
        children[1] = sibling1[0] + at0 * (sibling1[0] + sibling0[0]) + at1 * (sibling1[0] + node)
        children[2] = sibling2[0] + (at0 + at1) * (sibling2[0] + sibling1[0]) + at2 * (sibling2[0] + node)
        children[3] = sibling2[0] + at3 * (sibling2[0] + node)
        merkle_key = StackBuf(WORDS_PER_BLOCK)
        merkle_key[0] = pp
        merkle_key[1] = merkle_tweaks[tweak_slot]
        parent = StackBuf(WORDS_PER_BLOCK)
        blake3(children[0:2], children[2:4], parent, cv=merkle_key, step=0, end=1, root=1, keyed=1)
        node = parent[0]
        bit_slot = bit_slot * GEN ** 2
        tweak_slot = tweak_slot * GEN
    assert node == pk_ptr[1]
    return


def walk(value, chain_tweaks, pp, k: Const):
    # Walk WOTS chain steps k..CHAIN_STEPS-1: value' is keyed BLAKE3 of the
    # 16-byte value under public_parameter | tweak; the
    # step tweaks read off the bound subtable (cursor advanced to step k first).
    tweak_cur = chain_tweaks
    for a in unroll(0, k):
        tweak_cur = tweak_cur * GEN
    first_half = StackBuf(WORDS_PER_BLOCK)
    first_half[0] = value
    first_half[1] = 0
    zero_half = StackBuf(WORDS_PER_BLOCK)
    zero_half[0] = 0
    zero_half[1] = 0
    for s in unroll(k, CHAIN_STEPS):
        step_key = StackBuf(WORDS_PER_BLOCK)
        step_key[0] = pp
        step_key[1] = tweak_cur[1]
        out = StackBuf(WORDS_PER_BLOCK)
        blake3(first_half, zero_half, out, cv=step_key, step=0, end=1, root=1, keyed=1, block_len=16)
        first_half = StackBuf(WORDS_PER_BLOCK)
        first_half[0] = out[0]
        first_half[1] = 0
        tweak_cur = tweak_cur * GEN
    return first_half[0], k
