# The in-VM XMSS aggregation verifier. The public input is the full 32-byte
# Merkle-Damgard state (IV = g^{num_bytes} | 0^16) of
#     message | tweaks | merkle_bits | public keys,
# num_bytes = 5792 + 32·n, with n (the signature count) hinted in the exponent
# and range checked. The fixed part (1 + 164 + 16 = 181 blocks) is hinted,
# absorbed, and stored into buffers — so everything a verification later reads
# is bound by the hash the outer verifier recomputes. One runtime loop absorbs
# each public key block and verifies its signature (same message and slot for
# all). The IV size element is computed from n directly (the loop absorbs
# exactly n pk blocks, so it needs no separate hint or consistency check).
#
# Tweak table layout (word index in `tweak_table`):
#     0            : encoding tweak
#     1 + 7i + s   : chain tweak, chain i < 42, step s < 7
#     295          : wots-pk tweak
#     296 + l      : merkle tweak, level l < 32
from snark_lib import *


def main():
    # n_sigs = number of signatures, hinted in the exponent (g^{n_sigs});
    # range-checked below 2^16 (ample). The per-signature buffers are sized to
    # fit at runtime, so there is no fixed batch cap.
    n_sigs_hint = StackBuf(1)
    hint_witness(n_sigs_hint[0:1], "n_pks")
    n_sigs = n_sigs_hint[0]
    assert log(n_sigs) < 65536

    # IV of the top-level Merkle-Damgard hash: g^{num_bytes} | 0, with
    # num_bytes = 5792 + 32·n_sigs computed straight from n_sigs — the loop
    # absorbs exactly n_sigs 32-byte pk blocks, so ×32 in the exponent is
    # n_sigs squared five times (n_sigs^32); no hint, no separate check.
    pk_bytes = n_sigs * n_sigs  # g^{2·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{4·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{8·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{16·n_sigs}
    pk_bytes = pk_bytes * pk_bytes  # g^{32·n_sigs}
    iv = StackBuf(2)
    iv[0] = GEN ** 5792 * pk_bytes  # g^{5792 + 32·n_sigs}
    iv[1] = 0

    # Buffers for the common (per-batch) data — message, the 328-word tweak
    # table, the 32-word merkle-bit decomposition. Each block below is hinted,
    # absorbed into the hash, AND stored, which binds it to the public input.
    message = HeapBuf(2)
    tweak_table = HeapBuf(328)
    merkle_bits = HeapBuf(32)

    msg_block = StackBuf(2)
    hint_witness(msg_block, "msg")
    message[1] = msg_block[0]
    message[GEN] = msg_block[1]
    state = StackBuf(2)
    blake3(iv, msg_block, state)

    tweak_slot = 1  # tweak_table word cursor: g^0, g^2, g^4, … (2 words / block)
    for t in unroll(0, 164):
        block = StackBuf(2)
        hint_witness(block, "tweaks")
        tweak_table[tweak_slot] = block[0]
        tweak_table[tweak_slot * GEN] = block[1]
        tweak_slot = tweak_slot * GEN ** 2
        next_state = StackBuf(2)
        blake3(state, block, next_state)
        state = next_state

    bit_slot = 1
    for u in unroll(0, 16):
        block = StackBuf(2)
        hint_witness(block, "merkle_bits")
        merkle_bits[bit_slot] = block[0]
        merkle_bits[bit_slot * GEN] = block[1]
        bit_slot = bit_slot * GEN ** 2
        next_state = StackBuf(2)
        blake3(state, block, next_state)
        state = next_state

    # Per-signature buffers, sized in the exponent from n_sigs (see HeapBuf
    # docs): the MD state and each pk pair take a 2-cell slot per signature
    # (slot k at g^{2k}, g^{2k+1}), so n_sigs·n_sigs·g^2 cells.
    agg_states = HeapBuf(n_sigs * n_sigs * GEN ** 2)
    pubkeys = HeapBuf(n_sigs * n_sigs * GEN ** 2)
    agg_states[1] = state[0]
    agg_states[GEN] = state[1]
    for j in mul_range(1, n_sigs):
        slot = j * j  # signature k occupies cells g^{2k}, g^{2k+1}
        hint_witness(pubkeys[slot:slot + 2], "pks")
        blake3(agg_states[slot:slot + 2], pubkeys[slot:slot + 2], agg_states[slot * GEN ** 2:slot * GEN ** 2 + 2])
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

    # Encoding digest D = MD(tweak|pp, msg, randomness): IV = g^96 | 0.
    enc_iv = StackBuf(2)
    enc_iv[0] = GEN ** 96
    enc_iv[1] = 0
    tweak_pp = StackBuf(2)
    tweak_pp[0] = tweak_table[1]
    tweak_pp[1] = pp
    after_tweak = StackBuf(2)
    blake3(enc_iv, tweak_pp, after_tweak)
    msg_block = StackBuf(2)
    msg_block[0] = message[1]
    msg_block[1] = message[GEN]
    after_msg = StackBuf(2)
    blake3(after_tweak, msg_block, after_msg)
    rand_block = StackBuf(2)
    hint_witness(rand_block, "rand")
    digest = StackBuf(2)
    blake3(after_msg, rand_block, digest)

    # 42 WOTS chains. Per chain: the digit is hinted in the exponent (g^{e_i}),
    # range checked, and dispatched once — arm k walks the remaining 7-k steps
    # and returns the tip plus the digit literal. The product of the digits is
    # the target sum (g^{Σe_i}); the digits, weighted by 8^i, reconstruct D.
    tips = StackBuf(42)
    digit_product = 1
    encoding_acc = 0
    weight = 1
    chain_tweaks = tweak_table * GEN  # chain i's tweaks start at g^{1+7i}
    for i in unroll(0, 42):
        # The encoding digit e_i for chain i, hinted in the exponent (g^{e_i});
        # log(digit[0]) = e_i, which the match dispatches on.
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < 8
        # The signature's chain value for chain i — the start of the walk the
        # arm hashes forward (7-k steps) to the public-key tip.
        chain_start = StackBuf(1)
        hint_witness(chain_start[0:1], "chain_starts")
        tip, e = match_range(log(digit[0]), range(0, 8), lambda k: walk(chain_start[0], chain_tweaks, pp, k))
        tips[i] = tip
        digit_product = digit_product * digit[0]
        encoding_acc = encoding_acc + e * weight  # e_i in its monomial subspace
        weight = weight * 8
        chain_tweaks = chain_tweaks * GEN ** 7
    assert digit_product == GEN ** 194
    assert encoding_acc == digest[0]

    # WOTS public-key hash: MD over the 42 tips, IV = g^704 | 0 — the leaf.
    leaf_iv = StackBuf(2)
    leaf_iv[0] = GEN ** 704
    leaf_iv[1] = 0
    pk_tweak_pp = StackBuf(2)
    pk_tweak_pp[0] = tweak_table[GEN ** 295]
    pk_tweak_pp[1] = pp
    leaf = StackBuf(2)
    blake3(leaf_iv, pk_tweak_pp, leaf)
    for q in unroll(0, 21):
        next_leaf = StackBuf(2)
        blake3(leaf, tips[2 * q:2 * q + 2], next_leaf)
        leaf = next_leaf

    # Merkle path from the leaf to the root: the hinted slot bit orders the
    # two children at each level; the tweak comes from the bound table.
    node = leaf[0]
    level = 1
    merkle_tweaks = tweak_table * GEN ** 296
    for l in unroll(0, 32):
        bit = merkle_bits[level]
        sibling = StackBuf(1)
        hint_witness(sibling[0:1], "siblings")
        children = StackBuf(2)
        if bit == 0:
            children[0] = node
            children[1] = sibling[0]
        else:
            children[0] = sibling[0]
            children[1] = node
        merkle_tweak_pp = StackBuf(2)
        merkle_tweak_pp[0] = merkle_tweaks[level]
        merkle_tweak_pp[1] = pp
        parent = StackBuf(2)
        blake3(merkle_tweak_pp, children, parent)
        node = parent[0]
        level = level * GEN
    assert node == pk_ptr[1]
    return


def walk(value, chain_tweaks, pp, k: Const):
    # Walk WOTS chain steps k..6: value' = H(tweak|pp, value|0), the step
    # tweaks read off the bound subtable (cursor advanced to step k first).
    tweak_cur = chain_tweaks
    for a in unroll(0, k):
        tweak_cur = tweak_cur * GEN
    block = StackBuf(2)
    block[0] = value
    block[1] = 0
    for s in unroll(k, 7):
        step_tweak = StackBuf(2)
        step_tweak[0] = tweak_cur[1]
        step_tweak[1] = pp
        out = StackBuf(2)
        blake3(step_tweak, block, out)
        block = StackBuf(2)
        block[0] = out[0]
        block[1] = 0
        tweak_cur = tweak_cur * GEN
    return block[0], k
