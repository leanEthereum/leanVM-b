# The in-VM XMSS aggregation verifier. The public input is the first 16 bytes
# (two 64-bit words) of the 32-byte Merkle-Damgard state (IV = g^{num_bytes} |
# 0^24) of
#     message | tweaks | merkle_bits | public keys,
# num_bytes = 5792 + 32·n, with n (the signature count) hinted in the exponent
# and range checked. The fixed part (1 + 164 + 16 = 181 blocks) is hinted,
# absorbed, and stored into buffers — so everything a verification later reads
# is bound by the hash the outer verifier recomputes. One runtime loop absorbs
# each public key block and verifies its signature (same message and slot for
# all). The IV size element is computed from n directly (the loop absorbs
# exactly n pk blocks, so it needs no separate hint or consistency check).
#
# Every 16-byte native value (tweak, digest, chain tip, sibling, pp) spans TWO
# 64-bit cells; a 32-byte hash block spans FOUR. Tweak table layout (tweak
# index t at cells g^{2t}, g^{2t+1}):
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
    iv = StackBuf(4)
    iv[0] = GEN ** 5792 * pk_bytes  # g^{5792 + 32·n_sigs}
    iv[1] = 0
    iv[2] = 0
    iv[3] = 0

    # Buffers for the common (per-batch) data — message, the 656-cell tweak
    # table (328 two-cell tweaks), the 64-cell merkle-bit decomposition (32
    # two-cell words). Each block below is hinted, absorbed into the hash, AND
    # stored, which binds it to the public input.
    message = HeapBuf(4)
    tweak_table = HeapBuf(656)
    merkle_bits = HeapBuf(64)

    msg_block = StackBuf(4)
    hint_witness(msg_block, "msg")
    message[1] = msg_block[0]
    message[GEN] = msg_block[1]
    message[GEN ** 2] = msg_block[2]
    message[GEN ** 3] = msg_block[3]
    state = StackBuf(4)
    blake3(iv, msg_block, state)

    tweak_slot = 1  # tweak_table cell cursor: g^0, g^4, g^8, … (4 cells / block)
    for t in unroll(0, 164):
        block = StackBuf(4)
        hint_witness(block, "tweaks")
        tweak_table[tweak_slot] = block[0]
        tweak_table[tweak_slot * GEN] = block[1]
        tweak_table[tweak_slot * GEN ** 2] = block[2]
        tweak_table[tweak_slot * GEN ** 3] = block[3]
        tweak_slot = tweak_slot * GEN ** 4
        next_state = StackBuf(4)
        blake3(state, block, next_state)
        state = next_state

    bit_slot = 1
    for u in unroll(0, 16):
        block = StackBuf(4)
        hint_witness(block, "merkle_bits")
        merkle_bits[bit_slot] = block[0]
        merkle_bits[bit_slot * GEN] = block[1]
        merkle_bits[bit_slot * GEN ** 2] = block[2]
        merkle_bits[bit_slot * GEN ** 3] = block[3]
        bit_slot = bit_slot * GEN ** 4
        next_state = StackBuf(4)
        blake3(state, block, next_state)
        state = next_state

    # Per-signature buffers, sized in the exponent from n_sigs (see HeapBuf
    # docs): the MD state and each pk block take a 4-cell slot per signature
    # (slot k at g^{4k}..g^{4k+3}), so n_sigs^4·g^4 cells.
    n_sigs_4 = n_sigs * n_sigs * n_sigs * n_sigs  # g^{4·n_sigs}
    agg_states = HeapBuf(n_sigs_4 * GEN ** 4)
    pubkeys = HeapBuf(n_sigs_4 * GEN ** 4)
    agg_states[1] = state[0]
    agg_states[GEN] = state[1]
    agg_states[GEN ** 2] = state[2]
    agg_states[GEN ** 3] = state[3]
    for j in mul_range(1, n_sigs):
        slot = j * j * j * j  # signature k occupies cells g^{4k}..g^{4k+3}
        hint_witness(pubkeys[slot:slot + 4], "pks")
        blake3(agg_states[slot:slot + 4], pubkeys[slot:slot + 4], agg_states[slot * GEN ** 4:slot * GEN ** 4 + 4])
        verify_sig(message, tweak_table, merkle_bits, pubkeys * slot)

    # Publish the first two words of the final MD state = the aggregation
    # public input.
    final_slot = n_sigs_4
    public_input = GEN ** 0
    public_input[1] = agg_states[final_slot]
    public_input[GEN] = agg_states[final_slot * GEN]
    return


def verify_sig(message, tweak_table, merkle_bits, pk_ptr):
    # pk_ptr[g^0..g^1] is the signer's merkle root, pk_ptr[g^2..g^3] its
    # public parameter (two 64-bit words each).
    pp0 = pk_ptr[GEN ** 2]
    pp1 = pk_ptr[GEN ** 3]

    # Encoding digest D = MD(tweak|pp, msg, randomness): IV = g^96 | 0.
    enc_iv = StackBuf(4)
    enc_iv[0] = GEN ** 96
    enc_iv[1] = 0
    enc_iv[2] = 0
    enc_iv[3] = 0
    tweak_pp = StackBuf(4)
    tweak_pp[0] = tweak_table[1]
    tweak_pp[1] = tweak_table[GEN]
    tweak_pp[2] = pp0
    tweak_pp[3] = pp1
    after_tweak = StackBuf(4)
    blake3(enc_iv, tweak_pp, after_tweak)
    msg_block = StackBuf(4)
    msg_block[0] = message[1]
    msg_block[1] = message[GEN]
    msg_block[2] = message[GEN ** 2]
    msg_block[3] = message[GEN ** 3]
    after_msg = StackBuf(4)
    blake3(after_tweak, msg_block, after_msg)
    rand_block = StackBuf(4)
    hint_witness(rand_block, "rand")
    digest = StackBuf(4)
    blake3(after_msg, rand_block, digest)

    # 42 WOTS chains. Per chain: the digit is hinted in the exponent (g^{e_i}),
    # range checked, and dispatched once — arm k walks the remaining 7-k steps
    # and returns the two tip words plus the digit literal. The product of the
    # digits is the target sum (g^{Σe_i}); the digits, weighted by 8^i inside
    # each 64-bit word (21 digits per word, GF(2^64)'s monomial budget, with
    # each word's leftover top bit ground to zero by the signer), reconstruct
    # D's two words.
    tips = StackBuf(84)
    digit_product = 1
    chain_tweaks = tweak_table * GEN ** 2  # chain i's tweaks start at cell 2·(1+7i)
    acc_lo = 0
    weight = 1
    for i in unroll(0, 21):
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < 8
        chain_start = StackBuf(2)
        hint_witness(chain_start, "chain_starts")
        t0, t1, e = match_range(log(digit[0]), range(0, 8), lambda k: walk(chain_start[0], chain_start[1], chain_tweaks, pp0, pp1, k))
        tips[2 * i] = t0
        tips[2 * i + 1] = t1
        digit_product = digit_product * digit[0]
        acc_lo = acc_lo + e * weight  # e_i in its monomial subspace of word 0
        weight = weight * 8
        chain_tweaks = chain_tweaks * GEN ** 14
    acc_hi = 0
    weight = 1
    for i in unroll(21, 42):
        digit = StackBuf(1)
        hint_witness(digit[0:1], "digits")
        assert log(digit[0]) < 8
        chain_start = StackBuf(2)
        hint_witness(chain_start, "chain_starts")
        t0, t1, e = match_range(log(digit[0]), range(0, 8), lambda k: walk(chain_start[0], chain_start[1], chain_tweaks, pp0, pp1, k))
        tips[2 * i] = t0
        tips[2 * i + 1] = t1
        digit_product = digit_product * digit[0]
        acc_hi = acc_hi + e * weight  # e_i in its monomial subspace of word 1
        weight = weight * 8
        chain_tweaks = chain_tweaks * GEN ** 14
    assert digit_product == GEN ** 194
    assert acc_lo == digest[0]
    assert acc_hi == digest[1]

    # WOTS public-key hash: MD over the 42 tips, IV = g^704 | 0 — the leaf.
    leaf_iv = StackBuf(4)
    leaf_iv[0] = GEN ** 704
    leaf_iv[1] = 0
    leaf_iv[2] = 0
    leaf_iv[3] = 0
    pk_tweak_pp = StackBuf(4)
    pk_tweak_pp[0] = tweak_table[GEN ** 590]
    pk_tweak_pp[1] = tweak_table[GEN ** 591]
    pk_tweak_pp[2] = pp0
    pk_tweak_pp[3] = pp1
    leaf = StackBuf(4)
    blake3(leaf_iv, pk_tweak_pp, leaf)
    for q in unroll(0, 21):
        next_leaf = StackBuf(4)
        blake3(leaf, tips[4 * q:4 * q + 4], next_leaf)
        leaf = next_leaf

    # Merkle path from the leaf to the root: the hinted slot bit orders the
    # two children at each level; the tweak comes from the bound table. The
    # cursor g^{2l} indexes both two-cell tables (bit l, tweak word 296+l).
    node0 = leaf[0]
    node1 = leaf[1]
    lvl = 1
    merkle_tweaks = tweak_table * GEN ** 592
    for l in unroll(0, 32):
        bit = merkle_bits[lvl]
        sibling = StackBuf(2)
        hint_witness(sibling, "siblings")
        children = StackBuf(4)
        if bit == 0:
            children[0] = node0
            children[1] = node1
            children[2] = sibling[0]
            children[3] = sibling[1]
        else:
            children[0] = sibling[0]
            children[1] = sibling[1]
            children[2] = node0
            children[3] = node1
        merkle_tweak_pp = StackBuf(4)
        merkle_tweak_pp[0] = merkle_tweaks[lvl]
        merkle_tweak_pp[1] = merkle_tweaks[lvl * GEN]
        merkle_tweak_pp[2] = pp0
        merkle_tweak_pp[3] = pp1
        parent = StackBuf(4)
        blake3(merkle_tweak_pp, children, parent)
        node0 = parent[0]
        node1 = parent[1]
        lvl = lvl * GEN ** 2
    assert node0 == pk_ptr[1]
    assert node1 == pk_ptr[GEN]
    return


def walk(value0, value1, chain_tweaks, pp0, pp1, k: Const):
    # Walk WOTS chain steps k..6: value' = H(tweak|pp, value|0), the step
    # tweaks read off the bound subtable (cursor advanced to step k first,
    # two cells per tweak).
    tweak_cur = chain_tweaks
    for a in unroll(0, k):
        tweak_cur = tweak_cur * GEN ** 2
    block = StackBuf(4)
    block[0] = value0
    block[1] = value1
    block[2] = 0
    block[3] = 0
    for s in unroll(k, 7):
        step_tweak = StackBuf(4)
        step_tweak[0] = tweak_cur[1]
        step_tweak[1] = tweak_cur[GEN]
        step_tweak[2] = pp0
        step_tweak[3] = pp1
        out = StackBuf(4)
        blake3(step_tweak, block, out)
        block = StackBuf(4)
        block[0] = out[0]
        block[1] = out[1]
        block[2] = 0
        block[3] = 0
        tweak_cur = tweak_cur * GEN ** 2
    return block[0], block[1], k
