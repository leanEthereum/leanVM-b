# XMSS over BLAKE3, specification

## Hash functions

Single-block hashes (chain steps, Merkle nodes): plain BLAKE3, truncated to
`n = 16` bytes:

```
blake3(tweak | pp | payload)[..16]
```

with inputs of 48 bytes (chain step) and 64 bytes (Merkle node).

Multi-block hashes (WOTS public key: 42 chain tips = 672 bytes; message
encoding: `msg (32) | randomness (24) | zeros (8)`): a Merkle-Damgard mode
over

```
H: {0,1}^512 -> {0,1}^256,   H(x) = BLAKE3(x)
```

where the 32-byte state starts at `IV = tweak | pp` and absorbs 32-byte blocks
via `state <- H(state | block)`; the final state is truncated to 16 bytes.

The 16-byte tweak, little-endian:

```
[tweak_type (1) | sub_position (4) | index (4) | zeros (7)]
```

where `index` is the slot or the Merkle node index, and `sub_position` is the
chain position or the Merkle level. Tweak types: `chain = 0`, `wots_pk = 1`,
`merkle = 2`, `encoding = 3`.

## Sizes (bytes)

- `n = 16`: digest
- `|pp| = 16`: public parameter
- `|randomness| = 24`
- `|msg| = 32`: message

## WOTS

- `v = 42` chains, `w = 3`, `chain_length = 2^w = 8`
- `target_sum = 194`

Encoding: `D = MD(msg | randomness)` under the encoding tweak. `D`'s 128 bits,
split little-endian into 42 chunks of 3 bits, are the encoding
`(e_0, .., e_41)`; valid iff the 2 leftover top bits (126, 127) are zero and
`sum(e_i) = 194`. The signer grinds the randomness until valid (~2^14
attempts).

## XMSS

`log_lifetime = 32`: Merkle tree of height 32 over the WOTS public-key hashes.
Key generation takes a slot range; out-of-range nodes are deterministic
pseudo-random fillers.

## Keys

- Secret key: a 32-byte seed. All secret material (WOTS pre-images, public
  parameter, filler nodes) is derived from it with a PRF
  (`blake3::keyed_hash`).
- Public key: 32 bytes, `merkle_root (16) | pp (16)`.

## Verification cost

A constant 155 compressions per signature: 2 (encoding) + 100 (chain walks,
fixed by the target sum) + 21 (WOTS public-key hash) + 32 (Merkle path).

## Signature size

1208 bytes = `randomness (24) + v*n (672) + log_lifetime*n (512)`.
