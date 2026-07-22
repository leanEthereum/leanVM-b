# XMSS over BLAKE3, specification

## Hash functions

Every XMSS verification hash is keyed BLAKE3 of an exact payload. The 32-byte
key is the concatenation of the public parameter and tweak:

```
H(tweak, pp, payload) = BLAKE3_keyed(key = pp | tweak, payload)[..16]
```

The 16-byte chain-step payload takes one compression; the 64-byte quaternary
Merkle-node payload takes one; the 64-byte message-encoding payload takes one;
and the 672-byte WOTS public-key payload takes eleven. The VM supplies the key
as the initial chaining value and sets `KEYED_HASH` on every compression,
together with the standard chunk position, exact block length, and flags.

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

Encoding: `D = H(tweak_encoding, pp, msg | randomness | zeros(8))`. `D`'s 128 bits,
split little-endian into 42 chunks of 3 bits, are the encoding
`(e_0, .., e_41)`; valid iff the 2 leftover top bits (126, 127) are zero and
`sum(e_i) = 194`. The signer grinds the randomness until valid (~2^14
attempts).

## XMSS

`log_lifetime = 32`: a 4-ary Merkle tree of height 16 over 2^32 WOTS public-key
hashes. Each authentication level carries the other three children. Key
generation takes a slot range; out-of-range nodes are deterministic pseudo-random
fillers.

## Keys

- Secret key: a 32-byte seed. All secret material (WOTS pre-images, public
  parameter, filler nodes) is derived from it with a PRF
  (`blake3::keyed_hash`).
- Public key: 32 bytes, `merkle_root (16) | pp (16)`.

## Verification cost

A constant 128 compressions per signature: 1 (encoding) + 100 (chain walks,
fixed by the target sum) + 11 (WOTS public-key hash) + 16 (Merkle path).

## Signature size

1464 bytes = `randomness (24) + v*n (672) + 16*3*n (768)`.
