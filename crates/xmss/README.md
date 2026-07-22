# XMSS over BLAKE3, specification

## Hash functions

Every XMSS hash is standard BLAKE3 of an exact byte string:

```
H(tweak, pp, payload) = BLAKE3(tweak | pp | payload)[..16]
```

The 48-byte chain-step input takes one compression; the 64-byte Merkle-node
input takes one; the 96-byte message-encoding input takes two; and the
704-byte WOTS public-key input takes eleven. The VM supplies the standard IV,
chaining value, chunk position, exact block length, and flags to each BLAKE3
compression instruction.

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

`log_lifetime = 32`: Merkle tree of height 32 over the WOTS public-key hashes.
Key generation takes a slot range; out-of-range nodes are deterministic
pseudo-random fillers.

## Keys

- Secret key: a 32-byte seed. All secret material (WOTS pre-images, public
  parameter, filler nodes) is derived from it with a PRF
  (`blake3::keyed_hash`).
- Public key: 32 bytes, `merkle_root (16) | pp (16)`.

## Verification cost

A constant 145 compressions per signature: 2 (encoding) + 100 (chain walks,
fixed by the target sum) + 11 (WOTS public-key hash) + 32 (Merkle path).

## Signature size

1208 bytes = `randomness (24) + v*n (672) + log_lifetime*n (512)`.
