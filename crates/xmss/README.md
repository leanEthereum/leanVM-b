# XMSS over BLAKE3, specification

The complete scheme specification is [`doc/xmss/main.tex`](../../doc/xmss/main.tex).

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

where `index` is the epoch or the Merkle node index, and `sub_position` is the
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

Encoding: `D = H(tweak_encoding, pp, msg | randomness | zeros(8))`. Each of `D`'s two little-endian 64-bit words contains 21 consecutive 3-bit digits and one unused top bit. The 42 digits form `(e_0, .., e_41)`; the encoding is valid exactly when bits 63 and 127 are zero and `sum(e_i) = 194`. The signer grinds the randomness until the encoding is valid, which takes about `2^14` attempts.

## XMSS

`log_lifetime = 32`: Merkle tree of height 32 over the WOTS public-key hashes.
Key generation takes an epoch range; out-of-range nodes are deterministic
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

1208 bytes = `v*n (672) + randomness (24) + log_lifetime*n (512)`.
