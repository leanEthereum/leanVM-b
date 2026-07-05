<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./misc/images/banner-b.svg">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/spec-latest/doc.pdf"><img src="https://img.shields.io/badge/Documentation-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Documentation"></a>
</p>

- WARNING: Highly experimental / sloppy (currently).
- Proving architecture is volontarily kept simple for now

# Benchmarks

Machine: M4 Max

## XMSS aggregation

`RAYON_NUM_THREADS=10 LEANVM_XMSS_N=820 cargo test --release --test xmss_vm -- --nocapture`

```
XMSS aggregation, 820 signatures
  cycles (VM steps)           :    2029286 = 2^20.95   (  2474.7 / XMSS)
    XOR    instructions       :      63961 = 2^15.96   (    78.0 / XMSS)
    MUL    instructions       :     665036 = 2^19.34   (   811.0 / XMSS)
    SET    instructions       :     484634 = 2^18.89   (   591.0 / XMSS)
    DEREF  instructions       :     468599 = 2^18.84   (   571.5 / XMSS)
    JUMP   instructions       :     217315 = 2^17.73   (   265.0 / XMSS)
    BLAKE3 instructions       :     129741 = 2^16.99   (   158.2 / XMSS)
  committed witness size      : 2^25.872
  proof size                  : 716.4 KiB
  proving (incl. witness gen) : 2.510787917s
  verifying                   : 8.257917ms
  throughput                  : 326.6 XMSS/s
```

## Fibonacci

`RAYON_NUM_THREADS=10 cargo run --release`

```
Fibonacci (in the exponent, i.e. modulo 2^128 - 1), N = 2000000
  cycles (VM steps)           : 2054025
    XOR   instructions        : 2^10.966
    MUL   instructions        : 2^20.944
    SET   instructions        : 2^13.774
    DEREF instructions        : 2^13.967
    JUMP  instructions        : 2^11.967
    BLAKE3 instructions        : 0
  committed witness size      : 2^25.108
  proof size                  : 715.8 KiB
  proving (incl. witness gen) : 1.31697125s
  verifying                   : 7.348958ms
  throughput                  : 1559658 cycles/s
```

## Hash chain (BLAKE3)

`RAYON_NUM_THREADS=10 LEANVM_HASH_UNROLL=1000 LEANVM_HASH_N=128000 cargo test --release --package leanvm-b --test hash_chain -- blake3_hash_chain --nocapture`

```
BLAKE3 hash chain, N = 128000, unroll = 1000
  cycles (VM steps)           : 131487
    XOR    instructions       : 2^7.000
    MUL    instructions       : 2^10.177
    SET    instructions       : 2^9.828
    DEREF  instructions       : 2^10.014
    JUMP   instructions       : 2^8.011
    BLAKE3 instructions       : 2^16.966
  committed witness size      : 2^24.206
  proof size                  : 671.7 KiB
  proving (incl. witness gen) : 583.345167ms
  verifying                   : 6.411209ms
  throughput                  : 219424 hashes/s
```


## Security, proof size etc

- security = 120 bits, proven, UDR, Ligerito
- proof size = BIG (≈ 0.7 MiB)

Both will be improved later.

## Credits

- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
- [flock](https://github.com/succinctlabs/flock/tree/main)
