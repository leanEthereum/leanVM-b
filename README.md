<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./misc/images/banner-b.svg">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/spec-latest/doc.pdf"><img src="https://img.shields.io/badge/Documentation-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Documentation"></a>
</p>

- WARNING: Highly experimental / sloppy (currently).
- Proving architecture is volontarily kept simple for now


## XMSS aggregation benchmark

`RAYON_NUM_THREADS=10 LEANVM_XMSS_N=1024 cargo test --release --test xmss_vm -- --nocapture`

```
XMSS aggregation, 1024 signatures
  cycles (VM steps)           :    3530378 = 2^21.75   (  3447.6 / XMSS)
    XOR    instructions       :      79873 = 2^16.29   (    78.0 / XMSS)
    MUL    instructions       :    1383141 = 2^20.40   (  1350.7 / XMSS)
    SET    instructions       :    1048956 = 2^20.00   (  1024.4 / XMSS)
    DEREF  instructions       :     585083 = 2^19.16   (   571.4 / XMSS)
    JUMP   instructions       :     271352 = 2^18.05   (   265.0 / XMSS)
    BLAKE3 instructions       :     161973 = 2^17.31   (   158.2 / XMSS)
  committed witness size      : 2^26.956
  proof size                  : 527.8 KiB
  proving (incl. witness gen) : 4.168371291s
  verifying                   : 6.717958ms
  throughput                  : 245.7 XMSS/s
```

## Fibonacci benchmark

`RAYON_NUM_THREADS=10 cargo run --release`

M4 Max:

```
Fibonacci (in the exponent, i.e. modulo 2^128 - 1), N = 2000000
  cycles (VM steps)           : 2052091
    XOR   instructions        : 2^10.977
    MUL   instructions        : 2^20.943
    SET   instructions        : 2^13.776
    DEREF instructions        : 2^13.968
    JUMP  instructions        : 2^11.967
    BLAKE3 instructions        : 0
  committed witness size      : 2^25.108
  proof size                  : 493.7 KiB
  proving (incl. witness gen) : 1.202985166s
  verifying                   : 6.568208ms
  throughput                  : 1705832 cycles/s
```

## Hash chain benchmark (BLAKE3)

`RAYON_NUM_THREADS=10 LEANVM_HASH_UNROLL=1000 LEANVM_HASH_N=128000 cargo test --release --package leanvm-b --test hash_chain -- blake3_hash_chain --nocapture`

```
BLAKE3 hash chain, N = 128000, unroll = 1000
  cycles (VM steps)           : 131359
    XOR    instructions       : 2^7.000
    MUL    instructions       : 2^10.008
    SET    instructions       : 2^9.828
    DEREF  instructions       : 2^10.014
    JUMP   instructions       : 2^8.011
    BLAKE3 instructions       : 2^16.966
  committed witness size      : 2^24.206
  proof size                  : 465.1 KiB
  proving (incl. witness gen) : 523.120292ms
  verifying                   : 5.520167ms
  throughput                  : 244686 hashes/s
```


## Security, proof size etc

- security = 100 bits, proven, LDR, Ligerito
- proof size = BIG (≈ 0.5 MiB)

Both will be improved later.

## Credits

- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
- [flock](https://github.com/succinctlabs/flock/tree/main)
