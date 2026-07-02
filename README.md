<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./misc/images/banner-b.svg">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/spec-latest/doc.pdf"><img src="https://img.shields.io/badge/Documentation-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Documentation"></a>
</p>

- WARNING: Highly experimental / sloppy (currently).
- Proving architecture is volontarily kept simple for now

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
  proof size                  : 1196.8 KiB
  proving (incl. witness gen) : 1.136911375s
  verifying                   : 5.152375ms
  throughput                  : 1804970 cycles/s
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
  committed witness size      : 2^24.264
  proof size                  : 1169.7 KiB
  proving (incl. witness gen) : 526.35125ms
  verifying                   : 7.045041ms
  throughput                  : 243184 hashes/s
```


## Security, proof size etc

- security = 100 bits, proven, UDR, Basefold
- proof size =  BIG (≈ 1 MiB)

Both will be improved later.

## Credits

- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
- [flock](https://github.com/succinctlabs/flock/tree/main)
