<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-750%20XMSS%2Fs-brightgreen?style=for-the-badge" alt="Aggregation: 750 XMSS/s"></a>
  <a href="#recursion"><img src="https://img.shields.io/badge/2%20to%201%20recursion-0.73s-orange?style=for-the-badge" alt="2 to 1 recursion: 0.73s"></a>
</p>

Warning: highly experimental.

# Benchmarks

Machine: Mac M4 Max

### XMSS aggregation

Our XMSS is specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/XMSS.pdf).

```bash
cargo run --release -- xmss --n-signatures 900 --log-inv-rate 1 --repeat 3
```

```
XMSS aggregation, 900 signatures
  cycles (VM steps)           : 1,546,157 = 2^20.56
    proven rows               : 1,967,104 = 2^20.908  (filled to powers of two)
    details                   : DEREF 2^18.988 (33.6%)  SET 2^18.416 (22.6%)  MUL 2^18.198 (19.5%)  SHA2 2^16.995 (8.4%)  XOR 2^16.96 (8.2%)  JUMP 2^16.831 (7.5%)  PACK64X2 2^9.943 (0.1%)  MEMORY 2^21.726  TOTAL_COMMITTED 2^26.718
  signers                     : 900
  proof size                  : 333.2 KiB
  aggregating                 : 1.169 s ± 5.2%      peak memory 22.168 GiB
  per signature               : 769.853 XMSS/s
  verifying                   : 0.0119 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 signatures
  cycles (VM steps)           : 800,125 = 2^19.61
    proven rows               : 1,196,032 = 2^20.19  (filled to powers of two)
    details                   : DEREF 2^18.169 (36.8%)  MUL 2^17.826 (29.0%)  XOR 2^17.383 (21.4%)  SET 2^15.581 (6.1%)  SHA2 2^14.442 (2.8%)  PACK64X2 2^14.353 (2.6%)JUMP 2^13.27 (1.2%)  MEMORY 2^19.94  TOTAL_COMMITTED 2^25.213
  signers                     : 1,800
  proof size                  : 204.2 KiB
  aggregating                 : 0.66 s ± 2.5%      peak memory 26.302 GiB
  verifying                   : 0.0125 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,881
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964  TOTAL_COMMITTED 2^25.263
  proof size                  : 286.1 KiB
  proving                     : 0.527 s ± 8.4%   4,041,167 cycles/s      peak memory 7.771 GiB
  verifying                   : 0.00228 s
```

### Batch proving SHA256 compression

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=17 cargo test --release -p flock --test sha2_batch -- --ignored --nocapture
```

```
Flock SHA-256 batch proving, 131,072 compressions (2^17 slots)
  setup (preprocessing, excluded) :     19.2 ms
  witness-gen                     :     44.3 ms ± 22.7%   7.5%
  commit                          :     81.8 ms ± 7.4%   13.9%
  zerocheck                       :    232.5 ms ± 12.2%  39.5%
  lincheck                        :     18.9 ms ± 13.4%   3.2%
  pcs opening                     :    211.4 ms ± 9.3%   35.9%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    544.5 ms ± 7.9%   92.5%
  verify                          :      1.8 ms
  throughput                      :        240,708 compressions/s ± 7.9%
  (~1648.7 XMSS/s equivalent at 146 compressions/signature)
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving SHA-256 by [Flock](https://github.com/succinctlabs/flock/tree/main)
- RingSwitching, M3 arithmetisation, (and more) by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))

