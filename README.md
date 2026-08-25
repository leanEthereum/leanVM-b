<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-1100%20XMSS%2Fs-brightgreen?style=for-the-badge"></a>
  <a href="#sphincs-aggregation"><img src="https://img.shields.io/badge/Aggregation-200%20SPHINCS%2Fs-green?style=for-the-badge"></a>
  <a href="#recursion"><img src="https://img.shields.io/badge/2%20to%201%20recursion-0.45s-orange?style=for-the-badge"></a>
</p>

Warning: highly experimental.

# Benchmarks

Machine: Mac M4 Max

### XMSS aggregation

Our XMSS is specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/XMSS.pdf).

```bash
cargo run --release -- aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

```
aggregation, 900 XMSS signatures
  cycles (VM steps)           : 1,542,871 = 2^20.557
    details                   : DEREF 2^18.988 (33.7%)  SET 2^18.402 (22.4%)  MUL 2^18.199 (19.5%)  BLAKE2S 2^16.995 (8.5%)  XOR 2^16.961 (8.3%)  JUMP 2^16.843 (7.6%)  MEMORY 2^21.724  TOTAL_COMMITTED 2^26.195
  proof size                  : 304.5 KiB
  proving time                : 0.821 s ± 2.6%      peak memory 13.956 GiB
  per signature               : 1,096.508 signatures/s
  verifying                   : 0.0135 s
```

### SPHINCS aggregation

Our SPHINCS is specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/SPHINCS.pdf).

```bash
cargo run --release -- aggregate --sphincs 245 --log-inv-rate 1 --repeat 3
```

```
aggregation, 245 SPHINCS signatures
  cycles (VM steps)           : 2,677,883 = 2^21.353
    details                   : DEREF 2^19.45 (26.7%)  XOR 2^19.306 (24.2%)  MUL 2^19.212 (22.7%)  SET 2^18.866 (17.8%)  BLAKE2S 2^16.996 (4.9%)  JUMP 2^16.568 (3.6%)  MEMORY 2^22.089  TOTAL_COMMITTED 2^26.875
  proof size                  : 345.8 KiB
  proving time                : 1.219 s ± 5.2%      peak memory 20.119 GiB
  per signature               : 201.022 signatures/s
  verifying                   : 0.0177 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 807,861 = 2^19.624
    details                   : DEREF 2^18.109 (35.0%)  MUL 2^17.876 (29.8%)  XOR 2^17.503 (23.0%)  SET 2^15.539 (5.9%)  JUMP 2^14.826 (3.6%)  BLAKE2S 2^14.437 (2.7%)  MEMORY 2^19.911  TOTAL_COMMITTED 2^24.856
  proof size                  : 212.7 KiB
  proving time                : 0.453 s ± 4.9%      peak memory 17.287 GiB
  verifying                   : 0.0161 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,880
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964  TOTAL_COMMITTED 2^25.263
  proof size                  : 286.2 KiB
  proving                     : 0.425 s ± 6.9%   5,009,971 cycles/s      peak memory 7.523 GiB
  verifying                   : 0.00315 s
```

### Batch proving BLAKE2s

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release -p flock --test hash_batch -- --ignored --nocapture
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     62.2 ms ± 29.8%  10.1%
  commit                          :    100.2 ms ± 1.2%   16.3%
  zerocheck                       :    234.8 ms ± 1.4%   38.3%
  lincheck                        :     20.5 ms ± 7.7%    3.3%
  pcs opening                     :    195.9 ms ± 3.4%   31.9%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    551.4 ms ± 1.9%   89.9%
  verify                          :      2.0 ms
  throughput                      :        475,423 compressions/s ± 1.9%
  (~3256.3 XMSS/s equivalent at 146 compressions/signature)
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving BLAKE2s by [Flock](https://github.com/succinctlabs/flock/tree/main)
- RingSwitching, M3 arithmetisation, (and more) by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
