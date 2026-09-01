<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-1100%20XMSS%2Fs-brightgreen?style=for-the-badge"></a>
  <a href="#sphincs-aggregation"><img src="https://img.shields.io/badge/Aggregation-230%20SPHINCS%2Fs-green?style=for-the-badge"></a>
  <a href="#recursion"><img src="https://img.shields.io/badge/2%20to%201%20recursion-0.40s-orange?style=for-the-badge"></a>
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
  cycles (VM steps)           : 1,541,705 = 2^20.556
    details                   : DEREF 2^18.993 (33.9%)  SET 2^18.381 (22.1%)  MUL 2^18.204 (19.6%)  BLAKE2S 2^16.994 (8.5%)  XOR 2^16.97 (8.3%)  JUMP 2^16.843 (7.6%)  MEMORY 2^21.282  TOTAL_COMMITTED 2^26.195
  proof size                  : 295.2 KiB
  proving time                : 0.797 s ± 4.4%      peak memory 9.037 GiB
  per signature               : 1,128.79 signatures/s
  verifying                   : 0.0165 s
```

### SPHINCS aggregation

Our SPHINCS is specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/SPHINCS.pdf).

```bash
cargo run --release -- aggregate --sphincs 245 --log-inv-rate 1 --repeat 3
```

```
aggregation, 245 SPHINCS signatures
  cycles (VM steps)           : 2,602,803 = 2^21.312
    details                   : DEREF 2^19.444 (27.4%)  XOR 2^19.238 (23.8%)  MUL 2^19.216 (23.4%)  SET 2^18.735 (16.8%)  BLAKE2S 2^16.995 (5.0%)  JUMP 2^16.545 (3.7%)  MEMORY 2^21.78  TOTAL_COMMITTED 2^26.664
  proof size                  : 321.5 KiB
  proving time                : 1.053 s ± 1.6%      peak memory 12.634 GiB
  per signature               : 232.661 signatures/s
  verifying                   : 0.0175 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 711,107 = 2^19.44
    details                   : DEREF 2^17.852 (33.3%)  MUL 2^17.731 (30.6%)  XOR 2^17.366 (23.8%)  SET 2^15.258 (5.5%)  JUMP 2^14.804(4.0%)  BLAKE2S 2^14.302 (2.8%)  MEMORY 2^19.722  TOTAL_COMMITTED 2^24.656
  proof size                  : 205.8 KiB
  proving time                : 0.396 s ± 2.5%      peak memory 10.504 GiB
  verifying                   : 0.0158 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,880
    details                   : MUL 2^20.936 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.957  TOTAL_COMMITTED 2^25.263
  proof size                  : 285.4 KiB
  proving                     : 0.4 s ± 4.1%   5,320,879 cycles/s      peak memory 5.14 GiB
  verifying                   : 0.00294 s
```

### Batch proving BLAKE2s

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release --package flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     64.1 ms ± 8.1%   10.6%
  commit                          :    100.5 ms ± 0.7%   16.6%
  zerocheck                       :    243.6 ms ± 7.5%   40.3%
  lincheck                        :     20.7 ms ± 16.6%   3.4%
  pcs opening                     :    175.6 ms ± 2.4%   29.1%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    540.5 ms ± 4.6%   89.4%
  verify                          :      1.9 ms
  throughput                      :        485,033 compressions/s ± 4.6%
  (~3322.1 XMSS/s equivalent at 146 compressions/signature)
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving BLAKE2s by [Flock](https://github.com/succinctlabs/flock/tree/main)
- RingSwitching, M3 arithmetisation, (and more) by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
