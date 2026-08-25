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
cargo run --release -- aggregate --xmss 205 --log-inv-rate 1 --repeat 3
```

```
aggregation, 205 XMSS signatures
  cycles (VM steps)           : 528,117 = 2^19.01
    details                   : SET 2^17.523 (35.7%)  MUL 2^17.018 (25.1%)  DEREF 2^16.86 (22.5%)  KECCAK 2^14.966 (6.1%)  XOR 2^14.835 (5.5%)  JUMP 2^14.713 (5.1%)  MEMORY 2^20.838  TOTAL_COMMITTED 2^25.656
  proof size                  : 308.4 KiB
  proving time                : 0.764 s ± 2.3%      peak memory 8.832 GiB
  per signature               : 268.236 signatures/s
  verifying                   : 0.0145 s
```

### SPHINCS aggregation

Our SPHINCS is specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/SPHINCS.pdf).

```bash
cargo run --release -- aggregate --sphincs 55 --log-inv-rate 1 --repeat 3
```

```
aggregation, 55 SPHINCS signatures
  cycles (VM steps)           : 778,768 = 2^19.571
    details                   : SET 2^17.625 (26.0%)  MUL 2^17.602 (25.5%)  XOR 2^17.315 (20.9%)  DEREF 2^17.3 (20.7%)  KECCAK 2^14.937 (4.0%)  JUMP 2^14.418 (2.8%)  MEMORY 2^20.924  TOTAL_COMMITTED 2^25.797
  proof size                  : 316.9 KiB
  proving time                : 0.854 s ± 9.4%      peak memory 9.531 GiB
  per signature               : 64.387 signatures/s
  verifying                   : 0.0249 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 450 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 450 XMSS signatures
  cycles (VM steps)           : 951,746 = 2^19.86
    details                   : MUL 2^18.232 (32.4%)  DEREF 2^18.219 (32.0%)  XOR 2^17.636 (21.4%)  SET 2^16.314 (8.6%)  JUMP 2^14.888 (3.2%)  KECCAK 2^14.509 (2.4%)  MEMORY 2^20.44  TOTAL_COMMITTED 2^25.967
  proof size                  : 228.9 KiB
  proving time                : 1.378 s ± 14.8%      peak memory 35.494 GiB
  verifying                   : 0.018 s
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

### Batch proving Keccak

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=16 cargo test --release --package flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored
```

```
Flock Keccak-f[1600] batch proving, 65,536 permutations (2^16 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     33.9 ms ± 37.9%   4.4%
  commit                          :    230.2 ms ± 0.9%   29.9%
  zerocheck                       :    192.0 ms ± 4.0%   24.9%
  lincheck                        :     15.4 ms ± 17.6%   2.0%
  pcs opening                     :    299.1 ms ± 6.9%   38.8%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    736.7 ms ± 1.4%   95.6%
  verify                          :      3.3 ms
  throughput                      :         88,956 permutations/s ± 1.4%
  (~644.6 XMSS/s equivalent at 138 permutations/signature)
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving Keccak by [Flock](https://github.com/succinctlabs/flock/tree/main)
- RingSwitching, M3 arithmetisation, (and more) by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))

