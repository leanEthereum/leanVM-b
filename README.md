<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

Warning: highly experimental.

# Benchmarks

Machine: Mac M4 Max

### XMSS aggregation

Our XMSS is specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/XMSS.pdf).

```bash
cargo run --release -- aggregate --xmss 450 --log-inv-rate 1 --repeat 3
```

````
aggregation, 450 XMSS signatures
  cycles (VM steps)           : 773,972 = 2^19.562
    details                   : DEREF 2^17.99 (33.6%)  SET 2^17.417 (22.6%)  MUL 2^17.2 (19.5%)  SHA2 2^15.996 (8.4%)  XOR 2^15.963 (8.3%)  JUMP 2^15.844 (7.6%)  MEMORY 2^20.727  TOTAL_COMMITTED 2^25.725
  proof size                  : 311.0 KiB
  proving time                : 0.519 s ± 4.6%      peak memory 9.083 GiB
  per signature               : 866.405 signatures/s
  verifying                   : 0.0169 s
```

### SPHINCS aggregation

Our SPHINCS is specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/SPHINCS.pdf).

```bash
cargo run --release -- aggregate --sphincs 122 --log-inv-rate 1 --repeat 3
```

```
aggregation, 122 SPHINCS signatures
  cycles (VM steps)           : 1,335,535 = 2^20.349
    details                   : DEREF 2^18.446 (26.7%)  XOR 2^18.301 (24.2%)  MUL 2^18.207 (22.7%)  SET 2^17.869 (17.9%)  SHA2 2^15.991 (4.9%)  JUMP 2^15.563 (3.6%)  MEMORY 2^21.085  TOTAL_COMMITTED 2^26.228
  proof size                  : 305.6 KiB
  proving time                : 0.763 s ± 4.3%      peak memory 13.904 GiB
  per signature               : 159.799 signatures/s
  verifying                   : 0.0136 s
```

### Recursion

```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 807,023 = 2^19.622
    details                   : DEREF 2^18.108 (35.0%)  MUL 2^17.872 (29.7%)  XOR 2^17.499 (23.0%)  SET 2^15.571 (6.0%)  JUMP 2^14.806 (3.6%)  SHA2 2^14.424 (2.7%)  MEMORY 2^19.909  TOTAL_COMMITTED 2^25.208
  proof size                  : 202.9 KiB
  proving time                : 0.547 s ± 3.0%      peak memory 25.53 GiB
  verifying                   : 0.0143 s
```

### Fibonacci

```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

### Batch proving SHA-256 compression

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=17 cargo test --release --package flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored
```

```
Flock SHA-256 batch proving, 131,072 compressions (2^17 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     51.2 ms ± 16.3%   9.2%
  commit                          :     85.1 ms ± 2.1%   15.3%
  zerocheck                       :    221.8 ms ± 2.2%   39.8%
  lincheck                        :     19.4 ms ± 15.2%   3.5%
  pcs opening                     :    180.0 ms ± 14.3%  32.3%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    506.3 ms ± 5.2%   90.8%
  verify                          :      1.6 ms
  throughput                      :        258,881 compressions/s ± 5.2%
  (~1773.2 XMSS/s equivalent at 146 compressions/signature)
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## SNARK machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (also known as [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving SHA-256 by [Flock](https://github.com/succinctlabs/flock/tree/main)
- Ring switching, M3 arithmetization, and more by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
