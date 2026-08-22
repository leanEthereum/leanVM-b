<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-1100%20XMSS%2Fs-brightgreen?style=for-the-badge" alt="Aggregation: 1100 XMSS/s"></a>
  <a href="#recursion"><img src="https://img.shields.io/badge/2%20to%201%20recursion-0.45s-orange?style=for-the-badge" alt="2 to 1 recursion: 0.45s"></a>
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
  cycles (VM steps)           : 1,542,617 = 2^20.557
    proven rows               : 1,967,104 = 2^20.908  (filled to powers of two)
    details                   : DEREF 2^18.988 (33.7%)  SET 2^18.402 (22.4%)  MUL 2^18.198 (19.5%)  BLAKE2S 2^16.995 (8.5%)  XOR 2^16.96 (8.3%)  JUMP 2^16.831 (7.6%)  PACK64X2 2^9.938 (0.1%)  MEMORY 2^21.725  TOTAL_COMMITTED 2^26.195
  signers                     : 900
  proof size                  : 304.4 KiB
  aggregating                 : 0.816 s ± 4.2%      peak memory 13.815 GiB
  per signature               : 1,102.621 XMSS/s
  verifying                   : 0.0137 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 signatures
  cycles (VM steps)           : 807,637 = 2^19.623
    proven rows               : 1,179,648 = 2^20.17  (filled to powers of two)
    details                   : DEREF 2^18.108 (35.0%)  MUL 2^17.876 (29.8%)  XOR 2^17.503 (23.0%)  SET 2^15.539 (5.9%)  JUMP 2^14.826 (3.6%)  BLAKE2S 2^14.437 (2.7%)  MEMORY 2^19.911  TOTAL_COMMITTED 2^24.856
  signers                     : 1,800
  proof size                  : 213.4 KiB
  aggregating                 : 0.453 s ± 5.7%      peak memory 17.292 GiB
  verifying                   : 0.016 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,881
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%) JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964  TOTAL_COMMITTED 2^25.263
  proof size                  : 284.7 KiB
  proving                     : 0.41 s ± 2.9%   5,191,741 cycles/s      peak memory 7.482 GiB
  verifying                   : 0.00352 s
```

### Batch proving BLAKE2s

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release -p flock --test blake2s_batch -- --ignored --nocapture
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     51.2 ms ± 23.3%   8.6%
  commit                          :    100.1 ms ± 0.3%   16.8%
  zerocheck                       :    237.0 ms ± 4.2%   39.7%
  lincheck                        :     19.4 ms ± 10.8%   3.3%
  pcs opening                     :    188.9 ms ± 7.1%   31.7%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    545.5 ms ± 3.9%   91.4%
  verify                          :      2.0 ms
  throughput                      :        480,600 compressions/s ± 3.9%
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving BLAKE2s by [Flock](https://github.com/succinctlabs/flock/tree/main)
- RingSwitching, M3 arithmetisation, (and more) by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
