<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-890%20XMSS%2Fs-brightgreen?style=for-the-badge" alt="Aggregation: 890 XMSS/s"></a>
  <a href="#recursion"><img src="https://img.shields.io/badge/2%20to%201%20recursion-0.58s-orange?style=for-the-badge" alt="2 to 1 recursion: 0.58s"></a>
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
  proof size                  : 304.3 KiB
  aggregating                 : 1.01 s ± 5.1%      peak memory 15.994 GiB
  per signature               : 890.86 XMSS/s
  verifying                   : 0.0122 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 signatures
  cycles (VM steps)           : 798,657 = 2^19.607
    proven rows               : 1,196,032 = 2^20.19  (filled to powers of two)
    details                   : DEREF 2^18.168 (36.9%)  MUL 2^17.825 (29.1%)  XOR 2^17.383 (21.4%)  SET 2^15.55 (6.0%)  BLAKE2S 2^14.44 (2.8%)  PACK64X2 2^14.349 (2.6%) JUMP 2^13.272 (1.2%)  MEMORY 2^19.938  TOTAL_COMMITTED 2^24.863
  signers                     : 1,800
  proof size                  : 214.7 KiB
  aggregating                 : 0.588 s ± 6.2%      peak memory 20.775 GiB
  verifying                   : 0.0142 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,881
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964  TOTAL_COMMITTED 2^25.263
  proof size                  : 284.6 KiB
  proving                     : 0.571 s ± 2.0%   3,726,189 cycles/s      peak memory 9.896 GiB
  verifying                   : 0.00294 s
```

### Batch proving BLAKE2s

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release -p flock --test blake2s_batch -- --ignored --nocapture
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :   2178.2 ms
  witness-gen                     :     52.7 ms ± 41.5%   8.0%
  commit                          :    104.4 ms ± 19.3%  15.9%
  zerocheck                       :    242.5 ms ± 4.2%   36.9%
  lincheck                        :     24.5 ms ± 13.8%   3.7%
  pcs opening                     :    232.4 ms ± 8.1%   35.4%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    603.8 ms ± 1.8%   92.0%
  verify                          :      2.2 ms
  throughput                      :        434,176 compressions/s ± 1.8%
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving BLAKE2s by [Flock](https://github.com/succinctlabs/flock/tree/main)
- RingSwitching, M3 arithmetisation, (and more) by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))

