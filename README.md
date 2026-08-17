<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-800%20XMSS%2Fs-brightgreen?style=for-the-badge" alt="Aggregation: 800 XMSS/s"></a>
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
  proof size                  : 352.4 KiB
  aggregating                 : 1.109 s ± 4.8%      peak memory 20.748 GiB
  per signature               : 811.784 XMSS/s
  verifying                   : 0.0117 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 signatures
  cycles (VM steps)           : 798,539 = 2^19.607
    proven rows               : 1,196,032 = 2^20.19  (filled to powers of two)
    details                   : DEREF 2^18.168 (36.9%)  MUL 2^17.825 (29.1%)  XOR 2^17.383 (21.4%)  SET 2^15.55 (6.0%)  BLAKE2S 2^14.44 (2.8%)  PACK64X2 2^14.349 (2.6%)  JUMP 2^13.272 (1.2%)  MEMORY 2^19.938  TOTAL_COMMITTED 2^24.863
  signers                     : 1,800
  proof size                  : 218.2 KiB
  aggregating                 : 0.585 s ± 3.4%      peak memory 26.095 GiB
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
  proof size                  : 332.5 KiB
  proving                     : 0.608 s ± 6.6%   3,499,102 cycles/s      peak memory 12.112 GiB
  verifying                   : 0.00372 s
```

### Batch proving BLAKE2s

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release -p flock --test blake2s_batch -- --ignored --nocapture
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :   2169.8 ms
  witness-gen                     :     60.7 ms ± 20.0%   9.2%
  commit                          :     97.2 ms ± 4.5%   14.8%
  zerocheck                       :    244.2 ms ± 3.7%   37.1%
  lincheck                        :     25.1 ms ± 12.8%   3.8%
  pcs opening                     :    231.7 ms ± 11.2%  35.2%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    598.2 ms ± 5.6%   90.8%
  verify                          :      2.2 ms
  throughput                      :        438,204 compressions/s ± 5.6%
  (~3001.4 XMSS/s equivalent at 146 compressions/signature)
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
