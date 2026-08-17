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
  proof size                  : 353.2 KiB
  aggregating                 : 1.203 s ± 5.1%      peak memory 24.13 GiB
  per signature               : 748.246 XMSS/s
  verifying                   : 0.0133 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 signatures
  cycles (VM steps)           : 800,007 = 2^19.61
    proven rows               : 1,196,032 = 2^20.19  (filled to powers of two)
    details                   : DEREF 2^18.168 (36.8%)  MUL 2^17.826 (29.0%)  XOR 2^17.383 (21.4%)  SET 2^15.581 (6.1%)  SHA2 2^14.442 (2.8%)  PACK64X2 2^14.353 (2.6%)  JUMP 2^13.27 (1.2%)  MEMORY 2^19.94  TOTAL_COMMITTED 2^25.213
  signers                     : 1,800
  proof size                  : 226.3 KiB
  aggregating                 : 0.736 s ± 4.2%      peak memory 28.47 GiB
  verifying                   : 0.0127 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,881
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964  TOTAL_COMMITTED 2^25.263
  proof size                  : 331.3 KiB
  proving                     : 0.567 s ± 4.9%   3,755,763 cycles/s      peak memory 10.016 GiB
  verifying                   : 0.00392 s
```

### Batch proving SHA256 compression

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=17 cargo test --release -p flock --test sha2_batch -- --ignored --nocapture
```

```
Flock SHA-256 batch proving, 131,072 compressions (2^17 slots)
  setup (preprocessing, excluded) :     18.8 ms
  witness-gen                     :     54.3 ms ± 5.9%    9.1%
  commit                          :     78.0 ms ± 3.7%   13.1%
  zerocheck                       :    232.8 ms ± 8.4%   39.1%
  lincheck                        :     19.1 ms ± 16.9%   3.2%
  pcs opening                     :    210.5 ms ± 12.6%  35.4%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    540.4 ms ± 8.0%   90.9%
  verify                          :      1.7 ms
  throughput                      :        242,533 compressions/s ± 8.0%
  (~1661.2 XMSS/s equivalent at 146 compressions/signature)
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
