<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-780%20XMSS%2Fs-brightgreen?style=for-the-badge" alt="Aggregation: 780 XMSS/s"></a>
  <a href="#recursion"><img src="https://img.shields.io/badge/2%20to%201%20recursion-0.6s-orange?style=for-the-badge" alt="2 to 1 recursion: 0.6s"></a>
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
  cycles (VM steps)           : 1,542,699 = 2^20.557
    proven rows               : 1,968,128 = 2^20.908  (filled to powers of two)
    details                   : DEREF 2^18.988 (33.7%)  SET 2^18.402 (22.4%)  MUL 2^18.198 (19.5%)  BLAKE2S 2^16.996 (8.5%)  XOR 2^16.959 (8.3%)  JUMP 2^16.831 (7.6%)  PACK64X2 2^10.003 (0.1%)  MEMORY 2^21.725  TOTAL_COMMITTED 2^26.195
  signers                     : 900
  proof size                  : 385.6 KiB
  aggregating                 : 1.151 s ± 2.2%      peak memory 20.772 GiB
  per signature               : 781.846 XMSS/s
  verifying                   : 0.0164 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 signatures
  cycles (VM steps)           : 831,759 = 2^19.666
    proven rows               : 1,196,032 = 2^20.19  (filled to powers of two)
    details                   : DEREF 2^18.208 (36.4%)  MUL 2^17.929 (30.0%)  XOR 2^17.427 (21.2%)  SET 2^15.561 (5.8%)  BLAKE2S 2^14.482 (2.8%)  PACK64X2 2^14.418 (2.6%)  JUMP 2^13.273 (1.2%)  MEMORY 2^19.993  TOTAL_COMMITTED 2^24.863
  signers                     : 1,800
  proof size                  : 279.2 KiB
  aggregating                 : 0.598 s ± 2.4%      peak memory 26.155 GiB
  verifying                   : 0.0156 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,881
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964  TOTAL_COMMITTED 2^25.263
  proof size                  : 333.0 KiB
  proving                     : 0.63 s ± 9.3%   3,380,073 cycles/s      peak memory 12.128 GiB
  verifying                   : 0.00298 s
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
