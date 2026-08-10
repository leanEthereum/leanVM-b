<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<p align="center">
  <a href="#xmss-aggregation"><img src="https://img.shields.io/badge/Aggregation-850%20XMSS%2Fs-brightgreen?style=for-the-badge" alt="Aggregation: 750 XMSS/s"></a>
  <a href="#recursion"><img src="https://img.shields.io/badge/2%20to%201%20recursion-0.48s-orange?style=for-the-badge" alt="2 to 1 recursion: 0.55s"></a>
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
  cycles (VM steps)           : 1,528,252 = 2^20.543   (1,698.058 / XMSS)
    proven rows               : 1,966,081 = 2^20.907  (filled to powers of two)
    details                   : DEREF 2^18.97 (33.6%)  SET 2^18.397 (22.6%)  MUL 2^18.176 (19.4%)  BLAKE3 2^16.996 (8.6%)  XOR 2^16.953 (8.3%)  JUMP 2^16.825 (7.6%)  MEMORY 2^21.718  TOTAL_COMMITTED 2^26.185
  proof size                  : 356.0 KiB
  proving                     : 1.055 s ± 2.9%   852.69 XMSS/s      peak memory 18.717 GiB
  verifying                   : 0.00366 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1: 2 inner proofs of 1,472,223 cycles each
  guest cycles (VM steps)     : 727,289 = 2^19.472   (0.247 / inner cycle)
    proven rows               : 933,888 = 2^19.833  (filled to powers of two)
    details                   : DEREF 2^17.975 (35.4%)  MUL 2^17.753 (30.4%)  XOR 2^17.321 (22.5%)  SET 2^15.252 (5.4%)  PACK64X2 2^14.305 (2.8%)  BLAKE3 2^14.088 (2.4%)  JUMP 2^13.016 (1.1%)  MEMORY 2^19.802  TOTAL_COMMITTED 2^24.664
  proof size                  : 223.6 KiB
recursion proving         : 0.481 s ± 5.4%      peak memory 12.965 GiB
verification              : 0.0278 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,881
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964 TOTAL_COMMITTED 2^25.263
  proof size                  : 334.6 KiB
  proving                     : 0.584 s ± 2.7%   3,640,905 cycles/s      peak memory 10.48 GiB
  verifying                   : 0.00284 s
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
