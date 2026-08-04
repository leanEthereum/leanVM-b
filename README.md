<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Documentation"></a>
</p>

Warning: highly experimental.

# Benchmarks

Machine: Mac M4 Max

### XMSS aggregation

```bash
cargo run --release -- xmss --n-signatures 890 --log-inv-rate 1 --repeat 3
```

```
XMSS aggregation, 890 signatures
  cycles (VM steps)           : 1,513,580 = 2^20.53   (1,700.652 / XMSS)
    details                   : DEREF 2^18.956 (33.6%)  SET 2^18.383 (22.6%)  MUL 2^18.16 (19.3%)  BLAKE3 2^16.989 (8.6%)  XOR 2^16.937 (8.3%)  JUMP 2^16.809 (7.6%)  MEMORY 2^21.701  TOTAL_COMMITTED 2^26.364
  proof size                  : 359.6 KiB
  proving                     : 1.262 s ± 5.4%   705.247 XMSS/s      peak memory 21.288 GiB
  verifying                   : 0.00314 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1: 2 inner proofs of 1,472,224 cycles each
  guest cycles (VM steps)     : 832,542 = 2^19.667   (0.283 / inner cycle)
    details                   : DEREF 2^18.109 (33.9%)  MUL 2^17.965 (30.7%)  XOR 2^17.562 (23.2%)  SET 2^15.63 (6.1%)  PACK64X2 2^14.455 (2.7%)  BLAKE3 2^14.145 (2.2%)  JUMP 2^13.183 (1.1%)  MEMORY 2^19.991  TOTAL_COMMITTED 2^25.155
  proof size                  : 233.0 KiB
recursion proving         : 0.826 s ± 7.7%      peak memory 14.574 GiB
verification              : 0.0281 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,034,017
    details                   : MUL 2^20.937 (98.7%)  DEREF 2^13.967 (0.8%)  SET 2^12.552 (0.3%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.964  TOTAL_COMMITTED 2^25.658
  proof size                  : 336.4 KiB
  proving                     : 0.647 s ± 4.9%   3,142,652 cycles/s      peak memory 11.52 GiB
  verifying                   : 0.0023 s
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
