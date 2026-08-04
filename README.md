<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="./doc/main.tex"><img src="https://img.shields.io/badge/Specification-source-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Specification source"></a>
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/spec-latest/doc.pdf"><img src="https://img.shields.io/badge/main-PDF-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Latest main-branch PDF"></a>
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
  proving                     : 1.402 s ± 3.9%   634.605 XMSS/s      peak memory 21.467 GiB
  verifying                   : 0.00378 s
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1: 2 inner proofs of 1,472,224 cycles each
  guest cycles (VM steps)     : 869,888 = 2^19.73   (0.295 / inner cycle)
    details                   : MUL 2^18.036 (30.9%)  DEREF 2^18.017 (30.5%)  XOR 2^17.717 (24.8%)  SET 2^16.107 (8.1%)  PACK64X2 2^14.455 (2.6%)  BLAKE3 2^14.145 (2.1%)  JUMP 2^13.183 (1.1%)  MEMORY 2^20.044  TOTAL_COMMITTED 2^25.506
proof size                : 234.5 KiB
recursion proving         : 0.925 s ± 3.6%      peak memory 14.698 GiB
verification              : 0.0292 s
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
  proving                     : 0.718 s ± 7.6%   2,832,419 cycles/s      peak memory 11.655 GiB
  verifying                   : 0.00299 s
```

## Security

- 128-bit proven (LDR Johnson)

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
