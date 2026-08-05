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
  guest cycles (VM steps)     :        869,886 =   2^19.73   (0.295 / inner cycle)
    XOR    instructions     :        215,490 =  2^17.717
    MUL    instructions     :        268,787 =  2^18.036
    SET    instructions     :         70,556 =  2^16.106
    DEREF  instructions     :        265,183 =  2^18.017
    JUMP   instructions     :          9,299 =  2^13.183
    BLAKE3 instructions     :         18,115 =  2^14.145
    PACK64X2 instructions     :         22,456 =  2^14.455
  committed witness size      : 2^25.506
  data memory                 : 2^21 padded (2^20.044 used)
  recursive proof size        : 235.305 KiB
  outer proving               : 1.26 s
  complete recursive verify   : 0.0303 s
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,034,017
    XOR   instructions        : 2^10.966
    MUL   instructions        : 2^20.937
    SET   instructions        : 2^12.552
    DEREF instructions        : 2^13.967
    JUMP  instructions        : 2^10.968
    BLAKE3 instructions        : 0
    PACK64X2 instructions        : 0
  committed witness size      : 2^25.658
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
