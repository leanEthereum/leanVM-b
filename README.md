<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./misc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="./misc/doc.tex"><img src="https://img.shields.io/badge/Specification-source-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Specification source"></a>
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/spec-latest/doc.pdf"><img src="https://img.shields.io/badge/main-PDF-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Latest main-branch PDF"></a>
</p>

- Warning: highly experimental.
- The proving architecture is intentionally kept simple.

# Benchmarks

Measured on an AMD Ryzen 7 PRO 8700GE with 11 Rayon workers. Timings vary by machine; cycles and proof sizes describe the protocol configuration more reliably.

### XMSS aggregation

```bash
RAYON_NUM_THREADS=11 cargo run --release -- xmss --n-signatures 890 --log-inv-rate 1
```

```
XMSS aggregation, 890 signatures
  cycles (VM steps)           :      1,514,472 = 2^20.53   (1,701.7 / XMSS)
  committed witness size      : 2^26.364
  data memory                 : 2^22 padded (2^21.701 used)
  proof size                  : 358.227 KiB
  proving (incl. witness gen) : 6.545 s
  verifying                   : 5.45 ms
  throughput                  : 136.0 XMSS/s
```

### Recursion


```bash
RAYON_NUM_THREADS=11 cargo run --release -- recursion --n 2 --log-inv-rate 2
```

```
recursion 2→1: 2 inner proofs of 1,728,250 cycles each
  guest cycles (VM steps)     :      1,478,606 = 2^20.496  (0.428 / inner cycle)
  recursion program           :        606,980 instructions (2^20 padded)
  committed witness size      : 2^25.678
  data memory                 : 2^21 padded (2^20.735 used)
  recursive proof size        : 234.195 KiB
  outer proving               : 5.016 s
  complete recursive verify   : 165 ms
```

### Fibonacci


```bash
RAYON_NUM_THREADS=11 cargo run --release -- fibonacci --n 2000000  --log-inv-rate 1
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,042,017
    XOR   instructions        : 2^10.966
    MUL   instructions        : 2^20.942
    SET   instructions        : 2^12.967
    DEREF instructions        : 2^13.967
    JUMP  instructions        : 2^10.968
    BLAKE3 instructions        : 0
  committed witness size      : 2^25.658
  proof size                  : 335.7 KiB
  proving (incl. witness gen) : 3.853 s
  verifying                   : 5.50 ms
  throughput                  : 529,929 cycles/s
```

## Security

- 128-bit target soundness, with algebraic challenges in $\mathrm{GF}(2^{192})$ and the WHIR/Ligerito Johnson list-decoding analysis.

The proof-size target will be improved further.

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
