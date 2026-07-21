<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./misc/images/banner-b.svg">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/spec-latest/doc.pdf"><img src="https://img.shields.io/badge/Documentation-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Documentation"></a>
</p>

- WARNING: Highly experimental / sloppy (currently).
- Proving architecture is volontarily kept simple for now

# Benchmarks

Machine: M4 Max

### XMSS aggregation

```bash
RAYON_NUM_THREADS=11 cargo run --release -- xmss --n-signatures 890
```

```
XMSS aggregation, 820 signatures
  cycles (VM steps)           :    1370002 = 2^20.39   (  1670.7 / XMSS)
    XOR    instructions       :     115621 = 2^16.82   (   141.0 / XMSS)
    MUL    instructions       :     272255 = 2^18.05   (   332.0 / XMSS)
    SET    instructions       :     277184 = 2^18.08   (   338.0 / XMSS)
    DEREF  instructions       :     468599 = 2^18.84   (   571.5 / XMSS)
    JUMP   instructions       :     106602 = 2^16.70   (   130.0 / XMSS)
    BLAKE3 instructions       :     129741 = 2^16.99   (   158.2 / XMSS)
  committed witness size      : 2^25.648
  data memory                 : 2^22 padded (2^21.57 used)
  proof size                  : 594.2 KiB
  proving (incl. witness gen) : 1.435920916s
  verifying                   : 13.987917ms
  throughput                  : 571.1 XMSS/s
```

### Recursion


```bash
RAYON_NUM_THREADS=11 cargo run --release -- recursion --n 2
```

```
recursion 2→1: 2 inner proofs of 950519 cycles each
  guest cycles (VM steps)     :    2537008 = 2^21.27   (1.33 / inner cycle)
    XOR    instructions     :     577877 = 2^19.14
    MUL    instructions     :     787456 = 2^19.59
    SET    instructions     :     249425 = 2^17.93
    DEREF  instructions     :     819009 = 2^19.64
    JUMP   instructions     :      47982 = 2^15.55
    BLAKE3 instructions     :      55259 = 2^15.75
  committed witness size      : 2^26.079
  data memory                 : 2^22 padded (2^21.54 used)
  outer proof size            : 643.8 KiB
  outer proving               : 2.421577375s
  outer verifying             : 18.431417ms
  reduced claims (native)     : 9.111375ms
```

## Security, proof size etc

- security = 120 bits, proven, unique-decoding regime, Ligerito
- proof size = BIG (≈ 0.7 MiB)

Both will be improved later.

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
