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
XMSS aggregation, 890 signatures
  cycles (VM steps)           :    1529572 = 2^20.54   (  1718.6 / XMSS)
    XOR    instructions       :     125491 = 2^16.94   (   141.0 / XMSS)
    MUL    instructions       :     295495 = 2^18.17   (   332.0 / XMSS)
    SET    instructions       :     354194 = 2^18.43   (   398.0 / XMSS)
    DEREF  instructions       :     508569 = 2^18.96   (   571.4 / XMSS)
    JUMP   instructions       :     115702 = 2^16.82   (   130.0 / XMSS)
    BLAKE3 instructions       :     130121 = 2^16.99   (   146.2 / XMSS)
  committed witness size      : 2^25.662
  data memory                 : 2^22 padded (2^21.71 used)
  proof size                  : 593.3 KiB
  proving (incl. witness gen) : 1.401495542s
  verifying                   : 13.522416ms
  throughput                  : 635.0 XMSS/s
```

### Recursion


```bash
RAYON_NUM_THREADS=11 cargo run --release -- recursion --n 2
```

```
recursion 2→1: 2 inner proofs of 917755 cycles each
  guest cycles (VM steps)     :    2516723 = 2^21.26   (1.37 / inner cycle)
    XOR    instructions     :     573243 = 2^19.13
    MUL    instructions     :     786042 = 2^19.58
    SET    instructions     :     196196 = 2^17.58
    DEREF  instructions     :     868775 = 2^19.73
    JUMP   instructions     :      48646 = 2^15.57
    BLAKE3 instructions     :      43821 = 2^15.42
  committed witness size      : 2^26.085
  data memory                 : 2^22 padded (2^21.53 used)
  recursive proof size        : 648.2 KiB
  outer proving               : 2.186834667s
```

## Security, proof size etc

- security = 120 bits, proven, unique-decoding regime, Ligerito
- proof size = BIG (≈ 0.7 MiB)

Both will be improved later.

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
