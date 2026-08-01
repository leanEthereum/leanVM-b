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
  cycles (VM steps)           :      1,528,683 =  2^20.544   (   1,717.621 / XMSS)
    XOR    instructions       :        125,491 =  2^16.937   (     141.001 / XMSS)
    MUL    instructions       :        295,495 =  2^18.173   (     332.017 / XMSS)
    SET    instructions       :        354,194 =  2^18.434   (     397.971 / XMSS)
    DEREF  instructions       :        508,569 =  2^18.956   (     571.426 / XMSS)
    JUMP   instructions       :        114,813 =  2^16.809   (     129.003 / XMSS)
    BLAKE3 instructions       :        130,121 =  2^16.989   (     146.203 / XMSS)
  committed witness size      : 2^25.662
  data memory                 : 2^22 padded (2^21.707 used)
  proof size                  : 588.68 KiB
  proving (incl. witness gen) : 1.358 s
  verifying                   : 0.00594 s
  throughput                  : 655.559 XMSS/s
```

### Recursion


```bash
RAYON_NUM_THREADS=11 cargo run --release -- recursion --n 2
```

```
recursion 2→1: 2 inner proofs of 852,207 cycles each
  guest cycles (VM steps)     :      1,955,570 =  2^20.899   (1.147 / inner cycle)
    XOR    instructions     :        519,080 =  2^18.986
    MUL    instructions     :        651,514 =  2^19.313
    SET    instructions     :        161,965 =  2^17.305
    DEREF  instructions     :        561,871 =    2^19.1
    JUMP   instructions     :         18,431 =   2^14.17
    BLAKE3 instructions     :         42,709 =  2^15.382
  committed witness size      : 2^25.902
  data memory                 : 2^22 padded (2^21.21 used)
  recursive proof size        : 590.859 KiB
  outer proving               : 1.548 s
  complete recursive verify   : 0.292 s
```

## Security, proof size etc

- security = 120 bits, proven, unique-decoding regime, Ligerito
- proof size = BIG (≈ 0.7 MiB)

Both will be improved later.

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
