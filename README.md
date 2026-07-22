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
RAYON_NUM_THREADS=11 cargo run --release -- xmss --n-signatures 820 --log-inv-rate 1
```

```
XMSS aggregation, 820 signatures
  cycles (VM steps)           :      1,351,859 = 2^20.37   (  1648.6 / XMSS)
    XOR    instructions       :        115,621 = 2^16.82   (   141.0 / XMSS)
    MUL    instructions       :        269,792 = 2^18.04   (   329.0 / XMSS)
    SET    instructions       :        261,504 = 2^18.00   (   318.9 / XMSS)
    DEREF  instructions       :        468,599 = 2^18.84   (   571.5 / XMSS)
    JUMP   instructions       :        106,602 = 2^16.70   (   130.0 / XMSS)
    BLAKE3 instructions       :        129,741 = 2^16.99   (   158.2 / XMSS)
  committed witness size      : 2^26.360
  data memory                 : 2^22 padded (2^21.56 used)
  proof size                  : 374.6 KiB
  proving (incl. witness gen) : 2.446402417s
  verifying                   : 5.343375ms
  throughput                  : 335.2 XMSS/s
```

### Recursion


```bash
RAYON_NUM_THREADS=11 cargo run --release -- recursion --n 2  --log-inv-rate 2
```

```
recursion 2→1: 2 inner proofs of 950,518 cycles each
  guest cycles (VM steps)     :      2,122,954 = 2^21.02   (1.12 / inner cycle)
    XOR    instructions     :        460,742 = 2^18.81
    MUL    instructions     :        712,030 = 2^19.44
    SET    instructions     :        184,512 = 2^17.49
    DEREF  instructions     :        686,980 = 2^19.39
    JUMP   instructions     :         46,663 = 2^15.51
    BLAKE3 instructions     :         32,027 = 2^14.97
  committed witness size      : 2^26.360
  data memory                 : 2^22 padded (2^21.27 used)
  recursive proof size        : 376.9 KiB
  outer proving               : 2.592742583s
  complete recursive verify   : 23.070708ms
```

### Fibonacci


```bash
RAYON_NUM_THREADS=11 cargo run --release -- fibonacci --n 2000000  --log-inv-rate 1
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,046,015
    XOR   instructions        : 2^10.966
    MUL   instructions        : 2^20.942
    SET   instructions        : 2^13.288
    DEREF instructions        : 2^13.967
    JUMP  instructions        : 2^11.967
    BLAKE3 instructions        : 0
  committed witness size      : 2^25.662
  proof size                  : 348.4 KiB
  proving (incl. witness gen) : 1.304737417s
  verifying                   : 5.016916ms
  throughput                  : 1,568,143 cycles/s
```

## Security

- 128 bits, proven, Johnson list-decoding regime (Whir/Ligerito)

The proof-size target will be improved further.

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
