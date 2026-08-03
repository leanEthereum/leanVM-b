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

Machine: Mac M4 Max

### XMSS aggregation

```bash
LEANVM_NUM_THREADS=11 cargo run --release -- xmss --n-signatures 890 --log-inv-rate 1
```

```
XMSS aggregation, 890 signatures
  cycles (VM steps)           :      1,513,580 =   2^20.53   (   1,700.652 / XMSS)
    XOR      instructions     :        125,491 =  2^16.937   (     141.001 / XMSS)
    MUL      instructions     :        292,821 =   2^18.16   (     329.012 / XMSS)
    SET      instructions     :        341,765 =  2^18.383   (     384.006 / XMSS)
    DEREF    instructions     :        508,569 =  2^18.956   (     571.426 / XMSS)
    JUMP     instructions     :        114,813 =  2^16.809   (     129.003 / XMSS)
    BLAKE3   instructions     :        130,121 =  2^16.989   (     146.203 / XMSS)
    PACK64X2 instructions     :              0 =         -   (           0 / XMSS)
  committed witness size      : 2^26.364
  data memory                 : 2^22 padded (2^21.701 used)
  proof size                  : 359.617 KiB
  proving (incl. witness gen) : 1.905 s
  verifying                   : 0.00426 s
  throughput                  : 467.072 XMSS/s
```

### Recursion


```bash
LEANVM_NUM_THREADS=11 cargo run --release -- recursion --n 2 --log-inv-rate 2
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
LEANVM_NUM_THREADS=11 cargo run --release -- fibonacci --n 2000000  --log-inv-rate 1
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
  proving (incl. witness gen) : 1.031051291s
  verifying                   : 3.274ms
  throughput                  : 1,972,760 cycles/s
```

## Security

- 128-bit proven (LDR Johnson)

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
