<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./misc/images/banner-b.svg">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/spec-latest/doc.pdf"><img src="https://img.shields.io/badge/Documentation-blue?style=for-the-badge&logo=latex&logoColor=white" alt="Documentation"></a>
</p>

- WARNING: Highly experimental / sloppy (currently).
- Proving architecture is volontarily kept simple for now

## Fibonacci benchmark

`cargo run --release`

M4 Max:

```
Fibonacci (in the exponent, i.e. modulo 2^128 - 1), N = 2000000
  cycles (VM steps)           : 2052091
    XOR   instructions        : 2^10.977
    MUL   instructions        : 2^20.943
    SET   instructions        : 2^13.776
    DEREF instructions        : 2^13.968
    JUMP  instructions        : 2^11.967
  committed witness size      : 2^25.108
  proof size                  : 1196.5 KiB
  proving (incl. witness gen) : 1.281336625s
  verifying                   : 5.478042ms
  throughput                  : 1601524 cycles/s
```

## Security, proof size etc

- security = 100 bits, proven, UDR, Basefold
- proof size =  BIG (≈ 1 MiB)

Both will be improved later.

## Credits

- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
- [flock](https://github.com/succinctlabs/flock/tree/main)
