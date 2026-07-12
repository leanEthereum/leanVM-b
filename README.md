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
RAYON_NUM_THREADS=11 cargo run --release -- xmss --n-signatures 820
```

```
TODO
```

### Recursion


```bash
RAYON_NUM_THREADS=11 cargo run --release -- recursion --n 2
```

```
TODO
```

## Security, proof size etc

- security = 120 bits, proven, unique-decoding regime, Ligerito
- proof size = BIG (≈ 0.7 MiB)

Both will be improved later.

## Credits

- [flock](https://github.com/succinctlabs/flock/tree/main)
- [binius](https://github.com/IrreducibleOSS/binius)
- [binius64](https://github.com/binius-zk/binius64)
