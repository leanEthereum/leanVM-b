<h1 align="center">leanVM-b</h1>

<p align="center">
  <img src="./doc/images/banner-b.svg" alt="leanVM-b">
</p>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/leanVM-b.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

Warning: highly experimental.

# Benchmarks

Machine: Mac M4 Max

### XMSS aggregation

Our XMSS is specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/XMSS.pdf).

```bash
cargo run --release -- aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

### SPHINCS aggregation

Our SPHINCS is specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM-b/releases/download/doc-latest/SPHINCS.pdf). It is stateless, so a key needs no epoch, and each SPHINCS signer signs its own message where the XMSS signers share one. One verification costs 531 compressions against XMSS's 144, so a leaf of comparable proven size holds proportionally fewer signers; `--xmss` and `--sphincs` add up, so a mixed leaf is one command.

```bash
cargo run --release -- aggregate --sphincs 245 --log-inv-rate 1 --repeat 3
```

### Recursion

```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

### Fibonacci

```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

### Batch proving SHA-256 compression

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=17 cargo test --release -p flock --test hash_batch -- --ignored --nocapture
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## SNARK machinery

- Binary field of 192 bits
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (also known as [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving SHA-256 by [Flock](https://github.com/succinctlabs/flock/tree/main)
- Ring switching, M3 arithmetization, and more by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
