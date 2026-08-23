# SPHINCS+ parameter selection

Security, signature size and hash counts for the WOTS/FORS schemes of "Hash-based Signature Schemes for Bitcoin" (Kudinov, Nick, Blockstream Research), and a search for the set that verifies cheapest under a given set of budgets. See `src/lib.rs` for what is modelled and what is deliberately not.

One command. Give a parameter to pin it, leave it out to search it. Numbers may be written as `2e6`, including the lifetime, which is a signature count rather than its log:

```sh
cd doc/sphincs/params_selection
cargo run --release -- --lifetime 1e12 --scheme W+C_F+C --height 40 --layers 5 --top-height 8 -a 14 -k 11 -w 256 --drop-chains 0 --swn 2040
```

That pins everything, so it just costs that one set: the report's bold 2^40 row, 4356 bytes and 10425 compressions to verify. Size and verification do not depend on the lifetime, only the security line does. Leave axes out and they get searched instead, against whichever budgets you set:

```sh
cargo run --release -- --lifetime 24 --max-keygen 2e6 --max-sign 6e6 --max-sign-cached 4e6 --max-size 4000
```

Every cost is compression calls, one per 64 bytes of hash input: a Merkle node or a WOTS chain step is one, the message digest two, compressing `m` hash values `ceil((2n + mn) / 64)`. `--max-sign-cached` budgets signing with the top XMSS tree's half top kept as signer state, which costs sqrt storage for a sqrt-cost top tree. Since size and verification depend only on `(h, d)` and not on how the layers divide `h`, a taller top layer is free on both and cheaper to sign with the cache: compare `--top-height 8` against `--top-height 15` at `--height 40 --layers 5`.

`cargo run --release --` with no arguments prints every flag and its default. `cargo test --release` runs the goldens: the upstream sage fixtures, the report's own tables, and a naive search oracle that skips nothing.

The search is exhaustive over hardcoded ranges and warns when its answer leans on the top of one. Budgets loose enough that nothing prunes can take a couple of minutes, reported by `--stats`; realistic ones finish in seconds.
