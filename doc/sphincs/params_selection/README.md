# SPHINCS+ parameter selection

Security, signature size and hash counts for the WOTS/FORS schemes of "Hash-based Signature Schemes for Bitcoin" (Kudinov, Nick, Blockstream Research), and a search for the set that verifies cheapest under a given set of budgets. See `src/lib.rs` for what is modelled and what is deliberately not.

One command. Give a parameter to pin it, leave it out to search it. Numbers may be written as `2e6` or `100,000` or `100_000`, including the lifetime, which is a signature count rather than its log:

```sh
cd doc/sphincs/params_selection
cargo run --release -- --lifetime 1e12 --scheme W+C_F+C --height 40 --layers 5 --top-height 8 -a 14 -k 11 -w 256 --drop-chains 0 --swn 2040
```

That pins everything, so it just costs that one set: the report's bold 2^40 row, 4356 bytes and 10425 compressions to verify. Size and verification do not depend on the lifetime, only the security line does. Leave axes out and they get searched instead, against whichever budgets you set:

```sh
cargo run --release -- --lifetime 16,777,216 --max-keygen 2e6 --max-sign 200,000 --max-size 5000
```

Every cost is compression calls, one per 64 bytes of hash input: a Merkle node or a WOTS chain step is one, the message digest two, compressing `m` hash values `ceil((2n + mn) / 64)`.

`--max-sign` counts signing with the top XMSS tree's half top already in state, which is `sqrt(2^h_top)` of storage for a `sqrt(2^h_top)`-cost top tree and the steady-state cost of a signer that keeps it. That state is a cache, not state in the XMSS sense: it is a deterministic function of the seed, so losing it costs recomputation and nothing else. A signer holding nothing rebuilds every tree instead, a cost this computes but does not report, since it is paid once after restoring a backup.

Since size and verification depend only on `(h, d)` and not on how the layers divide `h`, a taller top layer is free on both and cheaper to sign with the cache: compare `--top-height 8` against `--top-height 15` at `--height 40 --layers 5`.

Layer heights can be given outright with `--heights 11,5,7,3`, which pins `h` and `d` with them. The search never produces an uneven lower half, and that is not a restriction: for the same `h`, `d` and top height, no other profile costs less on anything, since size, verification and keygen do not move and signing sums `2^height`, which at a fixed total is smallest when the heights are equal. `profile_shape_is_never_beaten` checks that against every composition of several small `(h, d)`. So `--heights` is for costing a profile you already have in mind.

`cargo run --release --` with no arguments prints every flag and its default. `cargo test --release` runs the goldens: the upstream sage fixtures, the report's own tables, and a naive search oracle that skips nothing.

The search is exhaustive over hardcoded ranges and warns when its answer leans on the top of one. Budgets loose enough that nothing prunes can take a couple of minutes, reported by `--stats`; realistic ones finish in seconds.
