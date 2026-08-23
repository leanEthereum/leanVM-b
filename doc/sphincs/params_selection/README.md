# SPHINCS+ parameter selection

Security, signature size and hash counts for the WOTS/FORS schemes of "Hash-based Signature Schemes for Bitcoin" (Kudinov, Nick, Blockstream Research), and a search for the set that verifies cheapest under a given set of budgets. See `src/lib.rs` for what is modelled and what is deliberately not.

One command. Give a parameter to pin it, leave it out to search it. Numbers may be written as `2e6` or `100,000` or `100_000`, including the lifetime, which is a signature count rather than its log:

```sh
cd doc/sphincs/params_selection
cargo run --release -- --lifetime 1e12 --scheme W+C_F+C --height 40 --layers 5 --top-height 8 -a 14 -k 11 -w 256 --drop-chains 0 --swn 2040
```

That pins everything, so it just costs that one set: the report's bold 2^40 row, 4356 bytes and 10425 compressions to verify. Size and verification do not depend on the lifetime, only the security line does. Leave axes out and they get searched instead, against whichever budgets you set:

```sh
cargo run --release -- --lifetime 16,777,216 --max-keygen 2e6 --max-sign 100,000 --max-size 5000
```

Every cost is compression calls, one per 64 bytes of hash input: a Merkle node or a WOTS chain step is one, the message digest two, compressing `m` hash values `ceil((2n + mn) / 64)`.

`--max-sign` counts signing with the top XMSS tree's half top already in state, which is `sqrt(2^h_top)` of storage for a `sqrt(2^h_top)`-cost top tree and the steady-state cost of a signer that keeps it. That state is a cache, not state in the XMSS sense: it is a deterministic function of the seed, so losing it costs recomputation and nothing else. A signer holding nothing rebuilds every tree instead, a cost this computes but does not report, since it is paid once after restoring a backup.

Since size and verification depend only on `(h, d)` and not on how the layers divide `h`, a taller top layer is free on both and cheaper to sign with the cache: compare `--top-height 8` against `--top-height 15` at `--height 40 --layers 5`.

Each layer carries its own WOTS instance too, so `w`, the target sum and the dropped chains need not agree across layers. `--layer 12,w=16,swn=240 --layer 12,w=8,drop=1` costs one such hypertree outright, `--heights 11,5,7,3` gives just the heights, and `--split-wots` searches a separate instance for the top layer.

Two instances is all a search needs. Any Lagrangian relaxation of the per-layer choice is separable, so each layer takes its own argmin, and every layer below the top has an identical cost function, since only the top tree is the cached one and only it is what keygen pays for. So at most two distinct choices come back. `two_groups_against_every_per_layer_assignment` checks that against every per-layer assignment of several small hypertrees, and finds no gap.

Whether it is worth searching is another matter. Size charges every layer the same `l * n` and verification charges every layer its own walk, so on those two the exchange rate is identical everywhere and a uniform `w` is what a size budget wants: the walk is convex in `l`, so at a fixed total `l` an equal split is cheapest. Only signing distinguishes the layers, a tall tree wanting cheap leaves. So per-layer WOTS pays only when the signing budget binds and the heights are uneven, and on the queries tried here the uniform choice still wins.

`cargo run --release --` with no arguments prints every flag and its default. `cargo test --release` runs the goldens: the upstream sage fixtures, the report's own tables, and a naive search oracle that skips nothing.

The search is exhaustive over hardcoded ranges and warns when its answer leans on the top of one. Budgets loose enough that nothing prunes can take a couple of minutes, reported by `--stats`; realistic ones finish in seconds.
