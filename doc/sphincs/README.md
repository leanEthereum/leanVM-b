# SPHINCS+ parameters

Security, signature size and hash counts for the WOTS/FORS schemes of "Hash-based Signature Schemes for Bitcoin" (Kudinov, Nick, Blockstream Research), plus a search for the parameter set that verifies cheapest under a given set of budgets. See `src/lib.rs` for what is modelled and what is deliberately not.

Its own cargo workspace, no dependencies, not a member of the repo's workspace.

```sh
cd doc/sphincs
cargo run --release -- params --scheme W+C_F+C --lifetime 40 --height 40 --layers 5 -a 14 -k 11 -w 256
cargo run --release -- params --top-height 15     # a taller top XMSS tree, cheaper to sign with the cache
cargo run --release -- search --lifetime 30 --max-keygen 2e6 --max-sign 6e6 --max-sign-cached 4e6 --max-size 4000
cargo test --release          # goldens: upstream sage fixtures, the report's tables, a naive search oracle
```

`cargo run --release --` with no subcommand prints the full option list.

The search is exhaustive over hardcoded ranges and prints a warning when its answer leans on the top of one of them. Budgets loose enough that nothing prunes can take a couple of minutes and are reported by `--stats`; realistic ones finish in seconds.
