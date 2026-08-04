# AGENT.md

## What this is

A minimal (zero-knowledge Virtual Machine, which is actually not ZK in the real sense, i.e. it's only a snark, not a zk-snark).

- `misc/doc.tex` describes the machine ISA, the snark that proves it.
- `crates/lean_compiler/zkDSL.md` documents the (pythonic) zkDSL (that compiles to the ISA that our VM runs, and that our snark proves).

Primary goal:
- Aggregate XMSS (stateful hash based signatures), via a snark proving knowledge soundness of the signatures, against a common message and a lust of public keys
- Further aggregate n previously aggregated signatures, which is performed by a recursive snark, that proves "I know n sub-proofs that are valid and the union of the public keys they handle contains the list of public keys I am given in public input". 

## Layout

Dependency order, leaves first:

| crate             | role                                                                   |
| ----------------- | ---------------------------------------------------------------------- |
| `parallel`        | thread pool (below)                                     |
| `zk_alloc`        | proving arena (below)                                    |
| `primitives`      | field kernels (NEON/AVX), bit transposes, multilinear helpers, `bench` |
| `fiat_shamir`     | VM-native sponge + prover/verifier transcript                          |
| `pcs`             | additive NTT, Merkle, ring switch, stacked Ligerito                    |
| `flock`           | batched R1CS over GF(2) for BLAKE3: zerocheck + lincheck               |
| `lean_vm`         | arithmetization: tables, bus, constraints, `cpu::prove`/`verify`       |
| `lean_compiler`   | zkDSL (Python subset) → ISA                                            |
| `xmss`            | XMSS over BLAKE3                     |
| `rec_aggregation` | the three workloads + the N→1 recursion harness                        |

`src/main.rs` is the CLI; guests are zkDSL under `crates/rec_aggregation/guests/`.

## Building / Testing / Formatting

- `.cargo/config.toml` pins `-C target-cpu=native`
- always run in `--release` mode any test or benchmark touching the VM (the zkDSL compiler stack-overflows in `debug` mode)

```bash
cargo testall                     # = test --all --release; 314 tests, seconds
cargo clippy --release --all-targets
cargo fmt --all                   # max_width = 120
```

Heavy benches are `#[ignore]`d; run by name with `-- --ignored --nocapture` (`blake3_batch`, `pcs_throughput`, `recursion_soundness_binds`, `recursion_generic_many`).

## Benchmarking

The benchmarks we care about:
- `cargo run --release -- xmss --n-signatures 890 --log-inv-rate 1 --repeat 3`
- `cargo run --release -- recursion --n 2 --log-inv-rate 2 --repeat 3`

## The proving arena (`zk_alloc`)

One proof is one **phase**, opened by `cpu::prove`. `ArenaVec` bumps a per-thread slab, freeing is a no-op, and the next `begin_phase()` reclaims everything. Not a `#[global_allocator]`: `raw_dealloc` picks arena-vs-system by address range, so with no phase open `ArenaVec` is an ordinary system vector (used in particular by the verifier, where correctness and simplicity matters much more than performance).

**The rule:** an `ArenaVec` allocated in a phase dies at the next `begin_phase()`. A reset neither clears nor unmaps, so a buffer that outlives its phase reads the previous proof's plausible bytes, so the symptom is a proof that stops verifying, never a crash. Anything outliving a phase (a `Proof`, a cache, a table) must be a plain `Vec`.

`LEANVM_NO_ARENA=1` halves resident memory but is unoptmized (not our concern for now, we assume we have enough RAM).

## The thread pool (`parallel`)

No rayon. Every parallel site is "N independent items, each writing its own disjoint slice", so the pool is a claim counter, not a work-stealing deque: `NUM_THREADS-1` workers plus the dispatcher inline, no per-dispatch allocation. Primitives: `for_each{,_chunk}`, `chunks_mut{,2,_zip}`, `Chunks`, `fill`, `map_collect`, `map_reduce`, `fold_reduce`, `map_reduce_with_state`, `find_first`, `SendPtr`.

- **Nested dispatch panics**, because it would deadlock the dispatch lock.
- **Both core clusters share one queue** (P at `USER_INTERACTIVE`, E at `UTILITY`); guided self-scheduling means a slow core claims fewer batches. Do not add a second pool: that was `primitives::epool`, now deleted.
- **The default holds back one performance worker when efficiency workers exist**, because `cpu::prove` also runs a setup-warming thread and a saturated small cluster stalls every barrier on any descheduled worker. Worth 13% on M4 Max, a wash on 16-thread Zen 4, hence the condition rather than a tuned constant.

`LEANVM_NUM_THREADS` (and `RAYON_NUM_THREADS`) sets the **performance**-worker count, leaving E-workers in place. `1` = strictly sequential.

## Three verifiers, one protocol

The same verification algorithm is written out three times, in three languages. Any change to snark protocol has to land in all three.

1. **Rust**, `lean_vm::cpu::verify`. The performant verifier implem.
2. **Python**, `python-verifier/verifier.py` (~2.5k lines, no dependencies). pure python, for readability and simplicity. Pinned by `lean_compiler/tests/python_verifier.rs`.
3. **Recursive verifier**, `crates/rec_aggregation/guests/recursion.py` (~2.4k lines of zkDSL). Written using our pythonic zkDSL (but it's not real python!), which then compiles to our custom ISA. Proving it result in recursion -> a snark of another snark.

The third is worth understanding before touching the verifier. `guests/recursion.py` is not Python that runs; it is the zkDSL, which `lean_compiler` lowers to the VM's seven-opcode ISA (`XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `BLAKE3`, `PACK64X2`) over write-once memory. So every verifier step, sponge absorption, sumcheck fold, Merkle path, field inverse, becomes VM instructions that the prover then proves the execution of, which is why the guest is ~500k instructions and why its opcode mix is what the recursion benchmark reports. Two consequences:

- The guest is **generic in the inner proof**: its placeholder map depends only on the inner bytecode size, so one compiled bytecode verifies inner proofs of different sizes and PCS rates (`recursion_2to1_mixed`, `recursion_generic_many`).
- It does not verify *quite* everything in-circuit. Three claims on fixed polynomials (stacked bytecode, and flock's A0/B0) are deferred, bound to the guest's public input, and discharged natively by `RecursiveProof::verify`. Sumcheck is used to merge and further deref those 'postponed' claims in recursion, moving `n` such inner claims to a single outer one (explained in doc.tex).

`recursion_2to1` is the fast end-to-end check; `recursion_soundness_binds` is the adversarial one, tampering each hint stream in turn and requiring rejection.

## Conventions that bite

- **Fiat-Shamir:** `add_scalar`/`next_scalar` bind into the sponge as a side effect. `observe_*` is only for the public statement. Never re-observe data that rode the stream, which silently desynchronizes the two sides.
- **Prover and verifier derive the layout identically** from announced sizes. Changes to `placements_of`, `col_kappas` or the schema land on both sides, and `col_kappa_sources` stays in lockstep with `col_kappas`.
- **A failed guest `assert` surfaces as a write-once memory conflict**, not an assertion message, so disassemble around the reported `pc` (`DBG_DISASM`).
- Guests are single-file; the compiler skips `from snark_lib import *`, which exists only so editors accept the file as Python.
- **No em-dashes or en-dashes in prose**, anywhere a human reads it: docs, LaTeX, comments, commit messages. Restructure with a comma, colon, parentheses, or two sentences.
- **Never hard-wrap prose in Markdown or LaTeX.** One paragraph is one line; let the editor wrap it. Artificial line breaks make every later edit a reflow, so diffs show rewrapped lines instead of changed words. Applies to `.md` and `.tex` alike; code blocks, tables and list items keep their own line.

## Env knobs

| var                                                                                                     | effect                                           |
| ------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| `LEANVM_NUM_THREADS` / `RAYON_NUM_THREADS`                                                              | performance-worker count; `1` = sequential       |
| `LEANVM_PROFILE`                                                                                        | per-stage prover timings                         |
| `LEANVM_NO_ARENA`                                                                                       | disable the arena (less memory, slower)          |
| `ZK_ALLOC_STATS`                                                                                        | arena bytes/phase, high water, overflow          |
| `BENCH_REPEAT`, `BENCH_COOLDOWN`                                                                        | `--repeat`/`--cooldown` for `#[ignore]`d benches |
| `LEANVM_XMSS_N`, `LEANVM_HASH_N`, `LEANVM_HASH_UNROLL`                                                  | workload sizes in tests                          |
| `FLOCK_N_LOG`, `FLOCK_PROVE_TRACE`, `FLOCK_ZC_TIMING`                                                   | flock batch size, stage traces                   |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_MIN_MU`, `PCS_SAMPLES`                                            | PCS throughput bench                             |
| `LIGERITO_TRACE`, `LIGERITO_NUM_VARS`, `LIGERITO_LOG_INV_RATE`                                          | Ligerito NTT/Merkle split                        |
| `DBG_PROF{,_DUMP}`, `DBG_LOOPS`, `DBG_DISASM`, `DBG_LOWER`, `DBG_CSE`, `DBG_NO_CSE`, `DBG_PLACEHOLDERS` | compiler / guest-cycle attribution               |
