# AGENT.md

## What this is

A minimal (zero-knowledge Virtual Machine, which is actually not ZK in the real sense, i.e. it's only a snark, not a zk-snark).

- `misc/doc.tex` describes the machine, the arithmetization and the protocol
- `crates/lean_compiler/zkDSL.md` documents the zkDSL.

## Layout

Dependency order, leaves first:

| crate | role |
|---|---|
| `parallel` | thread pool (below); `libc` only |
| `zk_alloc` | proving arena (below); `libc` only |
| `primitives` | field kernels (NEON/AVX), bit transposes, multilinear helpers, `bench` |
| `fiat_shamir` | VM-native sponge + prover/verifier transcript |
| `pcs` | additive NTT, Merkle, ring switch, stacked Ligerito |
| `flock` | batched R1CS over GF(2) for BLAKE3: zerocheck + lincheck |
| `lean_vm` | arithmetization: tables, bus, constraints, `cpu::prove`/`verify` |
| `lean_compiler` | zkDSL (Python subset) → ISA |
| `xmss` | XMSS over BLAKE3; **not** on the proving path |
| `rec_aggregation` | the three workloads + the N→1 recursion harness |

`src/main.rs` is the CLI; guests are zkDSL under `crates/rec_aggregation/guests/`.

## Build and test

`.cargo/config.toml` pins `-C target-cpu=native`. Always use release for anything perf-related.

```bash
cargo testall                     # = test --all --release; 314 tests, seconds
cargo clippy --release --all-targets
cargo fmt --all                   # max_width = 120
```

Two pre-existing `manual_is_multiple_of` warnings in `lean_vm/src/gkr.rs` are expected. Heavy benches are `#[ignore]`d; run by name with `-- --ignored --nocapture` (`blake3_batch`, `pcs_throughput`, `recursion_soundness_binds`, `recursion_generic_many`).

## Benchmarking

`primitives::bench` discards one warmup pass, averages `--repeat n` passes, and reports a 95% interval; the CLI also prints peak RSS, which the arena trades for the page faults it removes.

```bash
./target/release/leanvm-b xmss --n-signatures 820 --repeat 8 --cooldown-ms 6000
```

`--cooldown-ms` is required on a laptop. Same workload, M4 Max on AC:

| cooldown per pass | none | 1 s | 3 s | 6 s |
|---|---|---|---|---|
| proving | 3.14 s | 2.59 s | 1.85 s | 1.72 s |

A 1.8× thermal spread, stable within a run and therefore invisible in the interval. Two runs compare only if they used the same cooldown. A server-class x86 host needs none (±0.2%), so resolve anything under ~3% there. The two hosts disagree in magnitude and sometimes in sign, so check both.

Current `main` at 820 signatures: **1.373 s / 597 XMSS/s** (M4 Max, 11 P + 4 E, 6 s cooldown); **4.318 s / 190 XMSS/s** (Ryzen 7 PRO 8700GE, 16 threads).

`LEANVM_PROFILE=1` gives per-stage prover timings.

## The proving arena (`zk_alloc`)

One proof is one **phase**, opened by `cpu::prove`. `ArenaVec` bumps a per-thread slab, freeing is a no-op, and the next `begin_phase()` reclaims everything. Worth 14% of prove time on M4 Max, 30% on Zen 4. Not a `#[global_allocator]`: `raw_dealloc` picks arena-vs-system by address range, so with no phase open `ArenaVec` is an ordinary system vector, which is what makes it safe in the verifier and in tests.

**The rule, and the only silent-corruption footgun in the repo:** an `ArenaVec` allocated in a phase dies at the next `begin_phase()`. A reset neither clears nor unmaps, so a buffer that outlives its phase reads the previous proof's plausible bytes, so the symptom is a proof that stops verifying, never a crash. Anything outliving a phase (a `Proof`, a cache, a table) must be a plain `Vec`. `rec_aggregation/tests/arena_prove.rs` guards this; it needs its own test binary because phases are process-global and refuse to nest.

`ZK_ALLOC_STATS=1` reports bytes/phase, per-slab high water, and overflow to the system allocator (nonzero ⇒ `SLAB_SIZE` undersized). `LEANVM_NO_ARENA=1` halves resident memory but is currently *slower than the pre-arena baseline* (7.8 s vs 4.3 s on Zen 4) because the `primitives::scratch` pool it relied on is gone.

## The thread pool (`parallel`)

No rayon. Every parallel site is "N independent items, each writing its own disjoint slice", so the pool is a claim counter, not a work-stealing deque: `NUM_THREADS-1` workers plus the dispatcher inline, no per-dispatch allocation. Primitives: `for_each{,_chunk}`, `chunks_mut{,2,_zip}`, `Chunks`, `fill`, `map_collect`, `map_reduce`, `fold_reduce`, `map_reduce_with_state`, `find_first`, `SendPtr`.

- **Nested dispatch panics**, because it would deadlock the dispatch lock. Two genuine levels of fan-out pick the inner one via `is_in_task()`; only `xmss`'s tree build does, and that is key generation.
- **Both core clusters share one queue** (P at `USER_INTERACTIVE`, E at `UTILITY`); guided self-scheduling means a slow core claims fewer batches. Do not add a second pool: that was `primitives::epool`, now deleted.
- **The default holds back one performance worker when efficiency workers exist**, because `cpu::prove` also runs a setup-warming thread and a saturated small cluster stalls every barrier on any descheduled worker. Worth 13% on M4 Max, a wash on 16-thread Zen 4, hence the condition rather than a tuned constant.

`LEANVM_NUM_THREADS` (and `RAYON_NUM_THREADS`) sets the **performance**-worker count, leaving E-workers in place. `1` = strictly sequential.

## Conventions that bite

- **Fiat-Shamir:** `add_scalar`/`next_scalar` bind into the sponge as a side effect. `observe_*` is only for the public statement. Never re-observe data that rode the stream, which silently desynchronizes the two sides.
- **Prover and verifier derive the layout identically** from announced sizes. Changes to `placements_of`, `col_kappas` or the schema land on both sides, and `col_kappa_sources` stays in lockstep with `col_kappas`.
- **The recursion guest replays `cpu::verify` structurally**, so any transcript or layout change breaks `guests/recursion.py`. `recursion_2to1` is the fast check.
- **`python-verifier/verifier.py` mirrors the verifier**, pinned by `lean_compiler/tests/python_verifier.rs`.
- **A failed guest `assert` surfaces as a write-once memory conflict**, not an assertion message, so disassemble around the reported `pc` (`DBG_DISASM`).
- **`CREDIT:` headers mark upstream provenance** (succinctlabs/flock, MIT OR Apache-2.0); keep them.
- Guests are single-file; the compiler skips `from snark_lib import *`, which exists only so editors accept the file as Python.
- **No em-dashes or en-dashes in prose**, anywhere a human reads it: docs, LaTeX, comments, commit messages. Restructure with a comma, colon, parentheses, or two sentences.
- **Never hard-wrap prose in Markdown or LaTeX.** One paragraph is one line; let the editor wrap it. Artificial line breaks make every later edit a reflow, so diffs show rewrapped lines instead of changed words. Applies to `.md` and `.tex` alike; code blocks, tables and list items keep their own line.

## Env knobs

| var | effect |
|---|---|
| `LEANVM_NUM_THREADS` / `RAYON_NUM_THREADS` | performance-worker count; `1` = sequential |
| `LEANVM_PROFILE` | per-stage prover timings |
| `LEANVM_NO_ARENA` | disable the arena (less memory, slower) |
| `ZK_ALLOC_STATS` | arena bytes/phase, high water, overflow |
| `BENCH_REPEAT`, `BENCH_COOLDOWN_MS` | `--repeat`/`--cooldown-ms` for `#[ignore]`d benches |
| `LEANVM_XMSS_N`, `LEANVM_HASH_N`, `LEANVM_HASH_UNROLL` | workload sizes in tests |
| `FLOCK_N_LOG`, `FLOCK_PROVE_TRACE`, `FLOCK_ZC_TIMING` | flock batch size, stage traces |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_MIN_MU`, `PCS_SAMPLES` | PCS throughput bench |
| `LIGERITO_TRACE`, `LIGERITO_NUM_VARS`, `LIGERITO_LOG_INV_RATE` | Ligerito NTT/Merkle split |
| `DBG_PROF{,_DUMP}`, `DBG_LOOPS`, `DBG_DISASM`, `DBG_LOWER`, `DBG_CSE`, `DBG_NO_CSE`, `DBG_PLACEHOLDERS` | compiler / guest-cycle attribution |
