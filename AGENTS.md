# AGENT.md

## What this is

A minimal (zero-knowledge Virtual Machine, which is actually not ZK in the real sense, i.e. it's only a snark, not a zk-snark).

- `doc/leanvm/` is the LaTeX project describing the machine ISA and the snark that proves it. Its root is `doc/leanvm/main.tex`; build it with `cd doc/leanvm && latexmk -pdf main.tex`, which writes to the gitignored `doc/leanvm/.build/`. Sections live in `doc/leanvm/body/`, numbered `01`..`10` plus the lettered annexes `a` (ring switching), `b` (the PCS), and `c` (Flock), and every symbol is defined once in `doc/leanvm/preamble/macros.tex`. If latexmk fails oddly (a bibtex error, or a missing `main.log`) right after inputs are renamed or `refs.bib` is edited, remove `doc/leanvm/.build` and rerun; it has not reproduced on unchanged inputs. **Drafting one section:** each section file carries a `% !TeX root` comment pointing at its generated driver in `doc/leanvm/drafts/`, so the LaTeX build key (`F5`, or the extension's `cmd+alt+b`) compiles only that section, numbered as in the full document and with cross-references and citations resolved against `.build/main.aux`; in `main.tex` the same key builds everything. Run `doc/leanvm/make-drafts.sh` after adding, renaming or renumbering a section.
- `doc/xmss/` is the standalone specification of the concrete XMSS instance implemented by `crates/xmss`.
- The one hash function is BLAKE2s, in `primitives::blake2s`: scalar, streaming, keyed, and a lane-transposed batched form for the PCS Merkle tree. The VM proves one compression per opcode, and BLAKE2s takes the byte counter and final-block flag as ordinary compression inputs, so a single opcode is a complete hash for any length, with no tree structure to reproduce in-circuit.
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
| `pcs`             | additive NTT, Merkle, ring switch, stacked WHIR                    |
| `flock`           | batched R1CS over GF(2) for BLAKE2s: zerocheck + lincheck               |
| `lean_vm`         | arithmetization: tables, bus, constraints, `cpu::prove`/`verify`       |
| `lean_compiler`   | zkDSL (Python subset) → ISA                                            |
| `xmss`            | XMSS over BLAKE2s; an independent leaf, consumed only by `rec_aggregation` |
| `rec_aggregation` | recursive XMSS aggregation: the one guest, the public API, the benchmarks |

`src/main.rs` is the CLI; guests are zkDSL under `crates/rec_aggregation/guests/`.

## Building / Testing / Formatting

- `.cargo/config.toml` pins `-C target-cpu=native` and `-D warnings` for rustdoc
- always run in `--release` mode any test or benchmark touching the VM (the zkDSL compiler stack-overflows in `debug` mode)
- **One test binary per crate, not one per file:** each one rebuilds flock's BLAKE2s matrices from scratch. New `lean_compiler` integration tests go in `tests/suite/main.rs`. Exception: a test opening an arena phase (`lean_vm::init_prover`) needs its own binary, phases being process-global (`rec_aggregation/tests/arena_prove.rs`).

```bash
cargo testall                     # whole suite in seconds
cargo clippyall                   # clippy, -D warnings
cargo docall                      # rustdoc, -D warnings
cargo fmt --all                   # max_width = 120
ruff format --line-length 150 python-verifier/verifier.py   # and `ruff check` it
```

Heavy benches and measurement harnesses are `#[ignore]`d; run by name with `-- --ignored --nocapture`: `blake2s_batch_prove_verify`, `pcs_throughput`, `aggregate_three_levels`, `aggregate_statement_binds`, `aggregate_hints_bind`, `aggregate_rejects_a_bad_signature`, `print_whir_query_counts`, `encoding_grinding_bits`.

## Benchmarking

The benchmarks we care about:
- `cargo run --release -- xmss --n-signatures 900 --log-inv-rate 1 --repeat 3`
- `cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3`

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
2. **Python**, `python-verifier/verifier.py` (~2.5k lines, no dependencies). pure python, for readability and simplicity. Pinned by `lean_vm/tests/verifiers/python_verifier.rs`.
3. **Recursive verifier**, `crates/rec_aggregation/guests/aggregate.py` (~2.7k lines of zkDSL). Written using our pythonic zkDSL (but it's not real python!), which then compiles to our custom ISA. Proving it result in recursion -> a snark of another snark.

The third is worth understanding before touching the verifier. `guests/aggregate.py` is not Python that runs; it is the zkDSL, which `lean_compiler` lowers to the VM's seven-opcode ISA (`XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `BLAKE2S`, `PACK64X2`) over write-once memory. So every verifier step, sponge absorption, sumcheck fold, Merkle path, field inverse, becomes VM instructions that the prover then proves the execution of, which is why the guest is ~330k instructions (2^19 padded) and why its opcode mix is what the recursion benchmark reports. Two consequences:

- The guest is **self-referential**: it verifies proofs of itself, so `unified_guest` compiles it to a fixed point on its own log size. The digest needs no fixed point, riding the statement instead of the code, which is also what lets one bytecode serve any inner size and PCS rate.
- It does not verify *quite* everything in-circuit. Three claims on fixed polynomials (stacked bytecode, flock's A0/B0) are deferred. Each node batches its children's carried claims with the fresh ones its verifications raise, `2n` per polynomial down to one; only the root's are discharged natively, by `AggregateSignature::verify` (explained in `doc/leanvm/`).

`aggregate_two_to_one` is the fast end-to-end check; `aggregate_statement_binds` and `aggregate_hints_bind` are the adversarial ones, tampering the wire object and the witness respectively. A child must commit at least `2^MU_MIN` or the guest has no opening arm for it, so `aggregate` sets `Program::min_log_committed` and a smaller run grows its `SET` table through the fill blocks until it clears the floor.

## Conventions that bite

- Use comments only when necessary: uncommented but readable and simple code is better than commented slop. And when you use comments, be concise.
- Commit tests only that are useful in the future, to prevent regressions / failures. Don't add trivial tests that will always pass.
- Simpler is better.
- **Fiat-Shamir:** `add_scalar`/`next_scalar` bind into the sponge as a side effect. `observe_*` is only for the public statement. Never re-observe data that rode the stream, which silently desynchronizes the two sides.
- **Prover and verifier derive the layout identically** from announced sizes. Changes to `placements_of` or the schema land on both sides. `col_kappas` is derived from `col_kappa_sources` rather than written out twice, so the two can no longer drift; keep it that way.
- **The L0 lane fold binds the committed witness's TOP `INITIAL_FOLDING_FACTOR` variables**, because lane `l` of the interleaved commitment is the contiguous stack block `q[l·2^(μ-k) ..)`. That is what makes the stacked witness's zero tail whole lanes, so `whir::commit` encodes only `StackShape::n_lanes` of them, and the opening's dense weight, its first `k` sumcheck rounds and the stack allocation shrink with it. **A leaf image is still `2^k` words**, the absent lanes contributing the zeros their codeword would have been, but those zeros LEAD it (codeword lane `t` is stack block `n_lanes-1-t`), which buys two more things: their whole 64-byte blocks are one BLAKE2s chaining value every leaf shares (`blake2s::zero_prefix_state`), so the committer hashes them once instead of once per leaf, and only the image's tail rides the proof, so `PrunedMerklePaths` stores `n_lanes` words per L0 row while `RawMerklePath` (what the guest and the Python verifier read) carries the full image. The Rust and Python verifiers therefore derive `n_lanes` from the announced layout to read a row; the guest never needs it, since its hints are full images and its only change is a compile-time slot flip in the row weights. Since `mu = log2_ceil(placed)`, `n_lanes` is always in `[2^(k-1)+1, 2^k]`, so the encode saving is capped near half, the hashing saving is quantized to whole blocks of 8 lanes, and both are ~0 for a witness that just exceeds a power of two. The cost is that the fold challenges arrive in round order while every transparent weight is written in witness coordinates, so all three verifiers rotate the terminal point left by `k` before evaluating it (`whir.rs` before `eval_b_at`, `verifier.py` before `evaluate_basis`, and `open_stacked` returns the rotated pair in the guest). Anything else that reads the opening's point (per-level induced weights, the residual) stays in round order.
- **A failed guest `assert` surfaces as a write-once memory conflict**, not an assertion message, so disassemble around the reported `pc` (`DBG_DISASM`).
- Guests are single-file; the compiler skips `from snark_lib import *`, which exists only so editors accept the file as Python.
- **One symbol, one meaning, across the whole leanVM document.** All notation is defined in `doc/leanvm/preamble/macros.tex`: define a new macro there rather than inline, and check the letter is free first. Annex B's "Symbols" table maps its letters back to WHIR/Ligerito/BCHKS25, so read it before renaming one. A sumcheck round challenge is `\fc` everywhere, which is what keeps `\rho` free for the rate; `r` is the point a claim is made at, not a challenge. **A rename in the document is a rename in the implementations**: the Rust prover and verifier, `python-verifier/verifier.py`, and `guests/aggregate.py` name their variables after the document's symbols, so the four have to move together.
- **Doc labels are an API.** `crates/pcs` cites `thm:rbr` and `thm:mca-johnson` by name and several crates cite `doc/leanvm/main.tex` sections, so renaming a label breaks those pointers with nothing to catch it. `doc/leanvm/body/NN-*.tex` prefixes match section numbers, so inserting a section renumbers the rest.
- **No em-dashes or en-dashes in prose**, anywhere a human reads it: docs, LaTeX, comments, commit messages. Restructure with a comma, colon, parentheses, or two sentences.
- **Never hard-wrap prose in Markdown or LaTeX.** One paragraph is one line; let the editor wrap it. Artificial line breaks make every later edit a reflow, so diffs show rewrapped lines instead of changed words. Applies to `.md` and `.tex` alike; code blocks, tables and list items keep their own line.

## Soundness

- in the recursion program, the prover transmits advice to the verifier, called "hints". These advice should not be truster (a malicious prover should never be able to prove an invalid witness), and carefully checked by the verifier.

## Env knobs

| var                                                                                                     | effect                                           |
| ------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| `LEANVM_NUM_THREADS` / `RAYON_NUM_THREADS`                                                              | performance-worker count; `1` = sequential       |
| `LEANVM_PROFILE`                                                                                        | per-stage prover timings                         |
| `LEANVM_NO_ARENA`                                                                                       | disable the arena (less memory, slower)          |
| `ZK_ALLOC_STATS`                                                                                        | arena bytes/phase, high water, overflow          |
| `BENCH_REPEAT`, `BENCH_COOLDOWN`                                                                        | `--repeat`/`--cooldown` for `#[ignore]`d benches |
| `LEANVM_XMSS_N`, `LEANVM_HASH_N`, `LEANVM_HASH_UNROLL`                                                  | workload sizes in tests                          |
| `FLOCK_N_LOG`, `FLOCK_PROVE_TRACE`, `FLOCK_ZC_TIMING`, `LINCHECK_TRACE`                                 | flock batch size, stage traces                   |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_MIN_MU`, `PCS_SAMPLES`                                            | PCS throughput bench                             |
| `WHIR_TRACE`, `WHIR_NUM_VARS`, `WHIR_LOG_INV_RATE`                                          | WHIR NTT/Merkle split                        |
| `DBG_PROF{,_DUMP}`, `DBG_LOOPS`, `DBG_DISASM`, `DBG_LOWER`, `DBG_CSE`, `DBG_NO_CSE`, `DBG_PLACEHOLDERS` | compiler / guest-cycle attribution               |

## Side notes

- proofs, and thus proof size, are not deterministic; due to Proof of Work grinding, which is multi-threaded.
