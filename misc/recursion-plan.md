# Recursion (Ligerito recursive proof) — plan & status

Goal: a zkDSL guest program that verifies a leanVM-b proof in-circuit (the analog
of `../leanVM`'s `whir.py`/`recursion.py`), so proofs can be recursively
aggregated. leanVM-b's PCS is **Ligerito/BaseFold over GF(2^128)** (vendored
`flock-core`), so this is a verifier for leanVM-b's *own* proof format.

## Why leanVM-b is well-positioned
- **No extension field**: GF(2^128) is already 128-bit, so all verifier math is
  plain `MUL`/`XOR`. The reference's `DIM=5` extension machinery vanishes.
- **VM-native FS + Merkle already exist**: `transcript.rs` sponge and
  `vmhash.rs`/`merkle::hash_leaf` are built from the one `blake3` opcode, so the
  whole transcript + tree hashing replays in-circuit.
- **Challenger reconciliation** (crucial): leanVM-b *overrides* flock's
  `Challenger` (transcript.rs), so the PCS drives leanVM-b's own compress-sponge.
  `observe_f128_slice`/`sample_f128_vec` use trait defaults (per-element / n
  sequential samples). The entire PCS challenger surface = the compress-sponge.

## What `cpu::verify` does (the thing to replay in zkDSL)
seed sponge(pi, program_digest) → read announced sizes + commit root → bus (3×
GKR grand product + decompose) → 6× per-table zerocheck → PI-binding claim →
BLAKE3 pins → flock BLAKE3 R1CS reduction (zerocheck+lincheck+ring-switch) → ONE
stacked Ligerito opening → finish. Full Ligerito spec in the scratchpad notes
(`ligerito-verifier-spec.md`) — key: m22_secure = 3 levels, initial_k=6, r=2,
queries [298,187,131], grinding 0, 15 sumcheck messages; `sample_distinct_queries`
= `v.lo % block_len` with rejection sampling (dedup, sorted ascending).

## Methodology
Bottom-up gadgets, each a Rust→zkDSL emitter validated end-to-end via
`tests/recursion_gadgets.rs` (prove+verify a generated program against a REAL
leanVM-b transcript). Runtime sizes (μ, round counts, query counts) will be
dispatched to unrolled-const variants via `match_range`, exactly as `whir.py`
does. The harness will bake the inner seed cv, layout constants, and feed the
inner `Proof` (`stream: Vec<F128>` + `openings`) as `hint_witness` streams.

## Two findings that reshape the assembly
- **Compile-time specialization removes runtime dispatch.** The harness
  self-referentially compiles the guest for ONE known inner-proof shape, so every
  size (μ, level counts, query counts) is a compile-time constant baked in. The
  reference's `match_range`→unrolled-const dispatch is only needed to handle
  *varying* inner sizes in one program — an optimization for later. So the
  straight-line Rust→zkDSL codegen used by the gadgets IS the right tool; no new
  DSL control-flow capability is needed for a first end-to-end.
- **No compiler enrichment was needed for any primitive.** The existing zkDSL
  expressed all 10 gadgets. `assert` has only `==` and `log _ < _` (no `!=`); the
  nonzero check `x != 0` is done by exhibiting `x^-1` (`assert x·x⁻¹ == 1`).

## END-TO-END m33 (500-XMSS) LIGERITO OPENING VERIFIER — DONE & BENCHMARKED
`test_recursive_ligerito` (tests/recursion_gadgets.rs, #[ignore]) drives a real
m33_secure LigeritoProof (log_n=26, initial_k=6, 6 levels, queries
[290,177,145,132,126,124], fold-PoW [11,10,8,6,4,2], 994 query opens) through the
in-circuit verifier and proves+verifies it in leanVM-b. Real numbers (clean verifier,
after the cycle-reduction pass):
**1,164,128 cycles (2^20.2), 29,387 BLAKE3 (2^14.8), committed 2^24.70, proof 682 KiB,
prove 38.1s, verify 80ms** (inner commit+prove 54s; before the perf pass this was
2,569,442 cycles / 2^25.94 committed / 80s prove). Run:
`RAYON_NUM_THREADS=8 cargo test --release --test recursion_gadgets test_recursive_ligerito -- --ignored --nocapture`.

Per user direction, the verifier does NO dedup/sort — the opening is *transmitted*
compressed (index-dedup + octopus) and *expanded* to flat per-query form before
verification (storage compression only; flock's `_with_basis` path samples queries
in transcript order and verifies one Merkle path per query).

The verifier is ONE hand-written config-driven zkDSL program,
**`tests/ligerito_recursive.py`** (~330 lines) — no Rust codegen. Per-level
structure comes from placeholder-filled constant arrays (QUERIES/KLVL/DEPTH/LMC/
FOLDBASE/SVK/...); the program loops over levels with `unroll` + folded `if`s and
over queries with `mul_range`: sponge + RoundQuad folds + per-fold PoW + query
phases (sample/enforced loops) + per-query Merkle loops + per-query residual loops
(novel-basis Ŵ_k + foldyr) + terminal inner==t_r. The harness (`gen_clean`)
computes the config arrays + flat expanded witness hints. Validated at the tiny
config (`recursive_ligerito_tiny`), a small 3-level config (`ml_clean_small`), and
m33. Compiler features added for this: `GEN ** <expr>`, constant arrays + `len()`,
`base ** e` (square-and-multiply), compile-time `-`, const-folded `Let`/buffer
sizes, and folded-`if` branches lowering transparently (bindings persist).
Cycle-reduction pass (-55%): query sampling packs floor(128/depth) positions per
squeeze (disjoint d-bit chunks of one uniform squeeze — flock + mirror + guest in
sync), so ONE 128-bit decomposition covers ~6 queries (994->143; dec128 was 54% of
all cycles); the decomposition is fused with position extraction (`decq` stores
each chunk's q_field + bit-pointer as a side effect of reconstructing the
squeeze); the enforced-sum dot, Merkle leaf hash, and path walk are fused into one
per-query pass (each row value read once); the walk step is an inline branch-free
select (left = node + bit·(node+sibling)); foldyr is @unroll-inlined over stack
cells. Profiling via `DBG_PROF=1` (per-function cycle histogram in execute).

Remaining broader goal: the FULL `cpu::verify` replay (bus GKR + 6 zerochecks +
flock BLAKE3 R1CS reduction) + recursion harness.

## END-TO-END LIGERITO OPENING VERIFIER — DONE (tiny instance)
`ligerito_verify_end_to_end` (tests/recursion_gadgets.rs) is a complete zkDSL port of
`multilevel_verifier_with_basis_succinct` — leanVM-b's actual Ligerito opening — that
verifies a REAL flock `LigeritoProof` end-to-end, proven+checked by leanVM-b's own
prover/verifier. Full protocol: sponge replay + RoundQuad sumcheck + enforced-sum glue
+ single-path Merkle opens (query bits pinned by 128-bit decomposition) + residual
(novel-basis Ŵ_k recurrence + eval_b + terminal inner==t_r). Cross-checked vs a Rust
mirror that matches native accept. Tiny config (log_n=8, 1 query/level) for
tractability; the emitter is config-driven. To reach production m22: swap the
single-path Merkle for the octopus multi-proof (or harness-expand to independent
paths) and loop the query phases — all arithmetic already generalizes; no new
capability. The top-level `verify_opening_batch_mixed_ligerito_stacked` wraps this
with per-claim `ring_switch::verify_succinct` (DONE, gadget 12) + γ-combine +
`eval_b_residual`, plus the full `cpu::verify` replay (bus GKR + zerochecks + flock
BLAKE3 reduction) and the recursion harness.

## Progress into the actual opening (stage 1a DONE)
`ring_switch::verify_succinct`'s **claim check** is ported + tested in-circuit
(gadget 10): runtime φ₈ F₈-Lagrange (`build_claim_weights`) + the 128-term
weighted inner product, cross-checked against flock. This is the first real
stage of the production opening, and it retires the F₈-Lagrange hard sub-problem.

Remaining in `verify_succinct` (stage 1b): the `tensor_algebra_transpose` +
`sumcheck_claim`. Concrete feasibility finding — the 128×128 bit-transpose is
inherently ~128·(128 boolean + 128 reconstruct + 128 inner) ≈ 80k ops, which
**cannot be flat-unrolled** (the generated program is too large for the compiler
to be practical). It requires a **nested runtime loop** (outer i∈0..128, inner
b∈0..128) with accumulators threaded through write-once HeapBufs — the
`runtime_observe_loop` pattern, nested. Buildable, but intricate (multi-cycle
debug). No cheap algebraic bypass exists (the transpose touches every bit).
`build_eq(r_dprime)` (128-value eq tensor from 7 samples) is a small runtime loop.

## The target is the LIGERITO backend (not basefold)
leanVM-b's opening is `verify_opening_batch_mixed_ligerito_stacked` (pcs.rs:1802)
→ `ligerito::multilevel_verifier_with_basis_succinct` (ligerito.rs:3389). The
single-claim `verify_opening`→`basefold::verify` path (with NTT `fri_fold_coset`)
is a DIFFERENT scheme leanVM-b does not use — do not port it.

Remaining hard sub-problems on the Ligerito path: (1,2) ring-switch transpose +
φ₈ F₈-Lagrange — BOTH DONE (stage 1). (3) the Ligerito core's per-level query
opens: `sample_distinct_queries` (v.lo % block_len, rejection-sampled) + Merkle
multi-proof (sidestep: harness expands the octopus to independent per-query paths,
verified by the Merkle gadget) + `induce_sumcheck_enforced_sum` (eq-tensor · opened
rows). (4) the final residual: `induce_sumcheck_evaluate_at_residual` (novel-basis
Ŵ_k recurrence, `sks_vks` constants) + `eval_b_residual`/`eval_rs_eq` (TensorAlgebra
recurrence). NO NTT arithmetic anywhere on this path. Methodology: drive `pcs::open`
with a leanVM-b `ProverState` (compress-sponge, NOT flock's native `FsChallenger`),
cross-check each stage vs flock, port stage-by-stage — ring_switch done, Ligerito
core next.

## Status — DONE (all committed on branch `recursion`, tests green)
1. **bit-decomposition** — hint bits, `b*b==b`, reconstruct `Σ b_i·GEN**i` (full
   128-bit, exact). Basis for query indices + PoW leading-zero checks.
2. **FS sponge replay** — observe_f128 = compress(cv,[x,1]); sample = compress(cv,
   [0,4]); observe_bytes(root) = len-frame + DS_BYTE words; transcript reader
   (next_scalar loop over a hinted stream via GEN-cursor). Byte-identical to
   `vmhash::compress`. `fs_ref::seed_cv` mirrors Sponge seeding.
3. **degree-2 sumcheck / GKR** — code-generated unrolled `gkr::verify_product`
   replay: eq-trick round checks + Lagrange at {0,1,g} (baked inv-denominators)
   + layer fold; validated μ∈{1,2,3,5} against native `gkr::prove_product`.
4. **Merkle path verify** — leaf MD-hash + `compress` walk with index-bit sibling
   ordering; validated all queries at depth 1..4.
5. **runtime-count loop** — `mul_range` (runtime bound) with the sponge chained
   through a write-once HeapBuf (Fibonacci idiom).
6. **RoundQuad sumcheck** — the Ligerito fold (`b=t_r+u_2` consistency baking).
7. **grand-product balance verifier** — three GKR products + `push==pull` +
   `count!=0` over one transcript (first multi-sub-protocol composition; the bus).

## Status — TODO (the assembly)
6. **Enrich compiler as needed** — candidates: multi-file imports (modular guest
   libs), a `mul_range`+HeapBuf carry idiom helper, maybe runtime-int ergonomics.
   Track each gap when hit.
7. **Zerocheck verifier** (constraints.rs replay) — same sumcheck core, samples
   eta+r upfront, claim starts 0, final check `eq_acc·c_eval(eta,evals)`; the
   6-table version needs per-table AIR-constraint codegen (mirror of the
   reference's AIR-evaluator codegen, driven by `tables.rs`).
8. **Ligerito opening verifier** — the big one. Sub-pieces:
   - RoundQuad sumcheck fold (2-eval messages, coeff form, b=t_r+u_2).
   - `sample_distinct_queries` in-circuit: hint total sample count T, loop T,
     maintain sorted "seen" set, assert `count` distinct+sorted, rejects collide.
   - octopus multi-proof (shared internal nodes) — generalize the Merkle gadget.
   - ring-switch `verify_succinct`: 128-dim tensor-algebra transpose + inner
     products + `build_claim_weights`.
   - enforced-sum + residual eval: novel-basis Ŵ_k recurrence, eq-tensor weights.
   - terminal `inner == t_r` check.
   Only end-to-end-testable against a real `pcs::open`; build a Rust mirror
   (`lig_ref`) first, cross-check vs flock, then port stage-by-stage.
9. **flock BLAKE3 R1CS reduction verifier** (zerocheck+lincheck+ring-switch).
10. **Full `verify()` replay + harness** — compose all; serialize inner `Proof`
    into hints; compute layout/shape placeholders; self-referential compile;
    deferred bytecode-MLE claim + cross-level reduction; drive prove/verify.
