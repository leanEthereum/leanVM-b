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

## The genuinely-hard remaining sub-problems (algorithmic, not DSL gaps)
The full flock opening (`verify_opening_batch_mixed_ligerito_stacked` → ring_switch
+ basefold FRI) has ~290 FRI queries (rate ½, 120-bit) and these hard-in-circuit
pieces: (1) ring-switch `tensor_algebra_transpose` — a 128×128 F₂ bit-transpose
of `s_hat_v` (needs 128 bit-decompositions + recompose, or an algebraic bypass);
(2) `build_claim_weights`'s φ₈-embedded F₈ Lagrange; (3) BaseFold FRI fold checks
across NTT-domain positions (additive-NTT twiddle arithmetic); (4) the octopus
multi-proof (sidestep: harness expands to independent per-query paths, verified by
the Merkle gadget). Each is real work; the whole is comparable in scale to the
reference's multi-file `rec_aggregation` crate. Methodology: build a flat Rust
mirror (drive `pcs::open` with a leanVM-b `ProverState` so the transcript is the
compress-sponge, NOT flock's native `FsChallenger`), cross-check vs flock, port
stage-by-stage.

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
