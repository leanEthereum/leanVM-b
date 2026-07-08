# Shape-generic recursion guest: plan

Goal: ONE compiled recursion bytecode verifying ANY inner proof of the
baked inner program (any cycle count, memory size, hash count), like
../leanVM's single recursion.py. Today the generator bakes ~60
shape-dependent placeholders per (program, shape); the guest asserts the
announced sizes equal the baked ones. After this effort, placeholders are
protocol constants plus MIN/MAX bounds and small per-candidate tables, and
the shape is read from the transcript at runtime.

## Available DSL primitives (all exist today)

- `assert log(x) < k`: range check in the exponent, 3 cycles.
- `match` / `match_range(log(x), range(a, b), lambda i: f(i))`: dispatch a
  runtime g-power exponent to Const-specialized arms, ~7 cycles. Arms are
  branch-local; escape values through HeapBufs or return values.
- `mul_range` with a RUNTIME stop bound (threaded through the helper frame).
- Runtime `if` (values written to heap escape; frame bindings do not).
- `HeapBufDyn(e)`: runtime-sized allocation.
- Hinted-then-verified data (leanVM's `table_sort_perm` pattern).

## Shape parameters

Everything derives from the 7 announced words (log_mem, six table row
counts) plus the hash count implied by counts[5]. Derived: per-table
log-heights tau_t, the three GKR depths mu_s, the stacked layout, the
committed total m, flock's m_r1cs, both Ligerito level structures.

Announced counts are integer words, not g-powers: hint tau_t, verify with
a dec128 of the count that bit tau_t-1 is the top set bit (or the count is
exactly 2^tau_t). Then tau_t lives as a g-power g^tau_t for dispatch and
range checks. Same for log_mem (announced directly as a small integer:
convert by hinting g^log_mem and checking the match via a baked power
table selected with match_range).

## Strategy per phase (in guest order)

1. Announced sizes (P1). Read 7 words, obs as today, range-check each
   count (dec128, 6x ~900 cycles), derive tau_t/mu_s as g-powers. Delete
   the `assert x == ANN[i]` equality. MINLOG/MAXLOG placeholders.

2. GKR trees x3 (P1). Rounds = mu_s, bounded by MUMAX. Convert the round
   loop to runtime `mul_range(0, mu_s_gpow)` with the fs sponge threaded
   through HeapBuf chains (the sqz_chain pattern already in the guest);
   zeta writes via the loop cursor. Downstream consumers of zeta iterate
   with the same runtime bound. Alternative if chains get awkward:
   max-unroll to MUMAX with `if r < mu` guards (costlier bytecode, keep as
   fallback).

3. Bus balance + decompose + claim pool (P4, hardest). The layout tables
   (CT/CVAL/CSLOT/CSEL/SELN/NOVER/YTHI/CPOFF/CPLEN, NCLAIMS) implement the
   sort-and-pack of table columns by height. Hint the sorted order and the
   packed layout; verify in-circuit: (a) hinted order is a permutation,
   sorted by height (leanVM pattern, ~30 lines); (b) offsets are cumulative
   sums of 2^tau_t x ncols_t in the exponent (g-power MULs, additive in the
   exponent, so cumulative offsets are products of g^{2^tau}... NOTE:
   offsets are integers, not exponents; verify instead in the exponent
   domain per block: each block's slot count is a power of two, and the
   selector identities already checked per claim bind values to slots);
   (c) NCLAIMS becomes a runtime bound on the claim loops. This phase needs
   its own design pass; the guardrail is that every hinted layout entry is
   consumed by an equality the transcript or the opening already enforces.

4. AIR zerochecks x6 (P2). tau_t rounds: runtime mul_range with chained
   fs; the phi8 Horner inside a round is fixed-size (unrolled 8) so the
   body has no const-array-by-round indexing. TAUMAX bound placeholder.

5. Flock reduction (P2). LCR = K_LOG - 6 is protocol-fixed. MR1CS, NMLV,
   NB3, NLOGB3 derive from counts[5]: runtime loops for the univariate-skip
   rounds and the PIN prefix loop (NLOGB3+1 iterations, runtime bound).

6. Ring switch (nothing to do). Fixed 128/7 structure; QPKDV varies with
   m_r1cs: runtime bound on the z_vals loops.

7. Ligerito openings x2 (P3): stacked (m from the shape) and flock's
   (m_r1cs from NB3). Level structure = VerifierConfig::level_shapes(m) +
   derive_profile(m): bake a CONFIG TABLE indexed by candidate m in
   [MINM, MAXM] (~12 rows, each row: nlevels, then per-level bits, queries,
   k, depth, blocks, nsq, padded to MAXLEVELS), emitted by the generator
   from the same derive_profile the prover uses. Select the row with
   match_range(log(g^m)); the level loop stays unrolled to MAXLEVELS with
   a `if lvl < nlevels` guard; query/fold/squeeze loops take runtime
   bounds from the selected row. Grinding bit counts come from the row.
   Hint buffers (lrows/lpaths/lsbits/...) sized for MAXM; offsets become
   runtime values accumulated in the exponent (pointer = ptr * g^len,
   maintained as a cursor instead of baked *OFF arrays).

8. Aggregation (P5). Deferred point lengths vary per sub (kbc_s, taus_s):
   runtime bounds; DEFSZ becomes the MAX layout; the batching sumchecks
   run to the max announced rounds with guards.

9. Generator (every phase). Emits bounds + candidate tables instead of
   exact shapes; pads every witness entry to the compile-time hint length
   (WitnessHeap len is compile-time; the guest reads only the prefix it
   derives). End state: the rep map is shape-independent — add a generator
   assert that two different inner shapes produce IDENTICAL placeholder
   maps, which is the definition of done.

10. Milestone test (P5): recursion_2to1_mixed — inner A (1 << 13 iters)
    and inner B (1 << 15 iters), one guest bytecode, both verified by the
    SAME compiled program. Keep recursion_2to1 green at every phase.

## Cost expectations

- Runtime-loop conversions: a few ops/round overhead (fs chains through
  heap instead of stack pairs); guest cycles should stay within ~5%.
- match_range dispatch: ~7 cycles per select, negligible.
- The bytecode GROWS only where max-unroll replaces exact-unroll (GKR
  fallback, MAXLEVELS guard loop): estimate < 2x total; the verify_sub
  function refactor already brought it to 2^17.
- dec128 of 6 counts + range checks: ~6k cycles per sub.

## Order of execution

P1 (announced + GKR) -> P2 (zerochecks + flock sizes) -> P3 (ligerito
config tables) -> P4 (stacking hint+verify) -> P5 (aggregation + padding +
mixed test + shape-independence assert). Each phase lands with the suite
green and recursion_2to1 numbers recorded in the commit message.
