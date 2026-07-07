# End-to-end 1→1 recursion — working notes (guest spec)

STATUS: DONE (tests/recursion_e2e.rs `recursion_1to1`). Inner: 531 cycles, all six
tables, committed 2^17.13. Guest: 777,795 cycles, 23,935 BLAKE3. Outer: prove
33.7s, verify 105.7ms + 211ms native deferred checks, proof ~682 KiB. Deferred and
bound to the outer public input: 12 bytecode MLE claims, the lincheck matrix
evaluation (one sparse nnz pass native), the two ring-switch tensor transposes and
the two eval_rs_eq weights (bound-data claims; see the caveat below). Remaining
for 2→1: batch the bytecode/matrix claims with the sumcheck of doc.tex §Deferred
evaluation claims; the tensor/eval_rs_eq deferrals do not aggregate (they grow the
public input linearly with the tree), so either accept that or find an
in-circuit-cheap formulation (the transpose costs ~80k cycles as a gadget; the
eval_rs_eq tensor steps cost 2 transposes per coordinate, which is why both are
deferred).

Goal: a guest program replaying `cpu::verify(inner_program, pi, inner_proof)`
in-circuit with the bytecode + flock-matrix evaluations deferred (doc.tex
§Deferred evaluation claims), proven as the outer proof.

## The verify() flow the guest replays (all shapes compile-time for a fixed inner)

1. **Seed**: sponge `Sponge::new(b"leanvm-b", [pi0, pi1, dig0, dig1])`. The inner
   program digest is a baked constant (pure function of the fixed inner bytecode).
2. **read_public**: 7 `next_scalar`s (log_mem + 6 row_counts). Guest observes and
   asserts they equal the baked config (compile-time specialization).
3. **read_commitment**: 2 `next_scalar`s (root words).
4. **Bus** (`leaf::verify_balance`):
   - sample α; `grind_check(bits)` with `bits = grand_product_grinding_bits`
     (baked; raw nonce word + leading-zero check — fold-PoW gadget); sample γ.
   - `gkr::verify_product` ×3 (push/pull/count; μ's baked). Per layer i (mu..1):
     k=mu−i rounds of [3 scalars, sample, eq_acc update, claim via lagrange at
     {0,1,g}], then 2 scalars (eval0/eval1), sample c, claim=interp. Matches the
     validated gkr gadget.
   - `count_root != 0` via hinted inverse.
   - balance: `push_root·d_pull == pull_root·d_push`, `d_side =
     Π_b (γ + default_fingerprint_b)^(2^κ_b − real_b)` — fingerprints are α-polys
     with baked coeffs; exponents baked (`**` square-and-multiply).
   - decompose ×3 (push α,γ; pull α,γ; count α=1,γ=0): per block, eq_hi over
     baked selector bits × ζ_hi; coords: Const baked, Index → `index_mle(ζ_lo)`,
     Col/GCol → `next_scalar` (claim pool), **Public → DEFERRED**: hinted value +
     bytecode claim (col c ∈ 6, point ζ_lo). 6 public cols × {push,pull} = 12
     deferred bytecode evals at 2 points. Stack the 6 cols as ONE bytecode MLE
     (3 selector vars + log_bytecode) → 12 claims on one polynomial.
   - check decomposed value == leaf claim value, ×3.
5. **Zerochecks ×6** (`constraints::verify` per table): sample η, sample r (τ_t
   baked), τ_t rounds of [3 scalars, sample, eq_acc, lagrange], then n_cols_t
   scalars (evals), final check `claim == eq_acc·C_t(η, evals)` — **C_t = the
   table's AIR constraint evaluator, codegen from tables.rs** (degree ≤ 2).
6. **PI claim**: sample r_m; value = interp(pi0, pi1, r_m); claim on MEM col.
7. **BLAKE3 pins**: pin_point = first value-col bus claim's point;
   `mle_of_ones_then_zeros(n_b3, point)` (baked n_b3, O(n_log²) formula);
   3 pin claims on QPKD at slot_points.
8. **read_stack_proof**: hint_bytes = len word + ⌈len/16⌉ raw words (NOT observed
   — guest skips/ignores; the values arrive as their own hint streams and are
   bound by the replay observes); 1 opening (the ligerito hint channel).
9. **flock verify_reduction** (Blake3Setup::verify_reduction):
   - zerocheck verify (univariate-skip; TODO read flock_prover zerocheck verify —
     check whether C₀ = identity ⇒ no matrix eval on the c-side).
   - lincheck verify: label absorb; sample α_lc; **fold_alpha_batched DEFERRED**:
     instead of building comb_vec (nnz pass) + folding it, the guest (a) replays
     the round chain (14 e1/einf observes + samples), (b) observes z_partial
     (64), (c) takes the matrix part of `final_sum` as a HINT + deferred claim
     [weighted eval: weight = quirky-eq(z_skip, x_inner_rest) over rows ⊗
     (eq(r_rounds)⊗z_partial) over cols], (d) computes the const-pin β term
     itself, (e) asserts running == matrix_part + pin_part. Steps 6–7 (fresh
     z_skip, φ8 Lagrange on z_partial) ported (φ8 gadget exists).
   - Deferred matrix claims are weighted (u_t, v_t per-side dense tables), which
     the batching sumcheck supports: terminal W(r*) evaluation is succinct
     (φ8-lagrange MLE = 64 terms; eq⊗z_partial MLE = 64 terms).
10. **ring_switch_verify + pcs::verify**: γ-combine + per-claim
    ring_switch::verify_succinct (gadget DONE) + W_λ/eval_b weight evaluation
    (block-sparse slot claims: per claim, eq over baked selector bits ×
    eq(low_point) at the residual points — share the ris-part, per-y factor
    over yr_log_n coords) + the Ligerito opening core (DONE, config-driven,
    inner m = 22 for a small inner program).
11. **finish**: guest consumed the whole stream hint (assert cursor == len).

## Outer public input
The outer proof's `pi` (2 field elements) = hash of a buffer carrying: inner pi,
inner-proof acceptance, and the deferred claims (bytecode: point+value per claim
or post-batch single claim; matrices: points+values). For 1→1 first cut: defer
WITHOUT batching (n_rec=1: forward the fresh claims directly; batching sumcheck
comes with 2→1). The native outer harness checks the deferred claims directly.

## Mirror strategy
No hand-written duplicate: instrument `Sponge` with an env-gated op trace
(observe/sample/absorb_bytes/pow/raw), run the REAL `cpu::verify` on the inner
proof, and consume the trace + the real `Layout` (internals exposed pub) to
generate guest config + hints + checkpoints. Zero drift.

## Inner program (non-trivial)
zkDSL program with a BLAKE3 hash chain + mul_range loop + DEREF/JUMP traffic;
log_mem=16, stacked mu=15 (MIN_MU) ⇒ m=22 ⇒ inner opening is the m22 3-level
config (config-driven guest handles it).
