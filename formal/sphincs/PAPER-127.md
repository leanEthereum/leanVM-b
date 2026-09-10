# Continuing from 126 to 127 bits

The 126-bit theorem is proved. The 127-bit theorem is not: neither nontrivial budget interval has its complete original-game inequality yet. Keep the original scheme, SUF game, signing cap and whole-experiment hash budget in [Statement.lean](SphincsSecurity/Statement.lean) fixed.

The next milestone is the large-budget inequality. The original query bound now gives `forgeAdvantage_le_native_bound_add_cache_history`: for $x=q/2^{128}$ and $q\le2^{127}$, original SUF probability is at most $2x-x^2+(11/65536)x+\Pr[E_{\rm cache}]+2^{-700}$. Here $E_{\rm cache}$ records whether a cache exception occurred before or after any native step. Erasing the history flags recovers the monitored source game exactly. What remains is to bound this native cache-history probability by $q/2^{169}$.

The native bookkeeping invariants and whole-run exception classification are proved. Successful strong forgeries with a stopped monitor imply a recorded cache or proposal-prefix exception; primitive stops are not charged again. `exceptionHistorySourceGame_prefix_le` bounds the proposal-prefix history by $2^{-700}$ through an exponential weight on the actual adaptive law. The cache predicate need not persist as the cache grows, so its remaining bound must cover the recorded history rather than only the terminal cache.

The cache estimate now uses second moments: the deficit weight grows by at most $1023/2^{186}$ per message hash, and the cached-index weight by at most $2^{-170}$. Their sum is below $2^{-169}$, which suffices for the closing contract. The random-oracle and native query and signing kernel estimates are in `CertificateCacheExceptionKernels` and `RetainedResidualCacheKernels`. Their charges still need to be accumulated along the passive history and bounded by the original hash budget, including after the certificate monitor stops.

The small-budget interval separately needs the concrete OTS prefix simulator and completed-witness charges, plus coverage under forced FTS transitions. The generic endpoint likelihood and record-and-length projection are available; their concrete comparisons remain obligations.

| Note | Use |
| --- | --- |
| [Current proof status](paper-127/critical-path-review.md) | Completed interfaces, next steps and failed shortcuts. |
| [Closing contract](paper-127/minimal-closing-contract.md) | Sufficient constants, both budget intervals and the mathematical derivations. |
| [Small-range gate audit](paper-127/small-range-gate-audit.md) | Permitted observations, high-half counterexample and forced-FTS kernels. |
| [Small-budget transfer](paper-127/small-budget-transfer.md) | Shared query allocation and witness comparisons. |
| [Reference-frontier transfer](paper-127/reference-frontier-transfer.md) | Causal endpoint simulation, reference rows and cost preservation. |
| [Initial prior](paper-127/initial-prior-and-composition.md) | Exact hidden-coordinate sampling and the distinction between latent tables and observed history. |

Run the remaining paper checks with Python 3:

```sh
python3 paper-127/closing-arithmetic.py
python3 paper-127/adaptive-kernel-checks.py
python3 paper-127/transfer-kernel-checks.py
```

These are exact arithmetic and finite-model checks. They do not establish the missing concrete probability comparisons or replace the Lean proof.
