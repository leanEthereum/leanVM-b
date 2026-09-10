# Continuing from 126 to 127 bits

The 126-bit theorem is proved. The 127-bit theorem is not: neither nontrivial budget interval has its complete original-game inequality yet. Keep the original scheme, SUF game, signing cap and whole-experiment hash budget in [Statement.lean](SphincsSecurity/Statement.lean) fixed.

The next milestone is the large-budget inequality. The original query bound now gives `forgeAdvantage_le_monitored_bound_add_exception`: for $x=q/2^{128}$ and $q\le2^{127}$, original SUF probability is at most $2x-x^2+(11/65536)x+\Pr[E_{\rm native}]$. Here $E_{\rm native}$ is a successful strong forgery with the certificate monitor stopped. A surviving strong forgery supplies a full certificate, and an active monitor counts it in its native bank. Erasing the monitor recovers the retained source game exactly. What remains is to bound $E_{\rm native}$ by the original exceptional allowance, using `stopAfter := fun _ _ _ _ => false`.

The bookkeeping invariants needed for that bound are proved on the native execution: exact spent counts while active, cache size bounded by actual hash calls, cached digests for every successful signing entry, and signing-cap and macro-budget conditions inherited from a valid bounded continuation. `monitoredStep_stopped_iff_prefix` identifies the remaining stop after a successful active step with no cache exception. Lift this step classification to the whole-run exception and bound the actual cache and proposal-prefix events.

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
