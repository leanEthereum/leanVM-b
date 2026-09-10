# Continuing from 126 to 127 bits

The 126-bit theorem is proved. The 127-bit theorem is not: neither nontrivial budget interval has its complete original-game inequality yet. Keep the original scheme, SUF game, signing cap and whole-experiment hash budget in [Statement.lean](SphincsSecurity/Statement.lean) fixed.

The next milestone is the large-budget inequality. The primitive and certificate bounds already share one native execution and follow from the original query bound. Every surviving strong forgery now yields a full target certificate: signing history ties disclosed secrets to successful log entries, and canonical replay excludes the forgery's own digest input. What remains is to put that certificate into the counted native bank and transfer the original exceptional allowance.

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
