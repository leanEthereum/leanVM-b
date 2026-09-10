# Continuing from 126 to 127 bits

The 126-bit theorem is proved. The 127-bit bound is proved for every original hash budget $q\ge3\cdot2^{114}$ by [security127_of_large_budget](SphincsSecurity/Proof/Security127LargeBudget.lean). The full 127-bit theorem remains unfinished because smaller positive budgets still need their bound. Keep the original scheme, SUF game, signing cap and whole-experiment hash budget in [Statement.lean](SphincsSecurity/Statement.lean) fixed.

The completed large-budget reduction uses `forgeAdvantage_le_native_bound`: for $x=q/2^{128}$ and $q\le2^{127}$, original SUF probability is at most $2x-x^2+(11/65536)x+q/2^{169}+2^{-700}$. Exact Lean arithmetic bounds this by $q/2^{127}$ when $q\ge3\cdot2^{114}$; larger budgets use probability at most one. The reference dummy is explicitly instantiated by a proved valid encoding, so `security127_of_large_budget` has only the original hash-bound premise and the budget-range condition.

The native bookkeeping invariants, whole-run exception classification and both exception histories are bounded. `exceptionHistorySourceGame_prefix_le` gives $2^{-700}$. `exceptionHistorySourceGame_cache_le` gives $q/2^{169}$ by freezing a second-moment weight at the first exception, accumulating native message charges and bounding them by actual hash calls. Both histories include failed signing invocations and steps after the certificate monitor stops. Erasing their passive flags recovers the monitored source game exactly.

The OTS query interpreter is defined in [OtsPrefixSimulation.lean](SphincsSecurity/Proof/OtsPrefixSimulation.lean). For each fixed oracle, it reconstructs the original game after secret sampling, including the signing log, verification and original hash-cost trace. Its program is unchanged when private prefix entries in its auxiliary oracle are replaced arbitrarily. Each external prefix query requests one low reply and combines it with the full reply's high part; the reconstructed signer makes no prefix queries.

The next work is the small-budget interval: construct the endpoint-dependent auxiliary sampling law, prove its independence from the selected starting secret and low prefix tables, retain the additional monitoring observations, and cap ideal execution at the original budget. Then prove completed-witness charges with one shared query allocation and establish coverage under forced FTS transitions. The fixed-oracle reconstruction does not establish these probability comparisons. The full 127-bit theorem must combine that interval with the completed large-budget theorem and pass the axiom audit.

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
