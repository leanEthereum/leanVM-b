# Continuing from 126 to 127 bits

The 126-bit theorem is proved. The 127-bit bound is proved for every original hash budget $q\ge3\cdot2^{114}$ by [security127_of_large_budget](SphincsSecurity/Proof/Security127LargeBudget.lean). The full 127-bit theorem remains unfinished because smaller positive budgets still need their bound. Keep the original scheme, SUF game, signing cap and whole-experiment hash budget in [Statement.lean](SphincsSecurity/Statement.lean) fixed.

The completed large-budget reduction uses `forgeAdvantage_le_native_bound`: for $x=q/2^{128}$ and $q\le2^{127}$, original SUF probability is at most $2x-x^2+(11/65536)x+q/2^{169}+2^{-700}$. Exact Lean arithmetic bounds this by $q/2^{127}$ when $q\ge3\cdot2^{114}$; larger budgets use probability at most one. The reference dummy is explicitly instantiated by a proved valid encoding, so `security127_of_large_budget` has only the original hash-bound premise and the budget-range condition.

The native bookkeeping invariants, whole-run exception classification and both exception histories are bounded. `exceptionHistorySourceGame_prefix_le` gives $2^{-700}$. `exceptionHistorySourceGame_cache_le` gives $q/2^{169}$ by freezing a second-moment weight at the first exception, accumulating native message charges and bounding them by actual hash calls. Both histories include failed signing invocations and steps after the certificate monitor stops. Erasing their passive flags recovers the monitored source game exactly.

The OTS query interpreter is defined in [OtsPrefixSimulation.lean](SphincsSecurity/Proof/OtsPrefixSimulation.lean). For each fixed oracle, it reconstructs the original game after secret sampling, including the signing log, verification and original hash-cost trace. Its program is unchanged when private prefix entries in its auxiliary oracle are replaced arbitrarily. Each external prefix query requests one low reply and combines it with the full reply's high part; the reconstructed signer makes no prefix queries.

The raw sampling decomposition is proved in [OtsPrefixReferenceSeed.lean](SphincsSecurity/Proof/OtsPrefixReferenceSeed.lean). Conditional on the reference family, the low prefix tables are uniform and independent of the auxiliary seed, whose distribution uses no secret-key fields. The prefix depth may be chosen from that reference family. A uniform encoding table over a fixed domain supplies the remaining encoding rows. Rebuilding the oracle from these samples has exactly the original reference-family oracle distribution, and its prefix low and high replies equal the sampled rows.

The endpoint reconstruction is proved in [OtsPrefixSeedReconstruction.lean](SphincsSecurity/Proof/OtsPrefixSeedReconstruction.lean). Auxiliary oracle and frontier reconstruction uses the selected private prefix only through its endpoint. Replacing the chosen starting-secret field leaves the endpoint-supplied program unchanged. [OtsPrefixSourceGame.lean](SphincsSecurity/Proof/OtsPrefixSourceGame.lean) gives an exact original-game representation using this program with that secret field set to zero, independent low tables and auxiliary seeds. The real source inherits the original whole-experiment hash budget.

The chosen starting secret is separated from the other secret coordinates by an exact finite equivalence in [OtsPrefixSecretSampling.lean](SphincsSecurity/Proof/OtsPrefixSecretSampling.lean). [OtsPrefixObservedSource.lean](SphincsSecurity/Proof/OtsPrefixObservedSource.lean) identifies the original source with a mixture of the generic observed-prefix real runs. Discarding the endpoint and observed rows preserves the original forgery probability and hash-cost trace. [OtsPrefixObservedBudget.lean](SphincsSecurity/Proof/OtsPrefixObservedBudget.lean) transfers the original hash budget to each supported conditional real run.

The bounded OTS interface is supplied by [OtsPrefixCappedSource.lean](SphincsSecurity/Proof/OtsPrefixCappedSource.lean). An analytical cap stops before the next prefix query would exceed $q$, returning an ordinary result rather than dropping probability mass. Its syntactic query bound is unconditional. The explicit prefix counter is bounded by the original hash-cost trace, so the cap erases exactly on every supported conditional real run. For $q<2^{128}$, the positive likelihood factor puts ideal support inside real support: the ideal cap never stops either, and its completed outputs obey the original whole-experiment hash budget. The concrete capped interface needs no additional prefix-query-bound premise.

The shared OTS-prefix allocation is proved in [ReferenceFamilyAllocation.lean](SphincsSecurity/Proof/ReferenceFamilyAllocation.lean). One recorded external-query program preserves the original SUF probability, and the sum of its counts over all OTS prefixes is at most the original budget, both for each supported execution and in expectation. [OtsPrefixAllocation.lean](SphincsSecurity/Proof/OtsPrefixAllocation.lean) identifies each fixed-oracle interpreter count with its charge in this common program. The analytical cap also preserves the original result jointly with its prefix-query count.

The counter transport through reference sampling and the secret split is proved in [OtsPrefixSeedAllocation.lean](SphincsSecurity/Proof/OtsPrefixSeedAllocation.lean) and [OtsPrefixObservedAllocation.lean](SphincsSecurity/Proof/OtsPrefixObservedAllocation.lean), preserving the result jointly with its actual prefix-query count. [OtsPrefixIdealAllocation.lean](SphincsSecurity/Proof/OtsPrefixIdealAllocation.lean) averages the capped likelihood comparison over those samples and proves $(1-q/2^{128})\sum_c\mathbb E Q_c^{\rm ideal}\le q$. For $q<2^{128}$, the established cap contract excludes termination in the ideal law. The loss is one uniform likelihood factor, with no factor for the number of chains.

The joint reservation is proved in [ReferenceQueryAllocation.lean](SphincsSecurity/Proof/ReferenceQueryAllocation.lean). The recorded original law satisfies $Q+A_{\rm enc}+A_{\rm other}+A_{\rm msg}\le q$ on every supported execution. The conditional comparison preserves that reservation: $(1-q/2^{128})\sum_c\mathbb E Q_c^{\rm ideal}+\mathbb E_R[A_{\rm enc}+A_{\rm other}+A_{\rm msg}]\le q$. The message charge counts every proper message call at the actual public parameter, including internal signing attempts, repetitions and verification. External encoding and other non-message charges conservatively count all calls, so they also bound the fresh nonreference and structural subsets used by the paper estimates. External message calls are included only in the native message trace.

The next work is to retain the additional monitoring observations and prove the completed-witness estimates against this joint allocation. The forced-FTS transitions also need their coverage estimates. The full 127-bit theorem must combine the resulting small-budget bound with the completed large-budget theorem and pass the axiom audit.

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
