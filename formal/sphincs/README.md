# SPHINCS security in Lean 4

The public theorem proves **126 bits of classical strong unforgeability in the random-oracle model**, with at most `2^24` signing requests per key pair. **127 bits remains unfinished.** The bound $q/2^{127}$ is proved for budgets $q\ge3\cdot2^{114}$; smaller positive budgets remain open.

[Statement.lean](SphincsSecurity/Statement.lean) defines the concrete parameters, serialized hash inputs, algorithms, original SUF game and security statements. The claim uses independently sampled secret leaves and a random oracle; instantiating that oracle with BLAKE2s or deriving all secrets from a seed is outside this theorem. The whole-experiment query budget includes key generation, signing failures, repeated calls and final verification.

## Build and audit

Use the pinned Lean toolchain and VCVio revision:

```sh
cd formal/sphincs
lake exe cache get
lake build
```

The cache command is needed on initial setup. The build includes [Audit.lean](Audit.lean), which rejects any axiom used by a local declaration other than `propext`, `Classical.choice` and `Quot.sound`. It covers the public security theorem and the retained work toward 127 bits. Run `lake env lean Audit.lean` to repeat the audit directly.

## Where to work

| Entry | Purpose |
| --- | --- |
| [SphincsSecurity.lean](SphincsSecurity.lean) | Public 126-bit theorem; the weaker 125-bit and 120-bit results follow from it. |
| [Security126Completion.lean](SphincsSecurity/Proof/Security126Completion.lean) | Completed reduction for the 126-bit theorem. |
| [Proof.lean](SphincsSecurity/Proof.lean) | Imports the completed proof and the remaining 127-bit work. |
| [RetainedResidualPrimitivePotential.lean](SphincsSecurity/Proof/RetainedResidualPrimitivePotential.lean) | Joint primitive-stop and certificate bound with the original query budget. |
| [RetainedResidualGameTransfer.lean](SphincsSecurity/Proof/RetainedResidualGameTransfer.lean) | Original success implies a native stop or a surviving strong forgery. |
| [RetainedResidualReplay.lean](SphincsSecurity/Proof/RetainedResidualReplay.lean) | Accepting verification recovers the complete canonical signature. |
| [RetainedResidualStrongCoverage.lean](SphincsSecurity/Proof/RetainedResidualStrongCoverage.lean) | A surviving strong forgery has a full certificate using eligible signing-log witnesses. |
| [RetainedResidualMonitoredGame.lean](SphincsSecurity/Proof/RetainedResidualMonitoredGame.lean) | Original SUF probability is at most the joint primitive and certificate bound plus an explicit monitor-stop exception. The later cache and proposal-history bounds discharge this exception. |
| [RetainedResidualMonitorStops.lean](SphincsSecurity/Proof/RetainedResidualMonitorStops.lean) | Native accounting and cached-digest invariants rule out bookkeeping stops. A successful active step with no cache exception stops exactly at a proposal-prefix exception. |
| [RetainedResidualExceptionGame.lean](SphincsSecurity/Proof/RetainedResidualExceptionGame.lean) | Whole-run monitor exceptions imply a recorded cache or proposal-prefix exception, with exact erasure of the passive history flags. |
| [RetainedResidualProposalTail.lean](SphincsSecurity/Proof/RetainedResidualProposalTail.lean) | The actual adaptive proposal-prefix history has probability at most $2^{-700}$. |
| [RetainedResidualCacheKernels.lean](SphincsSecurity/Proof/RetainedResidualCacheKernels.lean) | A second-moment weight controls cache exceptions through native query and signing kernels. The charge continues after the certificate monitor stops. |
| [RetainedResidualCacheTail.lean](SphincsSecurity/Proof/RetainedResidualCacheTail.lean) | The actual native cache-history probability is at most $q/2^{169}$ under the unchanged original hash bound. |
| [Security127LargeBudget.lean](SphincsSecurity/Proof/Security127LargeBudget.lean) | Original SUF probability is at most $q/2^{127}$ for every $q\ge3\cdot2^{114}$, with no additional cryptographic premises. |
| [AdaptiveChainEndpoint.lean](SphincsSecurity/Proof/AdaptiveChainEndpoint.lean) and [OtsPrefixOracle.lean](SphincsSecurity/Proof/OtsPrefixOracle.lean) | Prefix-oracle likelihood machinery for the small-budget OTS comparison. |
| [OtsPrefixObservedSource.lean](SphincsSecurity/Proof/OtsPrefixObservedSource.lean) and [OtsPrefixCappedSource.lean](SphincsSecurity/Proof/OtsPrefixCappedSource.lean) | Exact original-game representation by observed prefix runs. A bounded analytical cap preserves supported real runs, never stops in the ideal law below $2^{128}$, and transfers the original hash budget to ideal outputs. |
| [NearCertificateBound.lean](SphincsSecurity/Proof/NearCertificateBound.lean) | Near-certificate estimate needed by the forced-FTS comparison. |
| [ReferenceFamilyAllocation.lean](SphincsSecurity/Proof/ReferenceFamilyAllocation.lean) | A recorded game preserves original SUF probability and bounds the sum of all OTS-prefix query counts by the original budget, on supported runs and in expectation. |
| [OtsPrefixIdealAllocation.lean](SphincsSecurity/Proof/OtsPrefixIdealAllocation.lean) | Transports the shared prefix budget through conditional sampling and proves $(1-q/2^{128})\sum_c\mathbb E Q_c^{\rm ideal}\le q$ for the capped ideal comparisons. |
| [ReferenceQueryAllocation.lean](SphincsSecurity/Proof/ReferenceQueryAllocation.lean) | Preserves encoding, other non-message and all native message charges alongside the conditional OTS costs in one original hash budget. |
| [AdaptiveChainContact.lean](SphincsSecurity/Proof/AdaptiveChainContact.lean) | Proves the generic first-contact probability bound using actual expected prefix-query cost and a potential that accounts for previously prepared paths. |
| [OtsPrefixContactProbability.lean](SphincsSecurity/Proof/OtsPrefixContactProbability.lean) | Connects first-contact probabilities to the shared conditional budget, preserving observed rows through cap erasure and reserving other query classes. |
| [AdaptiveChainRestart.lean](SphincsSecurity/Proof/AdaptiveChainRestart.lean) | Charges a later first contact to old prefix preparation and future queries in the fixed-endpoint partial-table law. |

[The 127-bit guide](PAPER-127.md) identifies the remaining original-game connections and the mathematical contracts they must establish. Historical proof routes and superseded status reports are available in Git history.
