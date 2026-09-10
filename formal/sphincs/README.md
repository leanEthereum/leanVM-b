# SPHINCS security in Lean 4

The public theorem proves **126 bits of classical strong unforgeability in the random-oracle model**, with at most `2^24` signing requests per key pair. **127 bits remains unfinished.**

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
| [RetainedResidualMonitoredGame.lean](SphincsSecurity/Proof/RetainedResidualMonitoredGame.lean) | Original SUF probability is at most the joint primitive and certificate bound plus an explicit monitor-stop exception. Bounding this exception is still required. |
| [RetainedResidualMonitorStops.lean](SphincsSecurity/Proof/RetainedResidualMonitorStops.lean) | Native accounting and cached-digest invariants rule out bookkeeping stops. A successful active step with no cache exception stops exactly at a proposal-prefix exception. |
| [AdaptiveChainEndpoint.lean](SphincsSecurity/Proof/AdaptiveChainEndpoint.lean) and [OtsPrefixOracle.lean](SphincsSecurity/Proof/OtsPrefixOracle.lean) | Prefix-oracle likelihood machinery for the small-budget OTS comparison. |
| [NearCertificateBound.lean](SphincsSecurity/Proof/NearCertificateBound.lean) | Near-certificate estimate needed by the forced-FTS comparison. |

[The 127-bit guide](PAPER-127.md) identifies the remaining original-game connections and the mathematical contracts they must establish. Historical proof routes and superseded status reports are available in Git history.
