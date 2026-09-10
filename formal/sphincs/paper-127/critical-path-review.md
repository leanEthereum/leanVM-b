# Current 127-bit proof status

The public theorem remains 126 bits. Neither nontrivial 127-bit interval is established. This is the status entry point; the other notes supply mathematical derivations rather than a chronological progress log.

Put $N=2^{128}$, $x=q/N$, $\delta=11/65536$ and $\epsilon(q)=q/2^{222}+q/2^{170}+2^{-700}$. The [closing contract](minimal-closing-contract.md) targets $2x-x^2+\delta x+\epsilon(q)$ for $3\cdot2^{114}\le q<2^{127}$ and $(15/8+\delta)x+\epsilon(q)$ below that split. Both suffice for the 127-bit slope. Budgets at least $2^{127}$ use probability at most one.

## Established interfaces

| Module | Result |
| --- | --- |
| [RetainedResidualOriginalBudget](../SphincsSecurity/Proof/RetainedResidualOriginalBudget.lean) | The unchanged original hash bound supplies the retained source budget, including key generation, failures, repeated calls and final verification. |
| [RetainedResidualTerminalCoverage](../SphincsSecurity/Proof/RetainedResidualTerminalCoverage.lean) | $\mathbb E C_{\rm full}\le\mathbb E D_{\rm native}/N+\delta x$, with proposal erasure and the actual native message count. |
| [RetainedResidualPrimitivePotential](../SphincsSecurity/Proof/RetainedResidualPrimitivePotential.lean) | $\Pr[B]+\mathbb E D_{\rm native}/N\le2x-x^2$, hence $\Pr[B]+\mathbb E C_{\rm full}\le2x-x^2+\delta x$. Stopped runs retain their earlier message costs. |
| [RetainedResidualGameTransfer](../SphincsSecurity/Proof/RetainedResidualGameTransfer.lean) | Original SUF success is bounded by a primitive stop or a live strong forgery, retaining the full signing log. |
| [RetainedResidualVerifySupport](../SphincsSecurity/Proof/RetainedResidualVerifySupport.lean) | Supported accepting verification has honest openings at all layers and disclosure of every required FTS secret. |
| [RetainedResidualReplay](../SphincsSecurity/Proof/RetainedResidualReplay.lean) | The recovered signature equals the original `signAfterDigest` result, including counters and every signature field. |
| [RetainedResidualSigningHistory](../SphincsSecurity/Proof/RetainedResidualSigningHistory.lean) | Every successful log entry has its original signing computation and cached digest; every disclosed FTS leaf has a log witness. The invariant holds initially and is preserved through the source execution. |
| [RetainedResidualStrongCoverage](../SphincsSecurity/Proof/RetainedResidualStrongCoverage.lean) | A supported, accepting strong forgery yields `TargetCertificateAt` for all FTS trees in the retained cache and log. Canonical replay excludes the forgery's own input from every signing witness. |
| [RetainedResidualBankCompleteness](../SphincsSecurity/Proof/RetainedResidualBankCompleteness.lean) | An active native monitor has the same signing log as the source memory and counts every full certificate in that memory's cache and log. |
| [RetainedResidualCertificateTransfer](../SphincsSecurity/Proof/RetainedResidualCertificateTransfer.lean) | On the actual initial monitored law, a supported strong forgery with an active monitor has bank count at least one. Its probability is bounded by the expected bank count plus successful strong forgeries with the monitor stopped. |
| [RetainedResidualMonitoredGame](../SphincsSecurity/Proof/RetainedResidualMonitoredGame.lean) | Averaging the initial sampling and erasing the monitor gives $\Pr[\mathrm{SUF}]\le2x-x^2+\delta x+\Pr[E_{\rm native}]$ from the unchanged original query bound, for $q\le2^{127}$. The exception probability remains explicit and unbounded. |
| [RetainedResidualAccounting](../SphincsSecurity/Proof/RetainedResidualAccounting.lean) | An active monitor's spent count equals the native hash-call count. Supported steps account for minimum macro costs and signing-log growth; valid bounded continuations supply the earlier signing-cap and macro-budget conditions. |
| [RetainedResidualCacheAccounting](../SphincsSecurity/Proof/RetainedResidualCacheAccounting.lean) | The native cache size never exceeds its actual hash-call count, including on stopped runs. Together with exact spending, this supplies the proposal cache bound outside the cache exceptions. |
| [RetainedResidualMonitorReadiness](../SphincsSecurity/Proof/RetainedResidualMonitorReadiness.lean) | Successful signing digests remain cached through every native step, including signing failures. Before a supported query on a valid bounded continuation, an unstopped monitor with no cache exception is active. |
| [RetainedResidualMonitorStops](../SphincsSecurity/Proof/RetainedResidualMonitorStops.lean) | A supported live step has an exact operational record. An active step with no resulting cache exception satisfies the post-step readiness conditions; with the default proposal rule, its stopped flag is equivalent to the proposal-prefix exception. |
| [AdaptiveChainEndpoint](../SphincsSecurity/Proof/AdaptiveChainEndpoint.lean) | Adaptive prefix likelihood and allocated cost comparison for the generic causal interface. |
| [ProposalQueryProjection](../SphincsSecurity/Proof/ProposalQueryProjection.lean) | Adaptive erasure of rejected proposal values to signing records and independent block lengths. |

## Remaining work

1. Bound the native monitor exception. Set `stopAfter := fun _ _ _ _ => false` in `forgeAdvantage_le_monitored_bound_add_exception` and prove $\Pr[E_{\rm native}]\le\epsilon(q)$. The native bookkeeping invariants and successful-step stop classification are proved. Lift them to a whole-run event that records whether a cache or proposal-prefix exception has occurred, then bound those events on their actual laws. Cache exceptions need a history flag because their predicates need not persist as the cache grows. Preserve the strong winning condition and avoid charging the primitive stop a second time.
2. Instantiate the causal OTS prefix simulator with raw low tables and an independent high-output function observed only at external inputs. Prove completed-witness charges with one shared original-query allocation, including preparation in either chronological order and caps inside omitted private work.
3. Establish fresh-message and signing kernels in each forced-FTS law. Use the record-and-length projection, attach that law's own proposal words, and bound one true guess with a near certificate plus two distinct guesses.
4. Combine the small-range bound, large-range bound and probability at most one. Audit the resulting public theorem without additional cryptographic premises.

The [small-range gate audit](small-range-gate-audit.md) specifies why secret-dependent canonical high halves cannot enter the OTS history, and why the forced-FTS comparison needs no joint posterior for rejected proposal values. The full-cache exceptional flag is also excluded from that projected stopping rule: its probability is paid on the original law using the spent-call invariant.

## Shortcuts that do not close the current estimates

Two tempting numerical shortcuts do not remove the small-budget obligation with the current estimates. First, crediting the established honest-work debits is insufficient. At $q=2^{112}$, $x=2^{-16}$ and $\delta=11/2^{16}$, the unshifted excess $\delta x-x^2$ is $10/2^{32}$ before exceptions. Even replacing $x$ in the primitive term by $(q-K)/2^{128}$ with $K=1212415+2^{24}\cdot28504$ leaves excess greater than $9/2^{32}$. This calculation grants the minimum debit for every allowed signing request; it is a generous arithmetic check, not a valid uniform debit for executions making fewer requests. Reclaiming key generation alone also fails this check. A sharper bound tied to the actual adaptive allocation would need a new argument.

Second, the existing terminal-price moments cannot justify replacing a correlated weighted price by its mean. For an abstract nonnegative price $P$ equal to $2$ with probability $10^{-4}$ and zero otherwise, $\mathbb E P\le1/5$ and $\operatorname{Var}(P)\le13/25000$. Taking a bounded charge $M=q\mathbf1_{P=2}$ nevertheless gives $\mathbb E[MP]=2\mathbb E[M]$. This is a counterexample to an inference from the moment bounds alone, not an attack on the scheme or a claim about its exact price distribution. The terminal-price excess term accounts for precisely this possible dependence; removing it requires more than an average-price estimate.

Sharpening the exact terminal-price tail alone cannot eliminate the small-budget argument either. In the existing uniform proposal word, put $m=2^{26}$, $L=25313293$, and $P=2^{-48}\sum_i R_i^{14}$, where $R_i$ is the number of occurrences of index $i$. Let $A_i$ mean $R_i=12$. The binomial and multinomial formulas, followed by Bernoulli's inequality and the first two inclusion-exclusion terms, give

\[
\Pr\Bigl[\bigcup_i A_i\Bigr]\ge m\frac{(L-11)^{12}}{12!m^{12}}\left(1-\frac{L-12}{m}\right)-\binom m2\frac{L^{24}}{(12!)^2m^{24}}>2^{-21}.
\]

On this event $P\ge12^{14}/2^{48}>4$, so $\mathbb E[(P-2)_+]>2^{-20}$. The two strict numerical inequalities were checked with exact rational arithmetic; this is a paper calculation, not a new Lean theorem. Even allowing a baseline payment of $2$ instead of $1$ therefore leaves a positive excess in this terminal-price estimate. At $q=2^{100}$, its coefficient exceeds $x=2^{-28}$, so a bound of the form $2x-x^2+\eta x$ with this excess coefficient $\eta$ does not close. This concerns the analytical proposal envelope, not an attack or a lower bound on forgery probability. A sharper joint allocation argument could still improve the result; computing higher moments of this same envelope alone cannot remove the separate small-budget obligation.
