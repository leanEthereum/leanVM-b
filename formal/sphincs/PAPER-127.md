# Paper route to 127-bit strong unforgeability

Start with the [current mathematical plan](paper-127/minimal-closing-contract.md), reviewed against `71718e2e`. The target is the unchanged original SUF game with probability at most `q / 2^127`. The public Lean endpoint remains 126 bits. This paper review adds no Lean code.

Keep the split at `q = 3 * 2^114`. Above the split, a joint first-match and message-cost potential leaves a quadratic saving. Below it, completed OTS witnesses and FTS guesses must share the actual query allocations. The plan derives sufficient inequalities for both intervals, checks their exact arithmetic, and specifies the probability comparisons still needed. It also simplifies encoding exhaustion to a fixed valid analytical dummy word, preserving the full original failure distribution.

The paper audit now derives the allocated two-edge coefficient directly from the partial-table likelihood and stopped hit-count moments. It explains why a one-edge target match costs about two units while a complete two-edge path costs three units for two queries, and proves the adaptive correction without assigning every chain a separate full budget. The recommended next security milestone is the large-range bound for the original game; it has no dependency on this endpoint comparison or the forced-FTS branch.

The paper plan now gives a concrete endpoint simulator: rebuild roots and canonical messages from the supplied frontiers, embed the conditional encoding blocks before execution, and replace private prefix work by its result and original cost. An adaptive transcript mass calculation derives the projected likelihood from this causal access rule. A backwards trace through `Statement.lean` accounts for every signature field and explains the full, near, and true-guess alternatives with own-input exclusion. These are paper derivations and concrete formalization obligations, not additional Lean security theorems.

The complete reference-family sampling law is now formalized in [ReferenceFamilyGame.lean](SphincsSecurity/Proof/ReferenceFamilyGame.lean) and its imports, with the original SUF and hash-budget correspondence. The remaining gates include the exhaustive strong-forgery decomposition, the concrete instantiation of the projected adaptive likelihood, and coverage from local message/signing rules in the two required alternative interpreters. The [mathematical audit](paper-127/mathematical-audit.md) contains the longer derivations and formal progress through the current branch. The 127-bit theorem remains unproved.

[AdaptiveChainEndpoint.lean](SphincsSecurity/Proof/AdaptiveChainEndpoint.lean) now proves the endpoint comparison for an adaptive prefix-oracle interface. It derives the posterior completion law, erases the original uniform starting secret, and proves `(1 - q/N) * E_ideal[Z] <= E_real[Z]` for every nonnegative retained payoff under a syntactic prefix-query bound. [OtsEndpointLikelihood.lean](SphincsSecurity/Proof/OtsEndpointLikelihood.lean) connects the chain evaluator to the actual `chainWalk` and specializes the bound to 128-bit digests. The concrete frontier signer still has to be represented in this causal interface; the conditional restart, completed-witness bounds and remaining cryptographic transfers are open.

## Historical development notes

The notes below record earlier routes and status reports. Their thresholds, error allowances and claims of what was then pending are historical. Use the current mathematical plan above for the recommended constants and completion criteria.

The joint exception transfer is now checked in [CertificateJointExceptions.lean](SphincsSecurity/Proof/CertificateJointExceptions.lean). One augmented certificate execution retains a persistent flag for message-deficit and cached-index exceptions at query and signing boundaries. Erasing the flag preserves the complete certificate monitor and proposal word, and then the original verdict and cache. The original whole-experiment budget gives Pr[cache flag or proposal overflow] <= q/2^223 + q/2^170 + 2^-704. The existing full-coverage bound holds in this same game, and an original-forgery inequality separates its clean winning event from that allowance. This does not yet prove that every administrative first stop is harmless: the reachable cache-cardinality, digest-log, minimum-cost and signing-cap arguments still need assembly. The graph and cryptographic transfers remain open.

The latest [paper plan with unit message payment](paper-127/unit-payment-plan.md) derives a simpler large-budget route from the existing fixed-word moments. Ordinary full coverage is charged at 1/N, with excess allowance 11/65536. A direct potential then gives Pr[B]+E[A_B]/N<=2x-x^2, and the existing split q=3*2^114 still closes with margin 2^-16 per x. The note specifies the original-game graph, monitor, OTS projection, and forced-FTS obligations that remain. It changes no Lean source and does not claim the public 127-bit theorem.

The cached-index exception has an original-game bound of q/2^170 in [CachedIndexExcessGame.lean](SphincsSecurity/Proof/CachedIndexExcessGame.lean), using a second-moment reserve and preserving the original verdict when its flag is erased. This weaker bound already fits the closing margin, so the current formal route does not need the earlier fourth-moment bound q/2^237. The joint certificate-game transfer above now uses this reserve together with the deficit reserve, debiting each actual signing record's hash cost.

The proposal-prefix exception is now bounded in Lean by 2^-704 in [CertificateProposalPrefixException.lean](SphincsSecurity/Proof/CertificateProposalPrefixException.lean). The exponential potential follows the actual certificate game, and [CertificateProposalPrefixPersistence.lean](SphincsSecurity/Proof/CertificateProposalPrefixPersistence.lean) proves that a detected overflow remains visible through subsequent supported continuations. This discharges the proposal-overflow component; the other exception transfers and the cryptographic security reductions remain incomplete.

The focused [proof contract](paper-127/proof-contract.md) records the current two-range closure, the remaining experiment-transfer obligations, and elementary bounds for all three monitoring exceptions, including a rational proposal-prefix bound of 2^-704. It identifies the original-game large-budget theorem as the next substantial milestone. This review changes no Lean source and does not claim that the public 127-bit theorem is proved.

The new [fixed-word variance route](paper-127/variance-route.md) simplifies the numerical coverage obligation: a deterministic terminal length of 25313293 and single-bin and two-bin factorial moments give a positive-part bound below 2^-13. Moving the split to q=3*2^114 still closes both security ranges. This removes Poissonization, its short-pool exception, and the sharp degree-14 occupancy tail analysis described below. The note gives the revised arithmetic and identifies the unchanged cryptographic transfer obligations. No Lean code is added by this paper step.

This is a proof strategy for the unchanged concrete scheme. The current [paper review and proof plan](paper-127/next-proof-plan.md) starts from the concrete scheme audited at commit 106024f5 and the subsequent paper derivations. The public 126-bit theorem is established; no public 127-bit theorem is claimed. The algorithms, independent secrets, finite failures, signing cap, and whole-experiment hash budget are unchanged.

The expanded [stopped coverage derivation](paper-127/cached-target-forecast.md) gives its local shape transitions, banked certificates, actual message payments, common terminal word, and numerical moments on paper. The expanded [canonical-graph argument](paper-127/paid-probe-quadratic.md) supplies the exact graph law, hidden-label induction, exhaustive strong-forgery implication, and a joint primitive/message estimate. Together they give the paper large-budget bound for q>=2^113. These new probability endpoints are not yet Lean theorems.

The large-branch interface is simpler than the earlier [two-filtration audit](paper-127/two-filtration-audit.md): the primitive analysis stops only at its first match B or original termination. Coverage has additional guards, so its message count A_cov is pathwise at most the primitive count A_B on the same original run. No auxiliary coverage stops need to be exposed to the hidden-secret analysis. The [small-budget transfer](paper-127/small-budget-transfer.md) now supplies the allocated multi-chain OTS likelihood argument, both orders of encoding preparation, the deferred FTS support and likelihood comparison, and their original-game assembly. The [complete paper bound](paper-127/complete-paper-bound.md) combines the two ranges. This is an end-to-end written argument awaiting further audit and formalization, not a public 127-bit Lean theorem.

## Target and revised closing argument

Write N=2^128 and x=q/N. The target is P[forge]<=2x for the original strong-unforgeability experiment, with independently sampled secrets, at most 2^24 signing requests, actual finite retry failures, and the original hash budget covering key generation, signing, adversarial queries, and verification. At q>=N/2 the probability bound by one suffices.

The coarse reduction spends approximately two primitive chances per query before adding FTS coverage. Even substituting the newer near-uniform coverage estimate and discarding the compatible credits would leave 35x/16, before smaller errors. The paper route instead charges the queries that prepare and complete a usable forgery, and pays for message queries inside the primitive probability bound.

The new target is a two-regime argument, split at

    x_0 = 2^-15,       q_0 = 2^113.

For x<=x_0, the small-budget transfer bounds completed primitive forgery witnesses and ordinary coverage charges together by (7/4)x. For x>=x_0, the graph argument gives the joint primitive/message bound 2x-3x^2/4. Its message count dominates the count in the coverage bound. In either range, the coverage excess is at most 2^-16 x plus smaller errors.

The new arguments for the two previously open obligations are [cached-target-forecast.md](paper-127/cached-target-forecast.md) and [fts-useful-witness.md](paper-127/fts-useful-witness.md). The exact discrete couplings are developed in [discrete-target-coupling.md](paper-127/discrete-target-coupling.md) and [fts-guess-kernel.md](paper-127/fts-guess-kernel.md). Their assembly is in [complete-paper-bound.md](paper-127/complete-paper-bound.md). The arithmetic and finite examples have been checked exactly; those checks do not substitute for the written probability arguments or their formalization.

## Exact reference encodings and OTS witnesses

The construction and full estimates are in [reference-frontier-transfer.md](paper-127/reference-frontier-transfer.md), supported by [long-chain-inversion.md](paper-127/long-chain-inversion.md), [multiple-chain-inversion.md](paper-127/multiple-chain-inversion.md), and [two-chain-hits.md](paper-127/two-chain-hits.md).

Each OTS address p has a fixed canonical message M_p, determined by non-encoding oracle domains and independent sampled secrets. With v=L/N, where

    L = [z^191](1+z+...+z^7)^42
      = 27362001415540541846731060490886528,

the least valid counter J_p has a truncated geometric law. Its selected word D_p is uniform on the valid code, independently of J_p and all non-encoding data. On retry exhaustion, an independent artificial D_p may be added for analysis. The family (J_p,D_p) can therefore be sampled first.

Conditional on the canonical message, counter, and word, encoding cells before J_p are uniformly invalid; the reference cell equals D_p; every other cell remains independently uniform. This is exactly the original oracle's conditional law. It handles queries before signing and avoids declaring all future queried digests valid in advance.

For a valid word d, a distinct valid word e with only one backward step must be d-unit_i+unit_j for distinct i,j. There are at most 1722 such neighbors, and at most 41 with a specified lowered chain. If A_enc counts fresh nonreference encoding queries, the exact conditional construction gives

    P[any queried neighbor] <= 1722 E[A_enc]/N,
    E[number of distinct marked chains] <= 1722 E[A_enc]/N,
    P[nonreference encoding equal to D_p] <= E[A_enc]/N.

The fixed-message premise is essential. Allowing an adversary to choose the honest OTS message after seeing encodings admits a birthday counterexample to such a linear preparation bound. That freedom is absent here.

For the chain analysis, publish all canonical OTS frontiers Y at digits D. Conditional on D, each prefix is an independent random-function chain with an independent uniform starting secret. Everything above those frontiers, including the canonical messages, is generated from Y and independent remaining data. The conditional encoding table depends on that same information and independent randomness. It can be simulated without querying an unknown prefix cell.

This is the sampling construction for transferring the static chain experiment to backward witnesses in the actual execution. The complete allocated adaptive transfer is now written in small-budget-transfer.md, including an explicit q cap for idealized paths that may not have a compatible original secret key. Internal honest prefix evaluations only compute already supplied frontier and forward values, and do not disclose their intermediate values to the adversary. The simulator can omit those internal evaluations while routing adversarial and verification prefix queries to the real functions. Their number remains bounded by the original syntactic hash budget, including when the input was previously evaluated internally by an honest algorithm.

Let Q count distinct externally evaluated OTS prefix inputs, and set

    c(x) = ((3/2)+4x+2x^2)/(1-x) + 4x/(1-x)^2.

The chain likelihood argument handles arbitrary precomputation, merged paths, adaptive query allocation, and two separate one-step inversions without a factor for the number of chains. Separating whether a neighboring encoding is found before or after its inversion gives the following bound for nonreference equal-code events or backward witnesses for any distinct codeword:

    [c(x)+82x/(1-x)] E[Q]/N
        + [1+3444x/(1-x)] E[A_enc]/N.

For x<=x_0, both coefficients are below 131/80. The two expected costs refer to the same actual execution and disjoint query classes. This is stronger than charging each event class the whole q. It does not assume that inversions occur only after preparation.

The estimate is for paths actually reaching the canonical frontier. A forgery that instead merges above that frontier requires a noncanonical output match. Such upper structural hashes can be analyzed with their canonical inputs and outputs exposed and their other rows still uniform. A fresh noncanonical query has match probability 1/N. Merely revealing full upper function tables would not justify this probability statement.

## Joint primitive probability and message-query charges

The complete paper argument is in [paid-probe-quadratic.md](paper-127/paid-probe-quadratic.md). It includes an exposure of the concrete graph and an abstract accumulated-reward estimate.

After sampling the reference counters and words, sample all honest structural node labels independently and program each hash domain at its unique honest input. Acyclicity and distinct tweaks make this exactly the original random-function law. For analysis, disclose canonical OTS frontiers and all values above them, all FTS leaf hashes and internal nodes, and the reference data. Keep OTS prefix values below their frontiers and FTS secrets hidden. These hidden labels remain independent uniforms. Do not disclose the full function tables.

Before the first primitive match, an OTS prefix query has at most two equality probes against different labels: its hidden honest input and the honest parent value compared with a fresh answer. An undisclosed FTS secret query similarly has an input probe and an output probe. Public structural targets and nonreference equal-code encodings have at most one fresh-answer probe. Message queries have none. Signatures disclose only selected FTS secrets beyond the information already supplied; the choice uses visible history and independent randomness, rather than inspecting hidden secret values.

Honest secret-dependent computations read the programmed graph internally. They are not adversarial probes, and their calls still count toward q. Cache repeats and high output bits are handled by the same programmed tables. The original adversary ignores the extra advice, so its original output and cost laws are preserved.

Let B be the first primitive match and A_B the number of message-domain hash calls before B or original termination. The paper bound is

    P[B] + (3/(2N)) E[A_B] <= U(x) <= 2x-3x^2/4.

The reward term is part of this same primitive-stopped execution. Only previous probe rounds exclude candidates from hidden coordinates. After r probes, the conditional two-probe hazard is at most h_r=1-((N-r-1)/(N-r))^2. Paying all non-probe hash rounds at rate 3/(2N) gives an upper scalar process whose optimal schedule has a paid prefix. Its value is

    max_(0<=a<=q) [3a/(2N)+1-((N-q+a)/N)^2]
        <= U(x)=2x-x^2+max(x-1/4,0)^2.

The continuation values are below one, justifying the upper-hazard replacement. Elementary maximization yields the stated quadratic bound. Coverage may stop earlier at its own guards: its A_cov<=A_B pathwise, so ordinary coverage is paid by the same estimate without changing the primitive history.

With no primitive match, an accepted OTS component is canonical, every accepted FTS secret has already been disclosed, and authentication nodes are canonical. A different signature on the same message and randomizer would force a primitive match. Therefore a strong forgery with no B gives a digest target covered by successful signing views at other inputs. This retains target-input exclusion and the actual Option failure cases.

## Proposed solution: charged cached-target coverage

The coverage argument applies to an execution stopped at prefix exceptions and, optionally, at B. With A_msg counting message queries in that execution, the proposed bound is

    E[completed full-target certificates] <= (3/(2N)) E[A_msg] + 2^-16 x.

A certificate records a target whose coordinates are covered by successful signing views at inputs other than its own input. Targets may be queried before the signatures that eventually cover them. Retain the existing target-shape forecasts for such pending targets. At first completion, bank one certificate and discard its forecast, which is at least one. At an exceptional stop, discard pending forecasts and retain the bank. This bounds an expected count without multiplying exception probabilities by the number of targets.

Use the actual remaining budget b=q-t in the forecast. Its fresh-target price W_j/N is bounded using positive polynomial moments and a discrete rejection sampler that embeds selected signing indices in uniform index proposals. The construction produces one terminal variable R, common to every external-query or signing boundary, such that

    W_j <= E[R | F_j],       E[(R-3/2)_+] < 2^-16.

Here F_j is the enlarged boundary filtration. No independence between an adaptively chosen charging time and final occupancy is assumed. For predictable creation multipliers a_j, the concrete signing cost and a finite stopping-time identity give

    sum_j a_j <= q,       E[sum_j a_j] <= E[A_msg].

Conditional Jensen and the tower identity then bound the excess adaptive charge by q E[(R-3/2)_+]. This is the missing strengthening over an ordinary first-moment occupancy envelope. The same construction at degree 13, summed over the 14 choices of a missing coordinate, gives

    E[completed near-target certificates] <= 557x.

For the terminal Poisson comparison, take I=2^26 bins and a terminal proposal-word length J~Poisson((19/50)*I). Its occupancy counts Z_i are independent Poisson(19/50) variables. Each signing index is accepted from uniform proposals by rejection sampling, with mean beta=1537/1024 proposals per signing. The exact bridge can run the actual signing invocation first and add its auxiliary rejected proposals afterward. This preserves the original signing record and unqueried message cells. The required terminal arithmetic is

    E[(sum_i Z_i^14/2^48-3/2)_+] < 2^-16,
    (14/2^38) E[sum_i Z_i^13] < 557.

Stop initially if J<25313293 and at a signing boundary if more than beta*s+S/128 proposals have been consumed. On a clean prefix the unused proposal counts dominate every required degree-14 forecast in falling-factorial moments. The two proposal exceptions together cost less than 2^-700. With the cap on each cached index and the message-deficit stop controlling cached digest reuse, the total is at most

    epsilon(q)=q/2^222+q/2^237+2^-700.

The paper makes two stopping distinctions explicit. Exceptions inside signing are acted upon only at the end of the invocation, retaining all its actual message calls in A_msg. Also, the original game rejects a final signing log longer than S; an analysis may terminate with a losing result before request S+1, without conditioning on a future valid log or changing the scheme's signing interface.

## Proposed solution: useful FTS guesses at small budgets

Separate true secret guesses from alternative preimages. A query H_l(z)=Y_l with z different from the true secret is a cheap output-match event, with rate 1/N per fresh FTS query. This includes alternative preimages found before a later disclosure of the true secret.

Before a true secret guess, that secret is uniform on its unexcluded values. Its conditional guessing probability is at most 1/(N-q). Two distinct true guesses therefore cost at most x^2/(2(1-x)^2). A forgery needing just one undisclosed secret also needs a near-target certificate, before or after the guess.

For each possible first-guess hash slot, use a conditional experiment that forces earlier eligible guesses to miss and that slot to hit. The explicit deferred-secret kernel gives likelihood weight p_j*product_(t<j)(1-p_t)<=1/(N-q). It changes only local branch probabilities, preserving unqueried message cells, the original path budget, and already disclosed secrets. The uniform near-target estimate then gives a total bound of 557x^2/(1-x), covering either chronological order and targets completed by later signatures.

The combined extra FTS contribution is thus

    557x^2/(1-x)+x^2/(2(1-x)^2) < (9/80)x       for x<=x_0.

The OTS coefficients, cheap structural output matches, and the ordinary message-query charge all fit below 131/80 with their disjoint query allocations retained. Together with this extra FTS term, the coefficient is below 131/80+9/80=7/4.

## Closure and next milestone

The proposed lemmas yield, for x<=x_0,

    P[forge] <= (7/4)x + 2^-16 x + epsilon < 2x.

For x_0<=x<=1/2, the paid primitive bound and charged coverage give

    P[forge] <= 2x-3x^2/4+2^-16 x+epsilon.

At x=x_0, (3/4)x-2^-16=2^-17, and this difference increases with x. Thus the large-budget range leaves at least 2^-17 x for the remaining errors. For q>=1, epsilon(q)/x<=2^-94+2^-109+2^-572<2^-17. At q>=N/2 use the probability bound by one. Both nontrivial ranges therefore close numerically at P[forge]<=2x=q/2^127.

The original-game small-budget derivation throughout q<=2^113 is now written in small-budget-transfer.md. Its OTS likelihood proof retains disjoint original query allocations and treats endpoint-dependent auxiliary behavior explicitly. Its forced FTS laws inherit the original budget through positive conditional branches and each receives its own coverage bridge. The next audit should target these experiment transfers before translating the complete paper argument into Lean.

After the complete paper argument survives that audit, the formalization order should produce the following endpoints:

1. Assemble the full and near certificate inequalities from the original monitor, common terminal word, and actual costs. Keep the theorem general enough for the deferred-secret kernels.
2. Formalize the canonical graph, posterior, and strong-forgery decomposition, then combine the joint primitive bound with A_cov<=A_B to establish the original-game large-budget theorem.
3. Formalize the allocated OTS witness and forced FTS guess transfers and derive the small-budget theorem.
4. Assemble the public 127-bit theorem for the unchanged statement and inspect its assumptions and axioms. This is completion; intermediate numerical endpoints are not completion.

The two coupling interfaces now have explicit paper kernels: a geometric rejection bridge with independent auxiliary randomness, and a deferred-secret kernel whose local hit and miss probabilities give the forced-guess likelihood exactly. The common terminal domination follows from finite-prefix independence and falling-factorial moments. Formalization must retain the recorded-history boundary: message queries, signing responses, and actual costs are recorded, while secret-dependent internal non-message inputs remain hidden. The plan does not depend on a further improvement of the final constants.

The Python files under paper-127 contain exact rational checks of partial-table likelihoods, conditional reference-table laws, finite probe decision problems, moment bounds, and closing constants. In particular, transfer-kernel-checks.py checks stopped transcript densities with endpoint-dependent auxiliary data and the adaptive forced-first-guess identity; reference-and-paid-checks.py checks the current split and scalar bound, the exact graph law, and surviving posteriors on finite examples; coverage-closing-checks.py checks proposal and Poisson constants and the older sufficient split; adaptive-kernel-checks.py checks the local planted-table kernel and rejection-bridge factorization. They can each be run with Python 3 and use only its standard library. These checks support the written arguments; they neither implement the security experiment nor certify the full adaptive constructions or the final Lean theorem.

## Formalization progress

[BinomialMoments.lean](SphincsSecurity/Proof/BinomialMoments.lean) defines finite Bernoulli averaging, proves its factorial moments and the general Stirling expansion into ordinary powers, and proves the shifted-power upper bound E[(c+B)^d]<=(c+ba+d)^d. It also proves the falling-factorial moment comparison used by the discrete proposal construction: a sufficient number of unused proposals dominates every required shifted power. These results are generic in the degree and trial counts.

[RawQueryMomentBound.lean](SphincsSecurity/Proof/RawQueryMomentBound.lean) identifies the existing query operator's iterates exactly with that binomial average. The signing operator preserves inequalities restricted to a fixed total degree. Together with the existing envelope's sum identity, `reuseRawEnvelope_query_shift_le` bounds the actual raw envelope by signing-only iterates whose cache argument is increased by b/2^36+d. This implements the paper step that bounds hypothetical future cache growth before giving the signing operator a stochastic interpretation.

[RawSigningMomentBound.lean](SphincsSecurity/Proof/RawSigningMomentBound.lean) proves the bounded stochastic interpretation of the signing operator. Under an explicit upper bound on its reachable increment rates, its signing-coordinate moments are bounded by finite Bernoulli averaging. This is proved for arbitrary monotone functions and then applied to powers; the raw polynomial operator is not assumed to be a probability kernel outside the bound.

[RawProposalMomentBound.lean](SphincsSecurity/Proof/RawProposalMomentBound.lean) instantiates the comparison with the concrete reuse coefficient, the cache cap C_i<=t/2^36+2^80, the remaining query budget and the signing cap. Lean checks the rate bound (1537/1024)/2^26 and the falling-factorial comparison with unused uniform proposals.

[UniformProposalMoments.lean](SphincsSecurity/Proof/UniformProposalMoments.lean) defines the actual uniform proposal-word sampler and identifies its count moments with the Bernoulli averages. Its endpoint `reuseRawEnvelope_le_expected_terminalProposalWord` bounds the existing raw envelope by the expected sum of powers of the occupancies of the consumed word followed by an independent uniform suffix. The endpoint derives the needed proposal-room condition from J>=25313293 and the prefix length bound K_s<=(1537/1024)s+131072, for every required degree up to 14.

[ProposalWordDistribution.lean](SphincsSecurity/Proof/ProposalWordDistribution.lean) constructs normalized geometric failure counts and finite rejected words as probability mass functions. Its bridge samples an arbitrary original record and an independent auxiliary rejected word. Projecting away that word returns exactly the original record distribution, with an explicit joint mass for every word and record.

[ProposalBridgeKernel.lean](SphincsSecurity/Proof/ProposalBridgeKernel.lean) constructs the residual proposal distribution from the bound a*p_i<=u_i, where a is the acceptance probability, p is the record's index distribution and u is the desired proposal distribution. Lean checks the geometric product density, the proposal marginal u, and the full one-step probability-kernel identity: either accept a record or emit a rejected index and continue the same bridge. This proves the local equivalence of the record-first and proposal-first constructions.

[AdaptiveProposalWords.lean](SphincsSecurity/Proof/AdaptiveProposalWords.lean) proves that a transition kernel with the same proposal marginal at every state emits independent proposals for every fixed finite prefix, allowing the record law and subsequent state to change adaptively. It instantiates acceptance a=1024/1537 and the existing index-rate cap, and proves equality with the evaluation distribution of `sampleUniformProposalWord`. The state in these generic results must be instantiated with the recorded history used by the paper argument.

[DigestSelectionIndex.lean](SphincsSecurity/Proof/DigestSelectionIndex.lean) proves the exact index distribution of the actual finite digest loop after adding a uniform dummy only on digest exhaustion. Its fresh and exhaustion contribution is `(F+E)/I`; its cached contribution is the message-specific indexed count times the exact reuse weight. The message-specific count is bounded by the all-message index multiplicity. On the explicit cache, deficit and spent-budget bounds, the completed index probability is at most `(1537/1024)/2^26`.

[SigningProposalRecord.lean](SphincsSecurity/Proof/SigningProposalRecord.lean) transfers that cap to a traced invocation of the actual signer and instantiates the geometric proposal bridge. The completed record keeps the selected index even when a later encoding fails. Lean checks the uniform next-proposal law, the full proposal-step recursion, and exact preservation of the original signing response, trace and final-cache distribution after erasing the auxiliary proposals and view. Its boundary trace records one marker per hash call, with input/output data only for message-domain calls; projecting away the private cache preserves the corresponding original signature/trace law. The accepted proposal index agrees with every retained selected view on the bridge's support.

[ProposalLengthProjection.lean](SphincsSecurity/Proof/ProposalLengthProjection.lean) proves that erasing rejected values while retaining their count plus one gives an independent geometric block length jointly with the original record. The equality holds for arbitrary record and rejection distributions and survives mixtures over private states. Its concrete signing endpoints retain the original Option response, trace and final cache together with that length, or project to the response and boundary trace alone.

[ProposalQueryProjection.lean](SphincsSecurity/Proof/ProposalQueryProjection.lean) lifts this projection through arbitrary adaptive oracle computations. Analysis state may be updated from the completed record and block length, including counters and stopping flags; those updates cannot read the rejected values. Erasing rejected values preserves the resulting analysis-state distribution. A second projection erases the analysis state when its updates preserve the specified original state transition.

[OriginalProposalExecution.lean](SphincsSecurity/Proof/OriginalProposalExecution.lean) instantiates the construction with the actual shared random oracle and signer. World queries consume no proposals, and signing proposals are enabled only when the caller's analysis flag and the concrete cache cap permit them. Every invocation retains its actual response, selected view, completed index, boundary trace and final cache. The theorem `simulateQ_originalProposalImpl_original` proves that erasing proposal values and analysis state recovers the lifted distribution of the original `unloggedMappedAdversaryImpl` execution, for every adaptive oracle computation and initial cache. This establishes an execution projection, not the stopped certificate inequality: the concrete monitoring and certificate updates, uniform unused terminal word, and final original-game probability bounds still need assembly.

[BankedCacheWeight.lean](SphincsSecurity/Proof/BankedCacheWeight.lean) proves the certificate ledger's local expectation inequality: completed inputs contribute one permanently, uncompleted inputs retain their forecasts, and stopping discards only the latter. Banking a completion is paid by its forecast being at least one. The proof separates old cached targets from fresh arrivals and permits arbitrary stopping decisions after the transition, without multiplying an exceptional probability by a target count.

[BankedTargetEnvelope.lean](SphincsSecurity/Proof/BankedTargetEnvelope.lean) instantiates that ledger with the existing target-shape forecasts for any required coordinate subset. Its coverage predicate uses the eligible signing views that exclude the target's own input; the full-coordinate case is equivalent to the existing coverage predicate. Lean checks that every completion pays one, including at exceptional post-states, and proves the local world-query and signing bounds. Signing retains its exact fresh-selection probability F in the arrival charge. The price is written as L*F times the raw fresh-message price, with L=1024.

[BankedProposalStep.lean](SphincsSecurity/Proof/BankedProposalStep.lean) transfers these inequalities to the actual completed execution records. The post-step forecast deducts the record's actual traced hash cost from the remaining budget. Signing consumes one remaining invocation, including failures. The bounds also hold for the geometric length bridge and the rejected-proposal bridge, with stopping allowed to depend on the whole augmented outcome. These are local inequalities; they do not yet define and analyze the complete adaptive certificate counter.

[CertificateMonitor.lean](SphincsSecurity/Proof/CertificateMonitor.lean) defines the adaptive monitoring state over the original execution records. It retains the signing log, actual hash and message-call counters, proposal lengths, completed certificates, predictable creation mass, and forecast-weighted creation costs. Active invocations retain their complete actual costs even when a post-step stopping rule fires. An inactive monitor freezes its counters and certificates while the underlying interpreter continues, preserving the original response and cache distribution. Erasing rejected proposal values retains exactly the same monitoring law; erasing the monitoring state recovers the original adaptive execution.

[CertificateMonitorStep.lean](SphincsSecurity/Proof/CertificateMonitorStep.lean) composes the concrete local banked-potential inequality through arbitrary adaptive oracle computations. Its endpoint `expected_certificateProposal_count_le_creationCost` bounds the expected completed-certificate count by expected accumulated forecast charges in the augmented original execution, initialized with no message cache entries. The local transition inequality is proved for the concrete interpreter rather than assumed as an endpoint hypothesis. This establishes accumulation, but does not yet replace the forecast charges by the final numerical coverage bound.

[BoundaryMessageCost.lean](SphincsSecurity/Proof/BoundaryMessageCost.lean) identifies expected message calls in the actual boundary trace with the existing expected query-charge semantics. [DigestMessageCost.lean](SphincsSecurity/Proof/DigestMessageCost.lean) proves that the finite digest-loop attempt expectation equals its message query charge. Consequently L times the actual fresh-selection probability is at most the expected message-call count of the completed original signing record. Cached repeats, digest exhaustion, and later encoding failures are retained. The proof only needs this inequality; it does not replace actual signing costs by a fixed attempt allowance.

[CertificateMessagePayment.lean](SphincsSecurity/Proof/CertificateMessagePayment.lean) carries this payment through the concrete adaptive monitor. Its endpoint `expected_certificateProposal_creationMass_le_messageCalls` proves that expected accumulated predictable creation mass is bounded by expected accumulated actual message calls in the same augmented execution. The intermediate geometric-length projection preserves both quantities. The endpoint does not assume a per-step payment inequality; that inequality is derived from the original world and signing kernels.

[BoundaryHashCost.lean](SphincsSecurity/Proof/BoundaryHashCost.lean) proves exact continuation-budget debit by the hash count of every supported actual trace. [SigningBoundaryHashCost.lean](SphincsSecurity/Proof/SigningBoundaryHashCost.lean) proves that every supported signing invocation costs at least 28504 hashes, including digest exhaustion and later encoding failures. [OriginalProposalBudget.lean](SphincsSecurity/Proof/OriginalProposalBudget.lean) transfers these facts to the original completed records and pays each predictable creation multiplier by that record's actual hashes. [CertificatePathBudget.lean](SphincsSecurity/Proof/CertificatePathBudget.lean) carries the payment through arbitrary adaptive computations and both proposal projections, deducting each realized record cost from the continuation's syntactic budget.

[CertificateGame.lean](SphincsSecurity/Proof/CertificateGame.lean) attaches the monitor to actual key generation, the adversary, and final verification. Its erased verdict and final cache are exactly those of the original game, and its winning probability equals the original forgeAdvantage for every monitor stopping rule. The verifier verdict uses the complete original signing log even after monitoring stops. Under the original HasHashQueryBound assumption, `certificateGame_cost_le` proves both the monitored spent counter and accumulated creation mass are at most q on every supported outcome. The same whole-game law satisfies expected creation mass at most expected monitored message calls, and expected banked certificate count at most expected accumulated forecast cost. The latter theorem derives the empty initial message cache from actual key-generation support. None of these endpoints assumes a per-record payment or an independently supplied rest-of-game budget.

[TerminalProposalWord.lean](SphincsSecurity/Proof/TerminalProposalWord.lean) defines completion by truncating consumed proposals or padding with an independent suffix. Its bridge theorem gives the exact completion-kernel identity, including blocks that overrun the chosen total. [OriginalTerminalProposal.lean](SphincsSecurity/Proof/OriginalTerminalProposal.lean) lifts that identity through the actual proposal interpreter and arbitrary adaptive continuations, and proves conservation of the corresponding terminal-payoff expectation.

[CertificateTerminalGame.lean](SphincsSecurity/Proof/CertificateTerminalGame.lean) attaches the completed word to the original certificate game. Its game projection is exact, its word marginal is uniform, and it inherits the original whole-path cost bounds. [PoissonCertificateGame.lean](SphincsSecurity/Proof/PoissonCertificateGame.lean) mixes over the paper's Poisson pool length, preserves the original verdict and cache law, and bounds creation mass times any terminal payoff using the original q and the independent-word mixture. No independence between creation mass and that payoff is assumed.

[TerminalProposalEnvelope.lean](SphincsSecurity/Proof/TerminalProposalEnvelope.lean) identifies the existing uniform-suffix expectation with this same completion kernel. Under explicit clean-boundary cache, signing-count and proposal-room premises, it bounds the actual monitor's creation charge by its creation multiplier times the terminal-price potential. That potential is conserved by the actual adaptive proposal kernel. This is a local domination theorem, not the complete numerical certificate bound.

[CertificateProposalInvariant.lean](SphincsSecurity/Proof/CertificateProposalInvariant.lean) discharges the count and room premises on actual active monitor states. A successful response's observed index equals its accepted proposal index, old signing views remain stable under cache extension, and every successful slot contributes at most one new count. The invariant propagates through arbitrary adaptive computations with the prefix guard, including failures and stopped monitors.

[TerminalCertificateCharge.lean](SphincsSecurity/Proof/TerminalCertificateCharge.lean) uses that invariant and the terminal potential's conservation to bound all accumulated creation costs by creation mass times the shared terminal payoff. Its original-game endpoint `expected_poissonCertificateGame_count_le_message_excess` proves E[banked certificates] <= c E[actual monitored message calls] + q E[(terminal price-c)_+] for any nonnegative baseline c. The final expectation is over the independent uniform-word mixture with the specified Poisson length, not over an adversarial occupancy law. The theorem assumes only the original whole-experiment hash bound and q<=2^127, besides the explicit coordinate subset and stopping rule; it does not assume a coverage bound or support invariant.

[UniformProposalMixedMoments.lean](SphincsSecurity/Proof/UniformProposalMixedMoments.lean) proves the exact mixed falling-factorial moments for distinct indices in a fixed uniform word, and the resulting nonpositive covariance bound for arbitrary powers. [UniformProposalVariance.lean](SphincsSecurity/Proof/UniformProposalVariance.lean) bounds the second moment of a sum by its squared mean plus the diagonal second moments. [StirlingMomentBounds.lean](SphincsSecurity/Proof/StirlingMomentBounds.lean) checks the concrete degree-13, degree-14 and degree-28 rational bounds. [PositivePartMomentBound.lean](SphincsSecurity/Proof/PositivePartMomentBound.lean) proves the excess estimate using nonnegative expectations and finite cancellation. [FixedProposalMoments.lean](SphincsSecurity/Proof/FixedProposalMoments.lean) instantiates these results at terminal length 25313293: the normalized full-price excess above 3/2 is at most 2^-13, and the normalized near-price mean is at most 557. No Poisson distribution assumption or favorable occupancy event is needed.

[FixedCertificateCoverage.lean](SphincsSecurity/Proof/FixedCertificateCoverage.lean) connects those numerical estimates to the actual monitor. Under only the original HasHashQueryBound and q<=2^127, `expected_fixedCertificateGame_full_count_le` proves E[C_full]<=3 E[A_msg]/(2N)+q/2^141. The corresponding degree-13 bound, summed over the 14 omitted-coordinate monitors, is at most 557q/N. Its fixed-word game projects exactly to the original verdict and cache law. Additional monitor stops remain permitted; these theorems bound banked certificates on stopped runs, not the probability of stopping or forging.

The next obligations are the exceptional probabilities for the actual stopped execution and the coverage extension to deferred FTS kernels. The current numerical endpoints instantiate the original signer. Applying them in the forced-guess argument still requires the message-kernel generalization and its concrete deferred-secret instantiation, with the appropriate common projected stopping history. The graph and OTS likelihood transfers also remain to be formalized. Their audit must retain the explicit OTS projection: the preimage-count density applies only after forgetting the hidden starting secret and private canonical prefix data. No public 127-bit security theorem follows from these intermediate results.
