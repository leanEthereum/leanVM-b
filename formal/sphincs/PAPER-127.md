# Paper route to 127-bit strong unforgeability

This is a proof strategy for the unchanged concrete scheme at source commit a743f717. The linked notes give a candidate paper argument through the final 127-bit inequality, including proposed solutions to cached-target charging and useful FTS guessing. This is not a completed Lean proof. The adaptive probability constructions and their exact connection to the original experiment are the main review and formalization risks. The raw envelope now has a checked comparison with the expected occupancy powers of a uniform proposal suffix, under the paper's explicit cache and prefix bounds. The algorithms and public security statements are unchanged.

A subsequent [paper review and proof plan](paper-127/next-proof-plan.md), based on source commit 89d33041, sharpens the abstract paid primitive bound to 2x-3x^2/4 by counting probe rounds separately from message queries. It permits a split at q=2^113 and prioritizes the complete stopped certificate estimate and its original-game filtration. The older bounds below remain sufficient; the new note distinguishes the algebraic improvement from the concrete probability interfaces still to establish.

The latest [two-filtration audit](paper-127/two-filtration-audit.md), based on source commit 86c5e4e8, simplifies that interface: coverage and primitive probabilities must refer to the same stopped execution and message costs, but may use different information histories. Erasing rejected proposal values preserves independent geometric lengths, which are sufficient for the shared stopping rules. The forced-guess likelihood can likewise be proved before adding rejected values, with a separate coverage coupling for each forced experiment. The note gives the transition obligations and revised work order; it does not claim a completed paper or Lean proof.

## Target and revised closing argument

Write N=2^128 and x=q/N. The target is P[forge]<=2x for the original strong-unforgeability experiment, with independently sampled secrets, at most 2^24 signing requests, actual finite retry failures, and the original hash budget covering key generation, signing, adversarial queries, and verification. At q>=N/2 the probability bound by one suffices.

The coarse reduction spends approximately two primitive chances per query before adding FTS coverage. Even substituting the newer near-uniform coverage estimate and discarding the compatible credits would leave 35x/16, before smaller errors. The paper route instead charges the queries that prepare and complete a usable forgery, and pays for message queries inside the primitive probability bound.

The new target is a two-regime argument, split at

    x_0 = 3*2^-14,       q_0 = 3*2^114.

For x<=x_0, bound completed primitive forgery witnesses and ordinary coverage charges together by (7/4)x. For x>=x_0, use the paper primitive bound 2x-x^2/8, which already includes the same ordinary coverage charge. In either range, the proposed unpaid coverage excess is at most 2^-16 x plus smaller errors.

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

This gives an exact transfer of the static chain experiment to backward witnesses in the actual execution. Internal honest prefix evaluations only compute already supplied frontier and forward values, and do not disclose their intermediate values to the adversary. The simulator can omit those internal evaluations while routing adversarial and verification prefix queries to the real functions. Their number remains bounded by the original syntactic hash budget, including when the input was previously evaluated internally by an honest algorithm.

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

Let B be the first primitive match and A_msg the number of message-domain hash calls before B or earlier termination. The paper bound is

    P[B] + (3/(2N)) E[A_msg] <= 2x-x^2/8.

The reward term is part of the same stopped experiment. After t rounds, the largest conditional two-probe hazard is at most h_t=1-((N-t-1)/(N-t))^2. A scalar decision problem either earns 3/(2N) for a message round or takes that hazard. Its optimal value is

    max_(0<=a<=q) [3a/(2N)+1-((N-q)/(N-a))^2].

An elementary polynomial inequality bounds this by 2x-x^2/8 for q<=N/2. Thus ordinary coverage can be paid without adding its whole cost after an already saturated primitive union bound.

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

    P[forge] <= 2x-x^2/8+2^-16 x+epsilon.

At x=x_0, x/8-2^-16=2^-17, and this difference increases with x. Thus the large-budget range leaves at least 2^-17 x for the remaining errors. For q>=1, epsilon(q)/x<=2^-94+2^-109+2^-572<2^-17. At q>=N/2 use the probability bound by one. Both nontrivial ranges therefore close numerically at P[forge]<=2x=q/2^127.

The implementation order should follow the mathematical dependencies and produce useful endpoints:

1. Review the exact planted-graph and reference-encoding experiments against the concrete byte domains and independently sampled secrets. Establish the SUF decomposition with Option failures and the rejection of overlong logs.
2. Establish the degree-14 and degree-13 certificate bounds with one terminal domination, the same stopped execution costs, and no conditioning on future good events. This is the highest-risk new probability construction and should be the first new coverage endpoint.
3. Establish the forced-first-guess comparison and combine it with degree-13 coverage. The resulting endpoint should prove the original-game bound throughout q<=3*2^114, using the OTS likelihood estimates and disjoint query costs.
4. Establish the paid primitive inequality in the concrete augmented experiment and combine it with degree-14 coverage. This closes the remaining range up to q=N/2.
5. Assemble the public 127-bit theorem for the unchanged statement and inspect its assumptions and axioms. This is completion; intermediate numerical endpoints are not completion.

The two coupling interfaces now have explicit paper kernels: a geometric rejection bridge with independent auxiliary randomness, and a deferred-secret kernel whose local hit and miss probabilities give the forced-guess likelihood exactly. The common terminal domination follows from finite-prefix independence and falling-factorial moments. Formalization must retain the recorded-history boundary: message queries, signing responses, and actual costs are recorded, while secret-dependent internal non-message inputs remain hidden. The plan does not depend on a further improvement of the final constants.

The Python files under paper-127 contain exact rational checks of partial-table likelihoods, conditional reference-table laws, finite probe decision problems, moment bounds, and closing constants. In particular, coverage-closing-checks.py checks the new proposal, Poisson, and two-regime arithmetic; adaptive-kernel-checks.py checks the local planted-table kernel and rejection-bridge factorization on finite examples. They can each be run with Python 3 and use only its standard library. These checks support the written arguments; they neither implement the security experiment nor certify the full adaptive constructions or the final Lean theorem.

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

The local bridge now applies to actual signing records, with the conditional index cap proved at each fixed full pre-state. The next missing coverage step is its adaptive composition through the paper's recorded-history filtration. In particular, the marginal erasure theorems do not establish the hidden-label posterior or independence of unqueried message cells after conditioning on that history. The raw forecast and the proposal residual law must be shown to depend only on the permitted history, then connected to one terminal proposal variable. The prefix and cache exception bounds, terminal Poisson excess, and banked certificate charging also remain open. The checked boundary estimate assumes its explicit clean-state and proposal-count hypotheses; it does not prove that an adaptive original execution satisfies them, the adaptive coverage inequality, or any strengthened public security theorem. The [paper review](paper-127/paper-review.md) states the original-experiment endpoints needed for completion.
