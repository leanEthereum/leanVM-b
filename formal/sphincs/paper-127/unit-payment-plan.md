# A direct quadratic payment and the remaining 127-bit proof

This paper review uses the unchanged experiment on branch `sphincs-fv` at `09dbcf69`. It adds no Lean source. The current public theorem establishes 126 bits. The 127-bit conclusion below is conditional on the explicitly listed original-experiment transfers; those are mathematical obligations, not assumptions to add to the public statement.

Subsequent formalization proves the unit payment in [UnitCertificateCoverage.lean](../SphincsSecurity/Proof/UnitCertificateCoverage.lean). [CertificateFamilyGame.lean](../SphincsSecurity/Proof/CertificateFamilyGame.lean) puts the full bank and all 14 near banks on a single execution with shared cache, proposal word, counters, stopping state and cache-exception flag. Each bank projects exactly to its original certificate game, and the verdict/cache projection is the original SUF experiment. [CertificateFamilyCoverage.lean](../SphincsSecurity/Proof/CertificateFamilyCoverage.lean) proves both coverage inequalities on this one law, while [CertificateFamilyClean.lean](../SphincsSecurity/Proof/CertificateFamilyClean.lean) pays the common exception event once and transfers the administrative-stop and terminal-certificate results. The shared stop may depend on the cache and common counters, but not on bank contents or their differing coverage prices. These results concern the original law; they do not establish the hidden-label hazard, the OTS likelihood projection, or coverage in forced-secret laws.

The recommendation is to keep the fixed proposal word and the two budget ranges, but pay ordinary full coverage at one unit per message query, rather than three halves. The existing moment bounds already support this. It replaces the large-budget scalar maximization by a direct potential with two elementary transition inequalities. It preserves the existing split and the same final error margin. The difficult remaining work is the concrete graph and witness transfers.

## Target and constants

Let

\[
N=2^{128},\quad I=2^{26},\quad L=1024,\quad S=2^{24},\quad x=q/N.
\]

The desired statement is \(\Pr[\mathrm{SUF}]\le 2x\). The budget \(q\) counts every original hash call, including key generation, failed signing, successful signing, adversarial queries, and verification. It counts repeated calls too. The signing cap and novelty test use the complete original log. Independent secrets, finite retry exhaustion, and every signature field remain unchanged.

Use

\[
M=25313293,\qquad x_*={3\over2^{14}}={12\over2^{16}},\qquad q_*=3\cdot2^{114},
\]

\[
\delta={11\over2^{16}},\qquad
\epsilon(q)={q\over2^{222}}+{q\over2^{170}}+2^{-700}.
\]

Here \(\delta\) replaces the earlier \(2^{-13}\) allowance because the baseline changes from \(3/2\) to \(1\). For every admitted \(q\ge1\),

\[
{\epsilon(q)\over x}\le2^{-94}+2^{-42}+2^{-572}<2^{-16}.
\]

For \(q\ge N/2\), the bound follows from probability at most one. Only \(1\le q<N/2\) needs a cryptographic argument.

## The existing moments support payment at one

Complete the adaptive proposal execution into its uniform word of fixed length \(M\), and let \(Z_i\) be its occupancies. The word has the uniform marginal; it need not be independent of the original execution. Define

\[
R=2^{-48}\sum_i Z_i^{14},\qquad
R_{\rm near}={14\over2^{38}}\sum_i Z_i^{13}.
\]

The [fixed-word calculation](variance-route.md), already represented in [FixedProposalMoments.lean](../SphincsSecurity/Proof/FixedProposalMoments.lean), supplies

\[
\mu=\mathbb E R\le{1\over5},\qquad
\operatorname{Var}(R)\le{13\over25000},\qquad
\mathbb E R_{\rm near}\le557.
\]

For every real \(y\) and \(a>0\), \((y-a)_+\le y^2/(4a)\). Above the threshold this is equivalent to \((y-2a)^2\ge0\), and below the threshold it is immediate. Therefore

\[
\mathbb E(R-1)_+
\le {\operatorname{Var}(R)\over4(1-\mu)}
\le {13\over80000}
< {11\over65536}=\delta.
\]

The generic baseline theorem `expected_fixedCertificateGame_count_le_message_excess` in [FixedCertificateCoverage.lean](../SphincsSecurity/Proof/FixedCertificateCoverage.lean) already allows baseline \(1/N\). Its mathematical specialization gives

\[
\boxed{\mathbb E C_{\rm full}\le{\mathbb E A_{\rm cov}\over N}+\delta x.}
\]

Here \(C_{\rm full}\) counts banked full certificates and \(A_{\rm cov}\) counts actual monitored message calls. The subsequent Lean specialization and its transfer to the shared game are now proved. The near estimate \(\mathbb E C_{\rm near}\le557x\) holds on that same law with its common stopping rule; extending it to forced-secret laws remains necessary.

The adaptive charging proof remains essential. If a creation multiplier \(a_j\) is predictable and the forecast is dominated by the conditional terminal price, then its excess is paid through \(\mathbb E[\sum_j a_j(R-1)_+]\le q\mathbb E(R-1)_+\), using the pathwise bound \(\sum_j a_j\le q\). The ordinary part uses \(\mathbb E\sum_j a_j\le\mathbb E A_{\rm cov}\). There is no factorization of an adaptively chosen occupancy and an adaptively chosen query count.

## A direct primitive potential

Let \(B\) be the first external primitive match from [the canonical-graph argument](paid-probe-quadratic.md), including matches during final verification. Let \(A_B\) count original message calls before \(B\) or original termination. This primitive process does not stop at the coverage exceptions.

The concrete graph argument must establish the following conditional hazard. After \(r\) external probe rounds, each hidden coordinate has at least \(N-r\) unexcluded values. A next probe has at most one hidden-input test and one fresh-output test, involving distinct hidden coordinates when both are hidden. Its probability of raising \(B\), conditional on survival and the permitted history, is at most

\[
h_r=1-\left({N-r-1\over N-r}\right)^2.
\]

Repeated external rows and allowed canonical reads can count as dummy probes. Message queries and honest internal hash calls exclude no hidden candidates. Uniform sampling and permitted disclosures use no hash slot. These are claims about the exact original graph presentation, not consequences of the scalar calculation below.

Once that hazard is established, define, for \(k\) remaining hash slots,

\[
F(r,k)=1-\left({N-r-k\over N-r}\right)^2,
\qquad r+k\le q\le N/2.
\]

We have \(F(r,0)=0\) and \(0\le F(r,k)<1\). There are just two transitions to check.

For a probe, failure has payoff one. Since the surviving continuation value is below one, replacing its actual hazard by \(h_r\) can only increase the upper bound. Direct cancellation gives

\[
h_r+(1-h_r)F(r+1,k-1)=F(r,k).
\]

For a non-probe hash slot, allow reward \(1/N\), even if that slot is not a message call. For \(k\ge1\),

\[
F(r,k)-F(r,k-1)
={2(N-r-k)+1\over(N-r)^2}
\ge{1\over N},
\]

because \(N-r-k\ge N/2\) and \(N-r\le N\). Hence \(1/N+F(r,k-1)\le F(r,k)\). Slots earning no reward satisfy the same inequality. Early termination can discard the remaining nonnegative potential; free transitions preserve the bound through their conditional kernels.

Backward induction now proves the joint estimate

\[
\boxed{\Pr[B]+{\mathbb E A_B\over N}\le F(0,q)=2x-x^2.}
\]

The proof permits adaptive choices of probe and paid slots. It requires no independence of that schedule, no maximization over schedules, and no additional split at \(x=1/4\).

## Closure of the large range

Attach coverage to this same original execution and stop it additionally at \(B\). Complete an active signing invocation and bank its certificates before acting on post-invocation guards. Honest signing cannot raise \(B\). On an external hash query that raises \(B\), no message reward is added. Thus \(A_{\rm cov}\le A_B\) pathwise.

Two concrete obligations are needed here:

1. An accepted strong forgery with no primitive match supplies a full certificate with own-input exclusion. Backwards tracing must fix all authentication nodes, chain values, counters, and FTS secrets. If its message/randomizer input was successfully signed, every field must equal that returned signature, contradicting strong novelty. Canonical encoding exhaustion admits no such accepting component.
2. Every coverage stop that could discard a winning run is either \(B\) or one of the bounded exceptions. The signing cap, cache consistency, actual spent budget, and minimum-cost gates must be discharged by reachability invariants.

These give

\[
\Pr[\mathrm{SUF}]
\le\Pr[B]+\mathbb E C_{\rm full}+\epsilon(q)
\le2x-x^2+\delta x+\epsilon(q).
\]

For \(x\ge x_*\),

\[
x-\delta\ge {12-11\over2^{16}}=2^{-16}
>{\epsilon(q)\over x}.
\]

Consequently this proves the target throughout \(q_*\le q<N/2\), once the two concrete obligations and the graph hazard are established. This should be the next complete original-game security milestone.

## The small range still needs completed witnesses

The quadratic saving is too small near zero to pay a fixed positive coefficient \(\delta x\). The smaller range therefore still needs the [allocated OTS and FTS witness argument](small-budget-transfer.md). Its proposed bound, with the new ordinary coverage price, is

\[
\begin{aligned}
\Pr[\mathrm{SUF}]\le{}&c_Q(x){\mathbb E Q\over N}
+c_{\rm enc}(x){\mathbb E A_{\rm enc}\over N}
+{\mathbb E A_{\rm str}\over N}
+{\mathbb E A_{\rm msg}\over N}\\
&+{557x^2\over1-x}+{x^2\over2(1-x)^2}+\delta x+\epsilon(q),
\end{aligned}
\]

where

\[
c_Q(x)={{3\over2}+4x+2x^2\over1-x}
+{4x\over(1-x)^2}+{82x\over1-x},\qquad
c_{\rm enc}(x)=1+{3444x\over1-x}.
\]

The counts partition actual monitored query costs: \(Q\) charges OTS steps below the reference frontier, \(A_{\rm enc}\) charges nonreference encoding queries, \(A_{\rm str}\) charges other structural queries, and \(A_{\rm msg}\) charges message calls. They must satisfy \(Q+A_{\rm enc}+A_{\rm str}+A_{\rm msg}\le q\) on the same original path. They cannot each receive the whole budget before addition.

For \(0\le x\le x_*\), monotonicity and exact rational evaluation give

\[
\max(c_Q(x),c_{\rm enc}(x),1)<{131\over80},\qquad
{557x\over1-x}+{x\over2(1-x)^2}<{9\over80}.
\]

Thus the proposed witness inequality closes as

\[
\Pr[\mathrm{SUF}]\le\left({7\over4}+\delta\right)x+\epsilon(q)<2x.
\]

The numerical slack does not prove the witness inequality. Two transfer arguments deserve a separate mathematical audit before a large Lean implementation.

For OTS, let \(Y=H_{d-1}\circ\cdots\circ H_0(S)\) and let \(W(H,Y)\) count its starting preimages. The real law relative to an independent endpoint has density \(W\) only after forgetting \(S\) and private prefix evaluations. If \(S\) is retained, the density is instead \(N\mathbf 1_{H_{d-1}\circ\cdots\circ H_0(S)=Y}\). For partially observed prefix tables, the projected density is

\[
w(T)=\mathbf 1^T P_0\cdots P_{d-1}e_Y
\ge\prod_j(1-a_j/N)\ge1-Q_i/N\ge1-x.
\]

This can transfer each chain's allocated ideal cost to its original cost. Every charged event, count, and stop must be computable after the projection. In particular, private cache-hit information cannot be retained. Full cache cardinality may depend on the forgotten prefix; its administrative guard must first be removed using the original invariant that distinct cached rows are bounded by spent calls. The intended projected monitor keeps the message cache, successful views, counters, and independent geometric lengths. Ideal endpoints can lack a compatible real secret, so auxiliary OTS executions need an explicit cap at \(q\). Both orders of encoding preparation and chain inversion must be paid; the unit-neighbor counts are at most \(42\cdot41=1722\) in total and \(41\) for a fixed lowered chain.

For FTS, use deferred secrets. An undisclosed, unguessed coordinate is uniform on its remaining candidate set \(U\). A fresh candidate has true-hit probability \(p=1/|U|\le1/(N-q)\). A miss can still return the public leaf hash as an alternative preimage; that event must remain separate from a true hit. A successful signature discloses a coordinate chosen without inspecting its hidden value; failed signatures disclose none.

To pay one true guess together with a near certificate, force the first true guess at hash slot \(j\), and force earlier eligible slots to miss. In the projected execution its likelihood factor is

\[
L_j=p_j\prod_{t<j}(1-p_t)\le{1\over N-q}.
\]

Each forced branch must have positive original conditional probability and preserve the actual \(q\) budget. Fresh message cells must remain uniform in the current deferred state. Only after establishing this comparison should a separate rejected-proposal bridge be attached to each forced law. The required theorem is near coverage in each such law, giving \(557x^2/(1-x)\) after summing over \(j\). The original-law near estimate alone cannot be multiplied by a guessing probability. Two distinct true guesses cost at most \(x^2/(2(1-x)^2)\). Exceptional probabilities are paid once in the original experiment; banked certificate bounds already include stopped forced executions.

## Concrete milestones and completion criteria

| Order | Deliverable | Required evidence |
| --- | --- | --- |
| 1 | Exact canonical graph and deterministic SUF decomposition | Preserve the original response and cost law; cover arbitrary query bytes, repeated rows, every signature field, both failure cases, and own-input exclusion. |
| 2 | One projected coverage monitor with all first stops accounted for | Common stopping history for the full and 14 near banks; cache and deficit exceptions coupled to that execution; proposal overflow persists; administrative gates cannot discard a winning prefix. |
| 3 | Original-game security for \(q_*\le q<N/2\) | Derive the hidden-label hazard, apply the direct potential, and combine with coverage using \(A_{\rm cov}\le A_B\). The only adversary premise is the original hash bound. |
| 4 | Original-game security for \(1\le q\le q_*\) | Prove the projected OTS cost transfer and the supported forced-FTS coverage extension, then retain the disjoint query allocations through the final inequality. |
| 5 | Public 127-bit theorem | Combine the two ranges and probability at most one, with unchanged algorithms and an explicit audit of theorem dependencies. |

For the exception milestone, a sum of marginal probability bounds is usable only after each relevant first stop has been related to the corresponding event on this execution. Private full-cache moments may be used to bound the original exception probability; that does not authorize exposing those private statistics in the OTS likelihood history. The monitor's actual index guard can use the projected counts \(C_i\le2^{-36}t+2^{80}\), while a stronger private-cache event is only an analytical upper bound on its failure.

The paper calculations in this review check the new excess allowance, both transition identities of the direct potential, and both closing ranges with exact rational arithmetic. Finite scalar consistency checks also agree. They do not verify the concrete cryptographic transfers. The recommendation is to pursue the plan because its constants close and its large-range scalar proof is now short, while treating the OTS projection and forced-secret coverage as the principal remaining research risks. A collection of helper lemmas with those obligations as premises is not a completed 127-bit proof.
