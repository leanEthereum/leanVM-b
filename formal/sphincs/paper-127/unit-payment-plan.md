# A direct quadratic payment and the remaining 127-bit proof

This paper plan has been reviewed against the unchanged experiment on branch `sphincs-fv` at `90eb52d0`. This review adds no Lean source. The current public theorem establishes 126 bits. The 127-bit conclusion below is conditional on the explicitly listed original-experiment transfers; those are mathematical obligations, not assumptions to add to the public statement. The final mathematical review specifies the next checks before further formalization.

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

**Paper audit before the next implementation.** The two-range argument remains the recommended route. Its benefit is mathematical: the first primitive match is a sufficiently accurate event when the quadratic saving is large, whereas small budgets require the extra work that makes a match usable in a signature. The following points make the remaining proof obligations more concrete. They do not assert that the existing original-game theorems already discharge them.

**Why the small-budget coefficient can be below two.** For independent uniform functions \(f,g:[N]\to[N]\), an independent uniform secret \(S\), and a fixed candidate \(a\),

\[
\Pr[f(a)=f(S)]={2\over N}-{1\over N^2},
\]

\[
\Pr[g(f(a))=g(f(S))]
=\left({2\over N}-{1\over N^2}\right)
+\left(1-{2\over N}+{1\over N^2}\right){1\over N}
={3\over N}-{3\over N^2}+{1\over N^3}.
\]

The first equality splits on \(a=S\); the second splits on equality of the two inputs to \(g\). Thus a fixed two-call attempt has leading success probability \(3/(2N)\) per call. A single last-edge query against a hash-derived endpoint can instead have probability \(2/N-1/N^2\). These examples explain why charging the first contact can lose the desired improvement. They are not adaptive inversion bounds. The adaptive proof must account for merged paths, old work, and both orders of querying the last two edges.

For a reference digit vector \(d\) and a different valid vector \(e\), write \(b=\sum_j(d_j-e_j)_+\). Equal digit sums imply \(b\ge1\). If \(b=1\), exactly one digit falls by one and one rises by one, giving at most \(42\cdot41=1722\) possible words and at most \(41\) lowering a specified chain. Once structural matches above the reference frontiers are excluded, \(b\ge2\) requires either a two-step chain inversion or contacts with two distinct chains. This deterministic dichotomy is the source of the small-budget improvement; a proof that only counts arbitrary hidden guesses discards it.

**One original execution, with separate analytical histories.** All of the estimates must retain the same original visible behavior and actual hash costs, but they do not use the same conditioning information.

| Analysis | Information retained | Information that must remain unobserved |
| --- | --- | --- |
| Primitive hazard | Canonical public cut, exact reference counters and words, external rows, message rows, disclosed FTS secrets, costs and control stage | Remaining hidden labels, private honest query inputs, and private cache-hit information |
| OTS likelihood for chain \(i\) | Its frontier \(Y_i\), externally queried prefix rows, reference data, original costs, and an auxiliary simulator depending on the prefix only through \(Y_i\) and those replies | Its starting secret and private prefix evaluations |
| Forced FTS guesses | Deferred candidate sets, analytical true-hit flags, ordinary replies, disclosures, message cache, and projected monitoring state | Unqueried message cells and unused proposal letters |

For the OTS likelihood calculation, independent auxiliary randomness can be fixed to prove the prefix density identity. Fresh-encoding or fresh-message probabilities must be proved in a history that hides their unqueried rows, then integrated into expectations on the same execution. They do not hold after exposing their entire future tables. The small-budget monitor must continue after a first primitive match. Stopping it at that match would discard later encoding preparation and later covering signatures used by the completed-witness argument.

**The canonical graph must be an exact sampling construction.** A finite topological construction samples an independent label at every canonical node and programs that node's uniquely addressed function at its canonical child payload. Conditional on previously sampled children, this programs one row in a separate domain with a uniform answer, exactly as the original random function does. Other rows are left independent and uniform. Repeated honest reads use that same programmed row. Numerical equality of labels at different nodes is allowed; no global distinct-label event or birthday loss is needed.

Sample the reference counter and word using the exact finite-search distribution, including exhaustion with an independent dummy word. Conditional reference rows, preceding invalid rows, unrestricted rows and high output bits must then reconstruct the original encoding table. The canonical messages depend only on the structural graph. Consequently the reference data can be sampled independently of that graph, and the choice of exposed cut does not bias its hidden labels. The original signer, including all three layer computations and both kinds of failure, runs against the reconstructed oracle and retains its original costs.

Two concrete details control the posterior proof. First, an externally fresh row can already have been read privately by the signer. If its payload guesses a hidden canonical child, it must still be tested; global cache freshness cannot replace external freshness. On a miss, it is a noncanonical row, so no honest structural computation has read it, and its unobserved answer is uniform. Second, disclosed FTS coordinates must be selected using the digest and exposed failure data, before inspecting their hidden values. Private computation counts must be determined by the exposed reference data and message trace, not by the hidden labels. These are the conditions under which the two-coordinate mass calculation in the [canonical-graph note](paid-probe-quadratic.md) gives the posterior invariant.

**Coverage needs a theorem about its transition rules.** The present [original-game coverage theorem](../SphincsSecurity/Proof/CertificateFamilyCoverage.lean) proves a substantial part of the argument, but its statement is specialized to `certificateFamilyGame`. Its stopping parameter is a function of the secret key and the existing monitored record. Sampling an entire canonical graph and conditioning on it changes the structural response kernel; forcing a secret guess changes another kernel. Neither construction is automatically an instance of that theorem merely because it has the same visible message interface.

The required extension should retain the numerical cache, deficit and proposal guards specified above and derive coverage from the following local facts, already used by the paper forecast calculation:

1. The initial message cache is empty. Conditional on the current analytical state, every fresh message cell is uniform and repeats are consistent. Other transitions cannot insert unseen message cells.
2. Each signing invocation uses the original finite digest loop with independent randomizers. Its post-selection computation makes no message calls and produces either failure or the selected view at its actual input. The selected view bounds the possible successful view even if failure depends on it.
3. All calls retain their actual costs and the original common budget. A completed invocation costs at least \(L=1024\); a digest exhaustion costs \(2^{32}\), and reaching post-selection entails the fixed FTS-opening work. The signer cannot invent a view at a different input.
4. The full bank and all near banks have the same stopping rule. It uses current information, does not read unused proposal letters, and banks an invocation's completed certificates before applying its post-state stop. Every discarded winning execution is classified separately.

The local shape-moment inequalities and creation charges depend on these facts, not on uniformity of non-message answers or on a fixed secret sampled in advance. The proposal bridge must be constructed from the record distribution in each particular law. Its accepted-index distribution is governed by the message cache and the unchanged digest loop. The revised [coverage proof](cached-target-forecast.md) carries the conditional forecasts, fixed terminal word and unit payment through these transition rules on paper. It also bounds the cached-index exception directly using message-cache counts minus the expected counts at the actual spent budget, retaining q/2^170 without inspecting private non-message cache rows. Its Lean generalization and concrete interpreter instantiations remain necessary. Unconditional uniformity of a terminal word by itself does not suffice.

There are three applications to establish explicitly: the original monitored law, the graph presentation with the additional primitive stop, and every supported law obtained by forcing the first true FTS guess. For the OTS likelihood comparison, first express the base monitor using the message cache, signing views and retained costs. Eliminate redundant full-cache administrative guards using their original reachability invariants. A private cache-hit flag cannot simply be carried through the projection that forgets a secret's private evaluations.

**The OTS transfer has a precise mathematical test.** Fix one chain and let \(\pi_i\) forget its starting secret and private prefix computations. An exact simulator must recover every charged event, stopping decision and count from the projected variables. It may depend on the chain's endpoint and observed prefix replies, but may not inspect an unqueried prefix row. Private honest computations are replaced by their original cost debits, determined by the reference data and tree shapes. Give idealized executions an explicit \(q\) cap, which never changes an admitted real execution.

The [reference-frontier proof](reference-frontier-transfer.md) now audits every use of an OTS starting secret in the concrete honest algorithms and gives their exact cost formulas, including all three layers when signing fails. It proves a causal transcript factorization, the resulting stopped likelihood comparison, and the conditional restart used to retain shared costs. This makes the paper comparison explicit. Its implementation still has to establish the concrete interpreter correspondence in Lean.

For a complete prefix table \(H_i\) and an independently uniform endpoint \(Y_i\), direct summation over the forgotten uniform secret gives

\[
{d\pi_i(R)\over dI_i}(H_i,Y_i)=W_i(H_i,Y_i).
\]

The endpoint-dependent auxiliary simulator uses the same conditional kernel in both laws, so that kernel cancels in this identity. Averaging over unqueried prefix rows gives the partial-table likelihood \(w_i\) already displayed above, and \(w_i\ge1-Q_i/N\ge1-x\). This proves the transfer of every nonnegative projected cost. It does not transfer an unprojected secret-dependent statistic. As a diagnostic, retaining \(S_i\) changes the density to \(N\mathbf1_{H_i(S_i)=Y_i}\), where \(H_i\) denotes the full prefix composition; treating that density as \(W_i\) is false even for a one-edge identity table.

After this projection is justified, the adaptive chain calculation has a concrete charge ledger. Productive last-edge attempts contribute at most twice their count plus the number of older queried paths ending at their inputs. Each older queried input has only one such endpoint, so it is charged at most once. If \(a\) counts queries before the last two functions, \(b\) penultimate-function queries and \(c\) last-function queries, the baseline is

\[
a+b+2\min(b,c)\le{3\over2}(a+b+c).
\]

Reverse-order attempts and multiple contacts contribute the stated terms involving \(x\). Transfer each chain's stopped allocated cost to its real cost before summing across chains. The result must use the single real \(Q\), with no factor for the number of addresses. The two unit-neighbor orders must likewise end in the real \(Q\) and \(A_{\rm enc}\) expectations. The reference-frontier proof spells out these transfers; preserving their projected histories and cost allocations is critical in the Lean translation.

**The forced-FTS transfer has a different test.** In the deferred representation, a candidate \(z\in U\) is the true secret with probability \(1/|U|\). On a miss, return a uniform low answer and delete \(z\) from \(U\), including when that answer happens to equal the public leaf hash. That latter event is an alternative preimage, not a true-secret disclosure. A true hit or a signing disclosure retires the coordinate and fixes its secret. These exact local kernels preserve a product of uniforms on the remaining candidate sets.

Forcing earlier eligible misses and the eligible hit at slot \(j\) changes only these conditional branches. Both have positive original probability in the relevant budget range. Each finite forced transcript can be completed by choosing remaining secrets from their nonempty sets and programming their still-unqueried canonical rows. Observed rows remain unchanged, so the completed transcript has original support and preserves the original hash count. Future message cells have not been inspected by this construction and keep their uniform kernel.

For every nonnegative terminal statistic \(F\) in this projected experiment, multiplying the changed conditional probabilities gives the exact identity

\[
\mathbb E_R[\mathbf1_{\{\text{first true guess at }j\}}F]
=\mathbb E_{R_j}\left[p_j\prod_{t<j}(1-p_t)F\right].
\]

Set the weight to zero if the forced slot is not reached or eligible. Apply the generalized coverage argument within each \(R_j\), with its own proposal bridge. Taking \(F=\mathbf1_{\{C_{\rm near}\ge1\}}\) then gives the required \(557x^2/(1-x)\) term. This construction handles covering signatures on either side of the guess. Multiplying the original-law near estimate by a guessing probability, without the identity and coverage in \(R_j\), would not establish it.

**Completion gates and order of work.** On paper, first settle the OTS projection and the coverage extension just described, because their failure could invalidate the proposed small-budget bound even if the large-budget proof succeeds. Also check the deterministic backwards trace against the concrete verifier: it must either produce the stated witnesses or fix every signature field to the canonical one. In particular, a successful response at the forgery's own input must force equality of the complete signature, and an exhausted canonical encoding must admit no accepting reference component. The accepted event must concern the full original signing log.

Once those paper arguments are satisfactory, the first security milestone to formalize should be the original-game large-range inequality

\[
q_*\le q<N/2
\quad\Longrightarrow\quad
\Pr[\mathrm{SUF}]\le2x-x^2+\delta x+\epsilon(q)\le2x.
\]

Its only adversary hypothesis should be the original whole-experiment query bound. The next security milestone should be the small-range inequality with the disjoint real allocations, yielding \(\Pr[\mathrm{SUF}]\le(7/4+\delta)x+\epsilon(q)<2x\). Probability at most one handles the final range. A posterior helper, an isolated inversion theorem, or a conditional assembly theorem is useful only as a step toward one of these original-game statements.

The arithmetic has been rechecked with exact rational numbers: at \(x_*\), both OTS coefficients are below \(131/80\), the extra FTS coefficient is below \(9/80\), and \(x_*-\delta-\epsilon(q)/x\) is positive using the uniform error bound above. Exact finite checks of the two potential transitions agree for \(N=2,\ldots,100\). Those finite checks are consistency checks; the displayed algebra supplies the general scalar argument. This review establishes a concrete plan with sufficient numerical slack. It does not certify the complete adaptive cryptographic transfers or a 127-bit Lean theorem.
