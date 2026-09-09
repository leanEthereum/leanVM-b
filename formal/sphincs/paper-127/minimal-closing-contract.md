# A minimal mathematical contract for the 127-bit proof

This paper review concerns the unchanged game through `7a0816c9`. It adds no Lean code. The public statement currently stops at 126 bits. The purpose here is to specify sufficient intermediate results, explain why their combination works, and identify which correspondences must be proved before calling this a security proof. This is the current plan; some earlier development notes use different constants and an independently uniform dummy word on encoding exhaustion.

## Conclusion of the review

The two-range route has sufficient numerical room. Its completion depends on concrete adaptive probability arguments, rather than sharper numerical estimates. I recommend retaining the current split and simplifying the small-range target to the dyadic bounds below. This leaves room to weaken intermediate constants without changing the public security claim.

The branch now has exact canonical graph sampling, simultaneous full-table reference conditioning across all addresses, and an original-game correspondence for signing with private prefix rows masked. [ReferenceFamilyGame.lean](../SphincsSecurity/Proof/ReferenceFamilyGame.lean) uses the sampled family directly to initialize its cuts and preserves the original SUF law and hash budget. [AdaptiveChainEndpoint.lean](../SphincsSecurity/Proof/AdaptiveChainEndpoint.lean) proves the projected likelihood and allocated cost comparison for an adaptive prefix-oracle interface, deriving the posterior row-completion law and syntactic query accounting. The concrete OTS simulator correspondence and coverage in the forced-FTS laws remain the main mathematical risks. The original-game equality proved for a real frontier does not authorize inserting an independent endpoint into its place without that correspondence.

Use the accepting-verifier argument and the explicit probability transitions below to fix the events and retained state before more formalization. The next security milestone should be the large-budget interval of the original game. Do not spend the remaining margin on tighter occupancy estimates: the weaker bounds below suffice.

The further paper derivations below specify an endpoint simulator, its adaptive transcript mass, and the accepting-verifier trace against `Statement.lean`. They explain why the proposed comparisons have a mathematical route for this particular signer. The coverage extension to changed transition laws and the concrete interpreter correspondences remain obligations. In particular, the arithmetic checks alone do not establish either original-game interval.

## The target and a sufficient closing calculation

Put

\[
N=2^{128},\qquad x=q/N,\qquad x_*=3/2^{14},\qquad
\delta=11/2^{16},\qquad
\epsilon(q)=q/2^{222}+q/2^{170}+2^{-700}.
\]

We need \(\Pr[\mathrm{SUF}]\le 2x\). Every original hash call consumes budget, including private honest work, repeated inputs, failures and verification. The signing cap and the strong novelty test retain the complete original log. For \(q\ge1\),

\[
e:=\epsilon(q)/x\le 2^{-94}+2^{-42}+2^{-572}<2^{-16}.
\]

For \(x\ge1/2\), probability at most one proves the claim. The remaining two intervals have the following sufficient contracts.

| Interval | Required bound on the original SUF experiment | Closing reason |
| --- | --- | --- |
| \(x_*\le x<1/2\) | \(\Pr[\mathrm{SUF}]\le2x-x^2+\delta x+\epsilon(q)\) | \(x-\delta\ge2^{-16}>e\) |
| \(0<x\le x_*\) | \(\Pr[\mathrm{SUF}]\le(15/8+\delta)x+\epsilon(q)\) | \(15/8+\delta+e<30723/16384<2\) |

These are desired conclusions with only the original hash-bound premise. They are not new assumptions for the public theorem.

## Common foundation: the exact graph and signer

Use a finite canonical graph, with one structural node per valid serialized tweak. Sample the independent secret leaves and independent canonical outputs in topological order. At each domain, program its canonical child payload to that output; other rows are independent uniform values and are memoized when requested. Two labels at different coordinates may have the same numerical value. No distinct-label condition or global birthday exception is needed.

For each OTS address, the canonical message is fixed by this non-encoding graph. The original finite encoding search therefore has an exact conditional-table presentation: its earlier canonical-message rows are invalid, its first valid row contains the reference word, and the remaining rows are uniform. Preserve exhaustion with its original probability. A valid dummy word on exhaustion is analytical data only. The 256-bit replies retain independently sampled high halves as well as their low 128-bit graph values.

Expose each OTS chain at its reference digit and above. Honest signing uses a private prefix only to reach this frontier or the full endpoint. Replace those private evaluations by their supplied result and the original number of cost markers. Reconstruct all roots, layer messages and authentication data consistently. Preserve the finite digest loop, every encoding search, all three layer computations even when a layer fails, and the selected FTS view when a later failure returns `None`.

The probability correspondence should be proved by equality of finite transition kernels, extending the externally observed row table one query at a time. Each finite execution observes finitely many residual rows, so this argument does not require first sampling a uniform function on the infinite type of arbitrary byte strings. It must preserve full external replies, original responses, the message trace and original costs. Equality for each compatible fixed function is only the deterministic part of this argument.

Classify external inputs by their bytes. An externally new row is new to the external history even if honest signing evaluated it privately. Neither hidden private inputs nor private cache-hit flags may enter the hidden-label history. Address separation limits a query to its own canonical target, including when its candidate value equals a label in another domain.

### The complete reference family, with a simpler exhaustion convention

The small-budget experiment conditions on all reference cuts at once. Independence of their marginal selected words is insufficient: retain the shared oracle table that answers every later query. Here is the required finite mass identity.

Let \(m=|\mathcal C|\), \(v=m/N\), and \(T=2^{32}\). Choose a fixed valid word \(d_*\): 27 digits equal to 7, one equal to 2, and the other 14 equal to 0. Its sum is 191. At each address use

\[
\Pr[J=j,D=d]=(1-v)^j/N\quad(j<T,\ d\in\mathcal C),
\qquad
\Pr[J=\bot,D=d_*]=(1-v)^T.
\]

On success, condition earlier counter rows to be invalid and the selected row to encode \(d\). On exhaustion, condition every counter row to be invalid. All remaining rows are unrestricted. A full invalid reply has \(N(N-m)\) possible values; a full reply encoding one specified valid word has \(N\). Thus a particular full counter table with first valid row \(j\) has generated mass

\[
\frac{(1-m/N)^j}{N}\,[N(N-m)]^{-j}\,N^{-1}\,(N^2)^{-(T-j-1)}
=N^{-2T}.
\]

A particular exhausted table has mass

\[
(1-m/N)^T[N(N-m)]^{-T}=N^{-2T}.
\]

Fix the entire non-encoding table and secrets first. Its canonical messages are now fixed, and different addresses use disjoint encoding domains, even when their messages coincide. Multiply the displayed identities over addresses and include the independent unrestricted rows. This recovers the uniform full encoding table for every fixed non-encoding environment. Integrating the environment proves the required joint equality for arbitrary adaptive continuations. In the reordered sampler the reference family is independent of the full non-encoding environment, not just of its graph labels.

The fixed dummy avoids an unnecessary extra sampler and fits the existing arbitrary-dummy interface. It does mean that \(D\) need not be uniform independently of \(J\) on exhaustion. No following argument needs that assertion: it needs a valid word and independence of the reference family from non-encoding data. Neighbor counts hold for every valid word, and chain estimates hold for every fixed digit length. Exhausted addresses still have no legitimate reference counter; no signing response or accepting verifier is allowed to use the dummy as an actual encoding result. A verifier using an encoding at such an address is either rejected or uses a nonreference valid row, to which the usual equal-word or backward-witness classification applies.

### Constructing the endpoint simulator without reading its secret prefix

Work inside a finite envelope containing the canonical inputs and every query of the capped simulator, over all its possible supplied frontiers and replies. Each prefix function below needs all \(N\) digest inputs; other residual rows may equivalently be generated lazily. This construction does not sample a uniform element of the function space on arbitrary byte strings.

Fix the sampled reference family. For a chain \(i\) with reference digit \(d_i>0\), separate its low-output functions \(H_{i,0},\ldots,H_{i,d_i-1}\) from all other randomness. Sample its original uniform starting secret \(S_i\) and form \(Y_i=H_{i,d_i-1}\circ\cdots\circ H_{i,0}(S_i)\). A zero digit simply publishes its starting secret as \(Y_i\). Distinct chain-step tweaks give disjoint independent function families. Denote all remaining independent randomness by \(\omega\), including forward functions, other structural functions, FTS secrets, message rows, high output halves, conditional encoding-table seeds, adversary and signing coins, and the projected monitor's auxiliaries.

For supplied \(Y\), compute every chain's remaining positions from \(Y_i\) using only steps \(d_i,\ldots,6\). These full endpoints determine every OTS leaf and hypertree node. The FTS secrets and functions in \(\omega\) determine the FTS keys. Consequently all canonical layer messages and the public root are functions of \((Y,\omega)\). The construction is acyclic: none of these structural computations reads an encoding or message row.

The conditional encoding oracle can be constructed before the adversary starts. At each address, independently sample a counter table with the previously specified law conditional on \((J,D)\), and a uniform residual table for every encoding input. Embed the conditional table at the counter block of the now-computed canonical message; use the residual table elsewhere. This defines the entire oracle consistently even if an external query precedes signing. Changing an endpoint recomputes that canonical message and hence the block's location from the beginning. It does not overwrite a row after an adversary has observed it. The independent random seeds used to fill the two tables do not depend on the selected chain's prefix functions.

The following replacements define the honest part of a simulator \(\Phi(Y,\omega;H)\). Its only access to a selected prefix function is through an external or verification query routed to that function.

| Original subroutine | Value used by the simulator | Original work retained in the count |
| --- | --- | --- |
| A full OTS chain in key generation or tree recomputation | Supplied frontier followed by its forward steps | All seven chain calls, including the omitted prefix |
| A successful canonical `otsSign` | The reference counter and the supplied frontiers | Its \(J+1\) encoding calls and all \(\sum_i d_i=191\) chain calls |
| An exhausted canonical `otsSign` | `None` | All \(2^{32}\) encoding calls |
| `treeRoot`, `treePath`, `ftsKey`, and `ftsOpen` | Values reconstructed from the frontier and \(\omega\) | Every call in the original fixed tree traversal |
| `signDigestLoop` | The original finite randomizer loop on the reconstructed root | Every actual message call, including repeats and exhaustion |
| The three `signLayer` invocations and final assembly | The original three results and `traverseOption` | All three invocations, including those after an earlier layer fails |

The FTS secrets supplied in a successful signature come from \(\omega\). A later layer failure still retains the selected digest in the analytical record but returns no signature and discloses no FTS secret. All original message calls are retained individually. A private prefix's input, intermediate values, and cache-hit flags are erased; only its number of calls remains. Repeated private work still spends its full original count. If a budget cap falls inside omitted work, spend markers one at a time and halt at that cap. The simulator never decides whether a supplied endpoint has a compatible secret.

On real frontiers, composition of the chain identity \(H_{6}\circ\cdots\circ H_0(S_i)=H_{6}\circ\cdots\circ H_{d_i}(Y_i)\) with the displayed subroutine replacements gives the original responses and costs. The fixed-width query classification and the projected monitor make the external prefix tables, contacts, encoding markers, message cache, selected views, and allocated counts functions of \(\Phi\)'s retained trace. This is the deterministic correspondence to establish compositionally in the concrete interpreter. A guard that inspects the private full cache must first be removed using its original reachability invariant; it cannot be included in this trace merely because it is analytical data.

Define the ideal law for chain \(i\) by replacing only \(Y_i\) by an independent uniform value, leaving its prefix functions uniform and using this same \(\Phi\). Recompute every dependent root, message and encoding block. Cap all these executions at the original \(q\); this changes no admitted real execution and gives a bound on ideal executions with no compatible starting secret. Other chains keep their real laws. No product of all chains' likelihoods is needed.

### The adaptive mass calculation

Here is a direct finite proof of the observation rule. Fix \((J,D)\) and the independent auxiliary randomness for a single-chain comparison. Write \(H=(H_0,\ldots,H_{d-1})\), so there are \(dN\) low-output table cells. For a compatible finite retained transcript \(t\), let \(y_t\) be its published endpoint and \(A(t)\) its distinct observed prefix rows. Causality of \(\Phi\) gives

\[
\Pr_I[H=h,Y=y,T=t]
=N^{-dN-1}\,\mathbf 1_{y=y_t}\,\kappa(t,y)
\prod_{(j,a,b)\in A(t)}\mathbf 1_{h_j(a)=b}.
\]

With all auxiliary coins fixed, \(\kappa\) is a consistency indicator for the simulator's requests and stopping decision. If those coins are integrated out, it is their summed weight. In either presentation it is independent of unobserved prefix cells. To prove the formula, multiply the successive transition weights: an auxiliary step uses only the retained history; a fresh prefix query adds its row equality; a repeated query checks an equality already recorded. A stop at a contact, marker, or budget is another function of that history. This proves the formula for adaptive choices and the stopping times used by the argument, without assuming that the choices are independent of past replies.

On the complete table, summing over the real uniform starting secret multiplies the displayed ideal mass by

\[
W(h,y)=\#\{s:H_{d-1}\circ\cdots\circ H_0(s)=y\}.
\]

After conditioning on \(t\), the ideal table is a uniform completion of exactly its recorded rows. Averaging \(W\) therefore gives the partial-table matrix formula and lower bound used below. The same \(\kappa\) occurs on both sides and cancels. If the starting secret or a private cache-hit flag is retained, this factorization fails: the complete-table density with the secret retained is \(N\mathbf 1_{H(S)=Y}\), and an extra flag can constrain an otherwise unobserved row. Thus erasure is a mathematical requirement, not a cosmetic change of the game state.

The auxiliary randomness may be fixed for this prefix argument because its prior is independent of the selected prefix tables and starting secret. It must not be fixed when using a fresh-message or fresh-encoding probability. Those estimates use their own histories hiding the respective unqueried rows and return expectations on the same real law. An adaptive cost can then be transferred using its likelihood identity; no independence of the cost and that likelihood is asserted.

### Backwards tracing of the concrete verifier

The deterministic step needs no probability estimate. Fix one complete oracle, its canonical graph and reference family, and an accepting verification trace. At a structural domain with canonical payload \(a_*\) and canonical output \(v_*\), a query returning \(v_*\) either used \(a_*\), or is a noncanonical output match. Outside those matches, fixed-width payload injectivity recovers every child from a canonical parent. Apply that statement in the following order, backwards through the accepting computation.

| Verification component | Consequence of its recovered parent being canonical |
| --- | --- |
| Top-layer `treeFold`, starting at the public root | Its OTS leaf and every supplied sibling are canonical |
| `leafHash` on 42 recovered endpoints | Each recovered chain endpoint is canonical |
| The chain suffix above its reference digit | Every traversed value at or above the reference frontier is canonical unless a forward structural output match occurred |
| `encode` at that OTS address | Its word either differs from the reference, equals it at a nonreference input, or uses the exact reference message and counter |
| The two remaining layers | The layer links identify the recovered message with the next canonical tree root, and finally the canonical FTS key |
| `ftsRecover`, its roots hash, and each `ftsFold` | Every FTS sibling and leaf hash is canonical; a supplied secret is the true secret unless an FTS noncanonical output match occurred |

For a verified word \(e\) and reference word \(d\), equal digit sums give \(b=\sum_j(d_j-e_j)_+\). If \(e\ne d\), then \(b\ge1\). When \(b=1\), exactly one coordinate falls by one and another rises by one. Acceptance supplies that encoding marker and a queried one-edge path to the lowered chain's reference frontier. When \(b\ge2\), either one decrease is at least two, supplying a complete queried two-edge suffix, or two distinct chains decrease, supplying two contacts. Earlier precomputation and verification's own queries are both included in these witnesses. A path through an alternative preimage below the frontier is allowed. A merger strictly above the frontier is instead the forward structural match already excluded.

If \(e=d\), any encoding input except the canonical message and least valid counter is the equal-code event. An exhausted address has no reference input. Otherwise the entire verified OTS component is canonical: tracing its forward suffix fixes its supplied frontier, and when its digit is seven the recovered endpoint itself is the supplied value. This zero-length case must be included when proving signature equality.

There are no unconstrained signature fields left: all 14 FTS secrets, all 140 FTS siblings, all three counters, all 126 chain values, and all 26 hypertree siblings have been accounted for. The path offsets in `Statement.lean` cover every entry. The randomizer is part of the final message-hash input. If a prior successful response selected that same input, fixed-width parsing fixes the same message and randomizer, oracle consistency fixes its index and leaf tuple, and the canonical component argument fixes the whole signature. It is then in the original signing log and cannot be a strong forgery. Hence the successful views used to cover a remaining forgery's target may exclude its own input. Failed responses contribute no disclosures.

It follows that, outside the original monitoring exceptions, an accepted strong forgery lies in

\[
E_{\rm OTS}\ \cup\ E_{\rm str}\ \cup\ \{C_{\rm full}\ge1\}
\ \cup\ \{\text{a true FTS guess and }C_{\rm near}\ge1\}
\ \cup\ \{\text{two distinct true FTS guesses}\}.
\]

For the last two alternatives, classify the 14 required coordinates by whether a successful response disclosed them. Exactly one undisclosed coordinate leaves a near certificate and a true guess, while at least two leave two distinct true guesses. Verification supplies any missing true-secret query. Coordinates are distinct by their tweaks even if their numerical secrets coincide. In the large-budget argument, absence of the first primitive match rules out every backward path and still-undisclosed true secret, reducing the decomposition to a full certificate alone. The remaining concrete proof must implement this trace argument and establish that the monitor remains active on each otherwise clean winning run.

## Large budgets: pay coverage inside the first-match bound

Let \(B\) be the first external primitive match, including verification: a guess of an undisclosed canonical child, a noncanonical output equal to its canonical parent, or a nonreference encoding equal to the reference word. Honest canonical reads are allowed.

The invariant to establish is a product of uniform distributions for the remaining hidden coordinates on their unexcluded sets. A miss at a hidden child removes the input candidate from one set. An output miss removes the returned value from a different set when the parent is hidden. For candidate \(z\), answer \(y\), child \(u\) and parent \(v\), the surviving mass has the factors

\[
\left(\prod_w\frac{\mathbf1_{x_w\in U_w}}{|U_w|}\right)
\mathbf1_{x_u\ne z}\,\frac1N\,\mathbf1_{x_v\ne y}.
\]

The coordinates \(u,v\) are distinct. Normalization gives exactly the updated product law, even if some numerical labels coincide. A signing disclosure retires a coordinate selected without inspecting its secret value. The graph and signer correspondence must show that other observable transitions preserve this invariant.

### Deriving the adaptive posterior from transcript masses

The native posterior and stopped-execution erasure are now proved in [AdaptiveHiddenLabels.lean](../SphincsSecurity/Proof/AdaptiveHiddenLabels.lean), including retention of visible memory on matched runs. The following paper induction explains their sampling identity. Applying it to SPHINCS still requires its concrete execution to have the causal transition rules specified here. An arbitrary auxiliary transition cannot be allowed to inspect an undisclosed label merely because its result has an innocent-looking type.

Condition on the public cut and reference family. Let \(V\) be the finite set of initially hidden coordinates, and let \(X\in[N]^V\) have its independent uniform prior. A retained history \(t\) contains the exposed cut, external inputs and full replies, observed message rows, disclosed coordinates and their values, original control stages and costs, and the fact that no primitive match has occurred. It excludes private prefix inputs, their intermediate values and private cache-hit flags. For each coordinate retain a candidate set \(U_v(t)\); a disclosure changes its set to the disclosed singleton.

The useful induction statement is the unnormalized joint identity

\[
\Pr[X=z,\ T=t,\ \text{alive}]
=\beta(t)N^{-|V|}\prod_{v\in V}\mathbf1_{z_v\in U_v(t)},
\]

where \(\beta(t)\ge0\) does not depend on \(z\). It holds initially with every candidate set equal to \([N]\). A surviving fresh noncanonical reply contributes its full-reply mass \(N^{-2}\), together with at most the two coordinate inequalities already displayed. A disclosure of value \(a\) contributes \(\mathbf1_{z_v=a}\). A public-target output test restricts the observed reply alone. A repeated external row checks only recorded data. Every other observable transition must have a kernel depending only on the retained history and fresh independent randomness; its probability then multiplies \(\beta\). These statements also cover adaptive selection of the next request, because that selection uses this same history.

Summing the identity over \(z\) and normalizing at any positive-probability live history gives

\[
\Pr[X=z\mid T=t,\ \text{alive}]
=\prod_{v\in V}\frac{\mathbf1_{z_v\in U_v(t)}}{|U_v(t)|}.
\]

Thus the posterior is a conclusion of the joint sampling law. In particular, numerical equality of labels at different coordinates does not impose an additional relation: the history contains only the displayed per-coordinate constraints. Disclosed singleton coordinates are omitted when asserting the lower bound on active candidate-set sizes.

For this signer, the causal condition has a concrete justification. Once the cut, reference counters and message trace are fixed, all honest structural values returned outside the private prefixes, every encoding success or exhaustion, all three layer invocations, and the hash count are determined without reading a hidden prefix value. Successful signatures disclose their selected FTS coordinates; the selection and the failure decision use the message trace and exposed graph. Their secret values cannot affect which coordinates are selected. Private honest rows may have been materialized in the original cache, but the external row table and the retained control trace do not report that fact. Establishing these assertions for the concrete response and cost projection is the required original-game bridge.

The sharper local hazard is actually at most \(1-(1-1/(N-r))(1-1/N)\): after an input miss the fresh output remains uniform on the entire output space. The square bound below deliberately weakens its second factor to simplify the potential. Sharpening it is unnecessary for the present split.

After \(r\) probe rounds, every active candidate set has size at least \(N-r\). Hence a next probe has hazard at most

\[
h_r=1-\left(\frac{N-r-1}{N-r}\right)^2.
\]

For \(k\) remaining original hash slots define

\[
F(r,k)=1-\left(\frac{N-r-k}{N-r}\right)^2,
\qquad r+k\le q\le N/2.
\]

The identities

\[
h_r+(1-h_r)F(r+1,k-1)=F(r,k),
\]

\[
F(r,k)-F(r,k-1)=\frac{2(N-r-k)+1}{(N-r)^2}\ge\frac1N
\]

pay a primitive probe or a message call within the same potential. Since \(F<1\), replacing the actual hazard by its upper bound is valid. Finite induction over the remaining hash budget permits adaptive scheduling, free sampling and early termination. It yields

\[
\Pr[B]+\frac{\mathbb E A_B}{N}\le2x-x^2,
\]

where \(A_B\) counts message calls until the first match or termination.

One must retain this message count on runs that hit \(B\), too. To make the induction explicit, pad a terminated execution with inert hash slots up to \(q\). After slot \(t\), let \(D_t\) be its message count before stopping, let \(B_t\) record whether a primitive match has happened, and let \(L_t\) say the monitored execution is still live. The potential with accumulated payment is

\[
M_t=\frac{D_t}{N}+\mathbf1_{B_t}+\mathbf1_{L_t}F(r_t,q-t).
\]

The two scalar transitions show \(\mathbb E[M_{t+1}\mid\mathcal G_t]\le M_t\). A primitive hit keeps all earlier payments and replaces the live potential by one. A message call increases \(D_t\) by one. Honest work and other unpaid calls only consume a slot. A free disclosure preserves the posterior and changes neither the payment nor the scalar parameters. Early termination discards nonnegative continuation potential. Consequently \(M_0=F(0,q)\) and \(M_q=\mathbf1_B+A_B/N\), proving the joint estimate. An equality concerning only surviving terminal outcomes would lose payments on matched runs and would not establish this inequality.

Coverage must be instantiated on this same law with an additional stop at \(B\), giving \(\mathbb E C_{\rm full}\le\mathbb E A_{\rm cov}/N+\delta x\) and \(A_{\rm cov}\le A_B\) pathwise. Backwards tracing of an accepting verifier must show that a strong forgery without \(B\) or an exception supplies a full certificate. These facts give the large-range contract directly. Bounding the primitive event by \(2x\) first would discard the saving needed here.

## Small budgets: sufficient bounds with simple constants

Use one stopped original law with disjoint counts \(Q,A_{\rm enc},A_{\rm str},A_{\rm msg}\), where \(Q\) counts external OTS prefix queries and the other counts cover nonreference encodings, remaining structural queries and message calls. Require

\[
Q+A_{\rm enc}+A_{\rm str}+A_{\rm msg}\le q
\]

pathwise. It is sufficient to establish

\[
\Pr[E_{\rm OTS}]\le\frac74\frac{\mathbb E(Q+A_{\rm enc})}{N},
\qquad
\Pr[E_{\rm str}]\le\frac{\mathbb E A_{\rm str}}N,
\]

\[
\mathbb E C_{\rm full}\le\frac{\mathbb E A_{\rm msg}}N+\delta x,
\]

and

\[
\Pr[\text{a true FTS guess and a near certificate}]
+\Pr[\text{two distinct true FTS guesses}]\le\frac18x.
\]

Together with the exhaustive forgery decomposition and the single original exception allowance, these imply \((7/4+1/8+\delta)x+\epsilon(q)\), the desired small-range contract. The shared allocation is essential before combining the linear contributions.

Here a full certificate covers the target's 14 FTS leaves using successful responses at other inputs; a near certificate covers 13 and specifies the omitted coordinate. The OTS event comprises a nonreference equal-code output or a completed backward witness for a different word. The structural event comprises a noncanonical output matching its canonical target outside the private OTS prefixes.

The more detailed proposed OTS coefficients in [the transfer argument](small-budget-transfer.md) are

\[
c_Q(x)=\frac{3/2+4x+2x^2}{1-x}+\frac{4x}{(1-x)^2}+\frac{82x}{1-x},
\qquad c_{\rm enc}(x)=1+\frac{3444x}{1-x}.
\]

Both are increasing on \([0,1)\). Exact rational evaluation at \(x_*\) gives \(c_Q(x_*)<7/4\) and \(c_{\rm enc}(x_*)<7/4\). Similarly,

\[
\frac{557x_*}{1-x_*}+\frac{x_*}{2(1-x_*)^2}<\frac18.
\]

Thus the existing proposed estimates are sufficient for these simpler contracts. This arithmetic verifies the closing allowance; it does not prove their applicability to the original law.

There is also room to round the correction constants upward. For \(0\le x<1\), the proposed coefficients satisfy

\[
c_Q(x)\le\frac{3/2+100x}{(1-x)^2},\qquad
c_{\rm enc}(x)\le1+\frac{4000x}{1-x},\qquad
\frac{557x^2}{1-x}+\frac{x^2}{2(1-x)^2}\le\frac{600x^2}{(1-x)^2}.
\]

At the split the first two upper bounds are respectively \(407568384/268337161<7/4\) and \(28381/16381<7/4\); the third, divided by \(x_*\), is \(29491200/268337161<1/8\). These are exact rational comparisons. Use this allowance to simplify proofs while preserving their leading coefficients and shared cost accounting. Replacing an allocated query count by the whole budget before summing is not covered by this allowance.

## The two small-budget probability arguments

For OTS, two distinct valid equal-sum digit vectors have positive total decrease. A decrease of one lowers one chain and raises one other, with at most \(42\cdot41\) possible neighboring words and at most \(41\) lowering a specified chain. A larger decrease requires a two-edge backward suffix in one chain or contacts in two chains, after excluding structural mergers above the reference frontiers. Charge completed witnesses, including preparation in either chronological order.

The real endpoint \(Y=H_{d-1}\circ\cdots\circ H_0(S)\) is not independent of the accessible prefix functions. After forgetting \(S\) and private prefix evaluations, its density against an independently uniform endpoint is the number \(W(H,Y)\) of starting preimages. For a causal partial transcript,

\[
w(T)=\mathbb E[W\mid T]=\mathbf1^TP_0\cdots P_{d-1}e_Y
\ge\prod_j(1-a_j/N)\ge1-Q_i(T)/N\ge1-x.
\]

The matrix \(P_j\) has a unit entry at the recorded answer of each queried input and a uniform row at each unqueried input. The number \(a_j\) counts distinct queried rows of that function, and \(Q_i=\sum_j a_j\). Independent completion of the remaining rows gives the equality; retaining only the uniform-row terms in the nonnegative matrix product gives the first inequality.

The complete-table density has a short direct proof. For any prior mass \(\mu(H)\), the projected real mass at \((H,y)\) is \(\mu(H)W(H,y)/N\), whereas the ideal mass is \(\mu(H)/N\). Any auxiliary kernel depending only on \((H,y)\) preserves this full-table density. For the partial-table formula the stronger causal condition is essential: the kernel may depend on \(y\) and already observed prefix rows, but may not inspect an unqueried prefix cell. Under the ideal law a fixed transcript then imposes exactly its recorded row equalities; adaptive choices impose no further restrictions. This is the observation rule to prove for the actual simulator. The displayed matrices can equivalently be written as finite averaging operators; no enumeration of an \(N\)-element table is part of the algorithm.

This converts each chain's allocated ideal cost to its real cost with factor at most \(1/(1-x)\). Transfer before summing over chains. The event, cost and stopping rule must all survive the projection. If the starting secret is retained, the density becomes \(N\mathbf1_{H(S)=Y}\), and this argument is invalid. An ideal endpoint may have no compatible starting secret, so cap every auxiliary execution explicitly at \(q\). Fixing independent auxiliary tables is permitted for the prefix likelihood calculation; fresh encoding probabilities need a history that has not exposed their unqueried rows.

The adaptive witness calculation must include the costs of preparation before a target is selected. For two-edge suffixes, the last-unqueried-edge expansion of \(w\) counts each older queried input at most once; the baseline charge is \(3Q_i/2\), with the stated quadratic and cubic corrections. For a new one-edge contact after a real transcript \(T\), the restart charge is \(a_i(T)+2Q_i^+\), where \(a_i(T)\) counts old prefix rows and \(Q_i^+\) counts future rows through the first contact. Transfer that charge to the real law before summing over uncontacted chains. Their charges sum to at most \(Q_{\rm past}+2Q_{\rm future}\le2q\). This handles both a second contacted chain and an encoding marker that precedes its contact. The opposite order uses at most 41 neighboring words per contacted chain. The detailed restart derivation is in [Section 8 of the audit](mathematical-audit.md#8-a-conditional-ots-restart-with-an-explicit-shared-charge).

### Auditing the allocated two-edge bound directly

The coefficient \(3/2\) has a concrete explanation. For independent uniform functions \(f,g\), a uniform secret \(S\), and a fixed candidate \(a\),

\[
\Pr[f(a)=f(S)]=1-(1-1/N)^2,
\qquad
\Pr[g(f(a))=g(f(S))]=1-(1-1/N)^3.
\]

To derive the first identity, split on \(S=a\); otherwise the two function cells are independent. For the second, split on \(f(a)=f(S)\); otherwise the two \(g\) cells are independent. Thus one edge has leading probability \(2/N\), whereas two queried edges have leading probability \(3/N\) for two calls. These are examples in the revealed-endpoint chain experiment. They explain the proposed coefficients without claiming an attack against the original signature game.

Here is a derivation that retains the adaptive allocation. Fix one chain of depth \(d\ge2\) in its causal independent-endpoint experiment \(I_i\), and stop at its first fully queried two-edge suffix to \(Y_i\), the base stop, or the budget cap. Let \(Q_i\) count its fresh prefix rows through that stop. For each level \(r\), let \(C_r\) count fully queried suffix paths from that level to \(Y_i\). Set \(C_d=1\). The last-unqueried-edge expansion gives

\[
w=C_0+\sum_{j=0}^{d-1}\alpha_jC_{j+1},
\qquad
\alpha_j=\frac{\mathbf1^TP_0\cdots P_{j-1}u_j}{N}\in[0,1],
\qquad
w\le1+\sum_{r<d}C_r.
\]

Before the first two-edge completion all \(C_r\) with \(r\le d-2\) vanish. Write \(k=C_{d-1}\). A fresh last-edge query at \(z\) can complete a witness only if a queried penultimate row already reaches \(z\). If it does, its ideal chance is \(1/N\), and its resulting likelihood is at most \(2+k+\sum_{r<d-1}m_r(z)\), where \(m_r(z)\) counts queried paths from level \(r\) to \(z\). A fresh penultimate query at \(a\) completes a witness with ideal chance \(k/N\), and its resulting likelihood is at most \(k+2+M(a)\), where \(M(a)\) counts queried paths from earlier levels to \(a\). A repeated row or an earlier-level query cannot be the first completion.

Let \(q_j\) be the stopped fresh-query count at level \(j\). Each older queried input contributes to \(m_r(z)\) at most once: its known forward path has one endpoint and each last-edge input has one first query. The number of productive last-edge queries is at most \(\min(q_{d-2},q_{d-1})\). Consequently the baseline likelihood numerators have the pathwise bound

\[
\sum_{j<d-1}q_j+2\min(q_{d-2},q_{d-1})
\le\frac32\sum_{j<d}q_j=\frac32Q_i.
\]

The same uniqueness argument gives \(\sum_aM(a)\le Q_i\le q\). Let \(K\) be the final number of last-edge replies equal to \(Y_i\), including unproductive ones. A fresh last-edge answer has conditional hit probability \(1/N\) in \(I_i\). Summing its indicator increments and the increments of \(K(K-1)\) gives

\[
\mathbb E_{I_i}K\le\frac{\mathbb E_{I_i}Q_i}{N},
\qquad
\mathbb E_{I_i}[K(K-1)]\le\frac{2q\,\mathbb E_{I_i}Q_i}{N^2}.
\]

For the second bound, the factorial increment at a last-edge trial is twice its previous hit count divided by \(N\) in conditional expectation, and the sum of those previous counts is pathwise at most \(qK\). This argument permits adaptive allocation and stopping; no independent random query count is assumed.

Across all last-edge and penultimate trials, their remaining \(k\) and \(k(k+2)\) numerators sum to at most \(qK(K+2)\). The earlier-path numerators sum to at most \(qK\). Applying the two moment bounds therefore bounds the nonbaseline contribution by

\[
\frac qN\mathbb E_{I_i}[K(K-1)+4K]
\le(4x+2x^2)\frac{\mathbb E_{I_i}Q_i}{N}.
\]

The first-success decomposition weights each ideal successful transition by its resulting \(w\). The preceding estimates establish

\[
\Pr_R[E_{2,i}]
\le(3/2+4x+2x^2)\frac{\mathbb E_{I_i}Q_i}{N}
\le\frac{3/2+4x+2x^2}{1-x}\frac{\mathbb E_RQ_i}{N}.
\]

The final step uses the stopped density lower bound, rather than equating the real and ideal endpoint laws. On the common real execution each chain's individual stopping rule only shortens its allocated count, so \(\sum_iQ_i\le Q\). Summing the displayed bounds introduces no number-of-chains factor. This proves the proposed two-edge estimate under the specified causal simulator correspondence; that concrete correspondence remains a required step for SPHINCS.

### FTS guesses and conditional coverage

For FTS, an active secret is uniform on its remaining candidates \(U\). A query at \(z\in U\) hits with probability \(1/|U|\). On a miss, remove \(z\) and return a uniform answer, allowing that answer to equal the public leaf hash. That alternative preimage remains distinct from guessing the true secret.

Force earlier eligible queries to miss and the eligible query at slot \(j\) to hit. If \(R_j\) is this conditional-kernel law, then for every nonnegative projected statistic \(Z\),

\[
\mathbb E_R[\mathbf1_{\{\text{first true hit at }j\}}Z]
=\mathbb E_{R_j}\left[p_j\prod_{t<j}(1-p_t)Z\right],
\qquad p_j\prod_{t<j}(1-p_t)\le\frac1{N-q}.
\]

Each modified branch has original support and preserves the original query budget. Prove that its fresh message kernel, finite signing loop and selected-view rules meet the coverage hypotheses, then attach that law's own proposal bridge. The near-certificate estimate in each \(R_j\) gives \(557x^2/(1-x)\) after summing over slots. The two-guess term is at most \(x^2/(2(1-x)^2)\). The original-law near estimate alone cannot justify this multiplication. Exceptions are paid once on the original execution, not once per forced law.

## The coverage interface that must be transported

The present certificate theorems quantify over adversaries in the original game. A forced-secret interpreter is not automatically another such adversary. Their use in a changed interpreter therefore needs a theorem derived from the local message and signing rules, rather than an application based only on similar type signatures.

Its admissible environment can have arbitrary current non-message state and arbitrary causal non-message transitions. Conditional on that state, unqueried message rows must still be independent uniform full replies. Each signing request runs the original finite randomizer loop. Conditional on a fresh selection, the selected index and leaf tuple are uniform before the later failure decision; initially cached input selection has the deficit-controlled per-input bound. Post-selection computation may suppress disclosure by returning `None`, and successful responses disclose only their selected view. Every completed invocation pays at least 1024 original hash calls, and every execution retains the original signing and hash limits. All stops use the current history; completed certificates are retained when a subsequent guard stops the monitor.

These are local assertions to establish, not an assumed global coverage inequality. The existing forecast and proposal arguments can then be transported from these assertions, with a separate record-first proposal construction for each law. A stop at a structural primitive match never inspects an unqueried message row. Likewise a forced FTS hit or miss uses only its current candidate set and queried input, not a future message answer. Those observations identify why the two required instantiations should satisfy the interface. The concrete records, stopping rules and cost identities still have to be checked. Conditioning globally on a future hit event would not satisfy the same argument.

## Completion gates

1. Use the established full-family reference conditioning and response/cost projection to instantiate the adaptive prefix-oracle interface with the concrete frontier execution. The all-address finite mass calculation, secret-erasure density and adaptive posterior completion law are now formalized. The interface must still reproduce the original responses, monitoring statistics and costs for every real frontier, and obey the required cap on independent-endpoint paths.
2. Write the deterministic accepting-verifier trace against the concrete byte layout. It must account for every signature field, canonical encoding exhaustion, failed signing disclosures and the exclusion of the forgery's own input. Without a listed witness, an earlier successful response at that input must force equality of the entire signature.
3. Establish the coverage interface just specified in both presentations: the graph law stopped at the first match, and each forced-FTS law. Use separate analytical histories where required, while retaining the same original statistics in the final bounds. Reuse the existing terminal moments and exception estimates.
4. Complete the original-game large-range inequality. This is the first security milestone that directly reaches the 127-bit slope on a nontrivial interval.
5. Complete the projected OTS likelihood and shared witness charging, and the forced-FTS comparison, to obtain the small-range inequality. Combine the intervals and probability at most one.

A scalar bound, a supported-execution correspondence, or a theorem assuming the global cryptographic inequality is an intermediate result. Completion means deriving both interval bounds for the unchanged original SUF experiment from its existing whole-experiment query-bound premise.

For the next milestone, prioritize the large-range original-game inequality in gate 4. Its dependencies are the canonical hidden-label invariant, the backwards verifier classification and coverage on that same law stopped at the first match. It does not depend on the independent-endpoint OTS comparison or forced-FTS coverage. The small-range chain and forced-secret arguments can then be assessed against a fixed, already useful security endpoint. Before translating each argument into Lean, its paper statement should specify the retained history, local transition law, stopping rule, original allocated cost and exact original-game conclusion.
