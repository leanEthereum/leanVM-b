# A minimal mathematical contract for the 127-bit proof

This paper review concerns the unchanged game at `69b56362`. It adds no Lean code. The public statement currently stops at 126 bits. The purpose here is to specify sufficient intermediate results, explain why their combination works, and identify which correspondences must be proved before calling this a security proof. The detailed arguments and their current status are collected in [the roadmap](paper-first-roadmap.md).

## Conclusion of the review

The two-range route has sufficient numerical room. Its completion depends on concrete adaptive probability arguments, rather than sharper numerical estimates. I recommend retaining the current split and simplifying the small-range target to the dyadic bounds below. This leaves room to weaken intermediate constants without changing the public security claim.

The main mathematical risks are the exact random-oracle presentation with hidden private computations, the transfer of allocated OTS work through a change of measure, and coverage in the forced-FTS laws. A pointwise equality of signer outputs for fixed hash answers is useful evidence for the first correspondence, but it does not by itself prove equality of random-oracle distributions or either of the other two correspondences.

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

For each OTS address, the canonical message is fixed by this non-encoding graph. The original finite encoding search therefore has an exact conditional-table presentation: its earlier canonical-message rows are invalid, its first valid row contains the reference word, and the remaining rows are uniform. Preserve exhaustion with its original probability. An independent valid dummy word on exhaustion is analytical data only. The 256-bit replies retain independently sampled high halves as well as their low 128-bit graph values.

Expose each OTS chain at its reference digit and above. Honest signing uses a private prefix only to reach this frontier or the full endpoint. Replace those private evaluations by their supplied result and the original number of cost markers. Reconstruct all roots, layer messages and authentication data consistently. Preserve the finite digest loop, every encoding search, all three layer computations even when a layer fails, and the selected FTS view when a later failure returns `None`.

The probability correspondence should be proved by equality of finite transition kernels, extending the externally observed row table one query at a time. Each finite execution observes finitely many residual rows, so this argument does not require first sampling a uniform function on the infinite type of arbitrary byte strings. It must preserve full external replies, original responses, the message trace and original costs. Equality for each compatible fixed function is only the deterministic part of this argument.

Classify external inputs by their bytes. An externally new row is new to the external history even if honest signing evaluated it privately. Neither hidden private inputs nor private cache-hit flags may enter the hidden-label history. Address separation limits a query to its own canonical target, including when its candidate value equals a label in another domain.

## Large budgets: pay coverage inside the first-match bound

Let \(B\) be the first external primitive match, including verification: a guess of an undisclosed canonical child, a noncanonical output equal to its canonical parent, or a nonreference encoding equal to the reference word. Honest canonical reads are allowed.

The invariant to establish is a product of uniform distributions for the remaining hidden coordinates on their unexcluded sets. A miss at a hidden child removes the input candidate from one set. An output miss removes the returned value from a different set when the parent is hidden. For candidate \(z\), answer \(y\), child \(u\) and parent \(v\), the surviving mass has the factors

\[
\left(\prod_w\frac{\mathbf1_{x_w\in U_w}}{|U_w|}\right)
\mathbf1_{x_u\ne z}\,\frac1N\,\mathbf1_{x_v\ne y}.
\]

The coordinates \(u,v\) are distinct. Normalization gives exactly the updated product law, even if some numerical labels coincide. A signing disclosure retires a coordinate selected without inspecting its secret value. The graph and signer correspondence must show that other observable transitions preserve this invariant.

After \(r\) probe rounds, every candidate set has size at least \(N-r\). Hence a next probe has hazard at most

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

## The two small-budget probability arguments

For OTS, two distinct valid equal-sum digit vectors have positive total decrease. A decrease of one lowers one chain and raises one other, with at most \(42\cdot41\) possible neighboring words and at most \(41\) lowering a specified chain. A larger decrease requires a two-edge backward suffix in one chain or contacts in two chains, after excluding structural mergers above the reference frontiers. Charge completed witnesses, including preparation in either chronological order.

The real endpoint \(Y=H_{d-1}\circ\cdots\circ H_0(S)\) is not independent of the accessible prefix functions. After forgetting \(S\) and private prefix evaluations, its density against an independently uniform endpoint is the number \(W(H,Y)\) of starting preimages. For a causal partial transcript,

\[
w(T)=\mathbb E[W\mid T]=\mathbf1^TP_0\cdots P_{d-1}e_Y
\ge\prod_j(1-a_j/N)\ge1-Q_i(T)/N\ge1-x.
\]

The matrix \(P_j\) has a unit entry at the recorded answer of each queried input and a uniform row at each unqueried input. The number \(a_j\) counts distinct queried rows of that function, and \(Q_i=\sum_j a_j\). Independent completion of the remaining rows gives the equality; retaining only the uniform-row terms in the nonnegative matrix product gives the first inequality.

This converts each chain's allocated ideal cost to its real cost with factor at most \(1/(1-x)\). Transfer before summing over chains. The event, cost and stopping rule must all survive the projection. If the starting secret is retained, the density becomes \(N\mathbf1_{H(S)=Y}\), and this argument is invalid. An ideal endpoint may have no compatible starting secret, so cap every auxiliary execution explicitly at \(q\). Fixing independent auxiliary tables is permitted for the prefix likelihood calculation; fresh encoding probabilities need a history that has not exposed their unqueried rows.

For FTS, an active secret is uniform on its remaining candidates \(U\). A query at \(z\in U\) hits with probability \(1/|U|\). On a miss, remove \(z\) and return a uniform answer, allowing that answer to equal the public leaf hash. That alternative preimage remains distinct from guessing the true secret.

Force earlier eligible queries to miss and the eligible query at slot \(j\) to hit. If \(R_j\) is this conditional-kernel law, then for every nonnegative projected statistic \(Z\),

\[
\mathbb E_R[\mathbf1_{\{\text{first true hit at }j\}}Z]
=\mathbb E_{R_j}\left[p_j\prod_{t<j}(1-p_t)Z\right],
\qquad p_j\prod_{t<j}(1-p_t)\le\frac1{N-q}.
\]

Each modified branch has original support and preserves the original query budget. Prove that its fresh message kernel, finite signing loop and selected-view rules meet the coverage hypotheses, then attach that law's own proposal bridge. The near-certificate estimate in each \(R_j\) gives \(557x^2/(1-x)\) after summing over slots. The two-guess term is at most \(x^2/(2(1-x)^2)\). The original-law near estimate alone cannot justify this multiplication. Exceptions are paid once on the original execution, not once per forced law.

## Completion gates

1. Establish the exact random-oracle graph presentation and response/cost projection. The fixed-answer signer correspondence is a component of this gate, not the entire gate.
2. Write the deterministic accepting-verifier trace against the concrete byte layout. It must account for every signature field, canonical encoding exhaustion, failed signing disclosures and the exclusion of the forgery's own input. Without a listed witness, an earlier successful response at that input must force equality of the entire signature.
3. Establish coverage from its local transition rules in both presentations: the graph law stopped at the first match, and each forced-FTS law. Use separate analytical histories where required, while retaining the same original statistics in the final bounds.
4. Complete the original-game large-range inequality. This is the first security milestone that directly reaches the 127-bit slope on a nontrivial interval.
5. Complete the projected OTS likelihood and shared witness charging, and the forced-FTS comparison, to obtain the small-range inequality. Combine the intervals and probability at most one.

A scalar bound, a supported-execution correspondence, or a theorem assuming the global cryptographic inequality is an intermediate result. Completion means deriving both interval bounds for the unchanged original SUF experiment from its existing whole-experiment query-bound premise.
