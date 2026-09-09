# Mathematical audit of the route to 127 bits

This is a paper-only review of branch `sphincs-fv` at `088bb5d9`. No Lean code is added. The original public theorem is still 126 bits. The recommendation is to retain the two-range proof, with the explicit sampling argument, shared costs and completion gates below. The arithmetic closes with room to weaken several constants. Establishing the adaptive probability lemmas for the concrete experiment remains necessary; this review does not claim that the security theorem is proved.

The current branch has progressed beyond the fixed-function correspondence described in some earlier notes. Its frontier game has the original SUF probability and inherits the original hash budget, using a finite uniform table sampled before the secrets. That is a useful foundation. An independent-label presentation of the canonical graph, its conditional hidden-label law, and the small-budget probability transfers are further obligations. The finite table may need enlargement to include canonical rows absent from the original computation's footprint; the existing correspondence permits such enlargement.

## 1. Fix the target and the source of difficulty

Write

\[
N=2^{128},\quad x=q/N,\quad x_*=3/2^{14},\quad
\delta=11/2^{16},\quad
\epsilon(q)=q/2^{222}+q/2^{170}+2^{-700}.
\]

The target is \(\Pr[\mathrm{SUF}]\le 2x\) for the unchanged game, including every original hash call and the complete original signing log. For \(q\ge1\),

\[
e:=\epsilon(q)/x\le2^{-94}+2^{-42}+2^{-572}<2^{-16}.
\]

The existing certificate estimates are \(\mathbb E C_{\rm full}\le\mathbb E A_{\rm msg}/N+\delta x\) and \(\mathbb E C_{\rm near}\le557x\). The near count already sums over all 14 choices of omitted leaf. Their present formal instantiation is the original execution. A modified structural interpreter must establish the message and signing kernel conditions before using these estimates.

Simply adding a \(2x\) primitive bound and a coverage bound fails. Nor can the excess coverage term be dismissed as an artifact of a loose variance calculation. Its terminal price is \(R=2^{-48}\sum_i Z_i^{14}\). A single occupancy \(Z_i=11\) contributes \(11^{14}/2^{48}>1\); occupancy 12 contributes more than 4. These outcomes have positive probability in the terminal word. Thus a pathwise claim \(R\le1\) is false. This observation does not refute security; it explains why this proof needs an additional source of slack.

For larger budgets the source is a quadratic saving in the first-match bound. For smaller budgets it is the work needed to turn a primitive match into a completed forgery witness. For independent random functions \(f,g\), a uniform secret \(S\), and a fixed candidate \(a\),

\[
\Pr[f(a)=f(S)]=2/N-1/N^2,
\]

\[
\Pr[g(f(a))=g(f(S))]=3/N-3/N^2+1/N^3.
\]

These follow by separating equality of the inputs from a collision at each next function. They explain the leading two-query coefficient \(3/2\). They do not justify treating an adaptive collection of queries as disjoint two-query attempts.

## 2. The exact graph sampling argument

Use one canonical node per distinct valid serialized structural tweak. The distinction must be on actual bytes, including field ranges. Every canonical row belongs to a different domain; repeated honest reads of that row are allowed. Its payload is determined by earlier graph nodes. The hidden parts below the chosen cut are unary OTS prefixes and unary FTS secret-to-leaf edges. All multi-input structural nodes have their children above the cut.

Here is a finite probability-mass proof of the sampling change. Let \(K_v\) be the number of retained input rows in domain \(v\), including every possible canonical payload, and let \(B=N^2\) be the full 256-bit output alphabet size. Sample the original independent secret leaves. At each node in topological order, sample an independent full output \(Z_v\), fix the domain's canonical row to it, and sample all remaining rows independently. For any fixed secret assignment and full collection of tables, exactly one sequence of \(Z_v\)'s is compatible: the ordinary graph evaluation. Its table-generation probability is

\[
\prod_v B^{-1}B^{-(K_v-1)}=B^{-\sum_v K_v},
\]

which is exactly the uniform-table probability, independent of the secrets. Other finite rows contribute identical factors on both sides. Thus the joint distribution, including secrets, full replies and graph values, is unchanged after erasing the advice. The analytical graph generation is not charged as additional original computation. Original reads keep their original costs.

This proof samples both halves of every hash reply. High halves are returned when queried; presampling them does not authorize revealing the high bits of an unqueried hidden canonical row. No distinctness of numerical node values is imposed, and no graph-size birthday term appears. The finite domain sets can cover the canonical graph and the syntactically possible original queries; no uniform function on arbitrary infinite byte strings is needed.

Reference encoding is another exact sampling change. Let \(\mathcal C\) be the valid words, \(v=|\mathcal C|/N\), and \(T=2^{32}\). Conditional on the non-encoding graph, the canonical message at each address is fixed and its counter rows are independent. For \(d\in\mathcal C\),

\[
\Pr[J=j,D=d]=(1-v)^j/N\quad(0\le j<T),
\]

\[
\Pr[J=\mathrm{none},D=d]=(1-v)^T/|\mathcal C|.
\]

The second formula adds an independent valid dummy on exhaustion. These probabilities do not depend on the canonical message, so the pairs \((J,D)\) are independent of the non-encoding graph. Conditional on a pair, preceding canonical-message rows are independently invalid, the reference row encodes \(D\), and unrestricted rows are uniform. Multiplying these conditional masses recovers the original table law, also on exhaustion. High halves remain independent uniforms.

The existing frontier replacement must then be used with this law. Its response, failure and cost depend on the cut, reference counters, message trace and disclosed FTS values. A private prefix's starting secret, internal inputs and cache-hit flags are absent from the analytical observation. A failed invocation still pays for all three layer computations and discloses no returned FTS secrets. These are necessary properties of the retained history, not conveniences that may be changed during the probability proof.

## 3. Large budgets: one local invariant and one potential

Let \(B_0\) be the first external primitive match, including verification. It includes guessing an undisclosed canonical unary input, a noncanonical output matching its canonical target, and a nonreference encoding matching its reference word. Honest canonical reads are allowed. The original adversary receives no match flag.

Before \(B_0\), retain the invariant that the hidden coordinates are independent uniforms on their surviving sets \(U_w\). For a unary query with hidden child \(u\), distinct hidden parent \(v\), candidate \(z\) and fresh low reply \(y\), the surviving mass is

\[
\left(\prod_w\frac{\mathbf1_{X_w\in U_w}}{|U_w|}\right)
\mathbf1_{X_u\ne z}\,\frac1N\,\mathbf1_{X_v\ne y}.
\]

After conditioning on the reply and survival, this is the product law with \(z\) removed from \(U_u\) and \(y\) removed from \(U_v\). A public parent only restricts the reply. A selected FTS disclosure reveals and retires one coordinate; its choice must depend only on the retained history, not that coordinate's hidden value. Repeated external rows already carry their exclusions. This accounts for equality of numerical labels at different graph positions without identifying those positions.

After \(r\) probe slots every surviving set has size at least \(N-r\). The next hazard is at most

\[
h_r=1-\left(\frac{N-r-1}{N-r}\right)^2.
\]

The input-hit probability is at most \(1/(N-r)\). Conditional on an input miss, the fresh noncanonical low reply is uniform and its output-match probability is \(1/N\le1/(N-r)\). This proves the hazard bound directly from the local kernels.

For \(k\) remaining original hash slots use

\[
F(r,k)=1-\left(\frac{N-r-k}{N-r}\right)^2,
\qquad r+k\le q\le N/2.
\]

Then

\[
h_r+(1-h_r)F(r+1,k-1)=F(r,k),
\]

\[
F(r,k)-F(r,k-1)=\frac{2(N-r-k)+1}{(N-r)^2}\ge1/N.
\]

The first identity pays a primitive probe; the second pays a message call. Other honest hash work spends slots without reward. Since \(F<1\), upper-bounding the hazard is valid. Finite induction, with stopping at the first match, gives

\[
\Pr[B_0]+\mathbb E A_{B_0}/N\le2x-x^2.
\]

Coverage needs its own additional stop at \(B_0\). Its counted message calls are pathwise at most \(A_{B_0}\). The coverage proof may retain more non-message state than the hidden-label proof; neither history may reveal future message replies. Once the deterministic implication below and this coverage instantiation are established,

\[
\Pr[\mathrm{SUF}]\le2x-x^2+\delta x+\epsilon(q)\le2x
\]

for \(x\ge x_*\), because \(x_*-\delta=2^{-16}>e\).

## 4. Write the exhaustive verifier argument before building more probability machinery

Trace accepted verification backwards from the canonical public root. Absent a noncanonical output match, each computed structural parent forces its entire fixed-width child payload. This fixes authentication siblings and OTS endpoints. Above an OTS reference frontier, a noncanonical path cannot merge into the canonical path without such a match.

Let \(d\) be the reference digits and \(e\) the verified digits. If \(e\ne d\), equal digit sums imply

\[
b=\sum_j\max(d_j-e_j,0)\ge1.
\]

If \(b=1\), one chain is lowered and another raised. There are at most \(42\cdot41=1722\) such words and at most 41 lowering a specified chain. Acceptance supplies both that word's encoding query and a one-edge contact at the lowered frontier. If \(b\ge2\), it supplies a complete two-edge suffix in one chain or contacts in two distinct chains. Verification's own queries are part of these witnesses and consume budget. This argument permits paths through alternative preimages below the frontier.

If \(e=d\), a different encoding input is an equal-code event. Otherwise its counter and message are the canonical reference. Exhaustion has no reference input and cannot give acceptance without an encoding event. Repeat through all three layers to fix the FTS key. Without a structural output match, each supplied FTS secret is the true canonical secret. It was either disclosed by a successful signing response or guessed while still undisclosed.

For the large-budget argument, \(B_0\) excludes every backward step and every still-undisclosed true secret. Thus an otherwise clean winning run yields a full certificate. For the small-budget argument, excluding OTS witnesses and structural output matches leaves exactly three possibilities: a full certificate; one true FTS guess and a near certificate; or two distinct true FTS guesses.

This must be a strong-forgery argument. Fix every counter, chain value, FTS path and hypertree path field, including zero-length chain walks. If a successful signing response selected the forgery's own message/randomizer input, consistency gives the same selected digest, and the canonical fields give exactly that earlier signature. Strong novelty excludes it. Therefore coverage sources may exclude the target's own input. Failed signing responses contribute no disclosed FTS leaves.

## 5. Small budgets: sufficient estimates with simpler constants

On one monitored original execution, let \(Q\) count external OTS prefix rows, \(A_{\rm enc}\) fresh nonreference encoding rows, \(A_{\rm str}\) other fresh structural rows, and \(A_{\rm msg}\) message calls. Their serialized domains and the prefix/forward split give

\[
Q+A_{\rm enc}+A_{\rm str}+A_{\rm msg}\le q
\]

pathwise. Uncounted honest calls and repetitions provide slack. The small-budget monitor continues after primitive matches so it can detect their completion into witnesses.

The detailed [OTS transfer argument](small-budget-transfer.md) aims for

\[
c_Q(x)=\frac{3/2+86x+2x^2}{1-x}+\frac{4x}{(1-x)^2},
\qquad c_{\rm enc}(x)=1+\frac{3444x}{1-x}.
\]

It is sufficient to prove the following weaker bounds, which have simpler correction constants:

\[
\Pr[E_{\rm OTS}]
\le\frac{3/2+100x}{(1-x)^2}\frac{\mathbb E Q}{N}
+\left(1+\frac{4000x}{1-x}\right)\frac{\mathbb E A_{\rm enc}}N,
\]

\[
\Pr[\text{true FTS guess and near certificate}]
+\Pr[\text{two distinct true FTS guesses}]
\le\frac{600x^2}{(1-x)^2}.
\]

Indeed, the numerator of \(c_Q\) over \((1-x)^2\) is \(3/2+(177/2)x-84x^2-2x^3\le3/2+100x\). Also \(3444<4000\), and

\[
\frac{557x^2}{1-x}+\frac{x^2}{2(1-x)^2}
\le\frac{600x^2}{(1-x)^2}.
\]

All three coefficients increase on \([0,1)\). At \(x=x_*\), exact rational comparison gives

\[
\frac{3/2+100x_*}{(1-x_*)^2}<7/4,\qquad
1+\frac{4000x_*}{1-x_*}<7/4,\qquad
\frac{600x_*}{(1-x_*)^2}<1/8.
\]

Structural output matches cost \(\mathbb E A_{\rm str}/N\): condition on the canonical graph and keep noncanonical rows unqueried. Each such fresh reply matches its domain's canonical low output with probability \(1/N\). Canonical true-secret queries are handled separately. Coverage costs \(\mathbb E A_{\rm msg}/N+\delta x\). Applying the shared allocation before replacing any count by \(q\) gives

\[
\Pr[\mathrm{SUF}]
\le(7/4+1/8+\delta)x+\epsilon(q)
<\frac{30723}{16384}x<2x.
\]

Thus there is no need to formalize the sharper coefficients if the weaker estimates are easier. For the original detailed coefficients, every split in \([3/16384,3/13779]\) satisfies both closing requirements; the upper endpoint makes \(c_{\rm enc}=7/4\). This interval concerns the detailed coefficients, not the coarser 4,000 bound. The chosen split is not a numerically isolated point.

## 6. What must establish those small-budget estimates

The OTS argument compares one chain at a time with an independently uniform endpoint, while preserving the allocation to that chain. Forget its starting secret and private prefix evaluations before comparing laws. With full prefix tables \(H\), the real projected density is the number \(W(H,Y)\) of starting preimages of the endpoint. Retaining the starting secret would instead give \(N\mathbf1_{H(S)=Y}\), which cannot be substituted for \(W\).

At an adaptive transcript, let \(P_j\) have the recorded answer in each queried row and a uniform distribution in each unqueried row. If \(a_j\) counts queried rows at step \(j\), then

\[
w(T)=\mathbb E[W\mid T]=\mathbf1^TP_0\cdots P_{d-1}e_Y
\ge\prod_j(1-a_j/N)\ge1-Q_i(T)/N\ge1-x.
\]

The equality follows by independently completing the unqueried rows. The first inequality retains only their nonnegative uniform-row terms. This converts each nonnegative allocated ideal cost to its real cost with factor \(1/(1-x)\). Roots and canonical messages must be recomputed from the idealized endpoint; the simulator must not inspect an unqueried prefix cell through hidden honest work. Explicitly cap auxiliary runs at \(q\), because an independent endpoint may have no preimage in its completed tables.

For the completed two-edge event, expand the likelihood by the last unqueried transition. Before first completion only one-edge suffixes to the endpoint can already exist. Each old queried path contributes to at most one productive last-edge input. The baseline numerator is bounded by

\[
\sum_{j<d-1}q_j+2\min(q_{d-2},q_{d-1})\le\tfrac32\sum_jq_j.
\]

Adaptive moment bounds on previously found last-edge preimages pay the remaining terms. Transfer this allocated cost before summing over addresses. A separate conditional restart on uncontacted chains pays for two distinct contacts. For unit neighbors, charge both chronological orders: inversion before encoding, and encoding before inversion. Fresh encoding probabilities must be proved in a history hiding unqueried encoding rows; fixing all auxiliary tables for the chain likelihood does not make those probabilities conditionally uniform in that richer history. These steps are the substantive adaptive OTS obligation.

For FTS, retain an undisclosed secret as uniform on its candidate set \(U\). An eligible candidate hits with probability \(p=1/|U|\); a miss removes it and samples an ordinary noncanonical reply. That reply may still equal the public leaf hash. A true-secret hit and an alternative preimage are different events.

Define \(R_j\) by forcing earlier eligible hit/miss choices to use their miss kernels, forcing an eligible hit at original slot \(j\), and using the ordinary kernels afterwards. Give ineligible or unreached slot \(j\) weight zero. This is a sequentially modified process, not the global conditional law given that the first hit is at \(j\). The latter could bias earlier message replies. For nonnegative terminal \(Z\), multiplying the local branch probabilities gives

\[
\mathbb E_R[\mathbf1_{\{\mathrm{first\ hit}=j\}}Z]
=\mathbb E_{R_j}\left[p_j\prod_{t<j}(1-p_t)Z\right],
\qquad p_j\prod_{t<j}(1-p_t)\le1/(N-q).
\]

Every positive-weight forced path must complete to an original path with the same observed replies and costs. Its remaining secret sets are nonempty and its canonical rows can be completed without changing observed rows. This is the required budget transfer. Each forced choice uses only current non-message state, so unqueried message cells retain their fresh uniform law. The finite digest loop, post-selection view and minimum invocation cost remain original.

Apply the coverage kernel theorem separately in each \(R_j\), constructing its own proposal bridge from its own record kernel. Then \(\mathbb E_{R_j} C_{\rm near}\le557x\), and summing the weighted identity gives \(557x^2/(1-x)\). The adaptive union over ordered hash-slot pairs gives the two-distinct-hit bound \(x^2/[2(1-x)^2]\). The certificate can occur before or after the guess. Multiplying two unconditional event probabilities would not establish this result. Original exceptions are paid once, not once per forced process.

## 7. Completion order and acceptance criteria

1. Finish the graph sampling correspondence and the deterministic verifier partition together. The first identifies the actual probability space; the second fixes the events that probability estimates must bound. Preserve 256-bit replies, finite failures, every signature field, actual costs and strong novelty.
2. Establish coverage from its local message/signing kernels. Instantiate those kernels for the graph process stopped at its first primitive match and for the supported forced-FTS processes. Reuse the existing certificate moments and terminal-word machinery. No new coverage assumption may appear in the public theorem.
3. Complete the hidden-label transition invariant and the two-transition potential. Combine them with the stopped coverage and verifier partition to obtain an original-game theorem for \(3\cdot2^{114}\le q<2^{127}\). This is the first direct 127-bit interval milestone.
4. Complete the allocated OTS likelihood and witness argument, plus the forced-FTS comparison, aiming only for the coarser sufficient bounds in Section 5. This must handle adaptive preparation in either order and expose one disjoint cost allocation on the original stopped law.
5. Combine the small interval, the large interval and probability at most one for \(q\ge2^{127}\). Audit the final theorem against the unchanged original game and its original hash-bound premise.

The common sampling and posterior construction has a direct local proof strategy. The OTS allocation and the forced-FTS coverage application are the highest-risk remaining steps because they compare different analytical laws. The next useful result must discharge one of those concrete correspondences or prove an original-game interval. Another endpoint that assumes its own global cryptographic inequality would leave the main question open.
