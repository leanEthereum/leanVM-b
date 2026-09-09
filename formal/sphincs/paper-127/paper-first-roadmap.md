# Paper-first roadmap for 127-bit strong unforgeability

This review concerns the unchanged scheme in `Statement.lean`, at `6b7f4d5f`. It adds no Lean code. The current public endpoint is 126 bits. The recommendation is to pursue the two-range argument below. Its closing inequalities work; its security conclusion still requires the concrete probability and execution correspondences specified here. Earlier notes contain superseded constants. This roadmap uses the unit-payment bounds throughout.

## The mathematical target

Put N=2^128 and x=q/N. We need Pr[SUF win]<=2x for every admitted adversary. The budget counts every original hash call, including repeated calls, key generation, failed signing, successful signing and final verification. The cap remains 2^24 signing requests, and novelty is tested against the complete original signing log. At q>=N/2, probability at most one suffices.

Fix the following constants, already sufficient for the closing argument:

    x_* = 3/2^14,       q_* = 3*2^114,
    delta = 11/65536,
    epsilon(q) = q/2^222 + q/2^170 + 2^-700.

For q>=1, epsilon(q)/x <= 2^-94+2^-42+2^-572 < 2^-16. The error allowance is paid once for the original execution.

The existing original-game certificate results are useful inputs. A full certificate means that successful signing responses at other inputs cover all 14 leaves required by a cached target. A near certificate omits one specified leaf; the near count sums over all 14 omissions. Their current bounds, in one shared original-law monitor, are

    E[C_full] <= E[A_message]/N + delta*x,
    E[C_near] <= 557*x.

These are theorems in [CertificateFamilyCoverage.lean](../SphincsSecurity/Proof/CertificateFamilyCoverage.lean). They do not automatically apply after changing how structural oracle answers are sampled. Establishing their applicability to the particular alternative presentations below is part of the plan.

## Why two ranges

An upper bound of 2x on the first primitive match leaves no room for the coverage error. For larger x, retain the quadratic saving from conditioning on all earlier misses. For smaller x, bound completed forgery witnesses, whose preparation has an additional cost. This separates two different mathematical sources of slack.

The small-range distinction is necessary for this strategy. For independent random functions f,g and a uniform secret S, a fixed candidate a satisfies

    Pr[f(a)=f(S)] = 2/N - 1/N^2,
    Pr[g(f(a))=g(f(S))] = 3/N - 3/N^2 + 1/N^3.

A last-edge match can therefore have leading cost 2/N, while a complete two-edge attempt has leading cost 3/(2N) per call. These identities explain the intended improvement; the adaptive, shared-budget lemma must still justify it for arbitrary querying order and merged paths.

## First obligation: an exact presentation of the signer

Construct the finite canonical hash graph with a separate domain for each valid serialized tweak. Sample independent canonical node labels in topological order and program each domain at its one canonical child payload. Leave other rows uniform. Distinct node labels may coincide; there is no global distinctness condition or birthday loss.

For each OTS address, its canonical message is determined by the non-encoding graph. Sample its first valid encoding counter J and valid digit vector D from their exact finite-search distribution, including exhaustion. Conditional encoding rows before J are invalid, the reference row encodes D, and unrestricted rows remain uniform. An independent dummy D on exhaustion is analysis data only. The digits of D need not be independent.

The retained public cut contains each OTS chain value at its reference digit and all values above it, plus the FTS leaf hashes and the higher structural graph. Private chain prefixes are accessed by the honest algorithms only to compute those reference values or full chain endpoints. They can be replaced by supplied values and the exact original number of cost markers. This requires preserving the message trace and every response, including `None`. All three `signLayer` computations run before the final failure decision. A failed request can have computed private values without disclosing them.

This presentation must handle actual byte inputs and externally fresh rows. A row previously evaluated only inside signing can still be an external secret guess. The private cache and its hit flags are therefore absent from the hidden-label history. The [reference-frontier argument](reference-frontier-transfer.md) gives the paper response and cost correspondence and the exact cost formulas. This is the common foundation for the following bounds.

## Large range: a joint primitive and message inequality

Let B be the first external primitive match, including final verification. An input match against an undisclosed canonical child, or a noncanonical output matching its canonical parent, is such a match. Allowed honest canonical reads are not. Include nonreference encodings equal to their reference word.

Before B, the remaining hidden labels must have a product of uniform distributions on their unexcluded candidate sets. After r probe rounds, every set has at least N-r elements. A query has at most one hidden-input test and one fresh-output test. When both tested labels are hidden, they belong to distinct coordinates. Thus its conditional hazard is at most

    h_r = 1 - ((N-r-1)/(N-r))^2.

For k remaining hash slots, use

    F(r,k) = 1 - ((N-r-k)/(N-r))^2,
    r+k <= q <= N/2.

The two transition inequalities are elementary:

    h_r + (1-h_r)*F(r+1,k-1) = F(r,k),
    F(r,k)-F(r,k-1) = (2*(N-r-k)+1)/(N-r)^2 >= 1/N.

The first pays a primitive match. The second pays each message call. Give other non-probe hash slots no reward. Free transitions and selected FTS disclosures preserve the posterior; early termination discards nonnegative remaining potential. Induction handles an adaptive query schedule and gives

    Pr[B] + E[A_B]/N <= 2x-x^2,

where A_B counts message calls until B or termination.

Run coverage on the same execution, with an additional stop at B. Its message count is pathwise at most A_B. Trace accepting verification backwards from the public root: without B, every recovered structural value is canonical. Equal digit sums force the reference OTS word, and the encoding input fixes its counter and message. Repeat through all three layers to the FTS leaves. Every required secret must have been disclosed by a successful response. If a response used the forgery's own input, all signature fields equal that response, contradicting strong novelty. Consequently a clean strong forgery without B supplies a full certificate.

Once this correspondence and the coverage application are established,

    Pr[SUF win] <= 2x-x^2+delta*x+epsilon(q) <= 2x

for x>=x_*. The margin follows from x_*-delta=2^-16. This should be the first original-game security interval to complete.

## Small range: completed witnesses with one shared budget

Partition counted calls into Q for external OTS prefix queries, A_encoding for fresh nonreference encoding queries, A_structure for other structural queries, and A_message for message calls. They must all be statistics of the same stopped original execution, with

    Q+A_encoding+A_structure+A_message <= q

pathwise. The small-range monitor continues after a first primitive match, because later work can complete a witness or its coverage.

For two distinct valid digit vectors d,e, define b=sum_j max(d_j-e_j,0). Equal sums imply b>=1. If b=1, e lowers one digit and raises another, giving at most 42*41=1722 neighbors, and at most 41 lowering a specified chain. If b>=2, a backward witness contains a two-edge suffix in one chain or contacts in two distinct chains. Structural mergers above the reference cut are counted separately.

The required adaptive OTS estimate is

    Pr[E_OTS] <= c_Q(x)*E[Q]/N + c_encoding(x)*E[A_encoding]/N,
    c_Q(x) = ((3/2)+4x+2x^2)/(1-x) + 4x/(1-x)^2 + 82x/(1-x),
    c_encoding(x) = 1 + 3444x/(1-x).

The [allocated chain argument](small-budget-transfer.md) supplies its paper derivation. Its crucial transfer is precise: forget a chain's starting secret and private prefix evaluations. For an independently uniform endpoint, the real projected law has density W, the number of starting preimages of that endpoint. After an adaptive observed transcript T,

    w(T) = E[W | T] = 1^T P_0 ... P_(d-1) e_Y,
    P_j = K_j + u_j*1^T/N,
    w(T) >= product_j(1-a_j/N) >= 1-Q_i/N >= 1-x.

Here K_j records queried rows, u_j marks unqueried rows and a_j is their queried count. Thus each nonnegative allocated ideal cost transfers to its corresponding real cost with factor at most 1/(1-x). Transfer before summing across addresses. Retaining the starting secret would give density N times a compatibility indicator instead of W and invalidate this argument. The simulator must recompute roots and reference messages from an idealized endpoint, and cap auxiliary paths at q because that endpoint may have no compatible original secret. Both chronological orders of encoding preparation and inversion contribute to the displayed coefficients.

FTS requires a separate comparison. An undisclosed true secret is uniform on its unexcluded set U, so a candidate hits it with probability p=1/|U|<=1/(N-q). On a miss, delete the candidate and return a uniform hash answer, including the possibility of an alternative preimage. A true hit and an alternative preimage are different events.

For each hash slot j, force earlier eligible choices to miss and slot j to hit. The likelihood of the corresponding original first-hit branch is

    L_j = p_j*product_(t<j)(1-p_t) <= 1/(N-q).

These are supported conditional branches of the deferred-secret execution. They preserve the original budget and fresh-message kernel. Prove near coverage in each forced law, attaching that law's own proposal construction. The resulting bounds are

    Pr[a true guess and a near certificate] <= 557*x^2/(1-x),
    Pr[two distinct true guesses] <= x^2/(2*(1-x)^2).

Multiplying an unconditional near-coverage probability by an unconditional guess probability would not prove the first inequality. The conditional likelihood and the coverage theorem in the changed law are essential.

The exhaustive verifier trace then gives

    Pr[SUF win] <= c_Q(x)*E[Q]/N + c_encoding(x)*E[A_encoding]/N
        + E[A_structure]/N + E[A_message]/N
        + 557*x^2/(1-x) + x^2/(2*(1-x)^2) + delta*x + epsilon(q).

For x<=x_*, both query coefficients are below 131/80 and the two additional FTS coefficients sum to less than 9/80. Using the shared allocation gives Pr[SUF win]<=(7/4+delta)*x+epsilon(q)<2x. Thus this interval overlaps the large-range interval. No sharper occupancy constant is required to make the current plan close.

## Order of work and what counts as completion

1. Finish the paper correspondences for the exact graph, private-prefix erasure and exhaustive strong-forgery decomposition. Require preservation of observable responses and actual costs, including finite failures and own-input exclusion.
2. State and prove coverage from its local message and signing transition rules. Instantiate it for the graph process stopped at B and for every supported forced-FTS process. The [coverage derivation](cached-target-forecast.md) identifies the rules and supplies the paper proof. Fresh message cells must remain uniform in the conditioning state actually used.
3. Complete the original-game large-range theorem using the two-transition potential. Its only adversary premise must be the existing whole-experiment hash bound.
4. Complete the small-range theorem using projected, allocated OTS costs and the forced-FTS comparison. Audit that every statistic and stop survives its stated projection and that no query class is charged q independently before addition.
5. Combine both ranges with probability at most one. Audit the public theorem's dependencies against the unchanged game and assumptions.

The exact rational closing calculation and the potential transition identities were checked independently in this review. Those checks establish the arithmetic, not the concrete security transfers. The credible endpoint is a theorem about the original SUF game with the existing query-bound premise; a theorem that assumes any of the displayed global cryptographic inequalities remains an intermediate result.
