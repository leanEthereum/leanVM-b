# Paper route to 127-bit strong unforgeability

This is a proof strategy for the unchanged concrete scheme at source commit a743f717. Full 127-bit security remains open, mathematically and in Lean. The linked notes supply paper arguments for the OTS witness estimates and a joint primitive bound. The two remaining full-game obligations are stated explicitly below. No Lean implementation change accompanies these notes.

## Target and revised closing argument

Write N=2^128 and x=q/N. The target is P[forge]<=2x for the original strong-unforgeability experiment, with independently sampled secrets, at most 2^24 signing requests, actual finite retry failures, and the original hash budget covering key generation, signing, adversarial queries, and verification. At q>=N/2 the probability bound by one suffices.

The coarse reduction spends approximately two primitive chances per query before adding FTS coverage. Even substituting the newer near-uniform coverage estimate and discarding the compatible credits would leave 35x/16, before smaller errors. The paper route instead charges the queries that prepare and complete a usable forgery, and pays for message queries inside the primitive probability bound.

The new target is a two-regime argument, split at

    x_0 = 3*2^-14,       q_0 = 3*2^114.

For x<=x_0, aim to bound completed primitive forgery witnesses and ordinary coverage charges together by (7/4)x. For x>=x_0, use the paper primitive bound 2x-x^2/8, which already includes the same ordinary coverage charge. In either range, the proposed unpaid coverage excess is at most 2^-16 x plus smaller errors.

This leaves two substantive obligations: complete the FTS work accounting for the small-budget bound, and prove the charged coverage estimate for targets that may have been cached before signing. The arithmetic is sufficient if those obligations hold; it does not establish them.

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

For x<=x_0, both coefficients are below 7/4. The two expected costs refer to the same actual execution and disjoint query classes. This is stronger than charging each event class the whole q. It does not assume that inversions occur only after preparation.

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

## Remaining obligation: charged cached-target coverage

The required estimate is an adaptive coverage statement that can be applied to the full execution or to an execution stopped at B. With A_msg counting message queries in that execution, the desired bound is

    P[covered target] <= (3/(2N)) E[A_msg] + 2^-16 x + epsilon.

Coverage must use signing views at inputs other than the target's own input. Targets may be queried before the signatures that eventually cover them. The statement must retain this exclusion, cached digest reuse, the actual signing limit, and the same q. This inequality is unproved.

An auxiliary Poisson calculation supports the proposed excess. If Z_i are 2^26 independent Poisson variables of mean 19/50 and R_P=sum_i Z_i^14/2^48, then E[(R_P-3/2)_+]<2^-16. A proof splits occupancies into at most 10, exactly 11, and at least 12, using exponential and factorial moments with exact rational bounds.

Near-uniform reuse can support a domination of ordinary index occupancy, apart from small cache and waiting-time errors. That does not by itself control targets that were queried earlier and become covered later. A sufficient next lemma would dominate the positive excess of a predictable target-completion forecast by a conditional expectation of (R_P-3/2)_+, or establish an equivalent charged supermartingale. The existing first-moment envelope does not prove this stronger claim.

## Remaining obligation: FTS work at small budgets

For x<=x_0, the OTS work now has a rate below 7/(4N) with its actual allocation retained. The missing step is a compatible FTS bound. Finding a preimage of an undisclosed FTS leaf hash must produce a usable signature, which also requires an admissible digest with all other forest coordinates available. Both chronological orders must be handled: a digest may prepare the missing leaf before inversion, or an inversion may precede the digest search. Cached digests can acquire the remaining coordinates through later signing calls.

A useful analysis can expose all FTS leaf hashes, keep their secrets hidden until disclosed, and treat each leaf as a separate one-step inversion challenge. A signature needing two undisclosed leaf inversions requires two distinct contacts. A signature needing one requires a near-covered digest target. The required target-marking bound must share its message-query costs with ordinary coverage. It cannot be obtained by assigning the full q separately to inversions and digest searches.

The sufficient small-budget conclusion is a bound on completed primitive forgery witnesses plus the ordinary message charge by (7/4)x, using the same query allocation. This is a proposed full-game inequality, not a consequence already established by the OTS lemmas.

## Closure and next milestone

If the two remaining obligations hold, then for x<=x_0,

    P[forge] <= (7/4)x + 2^-16 x + epsilon < 2x.

For x_0<=x<=1/2, the paid primitive bound and charged coverage give

    P[forge] <= 2x-x^2/8+2^-16 x+epsilon.

At x=x_0, x/8-2^-16=2^-17, and this difference increases with x. Thus the large-budget range leaves at least 2^-17 x for the remaining errors. The candidate errors q/2^216+q/2^223+q/2^237+2^-700 fit inside that margin for q>=1, if their stated bounds are established in the final construction. At q>=N/2 use the probability bound by one.

The next mathematical milestone is the charged target-completion estimate, including the version with one missing FTS coordinate. It is the common missing ingredient in the two remaining obligations. Return to Lean only after these ingredients form one complete paper proof for the original strong-unforgeability game. The paper lemmas and their arithmetic checks do not constitute a completed 127-bit Lean theorem.

The Python files under paper-127 contain exact rational checks of the partial-table likelihoods, conditional reference-table laws, finite probe decision problems, and closing constants. They can each be run with Python 3 and use only its standard library. These checks support the written arguments; they neither implement the security experiment nor certify the missing full-game inequalities.
