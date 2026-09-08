# Paper route to 127-bit strong unforgeability

This is a proposed proof strategy for the unchanged concrete scheme at source commit a743f717. The full 127-bit mathematical argument remains incomplete. The auxiliary lemmas described below have paper arguments, but the three full-game inequalities in the closing argument are proof obligations. No Lean implementation change accompanies this document.

## Target and current obstruction

Write N=2^128 and x=q/N. The target is P[forge] <= 2x for the original strong-unforgeability experiment, with independently sampled secrets, at most 2^24 signing requests, and the original hash budget covering key generation, signing, adversarial queries, and verification. At q>=N/2 the probability bound by one suffices. Retry exhaustion and signatures on previously signed messages remain part of the original experiment.

The coarse reduction already allows approximately two primitive chances per hash query. Adding the FTS coverage bound then exceeds the desired coefficient. Even substituting the newer near-uniform coverage estimate and dropping the compatible credits would leave 35x/16, before smaller errors. Another unconditional union bound cannot close that expression.

The proposed repair is to charge the work needed to make the second primitive chance useful, retain the overlap between repeated attempts at larger q, and charge ordinary FTS coverage to the same budget. All three must describe one execution. Giving each attack class the whole budget separately loses the required constant.

## 1. Exploit the cost of preparing a useful inversion

An inversion of a hash of an unknown input can exploit both guessing that input and finding an alternative preimage. Recovering one intermediate value does not automatically supply a new valid signature. For the target-sum OTS, let d be the honest codeword and e a new valid codeword. Both have 42 digits in {0,...,7} and sum 191. If sum_j max(d_j-e_j,0)=1, then e=d-unit_i+unit_j for distinct i,j. Thus an encoding that makes exactly one extra backward step sufficient is one of at most 1722 neighbors.

There are exactly

    L = [z^191](1+z+...+z^7)^42
      = 27362001415540541846731060490886528

valid codewords, and 1722*N/L < 2^25. For the concrete scheme, an OTS address has a fixed structural message, independent of its encoding-oracle domain. Separating each oracle answer's validity indicator from its uniform valid codeword fixes the least valid counter without inspecting that codeword. Exposing the reference words then gives the adaptive preparation bound

    P[G_OTS] <= (1722/L) E[A] < 2^25 E[A]/N,

where A counts fresh nonreference encoding queries. This includes queries before signing and finite counter exhaustion. The argument concerns preparation only; exposing independent structural secrets in that counting argument must not be reused as an unforgeability argument.

The fixed-message premise matters. If an adversary could choose an OTS key's honest message after seeing encoding outputs, it could choose one member of a birthday pair of neighboring codewords. The analogous linear preparation lemma is false for that stronger chosen-message OTS setting. The concrete hypertree avoids that freedom.

There is also a paper bound for the work required when the new codeword is not a neighbor. In a static independent-chain experiment, publish the honest values at positions d_j initially. Define a backward witness to require a complete queried path to those values in every chain where e_j<d_j. Arbitrary query ordering, earlier-function queries, cache mergers, and adaptive allocation among chains are allowed. Then

    P[backward witness for some distinct non-neighbor e]
      <= ((3/2)x + 4x^2 + 2x^3)/(1-x)
          + 4x^2/(1-x)^2
      < (7/4)x                       when x<=1/64.

The first term handles two backward steps in one chain. The second handles one backward step in each of two different chains. There is no factor of 42 and no union bound over encodings.

The central technique is a change of measure. Replace one chain endpoint Y by an independent uniform value. The density of the real challenge is W, its number of full-chain preimages. For a partial oracle table, let C_r count known suffix paths from layer r to Y, with C_h=1. Its conditional density satisfies

    1-Q_i/N <= w_i=E[W_i | transcript] <= sum_(r=0)^h C_r,

where Q_i is the number of queries allocated to that chain. Known paths ending at a fresh successful query can be charged to earlier queries, even when they merge. The lower density bound converts the separate analyses back to expected costs in the same real experiment. Their allocated query counts sum to at most q. A conditional version after the first contacted chain gives the quadratic bound for contacting a second different chain without assuming independent searches.

The required full-game statement is stronger than this static witness bound. It must include the actual encoding oracle and selected frontiers, collisions above the honest values, FTS inversions, and queries before signature disclosure. In particular, define fast work F and remaining work R=q-F, including unused budget, so that preparation work A<=R and F<=q*1_G. The desired joint inequalities are

    P[forge] <= 2x - E[R]/(4N) + E_cov + epsilon,
    P[G] <= c E[A]/N,               c<=2^25.

Here G must include FTS preparation as well as OTS preparation. Proving that classification and the common work accounting is the first remaining full-game obligation.

If these inequalities hold, put f=P[G]. Then E[R]/N >= max{x(1-f),f/c} >= x/(1+cx), giving a discount of at least

    x/(4(1+cx)) >= min{x/8,2^-28}.

## 2. Charge ordinary FTS coverage and bound its excess

For index i, let s_i count signing uses. The usual coverage envelope involves sum_i s_i^14/2^48. Its whole mean is too expensive to add after spending two primitive chances per query. Instead, charge an ordinary rate of 3/(2N) to target-creation opportunities and bound only the remaining excess. The desired full-game estimate is

    E_cov <= 2^-16 x.

An auxiliary calculation supports that target. For 2^26 independent Poisson variables Z_i of mean 19/50, put R_P=sum_i Z_i^14/2^48. Then

    E[(R_P-3/2)_+] < 2^-16.

A paper proof splits counts into at most 10, exactly 11, and at least 12. Exponential moments control the first part, and factorial moments control the latter two. Exact rational bounds suffice; simulation is unnecessary. The near-uniform reuse estimate suggests dominating ordinary adaptive index occupancy by these Poisson variables, apart from small cache and waiting-time errors.

Ordinary occupancy is insufficient for the desired inequality. A digest queried before a later signing call can become covered afterwards, and the adversary can adapt its choices to cached answers. The proof must retain exclusion of that target input from the signing views that cover it, and charge these earlier targets as well. A sufficient next lemma would dominate the positive excess of a predictable target-completion forecast by a conditional expectation of (R_P-3/2)_+. The existing first-moment envelope does not establish that domination. This is the second remaining full-game obligation.

## 3. Retain a quadratic saving at larger query budgets

For one isolated random-function inversion challenge Y=H(S), k distinct trials have success probability

    1-(1-k/N)(1-1/N)^k <= 2k/N-(k/N)^2.

An abstract adaptive version also has a paper proof. With independent hidden N-valued labels, at most one guess against each of two distinct labels per round, and disclosures selected using only already visible information, the success probability in q rounds is at most 2x-x^2. The proof uses the martingale 1_survival/product_i(1-c_i/N), where c_i records distinct failed guesses, retained after disclosure. Since c_i<=q and sum_i c_i<=2q, that product is at least (1-x)^2.

The distinct-label and disclosure assumptions must be checked. Two guesses against the same label in one round can give exactly 2x with no quadratic saving. Honest computations and reference encodings also cannot be treated as independent random advice without proving the corresponding simulation.

The desired full-game conclusion, with the same E_cov as above, is the weaker bound

    P[forge] <= 2x - x^2/8 + E_cov + epsilon.

Establishing this in the actual experiment is the third remaining full-game obligation. The two bad events in the existing reduction must not be assumed independent.

## Numerical closure and order of work

If the three full-game obligations hold, they imply

    P[forge] <= 2x - max{x^2/8,min(x/8,2^-28)} + 2^-16 x + epsilon.

For every x>0,

    max{x^2/8,min(x/8,2^-28)} >= (5*2^-18)x.

Thus at least 2^-18 x remains after paying the proposed coverage excess. The proposed errors q/2^216 + q/2^223 + q/2^237 + 2^-700 fit comfortably inside that margin for q>=1. These are sufficient constants to aim for, not established full-game bounds.

There is a useful split in the work: at x>=2^-12, the proposed quadratic discount alone exceeds the proposed coverage excess with room for the errors. Consequently the useful-inversion argument only needs to be applied for q<=2^116. The static OTS bound above already has room in that range.

The next task is to transfer the static OTS result to the actual reference-encoding and disclosure process, then include the FTS one-step preparation cases in the same query accounting. Next prove the charged excess estimate for cached targets and the quadratic estimate in that same experiment. Recheck the final constants if any coefficient changes. Return to Lean only after these steps produce one complete paper inequality for the original SUF game.

The current status is a quantitative, testable route with several established auxiliary paper lemmas. A complete mathematical proof of 127-bit security remains to be supplied.
