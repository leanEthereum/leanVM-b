# Two different chain inversions and a static OTS consequence

These are paper lemmas in the static independent-chain experiment. They complete the distinction between two backward steps in one chain and one backward step in each of two different chains. They do not yet prove the full SPHINCS useful-work inequality.

## A one-edge contact

Use independent chain challenges of lengths at least one, all endpoints published initially, and at most q<N total queries. A contact with chain i is a queried last-function input mapping to that chain's endpoint. Set x=q/N.

For a fixed challenge, stop at its first contact. In its ideal experiment, each fresh last-function answer is the endpoint with probability 1/N. Before contact all its nonempty queried suffix counts C_r vanish. On contact the posterior likelihood from long-chain-inversion.md is at most

    2 + sum_(r=0)^(h-2) m_r,

where m_r counts previously queried paths ending at this last-function input. Each queried earlier-function input contributes at most once over all last-function attempts. Thus the baseline cost for this challenge is bounded by twice its last-function queries plus its earlier-function queries.

Comparing the ideal expectation with the real one using w >= 1-x, then summing actual costs across chains, gives

    P[at least one contacted chain] <= 2x/(1-x).

This includes candidate paths chosen using earlier functions and arbitrary adaptive allocation among challenges.

## Continuing after a contact

The same argument can be restarted from a real transcript T. Restrict attention to chains with no contact yet. For each such chain i, the conditional real law of its unqueried function cells has density W_i/w_i(T) relative to independent uniform completion of its partial tables. Other challenges and the adversary's private state are retained with their conditional real laws. Conditional on the fixed transcript, the underlying challenge distributions factor: adaptive query choices impose no constraints beyond their observed replies. Independent auxiliary randomness can be included in that conditioning.

Let I_i^T be this conditional ideal continuation for just chain i. The conditional real transcript likelihood is w_i(final)/w_i(T). Because w_i(final) >= 1-x, every nonnegative continuation cost C satisfies

    E_(I_i^T)[C]/w_i(T) <= E_R[C | T]/(1-x).

At the first future contact, the ideal first-success bound has numerator two for the fresh last-function query and one for each earlier queried path reaching its input. The latter paths may include queries made before T. Each earlier input is charged at most once.

Let tau be the total query count already spent at T. Summing these real costs over all still uncontacted chains gives at most

    2(q-tau) + tau <= 2q.

The old-query term counts only old earlier-function inputs of the remaining chains; using tau is an upper bound. Future costs use one or two units per fresh query. Therefore, uniformly over such transcripts,

    P[a further distinct chain is contacted | T] <= 2x/(1-x).

A query belongs to only one chain, so one query cannot make the first contact with two different chains. Stop at the first contacted chain and apply the conditional bound to all the others. Together with the bound for the first contact, this proves

    P[at least two different chains contacted] <= 4x^2/(1-x)^2.

No independence between the two successful searches is asserted. The second estimate is conditional on the complete first-contact history and permits reuse of earlier work.

## Static target-sum OTS consequence

Fix an honest codeword d with 42 digits in {0,...,7} and sum 191. For each chain j, independently generate its prefix through position d_j and publish its value Y_j there. Chains with d_j=0 need no challenge. Give the adversary access to all the prefix functions. Independent functions above the published positions and information computed from the published values and those functions may also be provided.

Define a backward witness for another valid codeword e to mean that, for every j with e_j<d_j, there is a complete queried chain path from position e_j ending at Y_j. Count all calls needed to check these paths. This is an explicit event in the static experiment. A real signature forgery with a merger above Y_j need not satisfy this event; that case must be accounted for separately in a full reduction.

Write b=sum_j max(d_j-e_j,0). Since d and e have the same sum, b=1 implies e=d-unit_i+unit_j for distinct i,j. Thus for a distinct, non-neighbor codeword, b>=2. Either one chain has d_j-e_j>=2, giving a two-edge suffix contact, or two different chains have positive backward distances, giving two distinct one-edge contacts.

Combining multiple-chain-inversion.md with the preceding bound yields

    P[a backward witness for some distinct non-neighbor e]
      <= ((3/2)x + 4x^2 + 2x^3)/(1-x) + 4x^2/(1-x)^2.

For x<=1/64 this is strictly below (7/4)x. The constants are independent of the number of chains and their lengths. The codeword e may be chosen adaptively; the bound already covers all successful queried suffixes, so there is no union bound over codewords.

The candidate full-proof plan needs its useful-inversion estimate only for x<=2^-12, assuming the proposed quadratic bound handles larger x. Hence this static estimate has room in the needed range. The remaining transfer must preserve the actual reference encoding oracle, the joint distribution of selected frontiers, the other hash domains, and the common resource accounting with other ways to forge. The static experiment alone does not establish that transfer.
