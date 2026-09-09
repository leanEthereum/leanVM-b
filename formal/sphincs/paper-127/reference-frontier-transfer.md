# Canonical frontiers and the actual reference-encoding oracle

The current paper assembly and shared costs are in [small-budget-transfer.md](small-budget-transfer.md). This note spells out the OTS simulator's dependence on the retained data and proves the likelihood comparison for its adaptive transcripts. The concrete Lean interpreter correspondence and the full strong-forgery reduction remain to be established.

This is a paper change of experiment for the unchanged scheme. It justifies transferring the static chain bounds to a precisely defined backward-witness event in the actual execution. It also improves the OTS neighborhood preparation coefficient. It does not by itself bound every way to forge a signature.

## Sampling reference counters and words first

Fix the public parameter. Let Omega contain all independently sampled secrets and all non-encoding oracle tables. The finite family of geometrically possible OTS addresses p has canonical messages M_p(Omega), given by the next tree root or FTS public key. Distinct addresses have disjoint encoding domains. Set T=2^32, N=2^128, and let C be the valid codewords, with L=|C| and validity probability v=L/N.

Conditional on any Omega, each address's least valid counter J_p has law P[J_p=j]=(1-v)^j v for 0<=j<T and P[J_p=none]=(1-v)^T. On success, its selected codeword D_p is uniform on C, independently of J_p. On exhaustion, add an independent artificial D_p uniform on C. Across addresses these pairs are independent, and their joint law does not depend on Omega. Therefore the family (J_p,D_p) can be sampled before Omega without changing the joint distribution.

Conditional on Omega,J,D, generate the encoding table at address p as follows. If J_p=j, the cells (M_p,c) for c<j have independent uniform invalid low digests; cell (M_p,j) has low digest equal to the encoding of D_p; every other cell has an independent uniform low digest. If J_p=none, all T cells (M_p,c) are independently uniform invalid, and every other cell is uniform. Every high 128-bit part is independent uniform in both cases.

These are exactly the conditional laws of the original oracle. In particular, this construction does not expose validity indicators at the unrestricted cells. That avoids the loss incurred by treating a future query as already known to be valid.

Give J,D and all canonical messages to the analyst, and run the original algorithm ignoring the advice. A fresh nonreference input either has an invalid output, in which case it cannot be a neighbor or equal D_p, or it has an independent uniform N-valued low digest. Consequently, if A counts fresh nonreference encoding queries,

    P[any queried unit neighbor] <= 1722 E[A]/N,
    E[number of distinct marked chains] <= 1722 E[A]/N,
    P[any nonreference encoding equal to D_p] <= E[A]/N.

A neighbor D_p-unit_i+unit_j marks its uniquely lowered chain i. There are at most 41 neighbors lowering a specified chain. If all J_p are defined, nonreference means any input other than (M_p,J_p). At an exhausted address every input is nonreference, with its artificial D_p used only for the analysis.

The advice does not alter the execution or its cost distribution. Fresh unrestricted cells remain uniform under adaptive querying, even when the analyst knows Omega,J,D and the previously returned encoding answers. Queries before publication of a signature are included. The coefficient 1722/N is stronger than the earlier 1722/L estimate.

## Separating prefixes from the rest of the graph

Conditional on D, split every OTS chain j at its canonical digit d_j. The chain's sampled secret and its d_j independent prefix functions form a challenge with endpoint Y_j equal to the honest value at position d_j. A zero-length prefix has Y_j equal to its sampled secret and needs no hidden challenge. Different chain prefixes have disjoint tweaks and independently sampled starting secrets.

The conditioning is on the complete reference words. Their digits need not be independent. Once the words are fixed, the prefix lengths and disjoint oracle domains are fixed, and the independent secret and function laws are the original ones.

All remaining structural hashes form an acyclic graph above these endpoints and the FTS secrets. Given the complete family Y and independent remaining functions and FTS data, one can compute every OTS endpoint at position 7, every Merkle root, every FTS public key, and hence all M_p and the actual public key. The conditional encoding table described above is a random function of this information, J,D, and independent table randomness. It does not require access to an unqueried OTS prefix cell.

Thus, for the OTS backward-witness analysis, give all Y,J,D and the independent remaining data to a simulator. It can answer non-prefix oracle queries, generate the public key, and reproduce signing responses. Every successful OTS response is the corresponding canonical frontier Y and counter J. The FTS part and authentication paths are computable from the remaining data. Retry failures are reproduced by the actual finite loops and J=none cases.

Internal honest prefix evaluations need not be made by this simulator. They only fill an oracle cache and compute values already supplied by Y or the independent forward tables. The adversary does not see their inputs or intermediate results. With the oracle sampled as a full function, omitting these internal evaluations leaves all subsequent answers unchanged. Calls made by the adversary and the final verifier to prefix domains are routed to the actual prefix functions, including any prefix inputs previously evaluated internally by an honest algorithm.

The chain challenge functions have N digest inputs. At a prefix domain, a correctly sized digest payload is routed to that challenge function. Other byte strings at the same domain are independent auxiliary rows, since an honest prefix and final chain verification only use digest payloads. Such auxiliary replies can be simulated as independent randomness without reading an unqueried challenge cell. The byte-layout injectivity lemmas distinguish these inputs and the different graph domains.

Let Q count distinct externally evaluated prefix-domain inputs; this upper-bounds the correctly sized challenge inputs. It is bounded by the number of actual adversarial and verification hash calls. Its sum with fresh nonreference encoding queries and the other charged call classes never exceeds the original whole-experiment syntactic budget. Q need not be the number of entries fresh relative to the hidden honest cache. Including malformed payloads in Q only enlarges the bound.

Running the original adversary while ignoring the added advice preserves its response distribution. The static multiple-chain estimates apply conditionally on J,D and the independent remaining randomness. Auxiliary tables can depend on the published Y through the kernel described above; this dependency is retained when idealizing one endpoint. There is no unexplained replacement of a selected chain value by an independent secret.

## Exact dependence of honest responses and costs

Fix a chain i with positive reference digit d_i. The projection forgets S_i and all private evaluations below Y_i. Fix its full prefix functions H_i, the endpoint Y_i, all reference data and the remaining independent data. Any two starting secrets compatible with these fixed data must give the same projected execution. The following inspection of Statement.lean establishes the required deterministic dependence.

The only uses of an OTS starting secret in honest hashing are chainWalk calls in oneTimePublicKey and otsSignFrom. The former walks all seven edges. The latter, on successful canonical encoding, walks exactly d_i edges. Therefore the private computation either returns Y_i or continues from Y_i through the independent forward functions. No honest subroutine returns a chain value strictly below its own reference digit. All other honest structural computations consume full chain endpoints, FTS data, or structural nodes above them.

A fixed OTS address has one canonical message even across different signing requests. For an upper-layer address (lay,tree,leaf), the next tree index is tree*2^layerHeight(lay)+leaf, by the concrete layer-link identities. At the bottom, the FTS index is tree*2^7+leaf. Thus all layer messages can be reconstructed from the retained frontiers and the other structural data. Reference encoding is consequently the same finite search at every honest visit to an address, including visits after an adversarial query to one of its rows.

The full 256-bit answer at a prefix row can be split into its low 128-bit function value H_j(x) and an independent high-half function value. Honest chain computations use only the low half. High halves can be retained in the auxiliary data and returned on external queries without revealing an unqueried low-half prefix value. An input with a payload other than a 16-byte digest uses an independent auxiliary row. Classify all such requests by their actual serialized bytes; no assumption that the adversary used typed constructors is required.

The exact cost calculation uses the hash-oracle-call count in HasHashQueryBound. Every call costs one, including a repeated row. Let

    TreeCost(h) = 296*2^h-1,
    PathCost(h) = 296*(2^h-1)-h,
    FtsKeyCost = 14*(2^11-1)+1 = 28659,
    FtsOpenCost = 14*sum_(l=0)^9 (2^(l+1)-1) = 28504.

A tree leaf uses 42*7 chain calls and one leaf hash, giving TreeCost(0)=295. Each internal node adds one to the costs of its two subtrees, proving the displayed TreeCost by induction. A tree path computes one sibling subtree at each level below h, giving PathCost. The FTS formulas follow from one hash per leaf and internal binary node. Levels above a layer's height in treePath return zero and cost no hash call.

For one signing layer p at height h, write ell(J_p)=J_p+1 on success and ell(none)=2^32. Its cost is exactly

    MessageCost(p) + ell(J_p)
        + 1_(J_p != none)*(191 + PathCost(h)),

where MessageCost is TreeCost(7) for either upper layer and FtsKeyCost for the bottom layer. The 191 is the sum of the valid reference digits. An exhausted encoding does not run its signing chains or authentication path. It still follows the already completed layerMessage computation.

If the message-digest loop exhausts, signing costs exactly its 2^32 attempts. If it selects a digest after K attempts, the whole signing invocation costs

    K + FtsOpenCost + sum_(three layers p) LayerCost(p).

The sum includes all three layers even if one fails: sign evaluates sequenceFin before traverseOption decides whether to return none. Key generation costs TreeCost(12). These identities account for every original private call; they depend on the retained reference data and message trace, not on S_i or private cache hits. They also reproduce the positions of message rows and empty non-message markers in SigningBoundaryTrace.

To define the simulator, replace each private prefix walk by d_i empty cost markers and its supplied Y_i, then run its forward portion and all other computations normally. Return the same signatures and failures at the same completed boundaries. Route every external or verification prefix input to the actual H_i table, even if an honest computation previously read that row privately. With a consistent full function, prior materialization does not change its answer. Consequently the original computation and this simulator have the same projected trace on every compatible complete table and secret, by induction through the subroutines above and the adversary's adaptive calls.

The projected monitor retains message cells, completed signing views, reference data, actual costs and geometric proposal lengths. Its index guard is C_i(t)<=t/(LI)+2^80, as in the revised coverage proof. The existing full-cache cardinality guard can first be removed on real paths using its bound by spent calls. Neither that private cardinality nor the stronger private cache-exception flag is part of the projected history. All bank tests and query allocations are determined by the remaining data.

On auxiliary executions, halt before consuming hash slot q+1, including when the cap lies inside a private cost debit. This rule depends only on the retained counter and control stage. It never changes an admitted real execution. An independently chosen ideal endpoint may have no compatible starting secret; the cap defines its bounded behavior without claiming such a secret exists.

## Likelihood for a causal transcript

The preceding dependence gives a direct likelihood theorem. For one chain, let H=(H_0,...,H_(d-1)) be independent uniform functions on [N]. In the real law sample a uniform S and set Y=H_(d-1)(...H_0(S)); in the ideal law sample Y independently and uniformly. Both laws run the same simulator, whose auxiliary transitions may depend on Y and already returned prefix rows but do not read an unqueried prefix row. Other chains remain real. The starting secret and private prefix computations are absent from the compared record.

For a fixed projected transcript T, let Rows(T) be its distinct recorded prefix rows. Conditional on H,Y, its probability has the form

    kappa_Y(T) * product_((j,x,y) in Rows(T)) 1_(H_j(x)=y).

The coefficient kappa includes all auxiliary transition probabilities, adaptive choices, high halves and stopping decisions. It does not depend on unqueried H rows or on S. This factorization follows by multiplying successive conditional kernels. Repeated rows add only a consistency requirement. A stop at a contact, marker or budget cap is determined by T and is absorbed into kappa. Thus the same factorization holds at the stopping times used by the inversion proof.

For a complete H and Y, summing the real probability over the forgotten uniform S gives

    W(H,Y) = #{s : H_(d-1)(...H_0(s))=Y}

as its density relative to the ideal law. The factor kappa is identical in the two laws and cancels. If S were retained, the density would instead be N*1_(H_(d-1)(...H_0(S))=Y). This distinguishes the valid projected comparison from an invalid assertion about the full secret-key state.

In the ideal law, conditioning on T leaves unqueried H cells independent and uniform: the displayed factorization imposes only the recorded row constraints. Let K_j be the matrix of known rows, let u_j indicate unknown rows, and put P_j=K_j+u_j*1^T/N. A chain uses one row from each distinct function, so averaging W over these independent completions gives the transcript density

    w(T) = E_ideal[W | T] = 1^T P_0 ... P_(d-1) e_Y.

If a_j is the number of observed rows of H_j and Q_i=sum_j a_j, nonnegativity of the matrices gives

    w(T) >= 1^T product_j(u_j*1^T/N) e_Y
         = product_j(1-a_j/N) >= 1-Q_i/N >= 1-x.

This holds pointwise at every relevant stopped transcript when the common q bound is below N. Hence every nonnegative projected cost Z satisfies

    E_real[Z] = E_ideal[w(T)*Z] >= (1-x)*E_ideal[Z].

The equality is a density identity, not independence of a chosen cost and W. If only chain i is idealized, the other chains use the same conditional kernels in both laws. Given their endpoints and independent auxiliary data, adaptive transcript constraints factor by queried rows, so the same proof applies without a factor for the number of chains.

For a conditional restart at a real transcript T_0, idealize only the unqueried completion of chain i. The conditional density at a later stopped transcript is w_i(T)/w_i(T_0), and therefore

    E_(I_i^T_0)[Z]/w_i(T_0) <= E_real[Z | T_0]/(1-x).

This is the comparison needed to sum allocated costs after a first contact. All stopping decisions and costs here are functions of the projected transcript. A private flag revealing whether an external input was previously evaluated on the secret chain would invalidate the factorization.

## Bounds retaining the allocation of queries

Put x=q/N<1 and

    c(x) = ((3/2)+4x+2x^2)/(1-x) + 4x/(1-x)^2.

The static proofs, before replacing every allocated cost by q, give

    P[non-neighbor backward witness] <= c(x) E[Q]/N.

Here is how the shared allocation survives the comparison. Stop chain i's analysis at its first fully queried two-edge suffix. Its ideal first-success numerator has baseline at most 3Q_i/2: a productive last-edge query is charged twice, and each earlier queried input contributes to a known predecessor path for at most one such query. If a,b,c count queries before the last two functions, to the penultimate function and to the last function, respectively, this uses a+b+2*min(b,c)<=3*(a+b+c)/2. The additional terms in multiple-chain-inversion.md are at most (4q/N^2+2q^2/N^3)*E_(I_i)[Q_i]. The causal density comparison transfers this particular stopped Q_i to its real expectation. On a real execution, summing these counts over i counts each external prefix query at most once. Thus the two-edge contribution is ((3/2)+4x+2x^2)*E_R[Q]/(N*(1-x)).

For contacts in two distinct chains, restart at the first contact, at spent count tau. For every still-uncontacted chain i, let B_i be its future first-contact charge: two per fresh last-edge query and one for each older queried input whose known path reaches such a query. Every older input is charged at most once, including inputs queried before tau. Its conditional first-contact probability is at most E_(I_i^T)[B_i]/(N*w_i(T)). The conditional density comparison bounds this by E_R[B_i | T]/(N*(1-x)). On each real path,

    sum_(uncontacted i) B_i <= 2*(q-tau)+tau <= 2q.

The first term covers future allocated calls and the second covers old prefix work, across all those chains together. Hence the conditional chance of a further distinct contact is at most 2x/(1-x). The expected number of first contacts is at most 2*E_R[Q]/(N*(1-x)), by the same single-contact charge and real-cost conversion. Their combination gives 4x*E_R[Q]/(N*(1-x)^2), the remaining term in c(x). No chain receives a separate full q allocation in this sum.

For neighboring codewords, separate the chronological order of the marker and the first one-edge contact with its lowered chain.

If the contact comes first, a subsequent fresh encoding query has at most 41 possible neighboring outputs per previously contacted chain. Summing individual contact probabilities using the same density comparison gives E[number of contacted chains] <= 2 E[Q]/(N(1-x)). At most q encoding queries follow, so this order contributes at most

    82x E[Q]/(N(1-x)).

If the marker comes first, stop at the first marker for its lowered chain i, provided i has not yet been contacted. At this real transcript T, the conditional probability of a later first contact is at most E_(I_i^T)[B_i]/(N*w_i(T)). The old-work and future-work accounting above gives B_i<=2q pointwise, and w_i(T)>=1-x. Thus this conditional probability is uniformly at most 2x/(1-x). Averaging over the real first-marker history and summing distinct marked chains, whose expected number is at most 1722*E_R[A]/N, gives contribution at most

    3444x E[A]/(N(1-x)).

This includes inversions precomputed before the encoding query. It does not assign all inversion work to the period after preparation or assume that preparation and a successful inversion are independent.

The two orders are exhaustive because a prefix query and an encoding query are different oracle calls. The prefix likelihood argument may fix independent auxiliary tables to establish its factorization. The fresh-encoding estimate is instead proved before revealing unqueried unrestricted encoding rows and is then integrated into the real expectations above. Neither calculation is applied in the other's inappropriate conditional history.

Consequently the event consisting of a nonreference encoding equal to its canonical D_p or a backward witness for any distinct valid codeword has probability at most

    [c(x)+82x/(1-x)] E[Q]/N
        + [1+3444x/(1-x)] E[A]/N.

For x<=2^-12 both coefficients are below 15/8. At x=2^-12, they are respectively 52281827327/34342963200 and 359/195. The expressions are increasing for 0<=x<1, so checking that endpoint suffices.

In the range x<=3*2^-14 used by the current plan, both coefficients are below 131/80. This leaves the stated 9/80 allowance for the extra FTS terms and closes with the unit coverage payment. The bound applies to the same real query allocations used by that coverage calculation.

This gives the paper OTS witness bound with separate expected real costs, using the simulator correspondence and causal density argument above. The Lean proof must establish those correspondences for the concrete interpreter. A deterministic reduction must also distinguish these witnesses from structural matches above the frontiers and from FTS forgeries. Revealing canonical OTS signatures for analysis does not establish security of the whole scheme by itself.

The exact finite checks in transfer-kernel-checks.py compare honest executions with executions that erase private prefix walks while retaining their costs. They include finite encoding failure, a later layer running after that failure, repeated external rows, full replies with fixed auxiliary high halves, and budget caps inside private work. The resulting stopped transcript probabilities agree with the partial-table likelihood. As a negative control, retaining a flag for a previously private cache hit distinguishes compatible secrets with the same frontier and fails the erasure test. These finite models check the mathematical interface; they are not the full SPHINCS interpreter or a Lean proof of its security.
