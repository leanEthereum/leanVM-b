# Canonical frontiers and the actual reference-encoding oracle

The complete current original-experiment transfer, shared cost definitions, and small-budget assembly are in [small-budget-transfer.md](small-budget-transfer.md). That note also handles auxiliary budget caps, the information histories for encoding preparation, and the inherited budget of forced FTS laws.

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

All remaining structural hashes form an acyclic graph above these endpoints and the FTS secrets. Given the complete family Y and independent remaining functions and FTS data, one can compute every OTS endpoint at position 7, every Merkle root, every FTS public key, and hence all M_p and the actual public key. The conditional encoding table described above is a random function of this information, J,D, and independent table randomness. It does not require access to an unqueried OTS prefix cell.

Thus, for the OTS backward-witness analysis, give all Y,J,D and the independent remaining data to a simulator. It can answer non-prefix oracle queries, generate the public key, and reproduce signing responses. Every successful OTS response is the corresponding canonical frontier Y and counter J. The FTS part and authentication paths are computable from the remaining data. Retry failures are reproduced by the actual finite loops and J=none cases.

Internal honest prefix evaluations need not be made by this simulator. They only fill an oracle cache and compute values already supplied by Y or the independent forward tables. The adversary does not see their inputs or intermediate results. With the oracle sampled as a full function, omitting these internal evaluations leaves all subsequent answers unchanged. Calls made by the adversary and the final verifier to prefix domains are routed to the actual prefix functions, including any prefix inputs previously evaluated internally by an honest algorithm.

The chain challenge functions have N digest inputs. At a prefix domain, a correctly sized digest payload is routed to that challenge function. Other byte strings at the same domain are independent auxiliary rows, since an honest prefix and final chain verification only use digest payloads. Such auxiliary replies can be simulated as independent randomness without reading an unqueried challenge cell. The byte-layout injectivity lemmas distinguish these inputs and the different graph domains.

Let Q count distinct externally evaluated prefix-domain inputs; this upper-bounds the correctly sized challenge inputs. It is bounded by the number of actual adversarial and verification hash calls. Its sum with fresh nonreference encoding queries and the other charged call classes never exceeds the original whole-experiment syntactic budget. Q need not be the number of entries fresh relative to the hidden honest cache. Including malformed payloads in Q only enlarges the bound.

Running the original adversary while ignoring the added advice preserves its response distribution. The static multiple-chain estimates apply conditionally on J,D and the independent remaining randomness. Auxiliary tables can depend on the published Y through the kernel described above; this dependency is retained when idealizing one endpoint. There is no unexplained replacement of a selected chain value by an independent secret.

## Bounds retaining the allocation of queries

Put x=q/N<1 and

    c(x) = ((3/2)+4x+2x^2)/(1-x) + 4x/(1-x)^2.

The static proofs, before replacing every allocated cost by q, give

    P[non-neighbor backward witness] <= c(x) E[Q]/N.

For neighboring codewords, separate the chronological order of the marker and the first one-edge contact with its lowered chain.

If the contact comes first, a subsequent fresh encoding query has at most 41 possible neighboring outputs per previously contacted chain. Summing individual contact probabilities using the same density comparison gives E[number of contacted chains] <= 2 E[Q]/(N(1-x)). At most q encoding queries follow, so this order contributes at most

    82x E[Q]/(N(1-x)).

If the marker comes first, fix the lowered chain i and idealize its endpoint until its first contact. The first-contact likelihood charging, restricted to queries after its marker, has total numerator at most 2q times the indicator that i was marked before its first contact. The likelihood lower bound w_i>=1-x converts this ideal marking probability back to the real marking probability. Summing marked chains and using the fresh encoding estimate gives contribution at most

    3444x E[A]/(N(1-x)).

This includes inversions precomputed before the encoding query. It does not assign all inversion work to the period after preparation or assume that preparation and a successful inversion are independent.

Consequently the event consisting of a nonreference encoding equal to its canonical D_p or a backward witness for any distinct valid codeword has probability at most

    [c(x)+82x/(1-x)] E[Q]/N
        + [1+3444x/(1-x)] E[A]/N.

For x<=2^-12 both coefficients are below 15/8. At x=2^-12, they are respectively 52281827327/34342963200 and 359/195. The expressions are increasing for 0<=x<1, so checking that endpoint suffices.

In the slightly smaller range x<=3*2^-14, both coefficients are below 7/4. This range overlaps the range where the paid quadratic primitive bound can absorb the proposed coverage excess. It is therefore sufficient for the new two-regime closing argument.

This is an actual-execution OTS witness bound with separate expected query costs. It is stronger than a bound that adds a q-budget estimate for each event class. It still requires a deterministic reduction distinguishing these witnesses from collisions above the canonical frontiers and from forgeries against the FTS component. Revealing all canonical OTS signatures for analysis does not establish security of the whole scheme by itself.
