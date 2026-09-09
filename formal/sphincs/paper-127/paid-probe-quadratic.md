# A quadratic primitive bound that pays for message queries

This note gives the paper construction and induction for the original experiment in Statement.lean, followed by its large-budget assembly with [stopped coverage](cached-target-forecast.md). It strengthens the earlier total-time bound by counting only probe rounds as failed guesses. All actual hash calls still consume the original q. This is a paper argument, not a new Lean theorem; the small-budget completed-witness transfer remains separate.

Write N=2^128 and x=q/N, with 1<=q<=N/2. Let B be the first external primitive match defined below, including matches during final verification. Let A_B count original message-domain hash calls before B or original termination. We establish

    Pr[B] + (3/(2N)) E[A_B] <= U(x),
    U(x) = 2x-x^2 + max(x-1/4,0)^2 <= 2x-(3/4)x^2.

The primitive experiment has no cache, proposal, or signing-cap stop. These stops belong to coverage, whose message count will be bounded pathwise by A_B. The original verdict always uses the complete original signing log.

## Exact finite canonical graph

Fix the sampled public parameter. A relevant domain is identified by its actual 32-byte prefix: the 16-byte tweak followed by the parameter. Canonical graph nodes use only the geometrically valid addresses. For an OTS address p=(lay,tree,leaf), the ranges are

    lay=0,1,2;  h_lay=12,7,7;  a_lay=0,12,19;
    tree < 2^a_lay;  leaf < 2^h_lay.

The chain position is 8*chainIndex+step, with chainIndex<42 and step<7. A hypertree internal node at level j has 1<=j<=h_lay and nodeIdx<2^(h_lay-j). An FTS instance has index<2^26, tree<14, leaf<1024, and internal levels 1 through 10 with the corresponding node ranges. These are finite sets. All other sampled secret-key coordinates retain their original independent distributions.

Distinct canonical nodes have distinct serialized tweaks. Different kinds have distinct tags; within a kind, the displayed field ranges fit the serialized widths and distinguish the nodes. Repeated honest evaluation of one node uses its same row. It is not true that every honest evaluation has a new tweak, and no such premise is used.

Classify arbitrary adversarial requests by bytes. An out-of-range typed address whose 32-bit fields wrap to a valid prefix accesses that valid domain and receives its tests. A malformed payload at a valid structural prefix is a noncanonical row. Inputs with foreign parameters, nonzero reserved bytes, or prefixes outside the finite graph and encoding/message domains are auxiliary rows. This classification does not presume that adversarial inputs came from a typed constructor.

The structural payload lengths are 16 bytes for a chain or FTS leaf, 672 for an OTS leaf, 32 for a binary parent, and 224 for FTS roots. Encoding uses 16 message bytes and 4 counter bytes. A signing message input has 16 randomizer bytes, 16 root bytes, and 32 message bytes. Fixed-width serialization and concatenation are injective on these fields. All payloads at the proper message prefix can be counted as message calls; counting malformed ones only enlarges the payment.

For each valid OTS address p, its canonical message M_p is fixed by the non-encoding structural graph. At an upper layer it is the child tree root with tree index tree*2^h_lay+leaf; at the bottom it is the FTS key at that index. In particular M_p has no dependence on the encoding or message oracle. Let C be the 42-digit code with digits in 0..7 and sum 191. Its low 128-bit encodings are unique because bits 63 and 127 are required to be zero. Put v=|C|/N and T=2^32.

Conditional on all non-encoding data, the canonical-message counter rows are independent uniforms. Thus the least valid counter J_p and its word D_p have

    Pr[J_p=j,D_p=d] = (1-v)^j/N,       0<=j<T, d in C,
    Pr[J_p=none,D_p=d] = (1-v)^T/|C|.

The second line adds an independent dummy word on exhaustion. Across p these pairs are independent, and they are independent of all non-encoding data. They can therefore be sampled first. Conditional encoding rows are generated as follows: canonical-message counters before J_p, or all such counters on exhaustion, have independent uniformly invalid low outputs; the reference row has exactly the encoded D_p; all unrestricted rows have independent uniform low outputs. All high 128 bits are independently uniform and memoized. This is the conditional-table identity in [reference-frontier-transfer.md](reference-frontier-transfer.md). It does not reveal the validity of unrestricted rows or reject exhausted keys.

Now sample the original independent secret leaves and an independent uniform low output at every distinct valid canonical structural node. Process the graph in topological order, programming each node's domain at the payload of its canonical children. Sample its high output bits independently. Other rows remain lazy uniform 256-bit values. Conditional on the children, the node's input is fixed in a domain not used by another canonical node, so this is exactly its ordinary random-function law. Induction gives the original joint law of secrets, graph values, and all externally observed rows. Equal numerical labels at different coordinates are allowed throughout. There is no birthday conditioning or extra graph-collision probability.

Only the finite canonical graph and finitely many requested auxiliary rows need be sampled. This construction is an alternative sampling order, not extra work performed by the original algorithms. Run actual key generation, signing, adversarial calls, and verification against this consistent oracle; retain every original hash call, including repeated reads. Erasing the graph advice recovers their original joint outcome and cost law.

## Public cut and primitive history

For each OTS chain write X_(p,j,k), 0<=k<=7, and d=D_p(j). Reveal all values with k>=d. Keep all positions k<d hidden. Reveal every OTS leaf and hypertree node, every FTS leaf hash and internal/root node, the canonical M_p, J_p and D_p, and the public key. Keep each FTS secret hidden until a successful original response discloses that coordinate.

Conditional on this advice, the hidden coordinates initially have a product of independent uniform laws. The advice is an upward-closed cut: every canonical multi-input structural row has public children, while the hidden rows are unary chain steps or FTS leaf hashes. Full function tables and honest secret-dependent query inputs are not disclosed. A hidden coordinate remains hidden even if its numerical value happens to equal a disclosed value elsewhere.

Let G record the advice, external query bytes and full replies, the original signer's message queries and full replies, returned signing responses, and the original hash count and control stage. Independent coins may be revealed as they are used. Maintain a separate table of externally observed rows. In particular G does not expose the global cache's private entries or cache-hit flags. A later external query to a row previously computed only inside signing must still be tested as a guess. No proposal values, proposal lengths, terminal Poisson variable, or coverage stopping flags are needed in G.

The original signer's control flow discloses no additional hidden-label information. Its digest loop depends on the recorded message cells and independent randomizers. Once an index is selected, ftsOpen has a fixed shape. Each layerMessage is its public canonical M_p; its finite encoding search is determined by J_p and D_p. Its successful chain lengths are determined by D_p, and its authentication paths have fixed shapes determined by the index. All three signLayer computations are performed before traverseOption decides whether to return none. Thus the full hash count and failure mask depend on the exposed data and message trace, not on the numerical values of hidden secrets.

A successful response reveals its selected FTS secret coordinates and otherwise only data already public at the cut. Its selected index and leaves, and the decision to return a signature, are determined before examining those secrets' values. Disclose these coordinates one by one and retire them from the hidden family. Repeated disclosures return the same value. Digest exhaustion and later encoding failure disclose no secrets, even when their internal computations evaluated secret-dependent rows. Honest structural reads remain private and all consume their actual hash costs.

## Surviving transitions and posterior

Before B, let U_v be the unexcluded values of hidden coordinate v. Conditional on G and survival, the induction invariant is the product of uniforms on the U_v. The following external tests define B and specify the transition kernels needed to prove the invariant.

| External request | Tests and surviving update |
| --- | --- |
| A correctly sized OTS input at a hidden chain position | Test its candidate against the canonical child. A hit is B. A miss removes that candidate from the child's U. At a fresh noncanonical row, test the low answer against the canonical parent. A match is B; a miss removes the answer from the parent's U when the parent is hidden. |
| An FTS leaf input with undisclosed secret | Apply the same input test, then test a fresh noncanonical low answer against the public leaf hash. |
| A canonical input whose children are all public | Return its memoized canonical answer; no test is needed. |
| A noncanonical structural row with public children and parent | A fresh low answer is tested against its public canonical output. A match is B. |
| A malformed unary payload | It cannot equal the canonical child payload; only the output test applies. |
| An unrestricted nonreference encoding row | Test its fresh low answer against the encoded D_p. A match is B. |
| A restricted invalid encoding row or the reference row | Return its conditional-table answer. Invalid rows cannot match a valid D_p; a reference read is allowed. |
| A message row or an auxiliary domain | Return the ordinary memoized or fresh answer; there is no primitive test. |

A surviving repeated external row needs no new test: the candidate and output were already excluded, or the row was an allowed public canonical read. If its secret has since been disclosed, that disclosure cannot undo an earlier inequality. A fresh public canonical row may reveal its previously private high bits, which are independent of all hidden coordinates. An ordinary auxiliary answer may later be used as a guess in another domain; the test is charged when that later request occurs.

Here is the exact normalization for the only two-hidden-coordinate case. For an input candidate z at child u, a fresh low answer y, and hidden parent v, the surviving joint mass is proportional to

    product_w [1_(x_w in U_w)/|U_w|]
        * 1_(x_u != z) * (1/N) * 1_(x_v != y).

The coordinates u and v are distinct chain positions. Conditional on the observed y and survival, normalization gives uniforms on U_u without z and U_v without y, with all other factors unchanged. It remains valid when z=y or two coordinate values coincide. If the parent is public, the final indicator restricts y alone. Independent high bits contribute another unchanged factor. A disclosure selected without inspecting the hidden value simply conditions on that coordinate and removes its factor. These identities, together with the control-flow check above, prove the posterior invariant by induction over the complete original execution until B.

B is an analyst's first-match flag for external adversarial or verification requests. It includes matches that might never become useful in a forgery. The original adversary receives no flag. Honest canonical computations never trigger it: the signer reads canonical structural rows, invalid encoding prefixes, and reference rows only, besides its probe-free message calls.

## Scalar bound using the number of probes

Call each external primitive-query slot a probe round, permitting dummy rounds for repeats or allowed public reads. A round removes at most one value from each of at most two distinct hidden coordinates. After r probe rounds, every active U_v therefore has size at least N-r. A true input hit has conditional probability at most 1/(N-r). On a miss, a fresh off-canonical low answer is uniform; its match probability against its hidden or public target is 1/N, which is at most 1/(N-r). Hence the next round's conditional hazard is bounded by

    h_r = 1-((N-r-1)/(N-r))^2.

Message calls and honest internal calls add no exclusions. Give every non-probe hash round artificial reward c=3/(2N), including these honest calls. This dominates the reward c*A_B for actual message calls. Free uniform sampling and allowed disclosures earn nothing and occur between hash slots. There are at most q hash slots by the original whole-experiment bound; early termination may be padded with paid slots for an upper bound.

Consider the scalar upper process with r probes already used and k hash slots remaining:

    V(r,0)=0,
    V(r,k)=max(c+V(r,k-1), h_r+(1-h_r)*V(r+1,k-1)).

The failure payoff is one. For fixed upper hazards, a deterministic optimal surviving policy is a sequence of paid and probe rounds. Moving a paid round before a probe preserves the sequence of probe hazards and increases the probability that the reward is collected. Thus a paid prefix is optimal, and telescoping gives

    V(r,k) = max_(integer 0<=a<=k)
        [3a/(2N)+1-((N-r-k+a)/(N-r))^2].

It remains to justify replacing the actual hazards by upper hazards. At every reachable state r+k<=N/2, each schedule's survival probability satisfies

    ((N-r-k+a)/(N-r))^2 >= (1/2+a/N)^2 > 3a/(2N).

The strict inequality follows from (1/2+s)^2-(3/2)s=(s-1/4)^2+3/16. Therefore V(r,k)<1. Increasing the failure hazard now increases the value, since the failure payoff one exceeds the surviving continuation value. Backward induction bounds the actual adaptive process by this scalar recurrence; no independence of its action choices is assumed.

At r=0,k=q, put s=a/N and relax the integer maximum. The expression is

    2x-x^2+(2x-1/2)s-s^2,       0<=s<=x.

Its maximum is 2x-x^2 for x<=1/4, and (3/2)x+1/16 for 1/4<=x<=1/2. This is U(x). In the second range the difference between 2x-(3/4)x^2 and U(x) is (3/4)(1/2-x)(x-1/6)>=0; the first range is immediate. Consequently the original augmented execution satisfies

    Pr[B] + (3/(2N)) E[A_B] <= U(x) <= 2x-(3/4)x^2.

## Exhaustive strong-forgery implication

Assume the original verifier accepts and no B occurred anywhere in the run, including verification. Trace its computations backwards from the canonical public root. If a computed canonical Merkle parent had a noncanonical child tuple, that hash would be a noncanonical output match, hence B. The injective fixed-width payload implies that its computed child and supplied sibling are both canonical. Repeating down the path reaches the canonical OTS leaf, whose 42 recovered chain endpoints must therefore all be canonical.

At an OTS chain, trace backwards from its canonical endpoint through every step the verifier performed. A noncanonical input producing a canonical parent would again be B, so every walked value is canonical. Let e_j be the digit decoded by verification and d_j the reference digit. If e_j<d_j, verification queries a hidden canonical child below the disclosed frontier, which is an input match B. Thus e_j>=d_j for every j. Both words have sum 191, forcing e=d componentwise. This also handles e_j=7: the endpoint comparison itself fixes the supplied value when no step is performed.

The valid encoding uniquely fixes the low 128-bit digest. Any input other than the reference (M_p,J_p) that yields this encoded D_p is an encoding match B. Therefore the verified message and counter are the canonical M_p,J_p, and the supplied chain values are exactly the reference frontiers. If J_p=none, every canonical-message counter is invalid and there is no reference input, so acceptance without B is impossible. Exhaustion is retained, not charged as an exceptional key.

The concrete treeIndexAt and leafIndexAt layer links identify the canonical top-layer message with the actual middle tree root, then the middle-layer message with the bottom root, then the bottom-layer message with the FTS key at the digest's index. Apply the same backwards argument at each layer. At the FTS roots hash, the 14-element roots vector must be canonical. Trace each ten-level authentication path to its canonical leaf hash. A different secret producing that hash would be a noncanonical output match. The true secret, if still undisclosed, would be an input match. Thus every accepted FTS secret was previously disclosed by a successful original signing response at that index and leaf.

This fixes every signature component besides its message-bound randomizer: all 14 secret values, 140 FTS siblings, three counters, 126 chain values, and 26 hypertree siblings. The concrete path offsets partition all 26 authPath entries, as expressed by authPath_exhausted and signaturePath_flattenPaths; there is no unused field that could yield a different accepted signature. All FTS paths and all 42 chain endpoints per layer are likewise consumed.

Suppose the forgery's message/randomizer input was selected by an earlier successful response. Equality of its fixed-width input implies the same message and randomizer, and oracle consistency implies the same index and leaves. The canonicality just established fixes every remaining field to that earlier signature. The forgery is then in SigningTranscript.Contains and cannot win SUF. Consequently a genuine strong forgery with no B has no successful response at its own input, and all 14 required leaves come from successful responses at other inputs. Failed responses contribute none. This is exactly a full target certificate with own-input exclusion. Its digest is in the message cache at the latest when final verification queries it.

## Combining differently stopped counts on one original run

Attach the coverage construction to this same original graph execution. Let its base stop be original termination, the signing cap, or its cache, deficit, or proposal exception. Additionally stop it at B. Complete an active signing record and bank first certificates before applying its post-record guards, as in the coverage proof. B cannot occur inside honest signing, and an external non-message B query adds no message charge. Thus, if A_cov is its monitored message count,

    A_cov <= A_B

on every augmented execution. Erasing its auxiliary variables preserves the original graph execution and A_B. It is unnecessary to expose its stops or proposal variables in G, or to prove that its stopped count equals A_B. Coverage may use its richer history and even the graph's private state: fresh unqueried message cells remain uniform there, since the graph and reference advice involve only other domains.

The coverage theorem and its exceptional allowance give

    E[C_full] <= (3/(2N)) E[A_cov] + delta*x,
    Pr[E_exc] <= epsilon(q),
    delta=2^-16,
    epsilon(q)=q/2^222+q/2^237+2^-700.

An original winning run cannot exceed the signing cap because the final verdict uses the full original log. With neither B nor a bounded exception, its monitor remains active through the relevant verification query; the previous section supplies a banked full certificate. Therefore

    {original SUF win} subset B union E_exc union {C_full>=1},
    Pr[original SUF win]
        <= Pr[B] + E[C_full] + epsilon(q)
        <= Pr[B] + (3/(2N)) E[A_B] + delta*x + epsilon(q)
        <= U(x) + delta*x + epsilon(q)
        <= 2x-(3/4)x^2 + delta*x + epsilon(q).

For x>=2^-15, equivalently q>=2^113, the margin satisfies (3/4)x-delta>=2^-17. Since q>=1,

    epsilon(q)/x <= 2^-94+2^-109+2^-572 < 2^-17.

This closes the paper large-budget range 2^113<=q<2^127 for the unchanged experiment. For q>=2^127, probability at most one suffices. The range below 2^113 still needs the allocated OTS witness transfer and the FTS first-guess comparison from [the plan](next-proof-plan.md). The local table and scalar checks in reference-and-paid-checks.py are finite consistency checks; they do not certify this adaptive argument or replace its future Lean proofs.
