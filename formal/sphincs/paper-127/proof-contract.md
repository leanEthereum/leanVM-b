# A concrete proof contract for 127-bit SUF

This review keeps the original scheme and works on paper. It separates the numerical closure from the experiment transfers needed to justify it. The public 127-bit theorem is still missing. The current branch contains stopped full and near coverage estimates for the original signer; those estimates alone do not prove strong unforgeability. No Lean source is changed by this review.

Subsequent formalization establishes the proposal-prefix bound of 2^-704 in [CertificateProposalPrefixException.lean](../SphincsSecurity/Proof/CertificateProposalPrefixException.lean), using the exact geometric moment and its conserved potential in the original certificate monitor. [CertificateProposalPrefixPersistence.lean](../SphincsSecurity/Proof/CertificateProposalPrefixPersistence.lean) connects the active stop rule to that terminal event: once detected, an overflow persists. The other exceptional-stop transfers and the cryptographic reductions below remain obligations.

The cached-index component is now bounded in [CachedIndexExcessGame.lean](../SphincsSecurity/Proof/CachedIndexExcessGame.lean). A second-moment reserve proves q/2^170 for the original sampled game's ever-raised exception flag, with an exact projection to its original verdict. This suffices for the final arithmetic; the allowance below is updated accordingly. Its joint transfer with the other exceptions to the certificate monitor remains open.

The recommended route remains the fixed-word, two-range argument. Its constants already suffice. The next substantial milestone should be a security inequality for the original game on an entire budget range, with the monitoring exceptions and experiment transfers discharged. More accurate occupancy constants are unnecessary.

**1. Freeze the target and the accounting.** Put N=2^128, S=2^24, I=2^26, L=1024 and x=q/N. The target is Pr[original SUF win]<=2x for every admitted adversary and positive whole-experiment hash budget q. Key generation, failed and successful signing, adversarial hashing, and final verification all consume this same q. Uniform sampling does not. Preserve independent sampled secrets, finite retry exhaustion, Option failures, the original final signing log, and novelty of the entire message/signature pair. At q>=N/2, probability at most one proves the target.

For 1<=q<N/2, fix

    beta = 1537/1024,
    M = beta*S + 131072 + 13 = 25313293,
    delta = 2^-13,
    x_* = 3/2^14,                 q_* = 3*2^114,
    epsilon(q) = q/2^222 + q/2^170 + 2^-700.

There are three principal inequalities to establish. Their costs and events must refer to specified presentations of the same original execution, rather than unrelated experiments with individually favorable estimates.

| Obligation | Required endpoint |
| --- | --- |
| Coverage | E[C_full] <= (3/(2N))*E[A_cov] + delta*x, and E[C_near] <= 557*x. The near estimate must also hold in each supported forced-first-guess law. |
| Large budgets | Pr[B] + (3/(2N))*E[A_B] <= 2x-(3/4)*x^2, with A_cov<=A_B pathwise and SUF win implying B, a bounded exception, or C_full>=1. |
| Small budgets | A decomposition into completed OTS witnesses, structural matches, full coverage, and useful FTS guesses, retaining disjoint actual query allocations until the final addition. |

**2. The coverage arithmetic has enough room.** Complete the accepted signing indices into an auxiliary uniform word of fixed length M using the exact proposal bridge. This changes no original response. If Z_i is its occupancy at index i, set

    R = sum_i Z_i^14 / 2^48,
    R_near = 14*sum_i Z_i^13 / 2^38.

For distinct indices i,j, the mixed falling-factorial identity is

    E[(Z_i)_a (Z_j)_b] = (M)_(a+b)/I^(a+b)
                       <= E[(Z_i)_a]*E[(Z_j)_b].

Expand powers with nonnegative Stirling coefficients. This gives Cov(Z_i^14,Z_j^14)<=0; independence of the occupancies is unnecessary. With T_d(z)=sum_a StirlingSecond(d,a)*z^a and M/I<19/50,

    mu = E[R] <= 2^-22*T_14(19/50) < 1/5,
    Var(R) <= 2^-70*T_28(19/50) < 13/25000,
    E[R_near] <= (14/2^12)*T_13(19/50) < 557.

The elementary inequality (y-a)_+<=y^2/(4a), for a>0, now gives

    E[(R-3/2)_+] <= Var(R)/(4*(3/2-mu))
                 < (13/25000)/(4*(3/2-1/5))
                 = 1/10000 < delta.

These are finite rational calculations. Their exact checks are in variance-route-checks.py. The adaptive step is separate: the same terminal word must dominate every predictable creation price through its conditional completion law. A target may have been queried before its covering signatures, and the adversary may spend its remaining budget after observing an unusually favorable signing history. Replacing an expectation of a product by the product of its expectations would lose precisely this case.

The certificate potential pays ordinary creation at rate 3/(2N) per actual message call and pays the excess using the remaining total budget and E[(R-3/2)_+]. It banks a completed certificate before applying a post-invocation stop. Failed responses contribute no signing view; a selected digest is still retained analytically when a later encoding fails. Each certificate excludes successful views at its own message/randomizer input.

There is an additional interface requirement for the near estimate. The 14 omitted-coordinate ledgers must be projections of one execution with the same stopping rule. A sum of expectations from 14 monitors whose stopping decisions inspect different banks is not automatically the expectation of a single near-certificate count. Choose a stop depending only on their common projected state and prove the projection identities.

**3. All three numerical exceptions admit short paper bounds.** The argument needs an event that includes every exceptional first stop, not just a favorable final cache distribution.

For the cached-index bound, let p=1/(LI)=2^-36, let J be the cache's number of distinct inputs, and let C_i be its number of admissible message inputs at index i. Set X_i=C_i-p*J and U=sum_i max(X_i,0)^2. A fresh message input changes each X_i by Bernoulli(p)-p marginally. The elementary centered Bernoulli inequality gives E[U_after | history]<=U_before+I*p. A fresh non-message input decreases every X_i, and a repeated input leaves them unchanged. Both satisfy the same bound. Initially U=0. Stopping at the first exceptional cache and using the remaining-budget reserve U+(q-t)*I*p yields

    Pr[exists cached prefix and i: X_i>2^80]
      <= I*q*p/2^160 = q/2^170.

Because J<=t after t actual hash calls, an actual monitor violation C_i>p*t+2^80 implies X_i>2^80. This stronger cache event needs no extra counter in the exception monitor. The argument does not assume independence between different indices or adaptive query choices. A fourth moment can give the smaller q/2^237 paper allowance, but it is unnecessary for closing 127 bits.

For message deficits, write D_m for the number of cached randomizers for message m minus L times their admissible count. A fresh proper message cell changes its one score by X=1-L*Bernoulli(1/L). Thus E[X]=0, E[X^2]<=L, |E[X^3]|<=L^2 and E[X^4]<=L^3. Using 4*L^2*|D|<=2*L*D^2+2*L^3, the expected increment of D^4 is at most 8*L*D^2+3*L^3. Since E[sum_m D_m^2]<=L*t,

    E[sum_m D_m(q)^4] <= 4*L^2*q*(q-1)+3*L^3*q.

The sum is a nonnegative submartingale. Its maximal inequality at 2^372 bounds any message crossing D_m>2^93 by less than q/2^222. Summing the moments before applying the inequality avoids a factor for the number of possible messages. The existing formal deficit estimate is stronger than this paper allowance.

For proposal overflow, the auxiliary block lengths G_s are independent geometric variables on {1,2,...} with acceptance 1/beta. Extra unused blocks may be sampled for this calculation; an adaptive prefix is included in the event over all s<=S. Set

    t = 129/128,
    u = E[t^G] = 132096/130559,
    B_0 = 3*S/2 + 131072 = 25296896,
    K_s = G_1+...+G_s,
    V_s = t^K_s * u^(S-s).

Then V_s is a nonnegative martingale with E[V_s]=u^S. Because beta>=3/2 and u^2>=t^3, a prefix with K_s>beta*s+131072 satisfies

    V_s^2 >= t^(3*s+262144)*(u^2)^(S-s)
           >= t^(3*S+262144) = t^(2*B_0).

The finite maximal inequality therefore bounds the overflow probability by u^S/t^B_0. No logarithms or asymptotic tail theorem are needed. The following rational certificates suffice:

    (u^2/t^3)^1024 <= 16/15,
    t^128 >= 27/10,
    (((16/15)^8)/(27/10))^16 <= 2^-11.

Indeed,

    u^S/t^B_0 = (((u^2/t^3)^1024)^8/t^128)^1024 <= 2^-704.

These certificates were also checked by exact rational arithmetic during this review. Their exponents are analytical constants, not empirical estimates. Together the three events fit inside epsilon(q).

The remaining stop classification is deterministic but mandatory. Until the first stop, cached rows are bounded by actual spent hash calls, successful signing digests remain in the consistent message cache, and spent calls are bounded by q. A pre-invocation minimum-cost gate cannot fire on an admitted execution. A signing-cap stop cannot discard a winning execution because the original final verdict rejects a longer log. After accounting for these invariants, every other first stop must be one of the three bounded events, or the explicitly added primitive stop B. Finish and bank an active signing invocation before acting on its post-state exceptions.

**4. The large-budget saving comes from a joint estimate.** Give the analyst an upward-closed cut of the canonical graph: OTS frontiers and values above them, FTS leaf hashes and authentication nodes, and exact reference encoding data. Keep OTS values below the frontiers and undisclosed FTS secrets hidden. The full function tables and private honest hash inputs are not part of this advice. The graph must have the exact original distribution, with each distinct serialized structural domain programmed at its single canonical input. Repeated honest reads use that same row.

Let B be the first external primitive match, including verification. Before B, a query has at most two equality tests against distinct hidden coordinates. After r such probe rounds, each hidden coordinate has at least N-r unexcluded candidates. The posterior proof must establish a product of uniform laws on those sets. A two-test hazard is then at most

    h_r = 1-((N-r-1)/(N-r))^2.

Message calls do not exclude hidden candidates. Pay them at rate c=3/(2N). Paying every non-probe hash call at that rate only enlarges the bound. For the scalar process with at most q slots, moving a paid slot before a probe increases its expected collected payment. Its optimal surviving schedule therefore has a paid prefix of a slots, giving

    Pr[B]+c*E[A_B]
      <= max_(0<=a<=q) [3*a/(2*N)+1-((N-q+a)/N)^2]
      <= U(x) = 2*x-x^2+max(x-1/4,0)^2
      <= 2*x-(3/4)*x^2.

Replacing actual hazards by their upper bounds requires the surviving continuation value to be below one; this is part of the scalar proof in paid-probe-quadratic.md. The posterior must use the number of probe rounds for exclusions, while the budget still counts every original hash call.

Attach coverage on the same original run and stop it additionally at B. Its possibly earlier exception stops give A_cov<=A_B pathwise. There is no need to expose coverage's private state in the primitive history. Backwards tracing of accepting verification must show that, without B, every structural field is canonical and every supplied FTS secret was disclosed. If the message/randomizer input had a successful signing response, the entire signature equals that response and fails strong novelty. Otherwise it gives a full certificate with own-input exclusion. This is the required deterministic SUF implication, including counter exhaustion and every consumed signature field.

It follows, after those transfer obligations are established, that

    Pr[original SUF win] <= 2*x-(3/4)*x^2+delta*x+epsilon(q).

At x>=x_*, the available margin per x is

    (3/4)*x-delta >= (3/4)*(3/2^14)-2^-13 = 2^-16.

For every q>=1, epsilon(q)/x<=2^-94+2^-42+2^-572<2^-16. This closes the entire large-budget range.

**5. Small budgets need completed witnesses and shared costs.** An individual hidden-value match is too broad an event here: its leading coefficient can already consume the full 2x. Use the target-sum constraint. A distinct valid OTS word either moves one unit between two chains, lowers one chain by at least two, or lowers two distinct chains. Count the queried paths that make these changes usable, together with the encoding preparation needed for the one-unit case.

The projected chain likelihood is the critical interface. For a uniform secret S and random functions H, let Y be the endpoint and W(H,Y) the number of starting values reaching Y. The real density relative to an independent endpoint is W only after forgetting S and all private prefix evaluations that expose it. On the full (S,H,Y) space the density is instead N times the indicator that S reaches Y. Every charged cost, witness, and stopping decision must factor through the projection before using W. On a partial external table the projected likelihood satisfies w>=1-Q_i/N>=1-x. This lets each chain's ideal allocated cost be compared with its real cost without multiplying the answer by the number of chains. Ideal endpoint hybrids need an explicit q cap, since an ideal endpoint need not admit a compatible secret.

Retain the disjoint real query counts Q for OTS prefix inputs, A_enc for nonreference encoding inputs, A_str for the other structural inputs, and A_msg for actual message calls. The required OTS and structural estimates have coefficients

    c_Q(x) = ((3/2)+4*x+2*x^2)/(1-x)
             +4*x/(1-x)^2+82*x/(1-x),
    c_enc(x) = 1+3444*x/(1-x).

Encoding-before-inversion and inversion-before-encoding must both be covered. Their probabilities may be analyzed with different information histories, but the resulting expectations must be for these same real costs. Full private cache cardinality need not itself be retained in the OTS projection: its administrative guard is identically satisfied on reachable original prefixes and must be eliminated using that invariant. Secret-dependent cache-hit flags must not be exposed as extra observations.

The FTS estimate separates alternative preimages, already charged to A_str, from true guesses of undisclosed secrets. Two distinct true guesses cost at most x^2/(2*(1-x)^2). A single useful guess also needs a near certificate. To bound this adaptively, defer each undisclosed secret uniformly over its unexcluded candidates. For each slot j, force earlier eligible guesses to miss and the eligible guess at j to hit. The corresponding real first-hit branch has likelihood

    L_j = p_j*product_(t<j)(1-p_t) <= 1/(N-q).

Each forced transition must have positive original conditional probability. The forced law retains the original path budget and fresh-message kernel. Apply the near-certificate estimate in that law, not merely in the original law, then sum over j. This yields 557*x^2/(1-x), allowing the certificate to precede or follow the guess. Attach auxiliary rejected proposal values only after defining the forced projected law. Its coverage argument may use the current deferred state, not a fully revealed secret key selected using future events.

The complete required small-budget inequality is

    Pr[original SUF win]
      <= c_Q(x)*E[Q]/N + c_enc(x)*E[A_enc]/N
         +E[A_str]/N+(3/2)*E[A_msg]/N
         +557*x^2/(1-x)+x^2/(2*(1-x)^2)
         +delta*x+epsilon(q).

Use Q+A_enc+A_str+A_msg<=q before simplifying the coefficients. All coefficient functions increase on 0<=x<1. At x=x_*, exact arithmetic gives

    max(c_Q(x_*),c_enc(x_*),1,3/2) < 131/80,
    557*x_* /(1-x_*)+x_* /(2*(1-x_*)^2) < 9/80.

Thus Pr[original SUF win]<=(7/4+delta)*x+epsilon(q)<2*x throughout the small-budget range. This range overlaps the large one at q_*; the arithmetic does not require a further improvement in the cryptographic constants.

**6. Order the remaining work by proof risk.** First establish the exact canonical graph presentation and the deterministic SUF decomposition against arbitrary serialized queries, finite failures, and the complete signature layout. Second specify coverage using the message cache and successful views, prove its common-stop projection, and discharge the actual exceptional-stop classification. Third combine the hidden-label posterior, scalar payment, and coverage to obtain the original-game theorem for q_*<=q<N/2. Fourth establish the projected OTS allocation and supported forced-FTS transfer, then obtain the original-game theorem for 1<=q<=q_*. Finally combine these with the trivial range and audit the unchanged public statement and theorem dependencies.

The decisive review questions are whether the primitive advice preserves the hidden-label posterior, whether every OTS statistic survives the required projection, and whether near coverage applies to the forced laws with their original costs. These are mathematical requirements, not assumptions to add to the final theorem. The scalar optimization, moment estimates, and exception constants have enough margin once those requirements hold. The plan is credible, but the missing concrete transfers prevent calling 127 bits proved.
