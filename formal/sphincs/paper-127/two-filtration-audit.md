# A paper audit and revised construction for 127 bits

This note audits the route at source commit 86c5e4e8. It makes no changes to Lean code. The target is the original strong-unforgeability game, including independent secrets, finite retry failures, and its whole-experiment hash budget. The numerical closing argument in next-proof-plan.md is sufficient. The main improvement here is to separate the information histories used by coverage and by the primitive analysis. They need the same stopped execution and cost variable, but do not need the same filtration.

The resulting plan is a candidate proof with explicit remaining original-game obligations. The conditional-expectation calculations below do not establish those obligations merely by stating them.

## Target and the source of the missing bit

Put N=2^128, I=2^26, L=1024, S=2^24, and x=q/N. Here L is both the forest leaf count and the inverse message-digest admissibility probability. The target is

    P[strong forgery] <= 2x.

Budgets q>=N/2 are trivial. The difficulty is the coefficient for q<N/2. A primitive estimate of 2x followed by any positive additive coverage term cannot close. Improving only the occupancy estimate leaves this obstruction. The plan instead uses useful completed witnesses for small x, and a primitive probability bound that already pays message-query costs for larger x.

Use delta=2^-16, epsilon(q)=q/2^222+q/2^237+2^-700, and the split x_0=2^-15, or q_0=2^113. No change to the scheme, signature cap, failure behavior, or security definition is needed for this split.

## One execution, two information histories

Start with the exact canonical-graph augmentation described in reference-frontier-transfer.md and paid-probe-quadratic.md. It must preserve the original joint law. The primitive analysis exposes canonical OTS frontiers and forward labels, public structural nodes, FTS leaf hashes, and the conditional reference-encoding information. It keeps undisclosed FTS secrets and OTS labels below their frontiers hidden. Honest internal evaluations retain their original hash costs while their secret-dependent inputs remain private.

Independently add a terminal length J~Poisson((19/50)I) and geometric block lengths G_1,...,G_S with success probability 1/beta, where beta=1537/1024. They may be sampled on the underlying probability space in advance. Reveal J initially and G_s only at the end of signing invocation s. Do not reveal future block lengths to the coverage history.

Let tau_base stop on a cache or message-deficit exception, the initial short-J exception, or a geometric prefix exception. It also stops with loss before signing request S+1. A condition encountered inside a signing invocation takes effect at its completed boundary, and all actual calls of that invocation remain counted. Define the prefix exception using only

    G_1+...+G_s > beta*s+131072.

It does not inspect the values of any rejected proposal indices. In the large-budget argument additionally stop at B, the first primitive match, and write tau_large=min(tau_base,B). The small-budget argument uses tau_base. The two budget ranges need not have identical stopping times.

Use two histories on this probability space:

* The primitive history G records the exposed graph information, adversary observations, message-query inputs and answers, returned signing responses, actual costs, primitive test flags, J, and completed block lengths. It omits secret-dependent internal non-message inputs and rejected proposal values. Its hidden-label invariant is needed only up to B.
* The coverage history F, at completed macro boundaries and external hash steps, additionally records consumed proposal values and any current environmental state needed for its transition law. It can contain private information that is unsuitable for the primitive argument, provided it does not inspect unqueried message cells or unused proposals. In the original lazy-oracle experiment, the current secret key and private cache are permissible for coverage. In a forced-secret experiment, use its current deferred state instead of revealing secrets that will be chosen by future transitions.

At common boundaries F can refine G. During an honest signing invocation the primitive proof can account for individual hash calls, while coverage uses one completed macro transition. There is no requirement for an unused-proposal assertion at an intermediate signing hash call.

The certificate count C and actual message-call count A are variables of the stopped execution. If coverage, proved using F, gives

    E[C] <= (3/(2N)) E[A] + delta*x,

and the primitive analysis, proved using G, gives

    P[B before stopping] + (3/(2N)) E[A] <= 2x-(3/4)x^2,

the two inequalities combine directly. Conditional expectations have already been integrated out. Requiring the hidden labels to remain independent conditional on the richer coverage history would impose an unnecessary additional condition.

## Why erasing rejected values is sufficient

This is an abstract kernel calculation, allowing the next signing-index distribution to depend on private state. Fix a pre-state h and the exact distribution K_h of a completed signing record omega. Retain its selected index i(omega) even after a later encoding failure. Add an independent uniform index only when the digest loop exhausts. Suppose

    p_i = P[i(omega)=i | h] <= beta/I.

After canonical graph information has been exposed, K_h is the actual conditional signing kernel. Its non-message oracle answers need not have the ordinary unconditioned lazy-oracle law. The index cap must be derived from the unchanged message-only digest loop; it is not legitimate to replace the entire conditional signer by an unconditioned one. The bridge below accepts this general K_h.

Set a=1/beta and r_h(i)=(beta/I-p_i)/(beta-1). Run the original signing kernel. Independently conditional on h, sample G with P[G=k+1]=a(1-a)^k and then k rejected indices with law r_h. For a word u of length k,

    P[omega,u | h] = K_h(omega) a product_j (1/I-a*p_(u_j)).

Summing over all words of length k gives

    P[omega,G=k+1 | h] = K_h(omega) a(1-a)^k.

Thus erasing rejected values preserves the actual signing record and adds a geometric length independent of that record and the pre-state. This holds even if r_h depends on hidden information. Iterating the identity gives the original execution augmented by independent lengths, then stopped by the stated rules. This projected law is all the primitive proof needs.

For comparison, rejected values are not automatically harmless in an arbitrary kernel. With I=2, beta=3/2 and a hidden fair bit theta, take p=(3/4,1/4) when theta=0 and p=(1/4,3/4) when theta=1. Then a single rejected value determines theta, although G is independent of theta. This is an abstract example, not an attack on the concrete signer. It explains why hiding the rejected values is a more general interface than requiring them to reveal nothing about private state.

For coverage, the same displayed product is obtained by proposing independent uniform indices and accepting i with probability I*p_i/beta, then sampling the actual record conditional on its accepted index. Terms with p_i=0 have zero record mass and require no conditional choice. This constructs uniform proposals conditional on the current state, even when that state contains private information.

Use this proposal-first construction to justify exposure order: release the completed record at acceptance, and retain the unused proposal suffix as independent uniform randomness. The record-first description is an equality of joint laws, not permission to reveal the completed record and then claim that its still-unconsumed accepted proposal is uniform. Coverage charges are made before the macro and at completed boundaries, which avoids this problem.

After a kill, complete the terminal word with independent uniform indices. For every fixed J, finite-prefix induction gives a uniform word of length J. Consequently its counts Z_i are independent Poisson(19/50) unconditionally. Conditioning on a clean terminal word would invalidate this argument; killing on adapted exceptions does not.

## The actual coverage lemma to prove

The required abstract result concerns message sampling and successful signing views. Non-message transitions may be arbitrary adaptive kernels that do not inspect unqueried message cells. It should be stated in this form so it applies both to the original experiment and to the forced-secret experiments.

A full certificate is an admissible message input whose 14 coordinates are supplied by successful signing responses at other inputs. A near certificate also specifies an omitted coordinate and requires only the other 13. A target may be created before the responses that cover it. At first completion bank the certificate and remove its pending forecast. At a kill, discard pending forecasts while retaining banked certificates. Failed signing responses do not disclose views.

The local transition proof has the following cases:

| Transition | Required mathematical fact |
| --- | --- |
| External fresh message input | Its answer is uniform; create an admissible target at the raw forecast's fresh-target price and update pending forecasts. |
| Repeated or irrelevant external input | No new target is created; decrement the remaining actual hash budget. |
| Cached admissible selection | A specific cached randomizer is selected with probability E[T_m]/N, where T_m is the actual finite attempt count. |
| Fresh admissible selection | Conditional on its occurrence, the selected digest is uniform among admissible digests; create at most one target. |
| Digest exhaustion | No signing view; only the auxiliary completed index is uniform. All attempted hashes remain paid. |
| Encoding failure after selection | Keep the actual selected index in the coupling; the returned response remains none and adds no successful view. |
| Exception at a macro boundary | Finish the actual macro and its costs, bank any completed certificates allowed by the one-step inequality, then discard pending forecasts. |

The finite-loop acceptance floor on a clean pre-state is

    P[accept next attempt | executed prefix]
      >= (1/L)(1-(2^93+2^32)/N).

It yields E[T_m]/N<=rho=(1025/1024)*2^-118. If F_m is the probability of fresh selection and E_m the probability of exhaustion, the exact completed-index law is

    p_i = (F_m+E_m)/I + c_(m,i) E[T_m]/N
        <= 1/I + rho*C_i <= beta/I.

Cached repeats are included. An encoding failure is not part of E_m. This distinction is essential to preserve the actual selected-index law.

Let W_d(h) be the existing raw fresh-target forecast for d coordinates, normalized as in cached-target-forecast.md. The positive-polynomial comparison and the clean cache cap give

    W_14(h) <= 2^-48 sum_i E[(s_i+Binomial(S-s,v_q))^14],
    W_near(h) <= (14/2^38) sum_i E[(s_i+Binomial(S-s,v_q))^13],
    I*v_q <= beta.

Here s_i counts successful views, while s counts every signing invocation. Hypothetical cache growth must be absorbed algebraically before the signing operator is interpreted as a bounded probability transition. The current raw-moment lemmas already address that algebraic dependency.

At a clean boundary let K=sum_(j<=s) G_j and let z_i count the consumed proposals. Then z_i>=s_i and, for J>=25313293,

    m=J-K >= beta*(S-s)+13.

For j<=d<=14 the unused suffix satisfies

    (S-s)_j v_q^j <= (beta*(S-s)/I)^j <= (m)_j/I^j.

Nonnegative falling-factorial expansions of shifted powers therefore give, in the coverage filtration,

    W_14(h) <= E[R_14 | F_h],       R_14=2^-48 sum_i Z_i^14,
    W_near(h) <= E[R_near | F_h],   R_near=(14/2^38) sum_i Z_i^13.

The decisive feature is one terminal variable per execution, shared across all its adaptive charging times. A separate unconditional occupancy estimate at each time would not suffice.

Let a_h=1 for an external fresh message query and a_h=L*F_m for a signing invocation, and zero on other steps. Finite linearity of expectation over executed fresh attempts gives

    E[fresh message calls in invocation | F_h] = L*F_m.

Each completed signing invocation costs at least L actual hashes, including both failure cases. Consequently sum_h a_h<=q pathwise and E[sum_h a_h]<=E[A]. No pathwise bound of L*F_m by that invocation's realized number of message calls is asserted; the pathwise payment uses its total hash cost.

The local forecast and banking inequalities must establish

    E[C_full] <= N^-1 E[sum_h a_h W_14(h)],
    E[C_near] <= N^-1 E[sum_h a_h W_near(h)].

Put Z=(R_14-3/2)_+. Since a_h is predictable, the tower identity gives

    E[sum_h a_h W_14(h)]
      <= (3/2) E[sum_h a_h] + E[Z sum_h a_h]
      <= (3/2) E[A] + q E[Z].

The terminal moment bounds E[Z]<2^-16 and E[R_near]<557 then prove the two certificate estimates. Existing exact rational checks support these constants. The remaining coverage work is the full transition and banking theorem with this exposure order, rather than another improvement to the constants.

## Large budgets: combine two bounds on the same stopped law

In the projected primitive history, only external probe rounds exclude candidates from hidden labels. Honest internal reads and message calls consume q without making such exclusions. After r probe rounds, the next round has at most two tests against distinct coordinates, giving hazard

    h_r = 1-((N-r-1)/(N-r))^2.

Distinct coordinates and preservation of their uniform posteriors are original-graph obligations. They cannot be inferred from a query count alone. Revealed block lengths are independent auxiliary randomness, so they do not add exclusions or secret information.

Give every non-probe round reward c=3/(2N), which upper-bounds the actual message rewards. In the scalar relaxation, a paid round can be moved before a probe without changing later probe hazards and can only increase expected reward. An optimum therefore consists of a paid prefix of length a followed by probes. This gives

    V(0,q) = max_(0<=a<=q) [3a/(2N)+1-((N-q+a)/N)^2].

At every reachable scalar state r+k<=N/2, continuation values are below one, so substituting larger hazards is legitimate. For a schedule with a remaining paid rounds, probe survival is at least (1/2+a/N)^2, which exceeds 3a/(2N); hence its failure probability plus reward is below one.

Writing s=a/N, maximize 2x-x^2+(2x-1/2)s-s^2 on 0<=s<=x. The result is 2x-x^2 for x<=1/4 and (3/2)x+1/16 otherwise. Both are at most 2x-(3/4)x^2 for x<=1/2.

Use coverage with tau_large and exactly the same A. On a nonexceptional run without B, a strong forgery must give a full certificate: canonical components at an input already signed successfully give exactly the old signature, while a new signature requires either a deviation or coverage at other inputs. Therefore

    P[forge] <= 2x-(3/4)x^2 + delta*x + epsilon(q).

For x>=2^-15, (3/4)x-delta>=2^-17. For q>=1,

    epsilon(q)/x <= 2^-94+2^-109+2^-572 < 2^-17.

This closes the large-budget range, conditional on the graph and certificate theorems. There is no OTS useful-witness calculation in this branch.

## Small budgets: retain useful witnesses and query allocations

The static OTS route needs an actual-game transfer. With Q counting external prefix queries and A_enc counting fresh nonreference encoding queries, its proposed endpoint is

    P[OTS witness] <= c_Q(x) E[Q]/N + c_enc(x) E[A_enc]/N,
    c_Q(x) = ((3/2)+4x+2x^2)/(1-x) + 4x/(1-x)^2 + 82x/(1-x),
    c_enc(x) = 1+3444x/(1-x).

The linear 3/2 term charges completed two-edge paths. The smaller terms account for two distinct one-step contacts and preparation of unit-neighbor codewords. The fixed canonical message and conditional reference table are required to include encoding queries made before signing. The number of challenges must not multiply the allocated Q term.

For x<=2^-15 both coefficients are below 131/80. Cheap noncanonical structural output matches cost at most E[A_cheap]/N, and ordinary coverage costs (3/(2N)) E[A]. These call classes are disjoint in the same execution stopped at tau_base. Their combined bound is therefore (131/80)x.

For FTS, charge alternative preimages as cheap matches, including ones found before a later disclosure. A true guess of an undisclosed secret has conditional probability at most 1/(N-q); two distinct true guesses cost at most x^2/(2(1-x)^2). With just one such guess, an otherwise canonical forgery needs a near certificate.

Perform the first-guess likelihood comparison in the projected experiment, before adding rejected indices. For each hash slot j, force earlier eligible guesses to miss and the eligible guess at j to hit, using the deferred-secret kernels in fts-guess-kernel.md. Call this law Q_j. With zero weight for ineligible or unreached j, kernel multiplication gives

    E_real[1_{first guess at j} F]
      = E_(Q_j)[p_j product_(t<j)(1-p_t) F]
      <= (N-q)^-1 E_(Q_j)[F].

Here F may indicate a near certificate before or after j. It depends on the actual history and stopping variables, not on rejected proposal values. The independent J and geometric lengths have identical kernels on both sides.

Now augment each Q_j separately with its own rejected values and apply the abstract near-certificate theorem. The different laws do not need a common proposal stream, and there is no need to cancel rejected-word densities in the first-guess likelihood. It suffices that every Q_j preserves fresh unqueried message cells, the finite signing rule, and the original path budget. These remain concrete obligations of the forced-secret construction.

There is no exceptional-probability term to sum over j: each forced-law certificate bound already applies to its killed execution. The final epsilon(q) is charged once for exceptions in the original law.

Summing over j gives the additional FTS contribution

    557x^2/(1-x) + x^2/(2(1-x)^2).

For x<=2^-15, its coefficient after division by x is below 9/80. Thus

    P[forge] <= (7/4)x + delta*x + epsilon(q) < 2x.

The same-input strong-forgery case must remain in the deterministic decomposition: if its own input was signed, a changed canonical signature is impossible, so an OTS deviation or structural match is required. Ordinary and near certificates must not count the target's own signing response as a source.

## Work order and stopping criteria for the paper stage

1. Establish the projected augmented experiment: preserve the real game, expose the canonical graph exactly, retain actual costs, and define the two branch-specific stopping times. Record the deterministic SUF decomposition including every failure case.
2. Prove the full abstract stopped certificate theorem, including the macro transitions, record exposure order, one terminal word, and banking. Use the richer coverage history. Its endpoint must contain the actual E[A], not a replacement q in the ordinary term.
3. Instantiate the primitive posterior invariant in the projected experiment and derive the original-game result for 2^113<=q<2^127. This is the shortest route to completing one nontrivial range and does not depend on the useful OTS bound.
4. Transfer the allocated static OTS witness bound and the projected forced-first-guess comparison. Apply coverage separately to each forced law and close q<=2^113.
5. Assemble the two ranges and the trivial probability bound for q>=2^127. Only then is there a complete paper proof suitable for direct formalization.

The main new conclusion is an interface simplification: auxiliary rejected values do not need to be admitted into the primitive or likelihood histories. Exact erasure of those values and independence of the retained lengths suffice. This reduces the coupling burden without altering the scheme or weakening the requested statement. The graph transfer, complete certificate theorem, and allocated OTS/FTS witness transfer still require proof. Their completion, rather than a count of supporting lemmas, is the criterion for claiming that 127 bits are established on paper.
