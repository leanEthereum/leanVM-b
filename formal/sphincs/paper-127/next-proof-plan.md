# Revised paper plan for 127-bit SUF

This review starts from source commit 89d33041. It proposes a route for the unchanged experiment in Statement.lean, without adding Lean code. The public 126-bit theorem is established; the 127-bit theorem is not. The existing paper route has sufficient numerical slack, but its original-experiment probability interfaces remain proof obligations. The main new simplification below is to count primitive probe rounds separately from message queries in the accumulated-reward argument.

Write N=2^128, I=2^26, L=1024, S=2^24 and x=q/N. Here q bounds actual hash calls on every execution path, including key generation, signing, adversarial calls and verification. The desired statement is Pr[SUF forgery] <= 2x. It suffices to handle 1 <= q < N/2: larger budgets follow from probability at most one, and the public definition requires positive q. Retain independent sampled secrets, all finite retries, Option signing failures, and the original signing log cap.

## 1. Define one experiment before combining estimates

Start with the original game and add analysis variables. At each OTS address, sample the canonical counter and codeword using the exact conditional encoding-table construction in reference-frontier-transfer.md. Sample canonical structural labels along the acyclic graph, programming each distinct hash domain at its unique canonical input. This must preserve the original joint distribution, including the high output bits. The canonical OTS message is fixed by the non-encoding graph; it is not a message chosen after searching encodings.

Expose canonical OTS frontier and forward values, FTS leaf hashes and internal nodes, and the reference encoding information. Keep OTS labels below the frontier and undisclosed FTS secrets hidden. The original adversary ignores the additional advice. Honest internal evaluations compute the programmed graph without disclosing their secret-dependent inputs. Their actual hash calls still consume q.

The boundary history records public advice, message queries and answers, external replies, returned signing responses, actual hash counts, analysis stopping flags and consumed auxiliary proposals. Its hidden-label posterior and its unqueried-message-cell law are explicit invariants. In particular, revealing the entire real oracle cache is inappropriate: its honest non-message inputs contain secrets. Recording hash costs is permissible only after checking that their control flow depends on the exposed graph and digest/encoding outcomes, rather than on hidden secret values.

The existing raw forecast is written using a full Lean cache and secret-key record. Before applying it with this smaller history, establish that its value depends only on the public parameter/root, the message portion of the cache, and the observed signing views. The cap on the next digest index has the same dependence. Pointwise inequalities for full states can then be averaged over their hidden completions. This is the explicit connection between the current moment lemmas and the required boundary filtration.

The decisive deterministic implication is that an accepted strong forgery either has a primitive deviation or has an admissible message digest whose 14 coordinates are supplied by successful signing inputs other than its own input. If its own message/randomizer input was signed successfully and every component is canonical, the signature is identical to that response and is not a strong forgery. Failed responses do not disclose signing views. An OTS encoding failure after digest selection must still retain the selected digest in the analytical record.

This is the interface to establish first on paper. Exact local sampling identities do not, by themselves, establish this complete experiment correspondence.

## 2. Prove the stopped certificate estimate

The common coverage result needed by both budget ranges is

    E[C_full] <= (3/(2N)) E[A_msg] + delta*x,
    E[C_near] <= 557*x,                 delta=2^-16.

C_full counts distinct completed full-target certificates. C_near counts target/omitted-coordinate pairs with the other 13 coordinates covered. A_msg is the actual number of message hash calls in the same stopped execution. A certificate's own input is excluded from every source signing view. Previously completed certificates remain counted after a later stop; only pending forecasts are discarded. The result must also apply when non-message transitions are replaced by the forced-secret kernels used in step 5.

For a message m, let T_m be the number of digest attempts made by its actual finite signing loop. At a fixed pre-state, every cached admissible input for m is selected with probability E[T_m]/N. This is an equality: at each executed attempt the fresh randomizer draw hits that input with probability 1/N, and its admissibility ends the loop. Fresh selection has a uniform index conditional on occurring. On digest exhaustion only, add an independent uniform dummy index. Consequently the completed selected-index law satisfies

    p_i = (F+E)/I + c_(m,i) E[T_m]/N
        <= 1/I + rho*C_i,
    rho=(1025/1024)*2^-118.

Here F and E are fresh-selection and exhaustion probabilities, c_(m,i) is the message-specific admissible cache count, and C_i is its all-message upper bound. F+E <= 1. A later encoding failure may remove a successful view, but does not justify resampling this selected index.

The cache and message-deficit controls in cached-target-forecast.md give, before stopping,

    C_i(t) <= t/2^36 + 2^80,
    E[T_m]/N <= rho,
    p_i <= beta/I,                    beta=1537/1024.

For the deficit estimate, the loop's conditional acceptance probability stays at least (1/L)(1-(2^93+2^32)/N), even when rejected randomizers repeat. This bounds the finite expected attempt count without replacing the loop by infinite rejection sampling. Cache and deficit exceptions first reached inside signing are acted upon after that invocation finishes.

For a full signing record omega with conditional law K_h and selected index i(omega), append an auxiliary rejected word. Its exact joint mass with omega is

    K_h(omega)/beta * product_a (1/I-p_(u_a)/beta).

One construction runs the original signer first and independently adds a geometric number of rejections. The other proposes uniform indices and accepts index i with probability I*p_i/beta. Summing the displayed mass preserves K_h exactly. Induction through completed records must preserve both the original record law and independent unused proposals conditional on the boundary history. These are stronger requirements than an unconditional uniform marginal for the proposal word.

Independently choose J ~ Poisson((19/50)I). Complete the proposal sequence after termination with independent uniform values. The counts Z_i in its first J entries are independent Poisson(19/50) unconditionally. Stop initially if J < 25313293 and after a completed signing invocation if the number K_s of consumed proposals exceeds beta*s+131072. On every clean boundary, the unused length m satisfies

    m=J-K_s >= beta*(S-s)+13.

The existing positive-polynomial argument first absorbs hypothetical cache growth into its moments, then bounds the signing increment rate by v with I*v <= beta. It does not interpret an unbounded polynomial operator as a probability kernel. For r=S-s, d<=14 and j<=d,

    (r)_j v^j <= (beta*r/I)^j <= (m)_j/I^j.

Since actual successful index counts are bounded by consumed proposal counts, expansion of shifted powers in falling factorials gives one terminal domination at every clean boundary:

    W_full,h <= E[R_full | F_h],       R_full=sum_i Z_i^14/2^48,
    W_near,h <= E[R_near | F_h],       R_near=(14/2^38)sum_i Z_i^13.

The arithmetic in coverage-closing-checks.py supplies E[(R_full-3/2)_+] < delta and E[R_near] < 557. These are unconditional terminal estimates; the game is stopped on exceptions, not conditioned on their absence.

The remaining charging argument is short once this common terminal domination is established. An external fresh message query has predictable creation multiplier a_h=1. A signing invocation has multiplier a_h=L*f_h, where f_h is its conditional fresh-selection probability. The finite-loop identity gives E[number of fresh message calls in that invocation | F_h]=L*f_h, with F_h denoting the boundary filtration. Every completed invocation costs at least L actual hashes, including failed invocations. Therefore

    sum_h a_h <= q,             E[sum_h a_h] <= E[A_msg].

Set Z=(R_full-3/2)_+. From R_full <= 3/2+Z and the tower identity,

    E[sum_h a_h W_full,h]
        <= (3/2)E[sum_h a_h] + E[Z sum_h a_h]
        <= (3/2)E[A_msg] + q*delta.

No independence between the charging times and R_full is used. Dividing by N and applying the banked-forecast inequality proves the full certificate estimate. The same argument with R_near gives the near certificate estimate. This complete result, with its precise filtration and A_msg, is the next substantial coverage milestone. The checked raw-moment and proposal-kernel lemmas are ingredients for it.

The total proposed exceptional allowance remains

    epsilon(q)=q/2^222 + q/2^237 + 2^-700.

The game rejects a log with more than S signing requests. Terminating with loss before request S+1 therefore discards no winning run; this termination requires no exceptional allowance. Proposal overflow and cache exceptions retain all calls of the invocation that encountered them.

## 3. Sharpen the primitive probability calculation

Let B be the first primitive equality match in the exposed-graph experiment. Before B, a primitive probe round tests at most one candidate against each of two distinct hidden coordinates. An OTS prefix query tests its input against the hidden canonical child, then, on a miss, its fresh answer against the canonical parent. An FTS secret query has an input test and an output test. A public structural target or unrestricted nonreference encoding has at most one output test. A message hash has none.

The useful refinement is that only previous probe rounds can exclude candidates from a still-hidden coordinate. Message calls and honest internal graph evaluations consume the original budget but add no exclusions. After r probe rounds, each active coordinate has at most r excluded values. Under the product-of-uniform-posteriors invariant, the next probe round therefore has hazard at most

    h_r=1-((N-r-1)/(N-r))^2.

This is a conditional statement and permits the second coordinate to be chosen after the first miss. Distinctness of the two coordinates is essential. Adaptively selected disclosures retire coordinates; they may not inspect their hidden values to decide which coordinate to disclose. Fresh-answer tests against public values fit the same hazard bound. The concrete invariant must justify this classification; merely renaming the old total-time counter would not prove it.

Give each message round reward c=3/(2N). For an upper bound, give this same reward to every other non-probe round, including honest internal calls. Then the real quantity Pr[B]+c E[A_msg] is bounded by a scalar problem with q rounds, two actions, and state equal to the number of probes already taken. Its recurrence is

    V(r,0)=0,
    V(r,k)=max(c+V(r,k-1), h_r+(1-h_r)V(r+1,k-1)).

An optimal scalar policy can be deterministic. On its surviving branch it specifies a sequence of paid and probe rounds. Moving a paid round before a probe preserves the sequence of probe hazards and increases the chance that its reward is collected. Thus an optimal sequence has a paid prefix followed by probes. With a paid rounds, survival of the q-a probes telescopes to ((N-q+a)/N)^2. Consequently

    V(0,q)=max_(integer 0<=a<=q)
        [3a/(2N)+1-((N-q+a)/N)^2].

Replacing actual hazards by upper hazards is legitimate because the continuation values are below one. This can be checked directly from the same schedule formula at any reachable state r+k<=N/2. For a paid prefix of length a, the remaining survival probability is ((N-r-k+a)/(N-r))^2 >= (1/2+a/N)^2 > 3a/(2N). Its accumulated reward plus failure probability is therefore below one.

Put s=a/N and relax the integer maximum. The objective becomes

    2x-x^2+(2x-1/2)s-s^2.

Its maximum is 2x-x^2 for x<=1/4, and (3/2)x+1/16 for 1/4<=x<=1/2. Both are at most 2x-(3/4)x^2. For the second range the difference is exactly

    (3/4)(1/2-x)(x-1/6) >= 0.

We therefore obtain the stronger abstract paid bound

    Pr[B]+(3/(2N)) E[A_msg] <= 2x-(3/4)x^2.

This replaces the old total-time scalar bound 2x-x^2/8 by a simpler calculation. An exact rational dynamic-program check agrees with the finite schedule formula for N=2,...,80 and every q<=N/2. The displayed argument is the general proof; the finite check does not establish the concrete hidden-label invariant.

## 4. Close the large-budget range first

Use precisely the certificate experiment from step 2, also stopped at B. A forgery with no B and no exception has a banked full certificate. The message charge in the certificate bound is already paid by step 3, so

    Pr[forge] <= 2x-(3/4)x^2 + delta*x + epsilon(q).

Take the new split x_0=2^-15, equivalently q_0=2^113. At x>=x_0,

    (3/4)x-delta >= 2^-17.

For q>=1,

    epsilon(q)/x <= 2^-94+2^-109+2^-572 < 2^-17.

Thus this range closes. Establishing an original-game theorem for q>=2^113 would be a meaningful completion of one branch of the security proof, although it would not establish 127-bit security for all budgets. It requires the graph and coverage interfaces, but does not require the more elaborate useful OTS inversion argument.

## 5. Complete the small-budget witness bound

For x<=x_0, first primitive matches are too generous an event: guessing one hidden value need not provide a usable forgery. Use the existing paper's completed-witness analysis instead.

For OTS, let Q be the actual number of distinct external prefix queries and A_enc the number of fresh nonreference encoding queries. A distinct target-sum codeword either has a backward distance of at least two in one chain, has backward steps in two chains, or is a unit neighbor. There are at most 42*41 unit neighbors and at most 41 lowering a specified chain. The conditional reference table is needed to charge their preparation, including queries before signing. The chain likelihood argument must retain the allocations Q and A_enc in the original execution:

    Pr[OTS witness] <= c_Q(x) E[Q]/N + c_enc(x) E[A_enc]/N,
    c_Q(x)=((3/2)+4x+2x^2)/(1-x)+4x/(1-x)^2+82x/(1-x),
    c_enc(x)=1+3444x/(1-x).

At x<=2^-15 both coefficients are below 131/80. Cheap noncanonical structural output matches have coefficient one; the ordinary full-coverage message charge has coefficient 3/2. These allocations are disjoint. Their combined contribution is bounded by (131/80)x, rather than granting a separate q budget to each class. The static chain estimates and their transfer through canonical frontiers remain substantial proof obligations, even though their paper formulas have been developed.

For FTS, charge alternative preimages as cheap output matches, including those found before a later secret disclosure. A true guess of an undisclosed secret has conditional probability at most 1/(N-q). Two distinct true guesses cost at most x^2/(2(1-x)^2). A forgery using exactly one undisclosed secret also needs a near certificate.

Force the first true guess at slot j with the explicit deferred-secret kernels in fts-guess-kernel.md. The likelihood of the real first-guess branch relative to this forced experiment is

    p_j product_(t<j)(1-p_t) <= 1/(N-q).

The modified kernels must preserve unqueried message cells, the same pathwise q bound, and the coverage stopping rules. Applying the uniform near-certificate estimate to each forced experiment and summing j gives 557x^2/(1-x). This avoids assuming independence or a particular chronological order between guessing and target preparation.

At x<=2^-15, the existing looser constants already give

    557x/(1-x)+x/(2(1-x)^2) < 9/80.

Therefore

    Pr[forge] <= (131/80+9/80)x + delta*x + epsilon(q)
              = (7/4)x + delta*x + epsilon(q) < 2x.

No further constant optimization is needed in this branch.

## 6. Decision criteria before more Lean infrastructure

The paper work should deliver three original-experiment statements: the stopped full/near certificate bounds with their common filtration; the joint primitive/message-charge bound in that same stopped experiment; and the small-budget completed-witness decomposition with disjoint cost allocations. These statements imply the public claim by the elementary split above.

The next mathematical review should concentrate on the first statement. Write the full transition invariant, including what the record reveals, and carry it through one cached selection, one fresh selection, digest exhaustion, later encoding failure, an external query, and each stopping rule. Then prove the banked-certificate endpoint. An isolated index cap or another moment comparison is useful only as a dependency of that endpoint.

My assessment is that the route is mathematically plausible and its closing constants are adequate. The new probe-count calculation simplifies one branch. I do not regard the full paper proof as complete: the common adaptive filtration and the original-game transfers still need a rigorous construction, and the small-budget OTS/FTS interfaces still need assembly. Those are the criteria for moving from a candidate plan to a proof, rather than the number of intermediate lemmas or commits.
