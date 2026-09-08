# Charging cached targets through one terminal Poisson variable

This note supplies the paper coverage estimate for targets queried before or after signing. It uses the same target-input exclusion as the existing target-shape proof. It also bounds the expected number of near-covered targets needed for the FTS argument. None of these statements is yet a Lean theorem for the new construction.

## Constants and results

Set N=2^128, I=2^26, L=1024, S=2^24, and a=1/(LI)=2^-36. Assume at most q<=N/2 total hash calls. Let x=q/N. For the cache, C_i(t) counts distinct admissible message-domain inputs at index i after t actual hash calls. Let s_i count successful signing views at i; s counts all signing invocations, including failures.

The original game logs every signing request and rejects a final log longer than S. It does not implement a signing oracle that returns a no-op after the cap. In the analysis, terminate with a losing result immediately before request S+1. Every execution discarded this way necessarily loses in the original game, so this adapted termination preserves its winning probability and gives s<=S. Discard pending target forecasts at this termination and retain certificates already counted; no exceptional-event allowance is needed for the cap.

Stop on any of three exceptional conditions defined below. Conditions arising inside an honest signing invocation are recorded and acted upon at its end, so the whole invocation remains one macro step. Other conditions stop immediately after the current external hash call. Additional adapted stopping is permitted. Previously completed target certificates are retained when the process stops.

Let A_msg count actual message-domain hash calls in that stopped execution. A full target certificate is an admissible cached digest whose 14 coordinates are covered by successful signing views at other inputs. A near-target certificate is a pair consisting of such a digest and one of its 14 coordinates, with the other 13 coordinates covered at other inputs. Repeated certification of the same pair is counted once. Then

    E[number of full certificates] <= (3/(2N)) E[A_msg] + 2^-16 x,
    E[number of near-target certificates] <= 557x.

The probability that the original execution encounters an exceptional condition is at most

    epsilon(q) = q/2^222 + q/2^237 + 2^-700.

The estimates depend only on fresh message-oracle answers, the concrete digest-selection rule, and the budget. Other oracle behavior may provide arbitrary information based on existing history, provided it does not inspect unqueried message cells. This robustness is used by the forced-guess experiment in fts-useful-witness.md.

## The target forecast already present in the reduction

The source modules TargetShapeEnvelope, ReuseTargetEnvelope, ReuseCachedTargets, FreshTargetShapeAverage, and TargetArrivalStep provide the following construction. For a fixed cached target z, exclude its own input from every signing view and cache matching factor. A shape has disjoint groups of coordinates assigned to cached matching entries, and a disjoint set of coordinates to be covered by signing views. Its normalized moment is a product of cache-match counts and signing-match counts, with a factor L for each constrained coordinate.

The future-query operator removes cache factors with coefficient a. The future-signing operator accounts for a uniform fresh selected digest, which can add one cache entry and one signing view together, and for reuse of any existing admissible input with per-input coefficient rho. Its reuse term turns a nonempty subset of remaining signing coordinates into a new cache group. Disjointness is preserved. The query and signing operators have nonnegative coefficients; commuting a query past a signing produces an additional nonnegative reuse term. Thus putting all remaining hash opportunities before all remaining signing opportunities is an upper envelope for arbitrary interleavings.

Use the actual remaining hash budget b=q-t and remaining signing budget r=S-s. A signing macro of random actual hash cost k leaves b-k; replacing that by b only increases its continuation forecast. The per-query decrement and the operator commutation handle external hashes. This preserves the original path budget, rather than giving each pending target a new independent execution budget.

For d required coordinates, scale the target forecast by L^-d. It is at least one when those coordinates are covered. On averaging over a fresh digest, disjoint coordinate groups make the normalized matching products equal ordinary mixed index moments C_i^p s_i^e. Consequently the normalized price of a fresh target is W_d/N, where

    W_d = N/(I L^(d+1)) * sum_i E_B[f_r(C_i+B,s_i)],
    B ~ Binomial(b,a),
    f_r(c,u) = T^r(u^d),
    (T f)(c,u) = f(c,u)
        + (1/I)[f(c+1,u+1)-f(c,u)]
        + rho*c[f(c,u+1)-f(c,u)].

This is an algebraic polynomial identity for the raw-index envelope. One must not treat T as a stochastic kernel at arbitrarily large c: its formal reuse rate could then exceed one. A bounded stochastic interpretation is justified only after the polynomial comparison below.

An external fresh message query has creation-price multiplier one. During a signing macro, at most one new admissible digest is created. If F is the conditional probability that selection uses a fresh cell, its multiplier is LF. The selected fresh digest is uniform conditional on admissibility. Excluding its own signing view is essential to the corresponding fresh-target averaging identity.

The conditional expected number of fresh message queries during that digest loop is exactly LF. Each fresh cell is admissible with probability 1/L, and at most one fresh admissible cell appears before the loop stops. This finite stopping-time identity remains valid with cached selections and retry exhaustion. Hence the sum of these predictable creation multipliers has expectation at most E[A_msg]. Pathwise it is at most q: external multipliers are at most their hash costs, and each signing multiplier is at most 1024. Every completed signing invocation either exhausts all 2^32 digest attempts or computes the FTS opening, whose sibling computations use 14*sum_(h=0)^9(2^(h+1)-1)=28504 hashes. Both cases cost at least 1024 actual calls. These costs are disjoint from external calls.

For full coverage use d=14, so W_14 is the raw forecast divided by 2^48. For near-targets sum over the 14 choices of the omitted coordinate, giving W_near=14 times W_13, with scale 14/2^38 on sum_i s_i^13.

## Recording completed certificates

Maintain the sum of the forecasts of pending targets plus a counter of completed certificates. At a first completion, increase the counter by one and remove that target's pending forecast, which is at least one. This cannot increase the total. Removing a pending target does not remove its input from the real oracle cache, so other targets' forecasts retain every legitimate reuse contribution.

On an exceptional condition, discard pending forecasts but retain the completed counter. Thus later exceptions do not require multiplying their probability by the number of targets. Conditional one-step forecast inequalities and the creation prices imply

    E[completed certificates] <= (1/N) E[sum_j a_j W_j],

where j ranges over the external-query and signing macro steps, a_j is the predictable multiplier just described, and W_j is the corresponding raw forecast before the step. This applies to d=14 and, after summing omitted coordinates, to d=13. It includes cached targets completed by later signatures.

## Cache controls and the reuse coefficient

First stop if, at any hash prefix, C_i(t)>at+2^80 for some i. For each i, fill inactive steps with auxiliary Bernoulli(a) trials. Its actual cache count is then bounded by a binomial counting process. The centered process is a martingale, and its fourth moment at q is at most 3(qa)^2+qa. The maximal inequality and a sum over I indices give

    P[cache exception] <= 3q^2/2^366 + q/2^330 < q/2^237.

Second, for each proper message m at the fixed public root, let D_m be the number of cached randomizers minus L times their admissible count. Stop if D_m>2^93 at any prefix. A fresh cell changes its one message score by X=1-L*Bernoulli(1/L). Then E[X]=0, E[X^2]<L, |E[X^3]|<L^2, and E[X^4]<L^3. The inequality 4L^2|D|<=2LD^2+2L^3 gives conditional fourth-moment growth at most 8LD^2+3L^3. At time t, E[sum_m D_m^2]<=Lt, so the expected squared score of the adaptively selected message is also at most Lt. Summing the fourth-moment increments yields

    E[sum_m D_m^4] <=4L^2 q(q-1)+3L^3 q.

The sum is a nonnegative submartingale. Its maximal inequality at 2^372 gives a probability below q/2^222 for q<=N/2. Only fresh message cells enter this proof. The existing Lean deficit estimate is slightly sharper, but that sharper constant is unnecessary here.

On a clean prefix, a digest loop starts with D_m<=2^93. Before it finishes, at most 2^32 new rejected cells can be added. At every attempt its conditional acceptance probability is at least

    (1/L)[1-(2^93+2^32)/N].

Indeed cached admissible randomizers are accepted, and an unqueried randomizer has admissibility probability 1/L. Therefore the expected number of attempts divided by N, which bounds selection of any fixed cached admissible input, is at most

    rho=(1025/1024)*2^-118.

This uses the actual finite loop and permits cached inputs. It also gives, after assigning an independent dummy index on digest exhaustion, a selected-index distribution p_i bounded by 1/I+rho*C_i: fresh selection and exhaustion together have mass at most one and each gives a uniform index; each previously cached admissible input contributes at most rho. A failed later encoding may suppress a signing view, which only decreases s_i.

## Bounding the raw forecast by capped binomial moments

The polynomial f_r has nonnegative coefficients and total degree at most d. This follows directly from T: its diagonal increment lowers total degree, while c times a signing increment does not increase it.

For B~Binomial(b,a), mu=ba, and k<=d,

    E[(c+B)^k] <= (c+mu+d)^k.

Expand binomial moments in falling factorials; E[(B)_j]<=(ba)^j and the partition count is at most choose(k,j) k^(k-j). Thus E[B^k]<=(mu+k)^k, and expanding the shift by c proves the displayed bound. Coefficient positivity now gives E_B[f_r(c+B,u)]<=f_r(c+ba+d,u).

On a clean prefix c<=at+2^80, so c+ba+d+r<=aq+2^80+S+14. Throughout the remaining r signing transitions, interpret T at this bounded starting point as the Markov chain with a diagonal increment of probability 1/I and a signing-only increment of probability rho*c. All its probabilities are valid in this range. Its signing increments are dominated by Bernoulli(v_q), where

    v_q=1/I+rho*(aq+2^80+S+14).

Set beta=1537/1024. Exact rational arithmetic gives I*v_q<=beta for q<=N/2. The bounded signing process is dominated by r independent Bernoulli(v_q) increments. It follows that

    W_14 <= (1/2^48) sum_i E[(s_i+Binomial(r,v_q))^14],
    W_near <= (14/2^38) sum_i E[(s_i+Binomial(r,v_q))^13].

No tail event for hypothetical future cache counts is needed: the polynomial moment comparison occurs before the bounded Markov interpretation.

## One discrete terminal word for every adaptive charging time

The exact finite-word construction is in discrete-target-coupling.md. At the next signing invocation, repeatedly propose a uniform index i and accept with probability I*p_i/beta, where p is the actual selected-index distribution. Equivalently, run the actual invocation first, independently sample a geometric proposal-block length of mean beta and its rejected indices, then append the invocation's selected index. The two joint kernels agree exactly. A signing record contains message queries, the returned Option signature, and actual hash cost; it does not disclose hidden internal non-message query inputs.

The construction preserves the actual conditional signing law and unqueried message cells at boundaries. External queries consume no proposals. Independently choose a terminal proposal-word length J~Poisson((19/50)*I). Let Z_i count index i among the first J proposals. Finite-prefix independence and the Poisson-multinomial identity make these terminal Z_i independent Poisson(19/50) variables.

Put D=S/128, and let K_s be the number of proposals consumed by s completed signing invocations. The third exceptional condition is the union of J<beta*S+D+13 initially and K_s>beta*s+D at any signing boundary. Exact geometric and Poisson exponential bounds give a combined probability below 2^-700. Finish a signing invocation before acting on an exception caused by its proposal block, so all its message calls remain in the charged execution.

At a clean boundary, let z_i count consumed proposals. Then z_i>=s_i, and m=J-K_s>=beta*(S-s)+13. Conditional on the boundary history, each future bin count is Binomial(m,1/I). For r=S-s and 0<=j<=d<=14,

    (r)_j v_q^j <= (beta*r/I)^j <= (m)_j/I^j.

These are falling-factorial moments. Their nonnegative expansions into shifted powers show that the future binomial count dominates the required degree-d forecast in moments. Thus, with

    R_14=(1/2^48) sum_i Z_i^14,
    R_near=(14/2^38) sum_i Z_i^13,

the enlarged boundary filtration F_j satisfies

    W_14,j <= E[R_14 | F_j],
    W_near,j <= E[R_near | F_j].

This is one terminal variable for all query times. No probability law has been conditioned on a future good event, or on the terminal word being long enough. The process is killed on adapted exceptions and retains banked certificates. Unconditional Poisson moments therefore control the adaptive excess charges below.

## Paying the adaptive charges

Let Z=(R_14-3/2)_+. Conditional Jensen gives

    (W_14,j-3/2)_+ <= E[Z | F_j].

Since a_j is predictable and sum_j a_j<=q,

    E[sum_j a_j(W_14,j-3/2)_+]
      <= E[Z sum_j a_j] <=q E[Z].

The ordinary part is paid by E[sum_j a_j]<=E[A_msg]. For near-targets the same argument without subtracting a threshold gives E[sum_j a_j W_near,j]<=q E[R_near]. This controls adaptively selected charges; an ordinary terminal occupancy mean alone would not have done so.

For independent Poisson variables of mean 19/50, exact moment bounds give

    E[(R_14-3/2)_+]<2^-16,
    E[R_near]<557.

For the first, split counts into at most 10, exactly 11, and at least 12. The bulk B has mean below 1/5, sum of second moments below 1/2000, and independent summands bounded by m=3/8. The inequality log E[exp(theta B)]<=theta E[B]+(sum E[B_i^2]/m^2)(exp(theta m)-1-theta m), at theta=16, gives log E[exp(16(B-3/2))]<-19. Integrating the exponential tail gives E[(B-3/2)_+]<exp(-19)/16<2^-31.

Let Y count bins with occupancy 11, let r=11^14/2^48, and let H be the contribution from occupancies at least 12. Then E[Y]<3*10^-5, r<3/2, and E[H]<5*10^-6. Pointwise,

    (B+rY+H-3/2)_+ <= H+(B-3/2)_++YB+rY(Y-1)/2.

The 11-bin indicator and bulk contribution of the same bin have product zero; those of different bins are independent. Therefore E[YB]<=E[Y]E[B] and E[Y(Y-1)]<=E[Y]^2. These bounds give the claimed excess. The degree-13 mean is bounded by its series with an explicit geometric remainder; its rational upper bound is below 557.

The arithmetic can use short certificates. For lambda=19/50, bound exp(-lambda) by its alternating Taylor polynomial through degree 4. For t_j=j^d lambda^j/j!, with d<=14 and j>=12, the ratio t_(j+1)/t_j=lambda*(1+1/j)^d/(j+1) decreases with j and is below 1/10 at j=12. Thus sum_(j>=12) t_j<=(10/9)t_12. This bounds the degree-13 mean and the degree-14 tail using only terms through 12. The exponential inequalities used above and in the proposal tail need no long series: the degree-3 Taylor polynomial gives exp(7/10)>2, so exp(19)>2^27 and exp(500)>2^701; summing exp(1) through degree 5 with a geometric tail gives exp(1)<68/25, hence exp(6)<(68/25)^6<405. The script coverage-closing-checks.py checks these rational certificates.

Combining these estimates with the certificate counter proves the two stated coverage results. Adding the three original exceptional-event probabilities gives epsilon(q), without any multiplication by the number of cached targets.
