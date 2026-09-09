# A simpler paper route to 127 bits using a fixed word and variance

This note derives a simplification of the existing 127-bit paper argument for the unchanged experiment in Statement.lean. It changes analytical constants and the budget split, without changing the scheme, adversary, independent secrets, finite failures, or whole-experiment hash accounting. The numerical stopped coverage endpoints for the original signer are now checked in [FixedCertificateCoverage.lean](../SphincsSecurity/Proof/FixedCertificateCoverage.lean). The exceptional probabilities, deferred-secret coverage extension, and cryptographic transfers in [paid-probe-quadratic.md](paid-probe-quadratic.md) and [small-budget-transfer.md](small-budget-transfer.md) remain obligations to audit and formalize.

The proposed change is to use a fixed terminal proposal-word length and replace the sharp positive-part estimate by a second-moment bound. The old route uses Poissonization, an excess allowance delta=2^-16, and a split at q=2^113. The simpler route uses delta=2^-13 and splits at q=3*2^114. The existing small-budget coefficient estimates still hold at this larger split, and the large-budget argument still has enough quadratic saving. The numerical coverage proof no longer needs a Poisson distribution theorem, the short-pool exception, or the decomposition into occupancies at most 10, exactly 11, and at least 12. An exponential estimate for the geometric proposal-prefix exception is still needed.

## The exact target and the source of the difficulty

Write N=2^128, I=2^26, L=1024, S=2^24 and x=q/N. The requested security statement is Pr[original SUF win]<=2x. For q>=N/2 this follows from probability at most one. The nontrivial range is 1<=q<N/2, with q counting every original hash call, including key generation, signing and verification.

A primitive estimate of 2x followed by a positive coverage allowance cannot establish this statement. A completed forgery must be charged more carefully. The existing paper route gives small budgets a saving by counting completed OTS witnesses and useful FTS guesses, and large budgets a saving by analyzing the first primitive match jointly with the message calls that prepare coverage. The simplification below preserves those two arguments.

## A fixed terminal word supplies enough unused proposals

Retain the exact adaptive proposal bridge and completion kernel from [cached-target-forecast.md](cached-target-forecast.md), but fix its terminal length to

    beta = 1537/1024,
    D = S/128 = 131072,
    M = beta*S+D+13 = 25313293.

On a clean boundary after s invocations, the existing prefix guard says K_s<=beta*s+D, where K_s is the number of consumed proposals. The unused length therefore satisfies

    M-K_s >= beta*(S-s)+13.

This is precisely the proposal-room inequality needed for all forecast degrees up to 14. The completion-kernel argument works for each fixed terminal length, so completing or truncating the actual consumed proposals produces an unconditional uniform word of length M. It need not be independent of the execution. There is no random short-pool event and no conditioning on a future good event. As before, finish an invocation and bank its first completions before acting on a post-state exception; the room inequality is used at its clean pre-state only.

## Compute just the moments the coverage proof uses

Let Z_i count occurrences of index i, and define

    R = 2^-48 * sum_i Z_i^14,
    R_near = (14/2^38) * sum_i Z_i^13.

The stopped certificate construction needs E[(R-3/2)_+] and E[R_near]. Counts in a fixed-length word are not independent. The necessary sign of their covariance follows directly from single-bin and two-bin mixed factorial moments.

For distinct i,j and nonnegative integers a,b, counting ordered choices of distinct positions gives

    E[(Z_i)_a] = (M)_a/I^a,
    E[(Z_i)_a (Z_j)_b] = (M)_(a+b)/I^(a+b).

Here (z)_a is the falling factorial, including (z)_0=1. There is also a short finite induction: adding one uniform letter changes this expectation by (a/I) times the moment of orders (a-1,b), plus (b/I) times the moment of orders (a,b-1). The two indices cannot both be incremented by one letter. The displayed expression satisfies this recursion and its initial values.

Falling factorials satisfy (M)_(a+b)<=(M)_a*(M)_b. Define X_i=Z_i^14. Expand powers into falling factorials with nonnegative Stirling coefficients. Termwise comparison then gives

    E[X_i*X_j] <= E[X_i]*E[X_j]       for i!=j.

No general negative-association theorem is required. This explicit calculation proves the nonpositive pairwise covariances used below.

For the single-bin estimates, define the finite polynomial T_d(lambda)=sum_(a=0)^d StirlingSecond(d,a)*lambda^a and set lambda=19/50. Since M/I<lambda and (M)_a<=M^a,

    E[Z_i^d] <= T_d(lambda).

Consequently,

    mu = E[R] <= (I/2^48)*T_14(lambda),
    Var(R) <= 2^-96 * sum_i Var(X_i)
           <= (I/2^96)*T_28(lambda),
    E[R_near] <= (14*I/2^38)*T_13(lambda).

The variance upper bound even drops the negative square in each Var(X_i); its additional precision is unnecessary. Although T_d also describes Poisson moments, no Poisson random variable or limiting argument is used here. All three quantities are bounded moments of a finite uniform word.

These are finite rational expressions. The recurrence StirlingSecond(d+1,a)=a*StirlingSecond(d,a)+StirlingSecond(d,a-1) gives exact arithmetic certificates for

    mu < 1/5,
    Var(R) < 13/25000,
    E[R_near] < 557.

For orientation, the respective polynomial upper bounds are approximately 0.1993478614, 0.0005101418 and 556.2438629480. [variance-route-checks.py](variance-route-checks.py) checks the displayed rational inequalities and the closing constants exactly. It does not prove the adaptive proposal construction or a security theorem.

## Replace the positive-part tail estimate by one square

For any real y and a>0,

    (y-a)_+ <= y^2/(4a).

For y<a the left side is zero; for y>=a the inequality is exactly (y-2a)^2>=0. Apply this with y=R-mu and a=3/2-mu, then take expectations:

    E[(R-3/2)_+] <= Var(R)/(4*(3/2-mu))
                    < (13/25000)/(4*(3/2-1/5))
                    = 1/10000 < 2^-13.

The terminal word has fixed finite length, so all these terminal payoffs are bounded. The stopped coverage argument therefore gives, with delta=2^-13,

    E[C_full] <= (3/(2N))*E[A_cov] + delta*x,
    E[C_near] <= 557*x.

This uses the existing adaptive charging argument, not the false factorization of a chosen charging time and the final occupancy. Its common terminal variable and remaining-budget potential are still essential. The certificate theorem must also apply to the deferred-secret kernels needed in the small-budget branch; proving it only for the original fixed-key signer would not discharge that transfer.

## The two ranges still overlap

Choose

    x_* = 3/2^14,
    q_* = 3*2^114,
    delta = 2^-13,
    epsilon(q) = q/2^222 + q/2^237 + 2^-700.

The last quantity remains a valid combined cache, deficit and geometric proposal-prefix exception allowance. The removed short-pool exception only improves it. For every q>=1,

    epsilon(q)/x <= 2^-94 + 2^-109 + 2^-572 < 2^-16.

For the large-budget branch, let B be the first primitive match and A_B its stopped actual message-call count. The paper primitive argument gives

    Pr[B] + (3/(2N))*E[A_B] <= 2x-(3/4)*x^2.

The coverage monitor also stops at B, so A_cov<=A_B on the same original run. The deterministic SUF decomposition and the certificate bounds imply

    Pr[SUF win] <= 2x-(3/4)*x^2+delta*x+epsilon(q).

At and above the new split,

    (3/4)*x-delta >= (3/4)*(3/2^14)-2^-13 = 2^-16.

Thus the original target follows throughout q_*<=q<N/2. No sharpening of the primitive quadratic estimate is required.

For the small-budget branch, retain the original disjoint costs Q, A_enc, A_str and A_msg from small-budget-transfer.md. They satisfy Q+A_enc+A_str+A_msg<=q on each monitored original path. Put

    c_Q(x) = ((3/2)+4x+2x^2)/(1-x) + 4x/(1-x)^2 + 82x/(1-x),
    c_enc(x) = 1+3444x/(1-x).

The allocated OTS witnesses, cheap structural matches, full coverage and extra useful FTS guesses give the paper bound

    Pr[SUF win] <= c_Q(x)*E[Q]/N + c_enc(x)*E[A_enc]/N
                  + E[A_str]/N + (3/2)*E[A_msg]/N
                  + 557*x^2/(1-x) + x^2/(2*(1-x)^2)
                  + delta*x + epsilon(q).

All the coefficient functions are increasing on 0<=x<1. Exact endpoint evaluation at x_* gives

    max(c_Q(x_*),c_enc(x_*),1,3/2) < 131/80,
    557*x_* /(1-x_*) + x_* /(2*(1-x_*)^2) < 9/80.

The likelihood bounds underlying this calculation require q<N, and the coverage and support arguments require q<=N/2; they do not need the previous cutoff q<=2^113. The smaller cutoff in the existing transfer note can therefore be replaced by q_* once its quantitative endpoint is restated. Preserve the allocated costs before taking the maximum. This yields, for q<=q_*,

    Pr[SUF win] <= (7/4)*x+2^-13*x+epsilon(q) < 2x.

Together with the large-budget branch and the trivial range, these inequalities close the desired numerical bound q/2^127.

## What must be established before calling this a proof

The variance calculation removes a numerical obstacle. It does not replace the cryptographic reductions. The remaining mathematical endpoints should be reviewed in the following order.

1. Establish the exact canonical graph presentation and the deterministic implication from an accepted strong forgery to a primitive deviation or a full/near certificate. Include every signature field, own-input exclusion, arbitrary serialized query bytes, and both finite failure cases. The analyst's extra advice must preserve the original outcome and cost law.
2. Audit the two small-budget experiment transfers. For OTS, the preimage-count density is valid only after forgetting the starting secret and private prefix evaluations; every charged statistic must survive that projection. For FTS, force only eligible hit/miss branches of positive original conditional probability, retain the original path budget, and apply a coverage theorem for that changed kernel. A bound proved only under the original law cannot simply be multiplied by the probability of a guess.
3. Complete the coverage endpoint from the actual monitor at fixed length M, using the single-bin and two-bin factorial moments above, the square inequality, and the remaining exception estimates. Its scope must include the deferred-secret experiments. Neither a favorable terminal occupancy assumption nor full key disclosure may be smuggled into the secret-guess argument.
4. Establish the original-game large-budget theorem using its joint primitive/message bound and A_cov<=A_B. Establish the original-game small-budget theorem with the same disjoint query allocations. Only then combine the ranges into the unchanged public security statement.

The next formalization work should produce these original-game inequalities, with explicit checks that their auxiliary assumptions have been discharged. The new numerical route needs no improvement to the constants above. The most consequential remaining uncertainty is the correctness of the adaptive experiment transfers, not whether the final arithmetic can reach 127 bits.
