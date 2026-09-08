# Adaptive inversion of an isolated two-hash chain

This note proves a paper bound for an isolated two-hash random-function challenge. It allows arbitrary query order, precomputation, candidate mergers, caching, and adaptive stopping. It does not yet transfer that bound to all chains, disclosures, and encodings in the SPHINCS experiment.

## Result

Let f,g map an N-element set to itself and be independent uniform random functions. Sample S uniformly and independently, and give the adversary Y=g(f(S)). The adversary can query f and g adaptively, with independent private randomness, using at most q queries in total. Count the queries needed to verify the eventual candidate as well. A successful candidate must have a complete queried path x -> f(x) -> Y.

Then

    P[success] <= 3q/(2N)
        + 3q(q-1)/(2N^2)
        + q(q-1)(q-2)/(3N^3).

Terms with q<2 or q<3 are interpreted through the corresponding empty sums, so they vanish. In particular, with x=q/N and q>=2,

    P[success] <= (3/2)x + (3/2)x^2 + x^3/3.

For x<=1/8, this is at most (325/192)x, hence strictly below (7/4)x. The leading coefficient is 3/2. The estimate is an upper bound, not an assertion that all adversaries attain it.

## Change of measure

Analyze first an ideal experiment in which Y is independently uniform, independently of f and g. Let

    W = #{s : g(f(s))=Y}.

For the joint distribution of (Y,f,g), the real experiment has density W relative to the ideal experiment: sampling S makes the conditional probability of Y equal to W/N, while the independent experiment gives probability 1/N. Thus, for every transcript-measurable success event E,

    P_real[E] = E_ideal[1_E W].

For a partial query transcript let D_f,D_g be the queried input sets, with a=|D_f| and b=|D_g|. Write

    T = {z in D_g : g(z)=Y},       k=|T|,
    A = #{x in D_f : f(x) in T},
    B = #{x in D_f : f(x) not in D_g}.

Conditioned on an adaptive transcript, all unqueried function cells remain independent uniform cells. Therefore

    w := E_ideal[W | transcript]
       = A + B/N + (1-a/N)(k+1-b/N).

The terms count already completed roots, queried f-inputs awaiting a g-answer, and the remaining N-a roots. This identity handles unequal candidate multiplicities without an injectivity assumption.

Stop when A first becomes positive, or at the query budget. This only enlarges the probability of finding the adversary's eventual verified candidate. The real probability of this stopping event is the sum of the ideal one-step success probabilities weighted by the resulting value of w. Repeated queries cannot create a new complete path, and can be ignored while retaining q as an upper bound on the number of fresh queries.

## A fresh g-query

Before stopping, A=0. Suppose a fresh g-input z has m known f-preimages. If m=0, this query cannot complete a path. If m>0, it completes a path exactly when its answer is Y, with ideal probability 1/N.

On that answer, the new state has A'=m, B'=B-m, k'=k+1, b'=b+1. Its conditional likelihood is

    w' = m + (B-m)/N + (1-a/N)(k+2-(b+1)/N)
       <= m+2+k.

The inequality follows from B<=a and nonnegativity of all counts. Hence the weighted risk of this transition is at most (m+2+k)/N.

Call such a query productive when m>0. Each previously queried f-input contributes to m at most once, because its image has only one first g-query. If p is the total number of productive g-queries before stopping and M is the sum of their m values, then pathwise

    M<=a_final,       p<=min(a_final,b_final).

Consequently

    M+2p <= a_final+2min(a_final,b_final)
          <= (3/2)(a_final+b_final) <= 3q/2.

This is the amortization step that accounts for merged candidates. A large m increases the likelihood weight of a successful g-query, but its m predecessors were already paid for by distinct f-queries.

## A fresh f-query

An f-query completes a path only when its answer lies in T, with ideal probability k/N. On such an answer A'=1, B'=B, a'=a+1. Therefore

    w' = 1+B/N+(1-(a+1)/N)(k+1-b/N) <= k+2.

Its weighted risk is at most k(k+2)/N. This includes reverse-order precomputation: a g-preimage of Y can be found first and subsequently reached by an f-query.

## Bounding the remaining terms

The fresh productive g-queries contribute the amortized baseline (M+2p)/N plus k/N. The fresh f-queries contribute at most k(k+2)/N. Since k<=k(k+2), the remaining contribution at any query step is at most k(k+2)/N.

After t ideal query steps, k is dominated by a binomial variable with t trials and success probability 1/N. A fresh g-query has an independent uniform answer, even when its input is chosen adaptively; an f-query, repeated query, or padded step contributes no new g-answer. Thus

    E[k] <= t/N,
    E[k(k-1)] <= t(t-1)/N^2,
    E[k(k+2)] <= 3t/N+t(t-1)/N^2.

Summing this last bound divided by N over t=0,...,q-1, and adding 3q/(2N), proves the stated result. This first-hit likelihood calculation does not expose an internal hit flag to the adversary and does not factor dependent success events.

## What this resolves and what remains

This proves that arbitrary precomputation and candidate mergers do not, by themselves, prevent a useful constant below two for this isolated two-step problem. In particular, the simpler argument that counts independent two-query trials is unnecessary and would not have covered all allowed adversaries.

This isolated lemma needs extensions before it can bound OTS witnesses. An OTS frontier can have other queried chain positions below it, several chains can be attacked together, and signatures can disclose frontier values later. The starting label in a two-step segment can be correlated with queries to earlier positions; it must not be silently replaced by a fresh independent S. Those extensions are supplied in long-chain-inversion.md, multiple-chain-inversion.md, two-chain-hits.md, and reference-frontier-transfer.md, using conditional preimage weights and an exact reference-encoding construction.

The productive-work discount in the overall plan is needed only in the small-q range. For example, if the proposed full-game quadratic discount x^2/8 is established, then at x>=2^-12 it alone exceeds the proposed 2^-16 x coverage excess with room for the small errors. Thus the hardest useful-inversion accounting can be restricted to q<=2^116 without weakening the final 127-bit objective. In that range the correction terms in this isolated two-hop bound are much smaller than its gap to 7/4.

The script two-hop-arithmetic.py exhaustively checks the conditional likelihood formula and one-step weighted-risk identities on all partial tables for N=3. It also checks the rational coefficient comparison. These are checks of the paper calculation, not a Lean proof or a full-game validation.
