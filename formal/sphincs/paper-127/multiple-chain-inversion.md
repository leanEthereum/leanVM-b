# A shared budget for several static chain challenges

This paper lemma removes the factor equal to the number of challenges from the isolated-chain bound. All challenge endpoints are published initially. The functions of different chains are independent. The result allows adaptive allocation of queries, arbitrary earlier-function queries, and caches. It does not yet establish the full signature-game reduction or the case of two separate one-step inversions.

## Result

Take any finite family of independent chain challenges as in long-chain-inversion.md, each of length at least two. Give the adversary all their endpoints. Additional independent randomness and oracle access may be included. The total number of queries is at most q<N, including verification. Let E_i mean that a complete queried two-edge suffix reaches challenge i's endpoint, and let x=q/N.

Then

    P[exists i: E_i] <= ((3/2)x + 4x^2 + 2x^3)/(1-x).

For x <= 1/32, the right-hand side is at most (833/496)x < (7/4)x. There is no factor for the number of chains or their lengths.

## A lower bound on each challenge's likelihood

For one challenge, use the matrices and likelihood w from long-chain-inversion.md. If a_j rows of function j have been queried, the nonnegative matrix inequality

    P_j >= u_j 1^T/N

implies

    w >= product_j (1-a_j/N) >= 1-sum_j a_j/N.

If Q_i is the number of fresh queries to challenge i, this gives w_i >= 1-Q_i/N >= 1-x. This is a pointwise bound on the conditional likelihood at any adaptive stopping time. It uses only q<N.

Let R be the real joint experiment. For a fixed i, define I_i by replacing just endpoint i by an independent uniform value, while keeping all the other challenges real. Forget challenge i's starting secret and private canonical prefix data before comparing the laws. The simulated transcript does not inspect them. Since the different challenges were independent initially, the likelihood of that real projected transcript relative to I_i is precisely w_i. Auxiliary queries and queries to other challenges merely affect the adaptive choice of the next query to i. They do not reveal unqueried function cells of i.

Consequently, for every nonnegative transcript cost C,

    E_(I_i)[C] <= E_R[C]/(1-x).

This comparison is what allows actual query counts in the different analyses to be combined. Summing isolated bounds which each use the whole budget q would not do so.

## A bound proportional to the queries allocated to i

For analysis of E_i, stop the full execution at its first completed two-edge suffix for i, or at the original stopping time. Let Q_i count fresh queries to i up to that stop. All expectations in this paragraph are under I_i.

The pathwise baseline charging in long-chain-inversion.md gives contribution at most 3 E[Q_i]/(2N). Let k be the number of queried last-function inputs for i whose output is its endpoint. Independent uniform answers and predictable query choices give

    E[k_final] <= E[Q_i]/N,
    E[k_final(k_final-1)]
      = (2/N) E[sum_(fresh last-function queries) k_before]
      <= (2q/N) E[k_final]
      <= 2q E[Q_i]/N^2.

The extra term from already queried earlier prefixes is bounded by q k_final/N pathwise, hence by q E[Q_i]/N^2 in expectation. All the remaining terms sum to at most q k_final(k_final+2)/N, whose expectation is at most

    3q E[Q_i]/N^2 + 2q^2 E[Q_i]/N^3.

The same first-success likelihood calculation as in the isolated-chain proof therefore yields

    P_R[E_i] <= (3/(2N) + 4q/N^2 + 2q^2/N^3) E_(I_i)[Q_i]
             <= (3/(2N) + 4q/N^2 + 2q^2/N^3) E_R[Q_i]/(1-x).

The stopping time differs for each i, but Q_i never exceeds the number of queries to i in the original complete real execution. Thus sum_i Q_i <= q pathwise. A union bound over i now proves the claim without losing a challenge-count factor.

## Consequence and remaining scope

In a static OTS experiment with a fixed published honest codeword, give all its honest chain values to the adversary initially. For the chains whose digit is at least two, the lemma bounds finding any complete queried two-step suffix ending at one of those values. Independent oracle tables for positions above those values, and information computed from the published values and those independent tables, may be included as auxiliary information.

This still leaves essential work for the proposed SUF bound. A non-neighbor codeword may require only one backward step in each of two different chains, rather than two steps in one chain. The endpoint selection and reference encoding oracles must be represented with their actual joint law when transferring to SPHINCS. Structural collisions above the disclosed values, FTS opportunities, encoding collisions, and cached-target coverage must share the original budget in one final reduction. This lemma does not justify separately charging every one of those event classes the full q.
