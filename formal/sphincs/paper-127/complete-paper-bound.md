# Assembling the paper 127-bit bound

This note assembles the current paper derivations for the unchanged concrete scheme. The detailed original-experiment transfers are now in small-budget-transfer.md and paid-probe-quadratic.md, with the certificate theorem in cached-target-forecast.md. This is an end-to-end paper argument, not a completed Lean theorem. Its audit requires precise probability projections, described below, and its formalization must check the actual experiments and their hypotheses rather than infer security from passing arithmetic scripts.

Let N=2^128, x=q/N, x_0=2^-15, and

    delta=2^-16,
    epsilon(q)=q/2^222+q/2^237+2^-700.

The scheme uses independently sampled secrets and the original classical random oracle with 256-bit outputs and specified truncations. Retain the actual signing cap, finite retry loops, Option failures, message/randomizer binding, and strong-forgery definition. q counts every original hash call, including honest computation and final verification. The original verdict uses its complete signing log even after an analytical monitor stops.

## Supporting arguments and one original law

- reference-frontier-transfer.md gives the exact conditional law of the reference counter and word at each fixed canonical message. small-budget-transfer.md extends its static-chain discussion to the complete adaptive original experiment, with the same allocated costs and an explicit cap on idealized auxiliary paths.
- long-chain-inversion.md, multiple-chain-inversion.md and two-chain-hits.md give the partial-table likelihood and first-success charging calculations. The small-budget transfer retains their per-chain costs before summing and treats both orders of encoding preparation and inversion.
- cached-target-forecast.md gives the full and near certificate inequalities for the stated message kernel, including targets cached before signing, own-input exclusion, failed responses, and actual costs. discrete-target-coupling.md gives the exact rejected-word bridge and common terminal proposal variable. The guards and numerical moments give epsilon(q).
- paid-probe-quadratic.md gives the exact canonical graph law, the surviving hidden-label induction, the complete no-match SUF decomposition, and the joint primitive/message bound. Its primitive process needs no auxiliary coverage stops.
- fts-guess-kernel.md gives the exact local deferred-secret and forced-first-guess identities. small-budget-transfer.md supplies their original-game induction, support and cost transfer, and application of coverage separately in each forced law.

The small branch uses the original graph execution augmented by independent pool and geometric lengths, stopped at the base coverage guards. The large branch uses that coverage monitor with an additional primitive stop, but analyzes its primitive probability on the original run stopped only at the first primitive match. Adding and erasing rejected values preserves each required projected law. No claim that secrets remain hidden in a fully revealed private cache is used.

A monitor may stop before signing request S+1 because every original continuation then loses. Other exceptions are charged once in the original law. A signing invocation already in progress is completed and its certificates banked before stopping. Coverage bounds these banked counts without adding an exceptional allowance inside each forced experiment.

## Small budgets

For 0<x<=x_0, let Q, A_enc, A_str and A_msg be the disjoint actual charges defined in small-budget-transfer.md. They obey

    Q+A_enc+A_str+A_msg <= q.

The OTS estimate is

    Pr[E_OTS] <= c_Q(x) E[Q]/N + c_enc(x) E[A_enc]/N,
    c_Q(x)=((3/2)+4x+2x^2)/(1-x)+4x/(1-x)^2+82x/(1-x),
    c_enc(x)=1+3444x/(1-x).

It includes nonreference equal-code outputs and both neighbor and non-neighbor backward witnesses. The endpoint-dependent simulation preserves the original charges. Its idealized auxiliary paths are capped universally at q, without assuming that every ideal endpoint has a compatible original secret key.

Fresh noncanonical structural output matches have probability at most E[A_str]/N, including FTS alternative preimages found before disclosure. The certificate theorem gives

    E[C_full] <= (3/(2N)) E[A_msg]+delta*x,
    E[C_near] <= 557x.

A true guess of an undisclosed FTS secret has conditional hazard at most 1/(N-q). Two distinct true guesses cost at most x^2/(2(1-x)^2). For one guess together with a near certificate, force the first guess at slot j and compare by likelihood p_j product_(t<j)(1-p_t)<=1/(N-q). Each forced law preserves the original supported paths and fresh-message kernel. Apply its own near-certificate theorem and sum over j, obtaining 557x^2/(1-x). Certificates may occur before or after the guessed secret.

In the absence of an OTS witness and a cheap structural match, backwards verification fixes every OTS component and every authentication value. Each supplied FTS leaf value is its true secret. A successful response at the same message/randomizer input would then contain this exact signature, contradicting strong novelty. The winning run therefore has a full certificate, a near certificate and a true guess, or two distinct true guesses. This is the exhaustive original-game reduction from the detailed transfer note.

Consequently

    Pr[original SUF win]
        <= c_Q(x) E[Q]/N+c_enc(x) E[A_enc]/N
           +E[A_str]/N+(3/2)E[A_msg]/N
           +delta*x+557x^2/(1-x)+x^2/(2(1-x)^2)+epsilon(q).

For x<=x_0, the four linear coefficients are below 131/80, and the two quadratic FTS terms together are below (9/80)x. Use the shared path budget before adding those quadratic terms. This yields

    Pr[original SUF win] <= (7/4)x+delta*x+epsilon(q) < 2x.

## Larger budgets

For x_0<=x<=1/2, let B be the first external primitive equality match, and let A_B count message calls before B or original termination. The graph posterior and scalar calculation give

    Pr[B]+(3/(2N))E[A_B] <= U(x) <= 2x-(3/4)x^2,
    U(x)=2x-x^2+max(x-1/4,0)^2.

The coverage monitor may stop earlier at its own guards and also stops at B. Its count satisfies A_cov<=A_B pathwise on the same original run. This suffices to pay the coverage term; there is no requirement to expose its auxiliary stopping information to the primitive analysis. With no B or bounded exception, an original strong forgery supplies a banked full certificate. Thus

    Pr[original SUF win]
        <= Pr[B]+E[C_full]+epsilon(q)
        <= 2x-(3/4)x^2+delta*x+epsilon(q).

Since (3/4)x_0-delta=2^-17, the quadratic saving pays at least 2^-17*x throughout this range. For every q>=1,

    epsilon(q)/x <= 2^-94+2^-109+2^-572 < 2^-17.

This gives Pr[original SUF win]<=2x here too. For q>=N/2, use probability at most one. The cases cover every positive whole-experiment query bound q and give the paper inequality Pr[original SUF win]<=q/2^127.

## Audit of the probability interfaces

The OTS likelihood needed one explicit correction of scope: W_i is the density only after forgetting the hidden starting secret and private canonical prefix data. With the secret retained, the density is N times a consistency indicator. small-budget-transfer.md now defines the projection and checks that all charged costs, contacts, markers and stopping rules factor through it. The finite transfer checks include a counterexample to the unprojected W_i claim and verify its exact marginalization. The numerical bounds do not change.

The other interface checks use separate information histories on the same law. Prefix likelihoods may condition on independent auxiliary randomness, including future encoding randomness, because the projected simulator never inspects unqueried prefix cells. Fresh-encoding estimates instead hide unrestricted unqueried encoding rows. Their costs are combined only after taking expectations in the original law. Similarly, coverage may reveal private state suitable for its message kernel; neither the OTS nor FTS secret posterior is claimed in that richer history.

The forced FTS comparison is made in the deferred state, before completing its hidden secrets and before adding rejected proposal values. Each forced hit or miss is a positive conditional branch there. Completing its remaining secrets and private canonical rows then realizes an original supported execution with the same observations and hash costs. Coverage is instantiated separately in each forced law; no rejected-word density is canceled between different laws.

Finally, the coverage monitor banks completions before post-record stopping, and its terminal-word law comes from the bridge kernel before revealing the accepted record. Its boundary potential pays adaptive creation through actual message calls and the remaining creation budget. Initial short-pool and later cache, deficit or proposal exceptions are charged once in the original law. In the large branch the pathwise A_cov<=A_B comparison avoids exposing those auxiliary stops to the primitive posterior. These are the interfaces the Lean statements must retain.

## Remaining completion requirements

The paper now supplies the original-game constructions that the closing formulas need. Before treating them as established formal results, prove the projected endpoint-dependent OTS likelihood, capped auxiliary query counts, encoding-history estimates, and deferred-secret support argument with their stated interfaces. The original statement must remain the left side of every final transfer.

The Lean endpoint expected_poissonCertificateGame_count_le_message_excess now bounds the original monitor's expected banked certificates by c times its expected actual message calls plus q times the independent terminal-price excess above c. It derives the actual count and prefix invariants and accumulates the adaptive charges, rather than assuming them. The Poisson expectations in that endpoint remain unevaluated in Lean, and its original-signer instantiation does not yet cover the forced FTS kernels.

Formal completion requires the numerical full and near certificate estimates and exceptional probabilities; the coverage extension to deferred-secret kernels; the exact graph and both primitive transfers; the allocated small-budget and joint large-budget inequalities; assembly of the public theorem; and an audit of its assumptions and axioms. No public 127-bit Lean theorem follows merely from the existence of this paper argument or its finite consistency checks.
