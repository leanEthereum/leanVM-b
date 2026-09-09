# Transferring the small-budget witnesses to the original game

This note supplies the original-experiment transfer used by the small-budget branch. It combines the static chain calculations with the exact graph and reference construction, the deferred FTS kernels, and the stopped coverage theorem. The argument is on paper; it is not a Lean security theorem. It preserves the original algorithms, independent secrets, finite failures, own-input exclusion, and whole-experiment syntactic hash budget.

Fix an original adversary admitted by HasHashQueryBound at 1<=q<=2^113. Write N=2^128, x=q/N, delta=2^-16, and epsilon(q)=q/2^222+q/2^237+2^-700. We derive

    Pr[original SUF win] <= (7/4)x + delta*x + epsilon(q) < 2x.

The supporting probability and cost estimates below are derived in presentations of one original execution. Their information histories may differ. No endpoint assumes its own global witness probability or assigns a separate full q budget to every linear contribution.

## The shared stopped law and its costs

Use the exact reference counters J_p, words D_p, and canonical graph of paid-probe-quadratic.md. Add an independent terminal pool length J_pool and independent geometric block lengths with the laws in cached-target-forecast.md. Retain the original execution underneath the monitor. The base monitor stops at original termination, the signing cap, or its cache, deficit, short-pool, or geometric-prefix exception. An active signing invocation is completed and its certificates banked before applying post-record guards. It does not stop at a guessed secret or an OTS contact.

The base stop uses the message cache, completed signing views, actual costs, J_pool, and geometric lengths. It needs no rejected proposal values. Denote this projected stopped law by R. Attaching rejected words using the exact record-first bridge preserves R; its full and near certificate counts, message count, and stopping rule depend only on the projected variables. Thus the coverage theorem gives directly in R

    E_R[C_full] <= (3/(2N)) E_R[A_msg] + delta*x,
    E_R[C_near] <= 557*x.

A coverage certificate includes the target input, not just its digest value. Successful views at that same input are excluded. The original exception allowance is at most epsilon(q). Stopping before request S+1 discards only original losing executions; the original final verdict still reads the complete log.

Split actual monitored hash calls into the following charges. Freshness for an external row means not previously observed externally, regardless of private honest evaluations.

| Charge | Counted calls |
| --- | --- |
| Q | Distinct external inputs at valid OTS prefix domains, whose step is below the digit D_p(j). Malformed payloads may be included. |
| A_enc | Fresh external nonreference inputs at valid OTS encoding domains, including restricted invalid cells. Every input at an exhausted address is nonreference. |
| A_str | Fresh external inputs at all other valid structural domains, including forward OTS steps and FTS leaves. Canonical reads may be included. |
| A_msg | All actual calls at the proper message prefix and fixed parameter, including repeats, internal digest attempts, and verification. |

These classes have disjoint serialized prefixes, except that the OTS prefix/forward split partitions chain steps. Reference encoding reads are omitted from A_enc. Every counted item consumes a distinct original hash slot, so

    Q + A_enc + A_str + A_msg <= q

pathwise. Honest non-message calls, external repetitions outside the message class, and unrelated domains contribute unused slack. Counting malformed prefix rows in Q enlarges an upper bound; such a row is independent auxiliary randomness for a digest-input chain challenge.

## An OTS simulator that preserves the allocated costs

Condition first on the reference counters and words, which are independent of all non-encoding data. For each positive reference digit d_i, retain the original independent prefix functions H_(i,0),...,H_(i,d_i-1) and independent starting secret S_i. Publish their endpoint Y_i. A zero digit publishes its secret and needs no hidden prefix challenge. Prefixes at different chain addresses use disjoint serialized domains.

Collect the remaining independent randomness in R_aux: forward and other structural functions, FTS secrets and functions, unused secret coordinates, the independent randomness for conditional encoding rows, message rows and signing coins, and the monitor auxiliaries. Given the endpoints Y, J, D and R_aux, the simulator computes all forward chain values, OTS leaves, hypertree roots, FTS public keys, canonical messages M_p, and the public key. It generates each encoding row with the exact conditional law: invalid before J_p at M_p, equal to encoded D_p at its reference, and uniform elsewhere. High output bits are independently retained. The dependence of these data on Y is part of the simulation; an idealized endpoint must be used consistently when computing them.

The simulator reproduces actual signing responses and failures without reading an unqueried prefix cell. A successful OTS component contains Y_i and J_p. Its authentication path depends only on forward and structural data. The finite digest loop is run unchanged, including all repeated attempts and exhaustion. All signLayer invocations are performed; an exhausted canonical encoding causes the original Option failure and discloses no FTS secrets. The selected digest is retained in the analytical record even after that failure.

Private honest prefix computations can be omitted as function evaluations because their intermediate inputs and values are not observed. Their costs cannot be omitted. Each omitted chain computation has a fixed number of steps determined by D or the full chain length. Tree recomputations have fixed shapes; digest attempts and reference-counter searches give the remaining variable costs. The simulator debits these original hash slots and releases each response only after its original cost has been counted. It routes every external and verification digest-input prefix query to the corresponding prefix function. Private cache occupancy is not part of its observations: full consistent functions give the same later external answers whether or not honest reads were materialized.

On real prefix challenges this simulator has exactly R's observations, stopping rule, certificate data and charges. To define every idealized experiment, also halt the simulator before it would consume slot q+1. On R this cap never fires, by the original whole-experiment bound. An independently idealized endpoint need not have a preimage in its complete function tables, so a corresponding real secret key need not exist. The cap gives those auxiliary paths a q budget without presuming that they are original executions. Truncating an auxiliary execution is permitted in the chain estimates and preserves every real event and allocated cost used below.

R_aux may be fixed when analyzing prefix likelihoods. Equivalently, use lazy auxiliary kernels that never inspect an unqueried prefix cell; the density identities involve only finite observed transcripts. With it fixed, all auxiliary behavior is a function of the published endpoints and previously queried prefix replies; it never reads an unqueried prefix cell. This is sufficient for the adaptive partial-table identities. It does not license using a fresh-encoding probability after conditioning on an entire future encoding table. That separate probability is proved below in a history that hides unqueried encoding rows, then integrated into the same R expectations.

## Likelihoods and allocated chain estimates

For a particular chain i, let I_i be the same capped simulator, with Y_i independently uniform instead of generated from its secret and prefix. All other challenges remain real. Use the same endpoint-dependent auxiliary kernel in both laws. If W_i is the number of starting values whose full prefix ends at Y_i, the complete-table density of R relative to I_i is W_i. The starting secret itself need not be exposed: the simulated original responses depend on it only through Y_i.

At an adaptive transcript T, let K_j contain the queried rows of prefix function j, let u_j indicate its unqueried rows, and put P_j=K_j+u_j*1^T/N. The unqueried cells in I_i remain independent uniforms even with adaptive auxiliary queries and the cap. Hence the transcript density is

    w_i(T) = E_(I_i)[W_i | T] = 1^T P_0 ... P_(d_i-1) e_(Y_i).

The pointwise matrix inequality P_j>=u_j*1^T/N gives

    w_i(T) >= product_j(1-a_j/N) >= 1-Q_i(T)/N >= 1-x,

where a_j counts the queried rows of function j. Thus for every nonnegative stopped transcript cost Z,

    E_(I_i)[Z] <= E_R[Z]/(1-x).

This inequality concerns the actual allocated cost of chain i. It does not replace that cost by q before summing over chains. Conditional on all published endpoints and auxiliary randomness, different prefix-table constraints factor; adaptive query choices add no constraints beyond the recorded replies. This also justifies the conditional restart used for a second distinct contact.

For completeness, the charging calculation from long-chain-inversion.md and multiple-chain-inversion.md retains the following numerators. Stop at the first fully queried two-edge suffix reaching Y_i. Expand the likelihood according to its last unqueried edge. If C_r counts queried suffixes from level r to Y_i, then w_i<=1+sum_r C_r. Before the stop only the one-edge suffix count k can be nonzero. A fresh productive last-edge query contributes at most

    (2+k+sum_r m_r)/N,

where m_r counts previously queried paths ending at its input. Each earlier queried input contributes to these multiplicities at most once. The pathwise baseline is therefore at most 3Q_i/2. A penultimate query has weighted risk at most [k(k+2)+k*M]/N, and each older input contributes to M at most once. In I_i, fresh last-edge answers hit Y_i with probability 1/N, so

    E[k_final] <= E[Q_i]/N,
    E[k_final(k_final-1)] <= 2q E[Q_i]/N^2.

The remaining contributions are at most 4q E[Q_i]/N^2+2q^2 E[Q_i]/N^3. Convert this allocated ideal cost using w_i>=1-x, then sum over chains. Each chain-specific stopped Q_i is at most that chain's count in R's full monitored prefix, so the sum is at most Q. We obtain

    Pr_R[some two-edge suffix] <= ((3/2)+4x+2x^2)/(1-x) * E_R[Q]/N.

For a first one-edge contact, the likelihood numerator is two per last-edge query and one per older input whose known path reaches that query. The same conversion gives

    E_R[number of contacted chains] <= 2 E_R[Q]/(N(1-x)).

After the first contact, restart on uncontacted chains. At a fixed real transcript T, idealizing only chain i gives conditional density w_i(final)/w_i(T). Thus E_(I_i^T)[Z]/w_i(T)<=E_R[Z | T]/(1-x). Old queried prefixes can be used; their total cost plus twice the future-query cost is at most 2q. The conditional chance of another distinct contact is consequently at most 2x/(1-x). Combining with the allocated first-contact bound yields

    Pr_R[two distinct contacts] <= 4x/(1-x)^2 * E_R[Q]/N.

A different non-neighbor word of the same digit sum either lowers one chain by at least two, or lowers two different chains. Each accepting backward path supplies the corresponding queried suffix. Thus, putting

    c(x)=((3/2)+4x+2x^2)/(1-x)+4x/(1-x)^2,

its non-neighbor witness probability is at most c(x) E_R[Q]/N. These arguments apply to the whole finite family of chain addresses, without a chain-count factor.

## Reference encodings and both orders of preparation

Use an encoding history that reveals the non-encoding graph and prefix information, J and D, and previously observed encoding rows, but not unqueried unrestricted encoding rows. The original simulator's requests use only past replies. A fresh nonreference encoding row either is restricted invalid, or has a uniform low output. A valid word has a unique low encoding. Consequently

    Pr_R[some nonreference equal-code output] <= E_R[A_enc]/N,
    E_R[number of chains marked by a unit neighbor] <= 1722 E_R[A_enc]/N.

A unit neighbor lowers exactly one chain and raises another, giving at most 42*41=1722 possible outputs. Each such output marks only its lowered chain; there are at most 41 neighbors lowering a specified chain. A marker is placed when its oracle answer is first observed, regardless of when the adversary chooses to use it. Honest internal encoding reads produce only invalid rows or their canonical reference, so they cannot create an uncounted different-word marker.

If a chain's first contact precedes its marker, a fresh encoding query can produce at most 41 suitable outputs per previously contacted chain. Summing over at most q encoding slots and applying the allocated expected contact count bounds this order by

    82x/(1-x) * E_R[Q]/N.

If the marker precedes first contact, fix its chain i and apply the first-contact likelihood calculation only after the marker. Pre-marker prefix work is allowed: every previously queried input can still enter a later productive path, but at most once. The total numerator is at most 2q times the indicator that the chain was marked before its first contact or termination. At this stopping time, w_i>=1-x converts that ideal indicator probability to its real probability. Sum over chains and apply the real expected marker count. This order is at most

    3444x/(1-x) * E_R[A_enc]/N.

Only prefix likelihoods were conditioned on all independent auxiliary randomness. The uniform encoding estimates were established in their own history and have already been integrated into R expectations before use here. There is no conditional independence claim between a marker and its inversion. There is also no assumption that inversion work starts after preparation.

Define E_OTS as a nonreference equal-code output, a non-neighbor backward witness, or a unit-neighbor marker with its lowered chain contacted. The preceding estimates give in the original stopped law

    Pr_R[E_OTS] <= c_Q(x) E_R[Q]/N + c_enc(x) E_R[A_enc]/N,
    c_Q(x)=c(x)+82x/(1-x),
    c_enc(x)=1+3444x/(1-x).

This is the required transfer with allocated costs. The endpoint-dependent auxiliary simulation, its universally capped hybrids, and the two separately integrated information histories are what allow the static bounds to be used here.

## Cheap structural matches and the deterministic reduction

For the cheap-match estimate, expose the entire canonical graph, including its secrets, but leave noncanonical function rows hidden. This is a different information history on the same R. Honest structural evaluations only read canonical rows. Each fresh external noncanonical row at a non-prefix structural domain therefore has a uniform low answer; equality with that domain's canonical output has probability 1/N. Canonical rows cause no such event. This includes an FTS alternative preimage queried before any later disclosure. Denoting their union by E_str,

    Pr_R[E_str] <= E_R[A_str]/N.

An FTS true-secret query is canonical and is not an alternative preimage. It is handled separately below. For this output-match bound, revealing its secret merely makes that classification visible; it does not change the original adversary.

Assume an original winning run has no exception, E_str, or E_OTS. Its monitor then includes all the relevant verification calls. Trace accepting verification backwards from the public root. A noncanonical child tuple producing a canonical Merkle node or OTS leaf would be E_str, so the authentication siblings and recovered chain endpoints are canonical. For each chain, its verified path must pass through the canonical frontier if the claimed digit is below D: a merger strictly above that frontier would use a forward-domain noncanonical output match. The path below the frontier need not be the secret's own path; its queried path to the frontier is exactly the backward witness counted above.

If the verified valid word differs from D, equal digit sums make it a non-neighbor witness or a unit neighbor with both its marker and lowered-chain contact. That would be E_OTS. If it equals D at a nonreference input, it is the equal-code part of E_OTS. Thus every OTS component uses the canonical message, counter, and frontier values. On canonical encoding exhaustion there is no such accepting counter. Repeat through all three linked layers to the canonical FTS key.

The same backwards tracing through the FTS roots and authentication paths fixes every leaf hash. Without E_str, each supplied leaf value is its actual secret. Every still-undisclosed such secret is queried externally at the latest by final verification. The argument fixes all signature fields, including all 26 hypertree path entries. If the same message/randomizer input had a successful response, the canonical fields give that exact earlier signature, contradicting strong novelty. Therefore source signing views at the forgery's own input never supply a winning run in this case.

If all 14 required leaves were disclosed by successful responses, the run has a full certificate. If exactly one was not, it has a near certificate and a true guess. If at least two were not, it has two distinct true guesses. Distinct coordinates remain distinct even when their secret values coincide. A failed signing response discloses no leaf, and an alternative preimage is already in E_str. This exhausts the original strong-forgery event on a nonexceptional run.

## Deferred FTS simulation after arbitrary earlier guesses

For this analysis, expose the canonical graph cut and, if desired, all OTS secrets and function data. Keep FTS secrets and unobserved FTS leaf rows deferred. Conditional on the public FTS leaf hashes, all other graph data can be generated without inspecting these secrets. Later OTS events may occur; this analysis does not stop at them. Signer control, failure masks, and selected disclosure coordinates still depend only on the message trace and exposed graph, as checked in paid-probe-quadratic.md.

An active FTS coordinate has a secret uniform on its unqueried digest candidates U. A fresh candidate z in U has the exact kernel

    hit with probability 1/|U|: set secret=z, return its canonical low hash, retire;
    miss otherwise: remove z from U, return an independent uniform low hash.

A miss answer may equal the canonical hash. It remains a miss of the actual secret, and the residual secret stays uniform on U without z. Full high bits and externally observed rows are memoized. Malformed payloads cannot be the true secret and do not remove candidates. A successful original signing response discloses each selected active coordinate by sampling uniformly from its current U and retiring it; failed responses disclose none. The disclosed coordinate is selected without inspecting its secret value. Retired coordinates retain their fixed secrets and row tables.

The joint mass, conditional on the previous history, for a miss answer y and residual secret s is 1/(|U|*N) for every s in U without z, even when y equals the public hash. Product normalization across the distinct FTS coordinates therefore proves this invariant through hits, misses, repeated queries, alternative preimages, adaptive later requests, and disclosures. Honest internal evaluations read public graph labels privately and retain their original costs. Their secret-dependent cache entries are not exposed as external rows. Completing each still-active secret from U and programming its canonical row reconstructs the corresponding original execution.

At every eligible original hash slot t, let p_t=1/|U_t|; otherwise set p_t=0. At most q candidates have been excluded, so p_t<=h=1/(N-q). The history includes all previous analytical hit flags, while the original adversary receives only its ordinary replies. Retiring guessed coordinates means the sum of hit indicators counts distinct true guesses. For two slots s<t, conditional expectation gives E[H_s H_t]<=h E[H_s]<=h^2. Thus

    Pr_R[two distinct true guesses] <= choose(q,2)*h^2 <= x^2/(2(1-x)^2).

## Forced first guesses and near certificates in the original law

For each hash slot j<=q, construct R_j by replacing all earlier eligible hit/miss choices by their conditional miss kernels, and the choice at j by its conditional hit kernel if eligible. All other transitions, including future choices after j, keep their original kernels. If j is ineligible or not reached before the base stop, use likelihood zero. Pad terminal records with inert slots to give the common index set 1,...,q.

The R_j paths on which j is eligible have density for the corresponding real first-hit branch

    L_j = p_j * product_(t<j)(1-p_t) <= 1/(N-q).

This is an identity of kernels in the projected law before rejected values are added. Message cells, high bits, signing responses and disclosures, and the independent pool and geometric lengths all have the same kernels along corresponding paths. Therefore, for any nonnegative projected terminal statistic F,

    E_R[1_(first true guess at j)*F] = E_(R_j)[L_j*F].

Every forced branch has positive original conditional probability: an eligible candidate is in U, and before a forced miss |U|>=N-q>1. No disclosed value or previously queried row is changed. Completing the deferred secrets as above realizes a supported original execution with the same visible replies and original hash costs. This transfers the original q bound to R_j. Unlike an OTS endpoint idealization, this argument uses only conditional branches of the real deferred experiment and needs no unsupported-key assumption.

The modified transitions inspect only the current U, candidate, public hash, and observed rows. Fresh message cells remain uniform, and the original finite digest loop and post-selection signing algorithm remain intact. Every completed invocation still costs at least L=1024, including digest exhaustion and later encoding failure. The coverage kernel's initialization, response, disclosure-view and cost conditions therefore hold in each R_j. Its current private environment is the deferred state, not a prematurely revealed final secret key.

Now attach a fresh rejected-word bridge to each R_j using that law's current record kernel. Its erasure preserves R_j and its base stop; it need not have the same rejected-value probabilities as another law. The coverage theorem gives E_(R_j)[C_near]<=557x. Taking F=1_(C_near>=1) and summing the density identity over j yields

    Pr_R[some true guess and C_near>=1]
        <= q/(N-q) * 557x = 557x^2/(1-x).

Certificates may precede the guess, follow it, or be completed by a later signing response. Banking retains them after subsequent exceptional stopping. No exception probability is multiplied by the number of forced experiments: their certificate expectations already apply to stopped executions, and epsilon(q) is charged once for the original run.

## Closing with the shared allocations

The deterministic implication and all estimates refer to R's same projected costs and certificates. They give

    Pr[original SUF win]
        <= c_Q(x) E_R[Q]/N + c_enc(x) E_R[A_enc]/N
           + E_R[A_str]/N + (3/2) E_R[A_msg]/N
           + delta*x + 557x^2/(1-x) + x^2/(2(1-x)^2) + epsilon(q).

For 0<x<=2^-15, monotonicity and exact rational endpoint evaluation show

    max(c_Q(x),c_enc(x),1,3/2) < 131/80,
    557x/(1-x) + x/(2(1-x)^2) < 9/80.

Use Q+A_enc+A_str+A_msg<=q before adding the two quadratic FTS terms. The resulting bound is

    Pr[original SUF win] <= (131/80+9/80)x + delta*x + epsilon(q)
                         = (7/4)x + delta*x + epsilon(q) < 2x.

The final strict inequality follows from epsilon(q)/x<=2^-94+2^-109+2^-572 and delta=2^-16. Together with the large-budget argument, this supplies an end-to-end paper derivation of the requested slope for the original experiment. Its mathematical transfers and subsequent Lean formalization still require scrutiny; arithmetic or finite-kernel checks alone do not certify this claim.
