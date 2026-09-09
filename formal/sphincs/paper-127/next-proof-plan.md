# Paper derivation and formalization plan for 127-bit SUF

This paper review starts from the unchanged concrete scheme audited at commit 106024f5 and the subsequent paper coverage and graph derivations. It proposes a route for the unchanged experiment in Statement.lean, without adding Lean code. The public 126-bit theorem is established; the 127-bit theorem is not. The closing arithmetic and the abstract charging arguments below have enough slack. The large-budget application is written in paid-probe-quadratic.md, and the small-budget completed-witness transfer is now written in small-budget-transfer.md. Together with the coverage derivation they supply an end-to-end paper argument, still requiring audit and formalization. This note incorporates the two histories from two-filtration-audit.md, audits the local hidden-label transitions, and specifies the mathematical endpoints to establish before resuming formalization. The additional results of this review are a single nonnegative potential that pays adaptive certificate creation directly from actual message calls and the original path budget, and a message-cache argument showing why the auxiliary rejected indices need not leak hidden secrets.

Write N=2^128, I=2^26, L=1024, S=2^24 and x=q/N. Here q bounds actual hash calls on every execution path, including key generation, signing, adversarial calls and verification. The desired statement is Pr[SUF forgery] <= 2x. It suffices to handle 1 <= q < N/2: larger budgets follow from probability at most one, and the public definition requires positive q. Retain independent sampled secrets, all finite retries, Option signing failures, and the original signing log cap.

The missing bit is a coefficient problem. Adding any positive coverage allowance to a primitive bound of 2q/N cannot establish the target. The plan gives large budgets a quadratic saving in a joint primitive-and-message bound, and gives small budgets a fixed saving by counting useful completed witnesses. Neither a terminal occupancy mean nor a count of individual secret guesses supplies both savings.

The recommendation from this review is to audit the now-written two-range argument against its original-experiment requirements before formalization. The expanded [stopped coverage proof](cached-target-forecast.md) now derives the local shape transitions, fresh-target charges, and complete certificate inequality from the message kernel, and identifies its instantiation in the original signer. Its deferred-secret application uses the exact graph simulation and inherited path budget now derived in small-budget-transfer.md. The committed Lean branch connects certificate accumulation and its pathwise and expected payments to the original whole game; the complete numerical coverage result is not yet formalized. The terminal-word construction, adaptive completion-kernel identity, original-game projection, Poisson-length mixture, and local forecast comparison are now checked in Lean. The actual monitored count and room invariants and the accumulated terminal-price excess bound are now checked too. The numerical Poisson estimates, exceptional probabilities, coverage extension to deferred-secret kernels, and cryptographic transfers are still missing. The expanded [canonical-graph argument](paid-probe-quadratic.md) now gives the exact sampling order, serialized-domain audit, hidden-label induction, exhaustive SUF decomposition, and large-budget assembly. The [small-budget transfer](small-budget-transfer.md) now gives the remaining original-game likelihood and cost arguments. The next audit should check those concrete transfers before formalization. None of these new paper endpoints is a public 127-bit Lean theorem.

## 1. Define one experiment before combining estimates

Start with the original game and add analysis variables. At each OTS address, sample the canonical counter and codeword using the exact conditional encoding-table construction in reference-frontier-transfer.md. Sample canonical structural labels along the acyclic graph, programming each distinct hash domain at its unique canonical input. This must preserve the original joint distribution, including the high output bits. The canonical OTS message is fixed by the non-encoding graph; it is not a message chosen after searching encodings.

Expose canonical OTS frontier and forward values, FTS leaf hashes and internal nodes, and the reference encoding information. Keep OTS labels below the frontier and undisclosed FTS secrets hidden. The original adversary ignores the additional advice. Honest internal evaluations compute the programmed graph without disclosing their secret-dependent inputs. Their actual hash calls still consume q.

Use two histories on the same probability space. The primitive history G records the graph advice, message queries and answers, external replies, returned signing responses, and actual hash counts. It omits all coverage auxiliaries and honest secret-dependent non-message inputs. It stops only at the first primitive match B or original termination. Its hidden-label posterior is an explicit invariant. The coverage history F additionally contains consumed proposal values and the current environmental state needed for the signing kernel. In the original lazy-oracle experiment this can include the private key and current cache; in a forced-secret experiment it contains the current deferred state, rather than secrets that future transitions will select.

Only the coverage history needs independent unused proposals and fresh unqueried message cells. Only the primitive history needs hidden labels to retain their uniform posteriors. For the large branch, coverage additionally stops at B, so its message count A_cov is pathwise at most the primitive count A_B in the same underlying original execution. This inequality suffices to combine their unconditional expectations; equality of the stopped counts is unnecessary. A posterior invariant for the richer coverage history is unnecessary and is not asserted. Recording actual costs in G still requires checking that honest control flow depends on the exposed graph and digest/encoding outcomes, rather than undisclosed secret values.

The existing raw forecast is written using a full Lean cache and secret-key record. Mathematically its ingredients are the fixed parameter/root, the message portion of the cache, and the observed signing views. The coverage theorem should accept arbitrary non-message kernels that preserve fresh message cells, the finite digest loop, and the stated cost and disclosure constraints. This is needed for its later use in forced-secret experiments; a theorem limited to a fully revealed, fixed original key would not by itself provide that application.

The decisive deterministic implication is that an accepted strong forgery either has a primitive deviation or has an admissible message digest whose 14 coordinates are supplied by successful signing inputs other than its own input. If its own message/randomizer input was signed successfully and every component is canonical, the signature is identical to that response and is not a strong forgery. Failed responses do not disclose signing views. An OTS encoding failure after digest selection must still retain the selected digest in the analytical record.

The expanded canonical-graph note derives this correspondence for the large branch, including the control-flow and signature-field checks below. Its argument is an induction through the original execution, beyond the local sampling identities. The small branch uses the separate transfer in small-budget-transfer.md for useful witnesses after guesses have occurred.

The exact graph construction must not condition on different node labels having different values. Equal 128-bit values at different nodes are allowed. Distinct valid tweaks, rather than distinct sampled values, give independent oracle rows for different canonical graph nodes. At each node, conditional on its children, its canonical input is fixed in a domain not used by another canonical node; sampling its output and then filling the other rows is the ordinary random-function law. Classify external requests by their actual serialized bytes: an out-of-range typed address that serializes to a valid address accesses that same domain. Inputs outside every relevant graph domain are auxiliary oracle rows. Unused secret-key coordinates retain their original independent distributions.

Canonical encoding exhaustion is also part of this construction. At an exhausted OTS address, every canonical-message counter cell is invalid, and the auxiliary reference word is used only to define the analytical frontier. It is not a signature the signer returned. At a nonexhausted address, cells before the first valid counter are uniformly invalid, the reference cell has the sampled valid word, and all unrestricted cells remain uniform. Independent high output bits must be retained at every row. This prevents either rejecting rare original keys or replacing the actual encoding law by a more convenient one.

There is a concrete deterministic way to audit the implication. Trace an accepting verification down from the public root. Whenever a computed canonical parent has noncanonical children, record a noncanonical output match. Otherwise the children and eventually the OTS endpoints must be canonical. In a chain, a merger above its disclosed frontier is another such output match; absent that event, a claimed value below the frontier must supply a complete queried path to the frontier. For the forest, an accepted leaf opening is either its true secret or an alternative preimage of its canonical leaf hash. This tracing argument accounts for every component the verifier reads and includes its final hash calls in the budget.

## 2. Prove the stopped certificate estimate

The common coverage result needed by both budget ranges is

    E[C_full] <= (3/(2N)) E[A_msg] + delta*x,
    E[C_near] <= 557*x,                 delta=2^-16.

C_full counts distinct completed full-target certificates. C_near counts target/omitted-coordinate pairs with the other 13 coordinates covered. A_msg is the actual number of message hash calls in the same stopped execution. A certificate's own input is excluded from every source signing view. Previously completed certificates remain counted after a later stop; only pending forecasts are discarded. The result must also apply when non-message transitions are replaced by the forced-secret kernels used in step 5.

Here is the required kernel contract for that last application. It is stronger than merely saying that fresh messages are uniform, and weaker than requiring a fully sampled original secret key in the coverage history.

| Component | Required property |
| --- | --- |
| Message oracle | Each previously unqueried proper message input receives a uniform 256-bit answer; later calls return the same answer. Its 176 digest bits have the original layout. |
| Digest selection | Every executed attempt samples an independent uniform 128-bit randomizer and makes its actual message call, including repeats; the first admissible digest is selected, with the original finite limit. These are all message-domain calls inside the invocation. |
| Completed signing view | A macro contributes at most one successful view, at precisely its selected input, index and leaves. Digest exhaustion contributes none; later encoding failure may discard the view but retains the selected digest in the analytical record. |
| Other transitions | They may depend on current private state and previously observed cells, but cannot inspect unqueried message cells or unused proposals. They cannot add arbitrary successful signing views. |
| Resources | The fixed root and parameter, cap of S invocations, whole-path hash budget q, and actual cost of at least L per completed invocation are retained. |
| Stopping | Additional stops are adapted to the recorded execution; a stop during a macro takes effect after its costs and possible first completions have been recorded. |

The expanded coverage note derives the local target-shape proof from these properties: product expansion gives the fresh-query and signing operators, and their positive commutator gives the continuation forecast. This is a paper derivation for the stated kernel, rather than an assumption of a global certificate bound. Its Lean translation must retain that scope; a theorem only for the original fixed-key signer would leave a new theorem to prove in every forced-secret experiment. Conversely, this contract does not grant arbitrary secret disclosure when applying the forgery decomposition: the original and forced primitive experiments must separately justify their allowed disclosures.

The local invariant is a bank plus pending forecasts. For a required coordinate set D, let B_h contain targets already certified and let phi_h(z) be the target-shape forecast at remaining actual budgets q-t_h and S-s_h. Define

    M_h = |B_h| + sum_(admissible cached z not in B_h) phi_h(z).

The zero-future-work term gives phi_h(z)>=1 as soon as all required coordinates are covered, even at an exceptional post-state. After the actual transition, bank first completions and remove their pending terms. If a stop fires, discard the other pending terms. Both operations can only decrease the tentative ledger. The old-target transition inequality and the fresh-target price must therefore give

    E[M_(h+1) | F_h] <= M_h + a_h W_D(h)/N.

Key generation creates no message targets, so M_0=0. There are at most q charged transitions: each external hash costs one and every signing macro costs at least one. Finite telescoping, with terminal pending forecasts discarded, yields

    E[C_D] <= N^-1 E[sum_h a_h W_D(h)].

This is the mathematical role of the committed local banking lemmas. The expanded paper proof connects the actual adaptive execution, the cost identities below, and the shared terminal domination. The complete Lean endpoint still needs this assembly; it cannot be replaced by assuming the displayed global inequality.

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

One construction runs the original signer first and independently adds a geometric number of rejections. The other proposes uniform indices and accepts index i with probability I*p_i/beta, then draws the record conditional on that index. Summing over rejected words of length g-1 gives

    P[omega,G=g | h] = K_h(omega) beta^-1 (1-beta^-1)^(g-1).

Thus erasing rejected values preserves the original record together with an independent geometric length. The large-branch primitive history can omit the lengths as well. For F, the proposal-first construction supplies independent uniform proposals; release the completed record at acceptance, leaving its unused suffix independent. Induction through completed boundaries must establish these properties for adaptive records. Revealing the record, and hence its selected index, before exposing its accepted proposal would not justify calling that proposal uniform.

For this particular signer, the bridge has an additional useful property: p_i is determined by the requested message, fixed parameter/root, and current message cache alone. To see this, condition on that cache and induct on the finite attempt counter. A randomizer is independent uniform; a cache hit has its recorded answer; a fresh cell has a uniform answer and extends only that cache. These rules determine the entire digest-loop distribution, including F, E, E[T_m], and the cached index counts in the formula for p_i. The subsequent OTS computations cannot alter the retained selected index. This argument also applies in a forced-secret law whenever its fresh message cells retain that same conditional kernel.

Let G_h contain this message cache, and define r_i=(beta/I-p_i)/(beta-1). The rejected word is sampled with r(G_h), independently of the original record. For a geometric length g, a rejected word u of length g-1, an original projected record omega, and any remaining hidden data X, the augmented joint mass factors as

    Pr[X,omega,g,u | G_h]
      = Pr[X,omega | G_h] * beta^-1*(1-beta^-1)^(g-1)
        * product_(a=1)^(g-1) r_(u_a)(G_h).

This factor is independent of X and omega. The selected final letter is already recoverable from omega's message trace, with an independent dummy on digest exhaustion. Thus adding the rejected word and dummy does not further change the hidden-secret posterior conditional on the original projected record. In particular, the rejected values are not intrinsically secret-dependent leakage. This factorization may be derived after averaging over private keys and non-message caches with the same message projection; revealing those private objects is not required.

The two histories remain a sufficient way to organize the proof. This extra observation is a concrete compatibility argument, and suggests stating the coverage kernel in terms of the message cache and successful views. It does not justify giving the primitive analyst the full private cache. Its use in the concrete proof requires showing that the recorded message trace reconstructs all relevant cached cells and that the selected index survives encoding failure. The forced-first-guess comparison can still be done before adding rejected values, avoiding any need to cancel their likelihood factors.

There is a finite-kernel way to state precisely the needed induction. For a fixed terminal length J and a consumed word u, let K_J(u) be the distribution obtained by keeping the first J letters of u if |u|>=J, or appending J-|u| independent uniform letters otherwise. For each active signing macro with its entire original record omega and auxiliary block b, prove the identity

    sum_(omega,b) Pr[omega,b | current state] K_J(u ++ b) = K_J(u).

For |u|>=J both sides are the same point mass. Otherwise, the proposal-first factorization makes the next letter uniform. Induction on J-|u| proves the identity: rejection repeats the same record kernel, while acceptance releases its conditionally sampled record, whose probabilities sum to one, and leaves an independent suffix. The record may determine an arbitrary later continuation; repeat the same identity from that continuation's state. External steps and inactive monitoring append no letters, so their identity is immediate. This is also why an invocation that overruns J can finish unchanged: its first J letters already determine K_J, and no post-overrun domination is needed.

The identity is stronger than an unconditional uniform marginal. At every completed boundary it identifies the conditional law of the eventual terminal word given the current private state and consumed word. It neither says that the whole terminal word is independent of the game nor allows unused letters into the conditioning history. For any nonnegative terminal payoff g, Phi_h=E[g(terminal word) | F_h] is therefore a martingale. Equivalently Phi_h is the explicit finite sum of g against K_J(u_h), so the argument can use kernel sums throughout.

Independently choose J ~ Poisson((19/50)I). Complete the proposal sequence after termination with independent uniform values. The counts Z_i in its first J entries are independent Poisson(19/50) unconditionally. Stop initially if J < 25313293 and after a completed signing invocation if the number K_s of consumed proposals exceeds beta*s+131072. On every clean boundary, the unused length m satisfies

    m=J-K_s >= beta*(S-s)+13.

The existing positive-polynomial argument first absorbs hypothetical cache growth into its moments, then bounds the signing increment rate by v with I*v <= beta. It does not interpret an unbounded polynomial operator as a probability kernel. For r=S-s, d<=14 and j<=d,

    (r)_j v^j <= (beta*r/I)^j <= (m)_j/I^j.

Since actual successful index counts are bounded by consumed proposal counts, expansion of shifted powers in falling factorials gives one terminal domination at every clean boundary:

    W_full,h <= E[R_full | F_h],       R_full=sum_i Z_i^14/2^48,
    W_near,h <= E[R_near | F_h],       R_near=(14/2^38)sum_i Z_i^13.

The arithmetic in coverage-closing-checks.py supplies E[(R_full-3/2)_+] < delta and E[R_near] < 557. These are unconditional terminal estimates; the game is stopped on exceptions, not conditioned on their absence.

The remaining charging argument is short once this common terminal domination is established. An external fresh message query has predictable creation multiplier a_h=1. A signing invocation has multiplier a_h=L*f_h, where f_h is its conditional fresh-selection probability. To prove the finite-loop payment, let I_l indicate that attempt l executes on a fresh cell, before its answer is drawn, and let V_l indicate admissibility. Then E[I_l V_l | the preceding history]=I_l/L, while sum_l I_l V_l is exactly the indicator of fresh selection. The finite sum gives E[number of fresh message calls in that invocation | F_h]=L*f_h, including cached acceptance and digest exhaustion.

For pathwise payment, use total actual hashes instead. A signing multiplier is at most L. Digest exhaustion spends 2^32 message hashes; any selected digest leads to the FTS opening, whose sibling computations spend 14*sum_(j=0)^9(2^(j+1)-1)=28504 hashes even if a later encoding fails. Each invocation therefore costs at least L. No pathwise comparison between L*f_h and that invocation's realized message-call count is needed. These two different payments establish

    sum_h a_h <= q,             E[sum_h a_h] <= E[A_msg].

The following potential packages the entire payment into one conditional step. It is the main simplification from this review. Put c=3/2, Z=(R_full-c)_+, and Phi_h=E[Z | F_h]. Let D_h=sum_(j<h) a_j be accumulated predictable creation mass and let A_h be accumulated actual message calls. The path budget gives 0<=D_h<=q and 0<=A_h<=q. Define

    V_h = M_h + c*(q-A_h)/N + (q-D_h)*Phi_h/N.

Every term is nonnegative. At a live boundary, W_full,h<=c+Phi_h. Moreover D_(h+1)=D_h+a_h with a_h already determined by F_h, E[A_(h+1)-A_h | F_h]>=a_h, and E[Phi_(h+1) | F_h]=Phi_h. Consequently

    E[V_(h+1) | F_h]
      <= M_h + a_h*(c+Phi_h)/N
         + c*(q-A_h-a_h)/N + (q-D_h-a_h)*Phi_h/N
       = V_h.

Banking completions and discarding pending forecasts at a stop can only decrease M. After stopping, set future a_h to zero and freeze the monitored A_h and D_h; completion of the terminal word still has the same kernel identity. Thus the same inequality holds through stopping. Collapse zero-hash computation between charged boundaries into its conditional kernel and pad after termination; at most q charged boundaries remain. Finite expectation telescoping needs no assertion of independence at an adversarial stopping time.

Initially M_0=A_0=D_0=0. At termination M_T>=C_full and the last term of V_T is nonnegative, so

    E[C_full] + c*(q-E[A_msg])/N
      <= E[V_T] <= E[V_0] = c*q/N + (q/N)*E[Z].

Cancel the finite c*q/N term to obtain

    E[C_full] <= (3/(2N))*E[A_msg] + delta*x.

All quantities in the cancellation are integrable: the resource counters are bounded by q, and the finite-degree Poisson moments bound the terminal payoffs. Pending forecasts are uniformly bounded by a finite function of q and S, since there are at most q cached message targets and all matching multiplicities are bounded by q and S. For near certificates, let M_h be the sum of the 14 ledgers, one for each omitted coordinate, and use Phi_h=E[R_near | F_h] and V_h=M_h+(q-D_h)*Phi_h/N. The aggregated price W_near already includes this factor of 14; D_h remains the single shared creation mass. The same step, with no message-credit term, gives E[C_near]<=x*E[R_near]<557x.

This argument does not assume that creation mass and terminal occupancy are independent. Such a replacement would be false even in a toy process: if R is 2 with probability 1/4 and otherwise zero, and an informed process charges a=q only when R=2, then E[aR]=q/2 whereas E[a]E[R]=q/8. The conditional kernel identity and the remaining-mass term in V are exactly what handles that correlation.

The one-potential argument is an abstract theorem under the displayed kernel contract and local forecast bounds. The expanded coverage note derives those local bounds and checks the original signer's message transitions, failure cases, and costs. It also explains why the same coverage argument applies to deferred-secret kernels once their exact graph simulation and original path budget are established. Its premises must be discharged in the corresponding Lean kernels, rather than added as assumptions to the final security claim.

The total proposed exceptional allowance remains

    epsilon(q)=q/2^222 + q/2^237 + 2^-700.

The game rejects a log with more than S signing requests. Terminating with loss before request S+1 therefore discards no winning run; this termination requires no exceptional allowance. Proposal overflow and cache exceptions retain all calls of the invocation that encountered them.

There are two useful consistency checks on these stops. Since every actual invocation costs at least L, requesting one with fewer than L actual hashes remaining is impossible on a path admitted by the original budget; the monitor's corresponding gate cannot silently discard a winning path. Also, on a clean boundary the terminal proposal pool dominates forecasts before the next macro, even if that macro overruns the pool and triggers a stop. Its first completions are paid by the pre-macro conditional inequality. No post-overrun domination or resampling of that completed macro is needed.

The concrete coverage audit must check the following cases against the same V, not give each case a new budget or a different terminal word.

| Transition or boundary | Required accounting |
| --- | --- |
| Fresh external message cell | Its answer is uniform before exposure; a_h=1, and the call is included in A_h. Its first certificate, if already covered, is banked immediately. |
| Cached external message cell | No new target is charged; the actual repeat still counts as a message call. |
| Fresh digest selection | Use the conditional multiplier L*f_h before the macro. Include all attempts, append the retained selected index, and exclude this input's own view when forecasting its new target. |
| Cached digest selection | Create no new target on that outcome. The selected cached index still terminates the proposal block, and a successful response may complete old targets. The multiplier remains a conditional pre-macro quantity, not a flag chosen after seeing this outcome. |
| Digest exhaustion | Retain every actual attempt and the failed response. Add only the independent analytical dummy index, with no successful signing view. |
| Encoding failure after selection | Keep the selected index, all actual costs, and the failed response. Do not add a successful signing view or replace the index with a fresh sample. |
| Cache, deficit, or proposal stop during a macro | Complete its actual record and bank first completions before dropping pending forecasts. Domination is needed at the clean pre-state only. |
| Request S+1 | The original final log is invalid on every continuation. Monitoring may stop without charging this as a probabilistic exception. |
| Verification | Its actual hash calls use the same message cache and costs. A newly queried forgery digest can itself complete a certificate. |

Use two branch-specific coverage stopping times. The base stop is termination, the signing cap, or a cache, deficit, or proposal exception. Large-budget coverage additionally stops at the first primitive match B. Its primitive analysis runs the original game up to B or termination, without the other stops, and therefore pays at least the coverage message count. The forced-first-guess argument uses the base stop, since stopping at the first guessed secret would remove the later signatures whose near certificate it needs. Counts from different budget branches are not combined.

## 3. Sharpen the primitive probability calculation

Let B be the first primitive equality match in the exposed-graph experiment, and A_B its message count up to B or original termination. Before B, a primitive probe round tests at most one candidate against each of two distinct hidden coordinates. An OTS prefix query tests its input against the hidden canonical child, then, on a miss, its fresh answer against the canonical parent. An FTS secret query has an input test and an output test. A public structural target or unrestricted nonreference encoding has at most one output test. A message hash has none.

The following local induction makes the posterior claim precise. For each still-hidden canonical coordinate v, let U_v be its possible 128-bit values. Initially all U_v have size N. Conditional on G and survival, require the hidden values to have the product law of uniforms on their respective U_v. Keep an external row table separately from the private canonical reads performed by honest algorithms.

| Surviving transition | Posterior update |
| --- | --- |
| Candidate input z misses a hidden child u | Delete z from U_u. Conditional on this miss, all other hidden coordinates keep their previous laws. |
| A fresh noncanonical answer y misses a hidden parent v | Delete y from U_v. The answer was sampled independently of the hidden coordinates after the input miss. |
| A fresh answer misses a public parent | Restrict the answer to a set fixed by public information; no hidden-coordinate law changes. |
| External cache repeat | Return the recorded row. Its input miss and any parent exclusion were already recorded, so there is no new test. |
| Honest canonical evaluation | Read the programmed graph privately and count the call. Its input is not added to the external table. |
| Successful FTS disclosure | Choose the coordinate from the digest and exposed failure data, sample its value from its current U_v, reveal it, and retire it. The choice does not inspect that hidden value. |

For example, after an input miss, a fresh off-canonical row is independent of both the hidden child and hidden parent. Conditional on its observed answer y and the parent miss, the only new constraint on the parent is X_v != y. These two constraints concern distinct coordinates, so their conditional law still factors. The coordinates may take equal numerical values; the argument uses independent sampling at distinct graph coordinates. This proves the local product update, including the case where the candidate and observed answer happen to be the same value.

Explicitly, for a candidate z at hidden child u, an answer y, and a distinct hidden parent v, the surviving joint mass is proportional to

    product_w [1_(x_w in U_w)/|U_w|] * 1_(x_u != z) * (1/N) * 1_(x_v != y).

The two indicators restrict different factors. Normalization therefore gives independent uniforms on U_u without z and U_v without y, leaving every other factor unchanged. When the parent is public, the last indicator restricts only y. Independent high output bits add an unchanged factor. This is the precise local argument to instantiate for the serialized graph; a global claim that hidden values stay uniform is not a substitute for it.

For actual signing, the cost and failure mask must satisfy this induction too. The digest path depends on message cells and randomizers. Every OTS counter search is determined by its exposed canonical message and reference counter; the tree and FTS recomputations have fixed shapes once the selected index is known. Successful responses add only exposed canonical data and the selected FTS secret coordinates. Therefore the intended conditional kernel has no extra secret-dependent branch to charge. The expanded canonical-graph note carries these facts through the finite valid graph, byte-level domain classification, and original query schedule. Distinct nodes have distinct prefixes; repeated honest reads remain the same row. This discharges the paper posterior induction for the primitive process without auxiliary coverage stops.

The useful refinement is that only previous probe rounds can exclude candidates from a still-hidden coordinate. Message calls and honest internal graph evaluations consume the original budget but add no exclusions. After r probe rounds, each active coordinate has at most r excluded values. Under the product-of-uniform-posteriors invariant, the next probe round therefore has hazard at most

    h_r=1-((N-r-1)/(N-r))^2.

This is a conditional statement and permits the second coordinate to be chosen after the first miss. Distinctness of the two coordinates is essential. Adaptively selected disclosures retire coordinates; they may not inspect their hidden values to decide which coordinate to disclose. Fresh-answer tests against public values fit the same hazard bound. The concrete invariant must justify this classification; merely renaming the old total-time counter would not prove it.

Give each message round reward c=3/(2N). For an upper bound, give this same reward to every other non-probe round, including honest internal calls. Then the real quantity Pr[B]+c E[A_B] is bounded by a scalar problem with q rounds, two actions, and state equal to the number of probes already taken. Its recurrence is

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

    Pr[B]+(3/(2N)) E[A_B] <= 2x-(3/4)x^2.

This replaces the old total-time scalar bound 2x-x^2/8 by a simpler calculation. An exact rational dynamic-program check agrees with the finite schedule formula for N=2,...,80 and every q<=N/2. The displayed argument is the general proof; the finite check does not establish the concrete hidden-label invariant.

It is useful to retain the exact scalar expression as well:

    U(x)=2x-x^2+(max(x-1/4,0))^2.

This separates the elementary optimization from the cryptographic interface. The canonical-graph note derives Pr[B]+(3/(2N))E[A_B]<=U(x) for the original graph execution stopped only at B or termination. The coarser quadratic is then just a convenience for the final split, with no further probabilistic loss.

## 4. Close the large-budget range first

Attach the certificate experiment from step 2 to the same graph execution, additionally stopping its monitor at B. It preserves the original graph marginal. Its count A_cov is at most A_B pathwise: its other guards may stop earlier, and B cannot occur inside an honest signing invocation. A forgery with no B and no exception has a banked full certificate. Thus the charge (3/(2N))E[A_cov] is paid by step 3 without exposing auxiliary stops to the primitive history, and

    Pr[forge] <= 2x-(3/4)x^2 + delta*x + epsilon(q).

Take the new split x_0=2^-15, equivalently q_0=2^113. At x>=x_0,

    (3/4)x-delta >= 2^-17.

For q>=1,

    epsilon(q)/x <= 2^-94+2^-109+2^-572 < 2^-17.

Thus this range closes on paper. The complete derivation is in paid-probe-quadratic.md and cached-target-forecast.md. A corresponding Lean theorem for the original game at q>=2^113 remains to be formalized; it would still not establish 127-bit security for all budgets. This branch does not require the more elaborate useful OTS inversion argument.

## 5. Transfer the small-budget witness bound

For x<=x_0, first primitive matches are too generous an event: guessing one hidden value need not provide a usable forgery. The complete original-experiment derivation is now in small-budget-transfer.md. It uses the same base-stopped law and disjoint charges throughout, with the following completed-witness estimates.

For OTS, let Q be the actual number of distinct external prefix queries and A_enc the number of fresh nonreference encoding queries. A distinct target-sum codeword either has a backward distance of at least two in one chain, has backward steps in two chains, or is a unit neighbor. There are at most 42*41 unit neighbors and at most 41 lowering a specified chain. The conditional reference table is needed to charge their preparation, including queries before signing. The chain likelihood argument must retain the allocations Q and A_enc in the original execution:

    Pr[OTS witness] <= c_Q(x) E[Q]/N + c_enc(x) E[A_enc]/N,
    c_Q(x)=((3/2)+4x+2x^2)/(1-x)+4x/(1-x)^2+82x/(1-x),
    c_enc(x)=1+3444x/(1-x).

At x<=2^-15 both coefficients are below 131/80. Cheap noncanonical structural output matches have coefficient one; the ordinary full-coverage message charge has coefficient 3/2. These allocations are disjoint. Their combined contribution is bounded by (131/80)x, rather than granting a separate q budget to each class. The transfer note now gives the endpoint-dependent simulator, private-cost debit, universal cap for idealized paths, and stopped likelihood conversion that preserve these allocations. Those are substantive parts of the paper argument to audit and later formalize.

The reason a leading OTS coefficient below two is plausible is an explicit likelihood calculation, not independence of inversion attempts. For an h-edge chain with published endpoint Y, idealize only Y as an independent uniform value. The real density is W=#{starting values whose chain ends at Y}. At a partial table its conditional mean is w=1^T P_0...P_(h-1)e_Y, where each P_j contains known rows and uniform unqueried rows. Expanding by the last unqueried edge gives w<=1+sum_r C_r, with C_r counting fully queried suffixes. Stop at the first completed two-edge suffix. A productive last-edge query with predecessor multiplicities m_r contributes at most (2+k+sum_r m_r)/N. Each earlier queried input contributes to these multiplicities at most once, so the baseline is at most 3Q/2. Reverse-order searches and extra preimages supply the stated higher-order terms. Finally w_i>=1-Q_i/N>=1-x converts each ideal allocated cost back to its real allocated cost before summing over chains. The transfer note carries this calculation through the original graph simulation. Granting each chain its own q would destroy the argument.

For FTS, charge alternative preimages as cheap output matches, including those found before a later secret disclosure. A true guess of an undisclosed secret has conditional probability at most 1/(N-q). Two distinct true guesses cost at most x^2/(2(1-x)^2). A forgery using exactly one undisclosed secret also needs a near certificate.

First erase rejected proposal values. Force the first true guess at slot j with the explicit deferred-secret kernels in fts-guess-kernel.md. In this projected history, the likelihood of the real first-guess branch relative to this forced experiment is

    p_j product_(t<j)(1-p_t) <= 1/(N-q).

The transfer note proves that the modified kernels preserve unqueried message cells, the same pathwise q bound, and the coverage stopping rules: every forced branch has positive original conditional probability, and deferred secrets can be completed consistently with every observed row. The independent J and geometric lengths keep the same kernels in the likelihood comparison. Now add rejected values separately to each forced law and apply the abstract near-certificate theorem there. There is no need for those rejected-value kernels to agree across laws, and their densities are not canceled. Summing j gives 557x^2/(1-x). This avoids assuming independence or a particular chronological order between guessing and target preparation. The certificate theorem already counts banked certificates on killed runs, so an exceptional probability is not added once per forced slot; epsilon(q) is charged once in the original experiment.

At x<=2^-15, the existing looser constants already give

    557x/(1-x)+x/(2(1-x)^2) < 9/80.

Therefore

    Pr[forge] <= (131/80+9/80)x + delta*x + epsilon(q)
              = (7/4)x + delta*x + epsilon(q) < 2x.

No further constant optimization is needed in this branch.

## 6. Decision criteria before more Lean infrastructure

The paper work should deliver three original-experiment statements: the stopped full/near certificate bounds; the joint primitive/message-charge bound whose message count dominates the monitored one on the same original run; and the small-budget completed-witness decomposition with disjoint cost allocations. Coverage and primitive analysis use their respective histories. These statements imply the public claim by the elementary split above.

| Paper milestone | Required endpoint | Acceptance condition |
| --- | --- | --- |
| Exact experiment and forgery decomposition | Original marginal, actual costs, and the exhaustive alternatives in section 1 | Handle canonical encoding exhaustion, later signing failure, previously queried cells, malformed inputs, and a different signature at a previously signed input. |
| Adaptive coverage | E[C_full]<=(3/(2N))E[A_msg]+delta*x and E[C_near]<=557*x | Derive the inequalities for the specified kernels, including deferred-secret kernels, using one terminal variable and banking at every stop. |
| Large budgets | Pr[forge]<=2x for 2^113<=q<2^127 | Use the written hidden-label induction and the pathwise A_cov<=A_B comparison on the same original run. This paper derivation is now present; its Lean translation remains. |
| Small budgets | Pr[forge]<=(7/4)x+delta*x+epsilon(q) for q<=2^113 | Audit the written transfer of allocated OTS costs and the projected first-guess likelihood, including each forced law's coverage application; then formalize them. |
| Public claim | Pr[forge]<=q/2^127 for every admitted q | Combine the two ranges with probability at most one for q>=2^127, without changing the scheme or its budget. |

The paper now contains the large-budget graph and posterior argument, the exhaustive SUF decompositions, the differently stopped count comparison, and the small-budget adaptive transfers. The next audit should target the small transfer's endpoint-dependent auxiliary kernel, cap on idealized paths, separately integrated encoding history, and positive-support argument for forced FTS laws. For formalization, use the single coverage potential V and the concrete kernel derivation, including a fresh bridge for every forced-secret law. Each implementation milestone should discharge a security endpoint for the original game.

The end-to-end acceptance test is an inequality whose left side is the original forgeAdvantage, whose right side is a numerical function of the original q, and whose only adversary assumption is the original whole-experiment bound. An endpoint that assumes its own certificate bound, a global posterior invariant, a favorable future occupancy event, or a newly restricted signing oracle has not completed the corresponding row. Intermediate lemmas may have such explicit premises, but the paper must discharge them before claiming the row is established.

This audit checked the existing exact rational cache, deficit, proposal, Poisson and closing certificates, and the finite planted-table and rejection-bridge checks. They passed. The new split and scalar expression were checked separately with rational arithmetic. These are arithmetic and finite-kernel checks, not a verification of the adaptive cryptographic transfers. The transfer-kernel-checks.py script also checks exact stopped transcript densities in a finite endpoint-dependent simulator and the adaptive forced-first-guess identity through disclosures and early termination. These finite identities support the written transfer; they do not certify it for the complete cryptographic experiment.

The arithmetic does not call for another optimization pass: at x=2^-15 the large-budget margin after delta is exactly 2^-17 per x, which exceeds the exceptional allowance. The small-budget coefficients leave a fixed gap below two. The complete paper derivation is now written, with the adaptive witness transfers identified as the main mathematical audit target. The audit made the OTS projection explicit and checked that its charged statistics factor through it: the preimage-count density is false on a record retaining the starting secret. Lean now connects the exact adaptive terminal-word kernel, actual support invariants, and accumulated forecast charges to an original-game inequality: expected banked certificates are at most c times expected actual monitored message calls plus q times the independent terminal-price excess above c. The next coverage obligation is the numerical Poisson estimate. The exception bounds, coverage extension to deferred-secret kernels, and both security transfers remain to be completed; finite examples do not replace those proofs.

For context, the corrected [SPHINCS+ proof](https://eprint.iacr.org/2022/346) and its [EasyCrypt formalization](https://eprint.iacr.org/2024/910) both emphasize the WOTS and game-transition arguments. They are useful audit references, but their theorems do not establish the constants or strong-unforgeability claim for this custom target-sum instance.
