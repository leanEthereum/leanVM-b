# Coverage with a fixed proposal word and deferred secrets

This note proves a paper coverage theorem from explicit rules for sampling message cells and completing signing invocations. The rules permit changes to non-message responses and deferred secrets, including the experiments needed in the 127-bit plan. It derives the local forecast inequalities, constructs one fixed terminal proposal word, and pays all adaptive charges in that execution. Target-input exclusion, failed responses, and actual hash costs are retained. The exact projections from the concrete graph and forced-secret experiments remain separate obligations; this is not a new Lean theorem. The fixed-word construction and unit payment here supersede this note's earlier Poisson calculation.

## Constants and results

Set N=2^128, I=2^26, L=1024, S=2^24, and a=1/(LI)=2^-36. Assume at most q<=N/2 total hash calls. Let x=q/N, beta=1537/1024, D=S/128=131072 and M=beta*S+D+13=25313293. Message-domain inputs in this note have the fixed key parameter and message tweak; their payloads need not be well-formed signing inputs. For the cache, C_i(t) counts distinct admissible such inputs at index i after t actual hash calls. Let s_i count successful signing views at i; s counts monitored signing invocations, including failures.

The original game logs every signing request and rejects a final log longer than S. Stop its coverage monitor immediately before request S+1 while letting the original computation and log continue. Such an execution necessarily loses in the original game, so this stop cannot discard an original win and gives s<=S in the monitor. Discard pending target forecasts at this stop and retain certificates already counted; no exceptional-event allowance is needed for the cap.

Check the exceptional conditions defined below at completed boundaries: after each external hash and after each complete signing invocation. Boundary checks suffice for the proof. For the OTS projection use the boundary state directly, without retaining private intermediate cache events. An invocation's message trace may be kept, but private non-message query inputs are unnecessary. In every case, complete the original invocation before stopping. Additional stopping based on current information is permitted. Previously completed target certificates are retained when the process stops.

Let A_msg count actual message-domain hash calls in that stopped execution. A full target certificate is an admissible cached digest whose 14 coordinates are covered by successful signing views at other inputs. A near-target certificate is a pair consisting of such a digest and one of its 14 coordinates, with the other 13 coordinates covered at other inputs. Repeated certification of the same pair is counted once. Then

    E[number of full certificates] <= E[A_msg]/N + (11/65536)*x,
    E[number of near-target certificates] <= 557x.

The probability that the original execution encounters an exceptional condition is at most

    epsilon(q) = q/2^222 + q/2^170 + 2^-700.

The coverage estimates depend only on the precise kernel below. Their proof does not assume favorable final occupancy, independent charging times, or a coverage probability. The same kernel also bounds the stated numerical exceptions, but the final security argument needs that allowance only in the original experiment. It is not added to the certificate estimates: those already count certificates on stopped runs. In particular, it must not be added once per forced-guess experiment.

## Execution kernel and information available at boundaries

The parameter and public root are fixed at initialization, possibly by random key generation using only non-message domains. The initial message cache and signing log are empty; the original key-generation hash cost t_0 is retained. Conditioned on the current analytical state, every fresh message-domain hash call gets a uniform 256-bit answer, and repeats return their cached answer. Every message-cache insertion must arise from an actual counted hash call. The current state may contain private environmental data, but cannot contain unqueried message cells or unused proposal letters. Non-message transitions may depend on the observed message cache and change later requests, but do not inspect unqueried message cells.

A signing invocation has exactly the original finite digest loop. Each executed attempt samples an independent uniform randomizer from N possibilities and makes the corresponding message call. It stops at its first admissible answer or after 2^32 attempts. A post-selection kernel may perform non-message computation and return either failure or one successful signing view at exactly that selected input, index, and leaf vector. It cannot read or create further message cells during the invocation. A failure contributes no successful view. A selected digest is retained analytically even when the post-selection kernel fails. All successful views retain their input identity, so a target can exclude its own input.

Other transitions can choose future queries and requests using the recorded history and private state. They cannot insert unqueried message cells, change existing message answers, or invent successful signing views. All original hashes, including repeated and internal calls, count toward the same pathwise budget q. Each completed signing invocation costs at least L hashes. Monitoring stops before invocation S+1 and at the stated boundary conditions; all costs and first certificate completions of an active invocation are recorded before a post-state stop takes effect.

These conditions leave the post-selection failure rule unrestricted. It may depend on the selected digest and private non-message information. The proof below bounds its possible successful view by the selected view before applying that failure rule; it never assumes that successful responses themselves have a uniform index distribution.

## Local target moments, derived from this kernel

Fix a target input z and its admissible view (i_z,v_z). For a nonempty coordinate block B, define C_B(z) as L^|B| times the number of admissible cached inputs other than z with index i_z and leaves equal to v_z on B. Define S_j(z) as L times the number of successful signing slots at inputs other than z with index i_z and the matching j-th leaf. Slots are counted with multiplicity, allowing repeated signing requests. For a family G of nonempty, pairwise disjoint coordinate blocks and a remaining coordinate set R disjoint from every block, put

    f_z(G,R) = product_(B in G) C_B(z) * product_(j in R) S_j(z).

This is exactly the normalized shape moment used by the existing source modules. All its factors depend only on the message cache and successful signing views. In particular, no secret value, failure mask, or private non-message cache entry occurs in f_z.

Define three linear operators on shape vectors:

    (C f)(G,R) = sum_(H proper subset of G) f(H,R),
    (D f)(G,R) = sum_(empty != B subset of R) f(G,R\B),
    (U f)(G,R) = sum_(empty != B subset of R) f(G union {B},R\B).

Write Q=Id+a*C and S_op=Id+(C+D+C*D)/I+rho*U, where rho is the finite-loop reuse bound proved below. Operator products mean composition. Every term has a nonnegative coefficient and a valid shape.

For an external fresh message input other than z, expand the product of old cache factors plus their increments. A nonempty set of incremented blocks imposes one index condition and disjoint leaf conditions on one uniform answer, together with admissibility. The powers of L cancel the leaf probabilities, leaving exactly 1/(LI)=a. Thus the conditional expected new f_z equals Q f_z. A repeat, a non-message query, or an excluded query at z changes none of these factors and is bounded by the same Q f_z. Successful old views remain fixed because their message cells are already cached consistently.

For a signing invocation, let F be its conditional probability of fresh selection. On that event the selected view, before any later failure, is uniform on I times L^14. There is exactly one new admissible cache entry. Allowing that view to contribute even if the signer subsequently fails gives a pointwise upper bound on all the nonnegative moments. Expanding the simultaneous cache and signing increments gives the terms C, D, and C*D. Each nonconstant term has conditional uniform expectation 1/I because its constrained coordinate sets are disjoint. Multiplying by F<=1 bounds this part by (C+D+C*D)f_z/I.

On selection of an initially cached admissible input y, no admissible cache entry is added. If y=z, its signing view is excluded and gives no increment. Otherwise, expanding the new signing factors for a nonempty subset B of R and summing over possible y converts their matching contribution into C_B(z). Each such y has selection probability at most rho. Allowing all messages' cached entries rather than only the requested message's entries enlarges this contribution to rho*U f_z. Exhaustion adds neither an admissible entry nor a successful view. Hence the complete macro kernel satisfies

    E[f_z after an external hash | history] <= Q f_z,
    E[f_z after a signing macro | history] <= S_op f_z.

This derivation includes encoding failures, cached selection, and adaptive failure masks. No conditional success-uniformity claim or cryptographic assumption about the non-message kernel was used.

Expanding the finite sums gives D*C=C*D and U*C=C*U+D+C*D. Consequently

    S_op*Q = Q*S_op + a*rho*(D+C*D) >= Q*S_op.

For a required set E of size d, define the forecast at actual remaining budgets b=q-t and r=S-s by

    phi_z(b,r) = L^-d * (S_op^r Q^b f_z)(empty,E).

The identity term of both operators ensures phi_z>=1 whenever E is already covered. Positivity and the displayed commutation prove the local continuation bounds. An external hash debits b by one; its Q transition is absorbed into Q^b. For a signing macro with actual hash cost k, first enlarge b-k to b, then use Q^b*S_op<=S_op*Q^b and debit r by one. This proves E[phi_z after | history]<=phi_z before for every previously cached target. It uses the actual remaining budget once, including failed invocations, and does not give each target a new budget.

## Fresh-target creation and its exact cost

If an input z is fresh, no prior successful slot has that input: its digest would already be cached. Average f_z over an independent uniform target view. After fixing the target index i, all constrained coordinate blocks are disjoint, so expanding the source choices and averaging the target leaves gives

    E_target[f_z(G,R)] = I^-1 * sum_i C_i^|G| s_i^|R|.

The cached and signed source values themselves can be arbitrary and correlated. Only the fresh target's coordinates are averaged. Linearity of the finite shape operators extends this identity to the forecast. Writing their action on the monomials as a two-variable polynomial gives the fresh-query price W_d/N, where

    W_d = N/(I L^(d+1)) * sum_i E_B[f_r(C_i+B,s_i)],
    B ~ Binomial(b,a),
    f_r(c,u) = T^r(u^d),
    (T f)(c,u) = f(c,u)
        + (1/I)[f(c+1,u+1)-f(c,u)]
        + rho*c[f(c,u+1)-f(c,u)].

This is an algebraic polynomial identity for the raw-index envelope. One must not treat T as a stochastic kernel at arbitrarily large c: its formal reuse rate could then exceed one. A bounded stochastic interpretation is justified only after the polynomial comparison below.

An external fresh message query produces an admissible target with probability 1/L, so its creation-price multiplier is one. For signing, condition on fresh selection. When forecasting its new target, exclude the newly inserted cache entry and the possible new signing view at that same input. All other admissible entries and all older signing views are unchanged by the macro; its rejected fresh cells are inadmissible. The fresh target's own forecast can therefore be averaged against the pre-macro counts, with its smaller post-macro budgets enlarged to the pre-macro budgets. This gives expected creation charge F/(I L^d) times the raw envelope, exactly LF*W_d/N. This calculation uses the selected view before the possibly biased post-selection failure rule.

The conditional expected number of fresh message queries during that digest loop is exactly LF. Each fresh cell is admissible with probability 1/L, and at most one fresh admissible cell appears before the loop stops. This finite stopping-time identity remains valid with cached selections and retry exhaustion. Hence the sum of these predictable creation multipliers has expectation at most E[A_msg]. Pathwise it is at most q: external multipliers are at most their hash costs, and each signing multiplier is at most 1024. Every completed signing invocation either exhausts all 2^32 digest attempts or computes the FTS opening, whose sibling computations use 14*sum_(h=0)^9(2^(h+1)-1)=28504 hashes. Both cases cost at least 1024 actual calls. These costs are disjoint from external calls.

For full coverage use d=14, so W_14 is the raw forecast divided by 2^48. For near-targets sum over the 14 choices of the omitted coordinate, giving W_near=14 times W_13, with scale 14/2^38 on sum_i s_i^13.

## Recording completed certificates

Maintain the sum of the forecasts of pending targets plus a counter of completed certificates. At a first completion, increase the counter by one and remove that target's pending forecast, which is at least one. This cannot increase the total. Removing a pending target does not remove its input from the real oracle cache, so other targets' forecasts retain every legitimate reuse contribution.

Let M_h be that bank plus the pending forecasts. Sum the derived old-target inequalities and fresh-target charge over the actual finite cache. Banking replaces a completed forecast of at least one by one. A post-state stop then discards only the remaining nonnegative forecasts. For the predictable pre-step multiplier a_h (one on a fresh external message call, LF on an active signing request, zero otherwise), the result is

    E[M_(h+1) | F_h] <= M_h + a_h W_d,h/N.

There is no assumption here about a global certificate bound: this inequality follows from the explicit Q and S_op calculations and the actual creation price. Initially the message cache is empty, so M_0=0 even though key generation has spent t_0 hashes. At most q boundaries incur a nonzero multiplier. Padding after termination and discarding terminal pending forecasts gives

    E[completed certificates] <= (1/N) E[sum_j a_j W_j],

where j ranges over the external-query and signing macro steps, a_j is the predictable multiplier just described, and W_j is the corresponding raw forecast before the step. This applies to d=14 and, after summing omitted coordinates, to d=13. It includes cached targets completed by later signatures.

## Cache controls and the reuse coefficient

First stop at a completed boundary if C_i(t)>at+2^80 for some i. This stop depends only on the message cache and actual spent calls, including all private honest calls. Define X_i(t)=C_i(t)-at and U(t)=sum_i max(X_i(t),0)^2. The elementary inequality

    max(z+y,0)^2 <= max(z,0)^2 + 2*max(z,0)*y + y^2

follows by splitting on the signs of z and z+y. At a fresh message cell, each X_i changes by B_i-a, where B_i is marginally Bernoulli(a). Its conditional mean is zero and its second moment is a(1-a), so E[U(t+1) | history]<=U(t)+Ia. No independence between the B_i is required. On every other hash call, all X_i decrease by a and U cannot increase. Free operations leave these statistics unchanged. Hence

    U(t) + (q-t)*Ia

is a nonnegative supermartingale through all actual hash slots. Initially the message cache is empty, so U(t_0)=0. If any index crosses its threshold then U>2^160. Stopping this potential at the first crossing gives

    P[cache exception] <= q*Ia/2^160 = q/2^170.

This bound does not inspect the number or contents of private non-message cache rows. It therefore supports a monitor that survives the OTS projection directly. Counting all distinct private rows first and then bounding them by spent calls is unnecessary for this version of the argument.

Second, for each proper message m at the fixed public root, let D_m be the number of cached randomizers minus L times their admissible count. Stop if D_m>2^93 at a completed boundary. Again the stronger event of crossing at any prefix bounds its probability. A fresh cell changes its one message score by X=1-L*Bernoulli(1/L). Then E[X]=0, E[X^2]<L, |E[X^3]|<L^2, and E[X^4]<L^3. The inequality 4L^2|D|<=2LD^2+2L^3 gives conditional fourth-moment growth at most 8LD^2+3L^3. At time t, E[sum_m D_m^2]<=Lt, so the expected squared score of the adaptively selected message is also at most Lt. Summing the fourth-moment increments yields

    E[sum_m D_m^4] <=4L^2 q(q-1)+3L^3 q.

The sum is a nonnegative submartingale. Its maximal inequality at 2^372 gives a probability below q/2^222 for q<=N/2. Only fresh message cells enter this proof. The existing Lean deficit estimate is slightly sharper, but that sharper constant is unnecessary here.

On a clean prefix, a digest loop starts with D_m<=2^93. Before it finishes, at most 2^32 new rejected cells can be added. At every attempt its conditional acceptance probability is at least

    (1/L)[1-(2^93+2^32)/N].

Indeed, if K randomizers are cached and A of them are admissible, the next attempt accepts with probability A/N+(1-K/N)/L=(1/L)(1-D_m/N). Before the first acceptance, each newly queried rejected cell increases D_m by exactly one, while a repeated rejection leaves it unchanged. Thus a clean pre-macro deficit and the actual finite attempt limit suffice even if a threshold is crossed inside the macro. The expected number of attempts divided by N, which bounds selection of any fixed cached admissible input, is at most

    rho=(1025/1024)*2^-118=1025/N.

For completeness, a fixed initially cached admissible randomizer is selected with probability exactly E[T_m]/N, where T_m is the actual number of attempts. At every executed attempt its next independent randomizer equals that fixed value with probability 1/N, and this event ends the loop. Summing these disjoint stopping events over the finite attempt range proves the equality. This justifies the per-input bound rho used in the local U operator, without assuming independent cached selections.

After assigning an independent dummy index on digest exhaustion, the completed selected-index probabilities are therefore p_i=(F+E)/I+c_(m,i)*E[T_m]/N<=1/I+rho*C_i, where E is exhaustion probability and c_(m,i) counts initially cached admissible inputs for the requested message and index. Fresh selection and exhaustion together have mass at most one and each gives a uniform index. A failed later encoding may suppress a signing view, which only decreases s_i. The finite digest-loop induction also shows that this distribution depends only on the current message cache, parameter/root, and request, not on hidden secret values or the later failure rule.

## Bounding the raw forecast by capped binomial moments

The polynomial f_r has nonnegative coefficients and total degree at most d. This follows directly from T: its diagonal increment lowers total degree, while c times a signing increment does not increase it.

For B~Binomial(b,a), mu=ba, and k<=d,

    E[(c+B)^k] <= (c+mu+d)^k.

Expand binomial moments in falling factorials; E[(B)_j]<=(ba)^j and the partition count is at most choose(k,j) k^(k-j). Thus E[B^k]<=(mu+k)^k, and expanding the shift by c proves the displayed bound. Coefficient positivity now gives E_B[f_r(c+B,u)]<=f_r(c+ba+d,u).

On a clean prefix c<=at+2^80, so c+ba+d+r<=aq+2^80+S+14. Throughout the remaining r signing transitions, interpret T at this bounded starting point as the Markov chain with a diagonal increment of probability 1/I and a signing-only increment of probability rho*c. All its probabilities are valid in this range. Its signing increments are dominated by Bernoulli(v_q), where

    v_q=1/I+rho*(aq+2^80+S+14).

Set beta=1537/1024. Exact rational arithmetic gives I*v_q<=beta for q<=N/2, with beta/I<1. These bounds also give p_i<=v_q<=beta/I on every active pre-state, discharging the cap required by the proposal bridge below. The bounded signing process is dominated by r independent Bernoulli(v_q) increments. It follows that

    W_14 <= (1/2^48) sum_i E[(s_i+Binomial(r,v_q))^14],
    W_near <= (14/2^38) sum_i E[(s_i+Binomial(r,v_q))^13].

No tail event for hypothetical future cache counts is needed: the polynomial moment comparison occurs before the bounded Markov interpretation.

## One discrete terminal word for every adaptive charging time

The exact finite-word construction is in discrete-target-coupling.md. At the next signing invocation, repeatedly propose a uniform index i and accept with probability I*p_i/beta, where p is the actual selected-index distribution. Equivalently, run the actual invocation first, independently sample a geometric proposal-block length of mean beta and its rejected indices, then append the invocation's selected index. The two joint kernels agree exactly. A signing record contains message queries, the returned Option signature, and actual hash cost; it does not disclose hidden internal non-message query inputs.

Here is the exact law and its boundary induction. For a current original record law K, with selected-index probabilities p_i<=beta/I, put r_i=(beta/I-p_i)/(beta-1). These are nonnegative and sum to one. Run the record first, sample a geometric G with P[G=g]=beta^-1*(1-beta^-1)^(g-1), independently sample G-1 letters with law r, and append the record's selected index. For a rejected word u and a compatible record omega, the joint mass is

    K(omega)/beta * product_(a=1)^|u| (1/I-p_(u_a)/beta).

In the proposal-first construction each next letter is uniform, letter i is accepted with probability I*p_i/beta, and at acceptance its record is sampled with conditional law K(omega)/p_i. Multiplying these factors gives exactly the same displayed mass; a zero p_i has no record of positive mass and never requires division. Summing over rejected words recovers K and an independent geometric length. Hence the bridge preserves the entire original record, including its response, selected digest, all actual costs, and any retained private post-state.

For a consumed word u, define the completion kernel K_M(u) by truncating u to M letters when |u|>=M, or padding it to M letters with independent uniforms otherwise. For the next bridge block b,

    E[K_M(u ++ b) | pre-macro state] = K_M(u).

Prove this identity by induction on the number of still-needed letters. When none are needed the kernel is a fixed point mass. Otherwise the next proposal is uniform; after rejection use the induction hypothesis for the same record kernel, and after acceptance the conditional record probabilities sum to one and the remaining padding is uniform. Every recursive call needs one fewer letter, even if the full rejection block is longer than M. This avoids an infinite-series approximation. The argument also applies after acceptance to any adaptively chosen next computation. External queries and inactive monitoring append no letters. Composition therefore proves, for every completed boundary, that the conditional eventual terminal-word law is exactly K_M(u_h). The original record must not be revealed before claiming uniformity of its accepted proposal; the proof uses the equal proposal-first kernel.

No infinite stream or independence of the whole word from the game is required. Run the actual experiment with monitoring and at most S geometric blocks, then use K_M to finish the word. This construction works even if a completed block overruns M. The tower identity gives a uniform word of length M. Its occupancy vector Z has the multinomial law

    P[Z=z] = M!/(product_i z_i!)*I^-M,       sum_i z_i=M.

The occupancies are not independent, and no independence claim about them is used.

Let K_s be the number of proposals consumed by s completed monitored invocations. The third exceptional condition is K_s>beta*s+D at a signing boundary. Each geometric block length has the same law independently of its completed record and preceding history. Unused lengths may be independently padded up to S. For t=129/128 and u=E[t^G]=132096/130559, the process t^K_s*u^(S-s) is a nonnegative martingale. Since u^2>=t^3, a crossing implies its square is at least t^(3*S+2*D). The maximal inequality bounds the crossing probability by u^S/t^(3*S/2+D). The exact rational certificates

    (u^2/t^3)^1024 <= 16/15,
    t^128 >= 27/10,
    (((16/15)^8)/(27/10))^16 <= 2^-11

give a bound of 2^-704. This fits inside the stated allowance. There is no random-pool or short-pool event. Finish an invocation before acting on its proposal exception, so all its message calls and newly banked certificates remain in the charged execution.

At a clean boundary, each successful signing slot injects into the final position of its own proposal block, with its retained selected index. Different slots have different positions, even if they signed the same input. Failed invocations add no slot. Therefore, if z_i counts consumed proposal letters, z_i>=s_i holds pathwise by induction. Also K_s is exactly the consumed word length, since both counters add the same G at every active invocation and otherwise remain fixed. The guards give m=M-K_s>=beta*(S-s)+13. By the completion-kernel identity, each future bin count has conditional law Binomial(m,1/I). For r=S-s and 0<=j<=d<=14,

    (r)_j v_q^j <= (beta*r/I)^j <= (m)_j/I^j.

These are falling-factorial moments. Their nonnegative expansions into shifted powers show that the future binomial count dominates the required degree-d forecast in moments. Thus, with

    R_14=(1/2^48) sum_i Z_i^14,
    R_near=(14/2^38) sum_i Z_i^13,

the enlarged boundary filtration F_j satisfies

    W_14,j <= E[R_14 | F_j],
    W_near,j <= E[R_near | F_j].

This is one terminal variable for all query times. No probability law has been conditioned on a future good event. The monitor stops on current exceptions and retains banked certificates. Unconditional multinomial moments therefore control the adaptive excess charges below.

If the next macro overruns M, finish its record, append its full block, and bank first completions before stopping. Its post-state need not satisfy z_i>=s_i for the truncated terminal word, and no such claim is used. The local banked-forecast inequality is paid from its clean pre-state. The completion-kernel identity remains valid after overrun because the first M letters have already been determined.

## Paying the adaptive charges

Let c=1, Z=(R_14-c)_+, and Phi_h=E[Z | F_h]. The completion-kernel identity makes Phi a martingale, and W_14,h<=E[R_14 | F_h]<=c+Phi_h on every active pre-state. Write D_h=sum_(j<h) a_j for accumulated predictable creation mass and A_h for accumulated actual monitored message calls. The proved payments give D_h<=q, A_h<=q, and E[A_(h+1)-A_h | F_h]>=a_h. Use the single nonnegative potential

    V_h=M_h+c*(q-A_h)/N+(q-D_h)*Phi_h/N.

Since D_(h+1)=D_h+a_h is already determined at the pre-state, the one-step calculation is

    E[V_(h+1) | F_h]
      <= M_h+a_h*(c+Phi_h)/N
         +c*(q-A_h-a_h)/N+(q-D_h-a_h)*Phi_h/N
       = V_h.

The local forecast inequality includes banking and arbitrary post-state stopping. After stopping, freeze A_h and D_h, set future a_h=0, and keep the bank; the same calculation continues to hold. Zero-hash computation can be incorporated in the kernels between charged boundaries. There are at most q boundaries consuming hashes, and padding with inert steps makes finite telescoping sufficient.

Initially M_0=A_0=D_0=0. At the final boundary M_T is at least the banked certificate count. Drop the remaining nonnegative Phi term and telescope to get

    E[C_full]+c*(q-E[A_msg])/N <= E[V_T] <= E[V_0]
      =c*q/N+(q/N)*E[Z].

Cancel c*q/N to obtain E[C_full]<=E[A_msg]/N+x*E[Z]. The cancellation is between finite quantities. Cache and slot multiplicities are bounded by q and S, and the terminal word has fixed length M, so all pending forecasts and terminal prices have finite uniform bounds. This argument explicitly permits D_T and R_14 to be correlated.

For near certificates, sum the 14 pending-and-banked ledgers, use Phi_h=E[R_near | F_h], and omit the c*(q-A_h)/N term. The summed price is W_near; the resource counter D_h is still the single shared creation mass. The same calculation gives E[C_near]<=x*E[R_near]. There is no additional factor of 14 in the resource payment.

For the multinomial occupancies of the uniform word, exact finite moment bounds give

    E[R_14] <= 1/5,
    Var(R_14) <= 13/25000,
    E[R_near] <= 557.

For distinct indices i and j and falling factorials of orders b,c, direct counting gives

    E[(Z_i)_b*(Z_j)_c] = (M)_(b+c)/I^(b+c)
        <= (M)_b*(M)_c/I^(b+c).

Expand ordinary powers using nonnegative Stirling coefficients. This proves Cov(Z_i^14,Z_j^14)<=0. For T_d(z)=sum_b StirlingSecond(d,b)*z^b and M/I<=19/50, it follows that

    E[R_14] <= 2^-22*T_14(19/50) <= 1/5,
    Var(R_14) <= 2^-70*T_28(19/50) <= 13/25000,
    E[R_near] <= (14/2^12)*T_13(19/50) <= 557.

These inequalities are represented in FixedProposalMoments.lean. With mu=E[R_14], the elementary positive-part inequality gives

    E[(R_14-1)_+] <= Var(R_14)/(4*(1-mu))
        <= 13/80000 < 11/65536.

The terminal law is the same uniform word under every allowed sequence of transition kernels, including changes to non-message replies. Its correlation with the adversary's chosen costs is handled by the potential, not by factoring their expectations.

Combining these estimates with the certificate counter proves the two stated coverage results. Adding the three original exceptional-event probabilities gives epsilon(q), without any multiplication by the number of cached targets.

## Instantiation and scope of the paper theorem

The original experiment in Statement.lean meets the kernel conditions directly. Key generation samples independent secrets and hashes only structural domains, so its message cache is empty and its actual hash cost is t_0. Its shared oracle gives precisely the fresh and cached message transitions used above. The only message calls inside signing are signDigestLoop's finite attempts. Everything following selection uses the distinct FTS, encoding, chain, or tree domains. The final Option response either fails or carries exactly the selected input and view. Successful views are therefore backed by already cached message cells and stay fixed under later cache extensions.

Every selected digest is followed by ftsOpen before an encoding failure can return none. Its sibling computations cost 28504 hashes; digest exhaustion costs 2^32. Thus the required per-invocation lower bound L is a property of every actual response path, including both failure cases. The original HasHashQueryBound supplies the single whole-path q bound, including key generation, all these actual invocation costs, and verification. Final verification consists of further original hash transitions, so a newly queried forgery digest is processed by the same ledger.

Attach the auxiliary proposal blocks after running each active original record and preserve the original interpreter even after monitoring stops. Forgetting the auxiliary data and the monitor therefore recovers the original response, cache, cost, and verdict laws. The verdict still reads the complete original signing log. An original run reaching request S+1 cannot win; hence stopping its monitor costs no exceptional allowance. The actual remaining-budget gate cannot stop an otherwise active admitted run: an external hash needs one remaining hash, and a signing invocation needs at least L; otherwise that supported continuation would exceed the original q bound. Cache cardinality is at most the number of actual hash calls, and successful digest cells remain cached, so those administrative checks do not create further exceptions.

The boundary guards now give all forecast premises on every active state: t<=q<=N/2; s<=S; the cache and deficit bounds; K_s equal to the consumed word length; s_i bounded by its index counts; and M-K_s>=beta*(S-s)+13. Every possible loss of a guard is either an explicitly bounded cache, deficit, or proposal event, or the losing signing-cap case. The current invocation is completed and banked before stopping. These observations discharge the monitor premises for this presentation of the original execution; an additional stop based on current information can only discard pending forecasts and later charges.

For a modified experiment, apply the theorem separately to that law. Its non-message transitions may alter future requests or post-selection outcomes; they may not inspect unqueried message cells, alter existing message answers, or add signing views outside an invocation. The coverage proof needs no secret key fixed in advance and no equality of rejected-word laws across different experiments. The fresh-message and budget conditions must hold in the actual current state of the modified law, not after conditioning on a final secret key.

The exact deferred graph, inherited original budget and first-guess likelihood in small-budget-transfer.md still require their concrete transfer proofs. The large-budget graph and posterior argument is described in paid-probe-quadratic.md. Its primitive process stops only at its first match or original termination, while its coverage monitor can stop earlier on the numerical guards above. Once the graph coupling is established, that ordering gives A_cov<=A_B. The abstract coverage result here does not itself prove either original-game security inequality.

## Why non-message changes preserve the message kernel

State the lazy-oracle invariant for every finite set F of as-yet-unqueried message inputs: conditional on the analytical history, their answers have the product uniform law. This avoids sampling an infinite table. The invariant holds initially because key generation and canonical graph advice use disjoint non-message domains. The fresh set F and the next query may be selected from the current history; they may not be chosen by inspecting those unqueried answers.

A non-message transition samples its next state from a kernel depending only on the current state. Conditional on that state, the transition supplies no information about the unqueried message answers. Multiplying and normalizing the joint mass therefore leaves their product law unchanged. At a message query, a repeat returns its fixed cached answer, while a fresh query selects one uniform coordinate, records it and leaves every other unqueried coordinate independent and uniform. Induction establishes the invariant through adaptive non-message transitions, message queries and the finite signing loop.

In the graph presentation, pre-sampling structural labels and conditional reference-encoding data changes only non-message domains. The primitive stop depends on those data and already observed requests and replies. In the deferred FTS presentation, a hit or miss kernel depends on the current candidate set, chosen candidate, public leaf hash and past rows. Forcing one of these conditional branches, when it has positive probability, does not inspect a future message cell. Secret disclosures have the same property. These operations therefore preserve the message invariant. Completing deferred canonical rows never changes a message row because their serialized tags are disjoint.

Completing a finite forced transcript remains a separate support argument: choose each remaining secret in its nonempty candidate set and program its unqueried canonical row. No observed row is changed. Once this is proved for the concrete graph interpreter, it supplies a supported original execution with the same actual costs, so the original whole-experiment bound transfers. The coverage theorem then applies to the forced law without another security assumption. An OTS experiment with an independently replaced endpoint need not have original support and instead requires the explicit q cap described in the small-budget plan; this coverage application does not use those unsupported OTS laws.

The record-first proposal bridge must be attached after choosing which law is being analyzed. Its rejected-letter distribution is computed from that law's current completed-record distribution. Even when the selected-index marginal is the same, no equality of full record distributions is needed. The proof uses the normalized record distribution and its pointwise index cap, then establishes the terminal completion identity inside that law. This order prevents an unjustified cancellation of proposal probabilities in the forced-guess likelihood comparison.

## What this resolves before formalization

The paper theorem now uses the same fixed length, unit payment and exception allowances as the current 127-bit plan. Its index and deficit stops are functions of the message cache and actual spent count, so they can be retained by the OTS projection without exposing private chain evaluations. The common proposal stop uses only completed block lengths. The full and all near banks share these stops; their contents do not determine them.

The existing monitor already helps implement this projection. ProposalCacheBound.index_le uses spent calls, and SigningBoundaryTrace records message input/output pairs while replacing every other hash call by an empty marker. Its costs and message trace therefore survive forgetting private chain inputs. CertificateCacheMonitorUpdate adds a separate analytical cache-exception flag without using that flag to update the coverage core. That stronger flag can be omitted from the OTS history. The remaining full-cache cardinality guard is redundant on supported original paths and must be eliminated using the existing bound by spent calls. This does not authorize keeping that private cardinality in the likelihood comparison.

The remaining Lean generalization is identifiable: replace the fixed original record interpreter by a record kernel carrying its environment, message cache, response, selected view and actual costs. The generic proposal bridge already accepts a record kernel. The local old-target inequality, fresh-target creation charge, expected message payment and selected-index cap must be proved from the message and signing rules above for that kernel. The terminal-word, moment and shared-bank arguments can then use those local results. The final theorem must instantiate the kernel with each concrete graph or forced-secret interpreter and prove its original cost and response correspondence. It must not expose a new adversary premise asserting coverage.

Independent exact finite checks covered the projected-index drift, proposal-prefix normalization with private record data and zero-probability indices, and the finite digest-loop identities. The digest checks included cache repeats, exhaustion, own-input exclusion, simultaneous cache and signing updates, and failure rules depending on the selected view. These checks are diagnostic; the identities and inequalities above give the general paper argument. They do not replace the missing concrete interpreter proofs or establish 127-bit SUF in Lean.
