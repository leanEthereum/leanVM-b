# Paper review and decision plan for 127 bits

The target is the unchanged strong-unforgeability game in Statement.lean, with independently sampled secrets and a classical random oracle. Put N=2^128 and x=q/N, where q bounds all original hash calls on every execution path. The required inequality is P[forge]<=2x. The existing paper notes describe a candidate proof of this inequality. Reviewing their algebra and finite examples supports the route; it does not certify the adaptive probability constructions or their concrete-game interfaces. This review makes no change to Lean sources.

The central conclusion is that tightening a standalone occupancy estimate is insufficient. A primitive bound of 2x followed by any positive coverage allowance cannot prove 127 bits. There are two complementary ways to recover room: count completed forgery witnesses for small x, and obtain a quadratic saving while paying message-query costs inside the primitive bound for larger x. Both must use the original query allocations.

## A sufficient pair of inequalities

Let delta=2^-16, x_0=3*2^-14, and epsilon(q)=q/2^222+q/2^237+2^-700. It suffices to establish the following inequalities for the actual experiment:

    0<x<=x_0:       P[forge] <= (7/4)x + delta*x + epsilon(q),
    x_0<=x<=1/2:    P[forge] <= 2x - x^2/8 + delta*x + epsilon(q).

The closure is exact. At x_0, x_0/8-delta=2^-17. For every q>=1, epsilon(q)/x<=2^-94+2^-109+2^-572<2^-17. The first range has still more room. For x>=1/2, probability at most one proves the claim directly. Thus the final arithmetic is no longer the main uncertainty. The questions are whether the two probability inequalities apply to one correctly defined original experiment, and whether the same stopped message costs occur on both sides of the large-budget argument.

## First decision point: adaptive coverage, with a precise filtration

Prove an abstract lemma for the real digest-selection mechanism, allowing arbitrary adaptive non-message transitions that do not inspect unqueried message cells. The result must cover successful Option signing responses, targets created before later signatures, and exclusion of the target's own message/randomizer input. It must bound certificate counts, not just the chance of a fixed target being covered:

    E[C_full] <= (3/(2N))*E[A_msg] + delta*x,
    E[C_near] <= 557*x.

Here a full certificate has all 14 coordinates covered by other successful signing inputs; a near certificate specifies one omitted coordinate and covers the other 13. A_msg counts original message hash calls in precisely the stopped experiment under analysis. Previously completed certificates survive a later exceptional stop.

The required history is neither the adversary's transcript alone nor every internal oracle input. At a boundary it includes the exposed canonical graph, original message-query records, returned signing responses, original hash counts, prior analysis flags, and consumed auxiliary proposals. It excludes still-hidden secret labels, the internal non-message inputs that reveal them, and unused proposal values. Fresh message cells must remain uniform conditional on this history. This is an explicit invariant to prove, rather than a consequence to assume from a marginal distribution.

Write W_j for the normalized fresh-target forecast before a charging step and a_j for its predictable creation multiplier. The decisive statement is existence of one terminal random variable R such that, at every clean boundary,

    W_j <= E[R | F_j],
    E[(R-3/2)_+] <= delta,
    sum_j a_j <= q,
    E[sum_j a_j] <= E[A_msg].

Conditional Jensen and the tower property then give the entire adaptive charging argument:

    E[sum_j a_j W_j]
      <= (3/2)*E[sum_j a_j] + E[(R-3/2)_+ * sum_j a_j]
      <= (3/2)*E[A_msg] + q*delta.

Divide by N and use the banked forecast argument to obtain the full-certificate bound. The analogous degree-13 terminal variable gives the near-certificate estimate. A small unconditional mean of W_j at fixed times would not establish these statements at adaptive charging times.

The candidate construction in discrete-target-coupling.md supplies a concrete way to prove the terminal domination. With I=2^26, S=2^24 and beta=1537/1024, embed each selected signing index with law p_i<=beta/I into uniform proposals. For a rejected word u_1,...,u_k and a signing record omega, the common mass of the macro-first and proposal-first constructions is

    K_h(omega)/beta * product_a (1/I-p_(u_a)/beta).

This identity must be lifted inductively to the full boundary history. Independently choose J~Poisson((19/50)*I) and take the first J proposals. Their occupancies Z_i are independent Poisson(19/50) without conditioning on a good event. The full terminal variable is R=sum_i Z_i^14/2^48; the near variable is (14/2^38)*sum_i Z_i^13.

The raw forecast comparison has a separate algebraic obligation. First bound future cache growth using positive polynomial moments, E[(c+Binomial(b,2^-36))^d]<=(c+b/2^36+d)^d. Only then interpret the remaining signing operator as a probability transition on its bounded reachable states. Its increment rate is at most v_q with I*v_q<=beta. If m unused uniform proposals remain and r signing calls remain, the clean-prefix construction ensures m>=beta*r+d-1. Consequently, for every j<=d,

    (r)_j*v_q^j <= (beta*r/I)^j <= (m)_j/I^j.

Expanding shifted powers in falling factorials proves domination by the unused proposal counts. This avoids treating the unbounded raw signing polynomial as a probability kernel.

The stopping rules are part of this lemma. Cache and deficit bounds may first be crossed during a signing invocation; that invocation must finish before the analysis stops, retaining all its original calls. Proposal overflow is also handled at the completed boundary. Stop with loss before signing request S+1, since every original execution reaching that request has an invalid final log. Never condition the experiment on remaining within the caps.

This is the first decision point because both budget ranges depend on it. Its review criterion is the complete stopped certificate inequality with the filtration invariant and original cost variable, rather than another isolated moment estimate.

## Second decision point: the small-budget forgery decomposition

Expose canonical OTS frontiers using the actual joint distribution of reference counters, codewords and canonical messages. The fixed canonical message matters: replacing it by an adaptively chosen honest message would invalidate the linear encoding preparation bound. Transfer the static chain likelihood argument while charging adversarial and verification prefix queries to their actual original call counts.

The OTS bound must retain two expected allocations, Q for prefix queries and A_enc for fresh nonreference encoding queries. Define

    c(x)=((3/2)+4x+2x^2)/(1-x)+4x/(1-x)^2,
    c_Q(x)=c(x)+82x/(1-x),
    c_enc(x)=1+3444x/(1-x).

The required OTS estimate is c_Q(x)*E[Q]/N+c_enc(x)*E[A_enc]/N. At x<=x_0 both coefficients are below 131/80. Cheap noncanonical structural output matches have coefficient one, and the ordinary message-coverage charge has coefficient 3/2. These classes are disjoint, so their sum is at most (131/80)x. Giving each class a separate budget q would destroy this conclusion.

For FTS, separate an alternative preimage from a true secret guess. An alternative preimage remains a cheap output-match event even if it was found before the true secret was later disclosed. Two distinct true guesses cost at most x^2/(2(1-x)^2). A forgery using just one still-undisclosed secret also requires a near certificate. Force the first true guess at slot j using the deferred-secret kernel; its likelihood weight is at most 1/(N-q), while unqueried message cells retain their original law. The coverage lemma must apply uniformly to this modified experiment. Summing over slots gives at most 557x^2/(1-x), including certificates completed either before or after the guess.

For x<=x_0,

    557x/(1-x)+x/(2(1-x)^2) < 9/80.

This yields 131/80+9/80=7/4 before the coverage excess and exceptional allowance. The review criterion is a decomposition of every accepted strong forgery into these events, including final verification queries, repeated signed messages, failed signing calls, and the target-input exclusion. The likelihood formula alone is insufficient without its compatibility with the coverage filtration and the original path budget.

## Third decision point: the large-budget joint charge

Use the canonical planted graph to define B, the first primitive equality match, and stop the same certificate experiment at B. Before B, a hash call has at most two probes against distinct still-hidden labels. Message calls have no such probes and earn reward 3/(2N). Honest internal canonical evaluations disclose no hidden inputs and still consume original hash budget.

After t hash slots, a hidden label has at most t excluded candidates. The scalar upper hazard is h_t=1-((N-t-1)/(N-t))^2. The stopped reward calculation gives

    P[B]+(3/(2N))*E[A_msg]
      <= max_(0<=a<=q) [3a/(2N)+1-((N-q)/(N-a))^2]
      <= 2x-x^2/8.

The abstract algebra has been checked. The concrete obligation is the hidden-label invariant: every external reply and signing disclosure before B must preserve the claimed product of uniform laws on unexcluded sets. Disclosures may depend on observed data, but cannot select a secret coordinate by inspecting its hidden value. Internal secret-dependent query inputs cannot silently enter the analyst's history.

With no B, an accepted strong forgery requires full coverage by other signing inputs. Apply the first decision point in this same stopped experiment. Its ordinary (3/(2N))*E[A_msg] charge is already paid by the displayed inequality, leaving only delta*x and epsilon(q). This proves the second sufficient inequality.

## Assessment

The proposed constants have a nonempty overlap between the two budget ranges, and the local kernel identities have concrete algebraic proofs. I found no numerical obstruction in this route. The exact rational scripts coverage-closing-checks.py and reference-and-paid-checks.py pass; adaptive-kernel-checks.py checks the proposed local kernels on finite instances. Such checks cannot establish a general adaptive coupling.

The plan should be judged by the three original-experiment endpoints above. The greatest uncertainty is the common coverage filtration and its compatibility with exceptional stopping and forced guesses. The planted-graph and OTS transfers are also substantive proof obligations. Until those interfaces are established, this is a credible candidate proof strategy, not a completed paper theorem or a promise that only routine Lean translation remains.
