# A discrete common terminal variable for adaptive target forecasts

This supplies an explicit coupling for the forecast argument in cached-target-forecast.md. All auxiliary random objects are integers or finite words. No continuous-time process or conditional oracle law inside a signing invocation is required.

Set I=2^26, S=2^24, d<=14, beta=1537/1024, D=S/128, and lambda=19/50. At a signing boundary, let h be the recorded history, K_h the actual distribution of the next signing record, and i(omega) its selected index, filled with an independent uniform index on digest exhaustion. Write p_i=sum_(omega:i(omega)=i) K_h(omega). On a clean cache prefix, p_i<=beta/I and sum_i p_i=1. A record includes the original message-query trace, returned Option signature, and actual hash-call count. It does not disclose secret-dependent internal non-message query inputs. Those remain hidden in the planted simulation and can be reconstructed after deferred secrets are sampled.

## Exact rejection bridge for one signing invocation

Sample the actual signing record omega with law K_h. Independently conditional on h, sample a number G>=1 with

    P[G=k+1]=(1/beta)(1-1/beta)^k,

then k rejected indices independently with distribution

    r_i=(beta/I-p_i)/(beta-1).

The auxiliary proposal block is the rejected word followed by i(omega). This law is well-defined: r_i>=0 and sum_i r_i=1. The bridge's length and rejected indices are independent of the actual record conditional on the preceding history; its final index is already determined by that record.

Equivalently, repeatedly propose a uniform index u and accept it with probability I*p_u/beta. At its first acceptance i, sample omega with conditional law K_h(omega)/p_i on i(omega)=i. The exact joint mass of a rejected word u_1,...,u_k and a compatible signing record omega is, in either construction,

    K_h(omega)/beta * product_(a=1)^k (1/I-p_(u_a)/beta).

Terms with p_i=0 have K_h(omega)=0 and need no conditional distribution. This equality proves both the original macro marginal and the uniform-proposal interpretation. The first construction makes preservation of unqueried message cells explicit: the added rejected word and length do not inspect them. The second makes every next proposal uniform conditional on the preceding proposals and completed actual transitions.

Between signing invocations, use the actual external-query transitions and do not consume proposals. Discarded executions can be extended using dummy uniform index choices. Repeating the bridge gives a single proposal word whose every fixed prefix is uniform on I to that power. Auxiliary acceptance decisions and completed signing records can be retained in the history; unused proposals remain independent uniforms at each completed boundary. This assertion follows by finite-prefix induction from the uniform-proposal construction, rather than by conditioning on the future event of a successful coupling.

An infinite word is only a convenient description. One can construct the same joint law with finitely many geometric blocks, at most S, and an independent finite uniform suffix. If a block exceeds the terminal length defined below, finish that block and the actual invocation, then terminate the analysis. The terminal word takes only its required prefix. Such an overflow necessarily triggers the prefix exception on a non-short terminal length.

## A random finite terminal word

Independently sample J~Poisson(lambda*I), and take the first J proposals as the terminal word. Let Z_i be its occupancy counts. For any nonnegative integer vector z and m=sum_i z_i,

    P[Z=z]=exp(-lambda*I)(lambda*I)^m/m! * m!/(product_i z_i!)*I^-m
          =product_i exp(-lambda)*lambda^(z_i)/z_i!.

Thus the Z_i are independent Poisson(lambda) variables exactly. The proposal construction works for every fixed J and keeps the original macro marginal conditional on J. J is known to the analyst, but it reveals no message-oracle cell.

Let K_s be the number of proposals consumed by s completed signing invocations. Actual signing counts satisfy s_i<=z_i, where z_i counts consumed proposals of index i, because every successful signing view contributes its accepted proposal. Kill the analysis if initially

    J < beta*S+D+13 = 25313293,

or if, after any signing invocation,

    K_s > beta*s+D.

Both conditions are adapted. As with the cache exceptions, a condition reached during the auxiliary construction of an invocation is acted upon only after the actual invocation finishes. All its actual hash costs are retained. Previously banked certificates are retained.

At a clean boundary after s signings, the number m=J-K_s of unused proposals satisfies

    m >= beta*(S-s)+13 >= beta*r+d-1,       r=S-s.

Conditional on the full boundary history, the future count in each individual bin is Binomial(m,1/I). Dependence between different future bins is harmless: the forecast uses a sum of their individual moments. The terminal occupancies are not conditionally claimed to be independent Poisson variables.

## Dominating the raw forecast at every boundary

The positive-polynomial comparison in cached-target-forecast.md bounds each raw degree-d forecast by E[(s_i+B)^d] for B~Binomial(r,v_q), where I*v_q<=beta. For 0<=j<=d, the falling-factorial moments obey

    E[(B)_j]=(r)_j v_q^j <= (beta*r/I)^j
             <= (m)_j/I^j = E[(Binomial(m,1/I))_j].

For j>0 the second inequality follows because every factor m-a, 0<=a<j, is at least beta*r. For j=0 both sides equal one. Powers and shifted powers have nonnegative expansions in falling factorials. Since z_i>=s_i, this proves

    E[(s_i+B)^d] <= E[Z_i^d | boundary history].

Consequently the same two terminal variables work for every adaptive charging time:

    W_14 <= E[sum_i Z_i^14/2^48 | boundary history],
    W_near <= E[(14/2^38)sum_i Z_i^13 | boundary history].

This is an unconditioned coupling with killing on prefix exceptions. On killed states set subsequent charges and pending forecasts to zero; do not condition the probability space on J being large or on future prefix inequalities. The unconditional Poisson moment calculations therefore apply directly to the one terminal variable used in the adaptive charge argument.

## Exceptional probability

The geometric bridge lengths are independent with mean beta, even when the actual states and index distributions are adaptive. Fill dummy lengths after early termination. For theta=1/128, b=beta-1, put

    u=b*(theta+theta^2/(2*(1-theta/3))),
    c=-b*theta+u+u^2/(2*(1-u)).

The identities for the geometric generating function, together with exp(theta)-1<=theta+theta^2/(2*(1-theta/3)) and -log(1-u)<=u+u^2/(2*(1-u)), give

    log E[exp(theta*(G-beta))] <= c.

The nonnegative supermartingale exp(theta*(K_s-beta*s)-s*c) and its maximal inequality give

    P[exists s<=S: K_s>beta*s+D] <= exp(-theta*D+S*c) < exp(-500).

For mu=lambda*I and j_0=25313293, a Poisson exponential bound gives

    P[J<j_0] <= exp(theta*j_0+mu*(exp(-theta)-1))
              <= exp(-theta*(mu-j_0)+mu*theta^2/2) < exp(-500).

All displayed parameter inequalities are rational and checked in coverage-closing-checks.py. Finally exp(500)>2^701, so the sum of these two exceptional probabilities is below 2^-700. The total exceptional allowance in the closing proof is unchanged.
