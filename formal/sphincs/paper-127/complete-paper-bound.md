# Assembling the paper 127-bit bound

This note assembles the preceding paper arguments for the unchanged concrete scheme. It does not assert that the Lean theorem has been proved. The new probability constructions, couplings, certificate counters, and their links to the original experiment still require formalization and review.

Let N=2^128, x=q/N, x_0=3*2^-14, and

    epsilon(q)=q/2^222+q/2^237+2^-700.

The scheme uses independently sampled secrets and a classical random oracle with 256-bit outputs, with the specified low-bit truncations. Retain the actual signing cap, finite retry loops, Option failures, message/randomizer binding, and strong-forgery definition. Every invocation counted in q is an original hash call, including honest computation and final verification. The original game rejects logs longer than S; terminating with a losing result before request S+1 preserves winning probability. This is an analysis step, not a change to the actual signing oracle.

## Supporting arguments

- reference-frontier-transfer.md supplies the exact conditional reference-encoding law, the transfer of canonical OTS prefixes to independent chain challenges, and the expected-cost bound for nonreference equal-code or different-code witnesses.
- paid-probe-quadratic.md supplies an exact planted-graph exposure and a primitive bound that pays the message-query charge in one stopped execution.
- cached-target-forecast.md supplies the degree-14 charged coverage bound and the degree-13 near-target certificate bound, including targets cached before signing. Its one terminal Poisson family controls all adaptive charging times. It also bounds the three exceptional conditions.
- fts-useful-witness.md handles true FTS guesses that become useful before or after digest preparation, and distinguishes alternative preimages even when found before later secret disclosure.

These arguments use changes of experiment only for analysis. They preserve the original marginal law where stated and never give extra interfaces or an internal success flag to the original adversary. The forced-first-guess games are explicitly compared by likelihood and used only for the uniform message-target estimate.

## Reduction of strong forgery

On a nonexceptional run, an accepted strong forgery has at least one of the following: an OTS code or backward-witness event; a noncanonical structural output match; an actual FTS secret guessed before disclosure and still needed undisclosed at forgery; or a digest target fully covered by successful signing views at other inputs.

The canonical graph fixes authentication values. With no noncanonical output match, accepted FTS leaf values are their true secrets. With no OTS deviation, the message, counter, and chain values of each OTS component are canonical. If the message-hash input equals one previously selected by a successful signing invocation, these canonical components give exactly the returned signature. Strong novelty therefore forces an earlier event or coverage by other inputs. Retry exhaustion cannot produce a canonical accepted counter where none exists.

This decomposition is used with full execution costs in the small-q argument. The large-q argument instead stops at the first primitive equality match, which is allowed to precede a usable forgery, and applies the charged coverage estimate to that same stopped execution. Cache exceptions inside honest signing are acted upon at the macro boundary; all its message calls are counted, and no adversarial primitive probe occurs inside the honest macro.

## Small budgets

For 0<x<=x_0, the OTS, cheap structural, and ordinary coverage costs are at most (131/80)x. The remaining useful FTS events have probability at most

    557x^2/(1-x)+x^2/(2(1-x)^2)<(9/80)x.

Consequently

    P[forge] <=(7/4)x+2^-16 x+epsilon(q)<2x.

All query classes share the same path budget; no event class is separately allocated q when its expected query cost is retained.

## Larger budgets

For x_0<=x<=1/2, let B be the first primitive equality match and A_msg the message-call count before that match or exceptional stopping. The paid-probe bound gives

    P[B]+(3/(2N))E[A_msg]<=2x-x^2/8.

The coverage certificate estimate in the same stopped experiment gives the following unconditioned event bound. Write G for the event that no cache, deficit, or clock exception occurs before termination:

    P[covered forgery and no B and G]<= (3/(2N))E[A_msg]+2^-16 x.

The expected charge is evaluated in the stopped experiment, without conditioning on G. Combining the two inequalities with the forgery decomposition and P[not G]<=epsilon(q) yields

    P[forge]<=2x-x^2/8+2^-16 x+epsilon(q).

Since x_0/8-2^-16=2^-17, the negative term pays at least 2^-17 x throughout this range. For q>=1,

    epsilon(q)/x <=2^-94+2^-109+2^-572 <2^-17.

Thus P[forge]<=2x here as well. When q>=N/2, use P[forge]<=1<=2q/N. These cases cover every positive whole-experiment query bound q.

The resulting paper inequality is P[forge]<=q/2^127. Completion of the requested task still requires translating this argument into Lean, connecting every new experiment and charge to Statement.lean, and checking the final theorem's assumptions and axioms. Passing the auxiliary arithmetic scripts is not a substitute for that work.
