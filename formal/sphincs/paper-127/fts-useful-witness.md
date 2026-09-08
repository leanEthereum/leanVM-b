# Useful FTS witnesses at small query budgets

This paper argument uses the near-target certificate bound in cached-target-forecast.md. Its purpose is to count a usable secret guess, rather than treating every hidden input guess as a complete forgery. Both chronological orders of digest preparation and secret guessing are included.

## Separate alternative preimages from true guesses

Expose all FTS leaf hashes and internal nodes for analysis. A leaf function has the planted form H_l(S_l)=Y_l, with S_l uniform and all other rows independently uniform. The secret is disclosed when a successful signing response selects that leaf.

A noncanonical output match, H_l(z)=Y_l with z!=S_l, costs at most 1/N per fresh external leaf query. This bound holds even if the query precedes disclosure of S_l: for this collision analysis one may expose S_l from the start, while leaving every noncanonical row unqueried and uniform. Running the original adversary while ignoring the advice preserves its law. Such matches are included with the other cheap structural collision events.

The remaining FTS event is a true guess: an external query uses z=S_l before that secret has been disclosed by signing. Internal honest evaluations are not guesses. Before the first such guess to an undisclosed leaf, its secret is uniform on the values not previously queried for that leaf. Previously observed alternative preimages do not change this conclusion on the event that no true guess has occurred: those queried rows are noncanonical, and their replies are independent of the remaining secret value.

Consequently, at any eligible query the conditional true-guess probability is at most

    h=1/(N-q).

After a true guess, remove that leaf from subsequent guess counting. Honest disclosures likewise retire their selected leaves. Each hash call addresses at most one leaf. The conditional bound h then gives

    P[at least two distinct true guesses] <= choose(q,2) h^2
      <= x^2/(2(1-x)^2).

The count is of distinct leaves, not repeated successful uses of one guessed value.

## Force the first true guess at a specified hash slot

Consider a signature requiring exactly one secret still undisclosed at the time of forgery. Its other 13 coordinates are covered by signing views at other inputs. Thus its digest supplies a near-target certificate for the missing coordinate. The real execution contains both a true guess and a near-target certificate, in either order.

For each of the at most q hash slots j, define a modified experiment. Before j, force every eligible undisclosed-leaf query to miss its true secret. At j, if it is eligible, force its candidate to be the true secret. Continue normally afterwards. Stop on the same cache and clock exceptions as in the coverage argument.

The forced-miss kernel maintains a secret uniform on its remaining values and produces an independent noncanonical hash answer, which is allowed to equal its public leaf hash. At the forced hit, the secret becomes the queried candidate and its answer is the public hash. Other secrets and all already disclosed values are unchanged. This is a conditional-kernel construction; it does not give the original adversary a true-guess flag.

The density of a real path whose first true guess is at j, relative to this forced experiment, is the product of its preceding miss probabilities and its hit probability at j. It is therefore at most h. All message-oracle calls remain fresh uniform calls when their inputs were not cached. The modifications inspect only prior history, known public hashes, and the selected secret coordinate. They do not inspect future message cells.

Honest internal leaf computations in the planted simulation read the public graph labels; only externally observed rows need be retained. Adjusting an undisclosed secret in a forced conditional kernel therefore changes no previously disclosed signing value or observed canonical node value. A final consistent secret and noncanonical row table realize the visible transcript. Internal hash counts are unchanged, so the original whole-experiment path bound q is preserved. Signature index selection, finite digest retries, target exclusion, and the fixed public root remain the same.

The near-target estimate applies to each forced experiment: its expected completed certificate count before exceptional stopping is at most 557x. The event of at least one certificate has probability at most that expectation. Summing over the possible first-guess slots gives

    P[one still-undisclosed secret supplies a forgery, without exception]
      <= q h *557x =557x^2/(1-x).

This argument includes certificates obtained before the guessed secret, after it, or through later signing calls that complete a previously cached target. It does not require a separate independence assumption between a guess and preparation.

## Why these cases suffice for FTS

In the absence of noncanonical structural output matches, every accepting authentication path reaches the canonical leaf hash. Every accepted leaf value is therefore its actual secret unless an alternative preimage event has already occurred. If at least two of the forgery's actual secrets remain undisclosed by signing, final verification entails two distinct true guesses. If exactly one remains undisclosed, the preceding near-target argument applies. If none remains undisclosed, the digest is an ordinary covered target, unless its own input was signed successfully.

In that last case, canonical FTS values, paths, and OTS components make the signature identical to the successful signing response. A strong forgery at the same input must instead contain an OTS deviation or a noncanonical structural output match. In particular, an alternative preimage found before a later disclosure is charged as a noncanonical output match; it is not omitted because its leaf happens to be disclosed by the time of forgery.

Hence, apart from cheap structural events and ordinary covered targets, the total FTS contribution on a nonexceptional run is at most

    557x^2/(1-x) + x^2/(2(1-x)^2).

## Shared budget and the small-query coefficient

For x<=x_0=3*2^-14, the OTS estimate in reference-frontier-transfer.md has its prefix and encoding coefficients below 131/80. Fresh noncanonical structural queries, including every FTS leaf query that might produce an alternative preimage, have coefficient at most one. Ordinary coverage costs 3/(2N) per message query in expectation. These are disjoint query classes in the same execution; legitimate honest calls and unused budget only add slack.

Thus the OTS and cheap structural events plus the ordinary coverage charge are at most (131/80)x. Exact rational arithmetic gives, throughout this range,

    557x/(1-x) + x/(2(1-x)^2) <9/80.

The useful FTS contribution therefore leaves the combined coefficient below

    131/80+9/80=7/4.

After adding the unpaid full-coverage excess and the exceptional-event probability from cached-target-forecast.md,

    P[forge] <=(7/4)x +2^-16 x +epsilon(q) <2x.

This is a paper small-budget conclusion for the same strong-unforgeability game. It is not yet formalized in Lean.
