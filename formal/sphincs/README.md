# SPHINCS security statement

This Lean project states, and does not yet prove, the classical random-oracle security of the concrete SPHINCS instance of `doc/sphincs/main.tex`: `SphincsSecurityStatement`, which reads `HasClassicalSecurityBits Concrete.scheme 120`.

Everything the claim depends on is in the single module `SphincsSecurity/Statement.lean`, in the order a reviewer needs it: the concrete parameters and types with the tweak and byte layout of every hash input and the target-sum code, the three algorithms with the oracle calls they make, then the strong-unforgeability experiment and the claim. It follows `formal/xmss`, whose statement module is the model for this one and whose proof machinery is what a proof here would extend.

## What the game says

Key generation samples the public parameter, one secret per Winternitz chain of every layer, tree and leaf, and one per few-time leaf of every instance, then builds layer 0's tree for the root. Signing draws a fresh randomizer per digest attempt until the digest's last index group is zero, opens the few-time forest, and produces one one-time signature per layer, recomputing through the random oracle whatever tree it needs; the specification's seed derivation and the signer's cache are implementations of this key and change no probability. Verification is the ordinary verifier. Key generation, the adversary, the signing oracle and the final verification share one lazily sampled oracle, and `q` bounds the hash queries of the whole experiment.

Three things differ from the XMSS statement, all because this scheme is stateless.

- A signing request is a message, with no epoch. What the game caps is therefore the number of signing queries, at `signatureLimit = 2^24`, rather than forbidding a repeated epoch.
- Signing is randomized, so one message has many valid signatures. The game rejects only a signature the signer actually returned for that message, which is what makes the claim a strong-unforgeability claim.
- The secret key holds the sampled secrets instead of precomputed tables, so signing queries the oracle for the chains, nodes and forests it reads, rebuilding a tree rather than caching it. The honest experiment therefore spends `2^44.5` hash queries of its own, against the `2^41.5` a real signer with the cache of `doc/sphincs/main.tex` pays. What the query bound counts is the worst-case path rather than the average, which the `2^32` digest and counter caps push to exactly `2^58`.

Every component of the `Signature` structure is read by verification, the authentication path being the `h` nodes of the `d` layers laid end to end. That matters, an unread component making the strong-unforgeability game trivially winnable by perturbing it, so `signaturePath_flattenPaths` and `authPath_exhausted` prove that the verifier reads a layer's node exactly where the signer laid it and that no entry goes unread. The index decomposition is proven the same way rather than asserted: `treeIndexAt_topLayer`, `layers_link_top`, `layers_link_middle` and `leafIndexAt_bottomLayer` hold for all `2^26` indices.

## Why 120 bits and not 128

The bound is the slope `q / 2^bits`, so it bounds what one query buys. Every strategy the specification accounts for costs `2^-128` per query: inverting a chain step, a node or a leaf, recovering a published secret, or grinding a counter onto an already signed codeword, each separated from the others by its tweak, so no query bears on two structural positions and no multi-target factor appears. The few-time leak is a per-query slope as well, `2^-133.3` at `q_s = 2^24`, five bits under the generic term, so it does not bind; it is what fixes `signatureLimit`, reaching `2^-128` at `2^25.1` signatures and `2^-120` at `2^26.4`, about two doublings of headroom. Read the claim where an adversary spending all `2^24` signatures lives: the query bound counts every execution path, so the `2^32` attempt caps put the floor at `q = 2^58`, where the bound reads `2^-62` against a true forging probability of about `2^-70`. The slack is that same `2^8` at every `q`, the dominant term being linear in it. Claiming 120 leaves `2^8` for the union bounds and constants a proof accumulates, where XMSS could claim 127 against the same digest length with one hash chain layer and one tree.

## Status

## What is proven

Correctness (`Ver` accepts honest signatures, against every answer function, which is what rules out the claim holding vacuously); domain separation and the injectivity of every payload in the scheme; incomparability of the target-sum code; the one-guess bound `2^-n` at the digest length and at any width, including the index a fresh digest selects; the accounting `(c * q + potential) * eps` for an arbitrary bad event on the oracle's cache; extraction of the first divergence for chains, layer trees, one-time signatures and few-time openings; and the frames the reduction is assembled in, including the adversary's queries logged at no cost to any distribution.

## The shape of the proof

The whole probabilistic side is one lemma, `Amortized.probEvent_bad_le_amortized`. Give it a predicate `Bad` on the random oracle's cache, a potential `Nat` on caches and a constant `c`, prove that a fresh answer on an uncached input turns the cache bad only by landing in a finite set of digests whose size the potential pays for up to `c` per query, and it returns `(c * q + potential) * eps`. Nothing else about the oracle is needed: no presampling, no reprogramming, no hybrid.

That shape is forced by what the forgery has to hit. Every hit the extraction produces is "a payload other than the honest one, hashing at the same tweak to the honest value there", and the honest value is itself an oracle answer, drawn during the run. So no fixed map on inputs can name the honest partner of an input, and a bound quantified over such a map cannot be instantiated. What replaces it is a cache-local event. A tweak names one structural position (`Bytes.tweakBytes_injective`), a position has one honest payload, and that payload is *determined* by the cache as soon as every honest query below it is cached, in the sense that all answer functions agreeing with the cache agree on it. `Bad` is then: some domain is determined, its honest input is cached, and some other cached input at the same domain has the same truncated answer.

The charges a fresh answer faces, and what pays for them:

- an adversarial input at a domain whose honest input is already cached and determined: one target, paid by `c`;
- the honest input at such a domain, queried fresh: one target per cached input at that domain, each of which deposited a unit when it was cached and had no honest counterpart to hit yet;
- the answer that *determines* a domain, one query being the last honest query below it: the domain's honest input is fixed only now, and may already be cached, so one target per cached input at that domain, each of which deposited one unit per undetermined slot of its own domain's payload.

Each honest position feeds exactly one parent, so one answer determines at most one domain and the third charge happens once per slot. The potential is therefore the sum, over cached inputs at a structural domain, of one plus the number of that domain's slots still undetermined, and `c` is `2` plus the widest payload, the `v = 42` chain endpoints of a leaf. That is `log2 44 = 5.5` bits of the `8` the claim leaves, against `2^-122.9` for the few-time leak: the two together stay under `2^-120`.

The frame splits the game at the secret sampling rather than after key generation. Key generation's own hash queries then belong to the accounted run, so the accounting starts from the empty cache, at potential `0` and trivially clean, and no fact about what key generation leaves behind is needed.

`PairBound` was deleted rather than kept: it bounded the same sum through a fixed partner map on inputs, which is exactly what the honest value's run dependence rules out.

## What remains

The probabilistic side is finished as a tool and half-instantiated. What is in place: `Position` (the finite index set, with `mem_children_iff`, so children and parent agree and no position has two parents), `Honest` (payload, input and value at a position, every payload being the values below it at sixteen bytes each, hence `honestPayload_congr` and `slots_injective`), `Settled` (the positions a cache pins, monotone), `Slot` (`slotDigest_flatMap`, reading the block of a payload a value lands in), and `Charge` (`Bad`, `cachedAt`, `unsettledChildren`, `potential`, and `settled_of_settled_cacheQuery`: one query settles no position but the one its input is at, unless it settles that position's parent).

In order:

- **The amortized step for `Bad`**, feeding `Amortized.probEvent_bad_le_amortized` with `c = 44`. The case analysis on the queried input `input₀` is: at no position, at a settled position (one target, the honest answer's truncation), at an unsettled position it is not the honest input of (no target, nothing settles), and the honest input of an unsettled position whose children are all settled. Only the last one charges: the truncations of the inputs already cached at that position, paid by the unit each of them deposited, and the blocks `slotDigest` reads at the parent, paid by the parent's per-child units. `settled_of_settled_cacheQuery` is what closes the rest.
- **The descent**, the deterministic bulk. A forgery is `Bad`, or a replay, or the few-time leak, or a guessed secret. It needs the honest values along the forgery's path settled, which is where "key generation queried all of layer 0" and "signing queried every tree it read" are used, and incomparability at each layer to turn "every value honest" into "the message is one that was signed".
- **The leak's counting side**, `LeakArith.leak_union_bound_scaled` being its arithmetic already, and the guessed secret, which is where `ProbeEps.probEvent_hiddenReadMany_le` fits: a few-time secret is drawn once and read only by the openings.
- **The final arithmetic** to `q / 2^120`.

Nothing closes the main claim yet. The one-time and Merkle halves of `formal/xmss` carry over, sharing the tweakable hash, the target-sum code and the shape of the bound; what is new is the hypertree, the few-time forest, the digest that picks the index, and the counter search under a tweak shared across attempts.

Two places a proof can go wrong, both found by attacking the claim rather than by reading it:

- **A strong forgery needs no chain inversion.** `Ver` does not check that the counter is the least admissible one, so a second `c'` with `Enc(P,lay,tau,e,M,c') = x` reuses the chain values verbatim and verifies. Since the codeword fixes the digest, that is one `2^-128` hit per query and it is harmless, but it is a branch of its own: the one-time signature is unforgeable on a *new* message by incomparability, and unforgeable on the *signed* message only by collision resistance at `tw_enc`.
- **Keep the conjunction in the one-time bound.** A forger does not need a codeword dominating `x`, only one lower on a single chain, `x' = x - e_j + e_l`, of which there are `1258` at these parameters. So an encoding query hits an exploitable shape with probability `2^-117.7`, above the `2^-120` slope; the event is a forgery only together with one chain inversion, giving `q^2 * 2^-247.7`. Charge the shape alone, linearly in `q`, and the proof fails at 120 bits.

Build with:

```bash
lake exe cache get   # first time only
lake build
```

`lake build` reports the `sorry` in `SphincsSecurity.lean`, which is the open goal, and nothing else.
