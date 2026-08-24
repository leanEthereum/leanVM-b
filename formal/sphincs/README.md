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

Correctness (`Ver` accepts honest signatures, against every answer function, which is what rules out
the claim holding vacuously); domain separation and the injectivity of every payload in the scheme;
incomparability of the target-sum code; the one-guess bound `2^-n`; the pair bound `q * 2^-n`;
extraction of the first divergence for chains, layer trees, one-time signatures and few-time
openings; and the frames the reduction is assembled in, including the adversary's queries logged at
no cost to any distribution.

## What remains, and where the tools are

The extraction lemmas all end in "the adversary's value equals the honest value", and an equality in
its output is not yet a break. Turning it into one needs the honest secret to be unpredictable given
the adversary's view, conditioned on no query having hit it: a hybrid in which the chain's first
answer is reprogrammed to a fresh value, after which the view is independent of the secret and the
logged queries hit it with probability at most `q * 2^-n`.

VCVio has that machinery, which is worth knowing before rebuilding it:

- `OracleComp/QueryTracking/ProgrammingOracle.lean` defines `withProgramming` with the bad flag of
  the identical-until-bad pattern, and `ProgramLogic/Relational/ProgrammingOracle.lean` proves the
  bound `tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad`, with a heterogeneous version
  for the lazy random oracle whose base implementation lives in `ProbComp`.
- `RandomOracle/ProbeEps.lean` has the hidden-target bound `probEvent_hiddenReadMany_le`: a target
  drawn once and probed by `q` adaptive reads fires with probability at most `q * eps`.
- `RandomOracle/DeferredSampling.lean` has the distribution-level bind commutation that front-loads
  answer-irrelevant draws onto a tape.

What does not fit yet is the shape. Those bridges are stated for a computation over one spec,
simulated by `so.withCaching`; the game here runs over `unifSpec + HashSpec` under
`unifFwdImpl + randomOracle`, which is not `so.withCaching` for any single `so`, and `roSim` carries
only lifting and dispatch lemmas, no bridge. Two routes: generalize the identical-until-bad bound to
the sum spec, or front-load the game's own sampling so the surface computation is hash-only, which is
what `DeferredTape.Factorizes` is for and which its authors flag as the scheme-specific part. The
randomizer resampling is the awkward case there, since it does influence control flow.

After the hybrid: composing the extractions through it, the leak's binomial argument for the
`2^-133.3` term, and the arithmetic to `q / 2^120`.

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
