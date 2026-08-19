# XMSS security formalization

This Lean project formalizes the classical random-oracle security game from `doc/xmss/main.tex`. The main result is `xmss_has_127_bits_of_classical_security`, a machine-checked 127-bit theorem for `xmssScheme`.

The project separates what is proven from how it is proven. A reviewer only has to read `XmssSecurity/Statement.lean`, the definitional modules it imports from `XmssSecurity/Statement/`, and the root module `XmssSecurity.lean`. `XmssSecurity/Statement.lean` defines the scheme interface, the strong-unforgeability experiment, the query-counting convention, and the security claim `XmssSecurityStatement`; the `XmssSecurity/Statement/` directory holds the concrete algorithms and types those definitions use, and imports no proof machinery. The root module states the theorem and discharges it against the proof, which lives under `XmssSecurity/Proof/` and never needs to be trusted, only checked by Lean.

The scheme deliberately uses an ideal precomputed secret key containing every WOTS chain value and Merkle node. Key generation samples these values through the random oracle. Signing reads the stored tables and queries the random oracle only for message encoding, once per attempt, for at most `2^23` attempts. Repeated table reads are not random-oracle queries. This isolates the cryptographic computation from implementation-specific storage and caching choices.

The adversary has access to the shared random oracle and a signing oracle. Signing responses are logged. Reusing a signing epoch invalidates the transcript, and the strong-forgery check rejects only an exact replay for the claimed message and epoch. The query bound covers the entire experiment, including key generation, adversarial queries, signing, and final verification.

`PrecomputedKeygen`, `PrecomputedKeygenCache`, and `PrecomputedKeyConsistency` connect the ideal table model to ordinary lazy random-oracle key generation. The signing modules prove correctness, replay, cache, and exact query-accounting properties for the retry loop. The exact first-lane reduction couples every adaptive adversary and final-verification query to one enforced hidden-value experiment. It charges the two first-lane event families jointly to at most `q - keygenQueries + numChains` probes. The second-lane bound and exact loss arithmetic then yield the final 127-bit theorem.

The theorem's axiom footprint is limited to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. It contains no `sorryAx` or compiler-evaluation axiom. The root module pins this footprint with `#guard_msgs`, so the build fails if it ever grows.

Build with:

```bash
lake build
```
