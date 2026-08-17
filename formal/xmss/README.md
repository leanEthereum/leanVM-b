# XMSS security formalization

This Lean project formalizes the classical random-oracle security game from `doc/xmss/main.tex`. The main result is `xmss_cappedSigner_has_126_bits_of_classical_security`, a machine-checked 126-bit theorem for `Concrete.cappedScheme`.

The scheme deliberately uses an ideal precomputed secret key containing every WOTS chain value and Merkle node. Key generation samples these values through the random oracle. Signing reads the stored tables and queries the random oracle only for message encoding, once per attempt, for at most `2^23` attempts. Repeated table reads are not random-oracle queries. This isolates the cryptographic computation from implementation-specific storage and caching choices.

The adversary has access to the shared random oracle and a signing oracle. Signing responses are logged. Reusing a signing epoch invalidates the transcript, and the strong-forgery check rejects only an exact replay for the claimed message and epoch. The query bound covers the entire experiment, including key generation, adversarial queries, signing, and final verification.

`PrecomputedKeygen`, `PrecomputedKeygenCache`, and `PrecomputedKeyConsistency` connect the ideal table model to ordinary lazy random-oracle key generation. The capped signing modules prove correctness, replay, cache, and exact query-accounting properties for the retry loop. The global chain modules reduce adaptive forgery events to hidden-value probes against a uniformly presampled chain table. `Capped126MainTheorem` combines the encoding, WOTS, Merkle, and structural-collision losses into the final 126-bit bound.

The theorem's axiom footprint is limited to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. It contains no `sorryAx` or compiler-evaluation axiom.

Build with:

```bash
lake build
```
