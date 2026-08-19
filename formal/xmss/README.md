# XMSS security formalization

This Lean project formalizes the classical random-oracle security game from `doc/xmss/main.tex`. The main result is `xmss_has_127_bits_of_classical_security`, a machine-checked 127-bit theorem for the concrete scheme `Concrete.scheme`.

The project separates what is proven from how it is proven. A reviewer only has to read four files, about 700 lines in total. `XmssSecurity/Statement/Spec.lean` is the oracle-free part of the specification: parameters, key and signature types, tweak and byte layout, the target-sum encoding, and the hash-chain walk. `XmssSecurity/Statement/Algorithms.lean` is the three algorithms: key generation, signing, and verification, with the oracle hash calls they make. `XmssSecurity/Statement.lean` defines the strong-unforgeability experiment once, generically in the scheme, instantiates it at `Concrete.scheme`, and states the security claim `XmssSecurityStatement`. The root module `XmssSecurity.lean` discharges the claim against the proof. Nothing in these four files imports proof machinery; the proof lives under `XmssSecurity/Proof/` and never needs to be trusted, only checked by Lean.

The scheme deliberately uses an ideal precomputed secret key containing every WOTS chain value and Merkle node. Key generation samples these values through the random oracle and stores them as the pure replay of its own query log. Signing reads the stored tables and queries the random oracle only for message encoding, once per attempt, for at most `2^23` attempts. Repeated table reads are not random-oracle queries. This isolates the cryptographic computation from implementation-specific storage and caching choices.

The adversary has access to the shared random oracle and a signing oracle. Signing responses are logged. Reusing a signing epoch invalidates the transcript, and the strong-forgery check rejects only an exact replay for the claimed message and epoch. The query bound starts after key generation and covers adversarial queries, signing, and final verification. Honest key-generation queries are free, but key generation and the rest of the game share the same random-oracle cache.

The theorem's axiom footprint is limited to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. It contains no `sorryAx` or compiler-evaluation axiom. The root module pins this footprint with `#guard_msgs`, so the build fails if it ever grows.

Build with:

```bash
lake build
```
