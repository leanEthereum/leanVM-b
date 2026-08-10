# XMSS security formalization

This Lean project formalizes the classical random-oracle security game from `doc/xmss/main.tex`. It pins Lean and VCVio so that the game, its query accounting, and its probability semantics are reproducible.

The adversary has access to the shared random oracle and a signing oracle. Signing responses are logged. A repeated signing epoch makes the transcript invalid, and the strong-forgery check rejects only an exact replay of the signature returned for the claimed message and epoch. The random-oracle query bound is imposed after the adversary and signing oracle have been simulated, so it covers key generation, adversarial queries, signing, and final verification.

`XmssSecurity.Encoding` proves target-sum incomparability and the exact 99-edge verification cost. `XmssSecurity.Wots` defines hash-chain walks and proves the first deterministic extraction step: a distinct valid encoding with the same recovered endpoints yields either a backward preimage or a domain-separated chain collision. `XmssSecurity.MainTheorem` isolates the unfinished probabilistic reduction in `xmss_forgeAdvantage_le`, the single intentional `sorry`, and derives the initial 120-bit theorem as a checked corollary. `Concrete.scheme` is declared as an axiom until the concrete key generation, signing, and verification algorithms are transcribed from the specification.

Build with:

```bash
lake build
```
