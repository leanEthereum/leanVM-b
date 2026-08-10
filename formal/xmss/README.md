# XMSS security formalization

This Lean project formalizes the classical random-oracle security game from `doc/xmss/main.tex`. It pins Lean and VCVio so that the game, its query accounting, and its probability semantics are reproducible.

The adversary has access to the shared random oracle and a signing oracle. Signing responses are logged. A repeated signing epoch makes the transcript invalid, and the strong-forgery check rejects only an exact replay of the signature returned for the claimed message and epoch. The random-oracle query bound is imposed after the adversary and signing oracle have been simulated, so it covers key generation, adversarial queries, signing, and final verification.

`XmssSecurity.Encoding` proves target-sum incomparability, the exact 99-edge verification cost, and injectivity of a security-level digest decoder. `XmssSecurity.Wots`, `XmssSecurity.Merkle`, and `XmssSecurity.ForgeryCases` give checked deterministic classifications of both same-epoch strong forgeries and fresh-epoch forgeries into 175 explicitly indexed bad-event slots. `XmssSecurity.RandomOracle` proves fixed-output and 128-bit truncated-output bounds for an empty or pre-populated lazy random-oracle cache, including a finite-target union bound. `XmssSecurity.HiddenValue` proves adaptive first-hit bounds for one or up to 175 independent hidden 128-bit values. `XmssSecurity.Execution` retains the final lazy random-oracle cache and proves that this does not change the signature-game advantage. `XmssSecurity.MixedOracle` proves the fixed-target bounds directly for the full game, where arbitrary public sampling is interleaved with the bounded hash queries, and closes the 120-bit bound for any static set of at most 175 truncated targets. `XmssSecurity.SecurityBudget` proves that 175 events at cost `q / 2^128` fit below `q / 2^120`. `XmssSecurity.MainTheorem` isolates the unfinished adaptive game reduction in `xmss_reduces_to_badEvents`, the single intentional `sorry`, and derives the 120-bit theorem as a checked corollary.

Two concrete bridges remain. `Concrete.scheme` is declared as an axiom until key generation, signing, and verification are transcribed from the specification. The current digest decoder is an abstract cardinality equivalence; it must be replaced with the concrete little-endian parser and connected to the scheme. The remaining game proof must factor honest targets sampled during the adaptive execution into the checked first-hit experiments, then connect each winning trace to the checked structural cases.

Build with:

```bash
lake build
```
