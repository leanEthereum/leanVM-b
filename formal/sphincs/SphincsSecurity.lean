import SphincsSecurity.Statement
import SphincsSecurity.Proof

namespace SphincsSecurity

/-!
The public security theorems for the statements in `SphincsSecurity.Statement`. The 127-bit proof splits the whole-experiment hash budget at `3 * 2^114`: larger budgets are bounded by the retained residual certificate monitor, and smaller budgets reduce the remaining near-certificate event to forced FTS guess games that are monitored and bounded slot by slot.
-/

/-- `127` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signing requests per key pair. -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurityStatement :=
  Concrete.security127

end SphincsSecurity
