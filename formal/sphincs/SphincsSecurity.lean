import SphincsSecurity.Statement
import SphincsSecurity.Proof

namespace SphincsSecurity

/-!
The security theorem for the statement in `SphincsSecurity.Statement`. The proof bounds the retained verifier-probe event through canonical execution, then combines it with the grouped terminal bounds.
-/

/-- `120` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signatures per key pair. -/
theorem sphincs_has_120_bits_of_classical_security : SphincsSecurityStatement := by
  exact Concrete.OtsProbeSimulation.security_of_completed_canonical_boundary

end SphincsSecurity
