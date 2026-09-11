import SphincsSecurity.Statement
import SphincsSecurity.Proof

namespace SphincsSecurity

/-!
The public security theorems for the statements in `SphincsSecurity.Statement`. The 127-bit proof splits the whole-experiment hash budget at `3 * 2^114`: larger budgets are bounded by the retained residual certificate monitor, and smaller budgets reduce the remaining near-certificate event to forced FTS guess games that are monitored and bounded slot by slot. The independent 126-bit proof projects residual forgeries into the native rejection and finalization experiment, bounds that experiment by the refined query reserve, and combines it with the forest, structural, encoding and message-collision bounds in the original SUF experiment.
-/

/-- `127` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signing requests per key pair. -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurity127Statement :=
  Concrete.security127

/-- `126` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signing requests per key pair. -/
theorem sphincs_has_126_bits_of_classical_security : SphincsSecurity126Statement := by
  exact Concrete.OtsProbeSimulation.security126_of_completed_native_boundary

/-- `125` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signing requests per key pair. -/
theorem sphincs_has_125_bits_of_classical_security : SphincsSecurity125Statement := by
  intro q hq adversary hbound
  apply (sphincs_has_126_bits_of_classical_security q hq adversary hbound).trans
  gcongr <;> norm_num [securityBits]

/-- `120` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signatures per key pair. -/
theorem sphincs_has_120_bits_of_classical_security : SphincsSecurityStatement := by
  intro q hq adversary hbound
  apply (sphincs_has_126_bits_of_classical_security q hq adversary hbound).trans
  gcongr <;> norm_num [securityBits]

end SphincsSecurity
