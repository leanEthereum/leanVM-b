import SphincsSecurity.Statement
import SphincsSecurity.Proof

namespace SphincsSecurity

/-!
The public security theorems for the statements in `SphincsSecurity.Statement`. The 125-bit proof combines the joint diagnostic and residual bounds with the forest, structural, encoding and message-collision bounds in the original SUF experiment.
-/

/-- `125` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signing requests per key pair. -/
theorem sphincs_has_125_bits_of_classical_security : SphincsSecurity125Statement := by
  exact Concrete.OtsProbeSimulation.Range125.security125_of_completed_joint_boundary

/-- `120` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signatures per key pair. -/
theorem sphincs_has_120_bits_of_classical_security : SphincsSecurityStatement := by
  exact Concrete.OtsProbeSimulation.security_of_completed_canonical_boundary

end SphincsSecurity
