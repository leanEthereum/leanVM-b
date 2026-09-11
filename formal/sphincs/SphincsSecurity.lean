import SphincsSecurity.Statement
import SphincsSecurity.Proof

namespace SphincsSecurity

/-!
The public security theorems for the statements in `SphincsSecurity.Statement`. The 127-bit proof splits the whole-experiment hash budget at `3 * 2^114`: larger budgets are bounded by the retained residual certificate monitor, and smaller budgets reduce the remaining near-certificate event to forced FTS guess games that are monitored and bounded slot by slot. The weaker statements follow from it.
-/

/-- `127` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signing requests per key pair. -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurity127Statement :=
  Concrete.security127

/-- `126` bits of classical strong unforgeability, a consequence of the `127`-bit theorem. -/
theorem sphincs_has_126_bits_of_classical_security : SphincsSecurity126Statement := by
  intro q hq adversary hbound
  apply (sphincs_has_127_bits_of_classical_security q hq adversary hbound).trans
  gcongr <;> norm_num

/-- `125` bits of classical strong unforgeability, a consequence of the `127`-bit theorem. -/
theorem sphincs_has_125_bits_of_classical_security : SphincsSecurity125Statement := by
  intro q hq adversary hbound
  apply (sphincs_has_127_bits_of_classical_security q hq adversary hbound).trans
  gcongr <;> norm_num

/-- `120` bits of classical strong unforgeability, a consequence of the `127`-bit theorem. -/
theorem sphincs_has_120_bits_of_classical_security : SphincsSecurityStatement := by
  intro q hq adversary hbound
  apply (sphincs_has_127_bits_of_classical_security q hq adversary hbound).trans
  gcongr <;> norm_num [securityBits]

end SphincsSecurity
