import XmssSecurity.Statement
import XmssSecurity.Proof

namespace XmssSecurity

/-!
The main result. Its statement lives entirely in the single module `XmssSecurity.Statement`; the modules under `XmssSecurity/Proof/` only contribute to the proof.
-/

/-- The concrete XMSS instance has 127 bits of classical security in the random-oracle model. -/
theorem xmss_has_127_bits_of_classical_security : XmssSecurityStatement :=
  Proof.concreteScheme_has_127_bits_of_classical_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'XmssSecurity.xmss_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xmss_has_127_bits_of_classical_security

end XmssSecurity
