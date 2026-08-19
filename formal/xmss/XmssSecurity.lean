import XmssSecurity.Statement
import XmssSecurity.Proof

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-!
The main result. Its statement lives entirely in `XmssSecurity.Statement` and the `XmssSecurity/Statement/` directory; the modules under `XmssSecurity/Proof/` only contribute to the proof.
-/

/-- The concrete XMSS instance has 127 bits of classical security in the random-oracle model. -/
theorem xmss_has_127_bits_of_classical_security :
    ∀ q, 1 ≤ q → xmssForgeAtMost q ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  intro q hq
  unfold xmssForgeAtMost
  refine iSup_le fun adversary => iSup_le fun hbound => ?_
  let internalAdversary : Adversary Concrete.scheme := ⟨adversary.main⟩
  have internalBound :
      HasHashQueryBound Concrete.scheme internalAdversary q := by
    exact hbound
  calc
    xmssForgeAdvantage adversary =
        forgeAdvantage Concrete.scheme internalAdversary := rfl
    _ ≤ forgeAtMost Concrete.scheme q :=
      le_iSup_of_le internalAdversary
        (le_iSup_of_le internalBound le_rfl)
    _ ≤ (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) :=
      Proof.concreteScheme_has_127_bits_of_classical_security q hq

theorem xmssSecurityStatement_holds : XmssSecurityStatement :=
  xmss_has_127_bits_of_classical_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'XmssSecurity.xmss_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xmss_has_127_bits_of_classical_security

/-- info: 'XmssSecurity.xmssSecurityStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xmssSecurityStatement_holds

end XmssSecurity
