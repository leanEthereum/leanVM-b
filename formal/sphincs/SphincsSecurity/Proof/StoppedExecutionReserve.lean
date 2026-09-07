import SphincsSecurity.Proof.SigningExecutionIndexBudget
import SphincsSecurity.Proof.StoppedTargetCoverage127

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def unusedTargetExecutionCost (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) : Nat :=
  unusedTargetHashCost parameter cache input + unusedSigningExecutionCost input

theorem targetArrivalHashCost_add_unused_execution (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    targetArrivalHashCost parameter cache input + unusedTargetExecutionCost parameter cache input = signingExecutionHashCost input := by
  rw [unusedTargetExecutionCost, ← Nat.add_assoc, targetArrivalHashCost_add_unused, signingMacroHashCost_add_unused_execution]

theorem expectedStoppedIndexCharge_arrival_add_unused_execution
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
        groups remaining computation frame state hit failed +
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (unusedTargetExecutionCost parameter)
        groups remaining computation frame state hit failed =
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (fun _ => signingExecutionHashCost)
        groups remaining computation frame state hit failed := by
  simp only [expectedStoppedIndexCharge]
  rw [← expectedStoppedLogCharge_add]
  simp_rw [← add_mul, ← Nat.cast_add, targetArrivalHashCost_add_unused_execution]

theorem expectedStoppedIndexCharge_execution_full_scaled_le_127
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (fun _ => signingExecutionHashCost)
      ∅ Finset.univ computation frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply (mul_le_mul' (expectedStoppedIndexCharge_le_unstopped exception parameter root otsTable ftsTable q
    (fun _ => signingExecutionHashCost) ∅ Finset.univ computation frame (cache, []) hit failed) le_rfl).trans
  exact expectedSigningExecutionIndexCharge_full_scaled_le_127 (secretKey parameter root otsTable ftsTable) q hq
    computation hbound cache hnone hbudget

theorem expectedStoppedIndexCharge_arrival_add_unused_execution_scaled_le_127
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter)
        ∅ Finset.univ computation frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (unusedTargetExecutionCost parameter)
        ∅ Finset.univ computation frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  rw [← add_mul, expectedStoppedIndexCharge_arrival_add_unused_execution]
  exact expectedStoppedIndexCharge_execution_full_scaled_le_127 exception parameter root otsTable ftsTable q hq computation hbound
    frame cache hit failed hnone hbudget

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
