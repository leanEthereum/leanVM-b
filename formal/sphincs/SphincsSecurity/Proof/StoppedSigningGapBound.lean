import SphincsSecurity.Proof.StoppedSigningGap
import SphincsSecurity.Proof.StoppedRemainder127

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem expectedStoppedExecutionCharge_add_remainder_gap_scaled_le_initial
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (fun _ => signingExecutionHashCost)
        ∅ Finset.univ computation frame (cache, []) hit failed +
      expectedStoppedIndexRemainder exception parameter root otsTable ftsTable q ∅ Finset.univ computation q frame (cache, []) hit failed +
      expectedStoppedSigningGap exception parameter root otsTable ftsTable q ∅ Finset.univ computation q frame (cache, []) hit failed) *
        ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤ (q : ENNReal) * initialRawIndexRate q := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hcharge := expectedStoppedExecutionCharge_add_remainder_gap_le_queryBudget exception parameter root otsTable ftsTable q hq
    ∅ Finset.univ hvalid computation q hbound frame (cache, []) hit failed hsigned hbudget
  apply (mul_le_mul' hcharge le_rfl).trans_eq
  rw [mul_assoc, cappedRawIndexCacheEnvelope_initial_scaled key q cache hnone]

theorem expectedStoppedArrival_add_executionReserve_remainder_gap_scaled_le_initial
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
      (expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (unusedTargetExecutionCost parameter)
          ∅ Finset.univ computation frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
        (expectedStoppedIndexRemainder exception parameter root otsTable ftsTable q ∅ Finset.univ computation q
            frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
          expectedStoppedSigningGap exception parameter root otsTable ftsTable q ∅ Finset.univ computation q
            frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹)) ≤
      (q : ENNReal) * initialRawIndexRate q := by
  rw [← add_assoc, ← add_assoc, ← add_mul, ← add_mul, ← add_mul, expectedStoppedIndexCharge_arrival_add_unused_execution]
  exact expectedStoppedExecutionCharge_add_remainder_gap_scaled_le_initial exception parameter root otsTable ftsTable q hq computation hbound
    frame cache hit failed hnone hbudget

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
