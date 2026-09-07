import SphincsSecurity.Proof.StoppedBudgetRemainder

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev expectedStoppedIndexRemainder
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  expectedStoppedBudgetRemainder exception
    (fun current => cappedRawIndexCacheEnvelope (secretKey parameter root otsTable ftsTable) cap current groups remaining)
    parameter root otsTable ftsTable computation budget frame state hit failed

theorem expectedStoppedExecutionCharge_add_remainder_scaled_le_127
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
      expectedStoppedIndexRemainder exception parameter root otsTable ftsTable q ∅ Finset.univ computation q frame (cache, []) hit failed) *
        ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  let key := secretKey parameter root otsTable ftsTable
  have hsigned : SigningDigestsCached parameter cache root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hcharge := expectedStoppedExecutionCharge_add_remainder_le_queryBudget exception parameter root otsTable ftsTable q hq
    ∅ Finset.univ hvalid computation q hbound frame (cache, []) hit failed hsigned hbudget
  have hcache := simulateQ_logTraced_initial_cache_bound key q computation (cache, []) hbudget
  have hpure : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) (pure () : OracleComp (OracleWorld + SigningSpec) Unit)).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q := by
    intro result hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst result
    exact hcache
  have hinitial := expected_adaptive_cappedRawIndex_full_scaled_le_127 key q hq (pure ()) cache hnone hpure
  simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul] at hinitial
  apply (mul_le_mul' hcharge le_rfl).trans
  rw [mul_assoc]
  exact mul_le_mul' le_rfl hinitial

theorem expectedStoppedArrival_add_executionReserve_remainder_scaled_le_127
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
        expectedStoppedIndexRemainder exception parameter root otsTable ftsTable q ∅ Finset.univ computation q
          frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹) ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  rw [← add_assoc, ← add_mul, ← add_mul, expectedStoppedIndexCharge_arrival_add_unused_execution]
  exact expectedStoppedExecutionCharge_add_remainder_scaled_le_127 exception parameter root otsTable ftsTable q hq computation hbound
    frame cache hit failed hnone hbudget

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
