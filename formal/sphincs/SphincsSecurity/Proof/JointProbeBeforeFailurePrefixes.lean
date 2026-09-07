import SphincsSecurity.Proof.QueryOccurrencePrefix
import SphincsSecurity.Proof.JointProbeBeforeFailureNonSecretBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liveQueryPrefixProbability
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (select : (OracleWorld + SigningSpec).Domain → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) : ENNReal :=
  Pr[fun result => result.1.2.1.1 = true ∧ result.1.2.2 = false ∧ result.2 = false |
    runWithFailure exception parameter root otsTable ftsTable (beforeQueryOccurrence select computation ordinal) frame cache hit failed]

@[simp] theorem liveQueryPrefixProbability_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (select : (OracleWorld + SigningSpec).Domain → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (value : α) (ordinal : Nat) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    liveQueryPrefixProbability exception select parameter root otsTable ftsTable (pure value) ordinal frame cache hit failed = 0 := by
  simp [liveQueryPrefixProbability, runWithFailure_pure]

theorem liveQueryPrefixProbability_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (select : (OracleWorld + SigningSpec).Domain → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (ordinal : Nat) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    liveQueryPrefixProbability exception select parameter root otsTable ftsTable (OracleSpec.query input >>= next) ordinal frame cache hit failed =
      if select input then
        match ordinal with
        | 0 => if hit || failed then 0 else 1
        | ordinal + 1 => ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
            liveQueryPrefixProbability exception select parameter root otsTable ftsTable (next result.1.2.1.1) ordinal
              result.1.1 result.1.2.1.2 result.1.2.2 result.2
      else ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          liveQueryPrefixProbability exception select parameter root otsTable ftsTable (next result.1.2.1.1) ordinal
            result.1.1 result.1.2.1.2 result.1.2.2 result.2 := by
  unfold liveQueryPrefixProbability
  rw [beforeQueryOccurrence_query_bind]
  by_cases hs : select input
  · rw [if_pos hs, if_pos hs]
    cases ordinal with
    | zero => cases hit <;> cases failed <;> simp [runWithFailure_pure]
    | succ ordinal => rw [runWithFailure_query_bind, probEvent_bind_eq_tsum]
  · rw [if_neg hs, if_neg hs, runWithFailure_query_bind, probEvent_bind_eq_tsum]

theorem tsum_liveQueryPrefixProbability_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (select : (OracleWorld + SigningSpec).Domain → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (∑' ordinal, liveQueryPrefixProbability exception select parameter root otsTable ftsTable
      (OracleSpec.query input >>= next) ordinal frame cache hit failed) =
      (if hit || failed then 0 else if select input then 1 else 0) +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
          ∑' ordinal, liveQueryPrefixProbability exception select parameter root otsTable ftsTable (next result.1.2.1.1) ordinal
            result.1.1 result.1.2.1.2 result.1.2.2 result.2 := by
  by_cases hs : select input
  · rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [liveQueryPrefixProbability_query_bind, if_pos hs]
    congr 1
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left]
  · simp only [liveQueryPrefixProbability_query_bind, if_neg hs, ite_self, zero_add]
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left]

def IsSelectedOuterHash (select : HashInput → Prop) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr input) => select input
  | _ => False

theorem expectedBeforeFailureOuterCharge_eq_prefixSum
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (select : HashInput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureOuterCharge exception (fun _ input => if select input then 1 else 0)
        parameter root otsTable ftsTable computation frame cache hit failed =
      ∑' ordinal, liveQueryPrefixProbability exception (IsSelectedOuterHash select) parameter root otsTable ftsTable computation ordinal
        frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureOuterCharge_query_bind, tsum_liveQueryPrefixProbability_query_bind]
      simp_rw [ih]
      congr 1
      have hc : outerHashQueryCharge (fun _ input => if select input then (1 : ENNReal) else 0) input cache =
          if IsSelectedOuterHash select input then 1 else 0 := by
        cases input with
        | inl query => cases query <;> simp [outerHashQueryCharge, hashQueryCharge, IsSelectedOuterHash]
        | inr message => simp [outerHashQueryCharge, IsSelectedOuterHash]
      rw [hc]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
