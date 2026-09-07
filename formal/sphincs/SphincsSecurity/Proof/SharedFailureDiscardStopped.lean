import SphincsSecurity.Proof.JointFailurePotentialConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem stepWithFailure_hit_of_hit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (failed : Bool)
    (result) (hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache true failed)) :
    result.1.2.2 = true := by
  have hm := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache true failed result hr
  rw [runExceptionMonitor_true, support_map] at hm
  obtain ⟨_, _, heq⟩ := hm
  exact (congrArg Prod.snd heq).symm

theorem expectedSharedFailureDiscard_failed_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedSharedFailureDiscard exception potential parameter root otsTable ftsTable computation frame cache hit true = 0 := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedSharedFailureDiscard_query_bind, sharedFailureDiscardStep]
      simp only [if_true, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit true)
      · rw [stepWithFailure_failed exception parameter root otsTable ftsTable input frame cache hit result hr, ih, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expectedSharedFailureDiscard_hit_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal) (hz : ∀ cache, potential cache true = 0)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (failed : Bool) :
    expectedSharedFailureDiscard exception potential parameter root otsTable ftsTable computation frame cache true failed = 0 := by
  induction computation using OracleComp.inductionOn generalizing frame cache failed with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedSharedFailureDiscard_query_bind]
      have hhead : sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache true failed = 0 := by
        rw [sharedFailureDiscardStep]
        split_ifs
        · rfl
        · apply ENNReal.tsum_eq_zero.mpr
          intro result
          by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache true failed)
          · rw [stepWithFailure_hit_of_hit exception parameter root otsTable ftsTable input frame cache failed result hr, hz]
            simp only [ite_self, mul_zero]
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
      rw [hhead, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache true failed)
      · rw [stepWithFailure_hit_of_hit exception parameter root otsTable ftsTable input frame cache failed result hr, ih, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
