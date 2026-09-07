import SphincsSecurity.Proof.JointProbeOriginalBeforeFailureCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expectedPreExceptionCharge_mono_of_finite
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal)
    (hle : ∀ cache, Finite cache → ∀ input, left cache input ≤ right cache input)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    expectedPreExceptionCharge exception left computation cache hit ≤ expectedPreExceptionCharge exception right computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp
  | query_bind query next ih =>
      rw [expectedPreExceptionCharge_query_bind, expectedPreExceptionCharge_query_bind]
      apply add_le_add
      · cases hit with
        | true => simp
        | false =>
            cases query with
            | inl sample => exact le_rfl
            | inr input => exact hle cache hfinite input
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((romImpl query).run cache)
        · exact mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr) _)
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

namespace Concrete.FtsProbeSimulation.JointOriginal

theorem expectedBeforeFailureCharge_mono_of_finite
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal)
    (hle : ∀ cache, Finite cache → ∀ input, left cache input ≤ right cache input)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) :
    expectedBeforeFailureCharge exception left parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureCharge exception right parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureCharge_query_bind, expectedBeforeFailureCharge_query_bind]
      apply add_le_add
      · cases failed with
        | true => simp
        | false => exact expectedPreExceptionCharge_mono_of_finite exception left right hle _ cache hfinite hit
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)
        · have hm := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hr
          have hf := finite_cache_of_mem_support _ cache result.1.2.1.1 result.1.2.1.2
            (runExceptionMonitor_support_project exception _ cache hit hm) hfinite
          exact mul_le_mul' le_rfl (ih result.1.2.1.1 result.1.1 result.1.2.1.2 hf result.1.2.2 result.2)
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end Concrete.FtsProbeSimulation.JointOriginal
end SphincsSecurity
