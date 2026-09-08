import SphincsSecurity.Proof.FirstExceptionStoppedCharge
import SphincsSecurity.Proof.CacheEntryExceptionInvariant

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expected_runFirstException_potential_le_preCharge_of_detects
    (Bad : QueryCache HashSpec → Prop)
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (hdetect : ∀ cache input answer, Bad (cache.cacheQuery input answer) → exception cache input answer)
    (potential : QueryCache HashSpec → Option ExceptionRecord → ENNReal)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hstep : ∀ query cache, Finite cache → ∀ saved,
      (saved.isSome = false → ¬ Bad cache) →
      (∑' result, Pr[= result | (romImpl query).run cache] *
        potential result.2 (retainFirstException exception saved cache query result.1)) ≤
      potential cache saved + if saved.isSome then 0 else hashQueryCharge charge cache query)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (saved : Option ExceptionRecord) (hclean : saved.isSome = false → ¬ Bad cache) :
    (∑' result, Pr[= result | runFirstException exception computation cache saved] * potential result.1.2 result.2) ≤
      potential cache saved + expectedPreExceptionCharge exception charge computation cache saved.isSome := by
  induction computation using OracleComp.inductionOn generalizing cache saved with
  | pure value => simp [runFirstException]
  | query_bind query next ih =>
      rw [runFirstException, construct_query_bind, tsum_probOutput_bind_mul, expectedPreExceptionCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (potential result.2 (retainFirstException exception saved cache query result.1) +
              expectedPreExceptionCharge exception charge (next result.1) result.2
                (retainFirstException exception saved cache query result.1).isSome) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support ((romImpl query).run cache)
          · apply mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr) _ ?_)
            intro hnone
            rw [retainFirstException_isSome] at hnone
            exact detectingException_query_clean Bad exception hdetect query cache saved.isSome hclean result hr hnone
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            potential result.2 (retainFirstException exception saved cache query result.1)) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedPreExceptionCharge exception charge (next result.1) result.2
                (saved.isSome || queryException exception cache query result.1) := by
          simp_rw [mul_add, ENNReal.tsum_add, retainFirstException_isSome]
        _ ≤ (potential cache saved + if saved.isSome then 0 else hashQueryCharge charge cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedPreExceptionCharge exception charge (next result.1) result.2
                (saved.isSome || queryException exception cache query result.1) :=
          add_le_add (hstep query cache hfinite saved hclean) le_rfl
        _ = _ := by rw [add_assoc]

end SphincsSecurity
