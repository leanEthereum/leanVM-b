import SphincsSecurity.Proof.PreExceptionChargeComparison
import SphincsSecurity.Proof.WorldPairReserve

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem expectedPreExceptionCharge_mono_of_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal) (cap : Nat)
    (hle : ∀ current, Finite current → QueryCache.enncard current ≤ cap → ∀ input, left current input ≤ right current input)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedPreExceptionCharge exception left computation cache hit ≤
      expectedPreExceptionCharge exception right computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp
  | query_bind query next ih =>
      have hbefore := Concrete.simulateQ_romImpl_initial_cache_bound cap (OracleSpec.query query >>= next) cache hcap
      rw [expectedPreExceptionCharge_query_bind, expectedPreExceptionCharge_query_bind]
      apply add_le_add
      · cases hit with
        | true => simp
        | false =>
            cases query with
            | inl sample => exact le_rfl
            | inr input => exact hle cache hfinite hbefore input
      · apply ENNReal.tsum_le_tsum
        intro middle
        by_cases hm : middle ∈ support ((romImpl query).run cache)
        · apply mul_le_mul' le_rfl
          apply ih middle.1 middle.2 (finite_of_mem_support_romImpl hfinite hm)
          intro result hr
          apply hcap result
          rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
          exact ⟨middle, hm, hr⟩
        · rw [probOutput_eq_zero_of_not_mem_support hm, zero_mul, zero_mul]

end SphincsSecurity
