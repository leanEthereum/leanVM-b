import SphincsSecurity.Proof.AmortizedStoppedCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- Charge up to and including the first exception query. The monitored execution is unchanged. -/
noncomputable def expectedPreExceptionCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) : QueryCache HashSpec → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ => 0)
    (fun query _ next cache hit =>
      (if hit then 0 else hashQueryCharge charge cache query) +
        ∑' result, Pr[= result | (romImpl query).run cache] *
          next result.1 result.2 (hit || queryException exception cache query result.1)) computation

@[simp] theorem expectedPreExceptionCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (value : α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge (pure value) cache hit = 0 := rfl

theorem expectedPreExceptionCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (query : OracleWorld.Domain) (next : OracleWorld.Range query → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge (OracleSpec.query query >>= next) cache hit =
      (if hit then 0 else hashQueryCharge charge cache query) +
        ∑' result, Pr[= result | (romImpl query).run cache] *
          expectedPreExceptionCharge exception charge (next result.1) result.2
            (hit || queryException exception cache query result.1) := by
  cases query <;> rfl

@[simp] theorem expectedPreExceptionCharge_true
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedPreExceptionCharge exception charge computation cache true = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind query next ih => simp [expectedPreExceptionCharge_query_bind, ih]

theorem expectedPreExceptionCharge_add
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (fun cache input => left cache input + right cache input) computation cache hit =
      expectedPreExceptionCharge exception left computation cache hit +
        expectedPreExceptionCharge exception right computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp
  | query_bind query next ih =>
      simp only [expectedPreExceptionCharge_query_bind, ih, mul_add, ENNReal.tsum_add]
      cases hit <;> cases query <;> simp only [hashQueryCharge, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
        if_false, if_true, zero_add] <;> ac_rfl

theorem expectedPreExceptionCharge_mul
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (factor : ENNReal)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (fun cache input => charge cache input * factor) computation cache hit =
      expectedPreExceptionCharge exception charge computation cache hit * factor := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp
  | query_bind query next ih =>
      simp only [expectedPreExceptionCharge_query_bind, ih, add_mul, ← mul_assoc, ENNReal.tsum_mul_right]
      congr 1
      cases hit <;> cases query <;> simp [hashQueryCharge]

theorem expectedPreExceptionCharge_le_queryCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge computation cache hit ≤ expectedQueryCharge charge computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => rfl
  | query_bind query next ih =>
      rw [expectedPreExceptionCharge_query_bind, expectedQueryCharge_query_bind]
      apply add_le_add
      · cases hit <;> simp
      · exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2 _)

theorem expectedPreExceptionCharge_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge (computation >>= next) cache hit =
      expectedPreExceptionCharge exception charge computation cache hit +
        ∑' result, Pr[= result | runExceptionMonitor exception computation cache hit] *
          expectedPreExceptionCharge exception charge (next result.1.1) result.1.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind query continuation ih =>
      rw [bind_assoc, expectedPreExceptionCharge_query_bind, expectedPreExceptionCharge_query_bind,
        runExceptionMonitor, construct_query_bind, tsum_probOutput_bind_mul]
      simp_rw [ih, mul_add, ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      rw [add_assoc]
      rfl

theorem expectedPreExceptionCharge_map
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp OracleWorld α) (f : α → β) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception charge (f <$> computation) cache hit =
      expectedPreExceptionCharge exception charge computation cache hit := by
  rw [← bind_pure_comp, expectedPreExceptionCharge_bind]
  simp only [Function.comp_apply, expectedPreExceptionCharge_pure, mul_zero, tsum_zero, add_zero]

theorem expected_runExceptionMonitor_potential_le_preExceptionCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hstep : ∀ query cache, Finite cache → ∀ hit,
      (∑' result, Pr[= result | (romImpl query).run cache] *
        potential result.2 (hit || queryException exception cache query result.1)) ≤
      potential cache hit + if hit then 0 else hashQueryCharge charge cache query)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor exception computation cache hit] * potential result.1.2 result.2) ≤
      potential cache hit + expectedPreExceptionCharge exception charge computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind query next ih =>
      rw [runExceptionMonitor, construct_query_bind, tsum_probOutput_bind_mul, expectedPreExceptionCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (romImpl query).run cache] *
            (potential result.2 (hit || queryException exception cache query result.1) +
              expectedPreExceptionCharge exception charge (next result.1) result.2
                (hit || queryException exception cache query result.1)) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support ((romImpl query).run cache)
          · exact mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr) _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            potential result.2 (hit || queryException exception cache query result.1)) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedPreExceptionCharge exception charge (next result.1) result.2
                (hit || queryException exception cache query result.1) := by
          simp_rw [mul_add, ENNReal.tsum_add]
        _ ≤ (potential cache hit + if hit then 0 else hashQueryCharge charge cache query) +
            ∑' result, Pr[= result | (romImpl query).run cache] *
              expectedPreExceptionCharge exception charge (next result.1) result.2
                (hit || queryException exception cache query result.1) :=
          add_le_add (hstep query cache hfinite hit) le_rfl
        _ = _ := by rw [add_assoc]

end SphincsSecurity
