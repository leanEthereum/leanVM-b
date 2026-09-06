import SphincsSecurity.Proof.PreExceptionQueryCharge
import SphincsSecurity.Proof.FirstExceptionMonitor

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def firstExceptionSelectionPotential
    (selected : ExceptionRecord → Prop) (reserve : QueryCache HashSpec → ENNReal)
    (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) : ENNReal :=
  match saved with
  | none => reserve cache
  | some record => if selected record then 1 else 0

theorem expected_runFirstException_potential_le_preExceptionCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Option ExceptionRecord → ENNReal)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hstep : ∀ query cache, Finite cache → ∀ saved,
      (∑' result, Pr[= result | (romImpl query).run cache] *
        potential result.2 (retainFirstException exception saved cache query result.1)) ≤
      potential cache saved + if saved.isSome then 0 else hashQueryCharge charge cache query)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (saved : Option ExceptionRecord) :
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
          · exact mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr) _)
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
          add_le_add (hstep query cache hfinite saved) le_rfl
        _ = _ := by rw [add_assoc]

theorem probEvent_firstException_selected_le_preExceptionCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (selected : ExceptionRecord → Prop) (reserve : QueryCache HashSpec → ENNReal)
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (hstep : ∀ query cache, Finite cache →
      (∑' result, Pr[= result | (romImpl query).run cache] *
        firstExceptionSelectionPotential selected reserve result.2 (recordQueryException exception cache query result.1)) ≤
      reserve cache + hashQueryCharge charge cache query)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    Pr[fun result => ∃ record ∈ result.2, selected record | runFirstException exception computation cache none] ≤
      reserve cache + expectedPreExceptionCharge exception charge computation cache false := by
  have hbound := expected_runFirstException_potential_le_preExceptionCharge exception
    (firstExceptionSelectionPotential selected reserve) charge (fun query cache hfinite saved => by
      cases saved with
      | none => exact hstep query cache hfinite
      | some record =>
          simp only [retainFirstException, firstExceptionSelectionPotential, Option.isSome_some, if_true, add_zero]
          rw [ENNReal.tsum_mul_right, romImpl_query_mass, one_mul]) computation cache hfinite none
  apply le_trans _ hbound
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result.2 with
  | none => simp
  | some record => simp [firstExceptionSelectionPotential, mul_ite]

end SphincsSecurity
