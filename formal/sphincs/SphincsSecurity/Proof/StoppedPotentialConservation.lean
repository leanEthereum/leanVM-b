import SphincsSecurity.Proof.PreExceptionQueryCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def exceptionDiscardCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → ENNReal) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  ∑' result, Pr[= result | (randomOracle input).run cache] *
    if queryException exception cache (.inr input) result.1 then potential result.2 else 0

theorem hashQueryCharge_exceptionDiscard_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → ENNReal) (cache : QueryCache HashSpec) (query : OracleWorld.Domain) :
    hashQueryCharge (exceptionDiscardCharge exception potential) cache query =
      ∑' result, Pr[= result | (romImpl query).run cache] *
        if queryException exception cache query result.1 then potential result.2 else 0 := by
  cases query with
  | inl sample => simp only [hashQueryCharge, Sum.elim_inl, queryException, Bool.false_eq_true, if_false, mul_zero, tsum_zero]
  | inr input => rfl

theorem expected_romImpl_stoppedPotential_add_discard
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → ENNReal) (cache : QueryCache HashSpec) (query : OracleWorld.Domain) (hit : Bool) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      (if hit || queryException exception cache query result.1 then 0 else potential result.2)) +
      (if hit then 0 else hashQueryCharge (exceptionDiscardCharge exception potential) cache query) =
      if hit then 0 else ∑' result, Pr[= result | (romImpl query).run cache] * potential result.2 := by
  cases hit with
  | true => simp
  | false =>
      simp only [Bool.false_or, Bool.false_eq_true, if_false]
      rw [hashQueryCharge_exceptionDiscard_eq, ← ENNReal.tsum_add]
      apply tsum_congr
      intro result
      rw [← mul_add]
      split_ifs <;> simp only [zero_add, add_zero]

theorem expected_stoppedPotential_add_discard_release_step
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → ENNReal)
    (release funding : QueryCache HashSpec → HashInput → ENNReal)
    (cache : QueryCache HashSpec) (query : OracleWorld.Domain) (hit : Bool)
    (hbalance : (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) + hashQueryCharge release cache query =
      potential cache + hashQueryCharge funding cache query) :
    (∑' result, Pr[= result | (romImpl query).run cache] *
      (if hit || queryException exception cache query result.1 then 0 else potential result.2)) +
      (if hit then 0 else hashQueryCharge (fun current input => release current input + exceptionDiscardCharge exception potential current input) cache query) =
      (if hit then 0 else potential cache) + (if hit then 0 else hashQueryCharge funding cache query) := by
  have hadd : hashQueryCharge (fun current input => release current input + exceptionDiscardCharge exception potential current input) cache query =
      hashQueryCharge release cache query + hashQueryCharge (exceptionDiscardCharge exception potential) cache query := by
    cases query <;> simp only [hashQueryCharge, Sum.elim_inl, Sum.elim_inr, zero_add]
  cases hit with
  | true => simp
  | false =>
      simp only [Bool.false_or, Bool.false_eq_true, if_false, hadd]
      rw [← add_assoc, add_right_comm]
      have hdiscard := expected_romImpl_stoppedPotential_add_discard exception potential cache query false
      simp only [Bool.false_or, Bool.false_eq_true, if_false] at hdiscard
      rw [hdiscard]
      exact hbalance

theorem expected_runExceptionMonitor_potential_add_preCharge_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (potential : QueryCache HashSpec → Bool → ENNReal)
    (release funding : QueryCache HashSpec → HashInput → ENNReal)
    (hstep : ∀ query cache, Finite cache → ∀ hit,
      (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2 (hit || queryException exception cache query result.1)) +
        (if hit then 0 else hashQueryCharge release cache query) = potential cache hit + (if hit then 0 else hashQueryCharge funding cache query))
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor exception computation cache hit] * potential result.1.2 result.2) +
      expectedPreExceptionCharge exception release computation cache hit =
      potential cache hit + expectedPreExceptionCharge exception funding computation cache hit := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value => simp [runExceptionMonitor]
  | query_bind query next ih =>
      rw [runExceptionMonitor, construct_query_bind, tsum_probOutput_bind_mul,
        expectedPreExceptionCharge_query_bind, expectedPreExceptionCharge_query_bind]
      calc
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            ((∑' final, Pr[= final | runExceptionMonitor exception (next result.1) result.2
                (hit || queryException exception cache query result.1)] * potential final.1.2 final.2) +
              expectedPreExceptionCharge exception release (next result.1) result.2 (hit || queryException exception cache query result.1))) +
            (if hit then 0 else hashQueryCharge release cache query) := by
          simp only [mul_add, ENNReal.tsum_add]
          ac_rfl
        _ = (∑' result, Pr[= result | (romImpl query).run cache] *
            (potential result.2 (hit || queryException exception cache query result.1) +
              expectedPreExceptionCharge exception funding (next result.1) result.2 (hit || queryException exception cache query result.1))) +
            (if hit then 0 else hashQueryCharge release cache query) := by
          congr 1
          apply tsum_congr
          intro result
          by_cases hr : result ∈ support ((romImpl query).run cache)
          · rw [ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hr)]
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [add_right_comm, hstep query cache hfinite hit, add_assoc]

end SphincsSecurity
