import SphincsSecurity.Proof.FrozenCompletion
import SphincsSecurity.Proof.UniformCompletionBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_adaptive_frozenCompletion_le {α : Type} (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      frozenLogCompletion key q degree result.2) ≤
        frozenLogCompletion key q degree state + expectedCompletionReuseCharge key q degree computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        expectedCompletionReuseCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCompletionReuseCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            (frozenLogCompletion key q degree result.2 +
              expectedCompletionReuseCharge key q degree (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            frozenLogCompletion key q degree result.2) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedCompletionReuseCharge key q degree (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (frozenLogCompletion key q degree state + completionReuseStepCharge key q degree state input) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedCompletionReuseCharge key q degree (next result.1) result.2 :=
          add_le_add (expected_logTraced_frozenCompletion_le key q degree hq state hsigned input) le_rfl
        _ = _ := by rw [add_assoc]

theorem expected_adaptive_frozenBinomial_le_uniform_add_reuse {α : Type}
    (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      frozenLogBinomialOccupancy key degree result.2) ≤
        (signatureLimit.choose degree : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ^ degree * (Fintype.card Index : ENNReal) +
          expectedCompletionReuseCharge key q degree computation (cache, []) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hinitial : frozenLogCompletion key q degree (cache, []) ≤
      (signatureLimit.choose degree : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ^ degree * (Fintype.card Index : ENNReal) := by
    rw [frozenLogCompletion_of_valid key q degree (cache, []) (by exact Nat.zero_le _)]
    exact cappedLogCompletion_empty_le key q degree cache
  apply le_trans ?_ ((expected_adaptive_frozenCompletion_le key q degree hq computation (cache, []) hsigned).trans
    (add_le_add hinitial le_rfl))
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, []))
  · apply mul_le_mul' le_rfl
    rw [frozenLogCompletion, if_pos (hbudget result hresult)]
    exact le_binomialCompletion (fun d => frozenLogBinomialOccupancy key d result.2)
      (signatureLimit - result.2.2.length) degree
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

theorem expected_adaptive_frozenOccupancy_le_seven_add_reuse {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      frozenLogOccupancy key result.2) ≤
        7 * (2 : ENNReal) ^ 40 +
          ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
            expectedCompletionReuseCharge key q (degree + 1) computation (cache, []) := by
  apply le_trans ?_ (add_le_add uniformCoverageCompletion_signatureLimit_le le_rfl)
  simp_rw [frozenLogOccupancy_eq_binomial, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), uniformCoverageCompletion, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, ← mul_add]
  exact mul_le_mul' le_rfl (expected_adaptive_frozenBinomial_le_uniform_add_reuse key q (degree + 1) hq computation cache hbudget)

end SphincsSecurity.Concrete
