import SphincsSecurity.Proof.ObservedCompletion
import SphincsSecurity.Proof.OccupancyBinomialExpansion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedCompletionReuseCharge {α : Type} (key : SecretKey) (q degree : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => completionReuseStepCharge key q degree state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedCompletionReuseCharge_pure {α : Type} (key : SecretKey) (q degree : Nat)
    (value : α) (state : CoverLogState) : expectedCompletionReuseCharge key q degree (pure value) state = 0 := rfl

theorem expectedCompletionReuseCharge_query_bind {α : Type} (key : SecretKey) (q degree : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedCompletionReuseCharge key q degree (OracleSpec.query input >>= next) state =
      completionReuseStepCharge key q degree state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedCompletionReuseCharge key q degree (next result.1) result.2 := by
  cases input <;> rfl

theorem expected_adaptive_cappedCompletion_le {α : Type} (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedLogCompletion key q degree result.2) ≤
        cappedLogCompletion key q degree state + expectedCompletionReuseCharge key q degree computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        expectedCompletionReuseCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCompletionReuseCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            (cappedLogCompletion key q degree result.2 +
              expectedCompletionReuseCharge key q degree (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            cappedLogCompletion key q degree result.2) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedCompletionReuseCharge key q degree (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (cappedLogCompletion key q degree state + completionReuseStepCharge key q degree state input) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedCompletionReuseCharge key q degree (next result.1) result.2 :=
          add_le_add (expected_logTraced_cappedCompletion_le key q degree hq state hsigned input) le_rfl
        _ = _ := by rw [add_assoc]

theorem cappedLogCompletion_empty_le (key : SecretKey) (q degree : Nat) (cache : QueryCache HashSpec) :
    cappedLogCompletion key q degree (cache, []) ≤
      (signatureLimit.choose degree : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ^ degree * (Fintype.card Index : ENNReal) := by
  have hempty : (fun degree => observedLogBinomialOccupancy key degree (cache, [])) =
      (fun degree => if degree = 0 then (Fintype.card Index : ENNReal) else 0) := by
    funext degree
    cases degree with
    | zero => simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_zero, if_true]
    | succ degree => simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_empty,
        Nat.cast_zero, Nat.succ_ne_zero, if_false]
  unfold cappedLogCompletion
  split_ifs
  · rw [hempty, List.length_nil, Nat.sub_zero, binomialCompletion_empty]
  · exact bot_le

theorem expected_adaptive_validBinomial_le_uniform_add_reuse {α : Type}
    (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogBinomialOccupancy key degree result.2 else 0)) ≤
        (signatureLimit.choose degree : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ^ degree * (Fintype.card Index : ENNReal) +
          expectedCompletionReuseCharge key q degree computation (cache, []) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  apply le_trans ?_ ((expected_adaptive_cappedCompletion_le key q degree hq computation (cache, []) hsigned).trans
    (add_le_add (cappedLogCompletion_empty_le key q degree cache) le_rfl))
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, []))
  · apply mul_le_mul' le_rfl
    simp only [cappedLogCompletion, hbudget result hresult, and_true]
    split_ifs
    · exact le_binomialCompletion (fun d => observedLogBinomialOccupancy key d result.2)
        (signatureLimit - result.2.2.length) degree
    · exact le_rfl
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

noncomputable def uniformCoverageCompletion (remaining : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
    ((remaining.choose (degree + 1) : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ^ (degree + 1) * (Fintype.card Index : ENNReal))

theorem expected_adaptive_validOccupancy_le_uniform_add_reuse {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤
        uniformCoverageCompletion signatureLimit +
          ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
            expectedCompletionReuseCharge key q (degree + 1) computation (cache, []) := by
  have hexpand (state : CoverLogState) :
      (if SigningTranscript.Valid state.2 then observedLogOccupancy key state else 0) =
        ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
          (if SigningTranscript.Valid state.2 then observedLogBinomialOccupancy key (degree + 1) state else 0) := by
    by_cases hvalid : SigningTranscript.Valid state.2
    · simp only [if_pos hvalid, observedLogOccupancy, observedLogBinomialOccupancy]
      exact coverageOccupancyMoment_eq_positive_binomial _
    · simp only [if_neg hvalid, mul_zero, Finset.sum_const_zero]
  simp_rw [hexpand, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), uniformCoverageCompletion, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, ← mul_add]
  exact mul_le_mul' le_rfl (expected_adaptive_validBinomial_le_uniform_add_reuse key q (degree + 1) hq computation cache hbudget)

end SphincsSecurity.Concrete
