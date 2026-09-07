import SphincsSecurity.Proof.ObservedBinomialOccupancy
import SphincsSecurity.Proof.ValidInterleavedCover
import SphincsSecurity.Proof.OccupancyBinomialExpansion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cappedLogBinomialOccupancy (key : SecretKey) (q degree : Nat) (state : CoverLogState) : ENNReal :=
  if SigningTranscript.Valid state.2 ∧ QueryCache.enncard state.1 ≤ q then
    observedLogBinomialOccupancy key degree state else 0

noncomputable def validBinomialOccupancyStepCharge (key : SecretKey) (q degree : Nat)
    (state : CoverLogState) (input : (OracleWorld + SigningSpec).Domain) : ENNReal :=
  if ValidSigningStep state.2 input ∧ QueryCache.enncard state.1 ≤ q then
    binomialOccupancyStepCharge key q degree state input else 0

theorem cappedLogBinomialOccupancy_le (key : SecretKey) (q degree : Nat) (state : CoverLogState) :
    cappedLogBinomialOccupancy key q degree state ≤ observedLogBinomialOccupancy key degree state := by
  unfold cappedLogBinomialOccupancy
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem expected_logTraced_cappedBinomialOccupancy_le (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : (OracleWorld + SigningSpec).Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedLogBinomialOccupancy key q (degree + 1) result.2) ≤
        cappedLogBinomialOccupancy key q (degree + 1) state + validBinomialOccupancyStepCharge key q degree state input := by
  by_cases hactive : ValidSigningStep state.2 input ∧ QueryCache.enncard state.1 ≤ q
  · rw [cappedLogBinomialOccupancy, if_pos ⟨hactive.1.valid_before, hactive.2⟩,
      validBinomialOccupancyStepCharge, if_pos hactive]
    apply le_trans ?_ (expected_logTraced_binomialOccupancy_le key degree q hq state hsigned hactive.2 input)
    apply ENNReal.tsum_le_tsum
    intro result
    exact mul_le_mul' le_rfl (cappedLogBinomialOccupancy_le key q (degree + 1) result.2)
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedLogBinomialOccupancy key q (degree + 1) result.2) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinactive : ¬ (SigningTranscript.Valid result.2.2 ∧ QueryCache.enncard result.2.1 ≤ q) := by
          intro hafter
          exact hactive ⟨(logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp hafter.1,
            (QueryCache.enncard_mono (logTracedMappedAdversaryImpl_cache_le key input state result hresult)).trans hafter.2⟩
        rw [cappedLogBinomialOccupancy, if_neg hinactive, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    rw [hzero]
    exact bot_le

noncomputable def expectedBinomialOccupancyCharge {α : Type} (key : SecretKey) (q degree : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => validBinomialOccupancyStepCharge key q degree state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedBinomialOccupancyCharge_pure {α : Type} (key : SecretKey) (q degree : Nat)
    (value : α) (state : CoverLogState) : expectedBinomialOccupancyCharge key q degree (pure value) state = 0 := rfl

theorem expectedBinomialOccupancyCharge_query_bind {α : Type} (key : SecretKey) (q degree : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedBinomialOccupancyCharge key q degree (OracleSpec.query input >>= next) state =
      validBinomialOccupancyStepCharge key q degree state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedBinomialOccupancyCharge key q degree (next result.1) result.2 := by
  cases input <;> rfl

theorem expected_adaptive_cappedBinomialOccupancy_le {α : Type} (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedLogBinomialOccupancy key q (degree + 1) result.2) ≤
        cappedLogBinomialOccupancy key q (degree + 1) state + expectedBinomialOccupancyCharge key q degree computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        expectedBinomialOccupancyCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedBinomialOccupancyCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            (cappedLogBinomialOccupancy key q (degree + 1) result.2 +
              expectedBinomialOccupancyCharge key q degree (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            cappedLogBinomialOccupancy key q (degree + 1) result.2) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedBinomialOccupancyCharge key q degree (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (cappedLogBinomialOccupancy key q (degree + 1) state + validBinomialOccupancyStepCharge key q degree state input) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedBinomialOccupancyCharge key q degree (next result.1) result.2 :=
          add_le_add (expected_logTraced_cappedBinomialOccupancy_le key q degree hq state hsigned input) le_rfl
        _ = _ := by rw [add_assoc]

theorem expected_adaptive_validBinomialOccupancy_from_empty_le {α : Type}
    (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogBinomialOccupancy key (degree + 1) result.2 else 0)) ≤
        expectedBinomialOccupancyCharge key q degree computation (cache, []) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hinitial : cappedLogBinomialOccupancy key q (degree + 1) (cache, []) = 0 := by
    simp only [cappedLogBinomialOccupancy, observedLogBinomialOccupancy,
      binomialOccupancyMoment_empty, Nat.cast_zero, ite_self]
  have hbound := expected_adaptive_cappedBinomialOccupancy_le key q degree hq computation (cache, []) hsigned
  rw [hinitial, zero_add] at hbound
  apply le_trans (le_of_eq ?_) hbound
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, []))
  · simp only [cappedLogBinomialOccupancy, hbudget result hresult, and_true]
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

theorem expected_adaptive_validOccupancy_from_empty_le {α : Type}
    (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤
        ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
          expectedBinomialOccupancyCharge key q degree computation (cache, []) := by
  have hexpand (state : CoverLogState) :
      (if SigningTranscript.Valid state.2 then observedLogOccupancy key state else 0) =
        ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
          (if SigningTranscript.Valid state.2 then observedLogBinomialOccupancy key (degree + 1) state else 0) := by
    by_cases hvalid : SigningTranscript.Valid state.2
    · simp only [if_pos hvalid, observedLogOccupancy, observedLogBinomialOccupancy]
      exact coverageOccupancyMoment_eq_positive_binomial _
    · simp only [if_neg hvalid, mul_zero, Finset.sum_const_zero]
  simp_rw [hexpand, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul' le_rfl (expected_adaptive_validBinomialOccupancy_from_empty_le key q degree hq computation cache hbudget)

end SphincsSecurity.Concrete
