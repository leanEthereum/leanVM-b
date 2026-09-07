import SphincsSecurity.Proof.CappedCachedFutureCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedFutureCacheCharge {α : Type} (key : SecretKey) (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => futureCacheStepCharge key q state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedFutureCacheCharge_pure {α : Type} (key : SecretKey) (q : Nat)
    (value : α) (state : CoverLogState) : expectedFutureCacheCharge key q (pure value) state = 0 := rfl

theorem expectedFutureCacheCharge_query_bind {α : Type} (key : SecretKey) (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedFutureCacheCharge key q (OracleSpec.query input >>= next) state =
      futureCacheStepCharge key q state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedFutureCacheCharge key q (next result.1) result.2 := by
  cases input <;> rfl

theorem expected_adaptive_cappedCachedFutureCoverage_le {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedCachedFutureCoverage key q result.2) ≤
      cappedCachedFutureCoverage key q state + expectedFutureCacheCharge key q computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        expectedFutureCacheCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedFutureCacheCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            (cappedCachedFutureCoverage key q result.2 + expectedFutureCacheCharge key q (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            cappedCachedFutureCoverage key q result.2) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedFutureCacheCharge key q (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (cappedCachedFutureCoverage key q state + futureCacheStepCharge key q state input) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedFutureCacheCharge key q (next result.1) result.2 :=
          add_le_add (expected_logTraced_cappedCachedFutureCoverage_le key q hq state hsigned input) le_rfl
        _ = _ := by rw [add_assoc]

theorem probEvent_adaptive_validCacheCovered_le {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧ SigningCacheCovered key.parameter key.root result.2.1 result.2.2 |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] ≤
      cappedCachedFutureCoverage key q state + expectedFutureCacheCharge key q computation state := by
  apply le_trans ?_ (expected_adaptive_cappedCachedFutureCoverage_le key q hq computation state hsigned)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state)
  · split_ifs with hcovered
    · rw [cappedCachedFutureCoverage, if_pos ⟨hcovered.1, hbudget result hresult⟩]
      exact le_mul_of_one_le_right' (one_le_cachedFutureCoverage_of_covered _ _ _ _ _ hcovered.2)
    · exact bot_le
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    split_ifs <;> exact le_rfl

theorem probEvent_adaptive_validObservedCover_le_futureCharge {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (forgery : α → Forgery)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => SigningTranscript.Valid result.2.2 ∧
      ObservedFewTimeCover (messageAnswers key.parameter result.2.1) key.root result.2.2 (forgery result.1) |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] ≤
      expectedFutureCacheCharge key q computation (cache, []) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hzero : cappedCachedFutureCoverage key q (cache, []) = 0 := by
    unfold cappedCachedFutureCoverage
    split_ifs
    · exact cachedFutureCoverage_of_no_message _ _ _ _ _ hnone
    · rfl
  have hbound := probEvent_adaptive_validCacheCovered_le key q hq computation (cache, []) hsigned hbudget
  rw [hzero, zero_add] at hbound
  apply le_trans ?_ hbound
  apply probEvent_mono
  intro result _ hcover
  exact ⟨hcover.1, observedFewTimeCover_signingCacheCovered _ _ _ _ _ hcover.2⟩

end SphincsSecurity.Concrete
