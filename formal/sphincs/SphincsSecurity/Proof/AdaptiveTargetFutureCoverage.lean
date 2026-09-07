import SphincsSecurity.Proof.FrozenTargetFutureCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedTargetCoverageReuseCharge {α : Type} (key : SecretKey) (q : Nat)
    (payload : HashInput) (target : FewTimeView)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => targetCoverageReuseStepCharge key q payload target state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedTargetCoverageReuseCharge_pure {α : Type} (key : SecretKey) (q : Nat)
    (payload : HashInput) (target : FewTimeView) (value : α) (state : CoverLogState) :
    expectedTargetCoverageReuseCharge key q payload target (pure value) state = 0 := rfl

theorem expectedTargetCoverageReuseCharge_query_bind {α : Type} (key : SecretKey) (q : Nat)
    (payload : HashInput) (target : FewTimeView) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedTargetCoverageReuseCharge key q payload target (OracleSpec.query input >>= next) state =
      targetCoverageReuseStepCharge key q payload target state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedTargetCoverageReuseCharge key q payload target (next result.1) result.2 := by
  cases input <;> rfl

theorem expected_adaptive_frozenTargetFutureCoverage_le {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (payload : HashInput) (target : FewTimeView)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      frozenTargetFutureCoverage key q payload target result.2) ≤
      frozenTargetFutureCoverage key q payload target state + expectedTargetCoverageReuseCharge key q payload target computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        expectedTargetCoverageReuseCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedTargetCoverageReuseCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            (frozenTargetFutureCoverage key q payload target result.2 +
              expectedTargetCoverageReuseCharge key q payload target (next result.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
            frozenTargetFutureCoverage key q payload target result.2) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedTargetCoverageReuseCharge key q payload target (next result.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (frozenTargetFutureCoverage key q payload target state + targetCoverageReuseStepCharge key q payload target state input) +
              ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
                expectedTargetCoverageReuseCharge key q payload target (next result.1) result.2 :=
          add_le_add (expected_logTraced_frozenTargetFutureCoverage_le key q hq payload target state hsigned input) le_rfl
        _ = _ := by rw [add_assoc]

theorem probEvent_adaptive_targetCovered_le {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (payload : HashInput) (target : FewTimeView)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => CoveredFewTimeView
      (eligibleSigningViews (messageAnswers key.parameter result.2.1) key.root payload (result.2.2.take signatureLimit)) target |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] ≤
      frozenTargetFutureCoverage key q payload target state + expectedTargetCoverageReuseCharge key q payload target computation state := by
  apply le_trans ?_ (expected_adaptive_frozenTargetFutureCoverage_le key q hq payload target computation state hsigned)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state)
  · split_ifs with hcovered
    · rw [frozenTargetFutureCoverage, if_pos (hbudget result hresult), observedTargetFutureCoverage,
        (uncoveredFewTimeTrees_eq_empty_iff _ _).mpr hcovered, futureFewTimeCoverage_empty, mul_one]
    · exact bot_le
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    split_ifs <;> exact le_rfl

theorem probEvent_adaptive_priorCacheCovered_le {α : Type} (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CoverLogState) (hfinite : Finite state.1)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => ∃ input ∈ cachedAdmissibleMessageInputs key.parameter state.1 hfinite,
      CoveredFewTimeView
        (eligibleSigningViews (messageAnswers key.parameter result.2.1) key.root (payloadOf input) (result.2.2.take signatureLimit))
        (cachedFewTimeView state.1 input) |
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] ≤
      ∑ input ∈ cachedAdmissibleMessageInputs key.parameter state.1 hfinite,
        (frozenTargetFutureCoverage key q (payloadOf input) (cachedFewTimeView state.1 input) state +
          expectedTargetCoverageReuseCharge key q (payloadOf input) (cachedFewTimeView state.1 input) computation state) := by
  apply (probEvent_exists_finset_le_sum _ _ _).trans
  exact Finset.sum_le_sum (fun input _ =>
    probEvent_adaptive_targetCovered_le key q hq (payloadOf input) (cachedFewTimeView state.1 input) computation state hsigned hbudget)

end SphincsSecurity.Concrete
