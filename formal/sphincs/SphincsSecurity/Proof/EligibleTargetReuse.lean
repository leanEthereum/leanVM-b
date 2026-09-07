import SphincsSecurity.Proof.SignerInputWeight
import SphincsSecurity.Proof.ObservedFutureCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetCoverageInputIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (input : HashInput) (source : FewTimeView) : ENNReal :=
  if input = tweakableHashInput key.parameter .message payload then 0 else
    futureFewTimeCoverageIncrement remaining
      (uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) target) target source

theorem targetCoverageInputIncrement_self (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView) :
    targetCoverageInputIncrement remaining key before log payload target (tweakableHashInput key.parameter .message payload) source = 0 := by
  simp only [targetCoverageInputIncrement, if_true]

theorem targetCoverageInputIncrement_of_ne (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView)
    (input : HashInput) (hne : input ≠ tweakableHashInput key.parameter .message payload) :
    targetCoverageInputIncrement remaining key before log payload target input source =
      futureFewTimeCoverageIncrement remaining
        (uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) target) target source := by
  exact if_neg hne

theorem targetCoverageInputIncrement_cache_stable (remaining : Nat) (key : SecretKey)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView)
    (input : HashInput) (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    targetCoverageInputIncrement remaining key after log payload target input source =
      targetCoverageInputIncrement remaining key before log payload target input source := by
  have hstable : eligibleSigningViews (messageAnswers key.parameter after) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root payload log := by
    funext slot
    exact eligibleSigningView?_cache_stable key.parameter key.root before after hcache payload (log.get slot)
      (hsigned _ (List.get_mem _ _))
  simp only [targetCoverageInputIncrement, hstable]

theorem signWithView_observedTargetFutureCoverage_le_input (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    observedTargetFutureCoverage remaining key.parameter key.root payload target result.2
      (log ++ [⟨message, result.1.1⟩]) ≤
      observedTargetFutureCoverage remaining key.parameter key.root payload target before log +
        successfulSignerInputWeight key message (targetCoverageInputIncrement remaining key before log payload target) result := by
  have hcoarse := signWithView_observedTargetFutureCoverage_le remaining key message before log payload target hsigned result hresult
  cases hresponse : result.1.1 with
  | none => simpa only [successfulSignerInputWeight, successfulSignerViewWeight, hresponse] using hcoarse
  | some signature =>
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · have heq : observedTargetFutureCoverage remaining key.parameter key.root payload target result.2
            (log ++ [⟨message, some signature⟩]) =
            observedTargetFutureCoverage remaining key.parameter key.root payload target before log := by
          unfold observedTargetFutureCoverage
          rw [uncovered_eligibleSigningViews_append_none _ _ _ _ _ _ (by simp [eligibleSigningView?, hsame])]
          exact observedTargetFutureCoverage_cache_stable remaining key.parameter key.root payload target before result.2 log
            (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) hsigned
        rw [heq]
        exact le_self_add
      · have hinput : tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness) ≠
            tweakableHashInput key.parameter .message payload := by
          intro heq
          exact hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) heq).2
        cases hview : result.1.2 <;>
          simpa only [successfulSignerInputWeight, successfulSignerViewWeight, hresponse, hview,
            targetCoverageInputIncrement, if_neg hinput] using hcoarse

noncomputable def targetInputReuseCharge (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (q : Nat) : ENNReal :=
  (∑' input, cachedSignerInputWeight key message before (targetCoverageInputIncrement remaining key before log payload target) input) *
    digestReuseWeight q

theorem cachedSignerInputWeight_target_self (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) :
    cachedSignerInputWeight key message before (targetCoverageInputIncrement remaining key before log payload target)
      (tweakableHashInput key.parameter .message payload) = 0 := by
  unfold cachedSignerInputWeight
  cases before (tweakableHashInput key.parameter .message payload) <;>
    simp only [targetCoverageInputIncrement_self, ite_self]

theorem expected_signWithView_observedTargetFutureCoverage_le_inputReuse (remaining : Nat) (key : SecretKey)
    (message : Message) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      observedTargetFutureCoverage remaining key.parameter key.root payload target result.2
        (log ++ [⟨message, result.1.1⟩])) ≤
      observedTargetFutureCoverage (remaining + 1) key.parameter key.root payload target before log +
        targetInputReuseCharge remaining key message before log payload target q := by
  let required := uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers key.parameter before) key.root payload log) target
  let weight := targetCoverageInputIncrement remaining key before log payload target
  have hweight (input : HashInput) (source : FewTimeView) : weight input source ≤ futureFewTimeCoverageIncrement remaining required target source := by
    unfold weight targetCoverageInputIncrement
    split_ifs
    · exact bot_le
    · exact le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        (futureFewTimeCoverage remaining required target + successfulSignerInputWeight key message weight result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_observedTargetFutureCoverage_le_input remaining key message before log payload target hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ futureFewTimeCoverage remaining required target +
        (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
          successfulSignerInputWeight key message weight result) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ futureFewTimeCoverage remaining required target +
        ((∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          futureFewTimeCoverageIncrement remaining required target source) +
          targetInputReuseCharge remaining key message before log payload target q) :=
      add_le_add le_rfl (expected_successfulSignerInputWeight_le key message before weight _ hweight q hq hcache)
    _ = _ := by
      rw [← add_assoc, expected_futureFewTimeCoverageIncrement]
      rfl

end SphincsSecurity.Concrete
