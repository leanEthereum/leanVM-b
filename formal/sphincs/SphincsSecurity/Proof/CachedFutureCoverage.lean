import SphincsSecurity.Proof.FutureCoverageCharge
import SphincsSecurity.Proof.EligibleTargetReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedFutureCoverage (remaining : Nat) (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  cacheMessageWeight parameter (fun input target =>
    observedTargetFutureCoverage remaining parameter root (payloadOf input) target cache log) cache

noncomputable def cachedFutureCoverageReuseCharge (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) : ENNReal :=
  cacheMessageWeight key.parameter (fun input target =>
    targetInputReuseCharge remaining key message before log (payloadOf input) target q) before

theorem signWithView_newTarget_futureCoverage_eq (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (input : HashInput) (output : HashOutput) (hmessage : MessageHashInput key.parameter input)
    (hfresh : before input = none) (houtput : result.2 input = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) (target : FewTimeView) :
    observedTargetFutureCoverage remaining key.parameter key.root (payloadOf input) target result.2
      (log ++ [⟨message, result.1.1⟩]) =
      observedTargetFutureCoverage remaining key.parameter key.root (payloadOf input) target before log := by
  obtain ⟨payload, rfl⟩ := hmessage
  rw [payloadOf_tweakableHashInput]
  have hnone : eligibleSigningView? (messageAnswers key.parameter result.2) key.root payload
      ⟨message, result.1.1⟩ = none := by
    cases hresponse : result.1.1 with
    | none => simp [eligibleSigningView?]
    | some signature =>
        have hresult' : ((some signature, result.1.2), result.2) ∈ support
            ((simulateQ romImpl (signWithView key message)).run before) := by
          have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
          rwa [heq] at hresult
        have hsame : payload = messageDigestPayload key.root message signature.randomness := by
          by_contra hne
          have hprior := signWithView_admissible_message_cached_before key message before result.2 signature result.1.2
            hresult' payload output hne houtput hadmissible
          rw [hfresh] at hprior
          contradiction
        simp [eligibleSigningView?, hsame]
  unfold observedTargetFutureCoverage
  rw [uncovered_eligibleSigningViews_append_none _ _ _ _ _ _ hnone]
  exact observedTargetFutureCoverage_cache_stable remaining key.parameter key.root payload target before result.2 log
    (simulateQ_romImpl_cache_le (signWithView key message) before result hresult) hsigned

theorem signWithView_cachedFutureCoverage_eq (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    cachedFutureCoverage remaining key.parameter key.root result.2 (log ++ [⟨message, result.1.1⟩]) =
      cacheMessageWeight key.parameter (fun input target =>
        observedTargetFutureCoverage remaining key.parameter key.root (payloadOf input) target result.2
          (log ++ [⟨message, result.1.1⟩])) before +
      newMessageFutureCoverage remaining key.parameter (fixedSigningViews key.parameter before key.root log) before result.2 := by
  rw [cachedFutureCoverage, cacheMessageWeight_of_le key.parameter _ before result.2
    (simulateQ_romImpl_cache_le (signWithView key message) before result hresult)]
  congr 1
  apply tsum_congr
  intro input
  unfold cacheMessageEntryWeight
  cases houtput : result.2 input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood hfresh
      · exact signWithView_newTarget_futureCoverage_eq remaining key message before log hsigned result hresult
          input output hgood.1 hfresh houtput hgood.2 _
      · rfl
      · rfl

theorem expected_signWithView_cachedFutureCoverage_le (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (hfinite : Finite before) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      cachedFutureCoverage remaining key.parameter key.root result.2 (log ++ [⟨message, result.1.1⟩])) ≤
      cachedFutureCoverage (remaining + 1) key.parameter key.root before log +
        expectedQueryCharge (freshFutureCoverageCharge remaining key.parameter (fixedSigningViews key.parameter before key.root log))
          (signWithView key message) before + cachedFutureCoverageReuseCharge remaining key message before log q := by
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      cachedFutureCoverage remaining key.parameter key.root result.2 (log ++ [⟨message, result.1.1⟩])) =
      (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        cacheMessageWeight key.parameter (fun input target =>
          observedTargetFutureCoverage remaining key.parameter key.root (payloadOf input) target result.2
            (log ++ [⟨message, result.1.1⟩])) before) +
      (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        newMessageFutureCoverage remaining key.parameter (fixedSigningViews key.parameter before key.root log) before result.2) := by
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · rw [signWithView_cachedFutureCoverage_eq remaining key message before log hsigned result hresult, mul_add]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul, zero_mul, add_zero]
  rw [heq, expected_cacheMessageWeight]
  have hprior := cacheMessageWeight_mono key.parameter _ _ before (fun input target =>
    expected_signWithView_observedTargetFutureCoverage_le_inputReuse remaining key message before log (payloadOf input) target hsigned q hq hcache)
  rw [cacheMessageWeight_add] at hprior
  exact (add_le_add hprior (expected_newMessageFutureCoverage_le remaining key.parameter
    (fixedSigningViews key.parameter before key.root log) (signWithView key message) before hfinite)).trans_eq (by
      unfold cachedFutureCoverage cachedFutureCoverageReuseCharge
      ac_rfl)

theorem cachedFutureCoverage_fixedLog_eq (remaining : Nat) (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log) :
    cachedFutureCoverage remaining parameter root after log = cachedFutureCoverage remaining parameter root before log +
      newMessageFutureCoverage remaining parameter (fixedSigningViews parameter before root log) before after := by
  have hweight : (fun input target => observedTargetFutureCoverage remaining parameter root (payloadOf input) target after log) =
      (fun input target => observedTargetFutureCoverage remaining parameter root (payloadOf input) target before log) := by
    funext input target
    exact observedTargetFutureCoverage_cache_stable remaining parameter root (payloadOf input) target before after log hcache hsigned
  rw [cachedFutureCoverage, hweight, cacheMessageWeight_of_le parameter _ before after hcache]
  rfl

theorem expected_cachedFutureCoverage_fixedLog_le {α : Type} (remaining : Nat) (parameter : PublicParameter) (root : Digest)
    (before : QueryCache HashSpec) (hfinite : Finite before) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached parameter before root log) (computation : OracleComp OracleWorld α) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
      cachedFutureCoverage remaining parameter root result.2 log) ≤
      cachedFutureCoverage remaining parameter root before log +
        expectedQueryCharge (freshFutureCoverageCharge remaining parameter (fixedSigningViews parameter before root log)) computation before := by
  have heq : (∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
      cachedFutureCoverage remaining parameter root result.2 log) =
      ∑' result, Pr[= result | (simulateQ romImpl computation).run before] *
        (cachedFutureCoverage remaining parameter root before log +
          newMessageFutureCoverage remaining parameter (fixedSigningViews parameter before root log) before result.2) := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl computation).run before)
    · rw [cachedFutureCoverage_fixedLog_eq remaining parameter root before result.2 log
        (simulateQ_romImpl_cache_le computation before result hresult) hsigned]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  rw [heq]
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one)
    (expected_newMessageFutureCoverage_le remaining parameter (fixedSigningViews parameter before root log) computation before hfinite)

theorem one_le_cachedFutureCoverage_of_covered (remaining : Nat) (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcover : SigningCacheCovered parameter root cache log) :
    1 ≤ cachedFutureCoverage remaining parameter root cache log := by
  obtain ⟨input, output, hmessage, houtput, hadmissible, hcovered⟩ := hcover
  have hentry : cacheMessageEntryWeight parameter
      (fun input target => observedTargetFutureCoverage remaining parameter root (payloadOf input) target cache log) cache input = 1 := by
    simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
    change futureFewTimeCoverage remaining
      (uncoveredFewTimeTrees (fixedSigningViews parameter cache root log input) (hashOutputFewTimeView output))
      (hashOutputFewTimeView output) = 1
    rw [(uncoveredFewTimeTrees_eq_empty_iff _ _).mpr hcovered, futureFewTimeCoverage_empty]
  rw [← hentry]
  exact ENNReal.le_tsum input

theorem cachedFutureCoverage_of_no_message (remaining : Nat) (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none) :
    cachedFutureCoverage remaining parameter root cache log = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  by_cases hmessage : MessageHashInput parameter input
  · simp only [cacheMessageEntryWeight, hnone input hmessage]
  · unfold cacheMessageEntryWeight
    cases cache input <;> simp only [hmessage, false_and, if_false]

end SphincsSecurity.Concrete
