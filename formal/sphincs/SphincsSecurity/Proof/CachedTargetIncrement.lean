import SphincsSecurity.Proof.CachedSourceIncrement
import SphincsSecurity.Proof.FutureTargetIncrementBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem eligibleSigningViews_fresh_eq_observed (parameter : PublicParameter) (root : Digest)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput)
    (hfresh : before (tweakableHashInput parameter .message payload) = none)
    (hsigned : SigningDigestsCached parameter before root log) :
    eligibleSigningViews (messageAnswers parameter before) root payload log =
      observedOptionalSigningViews (messageAnswers parameter before) root log := by
  funext slot
  simp only [eligibleSigningViews, observedOptionalSigningViews]
  cases hresponse : (log.get slot).2 with
  | none =>
      change Option.bind (log.get slot).2 _ = Option.bind (log.get slot).2 _
      rw [hresponse]
      rfl
  | some signature =>
      have hne : messageDigestPayload root (log.get slot).1 signature.randomness ≠ payload := by
        intro heq
        have hcached := hsigned (log.get slot) (List.get_mem _ _) signature hresponse
        apply hcached
        change before (tweakableHashInput parameter .message (messageDigestPayload root (log.get slot).1 signature.randomness)) = none
        rwa [heq]
      unfold eligibleSigningView?
      rw [hresponse]
      change (if messageDigestPayload root (log.get slot).1 signature.randomness = payload then none else _) = _
      rw [if_neg hne]

theorem cachedTargetSourceIncrement_freshTarget (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input sourceInput : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    cachedTargetSourceIncrement remaining key message (before.cacheQuery input output) log input sourceInput =
      cachedSignerInputWeight key message before (fun _ source =>
        if Admissible (truncateMessageDigest output) then
          futureFewTimeCoverageIncrement remaining
            (uncoveredFewTimeTrees (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
              (hashOutputFewTimeView output)) (hashOutputFewTimeView output) source else 0) sourceInput := by
  by_cases heq : sourceInput = input
  · subst sourceInput
    rw [cachedTargetSourceIncrement_self]
    simp only [cachedSignerInputWeight, hfresh]
  · rw [cachedTargetSourceIncrement_of_ne remaining key message _ log input sourceInput heq]
    obtain ⟨payload, rfl⟩ := hmessage
    have hstable : eligibleSigningViews (messageAnswers key.parameter (before.cacheQuery (tweakableHashInput key.parameter .message payload) output))
        key.root payload log = observedOptionalSigningViews (messageAnswers key.parameter before) key.root log := by
      rw [← eligibleSigningViews_fresh_eq_observed key.parameter key.root before log payload hfresh hsigned]
      funext slot
      exact eligibleSigningView?_cache_stable key.parameter key.root before _
        (QueryCache.le_cacheQuery before hfresh) payload (log.get slot) (hsigned _ (List.get_mem _ _))
    simp only [cacheMessageEntryWeight, QueryCache.cacheQuery_self, payloadOf_tweakableHashInput,
      show MessageHashInput key.parameter (tweakableHashInput key.parameter .message payload) from ⟨payload, rfl⟩,
      true_and, hstable]
    unfold cachedSignerInputWeight
    rw [QueryCache.cacheQuery_of_ne before output heq]
    cases before sourceInput <;> simp only
    · split_ifs <;> rfl
    · split_ifs <;> rfl

theorem expected_freshTargetReuseRow_le (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' sourceInput, cachedTargetSourceIncrement remaining key message (before.cacheQuery input output) log input sourceInput) ≤
      (∑' sourceInput, cachedSignerInputWeight key message before (fun _ source =>
        coverageOccupancyCompletionIncrement
          (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining source) sourceInput) *
        ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  simp only [cachedTargetSourceIncrement_freshTarget remaining key message before log input _ _ hfresh hsigned hmessage,
    ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro sourceInput
  unfold cachedSignerInputWeight
  cases before sourceInput with
  | none => simp only [mul_zero, tsum_zero, zero_mul, le_refl]
  | some output =>
      simp only
      split_ifs with hgood
      · exact expected_uniformHashOutput_futureCoverageIncrement_le _ remaining _
      · simp only [mul_zero, tsum_zero, zero_mul, le_refl]

end SphincsSecurity.Concrete
