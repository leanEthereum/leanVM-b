import SphincsSecurity.Proof.AllMessageReuseArrival
import SphincsSecurity.Proof.AllMessageOccupancyArrival

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def uniformTargetIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (target : FewTimeView) : ENNReal :=
  ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
    futureFewTimeCoverageIncrement remaining
      (uncoveredFewTimeTrees (eligibleSigningViews (messageAnswers key.parameter before) key.root (payloadOf input) log) target) target source

noncomputable def cachedUniformIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  cacheMessageWeight key.parameter (uniformTargetIncrement remaining key before log) before

noncomputable def uniformOccupancyIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
    coverageOccupancyCompletionIncrement (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining source

theorem cachedFutureCoverage_add_uniformIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    cachedFutureCoverage remaining key.parameter key.root before log + cachedUniformIncrement remaining key before log =
      cachedFutureCoverage (remaining + 1) key.parameter key.root before log := by
  rw [cachedFutureCoverage, cachedUniformIncrement, ← cacheMessageWeight_add]
  unfold cachedFutureCoverage
  congr 1
  funext input target
  exact expected_futureFewTimeCoverageIncrement remaining _ target

theorem observedOccupancy_add_uniformIncrement (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    observedLogOccupancyCompletion remaining key (before, log) + uniformOccupancyIncrement remaining key before log =
      observedLogOccupancyCompletion (remaining + 1) key (before, log) :=
  expected_coverageOccupancyCompletionIncrement _ remaining

theorem uniformTargetIncrement_cache_stable (remaining : Nat) (key : SecretKey)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (input : HashInput) (target : FewTimeView) :
    uniformTargetIncrement remaining key after log input target = uniformTargetIncrement remaining key before log input target := by
  have hviews : eligibleSigningViews (messageAnswers key.parameter after) key.root (payloadOf input) log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root (payloadOf input) log := by
    funext slot
    exact eligibleSigningView?_cache_stable key.parameter key.root before after hcache _ (log.get slot) (hsigned _ (List.get_mem _ _))
  simp only [uniformTargetIncrement, hviews]

theorem uniformOccupancyIncrement_cache_stable (remaining : Nat) (key : SecretKey)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    uniformOccupancyIncrement remaining key after log = uniformOccupancyIncrement remaining key before log := by
  simp only [uniformOccupancyIncrement, observedOptionalSigningViews_cache_stable key.parameter key.root before after log hcache hsigned]

theorem cachedUniformIncrement_cacheQuery (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    cachedUniformIncrement remaining key (before.cacheQuery input output) log = cachedUniformIncrement remaining key before log +
      (if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
        uniformTargetIncrement remaining key before log input (hashOutputFewTimeView output) else 0) := by
  have hweight : uniformTargetIncrement remaining key (before.cacheQuery input output) log = uniformTargetIncrement remaining key before log := by
    funext targetInput target
    exact uniformTargetIncrement_cache_stable remaining key before _ log (QueryCache.le_cacheQuery before hfresh) hsigned targetInput target
  rw [cachedUniformIncrement, hweight, cacheMessageWeight_cacheQuery _ _ _ _ _ hfresh]
  rfl

theorem expected_fresh_uniformTargetIncrement_le (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then uniformTargetIncrement remaining key before log input (hashOutputFewTimeView output) else 0)) ≤
      uniformOccupancyIncrement remaining key before log * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  obtain ⟨payload, rfl⟩ := hmessage
  have hviews := eligibleSigningViews_fresh_eq_observed key.parameter key.root before log payload hfresh hsigned
  have hexpand (output : HashOutput) :
      (if Admissible (truncateMessageDigest output) then uniformTargetIncrement remaining key before log
        (tweakableHashInput key.parameter .message payload) (hashOutputFewTimeView output) else 0) =
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        (if Admissible (truncateMessageDigest output) then futureFewTimeCoverageIncrement remaining
          (uncoveredFewTimeTrees (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log)
            (hashOutputFewTimeView output)) (hashOutputFewTimeView output) source else 0) := by
    by_cases hadmissible : Admissible (truncateMessageDigest output) <;>
      simp only [hadmissible, if_true, if_false, mul_zero, tsum_zero, uniformTargetIncrement, payloadOf_tweakableHashInput, hviews]
  simp only [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_left_comm (Pr[= _ | ($ᵗ HashOutput : ProbComp HashOutput)])]
  simp only [ENNReal.tsum_mul_left]
  apply (ENNReal.tsum_le_tsum (fun source => mul_le_mul' le_rfl
    (expected_uniformHashOutput_futureCoverageIncrement_le _ remaining source))).trans_eq
  simp only [uniformOccupancyIncrement, ← mul_assoc, ENNReal.tsum_mul_right]

theorem expected_cachedUniformIncrement_cacheQuery_le (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      cachedUniformIncrement remaining key (before.cacheQuery input output) log) ≤
      cachedUniformIncrement remaining key before log + uniformOccupancyIncrement remaining key before log * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [cachedUniformIncrement_cacheQuery remaining key before log input _ hfresh hsigned, hmessage, true_and,
    mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  exact add_le_add le_rfl (expected_fresh_uniformTargetIncrement_le remaining key before log input hfresh hsigned hmessage)

theorem expected_fresh_cachedTargetFutureIncrement_eq (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * cachedTargetFutureIncrement remaining key before log input source) =
      cachedUniformIncrement remaining key before log := by
  simp only [cachedTargetFutureIncrement_of_fresh remaining key before log input hfresh, expected_cacheMessageWeight]
  rfl

end SphincsSecurity.Concrete
