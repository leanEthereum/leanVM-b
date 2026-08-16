import XmssSecurity.CappedEncodingQueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem cappedSampledDetailedGame_externalCollision_probability_le_of_bound
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : ∀ keyResult ∈
      support ((simulateQ xmssRomImpl Concrete.cappedScheme.keygen).run ∅),
      (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary
        keyResult.1.1 keyResult.1.2 keyResult.2).IsQueryBoundP
          (· matches .inr _) q) :
    Pr[fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2 = true |
      cappedSampledDetailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold cappedSampledDetailedGameWithEncodingTrace
  refine probEvent_bind_le_of_forall_le fun keyResult hkeyResult => ?_
  exact CappedEncodingMonitor.encodingSamplingTrace_collision_probability_le_of_sample_bound
    (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary
      keyResult.1.1 keyResult.1.2 keyResult.2) q
    (hbound keyResult hkeyResult)

theorem cappedSampledDetailedGame_externalCollision_probability_le
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q) :
    Pr[fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.2 = true |
      cappedSampledDetailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  exact cappedSampledDetailedGame_externalCollision_probability_le_of_bound q adversary
    (fun keyResult hkeyResult =>
      cappedSplitDetailedGameAfterKeygenWithEncodingTrace_encodingSample_bound
        q adversary hbound keyResult hkeyResult)

end XmssSecurity
