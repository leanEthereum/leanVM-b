import XmssSecurity.CappedEncodingActionTrace
import XmssSecurity.CappedEncodingPrehitProbability
import XmssSecurity.EncodingEventProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem cappedWinning_encoding_event_trace_postSigning_decomposition
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : execution ∈ support (cappedDetailedGameWithSigningTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding) :
    ∃ entry ∈ execution.2.2,
      entry.EncodingInputPrehit execution.1.secretKey ∨
        entry.FreshSigningEncodingCollision execution.1.secretKey ∨
          entry.PostSigningFreshForgedEncodingCollision execution.1.secretKey
            execution.1.forgery execution.2.1 := by
  obtain ⟨hlog, hcaches, hcached⟩ :=
    cappedDetailedGameWithSigningTrace_invariants adversary execution hmem
  obtain ⟨entry, hentry, hprehit | hsigning | hforged⟩ :=
    winning_encoding_event_trace_monitor_decomposition execution.2.1 execution.1
      execution.2.2 hlog hcaches hcached hevent
  · exact ⟨entry, hentry, Or.inl hprehit⟩
  · exact ⟨entry, hentry, Or.inr (Or.inl hsigning)⟩
  · obtain ⟨encoding, hdecode⟩ := hevent.forgery_decode
    have hpreserves :=
      cappedDetailedGameWithSigningTrace_preservesOtherValidEncodingInputs
        adversary execution hmem
    have hforged' := hforged
    obtain ⟨signature, _signedOutput, _forgedOutput, hsignature, _rest⟩ := hforged'
    cases hsignedFresh : entry.initialCache
        (Concrete.CacheView.encodingInput execution.1.secretKey.parameter
          entry.request.epoch (entry.request.message, signature.randomness)) with
    | none =>
        exact ⟨entry, hentry, Or.inr (Or.inr
          (entry.postSigningFreshForgedEncodingCollision_of_valid_fresh
            execution.1.secretKey execution.1.forgery execution.2.1
            (hpreserves entry hentry) (hcaches entry hentry).2 hforged encoding hdecode
            signature hsignature hsignedFresh))⟩
    | some output =>
        exact ⟨entry, hentry, Or.inl ⟨signature, output, hsignature, hsignedFresh⟩⟩

theorem cappedWinning_encoding_event_probability_eq_encodingTrace
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] =
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding |
      cappedDetailedGameWithEncodingTrace adversary] := by
  rw [← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map]
  rfl

theorem cappedWinning_encoding_event_probability_le_prehit_add_monitorHit
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.1.2,
          entry.EncodingInputPrehit execution.1.secretKey |
      cappedDetailedGameWithEncodingTrace adversary] +
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          execution.2.2 = true |
      cappedDetailedGameWithEncodingTrace adversary] := by
  rw [cappedWinning_encoding_event_probability_eq_encodingTrace]
  let win := fun execution : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
    WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding
  let prehit := fun execution : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
    ∃ entry ∈ execution.2.1.2,
      entry.EncodingInputPrehit execution.1.secretKey
  let monitorHit := fun execution : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true
  calc
    Pr[win | cappedDetailedGameWithEncodingTrace adversary] ≤
        Pr[fun execution =>
          (win execution ∧ prehit execution) ∨
            (win execution ∧ monitorHit execution) |
          cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      have hprojected : (execution.1, execution.2.1) ∈
          support (cappedDetailedGameWithSigningTrace adversary) := by
        rw [← cappedDetailedGameWithEncodingTrace_projection, support_map]
        exact ⟨execution, hmem, rfl⟩
      obtain ⟨entry, hentry, hprehit | hsigning | hpostSigning⟩ :=
        cappedWinning_encoding_event_trace_postSigning_decomposition adversary
          (execution.1, execution.2.1) hprojected hwin
      · exact Or.inl ⟨hwin, entry, hentry, hprehit⟩
      · exact Or.inr ⟨hwin,
          cappedDetailedGameWithEncodingTrace_freshSigningCollision_monitorHit
            adversary execution hmem hwin ⟨entry, hentry, hsigning⟩⟩
      · obtain ⟨encoding, hdecode⟩ := hwin.forgery_decode
        exact Or.inr ⟨hwin,
          cappedDetailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
            adversary execution hmem hwin encoding hdecode
              ⟨entry, hentry, hpostSigning⟩⟩
    _ ≤ Pr[fun execution => win execution ∧ prehit execution |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[fun execution => win execution ∧ monitorHit execution |
          cappedDetailedGameWithEncodingTrace adversary] :=
      probEvent_or_le _ _ _

theorem cappedWinning_encoding_prehit_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.1.2,
          entry.EncodingInputPrehit execution.1.secretKey |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  calc
    _ = Pr[fun execution : GameOutcome ×
          (QueryCache HashSpec × SigningCacheTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
          execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
        cappedDetailedGameWithSigningTrace adversary] := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl
    _ ≤ _ := cappedDetailedGameWithSigningTrace_winning_prehit_probability_le
      q adversary hbound

theorem cappedWinning_encoding_event_probability_le_two_terms
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
      2 * ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
  calc
    _ ≤
        Pr[fun execution : GameOutcome ×
            ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
          WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
            ∃ entry ∈ execution.2.1.2,
              entry.EncodingInputPrehit execution.1.secretKey |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[fun execution : GameOutcome ×
            ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
          WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
            CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
              execution.2.2 = true |
          cappedDetailedGameWithEncodingTrace adversary] :=
      cappedWinning_encoding_event_probability_le_prehit_add_monitorHit adversary
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      add_le_add (cappedWinning_encoding_prehit_probability_le q adversary hbound)
        (cappedWinning_encoding_monitorHit_probability_le q adversary hbound)
    _ = 2 * ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      rw [two_mul]

end XmssSecurity
