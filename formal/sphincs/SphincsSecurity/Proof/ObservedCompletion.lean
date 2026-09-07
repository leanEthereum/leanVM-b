import SphincsSecurity.Proof.BinomialCompletion
import SphincsSecurity.Proof.ObservedBinomialOccupancy
import SphincsSecurity.Proof.ValidInterleavedCover

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def binomialReuseMoments (key : SecretKey) (q : Nat) (state : CoverLogState)
    (message : Message) : Nat → ENNReal
  | 0 => 0
  | degree + 1 =>
      let views := observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2
      (∑' source, cachedMessageEntryCountWhere state.1 key.parameter key.root message (· = source) *
        ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) * digestReuseWeight q

theorem expected_logTraced_sign_completion_le (key : SecretKey) (q remaining degree : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      binomialCompletion (fun degree => observedLogBinomialOccupancy key degree result.2) remaining degree) ≤
        binomialCompletion (fun degree => observedLogBinomialOccupancy key degree state) (remaining + 1) degree +
          binomialCompletion (binomialReuseMoments key q state message) remaining degree := by
  apply expected_binomialCompletion_le
  intro d
  cases d with
  | zero =>
      simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_zero, binomialStep,
        binomialReuseMoments, add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | succ d =>
      simpa only [binomialStep, binomialOccupancyStepCharge, binomialReuseMoments,
        observedLogBinomialOccupancy, add_assoc] using
          expected_logTraced_binomialOccupancy_le key d q hq state hsigned hcache (.inr message)

noncomputable def cappedLogCompletion (key : SecretKey) (q degree : Nat) (state : CoverLogState) : ENNReal :=
  if SigningTranscript.Valid state.2 ∧ QueryCache.enncard state.1 ≤ q then
    binomialCompletion (fun degree => observedLogBinomialOccupancy key degree state)
      (signatureLimit - state.2.length) degree else 0

noncomputable def completionReuseStepCharge (key : SecretKey) (q degree : Nat) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message =>
      if state.2.length < signatureLimit ∧ QueryCache.enncard state.1 ≤ q then
        binomialCompletion (binomialReuseMoments key q state message)
          (signatureLimit - (state.2.length + 1)) degree else 0

theorem expected_logTraced_cappedCompletion_le (key : SecretKey) (q degree : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : (OracleWorld + SigningSpec).Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedLogCompletion key q degree result.2) ≤
        cappedLogCompletion key q degree state + completionReuseStepCharge key q degree state input := by
  by_cases hactive : ValidSigningStep state.2 input ∧ QueryCache.enncard state.1 ≤ q
  · rw [cappedLogCompletion, if_pos ⟨hactive.1.valid_before, hactive.2⟩]
    cases input with
    | inl world =>
        simp only [completionReuseStepCharge, add_zero]
        have hpoint (result : (OracleWorld + SigningSpec).Range (.inl world) × CoverLogState)
            (hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)) :
            cappedLogCompletion key q degree result.2 ≤
              binomialCompletion (fun degree => observedLogBinomialOccupancy key degree state)
                (signatureLimit - state.2.length) degree := by
          rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
          obtain ⟨base, hbase, rfl⟩ := hresult
          simp only [signingLogFragment, List.append_nil]
          have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root state.1 base.2 state.2
            (unloggedMappedAdversaryImpl_cache_le key (.inl world) state.1 base hbase) hsigned
          unfold cappedLogCompletion
          split_ifs
          · simp only [observedLogBinomialOccupancy, hstable, le_refl]
          · exact bot_le
        calc
          _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl world)).run state] *
              binomialCompletion (fun degree => observedLogBinomialOccupancy key degree state)
                (signatureLimit - state.2.length) degree := by
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
            · exact mul_le_mul' le_rfl (hpoint result hresult)
            · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive.1
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        rw [completionReuseStepCharge, if_pos ⟨hlength, hactive.2⟩, hremaining]
        apply le_trans ?_ (expected_logTraced_sign_completion_le key q _ degree hq state hsigned hactive.2 message)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          unfold cappedLogCompletion
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedLogCompletion key q degree result.2) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinactive : ¬ (SigningTranscript.Valid result.2.2 ∧ QueryCache.enncard result.2.1 ≤ q) := by
          intro hafter
          exact hactive ⟨(logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp hafter.1,
            (QueryCache.enncard_mono (logTracedMappedAdversaryImpl_cache_le key input state result hresult)).trans hafter.2⟩
        rw [cappedLogCompletion, if_neg hinactive, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    rw [hzero]
    exact bot_le

end SphincsSecurity.Concrete
