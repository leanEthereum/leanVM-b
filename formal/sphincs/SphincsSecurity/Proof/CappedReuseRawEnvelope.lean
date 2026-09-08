import SphincsSecurity.Proof.ReuseRawEnvelope
import SphincsSecurity.Proof.AdaptiveCacheCapacity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def cappedReuseRawEnvelope (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) : TargetShapeVector :=
  fun groups remaining => if SigningTranscript.Valid state.2 then
    reuseRawEnvelope key reuse budget (signatureLimit - state.2.length) state groups remaining else 0

theorem cappedReuseRawEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (state : CoverLogState)
    {small large : Nat} (hbudget : small ≤ large)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    cappedReuseRawEnvelope key reuse small state groups remaining ≤ cappedReuseRawEnvelope key reuse large state groups remaining := by
  unfold cappedReuseRawEnvelope
  split_ifs
  · exact targetShapeEnvelope_queries_mono _ _ _ _ _ hbudget groups remaining hvalid
  · exact le_rfl

theorem expected_logTraced_cappedReuseRawEnvelope_le (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : ∀ message, exactDigestReuseWeight key message state.1 ≤ reuse)
    (input : (OracleWorld + SigningSpec).Domain) (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedReuseRawEnvelope key reuse (budget - signingExecutionHashCost input) result.2 groups remaining) ≤
      cappedReuseRawEnvelope key reuse budget state groups remaining := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedReuseRawEnvelope, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        apply le_trans _ (expected_logTraced_world_reuseRawEnvelope_le key reuse budget
          (signatureLimit - state.2.length) state world hsigned hcost groups remaining hvalid)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
            obtain ⟨base, _, rfl⟩ := hr
            simp only [signingLogFragment, List.append_nil]
          apply mul_le_mul' le_rfl
          unfold cappedReuseRawEnvelope
          rw [hlog, if_pos hactive.valid_before]
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        rw [hremaining]
        apply le_trans _ (expected_logTraced_sign_reuseRawEnvelope_le key reuse budget _ state hsigned message
          (hreuse message) groups remaining hvalid)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
            obtain ⟨base, _, rfl⟩ := hr
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          apply mul_le_mul' le_rfl
          unfold cappedReuseRawEnvelope
          split_ifs
          · rw [hlog]
          · exact zero_le
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedReuseRawEnvelope key reuse (budget - signingExecutionHashCost input) result.2 groups remaining) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun h =>
            hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hr).mp h)
        rw [cappedReuseRawEnvelope, if_neg hinvalid, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    rw [hzero]
    exact zero_le

end SphincsSecurity.Concrete
