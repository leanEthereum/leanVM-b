import SphincsSecurity.Proof.CappedTargetEnvelope
import SphincsSecurity.Proof.FreshTargetWorld

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetArrivalHashCost (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl input => freshWorldTargetHashCost parameter cache input
  | .inr _ => 1024

noncomputable def unusedTargetHashCost (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) : Nat :=
  signingMacroHashCost input - targetArrivalHashCost parameter cache input

theorem targetArrivalHashCost_le_macro (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    targetArrivalHashCost parameter cache input ≤ signingMacroHashCost input := by
  cases input with
  | inr message => exact le_rfl
  | inl world =>
      cases world with
      | inl sample => exact le_rfl
      | inr input =>
          simp only [targetArrivalHashCost, freshWorldTargetHashCost, signingMacroHashCost]
          split_ifs <;> omega

theorem targetArrivalHashCost_add_unused (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    targetArrivalHashCost parameter cache input + unusedTargetHashCost parameter cache input = signingMacroHashCost input :=
  Nat.add_sub_of_le (targetArrivalHashCost_le_macro parameter cache input)

theorem expected_logTraced_cappedCachedTargetEnvelope_le_arrival (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (input : (OracleWorld + SigningSpec).Domain)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key input).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedCachedTargetEnvelope key q result.2 groups remaining) ≤
      cappedCachedTargetEnvelope key q state groups remaining +
        (targetArrivalHashCost key.parameter state.1 input : ENNReal) *
          ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
            cappedRawIndexCacheEnvelope key q state groups remaining) := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedCachedTargetEnvelope, if_pos hactive.valid_before, cappedRawIndexCacheEnvelope, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        have hcost : targetArrivalHashCost key.parameter state.1 (.inl world) = freshWorldTargetHashCost key.parameter state.1 world := by cases world <;> rfl
        rw [hcost]
        apply le_trans ?_ (expected_logTraced_world_cachedTargetEnvelope_le_fresh key q (signatureLimit - state.2.length) state world hsigned hcap groups remaining hvalid)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.append_nil]
          unfold cappedCachedTargetEnvelope
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        have hrate : (1024 : ENNReal) * (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) = (Fintype.card Index : ENNReal)⁻¹ := by
          have hpow : ((2 ^ ftsTreeHeight : Nat) : ENNReal) = 1024 := by norm_num [ftsTreeHeight]
          rw [hpow, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        simp only [targetArrivalHashCost, Nat.cast_ofNat]
        rw [← mul_assoc, hrate, hremaining]
        apply le_trans ?_ ((expected_logTraced_sign_cachedTargetEnvelope_le key q (signatureLimit - (state.2.length + 1)) hq state hsigned hcache message hcap groups remaining hvalid).trans
          (add_le_add le_rfl (mul_le_mul' le_rfl (rawIndexCacheEnvelope_signatures_mono key q state (Nat.le_succ _) groups remaining))))
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          unfold cappedCachedTargetEnvelope
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedCachedTargetEnvelope key q result.2 groups remaining) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun h =>
            hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp h)
        rw [cappedCachedTargetEnvelope, if_neg hinvalid, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    rw [hzero]
    exact bot_le

end SphincsSecurity.Concrete
