import SphincsSecurity.Proof.CacheCapacityWorld
import SphincsSecurity.Proof.ValidInterleavedCover

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cappedCacheCapacityPotential (key : SecretKey) (q : Nat) (state : CoverLogState) : ENNReal :=
  if SigningTranscript.Valid state.2 then cacheCapacityPotential (signatureLimit - state.2.length) key q state else 0

noncomputable def capacityReuseStepCharge (key : SecretKey) (q : Nat) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message => if state.2.length < signatureLimit then
      cacheCapacityReuseCharge (signatureLimit - (state.2.length + 1)) key q state message else 0

theorem expected_logTraced_cappedCacheCapacityPotential_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (input : (OracleWorld + SigningSpec).Domain)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key input).run state), QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * cappedCacheCapacityPotential key q result.2) ≤
      cappedCacheCapacityPotential key q state + capacityReuseStepCharge key q state input := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedCacheCapacityPotential, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        simp only [capacityReuseStepCharge, add_zero]
        apply le_trans ?_ (expected_world_cacheCapacityPotential_le _ key q state (Finite.of_enncard_le hcache) hsigned world hcap)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.append_nil]
          unfold cappedCacheCapacityPotential
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        rw [capacityReuseStepCharge, if_pos hlength, hremaining]
        apply le_trans ?_ (expected_logTraced_sign_cacheCapacityPotential_le _ key q hq state hsigned hcache message hcap)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          unfold cappedCacheCapacityPotential
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedCacheCapacityPotential key q result.2) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun h =>
            hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp h)
        rw [cappedCacheCapacityPotential, if_neg hinvalid, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    rw [hzero]
    exact bot_le

end SphincsSecurity.Concrete
