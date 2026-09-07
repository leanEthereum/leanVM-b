import SphincsSecurity.Proof.SigningQueryCommutationGap
import SphincsSecurity.Proof.AdaptiveRawIndex

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def rawIndexSigningGap (key : SecretKey) (q signatures : Nat) (state : CoverLogState) : TargetShapeVector :=
  signingQueryCommutationGap (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
    (messageCacheSlotCount key.parameter q state.1) signatures (observedRawIndexShapeVector key state)

theorem expected_logTraced_sign_rawIndex_add_gap_le (key : SecretKey) (q signatures : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      rawIndexCacheEnvelope key q signatures result.2 groups remaining) + rawIndexSigningGap key q signatures state groups remaining ≤
      rawIndexCacheEnvelope key q (signatures + 1) state groups remaining := by
  let queries := messageCacheSlotCount key.parameter q state.1
  let uniform := (Fintype.card Index : ENNReal)⁻¹
  let reuse := digestReuseWeight q
  let arrival := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹
  have hfreeze : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      rawIndexCacheEnvelope key q signatures result.2 groups remaining) ≤
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
        targetShapeEnvelope uniform reuse arrival queries signatures (observedRawIndexShapeVector key result.2) groups remaining := by
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
    · exact mul_le_mul' le_rfl (targetShapeEnvelope_queries_mono uniform reuse arrival signatures _
        (messageCacheSlotCount_antitone key.parameter q state.1 result.2.1
          (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hr) (Finite.of_enncard_le (hcap result hr))) groups remaining hvalid)
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  rw [targetShapeEnvelope_expected] at hfreeze
  have hsign := targetShapeEnvelope_mono uniform reuse arrival queries signatures
    (fun G R hv => expected_logTraced_sign_rawIndexShape_le key q hq state hsigned hcache message G R hv) groups remaining hvalid
  exact (add_le_add (hfreeze.trans hsign) le_rfl).trans_eq
    (targetShapeEnvelope_signing_gap uniform reuse arrival queries signatures (observedRawIndexShapeVector key state) groups remaining hvalid)

noncomputable def cappedRawIndexStepGap (key : SecretKey) (q : Nat) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → TargetShapeVector
  | .inl _ => fun _ _ => 0
  | .inr _ => fun G R => if state.2.length < signatureLimit then
      rawIndexSigningGap key q (signatureLimit - (state.2.length + 1)) state G R else 0

theorem expected_logTraced_cappedRawIndex_add_gap_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (input : (OracleWorld + SigningSpec).Domain)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key input).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedRawIndexCacheEnvelope key q result.2 groups remaining) + cappedRawIndexStepGap key q state input groups remaining ≤
      cappedRawIndexCacheEnvelope key q state groups remaining := by
  cases input with
  | inl world =>
      rw [cappedRawIndexStepGap, add_zero, expected_logTraced_world_cappedRawIndex_eq key q state world hsigned hcap groups remaining hvalid]
  | inr message =>
      by_cases hactive : state.2.length < signatureLimit
      · have hv : SigningTranscript.Valid state.2 := Nat.le_of_lt hactive
        have hn : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        simp only [cappedRawIndexStepGap, if_pos hactive]
        rw [cappedRawIndexCacheEnvelope, if_pos hv, hn]
        apply le_trans (add_le_add ?_ le_rfl)
          (expected_logTraced_sign_rawIndex_add_gap_le key q _ hq state hsigned hcache message hcap groups remaining hvalid)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
            obtain ⟨base, _, rfl⟩ := hr
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          apply mul_le_mul' le_rfl
          unfold cappedRawIndexCacheEnvelope
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      · simp only [cappedRawIndexStepGap, if_neg hactive, add_zero]
        exact expected_logTraced_cappedRawIndexCacheEnvelope_le key q hq state hsigned hcache (.inr message) hcap groups remaining hvalid

end SphincsSecurity.Concrete
