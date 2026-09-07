import SphincsSecurity.Proof.RawIndexCacheEnvelope
import SphincsSecurity.Proof.AdaptiveCacheCapacity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cappedRawIndexCacheEnvelope (key : SecretKey) (q : Nat) (state : CoverLogState) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  if SigningTranscript.Valid state.2 then rawIndexCacheEnvelope key q (signatureLimit - state.2.length) state groups remaining else 0

theorem expected_logTraced_cappedRawIndexCacheEnvelope_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (input : (OracleWorld + SigningSpec).Domain)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key input).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedRawIndexCacheEnvelope key q result.2 groups remaining) ≤ cappedRawIndexCacheEnvelope key q state groups remaining := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedRawIndexCacheEnvelope, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        apply le_trans ?_ (expected_logTraced_world_rawIndexCacheEnvelope_le key q (signatureLimit - state.2.length) state world hsigned hcap groups remaining hvalid)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.append_nil]
          unfold cappedRawIndexCacheEnvelope
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        rw [hremaining]
        apply le_trans ?_ (expected_logTraced_sign_rawIndexCacheEnvelope_le key q _ hq state hsigned hcache message hcap groups remaining hvalid)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          unfold cappedRawIndexCacheEnvelope
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedRawIndexCacheEnvelope key q result.2 groups remaining) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun h =>
            hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp h)
        rw [cappedRawIndexCacheEnvelope, if_neg hinvalid, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    rw [hzero]
    exact bot_le

theorem expected_adaptive_cappedRawIndexCacheEnvelope_le {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedRawIndexCacheEnvelope key q result.2 groups remaining) ≤ cappedRawIndexCacheEnvelope key q state groups remaining := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key q input next state hbudget
      have hbefore := simulateQ_logTraced_initial_cache_bound key q (OracleSpec.query input >>= next) state hbudget
      have hstep := expected_logTraced_cappedRawIndexCacheEnvelope_le key q hq state hsigned hbefore input
        (fun result hresult => simulateQ_logTraced_initial_cache_bound key q (next result.1) result.2 (htail result hresult)) groups remaining hvalid
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      apply le_trans ?_ hstep
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · exact mul_le_mul' le_rfl (ih result.1 result.2
          (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult) (htail result hresult))
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

theorem expected_adaptive_validRawIndexShape_le {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      (if SigningTranscript.Valid result.2.2 then observedRawIndexShapeVector key result.2 groups remaining else 0)) ≤
      cappedRawIndexCacheEnvelope key q state groups remaining := by
  apply le_trans ?_ (expected_adaptive_cappedRawIndexCacheEnvelope_le key q hq computation state hsigned hbudget groups remaining hvalid)
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  unfold cappedRawIndexCacheEnvelope
  split_ifs
  · exact le_targetShapeEnvelope _ _ _ _ _ _ groups remaining
  · exact le_rfl

end SphincsSecurity.Concrete
