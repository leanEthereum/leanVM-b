import SphincsSecurity.Proof.CachedFutureCoverage
import SphincsSecurity.Proof.ValidInterleavedCover

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cappedCachedFutureCoverage (key : SecretKey) (q : Nat) (state : CoverLogState) : ENNReal :=
  if SigningTranscript.Valid state.2 ∧ QueryCache.enncard state.1 ≤ q then
    cachedFutureCoverage (signatureLimit - state.2.length) key.parameter key.root state.1 state.2 else 0

noncomputable def futureCacheStepCharge (key : SecretKey) (q : Nat) (state : CoverLogState)
    (input : (OracleWorld + SigningSpec).Domain) : ENNReal :=
  if ValidSigningStep state.2 input ∧ QueryCache.enncard state.1 ≤ q then
    match input with
    | .inl world => hashQueryCharge
        (freshFutureCoverageCharge (signatureLimit - state.2.length) key.parameter
          (fixedSigningViews key.parameter state.1 key.root state.2)) state.1 world
    | .inr message => expectedQueryCharge
        (freshFutureCoverageCharge (signatureLimit - (state.2.length + 1)) key.parameter
          (fixedSigningViews key.parameter state.1 key.root state.2)) (signWithView key message) state.1 +
        cachedFutureCoverageReuseCharge (signatureLimit - (state.2.length + 1)) key message state.1 state.2 q
  else 0

theorem expected_world_cachedFutureCoverage_le (remaining : Nat) (key : SecretKey) (state : CoverLogState)
    (hfinite : Finite state.1) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : OracleWorld.Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      cachedFutureCoverage remaining key.parameter key.root result.2.1 result.2.2) ≤
      cachedFutureCoverage remaining key.parameter key.root state.1 state.2 +
        hashQueryCharge (freshFutureCoverageCharge remaining key.parameter
          (fixedSigningViews key.parameter state.1 key.root state.2)) state.1 input := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  have hbound := expected_cachedFutureCoverage_fixedLog_le remaining key.parameter key.root state.1 hfinite state.2 hsigned
    (OracleSpec.query input)
  have hquery : expectedQueryCharge
      (freshFutureCoverageCharge remaining key.parameter (fixedSigningViews key.parameter state.1 key.root state.2))
      (OracleSpec.query input) state.1 =
      hashQueryCharge (freshFutureCoverageCharge remaining key.parameter
        (fixedSigningViews key.parameter state.1 key.root state.2)) state.1 input := by
    rw [← bind_pure (OracleSpec.query input : OracleComp OracleWorld (OracleWorld.Range input)), expectedQueryCharge_query_bind]
    simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero]
  simpa only [simulateQ_spec_query, hquery, unloggedMappedAdversaryImpl, OracleSpec.Range,
    OracleSpec.add_apply_inl] using hbound

theorem expected_logTraced_sign_cachedFutureCoverage_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cachedFutureCoverage remaining key.parameter key.root result.2.1 result.2.2) ≤
      cachedFutureCoverage (remaining + 1) key.parameter key.root state.1 state.2 +
        expectedQueryCharge (freshFutureCoverageCharge remaining key.parameter
          (fixedSigningViews key.parameter state.1 key.root state.2)) (signWithView key message) state.1 +
        cachedFutureCoverageReuseCharge remaining key message state.1 state.2 q := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul]
  exact expected_signWithView_cachedFutureCoverage_le remaining key message state.1 (Finite.of_enncard_le hcache) state.2 hsigned q hq hcache

theorem expected_logTraced_cappedCachedFutureCoverage_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : (OracleWorld + SigningSpec).Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedCachedFutureCoverage key q result.2) ≤
      cappedCachedFutureCoverage key q state + futureCacheStepCharge key q state input := by
  by_cases hactive : ValidSigningStep state.2 input ∧ QueryCache.enncard state.1 ≤ q
  · rw [cappedCachedFutureCoverage, if_pos ⟨hactive.1.valid_before, hactive.2⟩, futureCacheStepCharge.eq_def, if_pos hactive]
    cases input with
    | inl world =>
        apply le_trans ?_ (expected_world_cachedFutureCoverage_le _ key state (Finite.of_enncard_le hactive.2) hsigned world)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.append_nil]
          unfold cappedCachedFutureCoverage
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive.1
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        rw [hremaining, ← add_assoc]
        apply le_trans ?_ (expected_logTraced_sign_cachedFutureCoverage_le _ key q hq state hsigned hactive.2 message)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          unfold cappedCachedFutureCoverage
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedCachedFutureCoverage key q result.2) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinactive : ¬ (SigningTranscript.Valid result.2.2 ∧ QueryCache.enncard result.2.1 ≤ q) := by
          intro hafter
          exact hactive ⟨(logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp hafter.1,
            (QueryCache.enncard_mono (logTracedMappedAdversaryImpl_cache_le key input state result hresult)).trans hafter.2⟩
        rw [cappedCachedFutureCoverage, if_neg hinactive, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    rw [hzero]
    exact bot_le

end SphincsSecurity.Concrete
