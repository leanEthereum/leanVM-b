import SphincsSecurity.Proof.MixedCacheEnvelope
import SphincsSecurity.Proof.AdaptiveCacheCapacity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cappedMixedCacheEnvelope (key : SecretKey) (q : Nat) (state : CoverLogState) (power order : Nat) : ENNReal :=
  if SigningTranscript.Valid state.2 then mixedCacheEnvelope key q 0 (signatureLimit - state.2.length) state power order else 0

theorem expected_logTraced_cappedMixedCacheEnvelope_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (input : (OracleWorld + SigningSpec).Domain)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key input).run state), QueryCache.enncard result.2.1 ≤ q)
    (power order : Nat) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedMixedCacheEnvelope key q result.2 power order) ≤ cappedMixedCacheEnvelope key q state power order := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedMixedCacheEnvelope, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        apply le_trans ?_ (expected_logTraced_world_mixedCacheEnvelope_le key q 0 (signatureLimit - state.2.length) state world hsigned hcap power order)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.append_nil]
          unfold cappedMixedCacheEnvelope
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        rw [hremaining]
        apply le_trans ?_ (expected_logTraced_sign_mixedCacheEnvelope_le key q 0 _ hq state hsigned hcache message hcap power order)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · apply mul_le_mul' le_rfl
          have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          unfold cappedMixedCacheEnvelope
          split_ifs
          · rw [hlog]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  · have hzero : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
        cappedMixedCacheEnvelope key q result.2 power order) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun h =>
            hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hresult).mp h)
        rw [cappedMixedCacheEnvelope, if_neg hinvalid, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
    rw [hzero]
    exact bot_le

theorem expected_adaptive_cappedMixedCacheEnvelope_le {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) (power order : Nat) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      cappedMixedCacheEnvelope key q result.2 power order) ≤ cappedMixedCacheEnvelope key q state power order := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key q input next state hbudget
      have hbefore := simulateQ_logTraced_initial_cache_bound key q (OracleSpec.query input >>= next) state hbudget
      have hstep := expected_logTraced_cappedMixedCacheEnvelope_le key q hq state hsigned hbefore input
        (fun result hresult => simulateQ_logTraced_initial_cache_bound key q (next result.1) result.2 (htail result hresult)) power order
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      apply le_trans ?_ hstep
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
      · exact mul_le_mul' le_rfl (ih result.1 result.2
          (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult) (htail result hresult))
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]

theorem expected_adaptive_validMixedDerivative_le {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run state),
      QueryCache.enncard result.2.1 ≤ q) (power order : Nat) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
      (if SigningTranscript.Valid result.2.2 then observedMixedDerivativeVector key 0 result.2 power order else 0)) ≤
      cappedMixedCacheEnvelope key q state power order := by
  apply le_trans ?_ (expected_adaptive_cappedMixedCacheEnvelope_le key q hq computation state hsigned hbudget power order)
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  unfold cappedMixedCacheEnvelope
  split_ifs
  · exact le_mixedRemainingEnvelope _ _ _ _ _ _ power order
  · exact le_rfl

theorem observedMixedDerivativeVector_zero_zero (key : SecretKey) (state : CoverLogState) :
    observedMixedDerivativeVector key 0 state 0 0 = observedLogOccupancy key state := by
  unfold observedMixedDerivativeVector
  have hzero : mixedIndexBinomialMoments key state.1 0 state = fun degree => observedLogBinomialOccupancy key degree state := by
    funext degree
    exact mixedIndexBinomialMoments_zero key state.1 state degree
  rw [hzero]
  change occupancyDerivativePolynomial 0 (fun degree => (binomialOccupancyMoment
    (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) degree : ENNReal)) 0 = _
  rw [← coverageOccupancyCompletion_eq_derivative, coverageOccupancyCompletion_zero]
  rfl

theorem expected_adaptive_validOccupancy_le_mixedEnvelope {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤
      mixedCacheEnvelope key q 0 signatureLimit (cache, []) 0 0 := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  simpa only [observedMixedDerivativeVector_zero_zero, cappedMixedCacheEnvelope,
    if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), List.length_nil, Nat.sub_zero] using
    expected_adaptive_validMixedDerivative_le key q hq computation (cache, []) hsigned hbudget 0 0

end SphincsSecurity.Concrete
