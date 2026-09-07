import SphincsSecurity.Proof.ObservedFutureCoverage
import SphincsSecurity.Proof.FrozenSigningLog

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def frozenTargetFutureCoverage (key : SecretKey) (q : Nat)
    (payload : HashInput) (target : FewTimeView) (state : CoverLogState) : ENNReal :=
  if QueryCache.enncard state.1 ≤ q then
    observedTargetFutureCoverage (signatureLimit - state.2.length) key.parameter key.root payload target
      state.1 (state.2.take signatureLimit) else 0

noncomputable def targetCoverageReuseStepCharge (key : SecretKey) (q : Nat)
    (payload : HashInput) (target : FewTimeView) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message =>
      if state.2.length < signatureLimit ∧ QueryCache.enncard state.1 ≤ q then
        targetFutureCoverageReuseCharge (signatureLimit - (state.2.length + 1)) key message
          state.1 state.2 payload target q else 0

theorem frozenTargetFutureCoverage_le_of_stable (key : SecretKey) (q : Nat)
    (payload : HashInput) (target : FewTimeView) (before after : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter before.1 key.root before.2)
    (hcache : before.1 ≤ after.1)
    (hlog : after.2.take signatureLimit = before.2.take signatureLimit)
    (hremaining : signatureLimit - after.2.length = signatureLimit - before.2.length) :
    frozenTargetFutureCoverage key q payload target after ≤ frozenTargetFutureCoverage key q payload target before := by
  by_cases hcap : QueryCache.enncard after.1 ≤ q
  · have hbefore := (QueryCache.enncard_mono hcache).trans hcap
    rw [frozenTargetFutureCoverage, if_pos hcap, frozenTargetFutureCoverage, if_pos hbefore, hlog, hremaining,
      observedTargetFutureCoverage_cache_stable _ _ _ _ _ _ _ _ hcache (hsigned.take signatureLimit)]
  · rw [frozenTargetFutureCoverage, if_neg hcap]
    exact bot_le

theorem expected_logTraced_sign_targetFutureCoverage_le (remaining : Nat) (key : SecretKey)
    (q : Nat) (hq : q ≤ 2 ^ 127) (payload : HashInput) (target : FewTimeView)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      observedTargetFutureCoverage remaining key.parameter key.root payload target result.2.1 result.2.2) ≤
      observedTargetFutureCoverage (remaining + 1) key.parameter key.root payload target state.1 state.2 +
        targetFutureCoverageReuseCharge remaining key message state.1 state.2 payload target q := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  rw [hrun, tsum_probOutput_map_mul]
  exact expected_signWithView_observedTargetFutureCoverage_le remaining key message state.1 state.2 payload target hsigned q hq hcache

theorem expected_logTraced_frozenTargetFutureCoverage_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (payload : HashInput) (target : FewTimeView) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : (OracleWorld + SigningSpec).Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      frozenTargetFutureCoverage key q payload target result.2) ≤
      frozenTargetFutureCoverage key q payload target state + targetCoverageReuseStepCharge key q payload target state input := by
  cases input with
  | inl world =>
      simp only [targetCoverageReuseStepCharge, add_zero]
      calc
        _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl world)).run state] *
            frozenTargetFutureCoverage key q payload target state := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
          · have hcache := logTracedMappedAdversaryImpl_cache_le key (.inl world) state result hresult
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            apply mul_le_mul' le_rfl
            apply frozenTargetFutureCoverage_le_of_stable key q payload target state _ hsigned hcache
            · simp only [signingLogFragment, List.append_nil]
            · simp only [signingLogFragment, List.append_nil]
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr message =>
      by_cases hactive : state.2.length < signatureLimit ∧ QueryCache.enncard state.1 ≤ q
      · have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        rw [frozenTargetFutureCoverage, if_pos hactive.2,
          List.take_of_length_le (Nat.le_of_lt hactive.1), targetCoverageReuseStepCharge, if_pos hactive, hremaining]
        apply le_trans ?_ (expected_logTraced_sign_targetFutureCoverage_le _ key q hq payload target state hsigned hactive.2 message)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · apply mul_le_mul' le_rfl
          have hlength : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
            obtain ⟨base, _, rfl⟩ := hresult
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          have hvalid : result.2.2.length ≤ signatureLimit := by omega
          unfold frozenTargetFutureCoverage
          split_ifs
          · rw [List.take_of_length_le hvalid, hlength]
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
      · rw [targetCoverageReuseStepCharge, if_neg hactive, add_zero]
        calc
          _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
              frozenTargetFutureCoverage key q payload target state := by
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
            · apply mul_le_mul' le_rfl
              have hcache := logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult
              by_cases hcap : QueryCache.enncard state.1 ≤ q
              · have hatlimit : signatureLimit ≤ state.2.length := Nat.le_of_not_gt (fun h => hactive ⟨h, hcap⟩)
                rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
                obtain ⟨base, _, rfl⟩ := hresult
                apply frozenTargetFutureCoverage_le_of_stable key q payload target state _ hsigned hcache
                · exact List.take_append_of_le_length hatlimit
                · simp only [signingLogFragment, List.length_append, List.length_singleton]
                  omega
              · have hafter : ¬ QueryCache.enncard result.2.1 ≤ q :=
                    fun h => hcap ((QueryCache.enncard_mono hcache).trans h)
                rw [frozenTargetFutureCoverage, if_neg hafter]
                exact bot_le
            · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete
