import SphincsSecurity.Proof.CachedSignerCoverStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev CoverLogState := QueryCache HashSpec × QueryLog SigningSpec

theorem logTracedMappedAdversaryImpl_run_map (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState) :
    (logTracedMappedAdversaryImpl key input).run state =
      (fun result => (result.1, (result.2, state.2 ++ signingLogFragment input result.1))) <$>
        (unloggedMappedAdversaryImpl key input).run state.1 := by
  rw [logTracedMappedAdversaryImpl, QueryImpl.extendState_apply]
  simp only [signingLogUpdate, bind_pure_comp]

theorem logTracedMappedAdversaryImpl_cache_le (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) : state.1 ≤ result.2.1 := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, hbase, rfl⟩ := hresult
  exact unloggedMappedAdversaryImpl_cache_le key input state.1 base hbase

theorem logTracedMappedAdversaryImpl_signingDigestsCached (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    SigningDigestsCached key.parameter result.2.1 key.root result.2.2 := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, hbase, rfl⟩ := hresult
  cases input with
  | inl world =>
      simpa only [signingLogFragment, List.append_nil] using hsigned.mono
        (unloggedMappedAdversaryImpl_cache_le key (.inl world) state.1 base hbase)
  | inr message =>
      change base ∈ support ((simulateQ romImpl (sign key message)).run state.1) at hbase
      rw [← simulateQ_signWithView_fst_run, support_map] at hbase
      obtain ⟨viewed, hviewed, rfl⟩ := hbase
      exact SigningDigestsCached.after_signing key message state.1 viewed.2 state.2 hsigned viewed.1.1 viewed.1.2 hviewed

noncomputable def worldCoverCharge (key : SecretKey) (state : CoverLogState) (input : OracleWorld.Domain) : ENNReal :=
  hashQueryCharge (fun cache input => freshCoverageCharge key.parameter
    (fixedSigningViews key.parameter state.1 key.root state.2) cache input * ((2 ^ 176 : Nat) : ENNReal)⁻¹) state.1 input

theorem probEvent_world_signingCacheCovered_le_charge (key : SecretKey) (state : CoverLogState)
    (hfinite : Finite state.1) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : OracleWorld.Domain) :
    Pr[fun result => SigningCacheCovered key.parameter key.root result.2 state.2 | (romImpl input).run state.1] ≤
      (if SigningCacheCovered key.parameter key.root state.1 state.2 then 1 else 0) + worldCoverCharge key state input := by
  let views := fixedSigningViews key.parameter state.1 key.root state.2
  let potential : QueryCache HashSpec → ENNReal := fun cache => if CoveredMessageCache key.parameter views cache then 1 else 0
  have hfixed := expected_potential_romImpl_le_charge potential
    (fun cache input => freshCoverageCharge key.parameter views cache input * ((2 ^ 176 : Nat) : ENNReal)⁻¹)
    (fun cache _ input hfresh => by
      simpa only [potential, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite] using
        probEvent_uniform_coveredMessageCache_le_charge key.parameter views cache input hfresh)
    input state.1 hfinite
  have hevent : Pr[fun result => SigningCacheCovered key.parameter key.root result.2 state.2 | (romImpl input).run state.1] =
      Pr[fun result => CoveredMessageCache key.parameter views result.2 | (romImpl input).run state.1] := by
    apply probEvent_congr' ?_ rfl
    intro result hresult
    have hcache := unloggedMappedAdversaryImpl_cache_le key (.inl input) state.1 result hresult
    unfold SigningCacheCovered
    rw [fixedSigningViews_cache_stable key.parameter key.root state.1 result.2 state.2 hcache hsigned]
  rw [hevent]
  simpa only [potential, views, SigningCacheCovered, worldCoverCharge, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite] using hfixed

noncomputable def interleavedCoverStepCharge (key : SecretKey) (q : Nat)
    (state : CoverLogState) (input : (OracleWorld + SigningSpec).Domain) : ENNReal :=
  if hcap : QueryCache.enncard state.1 ≤ q then
    match input with
    | .inl world => worldCoverCharge key state world
    | .inr message => observedSignerCoverCharge key message state.1 (Finite.of_enncard_le hcap) state.2 q
  else 0

def CappedSigningCacheCovered (key : SecretKey) (q : Nat) (state : CoverLogState) : Prop :=
  QueryCache.enncard state.1 ≤ q ∧ SigningCacheCovered key.parameter key.root state.1 state.2

theorem probEvent_interleaved_cappedCover_step_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (input : (OracleWorld + SigningSpec).Domain) :
    Pr[fun result => CappedSigningCacheCovered key q result.2 | (logTracedMappedAdversaryImpl key input).run state] ≤
      (if CappedSigningCacheCovered key q state then 1 else 0) + interleavedCoverStepCharge key q state input := by
  by_cases hcap : QueryCache.enncard state.1 ≤ q
  · by_cases hcovered : SigningCacheCovered key.parameter key.root state.1 state.2
    · rw [if_pos ⟨hcap, hcovered⟩]
      exact probEvent_le_one.trans le_self_add
    · rw [if_neg (fun h => hcovered h.2), zero_add, interleavedCoverStepCharge, dif_pos hcap]
      have hfinite := Finite.of_enncard_le hcap
      rw [logTracedMappedAdversaryImpl_run_map, probEvent_map]
      cases input with
      | inl world =>
          simp only [signingLogFragment, List.append_nil]
          have hbound := probEvent_world_signingCacheCovered_le_charge key state hfinite hsigned world
          rw [if_neg hcovered, zero_add] at hbound
          exact (probEvent_mono (fun _ _ h => h.2)).trans hbound
      | inr message =>
          simp only [signingLogFragment]
          have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
              (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
            (simulateQ_signWithView_fst_run key message state.1).symm
          rw [hrun, probEvent_map]
          exact (probEvent_mono (fun _ _ h => h.2)).trans
            (probEvent_signerCacheCover_le_charge key message state.1 hfinite state.2 hsigned hcovered q hq hcap)
  · rw [if_neg (fun h => hcap h.1), interleavedCoverStepCharge, dif_neg hcap, add_zero]
    exact (probEvent_eq_zero (fun result hresult hevent => hcap
      ((QueryCache.enncard_mono (logTracedMappedAdversaryImpl_cache_le key input state result hresult)).trans hevent.1))).le

end SphincsSecurity.Concrete
