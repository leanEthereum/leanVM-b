import SphincsSecurity.Proof.ObservedOccupancy
import SphincsSecurity.Proof.InterleavedCoverStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def successfulSignerViewWeight (weight : FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : ENNReal :=
  match result.1.1, result.1.2 with
  | some _, some view => weight view
  | _, _ => 0

theorem successfulSignerViewWeight_eq_tsum (weight : FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) :
    successfulSignerViewWeight weight result =
      ∑' source, if SuccessfulSignerViewSatisfies (· = source) result then weight source else 0 := by
  rcases result with ⟨⟨signature, view⟩, cache⟩
  cases signature <;> cases view <;>
    simp [successfulSignerViewWeight, SuccessfulSignerViewSatisfies, Prod.mk.injEq]

theorem expected_successfulSignerViewWeight_eq (weight : FewTimeView → ENNReal)
    (computation : ProbComp ((Option Signature × Option FewTimeView) × QueryCache HashSpec)) :
    (∑' result, Pr[= result | computation] * successfulSignerViewWeight weight result) =
      ∑' source, Pr[SuccessfulSignerViewSatisfies (· = source) | computation] * weight source := by
  simp_rw [successfulSignerViewWeight_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro source
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  split_ifs <;> simp

theorem signWithView_observedOccupancy_eq (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
      (log ++ [⟨message, result.1.1⟩])) : ENNReal) =
        (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) : ENNReal) +
          successfulSignerViewWeight
            (fun source => (occupancyIncrementAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1 : ENNReal)) result := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root before result.2 log hcache hsigned
  cases hresponse : result.1.1 with
  | none =>
      rw [observedOptionalSigningViews_append_none _ _ _ _ (by simp [observedSigningView?]), hstable]
      simp only [successfulSignerViewWeight, hresponse, add_zero]
  | some signature =>
      have hresult' : ((some signature, result.1.2), result.2) ∈ support
          ((simulateQ romImpl (signWithView key message)).run before) := by
        have heq : result = ((some signature, result.1.2), result.2) := Prod.ext (Prod.ext hresponse rfl) rfl
        rwa [heq] at hresult
      obtain ⟨output, houtput, _, hview⟩ := signWithView_successful_cached_output key message before result.2 signature result.1.2 hresult'
      have hsource : observedSigningView? (messageAnswers key.parameter result.2) key.root ⟨message, some signature⟩ = some (hashOutputFewTimeView output) := by
        simp [observedSigningView?, messageAnswers, houtput]
      rw [observedOptionalSigningViews_append_some _ _ _ _ _ hsource, hstable, Nat.cast_add]
      simp only [successfulSignerViewWeight, hresponse, hview]

theorem expected_signWithView_observedOccupancy_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard before ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
        (log ++ [⟨message, result.1.1⟩])) : ENNReal)) ≤
      (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) : ENNReal) +
        (∑' index, Pr[= index | ($ᵗ Index : ProbComp Index)] *
          (occupancyIncrementAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index : ENNReal)) +
        (∑' source, cachedMessageEntryCountWhere before key.parameter key.root message (· = source) *
          (occupancyIncrementAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) source.1 : ENNReal)) * digestReuseWeight q := by
  let views := observedOptionalSigningViews (messageAnswers key.parameter before) key.root log
  let weight := fun source : FewTimeView => (occupancyIncrementAtIndex views source.1 : ENNReal)
  have heq : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter result.2) key.root
        (log ++ [⟨message, result.1.1⟩])) : ENNReal)) =
      ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ((coverageOccupancyMoment views : ENNReal) + successfulSignerViewWeight weight result) := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
    · rw [signWithView_observedOccupancy_eq key message before log hsigned result hresult]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  rw [heq]
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, expected_successfulSignerViewWeight_eq]
  apply (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl).trans
  exact (add_le_add le_rfl (expected_successfulSigner_occupancyIncrement_le views key message before q hq hcache)).trans_eq (add_assoc _ _ _).symm

theorem worldCoverCharge_le_observedOccupancy (key : SecretKey) (state : CoverLogState) (input : OracleWorld.Domain) :
    worldCoverCharge key state input ≤
      hashQueryCharge (fun cache input =>
        (if cache input = none ∧ FtsProbeSimulation.MessageHashInput key.parameter input then
          (coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2) : ENNReal) else 0) *
            ((2 ^ 176 : Nat) : ENNReal)⁻¹) state.1 input := by
  cases input with
  | inl _ =>
      dsimp only [worldCoverCharge, hashQueryCharge, Sum.elim]
      exact le_rfl
  | inr input =>
      simp only [worldCoverCharge, hashQueryCharge]
      exact mul_le_mul' (freshCoverageCharge_le_observedOccupancy _ _ _ _ _ _) le_rfl

noncomputable def observedLogOccupancy (key : SecretKey) (state : CoverLogState) : ENNReal :=
  coverageOccupancyMoment (observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2)

noncomputable def observedOccupancyStepCharge (key : SecretKey) (q : Nat) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl _ => 0
  | .inr message =>
      let views := observedOptionalSigningViews (messageAnswers key.parameter state.1) key.root state.2
      (∑' index, Pr[= index | ($ᵗ Index : ProbComp Index)] * (occupancyIncrementAtIndex views index : ENNReal)) +
        (∑' source, cachedMessageEntryCountWhere state.1 key.parameter key.root message (· = source) *
          (occupancyIncrementAtIndex views source.1 : ENNReal)) * digestReuseWeight q

theorem expected_logTraced_observedOccupancy_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (input : (OracleWorld + SigningSpec).Domain) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * observedLogOccupancy key result.2) ≤
      observedLogOccupancy key state + observedOccupancyStepCharge key q state input := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  cases input with
  | inl world =>
      simp only [signingLogFragment, List.append_nil, observedOccupancyStepCharge, add_zero]
      have heq : (∑' result, Pr[= result | (unloggedMappedAdversaryImpl key (.inl world)).run state.1] *
          observedLogOccupancy key (result.2, state.2)) =
          ∑' result, Pr[= result | (unloggedMappedAdversaryImpl key (.inl world)).run state.1] * observedLogOccupancy key state := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support ((unloggedMappedAdversaryImpl key (.inl world)).run state.1)
        · have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root state.1 result.2 state.2
            (unloggedMappedAdversaryImpl_cache_le key (.inl world) state.1 result hresult) hsigned
          simp only [observedLogOccupancy, hstable]
        · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
      rw [heq, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr message =>
      have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
          (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
        (simulateQ_signWithView_fst_run key message state.1).symm
      rw [hrun, tsum_probOutput_map_mul]
      simpa only [observedLogOccupancy, observedOccupancyStepCharge, signingLogFragment, add_assoc] using
        expected_signWithView_observedOccupancy_le key message state.1 state.2 hsigned q hq hcache

end SphincsSecurity.Concrete
