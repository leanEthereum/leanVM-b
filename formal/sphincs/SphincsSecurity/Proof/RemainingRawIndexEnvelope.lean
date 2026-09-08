import SphincsSecurity.Proof.AdaptiveRawIndex
import SphincsSecurity.Proof.StoppedExecutionReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def remainingRawIndexEnvelope (key : SecretKey) (cap budget signatures : Nat) (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures
    (observedRawIndexShapeVector key state)

theorem remainingRawIndexEnvelope_budget_mono (key : SecretKey) (cap signatures : Nat) (state : CoverLogState)
    {smaller larger : Nat} (hbudget : smaller ≤ larger)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingRawIndexEnvelope key cap smaller signatures state groups remaining ≤
      remainingRawIndexEnvelope key cap larger signatures state groups remaining :=
  targetShapeEnvelope_queries_mono _ _ _ signatures _ hbudget groups remaining hvalid

theorem remainingRawIndexEnvelope_le_cacheEnvelope (key : SecretKey) (cap budget signatures : Nat) (state : CoverLogState)
    (hbudget : budget ≤ messageCacheSlotCount key.parameter cap state.1)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingRawIndexEnvelope key cap budget signatures state groups remaining ≤ rawIndexCacheEnvelope key cap signatures state groups remaining :=
  remainingRawIndexEnvelope_budget_mono key cap signatures state hbudget groups remaining hvalid

theorem expected_randomOracle_remainingRawIndex_le (key : SecretKey) (cap budget signatures : Nat)
    (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      remainingRawIndexEnvelope key cap budget signatures (result.2, state.2) groups remaining) ≤
      remainingRawIndexEnvelope key cap (budget + 1) signatures state groups remaining := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    exact expected_fresh_rawIndexEnvelope_le key cap budget signatures state.1 state.2 input hfresh hsigned groups remaining hvalid
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    exact remainingRawIndexEnvelope_budget_mono key cap signatures state (Nat.le_succ _) groups remaining hvalid

theorem expected_logTraced_world_remainingRawIndex_le (key : SecretKey) (cap budget signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      remainingRawIndexEnvelope key cap budget signatures result.2 groups remaining) ≤
      remainingRawIndexEnvelope key cap (budget + signingExecutionHashCost (.inl input)) signatures state groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_remainingRawIndex_le key cap budget signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        remainingRawIndexEnvelope key cap budget signatures (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

noncomputable def cappedRemainingRawIndexEnvelope (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  if SigningTranscript.Valid state.2 then remainingRawIndexEnvelope key cap budget (signatureLimit - state.2.length) state groups remaining else 0

theorem expected_logTraced_cappedRemainingRawIndex_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedRemainingRawIndexEnvelope key cap (budget - signingExecutionHashCost input) result.2 groups remaining) ≤
      cappedRemainingRawIndexEnvelope key cap budget state groups remaining := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedRemainingRawIndexEnvelope, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        have hstep := expected_logTraced_world_remainingRawIndex_le key cap (budget - signingExecutionHashCost (.inl world))
          (signatureLimit - state.2.length) state world hsigned groups remaining hvalid
        rw [Nat.sub_add_cancel hcost] at hstep
        apply le_trans ?_ hstep
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
            obtain ⟨base, _, rfl⟩ := hr
            simp only [signingLogFragment, List.append_nil]
          apply mul_le_mul' le_rfl
          simp only [cappedRemainingRawIndexEnvelope, hlog, if_pos hactive.valid_before, le_refl]
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        have hstep := expected_logTraced_sign_rawIndexEnvelope_le key cap (budget - signingExecutionHashCost (.inr message))
          (signatureLimit - (state.2.length + 1)) hcap state hsigned hcache message groups remaining hvalid
        change (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
            remainingRawIndexEnvelope key cap (budget - signingExecutionHashCost (.inr message))
              (signatureLimit - (state.2.length + 1)) result.2 groups remaining) ≤
          remainingRawIndexEnvelope key cap (budget - signingExecutionHashCost (.inr message))
            (signatureLimit - (state.2.length + 1) + 1) state groups remaining at hstep
        rw [← hremaining] at hstep
        apply le_trans ?_ (hstep.trans (remainingRawIndexEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid))
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
        · have hlog : result.2.2.length = state.2.length + 1 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
            obtain ⟨base, _, rfl⟩ := hr
            simp only [signingLogFragment, List.length_append, List.length_singleton]
          apply mul_le_mul' le_rfl
          unfold cappedRemainingRawIndexEnvelope
          split_ifs
          · rw [hlog]
          · exact zero_le
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  · apply le_trans ?_ zero_le
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro result
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
    · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun hv =>
        hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hr).mp hv)
      rw [cappedRemainingRawIndexEnvelope, if_neg hinvalid, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

end SphincsSecurity.Concrete
