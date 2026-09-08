import SphincsSecurity.Proof.RemainingCoveragePotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation.JointOriginal (unusedTargetExecutionCost targetArrivalHashCost_add_unused_execution)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_logTraced_sign_cappedRemainingRawIndex_fixed_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cappedRemainingRawIndexEnvelope key cap budget result.2 groups remaining) ≤
      cappedRemainingRawIndexEnvelope key cap budget state groups remaining := by
  by_cases hactive : ValidSigningStep state.2 (.inr message)
  · rw [cappedRemainingRawIndexEnvelope, if_pos hactive.valid_before]
    have hlength : state.2.length < signatureLimit := hactive
    have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
    have hstep := expected_logTraced_sign_rawIndexEnvelope_le key cap budget (signatureLimit - (state.2.length + 1))
      hcap state hsigned hcache message groups remaining hvalid
    change (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      remainingRawIndexEnvelope key cap budget (signatureLimit - (state.2.length + 1)) result.2 groups remaining) ≤
      remainingRawIndexEnvelope key cap budget (signatureLimit - (state.2.length + 1) + 1) state groups remaining at hstep
    rw [← hremaining] at hstep
    apply le_trans ?_ hstep
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
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
    · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun hv =>
        hactive ((logTracedMappedAdversaryImpl_validSigningStep key (.inr message) state result hr).mp hv)
      rw [cappedRemainingRawIndexEnvelope, if_neg hinvalid, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expected_logTraced_sign_cappedRemainingCachedTarget_fixed_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cappedRemainingCachedTargetEnvelope key cap budget result.2 groups remaining) ≤
      cappedRemainingCachedTargetEnvelope key cap budget state groups remaining +
        (targetArrivalHashCost key.parameter state.1 (.inr message) : ENNReal) *
          ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
            cappedRemainingRawIndexEnvelope key cap budget state groups remaining) := by
  by_cases hactive : ValidSigningStep state.2 (.inr message)
  · rw [cappedRemainingCachedTargetEnvelope, if_pos hactive.valid_before, cappedRemainingRawIndexEnvelope, if_pos hactive.valid_before]
    have hlength : state.2.length < signatureLimit := hactive
    have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
    have hrate : (1024 : ENNReal) * (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) =
        (Fintype.card Index : ENNReal)⁻¹ := by
      have hpow : ((2 ^ ftsTreeHeight : Nat) : ENNReal) = 1024 := by norm_num [ftsTreeHeight]
      rw [hpow, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    simp only [targetArrivalHashCost, Nat.cast_ofNat]
    rw [← mul_assoc, hrate]
    have hstep := expected_logTraced_sign_remainingCachedTarget_le key cap budget
      (signatureLimit - (state.2.length + 1)) hcap state hsigned hcache message groups remaining hvalid
    rw [← hremaining] at hstep
    have hraw := remainingRawIndexEnvelope_signatures_mono key cap budget state
      (show signatureLimit - (state.2.length + 1) ≤ signatureLimit - state.2.length by omega) groups remaining
    apply le_trans ?_ (hstep.trans (add_le_add le_rfl (mul_le_mul' le_rfl hraw)))
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
    · have hlog : result.2.2.length = state.2.length + 1 := by
        rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
        obtain ⟨base, _, rfl⟩ := hr
        simp only [signingLogFragment, List.length_append, List.length_singleton]
      apply mul_le_mul' le_rfl
      unfold cappedRemainingCachedTargetEnvelope
      split_ifs
      · rw [hlog]
      · exact zero_le
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  · apply le_trans ?_ zero_le
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro result
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
    · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun hv =>
        hactive ((logTracedMappedAdversaryImpl_validSigningStep key (.inr message) state result hr).mp hv)
      rw [cappedRemainingCachedTargetEnvelope, if_neg hinvalid, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

noncomputable def remainingCoverageExecutionGap (key : SecretKey) (cap budget cost arrivals : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  (cappedRemainingCachedTargetEnvelope key cap budget state groups remaining -
    cappedRemainingCachedTargetEnvelope key cap (budget - cost) state groups remaining) +
      (cappedRemainingRawIndexEnvelope key cap budget state groups remaining -
        cappedRemainingRawIndexEnvelope key cap (budget - cost) state groups remaining) * ((budget - cost + arrivals : Nat) : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)

theorem remainingCoveragePotential_add_executionGap (key : SecretKey) (cap budget cost arrivals unused : Nat)
    (hcost : cost ≤ budget) (hcount : arrivals + unused = cost)
    (state : CoverLogState) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (cappedRemainingCachedTargetEnvelope key cap (budget - cost) state groups remaining +
      cappedRemainingRawIndexEnvelope key cap (budget - cost) state groups remaining * ((budget - cost + arrivals : Nat) : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)) +
      (cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unused : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
          remainingCoverageExecutionGap key cap budget cost arrivals state groups remaining) =
      remainingCoveragePotential key cap budget state groups remaining := by
  have ht : cappedRemainingCachedTargetEnvelope key cap (budget - cost) state groups remaining ≤
      cappedRemainingCachedTargetEnvelope key cap budget state groups remaining := by
    simp only [cappedRemainingCachedTargetEnvelope]
    split_ifs
    · exact remainingCachedTargetEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid
    · exact le_rfl
  have hr : cappedRemainingRawIndexEnvelope key cap (budget - cost) state groups remaining ≤
      cappedRemainingRawIndexEnvelope key cap budget state groups remaining := by
    simp only [cappedRemainingRawIndexEnvelope]
    split_ifs
    · exact remainingRawIndexEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid
    · exact le_rfl
  have hcast : ((budget - cost + arrivals : Nat) : ENNReal) + (unused : ENNReal) = budget := by
    rw [← Nat.cast_add, Nat.add_assoc, hcount, Nat.sub_add_cancel hcost]
  unfold remainingCoveragePotential remainingCoverageExecutionGap
  calc
    _ = (cappedRemainingCachedTargetEnvelope key cap (budget - cost) state groups remaining +
          (cappedRemainingCachedTargetEnvelope key cap budget state groups remaining -
            cappedRemainingCachedTargetEnvelope key cap (budget - cost) state groups remaining)) +
        (cappedRemainingRawIndexEnvelope key cap (budget - cost) state groups remaining +
          (cappedRemainingRawIndexEnvelope key cap budget state groups remaining -
            cappedRemainingRawIndexEnvelope key cap (budget - cost) state groups remaining)) * ((budget - cost + arrivals : Nat) : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
        cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unused : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) := by ring
    _ = _ := by
      rw [add_tsub_cancel_of_le ht, add_tsub_cancel_of_le hr, ← hcast]
      ring

theorem expected_logTraced_sign_remainingCoverage_add_executionGap_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      remainingCoveragePotential key cap (budget - signingExecutionHashCost (.inr message)) result.2 groups remaining) +
      (cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 (.inr message) : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
          remainingCoverageExecutionGap key cap budget (signingExecutionHashCost (.inr message))
            (targetArrivalHashCost key.parameter state.1 (.inr message)) state groups remaining) ≤
      remainingCoveragePotential key cap budget state groups remaining := by
  let rate : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹
  have ht := expected_logTraced_sign_cappedRemainingCachedTarget_fixed_le key cap (budget - signingExecutionHashCost (.inr message))
    hcap state hsigned hcache message groups remaining hvalid
  have hr := mul_le_mul' (mul_le_mul' (expected_logTraced_sign_cappedRemainingRawIndex_fixed_le key cap
    (budget - signingExecutionHashCost (.inr message)) hcap state hsigned hcache message groups remaining hvalid)
      (le_refl ((budget - signingExecutionHashCost (.inr message) : Nat) : ENNReal))) (le_refl rate)
  apply le_trans ?_ (le_of_eq (remainingCoveragePotential_add_executionGap key cap budget
    (signingExecutionHashCost (.inr message)) (targetArrivalHashCost key.parameter state.1 (.inr message))
    (unusedTargetExecutionCost key.parameter state.1 (.inr message)) hcost
    (targetArrivalHashCost_add_unused_execution key.parameter state.1 (.inr message)) state groups remaining hvalid))
  apply add_le_add ?_ le_rfl
  calc
    _ ≤ (cappedRemainingCachedTargetEnvelope key cap (budget - signingExecutionHashCost (.inr message)) state groups remaining +
        (targetArrivalHashCost key.parameter state.1 (.inr message) : ENNReal) *
          (rate * cappedRemainingRawIndexEnvelope key cap (budget - signingExecutionHashCost (.inr message)) state groups remaining)) +
        cappedRemainingRawIndexEnvelope key cap (budget - signingExecutionHashCost (.inr message)) state groups remaining *
          ((budget - signingExecutionHashCost (.inr message) : Nat) : ENNReal) * rate := by
      simpa only [remainingCoveragePotential, rate, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right] using add_le_add ht hr
    _ = _ := by rw [Nat.cast_add]; dsimp only [rate]; ring

end SphincsSecurity.Concrete
