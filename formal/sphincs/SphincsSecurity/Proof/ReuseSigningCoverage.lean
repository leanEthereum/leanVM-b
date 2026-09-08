import SphincsSecurity.Proof.ReuseCoveragePotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation.JointOriginal (unusedTargetExecutionCost targetArrivalHashCost_add_unused_execution)
attribute [local instance] Classical.propDecidable

theorem expected_logTraced_sign_cappedReuseRaw_fixed_le (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : ∀ message, exactDigestReuseWeight key message state.1 ≤ reuse) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cappedReuseRawEnvelope key reuse budget result.2 groups remaining) ≤
      cappedReuseRawEnvelope key reuse budget state groups remaining := by
  by_cases hactive : ValidSigningStep state.2 (.inr message)
  · rw [cappedReuseRawEnvelope, if_pos hactive.valid_before]
    have hlength : state.2.length < signatureLimit := hactive
    have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
    have hstep := expected_logTraced_sign_reuseRawEnvelope_fixed_le key reuse budget (signatureLimit - (state.2.length + 1))
      state hsigned message (hreuse message) groups remaining hvalid
    change (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseRawEnvelope key reuse budget (signatureLimit - (state.2.length + 1)) result.2 groups remaining) ≤
      reuseRawEnvelope key reuse budget (signatureLimit - (state.2.length + 1) + 1) state groups remaining at hstep
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
      unfold cappedReuseRawEnvelope
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
      rw [cappedReuseRawEnvelope, if_neg hinvalid, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem expected_logTraced_sign_cappedReuseCachedTarget_fixed_le (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : ∀ message, exactDigestReuseWeight key message state.1 ≤ reuse) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      cappedReuseCachedTargetEnvelope key reuse budget result.2 groups remaining) ≤
      cappedReuseCachedTargetEnvelope key reuse budget state groups remaining +
        (targetArrivalHashCost key.parameter state.1 (.inr message) : ENNReal) *
          ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
            cappedReuseRawEnvelope key reuse budget state groups remaining) := by
  by_cases hactive : ValidSigningStep state.2 (.inr message)
  · rw [cappedReuseCachedTargetEnvelope, if_pos hactive.valid_before, cappedReuseRawEnvelope, if_pos hactive.valid_before]
    have hlength : state.2.length < signatureLimit := hactive
    have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
    have hrate : (1024 : ENNReal) * (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) =
        (Fintype.card Index : ENNReal)⁻¹ := by
      have hpow : ((2 ^ ftsTreeHeight : Nat) : ENNReal) = 1024 := by norm_num [ftsTreeHeight]
      rw [hpow, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    simp only [targetArrivalHashCost, Nat.cast_ofNat]
    rw [← mul_assoc, hrate]
    have hstep := expected_logTraced_sign_reuseCachedTarget_le key reuse budget
      (signatureLimit - (state.2.length + 1)) state hsigned message (hreuse message) groups remaining hvalid
    rw [← hremaining] at hstep
    have hraw := reuseRawEnvelope_signatures_mono key reuse budget state
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
      unfold cappedReuseCachedTargetEnvelope
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
      rw [cappedReuseCachedTargetEnvelope, if_neg hinvalid, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

noncomputable def reuseCoverageExecutionGap (key : SecretKey) (reuse : ENNReal) (budget cost arrivals : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  (cappedReuseCachedTargetEnvelope key reuse budget state groups remaining -
    cappedReuseCachedTargetEnvelope key reuse (budget - cost) state groups remaining) +
      (cappedReuseRawEnvelope key reuse budget state groups remaining -
        cappedReuseRawEnvelope key reuse (budget - cost) state groups remaining) * ((budget - cost + arrivals : Nat) : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)

theorem reuseCoveragePotential_add_executionGap (key : SecretKey) (reuse : ENNReal) (budget cost arrivals unused : Nat)
    (hcost : cost ≤ budget) (hcount : arrivals + unused = cost)
    (state : CoverLogState) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (cappedReuseCachedTargetEnvelope key reuse (budget - cost) state groups remaining +
      cappedReuseRawEnvelope key reuse (budget - cost) state groups remaining * ((budget - cost + arrivals : Nat) : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)) +
      (cappedReuseRawEnvelope key reuse budget state groups remaining * (unused : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
          reuseCoverageExecutionGap key reuse budget cost arrivals state groups remaining) =
      reuseCoveragePotential key reuse budget state groups remaining := by
  have ht : cappedReuseCachedTargetEnvelope key reuse (budget - cost) state groups remaining ≤
      cappedReuseCachedTargetEnvelope key reuse budget state groups remaining := by
    simp only [cappedReuseCachedTargetEnvelope]
    split_ifs
    · exact reuseCachedTargetEnvelope_budget_mono key reuse _ state (Nat.sub_le _ _) groups remaining hvalid
    · exact le_rfl
  have hr : cappedReuseRawEnvelope key reuse (budget - cost) state groups remaining ≤
      cappedReuseRawEnvelope key reuse budget state groups remaining := by
    simp only [cappedReuseRawEnvelope]
    split_ifs
    · exact reuseRawEnvelope_budget_mono key reuse _ state (Nat.sub_le _ _) groups remaining hvalid
    · exact le_rfl
  have hcast : ((budget - cost + arrivals : Nat) : ENNReal) + (unused : ENNReal) = budget := by
    rw [← Nat.cast_add, Nat.add_assoc, hcount, Nat.sub_add_cancel hcost]
  unfold reuseCoveragePotential reuseCoverageExecutionGap
  calc
    _ = (cappedReuseCachedTargetEnvelope key reuse (budget - cost) state groups remaining +
          (cappedReuseCachedTargetEnvelope key reuse budget state groups remaining -
            cappedReuseCachedTargetEnvelope key reuse (budget - cost) state groups remaining)) +
        (cappedReuseRawEnvelope key reuse (budget - cost) state groups remaining +
          (cappedReuseRawEnvelope key reuse budget state groups remaining -
            cappedReuseRawEnvelope key reuse (budget - cost) state groups remaining)) * ((budget - cost + arrivals : Nat) : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
        cappedReuseRawEnvelope key reuse budget state groups remaining * (unused : ENNReal) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) := by ring
    _ = _ := by
      rw [add_tsub_cancel_of_le ht, add_tsub_cancel_of_le hr, ← hcast]
      ring

theorem expected_logTraced_sign_reuseCoverage_add_executionGap_le (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : ∀ message, exactDigestReuseWeight key message state.1 ≤ reuse) (message : Message)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseCoveragePotential key reuse (budget - signingExecutionHashCost (.inr message)) result.2 groups remaining) +
      (cappedReuseRawEnvelope key reuse budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 (.inr message) : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) +
          reuseCoverageExecutionGap key reuse budget (signingExecutionHashCost (.inr message))
            (targetArrivalHashCost key.parameter state.1 (.inr message)) state groups remaining) ≤
      reuseCoveragePotential key reuse budget state groups remaining := by
  let rate : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹
  have ht := expected_logTraced_sign_cappedReuseCachedTarget_fixed_le key reuse (budget - signingExecutionHashCost (.inr message))
    state hsigned hreuse message groups remaining hvalid
  have hr := mul_le_mul' (mul_le_mul' (expected_logTraced_sign_cappedReuseRaw_fixed_le key reuse
    (budget - signingExecutionHashCost (.inr message)) state hsigned hreuse message groups remaining hvalid)
      (le_refl ((budget - signingExecutionHashCost (.inr message) : Nat) : ENNReal))) (le_refl rate)
  apply le_trans ?_ (le_of_eq (reuseCoveragePotential_add_executionGap key reuse budget
    (signingExecutionHashCost (.inr message)) (targetArrivalHashCost key.parameter state.1 (.inr message))
    (unusedTargetExecutionCost key.parameter state.1 (.inr message)) hcost
    (targetArrivalHashCost_add_unused_execution key.parameter state.1 (.inr message)) state groups remaining hvalid))
  apply add_le_add ?_ le_rfl
  calc
    _ ≤ (cappedReuseCachedTargetEnvelope key reuse (budget - signingExecutionHashCost (.inr message)) state groups remaining +
        (targetArrivalHashCost key.parameter state.1 (.inr message) : ENNReal) *
          (rate * cappedReuseRawEnvelope key reuse (budget - signingExecutionHashCost (.inr message)) state groups remaining)) +
        cappedReuseRawEnvelope key reuse (budget - signingExecutionHashCost (.inr message)) state groups remaining *
          ((budget - signingExecutionHashCost (.inr message) : Nat) : ENNReal) * rate := by
      simpa only [reuseCoveragePotential, rate, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right] using add_le_add ht hr
    _ = _ := by rw [Nat.cast_add]; dsimp only [rate]; ring

end SphincsSecurity.Concrete
