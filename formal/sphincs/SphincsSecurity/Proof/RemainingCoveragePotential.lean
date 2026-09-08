import SphincsSecurity.Proof.RemainingCachedTargets

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation.JointOriginal (unusedTargetExecutionCost targetArrivalHashCost_add_unused_execution)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cappedRemainingCachedTargetEnvelope (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  if SigningTranscript.Valid state.2 then remainingCachedTargetEnvelope key cap budget (signatureLimit - state.2.length) state groups remaining else 0

theorem remainingRawIndexEnvelope_signatures_mono (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    {smaller larger : Nat} (h : smaller ≤ larger) :
    remainingRawIndexEnvelope key cap budget smaller state ≤ remainingRawIndexEnvelope key cap budget larger state :=
  Function.monotone_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap) f from
    fun _ _ _ => le_self_add.trans le_self_add) h _

theorem expected_logTraced_cappedRemainingCachedTarget_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedRemainingCachedTargetEnvelope key cap (budget - signingExecutionHashCost input) result.2 groups remaining) ≤
      cappedRemainingCachedTargetEnvelope key cap budget state groups remaining +
        (targetArrivalHashCost key.parameter state.1 input : ENNReal) *
          ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
            cappedRemainingRawIndexEnvelope key cap budget state groups remaining) := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedRemainingCachedTargetEnvelope, if_pos hactive.valid_before, cappedRemainingRawIndexEnvelope, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        have hstep := expected_logTraced_world_remainingCachedTarget_le key cap (budget - signingExecutionHashCost (.inl world))
          (signatureLimit - state.2.length) state world hsigned groups remaining hvalid
        rw [Nat.sub_add_cancel hcost] at hstep
        apply le_trans ?_ (hstep.trans (add_le_add le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (remainingRawIndexEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid)))))
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
            obtain ⟨base, _, rfl⟩ := hr
            simp only [signingLogFragment, List.append_nil]
          apply mul_le_mul' le_rfl
          simp only [cappedRemainingCachedTargetEnvelope, hlog, if_pos hactive.valid_before, le_refl]
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    | inr message =>
        have hlength : state.2.length < signatureLimit := hactive
        have hremaining : signatureLimit - state.2.length = signatureLimit - (state.2.length + 1) + 1 := by omega
        have hrate : (1024 : ENNReal) * (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) =
            (Fintype.card Index : ENNReal)⁻¹ := by
          have hpow : ((2 ^ ftsTreeHeight : Nat) : ENNReal) = 1024 := by norm_num [ftsTreeHeight]
          rw [hpow, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        simp only [targetArrivalHashCost, Nat.cast_ofNat]
        rw [← mul_assoc, hrate]
        have hstep := expected_logTraced_sign_remainingCachedTarget_le key cap (budget - signingExecutionHashCost (.inr message))
          (signatureLimit - (state.2.length + 1)) hcap state hsigned hcache message groups remaining hvalid
        rw [← hremaining] at hstep
        have hraw := (remainingRawIndexEnvelope_signatures_mono key cap (budget - signingExecutionHashCost (.inr message)) state
          (show signatureLimit - (state.2.length + 1) ≤ signatureLimit - state.2.length by omega) groups remaining).trans
            (remainingRawIndexEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid)
        apply le_trans ?_ (hstep.trans (add_le_add
          (remainingCachedTargetEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) groups remaining hvalid) (mul_le_mul' le_rfl hraw)))
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
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
    · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun hv =>
        hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hr).mp hv)
      rw [cappedRemainingCachedTargetEnvelope, if_neg hinvalid, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

noncomputable def remainingCoveragePotential (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  cappedRemainingCachedTargetEnvelope key cap budget state groups remaining +
    cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (budget : ENNReal) *
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)

theorem expected_logTraced_remainingCoverage_add_unused_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      remainingCoveragePotential key cap (budget - signingExecutionHashCost input) result.2 groups remaining) +
      cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) ≤
      remainingCoveragePotential key cap budget state groups remaining := by
  let rate : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹
  have ht := expected_logTraced_cappedRemainingCachedTarget_le key cap budget hcap state hsigned hcache input hcost groups remaining hvalid
  have hr := mul_le_mul' (mul_le_mul'
    (expected_logTraced_cappedRemainingRawIndex_le key cap budget hcap state hsigned hcache input hcost groups remaining hvalid)
    (le_refl ((budget - signingExecutionHashCost input : Nat) : ENNReal))) (le_refl rate)
  have hsum := add_le_add (add_le_add ht hr)
    (le_refl (cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) * rate))
  have hcount : (targetArrivalHashCost key.parameter state.1 input : ENNReal) + (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) +
      ((budget - signingExecutionHashCost input : Nat) : ENNReal) = budget := by
    rw [← Nat.cast_add, targetArrivalHashCost_add_unused_execution, ← Nat.cast_add, Nat.add_sub_of_le hcost]
  calc
    _ ≤ (cappedRemainingCachedTargetEnvelope key cap budget state groups remaining +
        (targetArrivalHashCost key.parameter state.1 input : ENNReal) * (rate * cappedRemainingRawIndexEnvelope key cap budget state groups remaining) +
        cappedRemainingRawIndexEnvelope key cap budget state groups remaining * ((budget - signingExecutionHashCost input : Nat) : ENNReal) * rate) +
        cappedRemainingRawIndexEnvelope key cap budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) * rate := by
      simpa only [remainingCoveragePotential, rate, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right] using hsum
    _ = cappedRemainingCachedTargetEnvelope key cap budget state groups remaining + cappedRemainingRawIndexEnvelope key cap budget state groups remaining *
        ((targetArrivalHashCost key.parameter state.1 input : ENNReal) + (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) +
          ((budget - signingExecutionHashCost input : Nat) : ENNReal)) * rate := by ring
    _ = _ := by rw [hcount]; rfl

end SphincsSecurity.Concrete
