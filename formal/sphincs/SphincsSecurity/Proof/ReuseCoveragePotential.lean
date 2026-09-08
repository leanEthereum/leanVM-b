import SphincsSecurity.Proof.ReuseCachedTargets
import SphincsSecurity.Proof.CappedReuseRawEnvelope
import SphincsSecurity.Proof.StoppedExecutionReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation.JointOriginal (unusedTargetExecutionCost targetArrivalHashCost_add_unused_execution)
attribute [local instance] Classical.propDecidable

noncomputable def cappedReuseCachedTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  if SigningTranscript.Valid state.2 then reuseCachedTargetEnvelope key reuse budget (signatureLimit - state.2.length) state groups remaining else 0

theorem reuseRawEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (signatures : Nat) (state : CoverLogState)
    {smaller larger : Nat} (hbudget : smaller ≤ larger)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    reuseRawEnvelope key reuse smaller signatures state groups remaining ≤ reuseRawEnvelope key reuse larger signatures state groups remaining :=
  targetShapeEnvelope_queries_mono _ _ _ _ _ hbudget groups remaining hvalid

theorem reuseRawEnvelope_signatures_mono (key : SecretKey) (reuse : ENNReal) (budget : Nat) (state : CoverLogState)
    {smaller larger : Nat} (h : smaller ≤ larger) :
    reuseRawEnvelope key reuse budget smaller state ≤ reuseRawEnvelope key reuse budget larger state :=
  Function.monotone_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ reuse f from
    fun _ _ _ => le_self_add.trans le_self_add) h _

theorem expected_logTraced_cappedReuseCachedTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : ∀ message, exactDigestReuseWeight key message state.1 ≤ reuse) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      cappedReuseCachedTargetEnvelope key reuse (budget - signingExecutionHashCost input) result.2 groups remaining) ≤
      cappedReuseCachedTargetEnvelope key reuse budget state groups remaining +
        (targetArrivalHashCost key.parameter state.1 input : ENNReal) *
          ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
            cappedReuseRawEnvelope key reuse budget state groups remaining) := by
  by_cases hactive : ValidSigningStep state.2 input
  · rw [cappedReuseCachedTargetEnvelope, if_pos hactive.valid_before, cappedReuseRawEnvelope, if_pos hactive.valid_before]
    cases input with
    | inl world =>
        have hstep := expected_logTraced_world_reuseCachedTarget_le key reuse (budget - signingExecutionHashCost (.inl world))
          (signatureLimit - state.2.length) state world hsigned groups remaining hvalid
        rw [Nat.sub_add_cancel hcost] at hstep
        apply le_trans ?_ (hstep.trans (add_le_add le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (reuseRawEnvelope_budget_mono key reuse _ state (Nat.sub_le _ _) groups remaining hvalid)))))
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key (.inl world)).run state)
        · have hlog : result.2.2 = state.2 := by
            rw [logTracedMappedAdversaryImpl_run_map, support_map] at hr
            obtain ⟨base, _, rfl⟩ := hr
            simp only [signingLogFragment, List.append_nil]
          apply mul_le_mul' le_rfl
          simp only [cappedReuseCachedTargetEnvelope, hlog, if_pos hactive.valid_before, le_refl]
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
        have hstep := expected_logTraced_sign_reuseCachedTarget_le key reuse (budget - signingExecutionHashCost (.inr message))
          (signatureLimit - (state.2.length + 1)) state hsigned message (hreuse message) groups remaining hvalid
        rw [← hremaining] at hstep
        have hraw := (reuseRawEnvelope_signatures_mono key reuse (budget - signingExecutionHashCost (.inr message)) state
          (show signatureLimit - (state.2.length + 1) ≤ signatureLimit - state.2.length by omega) groups remaining).trans
            (reuseRawEnvelope_budget_mono key reuse _ state (Nat.sub_le _ _) groups remaining hvalid)
        apply le_trans ?_ (hstep.trans (add_le_add
          (reuseCachedTargetEnvelope_budget_mono key reuse _ state (Nat.sub_le _ _) groups remaining hvalid) (mul_le_mul' le_rfl hraw)))
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
    by_cases hr : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
    · have hinvalid : ¬ SigningTranscript.Valid result.2.2 := fun hv =>
        hactive ((logTracedMappedAdversaryImpl_validSigningStep key input state result hr).mp hv)
      rw [cappedReuseCachedTargetEnvelope, if_neg hinvalid, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

noncomputable def reuseCoveragePotential (key : SecretKey) (reuse : ENNReal) (budget : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  cappedReuseCachedTargetEnvelope key reuse budget state groups remaining +
    cappedReuseRawEnvelope key reuse budget state groups remaining * (budget : ENNReal) *
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)

theorem expected_logTraced_reuseCoverage_add_unused_le (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : ∀ message, exactDigestReuseWeight key message state.1 ≤ reuse) (input : (OracleWorld + SigningSpec).Domain)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
      reuseCoveragePotential key reuse (budget - signingExecutionHashCost input) result.2 groups remaining) +
      cappedReuseRawEnvelope key reuse budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) ≤
      reuseCoveragePotential key reuse budget state groups remaining := by
  let rate : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹
  have ht := expected_logTraced_cappedReuseCachedTarget_le key reuse budget state hsigned hreuse input hcost groups remaining hvalid
  have hr := mul_le_mul' (mul_le_mul'
    (expected_logTraced_cappedReuseRawEnvelope_le key reuse budget state hsigned hreuse input hcost groups remaining hvalid)
    (le_refl ((budget - signingExecutionHashCost input : Nat) : ENNReal))) (le_refl rate)
  have hsum := add_le_add (add_le_add ht hr)
    (le_refl (cappedReuseRawEnvelope key reuse budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) * rate))
  have hcount : (targetArrivalHashCost key.parameter state.1 input : ENNReal) + (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) +
      ((budget - signingExecutionHashCost input : Nat) : ENNReal) = budget := by
    rw [← Nat.cast_add, targetArrivalHashCost_add_unused_execution, ← Nat.cast_add, Nat.add_sub_of_le hcost]
  calc
    _ ≤ (cappedReuseCachedTargetEnvelope key reuse budget state groups remaining +
        (targetArrivalHashCost key.parameter state.1 input : ENNReal) * (rate * cappedReuseRawEnvelope key reuse budget state groups remaining) +
        cappedReuseRawEnvelope key reuse budget state groups remaining * ((budget - signingExecutionHashCost input : Nat) : ENNReal) * rate) +
        cappedReuseRawEnvelope key reuse budget state groups remaining * (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) * rate := by
      simpa only [reuseCoveragePotential, rate, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right] using hsum
    _ = cappedReuseCachedTargetEnvelope key reuse budget state groups remaining + cappedReuseRawEnvelope key reuse budget state groups remaining *
        ((targetArrivalHashCost key.parameter state.1 input : ENNReal) + (unusedTargetExecutionCost key.parameter state.1 input : ENNReal) +
          ((budget - signingExecutionHashCost input : Nat) : ENNReal)) * rate := by ring
    _ = _ := by rw [hcount]; rfl

end SphincsSecurity.Concrete
