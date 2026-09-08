import SphincsSecurity.Proof.StoppedSigningCoveragePayment

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem signingRemainingCoverageResidual_le_rawIndex (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    signingRemainingCoverageResidual key cap budget message state ≤
      (Fintype.card Index : ENNReal)⁻¹ * remainingRawIndexEnvelope key cap
        (budget - signingExecutionHashCost (.inr message)) (signatureLimit - (state.2.length + 1)) state ∅ Finset.univ *
          ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  have h := mul_le_mul' (expected_signWithView_newTargetEnvelopeCharge_le key message state.1 state.2 hsigned
    (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
    (budget - signingExecutionHashCost (.inr message)) (signatureLimit - (state.2.length + 1)) ∅ Finset.univ hvalid)
      (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  apply le_trans ?_ (h.trans_eq ?_)
  · unfold signingRemainingCoverageResidual signingNewTargetCoverageResidual
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro result
    rw [mul_assoc]
    exact mul_le_mul' le_rfl tsub_le_self
  · unfold remainingRawIndexEnvelope observedRawIndexShapeVector
    rw [targetShapeEnvelope_lift _ _ _ _ _ _ ∅ Finset.univ hvalid]

theorem signingRemainingCoverageResidual_le_refund_fraction (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hactive : ValidSigningStep state.2 (.inr message)) :
    signingRemainingCoverageResidual key cap budget message state ≤
      signingCoverageExecutionRefund key cap budget message state * ((2 ^ 22 : Nat) : ENNReal)⁻¹ := by
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  have hraw := (remainingRawIndexEnvelope_signatures_mono key cap (budget - signingExecutionHashCost (.inr message)) state
    (show signatureLimit - (state.2.length + 1) ≤ signatureLimit - state.2.length by omega) ∅ Finset.univ).trans
      (remainingRawIndexEnvelope_budget_mono key cap _ state (Nat.sub_le _ _) ∅ Finset.univ hvalid)
  have hleading : (Fintype.card Index : ENNReal)⁻¹ *
      cappedRemainingRawIndexEnvelope key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤
      signingCoverageExecutionRefund key cap budget message state * ((2 ^ 22 : Nat) : ENNReal)⁻¹ := by
    have hrate : (signingExecutionHashCost (.inr message) : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) * ((2 ^ 22 : Nat) : ENNReal)⁻¹ =
        (Fintype.card Index : ENNReal)⁻¹ := by
      have hcost : (signingExecutionHashCost (.inr message) : ENNReal) = 1024 * ((2 ^ 22 : Nat) : ENNReal) := by
        norm_num [signingExecutionHashCost, digestAttemptLimit]
      have hheight : ((2 ^ ftsTreeHeight : Nat) : ENNReal) = 1024 := by norm_num [ftsTreeHeight]
      rw [hcost, hheight]
      calc
        _ = (1024 * (1024 : ENNReal)⁻¹) * (((2 ^ 22 : Nat) : ENNReal) * ((2 ^ 22 : Nat) : ENNReal)⁻¹) *
            (Fintype.card Index : ENNReal)⁻¹ := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
          ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul, one_mul]
    unfold signingCoverageExecutionRefund coverageExecutionRefund
    rw [add_mul, add_mul]
    apply le_trans (le_of_eq ?_) le_self_add
    calc
      _ = cappedRemainingRawIndexEnvelope key cap budget state ∅ Finset.univ *
          ((signingExecutionHashCost (.inr message) : ENNReal) *
            (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) * ((2 ^ 22 : Nat) : ENNReal)⁻¹) *
          ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by rw [hrate]; ring
      _ = _ := by ring
  apply (signingRemainingCoverageResidual_le_rawIndex key cap budget message state hsigned).trans
  apply le_trans ?_ hleading
  rw [cappedRemainingRawIndexEnvelope, if_pos hactive.valid_before]
  exact mul_le_mul' (mul_le_mul' le_rfl hraw) le_rfl

namespace FtsProbeSimulation.JointOriginal

theorem paidRemainingCoverageStepResidual_le_refund_fraction
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) :
    paidRemainingCoverageStepResidual (secretKey parameter root otsTable ftsTable) cap budget input state hit failed ≤
      paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed *
        ((2 ^ 22 : Nat) : ENNReal)⁻¹ := by
  cases input with
  | inl world => exact zero_le
  | inr message =>
      simp only [paidRemainingCoverageStepResidual, paidRemainingCoverageStepRefund]
      split_ifs with hactive
      · unfold survivingLogPotential
        split_ifs
        · simp only [zero_mul, le_refl]
        · exact signingRemainingCoverageResidual_le_refund_fraction _ cap budget message state hsigned hactive
      · exact zero_le

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
