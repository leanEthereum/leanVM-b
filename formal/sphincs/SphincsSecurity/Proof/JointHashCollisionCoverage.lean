import SphincsSecurity.Proof.JointFailureCoverageOverlap
import SphincsSecurity.Proof.JointEncodingExhaustionReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointCollisionCoverageNonmessageHashCharge
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState) : ENNReal :=
  (1 - boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1) state) *
    (expectedPreExceptionCharge (parentException parameter otsTable ftsTable)
      (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
      (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) (.inl (.inr input))) state.1 false * (Fintype.card Digest : ENNReal)⁻¹) +
    jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap (budget - 1) (.inl (.inr input)) frame state

noncomputable def jointCollisionCoverageBudgetHashCharge
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState) : ENNReal :=
  if MessageHashInput parameter input then jointCollisionCoverageHashCharge parameter root otsTable ftsTable cap budget input frame state
  else jointCollisionCoverageNonmessageHashCharge parameter root otsTable ftsTable cap budget input frame state

theorem jointCollisionCoverageStepEnvelope_nonmessage
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hmessage : ¬ MessageHashInput parameter input)
    (result) (hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) frame state.1 false false)) :
    jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap budget (.inl (.inr input)) state result.1.2 =
      boundedUnionPotential (collisionStructuralEnvelope parameter root otsTable ftsTable state.1 result.1.2)
        (remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) := by
  have hc := remainingCoveragePotential_nonmessage_step (secretKey parameter root otsTable ftsTable) cap budget state input hsigned hmessage _
    (stepWithFailure_logged_support (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) frame state.1 state.2 false false result hr) ∅ Finset.univ
  dsimp only [stepSigningLogState] at hc
  rw [jointCollisionCoverageStepEnvelope, hc]

theorem expected_jointCollisionCoverage_nonmessage_add_credit_le_envelope
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (henabled : frame.Enabled parameter otsTable ftsTable (.inl (.inr input)) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hmessage : ¬ MessageHashInput parameter input) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) (some frame) state.1 false false] *
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
          (stepSigningLogState (.inl (.inr input)) state.2 result) result.1.2.2 result.2) +
      jointCollisionCoverageHashCredit (secretKey parameter root otsTable ftsTable) cap budget input state ≤
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
          jointCollisionCoverageNonmessageHashCharge parameter root otsTable ftsTable cap budget input (some frame) state := by
  let key := secretKey parameter root otsTable ftsTable
  let computation := stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) (some frame) state.1 false false
  have he := expected_jointCollisionCoverage_step_le_envelope parameter root otsTable ftsTable cap (budget - 1)
    (.inl (.inr input)) frame state henabled hcomputed
  have h := expected_boundedUnionPotential_add_decrease_le computation
    (fun result => collisionStructuralEnvelope parameter root otsTable ftsTable state.1 result.1.2)
    (collisionStructuralRecordPotential key state.1 none)
    (remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
    (remainingCoveragePotential key cap (budget - 1) state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) _
    (expected_collisionStructuralEnvelope_step_le parameter root otsTable ftsTable (.inl (.inr input)) (some frame) state.1 hfinite)
    (boundedRemainingCoveragePotential_budget_mono key cap state (Nat.sub_le _ _))
  have hm : (∑' result, Pr[= result | computation] *
      jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap (budget - 1) (.inl (.inr input)) state result.1.2) =
      ∑' result, Pr[= result | computation] *
        boundedUnionPotential (collisionStructuralEnvelope parameter root otsTable ftsTable state.1 result.1.2)
          (remainingCoveragePotential key cap (budget - 1) state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) := by
    apply tsum_congr
    intro result
    by_cases hr : result ∈ support computation
    · rw [jointCollisionCoverageStepEnvelope_nonmessage parameter root otsTable ftsTable cap (budget - 1) input (some frame) state hsigned hmessage result hr]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  rw [← hm] at h
  have hc := add_le_add he (le_refl (jointCollisionCoverageHashCredit key cap budget input state))
  rw [add_right_comm] at hc
  have hcredit : jointCollisionCoverageHashCredit key cap budget input state =
      (boundedRemainingCoveragePotential key cap budget state - boundedRemainingCoveragePotential key cap (budget - 1) state) *
        (1 - min 1 (collisionStructuralRecordPotential key state.1 none)) := by
    exact if_neg hmessage
  rw [hcredit] at hc ⊢
  exact (hc.trans (add_le_add h le_rfl)).trans_eq (add_assoc _ _ _)

theorem jointCollisionCoverageStepFailureCharge_nonmessage_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hmessage : ¬ MessageHashInput parameter input) :
    jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget (.inl (.inr input)) frame state ≤
      (1 - boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state) *
        Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
          parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 false false] := by
  let computation := stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) frame state.1 false false
  let value := boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state
  rw [jointCollisionCoverageStepFailureCharge]
  calc
    _ ≤ ∑' result, Pr[= result | computation] * (if result.2 then 1 - value else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · apply mul_le_mul' le_rfl
        cases hf : result.2 with
        | false => simp only [Bool.false_eq_true, if_false, le_refl]
        | true =>
            simp only [if_true]
            apply tsub_le_tsub_left
            rw [jointCollisionCoverageStepEnvelope_nonmessage parameter root otsTable ftsTable cap budget input frame state hsigned hmessage result hr]
            exact le_self_add
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      cases result.2 <;> simp only [Bool.false_eq_true, if_false, if_true, mul_zero]
      exact mul_comm _ _

theorem jointCollisionCoverageBudgetHashCharge_le_previous
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) :
    jointCollisionCoverageBudgetHashCharge parameter root otsTable ftsTable cap budget input frame state ≤
      jointCollisionCoverageHashCharge parameter root otsTable ftsTable cap budget input frame state := by
  by_cases hm : MessageHashInput parameter input
  · rw [jointCollisionCoverageBudgetHashCharge, if_pos hm]
  · rw [jointCollisionCoverageBudgetHashCharge, if_neg hm, jointCollisionCoverageNonmessageHashCharge,
      jointCollisionCoverageHashCharge, if_neg hm]
    exact (add_le_add le_rfl (jointCollisionCoverageStepFailureCharge_nonmessage_le parameter root otsTable ftsTable
      cap (budget - 1) input frame state hsigned hm)).trans_eq (by ring)

theorem jointCollisionCoverageNonmessageHashCharge_add_overlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState) :
    jointCollisionCoverageNonmessageHashCharge parameter root otsTable ftsTable cap budget input frame state +
      jointCollisionCoverageFailureOverlap parameter root otsTable ftsTable cap (budget - 1) (.inl (.inr input)) frame state =
        (1 - boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1) state) *
          (expectedPreExceptionCharge (parentException parameter otsTable ftsTable)
            (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
            (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) (.inl (.inr input))) state.1 false * (Fintype.card Digest : ENNReal)⁻¹) +
          Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
            parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 false false] := by
  rw [jointCollisionCoverageNonmessageHashCharge, add_assoc, jointCollisionCoverageStepFailureCharge_add_overlap]

theorem expected_jointCollisionCoverageBudget_hash_add_credit_le_refined
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (hbudget : 1 ≤ budget) (input : HashInput) (frame : Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (henabled : frame.Enabled parameter otsTable ftsTable (.inl (.inr input)) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) (some frame) state.1 false false] *
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
          (stepSigningLogState (.inl (.inr input)) state.2 result) result.1.2.2 result.2) +
      jointCollisionCoverageHashCredit (secretKey parameter root otsTable ftsTable) cap budget input state + encodingExhaustionTotalPotential state.1 ≤
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
          jointCollisionCoverageBudgetHashCharge parameter root otsTable ftsTable cap budget input (some frame) state := by
  by_cases hmessage : MessageHashInput parameter input
  · rw [jointCollisionCoverageBudgetHashCharge, if_pos hmessage]
    exact expected_jointCollisionCoverageBudget_hash_add_credit_le parameter root otsTable ftsTable cap budget hcap hbudget input frame state
      hfinite henabled hcomputed hsigned hcache
  · rw [jointCollisionCoverageBudgetHashCharge, if_neg hmessage]
    let key := secretKey parameter root otsTable ftsTable
    let computation := stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) (some frame) state.1 false false
    have h := expected_jointCollisionCoverage_nonmessage_add_credit_le_envelope parameter root otsTable ftsTable cap budget input frame state
      hfinite henabled hcomputed hsigned hmessage
    have hr := expected_stepWithFailure_exhaustionReserve_add_cost_eq (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) (some frame) state.1 false false budget 1 hbudget
    simp only [Nat.cast_one, one_mul] at hr
    calc
      _ = ((∑' result, Pr[= result | computation] * jointCollisionCoveragePotential key cap (budget - 1)
            (stepSigningLogState (.inl (.inr input)) state.2 result) result.1.2.2 result.2) +
          jointCollisionCoverageHashCredit key cap budget input state) +
          ((∑' result, Pr[= result | computation] * encodingExhaustionBudgetReserve (budget - 1) result.1.2.1.2) +
            encodingExhaustionTotalPotential state.1) := by
        simp only [jointCollisionCoverageBudgetPotential, mul_add, ENNReal.tsum_add, stepSigningLogState]
        dsimp only [key, computation]
        ring
      _ ≤ (jointCollisionCoveragePotential key cap budget state false false +
          jointCollisionCoverageNonmessageHashCharge parameter root otsTable ftsTable cap budget input (some frame) state) +
          encodingExhaustionBudgetReserve budget state.1 := add_le_add h hr.le
      _ = _ := by rw [jointCollisionCoverageBudgetPotential]; ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
