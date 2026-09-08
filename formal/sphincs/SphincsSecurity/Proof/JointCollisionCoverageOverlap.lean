import SphincsSecurity.Proof.SigningCollisionCoverageCharge
import SphincsSecurity.Proof.JointCollisionCoverageExecution
import SphincsSecurity.Proof.SharedFailureDiscardStopped

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointCollisionCoverageMessageFailureOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState) : ENNReal :=
  ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) frame state.1 false false] *
      if result.2 then boundedUnionPotential (collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) state.1 none)
        (remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
          (stepSigningLogState (.inl (.inr input)) state.2 result) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) else 0

private theorem expected_failureComplement_add_union (computation : SPMF α) (left : ENNReal) (right : α → ENNReal) (failed : α → Bool) :
    (1 - min 1 left) * (∑' result, Pr[= result | computation] * (if failed result then 1 - min 1 (right result) else 0)) +
      (∑' result, Pr[= result | computation] * (if failed result then boundedUnionPotential left (right result) else 0)) =
        Pr[fun result => failed result = true | computation] := by
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  cases failed result with
  | false => simp only [Bool.false_eq_true, if_false, mul_zero, add_zero]
  | true =>
      simp only [if_true]
      rw [mul_left_comm, ← mul_add, add_comm ((1 - min 1 left) * (1 - min 1 (right result))),
        boundedUnionPotential_add_complement, mul_one]

theorem jointCollisionCoverageMessageCharge_add_overlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState)
    (hmessage : MessageHashInput parameter input) :
    jointCollisionCoverageBudgetHashCharge parameter root otsTable ftsTable cap budget input frame state +
      jointCollisionCoverageMessageFailureOverlap parameter root otsTable ftsTable cap budget input frame state =
        Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
          parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 false false] := by
  simp only [jointCollisionCoverageBudgetHashCharge, jointCollisionCoverageHashCharge, if_pos hmessage]
  exact expected_failureComplement_add_union _ _ _ _

noncomputable def jointCollisionCoverageStepOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  if hit || failed then 0 else
    match input with
    | .inl (.inl _) => 0
    | .inl (.inr hash) =>
        if MessageHashInput parameter hash then jointCollisionCoverageMessageFailureOverlap parameter root otsTable ftsTable cap budget hash frame state
        else boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1) state *
          (expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
            (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) state.1 false * (Fintype.card Digest : ENNReal)⁻¹) +
          jointCollisionCoverageFailureOverlap parameter root otsTable ftsTable cap (budget - 1) input frame state
    | .inr message =>
        digestSelectionCollisionOverlap (secretKey parameter root otsTable ftsTable) cap (budget - signingExecutionHashCost input) message state.1 state.2 +
          jointCollisionCoverageFailureOverlap parameter root otsTable ftsTable cap (budget - signingExecutionHashCost input) input frame state

theorem jointCollisionCoverageStepCharge_add_overlap_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoverageBudgetStepCharge parameter root otsTable ftsTable cap budget input frame state hit failed +
      jointCollisionCoverageStepOverlap parameter root otsTable ftsTable cap budget input frame state hit failed ≤
        (if failed then 0 else expectedPreExceptionCharge (parentException parameter otsTable ftsTable)
          (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) state.1 hit) * (Fintype.card Digest : ENNReal)⁻¹ +
        sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (fun _ _ => 1)
          parameter root otsTable ftsTable input frame state.1 hit failed := by
  by_cases hstop : (hit || failed) = true
  · simp only [jointCollisionCoverageBudgetStepCharge, jointCollisionCoverageStepOverlap, hstop, if_true, zero_add, zero_le]
  · obtain ⟨rfl, rfl⟩ := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hstop)
    have hfailure : sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (fun _ _ => 1)
        parameter root otsTable ftsTable input frame state.1 false false =
        Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
          parameter root otsTable ftsTable input frame state.1 false false] := by
      simp only [sharedFailureDiscardStep, Bool.false_eq_true, if_false, probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero]
    rw [hfailure]
    simp only [jointCollisionCoverageBudgetStepCharge, jointCollisionCoverageStepOverlap, Bool.false_or, Bool.false_eq_true, if_false]
    cases input with
    | inl world =>
        cases world with
        | inl n => simp only [zero_add, zero_le]
        | inr hash =>
            dsimp only
            by_cases hmessage : MessageHashInput parameter hash
            · rw [if_pos hmessage, jointCollisionCoverageMessageCharge_add_overlap parameter root otsTable ftsTable cap budget hash frame state hmessage]
              exact le_add_self
            · rw [if_neg hmessage, jointCollisionCoverageBudgetHashCharge, if_neg hmessage, jointCollisionCoverageNonmessageHashCharge]
              rw [add_add_add_comm, ← add_mul, tsub_add_cancel_of_le (boundedRemainingCoveragePotential_le_one _ _ _ _), one_mul,
                jointCollisionCoverageStepFailureCharge_add_overlap]
    | inr message =>
        rw [add_add_add_comm, digestSelectionCollisionRisk_add_overlap, jointCollisionCoverageStepFailureCharge_add_overlap]
        exact le_rfl

noncomputable def expectedJointCollisionCoverageOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ _ => 0)
    (fun input _ next budget frame state hit failed =>
      jointCollisionCoverageStepOverlap parameter root otsTable ftsTable cap budget input frame state hit failed +
        ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input frame state.1 hit failed] * next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

theorem expectedJointCollisionCoverageCharge_add_overlap_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedJointCollisionCoverageCharge parameter root otsTable ftsTable cap computation budget frame state hit failed +
      expectedJointCollisionCoverageOverlap parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
      expectedSharedFailureDiscard (parentException parameter otsTable ftsTable) (fun _ _ => 1)
        parameter root otsTable ftsTable computation frame state.1 hit failed := by
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => simp [expectedJointCollisionCoverageCharge, expectedJointCollisionCoverageOverlap]
  | query_bind input next ih =>
      simp only [expectedJointCollisionCoverageCharge, expectedJointCollisionCoverageOverlap, construct_query_bind,
        expectedBeforeFailureCharge_query_bind, expectedSharedFailureDiscard_query_bind]
      rw [add_add_add_comm, ← ENNReal.tsum_add, add_mul, add_add_add_comm]
      apply add_le_add (jointCollisionCoverageStepCharge_add_overlap_le parameter root otsTable ftsTable cap budget input frame state hit failed)
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro result
      rw [← mul_add, mul_assoc, ← mul_add]
      exact mul_le_mul' le_rfl (ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
        (stepSigningLogState input state.2 result) result.1.2.2 result.2)

theorem expectedSharedFailureDiscard_one_eq_probEvent
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedSharedFailureDiscard exception (fun _ _ => 1) parameter root otsTable ftsTable computation frame cache hit failed =
      if failed then 0 else Pr[fun result => result.2 = true | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed] := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => cases failed <;> simp [runWithFailure_pure]
  | query_bind input next ih =>
      cases failed with
      | true => simp [expectedSharedFailureDiscard_failed_eq_zero]
      | false =>
          rw [expectedSharedFailureDiscard_query_bind, sharedFailureDiscardStep]
          simp only [Bool.false_eq_true, if_false, ih]
          rw [runWithFailure_query_bind, probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
          apply tsum_congr
          intro result
          cases hf : result.2 with
          | false => simp only [Bool.false_eq_true, if_false, mul_zero, zero_add]
          | true => simp only [if_true, probEvent_runWithFailure_failed_eq_one, mul_one, mul_zero, add_zero]

theorem expectedJointCollisionCoverageCharge_add_overlap_le_failure_add_collision
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedJointCollisionCoverageCharge parameter root otsTable ftsTable cap computation budget frame state hit failed +
      expectedJointCollisionCoverageOverlap parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
      expectedBeforeFailureCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame state.1 hit failed * (Fintype.card Digest : ENNReal)⁻¹ +
      (if failed then 0 else Pr[fun result => result.2 = true | runWithFailure (parentException parameter otsTable ftsTable)
        parameter root otsTable ftsTable computation frame state.1 hit failed]) := by
  simpa only [expectedSharedFailureDiscard_one_eq_probEvent] using
    expectedJointCollisionCoverageCharge_add_overlap_le parameter root otsTable ftsTable cap budget computation frame state hit failed

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
