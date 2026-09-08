import SphincsSecurity.Proof.CollisionCoveragePotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def completedCoveragePotential (key : SecretKey) (state : CoverLogState) : ENNReal :=
  if SigningTranscript.Valid state.2 then
    cacheMessageWeight key.parameter (fun input target =>
      normalizedTargetLogProduct key state.1 state.2 (payloadOf input) target Finset.univ) state.1
  else 0

theorem completedCoveragePotential_le_remaining (key : SecretKey) (cap budget : Nat) (state : CoverLogState) :
    completedCoveragePotential key state ≤ remainingCoveragePotential key cap budget state ∅ Finset.univ := by
  apply le_trans ?_ le_self_add
  unfold completedCoveragePotential cappedRemainingCachedTargetEnvelope
  split_ifs
  · apply cacheMessageWeight_mono
    intro input target
    have h := le_targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight cap)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget
      (signatureLimit - state.2.length) (observedTargetShapeVector key (payloadOf input) target state) ∅ Finset.univ
    simpa only [remainingTargetEnvelope, observedTargetShapeVector, targetShapeMoments, Finset.prod_empty, one_mul] using h
  · exact le_rfl

theorem completedCoveragePotential_eq_zero_forecast (key : SecretKey) (cap : Nat) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) :
    completedCoveragePotential key state = remainingCachedTargetEnvelope key cap 0 0 state ∅ Finset.univ := by
  simp only [completedCoveragePotential, if_pos hvalid, remainingCachedTargetEnvelope,
    remainingTargetEnvelope, targetShapeEnvelope, Function.iterate_zero_apply, observedTargetShapeVector,
    targetShapeMoments, Finset.prod_empty, one_mul]

theorem one_le_completedCoveragePotential_scaled_of_covered (key : SecretKey) (state : CoverLogState)
    (hvalid : SigningTranscript.Valid state.2) (hcover : SigningCacheCovered key.parameter key.root state.1 state.2) :
    1 ≤ completedCoveragePotential key state * ((2 ^ 140 : Nat) : ENNReal)⁻¹ := by
  obtain ⟨input, output, hmessage, houtput, hadmissible, hcovered⟩ := hcover
  have hentry : ((2 ^ 140 : Nat) : ENNReal) ≤ cacheMessageEntryWeight key.parameter
      (fun query target => normalizedTargetLogProduct key state.1 state.2 (payloadOf query) target Finset.univ) state.1 input := by
    simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
    exact normalizedTargetLogProduct_full_ge_of_covered key state _ _ hcovered
  have htotal : ((2 ^ 140 : Nat) : ENNReal) ≤ completedCoveragePotential key state := by
    rw [completedCoveragePotential, if_pos hvalid]
    exact hentry.trans (ENNReal.le_tsum input)
  have hpositive : ((2 ^ 140 : Nat) : ENNReal) ≠ 0 := by norm_num
  have hfinite : ((2 ^ 140 : Nat) : ENNReal) ≠ ∞ := by finiteness
  rw [← ENNReal.mul_inv_cancel hpositive hfinite]
  exact mul_le_mul' htotal le_rfl

noncomputable def boundedCompletedCoveragePotential (key : SecretKey) (state : CoverLogState) : ENNReal :=
  min 1 (completedCoveragePotential key state * ((2 ^ 140 : Nat) : ENNReal)⁻¹)

theorem boundedCompletedCoveragePotential_le_remaining (key : SecretKey) (cap budget : Nat) (state : CoverLogState) :
    boundedCompletedCoveragePotential key state ≤ boundedRemainingCoveragePotential key cap budget state :=
  min_le_min le_rfl (mul_le_mul' (completedCoveragePotential_le_remaining key cap budget state) le_rfl)

namespace FtsProbeSimulation.JointOriginal

noncomputable def completedJointCollisionCoveragePotential (key : SecretKey) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  boundedUnionPotential (collisionStopPotential key state.1 hit failed)
    (completedCoveragePotential key state * ((2 ^ 140 : Nat) : ENNReal)⁻¹)

theorem completedJointCollisionCoveragePotential_le_one (key : SecretKey) (state : CoverLogState) (hit failed : Bool) :
    completedJointCollisionCoveragePotential key state hit failed ≤ 1 := boundedUnionPotential_le_one _ _

theorem completedJointCollisionCoveragePotential_eq_one_of_stopped (key : SecretKey) (state : CoverLogState)
    (hit failed : Bool) (hstop : (hit || failed) = true) :
    completedJointCollisionCoveragePotential key state hit failed = 1 := by
  apply boundedUnionPotential_eq_one_of_left
  cases hit <;> cases failed <;> simp_all [collisionStopPotential, collisionSurvivingStructuralPotential]

theorem completedJointCollisionCoveragePotential_eq_one_of_bad (key : SecretKey) (state : CoverLogState)
    (hfinite : Finite state.1) (hit failed : Bool)
    (hbad : Bad key.parameter key.otsSecret key.ftsSecret state.1 ∨ EncodingBad state.1 key) :
    completedJointCollisionCoveragePotential key state hit failed = 1 := by
  apply boundedUnionPotential_eq_one_of_left
  cases hit <;> cases failed <;> simp only [collisionStopPotential, collisionSurvivingStructuralPotential, Bool.false_eq_true, if_false, if_true, le_refl]
  exact collisionStructuralRecordPotential_none_ge_bad key state.1 hfinite hbad

theorem completedJointCollisionCoveragePotential_eq_one_of_covered (key : SecretKey) (state : CoverLogState)
    (hit failed : Bool) (hvalid : SigningTranscript.Valid state.2) (hcover : SigningCacheCovered key.parameter key.root state.1 state.2) :
    completedJointCollisionCoveragePotential key state hit failed = 1 :=
  boundedUnionPotential_eq_one_of_right _ _ (one_le_completedCoveragePotential_scaled_of_covered key state hvalid hcover)

noncomputable def jointCollisionCoverageCompletionCredit (key : SecretKey) (cap : Nat) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  (boundedRemainingCoveragePotential key cap 0 state - boundedCompletedCoveragePotential key state) *
    (1 - min 1 (collisionStopPotential key state.1 hit failed))

theorem completedJointCollisionCoverage_add_credit (key : SecretKey) (cap : Nat) (state : CoverLogState) (hit failed : Bool) :
    completedJointCollisionCoveragePotential key state hit failed + jointCollisionCoverageCompletionCredit key cap state hit failed =
      jointCollisionCoveragePotential key cap 0 state hit failed :=
  boundedUnionPotential_add_decrease _ _ _ (boundedCompletedCoveragePotential_le_remaining key cap 0 state)

theorem jointCollisionCoverageCompletionCredit_le_potential (key : SecretKey) (cap : Nat) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoverageCompletionCredit key cap state hit failed ≤ jointCollisionCoveragePotential key cap 0 state hit failed :=
  le_add_self.trans_eq (completedJointCollisionCoverage_add_credit key cap state hit failed)

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
