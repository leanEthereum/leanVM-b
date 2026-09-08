import SphincsSecurity.Proof.BoundedUnionPotential
import SphincsSecurity.Proof.CoverageStopHazard
import SphincsSecurity.Proof.RemainingCoverageProbability
import SphincsSecurity.Proof.JointProbeCollisionStructuralStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem remainingCoveragePotential_budget_mono (key : SecretKey) (cap : Nat) (state : CoverLogState)
    {smaller larger : Nat} (hbudget : smaller ≤ larger)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingCoveragePotential key cap smaller state groups remaining ≤ remainingCoveragePotential key cap larger state groups remaining := by
  unfold remainingCoveragePotential cappedRemainingCachedTargetEnvelope cappedRemainingRawIndexEnvelope
  split_ifs
  · exact add_le_add (remainingCachedTargetEnvelope_budget_mono key cap _ state hbudget groups remaining hvalid)
      (mul_le_mul' (mul_le_mul' (remainingRawIndexEnvelope_budget_mono key cap _ state hbudget groups remaining hvalid)
        (Nat.cast_le.mpr hbudget)) le_rfl)
  · simp only [zero_mul, add_zero, le_refl]

noncomputable def boundedRemainingCoveragePotential (key : SecretKey) (cap budget : Nat) (state : CoverLogState) : ENNReal :=
  min 1 (remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)

theorem boundedRemainingCoveragePotential_le_one (key : SecretKey) (cap budget : Nat) (state : CoverLogState) :
    boundedRemainingCoveragePotential key cap budget state ≤ 1 := min_le_left _ _

theorem boundedRemainingCoveragePotential_budget_mono (key : SecretKey) (cap : Nat) (state : CoverLogState)
    {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    boundedRemainingCoveragePotential key cap smaller state ≤ boundedRemainingCoveragePotential key cap larger state :=
  min_le_min le_rfl (mul_le_mul' (remainingCoveragePotential_budget_mono key cap state hbudget ∅ Finset.univ (by constructor <;> simp)) le_rfl)

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

noncomputable def collisionStopPotential (key : SecretKey) (cache : QueryCache HashSpec) (hit failed : Bool) : ENNReal :=
  if failed then 1 else collisionSurvivingStructuralPotential key cache hit failed

noncomputable def jointCollisionCoveragePotential (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (hit failed : Bool) : ENNReal :=
  boundedUnionPotential (collisionStopPotential key state.1 hit failed)
    (remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)

theorem jointCollisionCoveragePotential_le_one (key : SecretKey) (cap budget : Nat) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoveragePotential key cap budget state hit failed ≤ 1 := boundedUnionPotential_le_one _ _

theorem jointCollisionCoveragePotential_add_overlap (key : SecretKey) (cap budget : Nat) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoveragePotential key cap budget state hit failed +
      boundedRemainingCoveragePotential key cap budget state * min 1 (collisionStopPotential key state.1 hit failed) =
      boundedRemainingCoveragePotential key cap budget state + min 1 (collisionStopPotential key state.1 hit failed) :=
  boundedUnionPotential_add_product _ _

theorem jointCollisionCoveragePotential_initial (key : SecretKey) (q : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hcollision : collisionStructuralRecordPotential key cache none = 0) :
    jointCollisionCoveragePotential key q q (cache, []) false false = min 1 ((q : ENNReal) * initialRawIndexRate q) := by
  simp only [jointCollisionCoveragePotential, collisionStopPotential, collisionSurvivingStructuralPotential,
    Bool.false_eq_true, if_false, hcollision, boundedUnionPotential, min_zero, mul_zero, add_zero,
    remainingCoveragePotential_initial_scaled key q cache hnone]

theorem jointCollisionCoveragePotential_eq_one_of_stopped (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (hit failed : Bool) (hstop : (hit || failed) = true) :
    jointCollisionCoveragePotential key cap budget state hit failed = 1 := by
  apply boundedUnionPotential_eq_one_of_left
  cases hit <;> cases failed <;> simp_all [collisionStopPotential, collisionSurvivingStructuralPotential]

theorem jointCollisionCoveragePotential_eq_one_of_bad (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (hfinite : Finite state.1) (hit failed : Bool)
    (hbad : Bad key.parameter key.otsSecret key.ftsSecret state.1 ∨ EncodingBad state.1 key) :
    jointCollisionCoveragePotential key cap budget state hit failed = 1 := by
  apply boundedUnionPotential_eq_one_of_left
  cases hit <;> cases failed <;> simp only [collisionStopPotential, collisionSurvivingStructuralPotential, Bool.false_eq_true, if_false, if_true, le_refl]
  exact collisionStructuralRecordPotential_none_ge_bad key state.1 hfinite hbad

theorem jointCollisionCoveragePotential_eq_one_of_covered (key : SecretKey) (cap budget : Nat) (state : CoverLogState)
    (hit failed : Bool) (hvalid : SigningTranscript.Valid state.2) (hcover : SigningCacheCovered key.parameter key.root state.1 state.2) :
    jointCollisionCoveragePotential key cap budget state hit failed = 1 := by
  apply boundedUnionPotential_eq_one_of_right
  exact (one_le_cappedRemainingCachedTargetEnvelope_scaled_of_covered key cap budget state hvalid hcover).trans
    (mul_le_mul' le_self_add le_rfl)

theorem expected_collisionStopPotential_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input (some frame) cache false false] *
      collisionStopPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        (Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input (some frame) cache false false] +
          expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
            (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache false * (Fintype.card Digest : ENNReal)⁻¹) := by
  have h := add_le_add (le_refl (Pr[fun result => result.2 = true |
    stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable input (some frame) cache false false]))
      (expected_collisionSurvivingStructuralPotential_step_le parameter root otsTable ftsTable input frame cache hfinite henabled hcomputed)
  apply le_trans ?_ (h.trans_eq (add_left_comm _ _ _))
  apply le_of_eq
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  cases result.2 <;> simp only [collisionStopPotential, collisionSurvivingStructuralPotential, Bool.false_eq_true,
    if_true, if_false, mul_one, mul_zero, zero_add, add_zero]

theorem expected_jointCollisionCoverage_nonmessage_add_decrease_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (henabled : frame.Enabled parameter otsTable ftsTable (.inl (.inr input)) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hmessage : ¬ MessageHashInput parameter input) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) (some frame) state.1 false false] *
      jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
        (stepSigningLogState (.inl (.inr input)) state.2 result) result.1.2.2 result.2) +
      (boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state -
        boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1) state) *
          (1 - min 1 (collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) state.1 none)) ≤
      jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
        (1 - boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1) state) *
          (Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
            (.inl (.inr input)) (some frame) state.1 false false] +
            expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
              (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) (.inl (.inr input))) state.1 false * (Fintype.card Digest : ENNReal)⁻¹) := by
  let key := secretKey parameter root otsTable ftsTable
  have h := expected_boundedUnionPotential_add_decrease_le
    (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable (.inl (.inr input)) (some frame) state.1 false false)
    (fun result => collisionStopPotential key result.1.2.1.2 result.1.2.2 result.2)
    (collisionStructuralRecordPotential key state.1 none)
    (remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
    (remainingCoveragePotential key cap (budget - 1) state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) _
    (expected_collisionStopPotential_step_le parameter root otsTable ftsTable (.inl (.inr input)) frame state.1 hfinite henabled hcomputed)
    (boundedRemainingCoveragePotential_budget_mono key cap state (Nat.sub_le _ _))
  apply le_trans ?_ h
  apply add_le_add ?_ le_rfl
  apply le_of_eq
  apply tsum_congr
  intro result
  by_cases hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) (some frame) state.1 false false)
  · have hinvariant := remainingCoveragePotential_nonmessage_step key cap (budget - 1) state input hsigned hmessage _
      (stepWithFailure_logged_support (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
        (.inl (.inr input)) (some frame) state.1 state.2 false false result hr) ∅ Finset.univ
    dsimp only [key] at hinvariant
    rw [jointCollisionCoveragePotential, hinvariant]
    rfl
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end FtsProbeSimulation.JointOriginal

end SphincsSecurity.Concrete
