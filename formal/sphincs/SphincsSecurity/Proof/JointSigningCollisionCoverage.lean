import SphincsSecurity.Proof.SigningCollisionCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointCollisionCoverageStepEnvelope
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool) : ENNReal :=
  boundedUnionPotential (collisionStructuralEnvelope parameter root otsTable ftsTable state.1 result)
    (remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget
      (result.1.2, state.2 ++ signingLogFragment input result.1.1) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)

noncomputable def jointCollisionCoverageStepFailureCharge
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) : ENNReal :=
  ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    input frame state.1 false false] *
      (if result.2 then 1 - jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap budget input state result.1.2 else 0)

theorem expected_jointCollisionCoverage_step_le_record
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (state : CoverLogState)
    (henabled : frame.Enabled parameter otsTable ftsTable input state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input (some frame) state.1 false false] *
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget
          (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      (∑' result, Pr[= result | runFirstException (parentException parameter otsTable ftsTable)
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) state.1 none] *
          jointCollisionCoverageRecordPotential (secretKey parameter root otsTable ftsTable) cap budget
            (result.1.2, state.2 ++ signingLogFragment input result.1.1) result.2) +
        jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget input (some frame) state := by
  let exception := parentException parameter otsTable ftsTable
  let computation := stepWithFailure exception parameter root otsTable ftsTable input (some frame) state.1 false false
  let cost := jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap budget input state
  have hstep : (∑' result, Pr[= result | computation] *
      jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget
        (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      (∑' result, Pr[= result | computation] * cost result.1.2) +
        jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget input (some frame) state := by
    rw [jointCollisionCoverageStepFailureCharge, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro result
    rw [← mul_add]
    by_cases hr : result ∈ support computation
    · apply mul_le_mul' le_rfl
      cases hf : result.2 with
      | true =>
          simp only [if_true]
          rw [add_tsub_cancel_of_le (show cost result.1.2 ≤ 1 from boundedUnionPotential_le_one _ _)]
          exact jointCollisionCoveragePotential_le_one _ _ _ _ _ _
      | false =>
          have he : ¬ EarlyOtsParentTransition parameter otsTable ftsTable state.1 result.1.2.1.2 := by
            intro he
            have h := stepWithFailure_earlyOtsParent_imp_failed exception parameter root otsTable ftsTable input frame state.1
              henabled hcomputed result hr he
            simp [hf] at h
          simp only [Bool.false_eq_true, if_false, add_zero]
          apply boundedUnionPotential_mono_left
          cases hh : result.1.2.2 <;>
            simp [collisionStopPotential, collisionSurvivingStructuralPotential, collisionStructuralEnvelope, stepSigningLogState, he, hh]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  apply hstep.trans
  apply add_le_add ?_ le_rfl
  have hm := tsum_probOutput_map_mul computation Prod.fst (fun result => cost result.2)
  rw [stepWithFailure_project, step_expect_original] at hm
  have hflag := runFirstException_flag_projection exception
    (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) state.1 none
  simp only [Option.isSome_none] at hflag
  rw [← hm, ← hflag, tsum_probOutput_map_mul]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runFirstException exception
      (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) state.1 none)
  · apply mul_le_mul' le_rfl
    exact boundedUnionPotential_mono_left
      (collisionStructuralEnvelope_le_recordPotential parameter root otsTable ftsTable input state.1 result hr) _
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem expected_jointCollisionCoverage_sign_le_digestSelection
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (message : Message) (frame : Frame) (state : CoverLogState) (hfinite : Finite state.1)
    (henabled : frame.Enabled parameter otsTable ftsTable (.inr message) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inr message) (some frame) state.1 false false] *
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget
          (stepSigningLogState (.inr message) state.2 result) result.1.2.2 result.2) ≤
      (∑' result, Pr[= result | (simulateQ romImpl
        (signDigestLoop digestAttemptLimit (secretKey parameter root otsTable ftsTable) message)).run state.1] *
          (jointCollisionCoverageRecordPotential (secretKey parameter root otsTable ftsTable) cap budget
            (digestSelectionCoverageState message state.2 result) none +
            digestSelectionCollisionCharge (secretKey parameter root otsTable ftsTable) cap budget message state.2 result)) +
        jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget (.inr message) (some frame) state :=
  (expected_jointCollisionCoverage_step_le_record parameter root otsTable ftsTable cap budget (.inr message) frame state henabled hcomputed).trans
    (add_le_add (expected_sign_jointRecordPotential_le_digestSelection (secretKey parameter root otsTable ftsTable)
      cap budget message state.1 hfinite state.2) le_rfl)

theorem expected_jointCollisionCoverage_sign_le_risks
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (message : Message) (frame : Frame) (state : CoverLogState) (hfinite : Finite state.1)
    (henabled : frame.Enabled parameter otsTable ftsTable (.inr message) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inr message) (some frame) state.1 false false] *
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget
          (stepSigningLogState (.inr message) state.2 result) result.1.2.2 result.2) ≤
      boundedUnionPotential (collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) state.1 none)
        (digestSelectionCoverageRisk (secretKey parameter root otsTable ftsTable) cap budget message state.1 state.2) +
          digestSelectionCollisionRisk (secretKey parameter root otsTable ftsTable) cap budget message state.1 state.2 +
          jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget (.inr message) (some frame) state :=
  (expected_jointCollisionCoverage_step_le_record parameter root otsTable ftsTable cap budget (.inr message) frame state henabled hcomputed).trans
    (add_le_add (expected_sign_jointRecordPotential_le_risks (secretKey parameter root otsTable ftsTable)
      cap budget message state.1 hfinite state.2) le_rfl)

theorem jointCollisionCoverageStepFailureCharge_le_probFailure
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) :
    jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget input frame state ≤
      Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
        parameter root otsTable ftsTable input frame state.1 false false] := by
  rw [jointCollisionCoverageStepFailureCharge, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result.2 <;> simp only [Bool.false_eq_true, if_false, if_true, mul_zero, le_refl]
  exact mul_le_of_le_one_right' tsub_le_self

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
