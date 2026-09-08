import SphincsSecurity.Proof.JointCollisionCoverageOverlap

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem collisionStructuralEnvelope_message_le_before
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : HashInput) (frame : Option Frame) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hmessage : MessageHashInput parameter input) (result)
    (hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) frame cache false false)) :
    collisionStructuralEnvelope parameter root otsTable ftsTable cache result.1.2 ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none := by
  have ha := stepWithFailure_original_support (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) frame cache false false result hr
  have hno : ∀ answer, ¬ parentException parameter otsTable ftsTable cache input answer := by
    intro answer he
    obtain ⟨child, parent, hat, _⟩ := he.2.exists_full_parent_input parameter _ _ le_rfl
    exact hmessage.not_atPosition child hat
  change result.1.2 ∈ support (do
    let middle ← (randomOracle input).run cache
    pure (middle, false || queryException (parentException parameter otsTable ftsTable) cache (.inr input) middle.1)) at ha
  rw [mem_support_bind_iff] at ha
  obtain ⟨middle, hm, he⟩ := ha
  simp only [queryException, hno, and_false, decide_false, Bool.false_or, mem_support_pure_iff] at he
  have hhit : result.1.2.2 = false := congrArg Prod.snd he
  have hcache : result.1.2.1.2 = middle.2 := congrArg (fun current => current.1.2) he
  rw [collisionStructuralEnvelope, hhit, if_neg Bool.false_ne_true, hcache]
  exact collisionStructuralRecordPotential_message_query_le (secretKey parameter root otsTable ftsTable) cache hfinite input hmessage middle hm

theorem jointFailureOverlap_le_messageFailureOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : HashInput) (frame : Option Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (hmessage : MessageHashInput parameter input) :
    jointCollisionCoverageFailureOverlap parameter root otsTable ftsTable cap (budget - 1) (.inl (.inr input)) frame state ≤
      jointCollisionCoverageMessageFailureOverlap parameter root otsTable ftsTable cap budget input frame state := by
  rw [jointCollisionCoverageFailureOverlap, jointCollisionCoverageMessageFailureOverlap]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) frame state.1 false false)
  · apply mul_le_mul' le_rfl
    cases hf : result.2 with
    | false => simp only [Bool.false_eq_true, if_false, le_refl]
    | true =>
        simp only [if_true, jointCollisionCoverageStepEnvelope, stepSigningLogState]
        exact boundedUnionPotential_mono_left (collisionStructuralEnvelope_message_le_before parameter root otsTable ftsTable input frame state.1
          hfinite hmessage result hr) _
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem stepWithFailure_uniform_never_fails
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (n : Nat) (frame : Option Frame) (cache : QueryCache HashSpec) (result)
    (hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable (.inl (.inl n)) frame cache false false)) :
    result.2 = false := by
  cases frame with
  | none =>
      rw [stepWithFailure, support_map] at hr
      obtain ⟨original, _, rfl⟩ := hr
      rfl
  | some frame =>
      by_cases he : frame.Enabled parameter otsTable ftsTable (.inl (.inl n)) cache false
      · exact stepWithFailure_uniform_failed_eq_false exception parameter root otsTable ftsTable n frame cache he result hr
      · rw [stepWithFailure, dif_neg he, support_map] at hr
        obtain ⟨original, _, rfl⟩ := hr
        rfl

theorem sharedFailureDiscardStep_uniform_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (potential : QueryCache HashSpec → Bool → ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (n : Nat) (frame : Option Frame) (cache : QueryCache HashSpec) :
    sharedFailureDiscardStep exception potential parameter root otsTable ftsTable (.inl (.inl n)) frame cache false false = 0 := by
  rw [sharedFailureDiscardStep, if_neg Bool.false_ne_true]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable (.inl (.inl n)) frame cache false false)
  · rw [stepWithFailure_uniform_never_fails exception parameter root otsTable ftsTable n frame cache result hr, if_neg Bool.false_ne_true, mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

theorem sharedFailureDiscardStep_hit_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (potential : QueryCache HashSpec → Bool → ENNReal)
    (hz : ∀ cache, potential cache true = 0)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (failed : Bool) :
    sharedFailureDiscardStep exception potential parameter root otsTable ftsTable input frame cache true failed = 0 := by
  rw [sharedFailureDiscardStep]
  split_ifs
  · rfl
  · apply ENNReal.tsum_eq_zero.mpr
    intro result
    by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache true failed)
    · rw [stepWithFailure_hit_of_hit exception parameter root otsTable ftsTable input frame cache failed result hr, hz]
      simp only [ite_self, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

noncomputable def jointCollisionCoverageStepAfterParentRefund
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  if hit || failed then 0 else
    match input with
    | .inl (.inl _) => 0
    | .inl (.inr hash) =>
        (if MessageHashInput parameter hash then 0 else
          boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - 1) state *
            (expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
              (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) state.1 false * (Fintype.card Digest : ENNReal)⁻¹)) +
          jointFailureCoverageAfterParentRefund parameter root otsTable ftsTable cap (budget - 1) input frame state
    | .inr message =>
        digestSelectionCollisionOverlap (secretKey parameter root otsTable ftsTable) cap (budget - signingExecutionHashCost input) message state.1 state.2 +
          jointFailureCoverageAfterParentRefund parameter root otsTable ftsTable cap (budget - signingExecutionHashCost input) input frame state

theorem sharedParentDiscard_add_remainder_le_stepOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hfinite : Finite state.1)
    (hcache : ∀ result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame state.1 hit failed), QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable input frame state.1 hit failed * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
      jointCollisionCoverageStepAfterParentRefund parameter root otsTable ftsTable cap budget input frame state hit failed ≤
        jointCollisionCoverageStepOverlap parameter root otsTable ftsTable cap budget input frame state hit failed := by
  by_cases hstop : (hit || failed) = true
  · simp only [jointCollisionCoverageStepAfterParentRefund, jointCollisionCoverageStepOverlap, hstop, if_true]
    cases hf : failed with
    | true => simp only [sharedFailureDiscardStep, if_true, zero_mul, add_zero, le_refl]
    | false =>
        have hh : hit = true := by simpa only [hf, Bool.or_false] using hstop
        rw [hh, sharedFailureDiscardStep_hit_eq_zero _ _ (fun _ => rfl)]
        simp
  · obtain ⟨rfl, rfl⟩ := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hstop)
    simp only [jointCollisionCoverageStepAfterParentRefund, jointCollisionCoverageStepOverlap, Bool.false_or, Bool.false_eq_true, if_false]
    cases input with
    | inl world =>
        cases world with
        | inl n => simp only [sharedFailureDiscardStep_uniform_eq_zero, zero_mul, zero_add, le_refl]
        | inr hash =>
            dsimp only
            by_cases hmessage : MessageHashInput parameter hash
            · rw [if_pos hmessage, if_pos hmessage, zero_add]
              exact (sharedParentDiscard_add_coverageRemainder_le_jointFailureOverlap parameter root otsTable ftsTable cap (budget - 1)
                (.inl (.inr hash)) frame state hfinite hcache).trans
                (jointFailureOverlap_le_messageFailureOverlap parameter root otsTable ftsTable cap budget hash frame state hfinite hmessage)
            · rw [if_neg hmessage, if_neg hmessage, add_left_comm]
              exact add_le_add le_rfl (sharedParentDiscard_add_coverageRemainder_le_jointFailureOverlap parameter root otsTable ftsTable cap (budget - 1)
                (.inl (.inr hash)) frame state hfinite hcache)
    | inr message =>
        rw [add_left_comm]
        exact add_le_add le_rfl (sharedParentDiscard_add_coverageRemainder_le_jointFailureOverlap parameter root otsTable ftsTable cap
          (budget - signingExecutionHashCost (.inr message)) (.inr message) frame state hfinite hcache)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
