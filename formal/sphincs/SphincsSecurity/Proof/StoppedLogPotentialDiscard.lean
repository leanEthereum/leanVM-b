import SphincsSecurity.Proof.StoppedTargetPotentials

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def discardedLogPotential (potential : CoverLogState → ENNReal) (state : CoverLogState)
    (beforeHit beforeFailed afterHit afterFailed : Bool) : ENNReal :=
  if beforeHit || beforeFailed then 0 else if afterHit || afterFailed then potential state else 0

noncomputable def expectedStepLogDiscard
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (potential : CoverLogState → ENNReal) : ENNReal :=
  ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
    discardedLogPotential potential (stepSigningLogState input state.2 result) hit failed result.1.2.2 result.2

theorem stepWithFailure_expect_surviving_add_discard
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (potential : CoverLogState → ENNReal) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential potential (stepSigningLogState input state.2 result) result.1.2.2 result.2) +
      expectedStepLogDiscard exception parameter root otsTable ftsTable input frame state hit failed potential =
      if hit || failed then 0 else
        ∑' result, Pr[= result | (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable) input).run state] *
          potential result.2 := by
  rw [expectedStepLogDiscard, ← ENNReal.tsum_add]
  by_cases hstop : (hit || failed) = true
  · rw [if_pos hstop]
    apply ENNReal.tsum_eq_zero.mpr
    intro result
    by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
    · rw [survivingLogPotential, if_pos (stepWithFailure_stopped exception parameter root otsTable ftsTable input frame state.1 hit failed hstop result hr),
        discardedLogPotential, if_pos hstop, mul_zero, zero_add]
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, zero_add]
  · rw [if_neg hstop, ← stepWithFailure_expect_logged exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed (fun _ => potential)]
    apply tsum_congr
    intro result
    rw [← mul_add]
    congr 1
    unfold survivingLogPotential discardedLogPotential
    rw [if_neg hstop]
    split_ifs <;> simp only [zero_add, add_zero]

theorem expectedStepLogDiscard_of_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (potential : CoverLogState → ENNReal) (hstop : (hit || failed) = true) :
    expectedStepLogDiscard exception parameter root otsTable ftsTable input frame state hit failed potential = 0 := by
  simp only [expectedStepLogDiscard, discardedLogPotential, if_pos hstop, mul_zero, tsum_zero]

theorem expectedStepLogDiscard_eq_prob_mul_of_constant
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (potential : CoverLogState → ENNReal) (value : ENNReal) (hactive : (hit || failed) = false)
    (hconstant : ∀ result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed),
      potential (stepSigningLogState input state.2 result) = value) :
    expectedStepLogDiscard exception parameter root otsTable ftsTable input frame state hit failed potential =
      Pr[fun result => (result.1.2.2 || result.2) = true |
        stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] * value := by
  rw [expectedStepLogDiscard, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
  · simp only [discardedLogPotential, hactive, Bool.false_eq_true, if_false, hconstant result hr]
    split_ifs <;> simp only [mul_zero, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hr]
    split_ifs <;> simp only [zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
