import SphincsSecurity.Proof.JointUniformCollisionCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem step_ftsFuel_ge_execution_budget
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (budget : Nat) (hfuel : budget ≤ frame.ftsFuel)
    (result) (hr : result ∈ support (step exception parameter root otsTable ftsTable input (some frame) cache hit))
    (finalFrame : Frame) (hframe : result.1 = some finalFrame) :
    budget - signingExecutionHashCost input ≤ finalFrame.ftsFuel := by
  by_cases h : frame.Enabled parameter otsTable ftsTable input cache hit
  · rw [step, dif_pos h, support_map] at hr
    obtain ⟨raw, _, rfl⟩ := hr
    cases hh : raw.2.2 with
    | true => simp [hh] at hframe
    | false =>
        simp only [hh, Bool.false_eq_true, if_false] at hframe
        rw [resume_ftsFuel parameter otsTable input frame.ftsFuel raw.1 finalFrame hframe]
        apply le_trans _ (remainingFtsFuel_ge parameter input frame.ftsFuel)
        cases input with
        | inl world =>
            cases world with
            | inl n => simpa only [signingExecutionHashCost, OtsProbeSimulation.IsOuterHash, if_false, Nat.sub_zero] using hfuel
            | inr input => exact Nat.sub_le_sub_right hfuel 1
        | inr message => exact (Nat.sub_le _ _).trans hfuel
  · rw [step, dif_neg h, support_map] at hr
    obtain ⟨original, _, rfl⟩ := hr
    contradiction

theorem jointCollisionCoveragePotential_budget_mono (key : SecretKey) (cap : Nat) (state : CoverLogState)
    (hit failed : Bool) {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    jointCollisionCoveragePotential key cap smaller state hit failed ≤ jointCollisionCoveragePotential key cap larger state hit failed :=
  boundedUnionPotential_mono_right _ (mul_le_mul'
    (remainingCoveragePotential_budget_mono key cap state hbudget ∅ Finset.univ (by constructor <;> simp)) le_rfl)

noncomputable def jointCollisionCoverageTerminalCredit (key : SecretKey) (cap budget : Nat) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  (jointCollisionCoveragePotential key cap budget state hit failed - jointCollisionCoveragePotential key cap 0 state hit failed) +
    encodingExhaustionBudgetReserve budget state.1

theorem jointCollisionCoverage_add_terminalCredit (key : SecretKey) (cap budget : Nat) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoveragePotential key cap 0 state hit failed + jointCollisionCoverageTerminalCredit key cap budget state hit failed =
      jointCollisionCoverageBudgetPotential key cap budget state hit failed := by
  rw [jointCollisionCoverageTerminalCredit, ← add_assoc, add_tsub_cancel_of_le
    (jointCollisionCoveragePotential_budget_mono key cap state hit failed (Nat.zero_le budget))]
  rfl

noncomputable def jointCollisionCoverageBudgetStepCharge
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  if hit || failed then 0 else
    match input with
    | .inl (.inl _) => 0
    | .inl (.inr hash) => jointCollisionCoverageHashCharge parameter root otsTable ftsTable cap budget hash frame state
    | .inr message =>
        digestSelectionCollisionRisk (secretKey parameter root otsTable ftsTable) cap
          (budget - signingExecutionHashCost (.inr message)) message state.1 state.2 +
        jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap
          (budget - signingExecutionHashCost (.inr message)) (.inr message) frame state

noncomputable def jointCollisionCoverageBudgetStepCredit (key : SecretKey) (cap budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  if hit || failed then 0 else
    match input with
    | .inl (.inl _) => 0
    | .inl (.inr hash) => jointCollisionCoverageHashCredit key cap budget hash state + encodingExhaustionTotalPotential state.1
    | .inr message => jointSigningCoverageCredit key cap budget message state

theorem expected_jointCollisionCoverageBudget_stopped_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hstop : (hit || failed) = true) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap (budget - signingExecutionHashCost input)
        (stepSigningLogState input state.2 result) result.1.2.2 result.2) ≤
      jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state hit failed := by
  simp only [jointCollisionCoverageBudgetPotential, mul_add, ENNReal.tsum_add]
  rw [jointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ _ _ hstop]
  apply add_le_add
  · calc
      _ ≤ ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] * 1 :=
        ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (jointCollisionCoveragePotential_le_one _ _ _ _ _ _)
      _ ≤ 1 := by simpa only [mul_one] using (tsum_probOutput_le_one (mx :=
        stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed))
  · change (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
        encodingExhaustionBudgetReserve (budget - signingExecutionHashCost input) result.1.2.1.2) ≤ _
    rw [expected_stepWithFailure_encodingExhaustionBudgetReserve]
    exact mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le _ _)) le_rfl

theorem expected_jointCollisionCoverageBudget_step_add_credit_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hfinite : Finite state.1)
    (hvalid : ∀ live, frame = some live → live.Valid parameter otsTable ftsTable state.1)
    (hhash : ∀ live, frame = some live → OtsProbeSimulation.IsOuterHash input → 0 < live.ftsFuel)
    (hcomputed : ∀ live, frame = some live → OtsProbeSimulation.DeferredComputationsClosed live.context)
    (hstate : frame.isNone = (hit || failed))
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost input ≤ budget) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame state.1 hit failed] * jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable)
        cap (budget - signingExecutionHashCost input) (stepSigningLogState input state.2 result) result.1.2.2 result.2) +
      jointCollisionCoverageBudgetStepCredit (secretKey parameter root otsTable ftsTable) cap budget input state hit failed ≤
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state hit failed +
          jointCollisionCoverageBudgetStepCharge parameter root otsTable ftsTable cap budget input frame state hit failed := by
  by_cases hstop : (hit || failed) = true
  · simp only [jointCollisionCoverageBudgetStepCredit, jointCollisionCoverageBudgetStepCharge, hstop, if_true, add_zero]
    exact expected_jointCollisionCoverageBudget_stopped_le _ parameter root otsTable ftsTable cap budget input frame state hit failed hstop
  · have hboth : hit = false ∧ failed = false := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hstop)
    rcases hboth with ⟨rfl, rfl⟩
    cases frame with
    | none => simp at hstate
    | some frame =>
        have henabled : frame.Enabled parameter otsTable ftsTable input state.1 false := ⟨rfl, hvalid frame rfl, hhash frame rfl⟩
        cases input with
        | inl world =>
            cases world with
            | inl n =>
                simpa only [jointCollisionCoverageBudgetStepCredit, jointCollisionCoverageBudgetStepCharge, Bool.false_or,
                  Bool.false_eq_true, if_false, signingExecutionHashCost, Nat.sub_zero, add_zero] using
                  expected_jointCollisionCoverageBudget_uniform_le parameter root otsTable ftsTable cap budget n frame state henabled
            | inr input =>
                simpa only [jointCollisionCoverageBudgetStepCredit, jointCollisionCoverageBudgetStepCharge, Bool.false_or,
                  Bool.false_eq_true, if_false, signingExecutionHashCost, add_assoc] using
                  expected_jointCollisionCoverageBudget_hash_add_credit_le parameter root otsTable ftsTable cap budget hcap hcost input frame state
                    hfinite henabled (hcomputed frame rfl) hsigned hcache
        | inr message =>
            simpa only [jointCollisionCoverageBudgetStepCredit, jointCollisionCoverageBudgetStepCharge, Bool.false_or,
              Bool.false_eq_true, if_false, add_assoc] using
              expected_jointCollisionCoverageBudget_sign_add_credit_le parameter root otsTable ftsTable cap budget hcap message frame state
                hfinite henabled (hcomputed frame rfl) hsigned hcache hcost

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
