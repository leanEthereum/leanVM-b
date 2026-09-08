import SphincsSecurity.Proof.JointSigningBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_logTraced_encodingExhaustionTotalPotential (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * encodingExhaustionTotalPotential result.2.1) =
      encodingExhaustionTotalPotential state.1 := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul, unloggedMappedAdversaryImpl_eq_simulateQ_expanded]
  exact expected_encodingExhaustionTotalPotential_run _ _

noncomputable def encodingExhaustionBudgetReserve (budget : Nat) (cache : QueryCache HashSpec) : ENNReal :=
  (budget : ENNReal) * encodingExhaustionTotalPotential cache

theorem encodingExhaustionBudgetReserve_initial_le (budget : Nat) :
    encodingExhaustionBudgetReserve budget ∅ ≤ (budget : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ :=
  mul_le_mul' le_rfl encodingExhaustionTotalPotential_empty_le_inv216

namespace FtsProbeSimulation.JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem expected_stepWithFailure_encodingExhaustionTotalPotential
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
      encodingExhaustionTotalPotential result.1.2.1.2) = encodingExhaustionTotalPotential cache := by
  have h := stepWithFailure_expect_logged exception parameter root otsTable ftsTable input frame cache [] hit failed
    (fun _ state => encodingExhaustionTotalPotential state.1)
  exact h.trans (expected_logTraced_encodingExhaustionTotalPotential _ _ _)

theorem expected_stepWithFailure_encodingExhaustionBudgetReserve
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) (budget : Nat) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
      encodingExhaustionBudgetReserve budget result.1.2.1.2) = encodingExhaustionBudgetReserve budget cache := by
  unfold encodingExhaustionBudgetReserve
  calc
    _ = (budget : ENNReal) * ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
        encodingExhaustionTotalPotential result.1.2.1.2 := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      ring
    _ = _ := by rw [expected_stepWithFailure_encodingExhaustionTotalPotential]

theorem expected_stepWithFailure_exhaustionReserve_add_cost_eq
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (budget cost : Nat) (hcost : cost ≤ budget) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed] *
      encodingExhaustionBudgetReserve (budget - cost) result.1.2.1.2) +
      (cost : ENNReal) * encodingExhaustionTotalPotential cache = encodingExhaustionBudgetReserve budget cache := by
  rw [expected_stepWithFailure_encodingExhaustionBudgetReserve, encodingExhaustionBudgetReserve,
    encodingExhaustionBudgetReserve, ← add_mul, ← Nat.cast_add, Nat.sub_add_cancel hcost]

theorem expected_sign_exhaustionReserve_add_charge_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (message : Message) (frame : Option Frame) (cache : QueryCache HashSpec) (budget : Nat)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inr message) frame cache false false] *
        encodingExhaustionBudgetReserve (budget - signingExecutionHashCost (.inr message)) result.1.2.1.2) +
      (1 - min 1 (collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none)) *
        encodingExhaustionTotalPotential cache ≤ encodingExhaustionBudgetReserve budget cache := by
  have hpositive : (1 : ENNReal) ≤ (signingExecutionHashCost (.inr message) : ENNReal) := by
    exact_mod_cast (show 1 ≤ signingExecutionHashCost (.inr message) by change 1 ≤ digestAttemptLimit; decide)
  exact (add_le_add le_rfl (mul_le_mul' (tsub_le_self.trans hpositive) le_rfl)).trans_eq
    (expected_stepWithFailure_exhaustionReserve_add_cost_eq (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inr message) frame cache false false budget _ hcost)

noncomputable def jointCollisionCoverageBudgetPotential (key : SecretKey) (cap budget : Nat) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  jointCollisionCoveragePotential key cap budget state hit failed + encodingExhaustionBudgetReserve budget state.1

theorem jointCollisionCoverageBudgetPotential_terminal (key : SecretKey) (cap : Nat) (state : CoverLogState) (hit failed : Bool) :
    jointCollisionCoverageBudgetPotential key cap 0 state hit failed = jointCollisionCoveragePotential key cap 0 state hit failed := by
  simp only [jointCollisionCoverageBudgetPotential, encodingExhaustionBudgetReserve, Nat.cast_zero, zero_mul, add_zero]

theorem jointCollisionCoverageBudgetPotential_initial (key : SecretKey) (q : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hcollision : collisionStructuralRecordPotential key cache none = 0) :
    jointCollisionCoverageBudgetPotential key q q (cache, []) false false =
      min 1 ((q : ENNReal) * initialRawIndexRate q) + encodingExhaustionBudgetReserve q cache := by
  rw [jointCollisionCoverageBudgetPotential, jointCollisionCoveragePotential_initial key q cache hnone hcollision]

theorem expected_jointCollisionCoverageBudget_sign_add_credit_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (message : Message) (frame : Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (henabled : frame.Enabled parameter otsTable ftsTable (.inr message) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inr message) (some frame) state.1 false false] *
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap (budget - signingExecutionHashCost (.inr message))
          (stepSigningLogState (.inr message) state.2 result) result.1.2.2 result.2) +
      jointSigningCoverageCredit (secretKey parameter root otsTable ftsTable) cap budget message state ≤
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
          digestSelectionCollisionRisk (secretKey parameter root otsTable ftsTable) cap (budget - signingExecutionHashCost (.inr message)) message state.1 state.2 +
          jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap (budget - signingExecutionHashCost (.inr message))
            (.inr message) (some frame) state := by
  let computation := stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inr message) (some frame) state.1 false false
  let key := secretKey parameter root otsTable ftsTable
  let rest := budget - signingExecutionHashCost (.inr message)
  let reserve := ∑' result, Pr[= result | computation] * encodingExhaustionBudgetReserve rest result.1.2.1.2
  have hstep := expected_jointCollisionCoverage_sign_add_credit_le parameter root otsTable ftsTable cap budget hcap message frame state
    hfinite henabled hcomputed hsigned hcache hcost
  have hreserve := expected_sign_exhaustionReserve_add_charge_le parameter root otsTable ftsTable message (some frame) state.1 budget hcost
  have h := add_le_add hstep (le_refl reserve)
  calc
    _ = ((∑' result, Pr[= result | computation] * jointCollisionCoveragePotential key cap rest
          (stepSigningLogState (.inr message) state.2 result) result.1.2.2 result.2) +
        jointSigningCoverageCredit key cap budget message state) + reserve := by
      simp only [jointCollisionCoverageBudgetPotential, mul_add, ENNReal.tsum_add]
      change (_ + reserve) + _ = (_ + _) + reserve
      ac_rfl
    _ ≤ (jointCollisionCoveragePotential key cap budget state false false +
          (1 - min 1 (collisionStructuralRecordPotential key state.1 none)) * encodingExhaustionTotalPotential state.1 +
          digestSelectionCollisionRisk key cap rest message state.1 state.2 +
          jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap rest (.inr message) (some frame) state) + reserve := h
    _ = (jointCollisionCoveragePotential key cap budget state false false +
        (reserve + (1 - min 1 (collisionStructuralRecordPotential key state.1 none)) * encodingExhaustionTotalPotential state.1)) +
        digestSelectionCollisionRisk key cap rest message state.1 state.2 +
        jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap rest (.inr message) (some frame) state := by ring
    _ ≤ _ := add_le_add (add_le_add (add_le_add le_rfl hreserve) le_rfl) le_rfl

theorem expected_jointCollisionCoverageBudget_hash_add_credit_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (hbudget : 1 ≤ budget) (input : HashInput) (frame : Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (henabled : frame.Enabled parameter otsTable ftsTable (.inl (.inr input)) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inl (.inr input)) (some frame) state.1 false false] *
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap (budget - 1)
          (stepSigningLogState (.inl (.inr input)) state.2 result) result.1.2.2 result.2) +
      jointCollisionCoverageHashCredit (secretKey parameter root otsTable ftsTable) cap budget input state +
      encodingExhaustionTotalPotential state.1 ≤
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
          jointCollisionCoverageHashCharge parameter root otsTable ftsTable cap budget input (some frame) state := by
  let key := secretKey parameter root otsTable ftsTable
  let computation := stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    (.inl (.inr input)) (some frame) state.1 false false
  have hstep := expected_jointCollisionCoverage_hash_add_credit_le parameter root otsTable ftsTable cap budget hcap hbudget input frame state
    hfinite henabled hcomputed hsigned hcache
  have hreserve := expected_stepWithFailure_exhaustionReserve_add_cost_eq (parentException parameter otsTable ftsTable)
    parameter root otsTable ftsTable (.inl (.inr input)) (some frame) state.1 false false budget 1 hbudget
  simp only [Nat.cast_one, one_mul] at hreserve
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
        jointCollisionCoverageHashCharge parameter root otsTable ftsTable cap budget input (some frame) state) +
        encodingExhaustionBudgetReserve budget state.1 := add_le_add hstep hreserve.le
    _ = _ := by rw [jointCollisionCoverageBudgetPotential]; ring

end FtsProbeSimulation.JointOriginal

end SphincsSecurity.Concrete
