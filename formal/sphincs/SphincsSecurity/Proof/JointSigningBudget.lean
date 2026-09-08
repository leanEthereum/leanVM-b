import SphincsSecurity.Proof.JointSigningCollisionCoverage
import SphincsSecurity.Proof.DigestSelectionCoverageBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointSigningCoverageCredit (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState) : ENNReal :=
  if remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤ 1 then
    (1 - min 1 (collisionStructuralRecordPotential key state.1 none)) * signingCoverageBudgetGap key cap budget message state
  else 0

theorem boundedUnion_digestSelectionCoverageRisk_add_credit_le (key : SecretKey) (cap budget : Nat) (hcap : cap ≤ 2 ^ 127)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ cap) (message : Message) (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    boundedUnionPotential (collisionStructuralRecordPotential key state.1 none)
      (digestSelectionCoverageRisk key cap (budget - signingExecutionHashCost (.inr message)) message state.1 state.2) +
      jointSigningCoverageCredit key cap budget message state ≤
        jointCollisionCoveragePotential key cap budget state false false +
          (1 - min 1 (collisionStructuralRecordPotential key state.1 none)) * encodingExhaustionTotalPotential state.1 := by
  by_cases hsmall : remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹ ≤ 1
  · rw [jointSigningCoverageCredit, if_pos hsmall]
    exact boundedUnionPotential_add_gap_le _ _ _ _ _
      (digestSelectionCoverageRisk_le_one key cap _ message state.1 state.2) hsmall
      (digestSelectionCoverageRisk_add_gap_le key cap budget hcap state hsigned hcache message hcost)
  · rw [jointSigningCoverageCredit, if_neg hsmall, add_zero, jointCollisionCoveragePotential,
      boundedUnionPotential_eq_one_of_right _ _ (le_of_lt (lt_of_not_ge hsmall))]
    exact (boundedUnionPotential_le_one _ _).trans le_self_add

theorem expected_jointCollisionCoverage_sign_add_credit_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (message : Message) (frame : Frame) (state : CoverLogState)
    (hfinite : Finite state.1) (henabled : frame.Enabled parameter otsTable ftsTable (.inr message) state.1 false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost (.inr message) ≤ budget) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (.inr message) (some frame) state.1 false false] *
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap (budget - signingExecutionHashCost (.inr message))
          (stepSigningLogState (.inr message) state.2 result) result.1.2.2 result.2) +
      jointSigningCoverageCredit (secretKey parameter root otsTable ftsTable) cap budget message state ≤
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget state false false +
          (1 - min 1 (collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) state.1 none)) *
            encodingExhaustionTotalPotential state.1 +
          digestSelectionCollisionRisk (secretKey parameter root otsTable ftsTable) cap (budget - signingExecutionHashCost (.inr message)) message state.1 state.2 +
          jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap (budget - signingExecutionHashCost (.inr message))
            (.inr message) (some frame) state := by
  have h := add_le_add (expected_jointCollisionCoverage_sign_le_risks parameter root otsTable ftsTable cap
    (budget - signingExecutionHashCost (.inr message)) message frame state hfinite henabled hcomputed)
      (le_refl (jointSigningCoverageCredit (secretKey parameter root otsTable ftsTable) cap budget message state))
  apply h.trans
  rw [add_right_comm, add_right_comm (boundedUnionPotential _ _)]
  exact add_le_add (add_le_add
    (boundedUnion_digestSelectionCoverageRisk_add_credit_le (secretKey parameter root otsTable ftsTable) cap budget hcap state hsigned hcache message hcost)
    le_rfl) le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
