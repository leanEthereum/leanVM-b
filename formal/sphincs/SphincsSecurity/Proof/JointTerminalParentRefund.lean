import SphincsSecurity.Proof.CompletedCollisionCoverage
import SphincsSecurity.Proof.RetainedCollisionCacheReserve
import SphincsSecurity.Proof.JointFailureCoverageOverlap

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem terminalPendingParentCount_eq_zero_of_stopped
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (result)
    (hstop : (result.1.2.2 || result.2) = true) : terminalPendingParentCount parameter otsTable ftsTable result = 0 := by
  apply if_neg
  intro h
  simp only [h.1, h.2.1, Bool.false_or, Bool.false_eq_true] at hstop

theorem terminalPendingParentCount_eq_zero_of_structural
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (result)
    (hstructural : SurvivingStructuralFailure parameter otsTable ftsTable result) :
    terminalPendingParentCount parameter otsTable ftsTable result = 0 :=
  if_neg (fun h => h.2.2 hstructural)

theorem twice_terminalPendingParentCount_scaled_le_bounded_collision
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (result)
    (hfinite : Finite result.1.2.1.2) (hcache : QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    (terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      min 1 (collisionStopPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) := by
  unfold terminalPendingParentCount
  split_ifs with h
  · have hcard : ((2 ^ 127 : Nat) : ENNReal) ≤ (Fintype.card Digest : ENNReal) := by norm_num [Digest, digestBits]
    have hsmall := twice_survivingFtsParentReserve_scaled_le_one (secretKey parameter root otsTable ftsTable) result.1.2.1.2 false hfinite hcache
    have hleft := twice_parentReserve_scaled_le_collisionRecordPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 hfinite (hcache.trans hcard)
    simp only [survivingFtsParentReserve, Bool.false_eq_true, if_false] at hsmall
    simp only [collisionStopPotential, collisionSurvivingStructuralPotential, h.1, h.2.1, Bool.false_eq_true, if_false]
    exact le_min hsmall hleft
  · simp only [Nat.cast_zero, zero_mul, zero_le]

noncomputable def terminalJointParentCredit
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : ENNReal :=
  match result.1.2.1.1 with
  | none => 0
  | some value =>
      (1 - boundedCompletedCoveragePotential (secretKey parameter value.1 otsTable ftsTable) (result.1.2.1.2, value.2.1.2)) *
        ((terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) * (2 * (Fintype.card Digest : ENNReal)⁻¹))

noncomputable def terminalParentCoverageOverlap
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : ENNReal :=
  match result.1.2.1.1 with
  | none => (terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) * (2 * (Fintype.card Digest : ENNReal)⁻¹)
  | some value =>
      boundedCompletedCoveragePotential (secretKey parameter value.1 otsTable ftsTable) (result.1.2.1.2, value.2.1.2) *
        ((terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) * (2 * (Fintype.card Digest : ENNReal)⁻¹))

theorem terminalJointParentCredit_add_overlap
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (result) :
    terminalJointParentCredit parameter otsTable ftsTable result + terminalParentCoverageOverlap parameter otsTable ftsTable result =
      (terminalPendingParentCount parameter otsTable ftsTable result : ENNReal) * (2 * (Fintype.card Digest : ENNReal)⁻¹) := by
  unfold terminalJointParentCredit terminalParentCoverageOverlap
  cases result.1.2.1.1 with
  | none => exact zero_add _
  | some value => rw [← add_mul, tsub_add_cancel_of_le (show boundedCompletedCoveragePotential _ _ ≤ 1 from min_le_left _ _), one_mul]

theorem terminalJointParentCredit_le_completed_potential
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (result)
    (hfinite : Finite result.1.2.1.2) (hcache : QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat))
    (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) :
    terminalJointParentCredit parameter otsTable ftsTable result ≤
      completedJointCollisionCoveragePotential (secretKey parameter value.1 otsTable ftsTable)
        (result.1.2.1.2, value.2.1.2) result.1.2.2 result.2 := by
  rw [terminalJointParentCredit, hv]
  exact (mul_le_mul' le_rfl (twice_terminalPendingParentCount_scaled_le_bounded_collision parameter value.1 otsTable ftsTable result hfinite hcache)).trans le_add_self

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
