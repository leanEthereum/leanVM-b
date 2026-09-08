import SphincsSecurity.Proof.JointOverlapParentStep
import SphincsSecurity.Proof.JointFailureCacheCap

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedJointCollisionCoverageAfterParentRefund
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ _ => 0)
    (fun input _ next budget frame state hit failed =>
      jointCollisionCoverageStepAfterParentRefund parameter root otsTable ftsTable cap budget input frame state hit failed +
        ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input frame state.1 hit failed] * next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

theorem expected_sharedParentDiscard_add_remainder_le_overlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) (hfinite : Finite state.1)
    (hcache : ∀ result ∈ support (runWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      computation frame state.1 hit failed), QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    expectedSharedFailureDiscard (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame state.1 hit failed * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
      expectedJointCollisionCoverageAfterParentRefund parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
        expectedJointCollisionCoverageOverlap parameter root otsTable ftsTable cap computation budget frame state hit failed := by
  let exception := parentException parameter otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => simp [expectedJointCollisionCoverageAfterParentRefund, expectedJointCollisionCoverageOverlap]
  | query_bind input next ih =>
      have htail := runWithFailure_tail_cache_cap exception parameter root otsTable ftsTable input next frame state.1 hit failed _ hcache
      have hhead : ∀ result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed),
          QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat) := by
        intro result hr
        exact runWithFailure_initial_cache_cap exception parameter root otsTable ftsTable (next result.1.2.1.1)
          result.1.1 result.1.2.1.2 result.1.2.2 result.2 _ (htail result hr)
      simp only [expectedSharedFailureDiscard_query_bind, expectedJointCollisionCoverageAfterParentRefund,
        expectedJointCollisionCoverageOverlap, construct_query_bind]
      rw [add_mul, add_add_add_comm]
      apply add_le_add (sharedParentDiscard_add_remainder_le_stepOverlap parameter root otsTable ftsTable cap budget input frame state hit failed hfinite hhead)
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro result
      rw [mul_assoc, ← mul_add]
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
      · apply mul_le_mul' le_rfl
        have ha := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame state.1 hit failed result hr
        have hf := finite_cache_of_mem_support _ state.1 result.1.2.1.1 result.1.2.1.2
          (runExceptionMonitor_support_project exception _ state.1 hit ha) hfinite
        exact ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
          (stepSigningLogState input state.2 result) result.1.2.2 result.2 hf (htail result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
