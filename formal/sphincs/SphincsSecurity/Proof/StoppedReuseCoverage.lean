import SphincsSecurity.Proof.ReuseCoverageGap
import SphincsSecurity.Proof.NearUniformRawStep
import SphincsSecurity.Proof.StoppedTargetCharge
import SphincsSecurity.Proof.StoppedLogPotentialDiscard

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)

noncomputable def stoppedReuseCoverageStepCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (reuse : ENNReal) (budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  survivingLogPotential (fun current => reuseUnusedCoverageStepCharge
    (secretKey parameter root otsTable ftsTable) reuse budget current input groups remaining) state hit failed +
      expectedStepLogDiscard exception parameter root otsTable ftsTable input frame state hit failed
        (fun current => reuseCoveragePotential (secretKey parameter root otsTable ftsTable)
          reuse (budget - signingExecutionHashCost input) current groups remaining)

noncomputable def expectedReuseUnusedCoverageCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (reuse : ENNReal) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ budget _ state hit failed =>
    survivingLogPotential (fun current => reuseCoverageTerminalReserve
      (secretKey parameter root otsTable ftsTable) reuse budget current groups remaining) state hit failed)
    (fun input _ next budget frame state hit failed =>
      stoppedReuseCoverageStepCharge exception parameter root otsTable ftsTable reuse budget input frame state hit failed groups remaining +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

@[simp] theorem expectedReuseUnusedCoverageCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (reuse : ENNReal) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (value : α) (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedReuseUnusedCoverageCharge exception parameter root otsTable ftsTable reuse groups remaining
      (pure value) budget frame state hit failed =
      survivingLogPotential (fun current => reuseCoverageTerminalReserve
        (secretKey parameter root otsTable ftsTable) reuse budget current groups remaining) state hit failed := rfl

theorem expectedReuseUnusedCoverageCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (reuse : ENNReal) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedReuseUnusedCoverageCharge exception parameter root otsTable ftsTable reuse groups remaining
        (OracleSpec.query input >>= next) budget frame state hit failed =
      stoppedReuseCoverageStepCharge exception parameter root otsTable ftsTable reuse budget input frame state hit failed groups remaining +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          expectedReuseUnusedCoverageCharge exception parameter root otsTable ftsTable reuse groups remaining
            (next result.1.2.1.1) (budget - signingExecutionHashCost input) result.1.1
              (stepSigningLogState input state.2 result) result.1.2.2 result.2 := rfl

theorem stepWithFailure_reuseCoverage_add_unused_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (reuse : ENNReal) (budget : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hreuse : hit = false → ∀ message, exactDigestReuseWeight (secretKey parameter root otsTable ftsTable) message state.1 ≤ reuse)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential (fun current => reuseCoveragePotential (secretKey parameter root otsTable ftsTable)
        reuse (budget - signingExecutionHashCost input) current groups remaining)
          (stepSigningLogState input state.2 result) result.1.2.2 result.2) +
      stoppedReuseCoverageStepCharge exception parameter root otsTable ftsTable reuse budget input frame state hit failed groups remaining ≤
      survivingLogPotential (fun current => reuseCoveragePotential (secretKey parameter root otsTable ftsTable)
        reuse budget current groups remaining) state hit failed := by
  rw [stoppedReuseCoverageStepCharge, ← add_assoc, add_right_comm, stepWithFailure_expect_surviving_add_discard]
  unfold survivingLogPotential
  split_ifs with hstop
  · simp only [zero_add, le_refl]
  · have hhit : hit = false := by cases hit <;> simp_all
    exact expected_logTraced_reuseCoverage_add_stepCharge_le (secretKey parameter root otsTable ftsTable)
      reuse budget state hsigned (hreuse hhit) input hcost groups remaining hvalid

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
