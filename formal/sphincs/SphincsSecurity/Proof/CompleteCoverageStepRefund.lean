import SphincsSecurity.Proof.StoppedSigningCoveragePayment

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def completeCoverageStepRefund
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) : ENNReal :=
  let key := secretKey parameter root otsTable ftsTable
  let potential := fun remaining current => remainingCoveragePotential key cap remaining current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹
  let before := survivingLogPotential (potential budget) state hit failed
  let after := ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
    survivingLogPotential (potential (budget - signingExecutionHashCost input))
      (stepSigningLogState input state.2 result) result.1.2.2 result.2
  let pairs := beforeFailureSigningStepCharge exception (encodingPairIncrementCharge key) key state.1 hit failed input * (Fintype.card Digest : ENNReal)⁻¹
  let reserve := beforeFailureSigningStepCharge exception (nonMessageNonEncodingHashCharge parameter) key state.1 hit failed input * (Fintype.card Digest : ENNReal)⁻¹
  let refund := paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed
  let residual := paidRemainingCoverageStepResidual key cap budget input state hit failed
  refund + (before + reserve + residual - (after + pairs + refund))

theorem paidRemainingCoverageStepRefund_le_complete
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed ≤
      completeCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed := le_self_add

theorem stepWithFailure_coverage_pairs_completeRefund_eq_reserved_add_residual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcapMax : cap ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost input ≤ budget)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run state.1),
      QueryCache.enncard result.2 ≤ cap) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap (budget - signingExecutionHashCost input) current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
          (stepSigningLogState input state.2 result) result.1.2.2 result.2) +
      beforeFailureSigningStepCharge exception (encodingPairIncrementCharge (secretKey parameter root otsTable ftsTable))
        (secretKey parameter root otsTable ftsTable) state.1 hit failed input * (Fintype.card Digest : ENNReal)⁻¹ +
      completeCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed =
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap budget current ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) state hit failed +
        beforeFailureSigningStepCharge exception (nonMessageNonEncodingHashCharge parameter)
          (secretKey parameter root otsTable ftsTable) state.1 hit failed input * (Fintype.card Digest : ENNReal)⁻¹ +
        paidRemainingCoverageStepResidual (secretKey parameter root otsTable ftsTable) cap budget input state hit failed := by
  have h := stepWithFailure_coverage_pairs_refund_le_reserved_add_residual exception parameter root otsTable ftsTable
    cap budget hcapMax input frame state hit failed hsigned hcache hcost hcap
  simpa only [completeCoverageStepRefund, add_assoc] using add_tsub_cancel_of_le h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
