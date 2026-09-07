import SphincsSecurity.Proof.ParentReserveStoppedConservation
import SphincsSecurity.Proof.JointFailurePotentialConservation
import SphincsSecurity.Proof.JointProbeMessageHashBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local irreducible] instFintypePosition parentReserve freshParentReserveCharge releasedParentQueryCharge exceptionDiscardCharge
set_option backward.isDefEq.respectTransparency false

noncomputable def survivingFtsParentReserve (key : SecretKey) (cache : QueryCache HashSpec) (hit : Bool) : ENNReal :=
  if hit then 0 else (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache : ENNReal)

noncomputable def freshFtsParentReserveCharge (key : SecretKey) : QueryCache HashSpec → HashInput → ENNReal :=
  freshParentReserveCharge key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position)

noncomputable def releasedFtsParentQueryCharge (key : SecretKey) : QueryCache HashSpec → HashInput → ENNReal :=
  releasedParentQueryCharge key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position)

noncomputable def discardedFtsParentQueryCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey) : QueryCache HashSpec → HashInput → ENNReal :=
  exceptionDiscardCharge exception (fun cache => (parentReserve key.parameter key.otsSecret key.ftsSecret
    (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache : ENNReal))

theorem expected_survivingFtsParentReserve_add_losses_eq_funding
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) :
    (∑' result, Pr[= result | runExceptionMonitor exception computation cache hit] * survivingFtsParentReserve key result.1.2 result.2) +
      expectedPreExceptionCharge exception (fun current input => releasedFtsParentQueryCharge key current input +
        discardedFtsParentQueryCharge exception key current input) computation cache hit =
      survivingFtsParentReserve key cache hit + expectedPreExceptionCharge exception (freshFtsParentReserveCharge key) computation cache hit := by
  rw [expectedPreExceptionCharge_add, ← add_assoc]
  exact expected_stoppedParentReserve_add_discard_releases_eq_funding key.parameter key.otsSecret key.ftsSecret
    (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) exception computation cache hfinite hit

namespace FtsProbeSimulation.JointOriginal

theorem expected_jointParentReserve_add_losses_eq_funding
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed] *
      jointSurvivingCachePotential (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable)) result.1.2.1.2 result.1.2.2 result.2) +
      expectedSharedFailureDiscard exception (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureCharge exception (releasedFtsParentQueryCharge (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed +
      expectedBeforeFailureCharge exception (discardedFtsParentQueryCharge exception (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable computation frame cache hit failed =
      jointSurvivingCachePotential (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable)) cache hit failed +
        expectedBeforeFailureCharge exception (freshFtsParentReserveCharge (secretKey parameter root otsTable ftsTable))
          parameter root otsTable ftsTable computation frame cache hit failed := by
  rw [add_assoc, ← expectedBeforeFailureCharge_add]
  apply expected_runWithFailure_potential_add_discard_charge_eq
    exception (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable)) _ _ parameter root otsTable ftsTable
    _ computation frame cache hfinite hit failed
  intro input current hcurrent stopped
  exact expected_survivingFtsParentReserve_add_losses_eq_funding exception (secretKey parameter root otsTable ftsTable)
    (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) current hcurrent stopped

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
