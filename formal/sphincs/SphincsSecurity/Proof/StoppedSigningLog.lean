import SphincsSecurity.Proof.StoppedTargetStep
import SphincsSecurity.Proof.RetainedWorldCoverBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def withSigningLog (computation : OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec) :
    OracleComp (OracleWorld + SigningSpec) (α × QueryLog SigningSpec) :=
  (fun result => (result.1, log ++ result.2)) <$> signingTraceComputation computation

@[simp] theorem withSigningLog_pure (value : α) (log : QueryLog SigningSpec) :
    withSigningLog (pure value) log = pure (value, log) := by
  simp [withSigningLog, signingTraceComputation]

theorem withSigningLog_query_bind (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec) :
    withSigningLog (OracleSpec.query input >>= next) log =
      (liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= fun output =>
        withSigningLog (next output) (log ++ signingLogFragment input output) := by
  rw [withSigningLog, signingTraceComputation_query_bind, map_bind]
  apply bind_congr
  intro output
  simp only [withSigningLog, Functor.map_map, List.append_assoc]

theorem withSigningLog_fst (computation : OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec) :
    Prod.fst <$> withSigningLog computation log = computation := by
  rw [withSigningLog, Functor.map_map]
  exact signingTraceComputation_fst computation

namespace JointOriginal

open OtsProbeSimulation (OtsSecretIndex)

theorem runWithFailure_map
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (f : α → β)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    runWithFailure exception parameter root otsTable ftsTable (f <$> computation) frame cache hit failed =
      (fun result => ((result.1.1, ((f result.1.2.1.1, result.1.2.1.2), result.1.2.2)), result.2)) <$>
        runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed := by
  rw [map_eq_bind_pure_comp, runWithFailure_bind]
  simp only [Function.comp_apply, runWithFailure_pure, bind_pure_comp]

theorem runWithFailure_withSigningLog_fst
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    (fun result => ((result.1.1, ((result.1.2.1.1.1, result.1.2.1.2), result.1.2.2)), result.2)) <$>
      runWithFailure exception parameter root otsTable ftsTable (withSigningLog computation log) frame cache hit failed =
      runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed := by
  rw [← runWithFailure_map, withSigningLog_fst]

end JointOriginal
end SphincsSecurity.Concrete.FtsProbeSimulation
