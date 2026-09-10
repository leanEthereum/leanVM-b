import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalQuerySelection
import SphincsSecurity.Proof.OtsProbeResolvedComputedInvariant

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

structure ActualQuerySelection where
  input : (OracleWorld + SigningSpec).Domain
  cache : QueryCache HashSpec

def CanonicalQuerySelectionRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) :
    Option CanonicalQuerySelection → Option ActualQuerySelection → Prop
  | none, _ => True
  | some left, some right => left.input = right.input ∧ left.table = table ∧
      ResolvedContextInvariant parameter table left.context (ordinaryQueryCache left.cache) right.cache ∧
      VisibleResolvedComputationsCached parameter table left.context right.cache ∧
      PublishedValues left.context.state ∧ DeferredComputationsClosed left.context
  | some _, none => False

end SphincsSecurity.Concrete.OtsProbeSimulation
