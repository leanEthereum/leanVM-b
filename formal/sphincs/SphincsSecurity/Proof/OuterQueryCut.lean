import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

inductive OuterQueryCut (α : Type) where
  | done (value : α)
  | query (input : (OracleWorld + SigningSpec).Domain)
      (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)

def OuterQueryCut.resume : OuterQueryCut α → OracleComp (OracleWorld + SigningSpec) α
  | .done value => pure value
  | .query input next => OracleSpec.query input >>= next

def OuterQueryCut.input? : OuterQueryCut α → Option (OracleWorld + SigningSpec).Domain
  | .done _ => none
  | .query input _ => some input

end SphincsSecurity.Concrete.OtsProbeSimulation
