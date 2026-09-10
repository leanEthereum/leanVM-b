import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def privatePositionAccessCandidate (target : Position) : Option (PrivateValueCut α) → Option Digest
  | some (.query (.probe coordinate digest) _) => if coordinate = .position target then some digest else none
  | _ => none

end SphincsSecurity.Concrete.OtsProbeSimulation
