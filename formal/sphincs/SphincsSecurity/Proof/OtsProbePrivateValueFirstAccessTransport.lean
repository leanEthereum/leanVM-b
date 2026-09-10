import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def privateSampledCandidatePair (pair : HashOutput × Option Digest) : Option (HashOutput × Digest) :=
  pair.2.map (fun digest => (pair.1, digest))

def PrivateCandidatePairHit : Option (HashOutput × Digest) → Prop
  | none => False
  | some (output, candidate) => candidate = truncateHash output

end SphincsSecurity.Concrete.OtsProbeSimulation
