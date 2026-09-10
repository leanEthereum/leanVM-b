import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeSimulation
import SphincsSecurity.Proof.OtsProbeSimulation

/-!
# Guarded preparation through the direct interpreter

The direct interpreter's private-stop projection is dominated by the guarded finite preparation observer whenever every probe issued by the computation is present in the fixed candidate list.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

def IsUncoveredProbe (candidates : List Probe) :
    (LazyRevealProbe.World Coordinate).Domain → Prop
  | .probe coordinate digest => ⟨coordinate, digest⟩ ∉ candidates
  | _ => False

instance instDecidablePredDomainQueryCoordinateWorldIsUncoveredProbe (candidates : List Probe) : DecidablePred (IsUncoveredProbe candidates)
  | .probe coordinate digest => inferInstanceAs (Decidable (⟨coordinate, digest⟩ ∉ candidates))
  | .uniform _ | .hashOutput | .ensure _ | .peek _ | .publish _ | .reveal _ => isFalse id

end SphincsSecurity.Concrete.OtsProbeSimulation
