import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalQuerySelection
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateRootCandidate

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def UnknownSourceFinalRootMatch (parameter : PublicParameter)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) : Prop :=
  ∃ terminal, result.1 = some terminal ∧ ∃ (i : Fin result.2.length),
    ∃ (input : HashInput) (candidate : Probe) (lay : Layer) (tree : TreeIndex) (output : HashOutput),
      (result.2.get i).input = .inl (.inr input) ∧
      EncodingLayerRootCandidateAt parameter input candidate ∧
      candidate.coordinate = .position (layerRootPosition lay tree) ∧
      terminal.context.positionValue (layerRootPosition lay tree) = some output ∧
      candidate.candidate = truncateHash output ∧
      (result.2.get i).context.positionValue (layerRootPosition lay tree) = none

end SphincsSecurity.Concrete.OtsProbeSimulation
