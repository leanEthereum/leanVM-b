import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeOrdinaryCache
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootState

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem ordinarySplitCacheEq_replaceHiddenRootCache
    (target : Position) (output : HashOutput) (cache : SplitHashCache) :
    OrdinarySplitCacheEq cache (replaceHiddenRootCache target output cache) := by
  intro input
  simp [replaceHiddenRootCache]

end SphincsSecurity.Concrete.OtsProbeSimulation
