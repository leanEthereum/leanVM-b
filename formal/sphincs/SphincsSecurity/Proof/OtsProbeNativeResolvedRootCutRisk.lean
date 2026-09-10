import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeValueReplacement
import SphincsSecurity.Proof.OtsProbeResolvedPrivateCommutation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def clearNativeRootPending (target : Position) (context : DeferredContext) : DeferredContext :=
  { context with state := context.state.clearPending (.position target) }

theorem replaceNativePosition_clearPending_eq_completePrivatePosition
    (target : Position) (output : HashOutput) (context : DeferredContext)
    (hstate : context.state.values (.position target) = none) :
    replaceNativePosition target output (clearNativeRootPending target context) =
      (completePrivatePosition target context output).toDeferredContext := by
  rw [replaceNativePosition_of_private target output (clearNativeRootPending target context) hstate]
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
