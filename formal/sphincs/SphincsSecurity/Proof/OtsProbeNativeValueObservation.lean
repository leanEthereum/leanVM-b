import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeValueReplacement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem replaceNativePosition_idem
    (target : Position) (first second : HashOutput) (context : DeferredContext) :
    replaceNativePosition target second (replaceNativePosition target first context) =
      replaceNativePosition target second context := by
  simp [replaceNativePosition, Function.comp_def, DeferredStructuralValues.install]

end SphincsSecurity.Concrete.OtsProbeSimulation
