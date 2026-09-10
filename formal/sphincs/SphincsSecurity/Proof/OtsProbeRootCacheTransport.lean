import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeRootCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem RootValuesCached.of_positionValue_eq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : RootValuesCached parameter table left cache)
    (hvalues : ∀ position, right.positionValue position = left.positionValue position) :
    RootValuesCached parameter table right cache := by
  intro lay tree output hvalue
  exact hclosed lay tree output ((hvalues _).symm.trans hvalue)

end SphincsSecurity.Concrete.OtsProbeSimulation
