import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeConditionalCoverage
import SphincsSecurity.Proof.JointProbeMessageReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def freshCoverageCharge {n : Nat} (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none ∧ MessageHashInput parameter input then coverageOccupancyMoment (views input) else 0

end SphincsSecurity.Concrete
