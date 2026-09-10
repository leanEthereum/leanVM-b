import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeUniform
import SphincsSecurity.Proof.JointProbeMessageReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedAdmissibleMessageInputs (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) : Finset HashInput :=
  hfinite.toFinset.filter (fun input => MessageHashInput parameter input ∧
    ∃ output, cache input = some output ∧ Admissible (truncateMessageDigest output))

def cachedFewTimeView (cache : QueryCache HashSpec) (input : HashInput) : FewTimeView :=
  hashOutputFewTimeView ((cache input).getD default)

end SphincsSecurity.Concrete
