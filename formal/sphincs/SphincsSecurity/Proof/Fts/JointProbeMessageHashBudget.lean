import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.JointProbeMessageReserve
namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def messageHashCharge (parameter : PublicParameter) (_ : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if MessageHashInput parameter input then 1 else 0

end SphincsSecurity.Concrete.FtsProbeSimulation
