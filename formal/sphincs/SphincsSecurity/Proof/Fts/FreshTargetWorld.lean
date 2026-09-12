import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.JointProbeMessageReserve
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def freshWorldTargetHashCost (parameter : PublicParameter) (cache : QueryCache HashSpec) : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr input => if MessageHashInput parameter input ∧ cache input = none then 1 else 0

end SphincsSecurity.Concrete
