import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec

def signingMacroHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 1024

end SphincsSecurity.Concrete
