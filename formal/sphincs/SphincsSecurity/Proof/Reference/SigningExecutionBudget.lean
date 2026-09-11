import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

/-- Debit from the syntactic continuation bound, including repeatable digest rejection. -/
def signingExecutionHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => digestAttemptLimit

end SphincsSecurity.Concrete
