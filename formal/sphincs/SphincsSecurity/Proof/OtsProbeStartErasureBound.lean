import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.DirectQueryBudget
import SphincsSecurity.Proof.FtsProbeSimulation
import SphincsSecurity.Proof.OtsProbeSimulation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

theorem simulateQ_unloggedMapped_eq_expanded (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (unloggedMappedAdversaryImpl secretKey) computation =
      simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation) := by
  have hhandler : unloggedMappedAdversaryImpl secretKey = romImpl ∘ₛ expandedAdversaryImpl secretKey := by
    funext input
    exact unloggedMappedAdversaryImpl_eq_simulateQ_expanded secretKey input
  rw [hhandler, QueryImpl.simulateQ_compose]

end SphincsSecurity.Concrete.OtsProbeSimulation
