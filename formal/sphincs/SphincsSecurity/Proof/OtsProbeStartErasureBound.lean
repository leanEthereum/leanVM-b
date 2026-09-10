import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.DirectQueryBudget
import SphincsSecurity.Proof.OtsProbeSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

noncomputable def concreteAfterRootComputation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) : OracleComp OracleWorld α := do
  let root ← liftM (treeRoot parameter topLayer rootTree
    (fun leafIdx chainIdx => truncateHash (table ⟨topLayer, rootTree, leafIdx, chainIdx⟩)) : OracleComp HashSpec Digest)
  simulateQ (expandedAdversaryImpl
    ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩)
    (continuation root)

theorem simulateQ_unloggedMapped_eq_expanded (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (unloggedMappedAdversaryImpl secretKey) computation =
      simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation) := by
  have hhandler : unloggedMappedAdversaryImpl secretKey = romImpl ∘ₛ expandedAdversaryImpl secretKey := by
    funext input
    exact unloggedMappedAdversaryImpl_eq_simulateQ_expanded secretKey input
  rw [hhandler, QueryImpl.simulateQ_compose]

end SphincsSecurity.Concrete.OtsProbeSimulation
