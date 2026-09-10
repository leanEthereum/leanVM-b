import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.SubsetTargetAssignment

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset FtsTree) (selected : Finset (Fin m)) :
    (∏ slot ∈ selected, sourceSubsetMatch target source (groups slot)) =
      sourceSubsetMatch target source (selected.biUnion groups) := by
  induction selected using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert slot selected hnot ih =>
      rw [Finset.prod_insert hnot, Finset.biUnion_insert, ih, sourceSubsetMatch_mul]

end SphincsSecurity.Concrete
