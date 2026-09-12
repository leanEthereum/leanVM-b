import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.SubsetTargetExpectation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_symm (target source : FewTimeView) (required : Finset FtsTree) :
    sourceSubsetMatch target source required = sourceSubsetMatch source target required := by
  unfold sourceSubsetMatch
  apply Finset.prod_congr rfl
  intro tree _
  simp only [sourceTreeMatch, eq_comm]

theorem sourceSubsetMatch_index_leaf (source : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty)
    (index : Index) (leaves : FtsTree → FtsLeaf) :
    sourceSubsetMatch (index, leaves) source required =
      (if source.1 = index then 1 else 0) * ∏ tree ∈ required, (if leaves tree = source.2 tree then 1 else 0) := by
  rw [sourceSubsetMatch_symm, sourceSubsetMatch_index source required hne]
  by_cases hi : index = source.1 <;> simp only [hi, eq_comm, if_true, if_false, one_mul, zero_mul]

end SphincsSecurity.Concrete
