import SphincsSecurity.Proof.HonestStructuralQueries
import SphincsSecurity.Proof.SigningSettlingTrace

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
attribute [local irreducible] instFintypePosition

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id)

theorem honestStructuralQueries_treePath (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    HonestStructuralQueries parameter otsSecret ftsSecret f
      (treePath parameter lay tree (otsSecret lay tree) leafIdx) := by
  apply HonestStructuralQueries.sequenceFin
  intro level
  split_ifs
  · apply honestStructuralQueries_treeNode parameter otsSecret ftsSecret f lay tree _ _ (by omega)
    exact FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val level.val level.isLt leafIdx.isLt
  · exact HonestStructuralQueries.pure _

theorem honestStructuralQueries_ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) :
    HonestStructuralQueries parameter otsSecret ftsSecret f
      (ftsLeafHash parameter index tree leafIdx (ftsSecret index tree leafIdx)) := by
  intro input hinput
  simp only [ftsLeafHash, queriedInputs_tweakableHash, List.mem_singleton] at hinput
  exact ⟨.ftsLeaf index tree leafIdx, by trivial, hinput⟩

theorem honestStructuralQueries_ftsNode (index : Index) (tree : FtsTree) (level nodeIdx : Nat)
    (hlevel : level ≤ ftsTreeHeight) (hrange : FtsRange level nodeIdx) :
    HonestStructuralQueries parameter otsSecret ftsSecret f
      (ftsNode parameter index tree (ftsSecret index tree) level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact honestStructuralQueries_ftsLeaf parameter otsSecret ftsSecret f index tree _
  | succ level ih =>
      have hleft : FtsRange level (2 * nodeIdx) := by
        simp only [FtsRange, pow_succ] at hrange ⊢
        nlinarith [Nat.zero_le (2 ^ level)]
      have hright : FtsRange level (2 * nodeIdx + 1) := by
        simp only [FtsRange, pow_succ] at hrange ⊢
        nlinarith
      have hindices : 2 * nodeIdx + 1 < 2 ^ ftsTreeHeight := by
        have hpow : 1 ≤ 2 ^ level := one_le_pow₀ (by omega)
        simp only [FtsRange] at hright
        nlinarith
      rw [ftsNode_succ_eq]
      apply (ih (2 * nodeIdx) (by omega) hleft).bind
      apply (ih (2 * nodeIdx + 1) (by omega) hright).bind
      intro input hinput
      simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
      exact ⟨.ftsNode index tree ⟨level, by omega⟩ ⟨nodeIdx, by omega⟩, hindices, hinput⟩

theorem honestStructuralQueries_ftsKey (index : Index) :
    HonestStructuralQueries parameter otsSecret ftsSecret f (ftsKey parameter index (ftsSecret index)) := by
  apply HonestStructuralQueries.bind
  · apply HonestStructuralQueries.sequenceFin
    intro tree
    apply honestStructuralQueries_ftsNode parameter otsSecret ftsSecret f index tree _ _ le_rfl
    simp only [FtsRange, zero_add, mul_one, le_refl]
  · intro input hinput
    simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
    refine ⟨.ftsRoots index, by trivial, ?_⟩
    simpa only [honestInput, honestPayload, Position.domain, evalWithAnswerFn_sequenceFin, honestFtsNode] using hinput

theorem honestStructuralQueries_ftsOpen (index : Index) (leaves : DigestTree → FtsLeaf) :
    HonestStructuralQueries parameter otsSecret ftsSecret f (ftsOpen parameter index leaves (ftsSecret index)) := by
  apply HonestStructuralQueries.sequenceFin
  intro tree
  apply HonestStructuralQueries.sequenceFin
  intro level
  apply honestStructuralQueries_ftsNode parameter otsSecret ftsSecret f index tree _ _ (by omega)
  exact FtsProbeSimulation.sibling_node_bound ftsTreeHeight _ level.val level.isLt (leaves (ftsIndexOf tree)).isLt

theorem honestStructuralQueries_layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) :
    HonestStructuralQueries secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f (layerMessage secretKey index lay) := by
  unfold layerMessage
  split_ifs
  · exact honestStructuralQueries_treeRoot secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f _ _
  · exact honestStructuralQueries_ftsKey secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f index

end SphincsSecurity.Concrete
