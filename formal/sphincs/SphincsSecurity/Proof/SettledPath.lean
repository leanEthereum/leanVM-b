import SphincsSecurity.Proof.Cached

/-!
# Settled authentication paths

A settled tree root recursively settles every node, leaf and chain below it. These lemmas select
the positions used by one authentication path.
-/

namespace SphincsSecurity.Concrete

open OracleSpec

variable {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}

private theorem settled_chain_step_of_succ (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (position : Nat)
    (hposition : position + 1 < chainLength - 1)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.chain lay tree leafIdx chainIdx ⟨position + 1, hposition⟩)) :
    Settled parameter otsSecret ftsSecret cache
      (.chain lay tree leafIdx chainIdx ⟨position, by omega⟩) := by
  apply hsettled.children
  rw [Position.mem_children_iff, Position.parentOf, dif_pos (by omega)]

theorem settled_chain_of_settled_leaf (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hleaf : Settled parameter otsSecret ftsSecret cache (.leaf lay tree leafIdx))
    (chainIdx : ChainIndex) (position : Nat) (hposition : position < chainLength - 1) :
    Settled parameter otsSecret ftsSecret cache
      (.chain lay tree leafIdx chainIdx ⟨position, hposition⟩) := by
  have hlast : Settled parameter otsSecret ftsSecret cache
      (.chain lay tree leafIdx chainIdx Position.lastChainStep) := by
    apply hleaf.children
    simp only [Position.children, List.mem_ofFn]
    exact ⟨chainIdx, rfl⟩
  have hdown : ∀ offset (hoffset : offset ≤ chainLength - 2),
      Settled parameter otsSecret ftsSecret cache
        (.chain lay tree leafIdx chainIdx ⟨chainLength - 2 - offset, by omega⟩) := by
    intro offset
    induction offset with
    | zero =>
        intro _
        simpa only [Nat.sub_zero, Position.lastChainStep] using hlast
    | succ offset ih =>
        intro hoffset
        have hprev : offset ≤ chainLength - 2 := by omega
        have hpos : chainLength - 2 - (offset + 1) + 1 = chainLength - 2 - offset := by omega
        have hlt : chainLength - 2 - (offset + 1) + 1 < chainLength - 1 := by omega
        have := settled_chain_step_of_succ lay tree leafIdx chainIdx
          (chainLength - 2 - (offset + 1)) hlt (by simpa only [hpos] using ih hprev)
        exact this
  have hoffset : chainLength - 2 - position ≤ chainLength - 2 := Nat.sub_le _ _
  convert hdown (chainLength - 2 - position) hoffset using 1
  all_goals simp only [Position.chain.injEq, Fin.ext_iff, true_and]
  omega

private theorem settled_tree_node_of_succ (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (level : Nat) (hlevel : level + 1 < maxLayerHeight)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨level + 1, hlevel⟩
        ⟨leafIdx.val / 2 ^ (level + 2), lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩)) :
    Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨level, by omega⟩
        ⟨leafIdx.val / 2 ^ (level + 1), lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩) := by
  apply hsettled.children
  rw [Position.mem_children_iff, Position.parentOf, dif_pos (by omega)]
  simp only [Option.some.injEq, Position.node.injEq, Fin.ext_iff, true_and]
  rw [show level + 2 = (level + 1) + 1 by omega, div_pow_succ, div_pow_succ]
  rw [← div_pow_succ]

private theorem settled_leaf_of_settled_node_zero (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨0, by decide⟩
        ⟨leafIdx.val / 2, lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩)) :
    Settled parameter otsSecret ftsSecret cache (.leaf lay tree leafIdx) := by
  apply hsettled.children
  rw [Position.mem_children_iff, Position.parentOf]

theorem settled_tree_path_of_settled_root (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (hleafIdx : leafIdx.val < 2 ^ layerHeight lay)
    (hroot : Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨layerHeight lay - 1, by
        have hpos : 0 < layerHeight lay := by unfold layerHeight; split <;> norm_num [maxLayerHeight]
        have hle := layerHeight_le lay
        omega⟩ ⟨0, by positivity⟩)) :
    Settled parameter otsSecret ftsSecret cache (.leaf lay tree leafIdx)
      ∧ ∀ level (hlevel : level < layerHeight lay),
        Settled parameter otsSecret ftsSecret cache
          (.node lay tree ⟨level, lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
            ⟨leafIdx.val / 2 ^ (level + 1),
              lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩) := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hheight := layerHeight_le lay
  have hroot' : Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨layerHeight lay - 1, by omega⟩
        ⟨leafIdx.val / 2 ^ layerHeight lay,
          lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩) := by
    convert hroot using 1
    all_goals simp only [Position.node.injEq, Fin.ext_iff, true_and]
    exact Nat.div_eq_of_lt hleafIdx
  have hdown : ∀ offset (hoffset : offset ≤ layerHeight lay - 1),
      Settled parameter otsSecret ftsSecret cache
        (.node lay tree ⟨layerHeight lay - 1 - offset, by omega⟩
          ⟨leafIdx.val / 2 ^ (layerHeight lay - offset),
            lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩) := by
    intro offset
    induction offset with
    | zero =>
        intro _
        simpa only [Nat.sub_zero] using hroot'
    | succ offset ih =>
        intro hoffset
        have hprev : offset ≤ layerHeight lay - 1 := by omega
        have hlevel : layerHeight lay - 1 - (offset + 1) + 1 < maxLayerHeight := by
          have hle := layerHeight_le lay
          omega
        have hlevelEq : layerHeight lay - 1 - offset
            = layerHeight lay - 1 - (offset + 1) + 1 := by omega
        have := settled_tree_node_of_succ lay tree leafIdx
          (layerHeight lay - 1 - (offset + 1)) hlevel (by
            convert ih hprev using 1
            simp only [Position.node.injEq, Fin.ext_iff, true_and]
            refine ⟨hlevelEq.symm, ?_⟩
            rw [show layerHeight lay - 1 - (offset + 1) + 2
              = layerHeight lay - offset by omega])
        convert this using 1
        simp only [Position.node.injEq, Fin.ext_iff, true_and]
        rw [show layerHeight lay - 1 - (offset + 1) + 1
          = layerHeight lay - (offset + 1) by omega]
  have hzero : Settled parameter otsSecret ftsSecret cache
      (.node lay tree ⟨0, by decide⟩
        ⟨leafIdx.val / 2, lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩) := by
    have := hdown (layerHeight lay - 1) (le_refl _)
    convert this using 1
    simp only [Position.node.injEq, Fin.ext_iff, true_and]
    refine ⟨by omega, ?_⟩
    rw [show layerHeight lay - (layerHeight lay - 1) = 1 by omega, pow_one]
  refine ⟨settled_leaf_of_settled_node_zero lay tree leafIdx hzero, ?_⟩
  intro level hlevel
  have hoffset : layerHeight lay - 1 - level ≤ layerHeight lay - 1 := Nat.sub_le _ _
  have := hdown (layerHeight lay - 1 - level) hoffset
  convert this using 1
  simp only [Position.node.injEq, Fin.ext_iff, true_and]
  refine ⟨by omega, ?_⟩
  rw [show layerHeight lay - (layerHeight lay - 1 - level) = level + 1 by omega]

private theorem settled_fts_node_of_succ (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (level : Nat) (hlevel : level + 1 < ftsTreeHeight)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨level + 1, hlevel⟩
        ⟨leafIdx.val / 2 ^ (level + 2), lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩)) :
    Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨level, by omega⟩
        ⟨leafIdx.val / 2 ^ (level + 1), lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩) := by
  apply hsettled.children
  rw [Position.mem_children_iff, Position.parentOf, dif_pos (by omega)]
  simp only [Option.some.injEq, Position.ftsNode.injEq, Fin.ext_iff, true_and]
  rw [show level + 2 = (level + 1) + 1 by omega, div_pow_succ, div_pow_succ]
  rw [← div_pow_succ]

private theorem settled_fts_leaf_of_settled_node_zero (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf)
    (hsettled : Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨0, by decide⟩
        ⟨leafIdx.val / 2, lt_of_le_of_lt (Nat.div_le_self _ _) leafIdx.isLt⟩)) :
    Settled parameter otsSecret ftsSecret cache (.ftsLeaf index tree leafIdx) := by
  apply hsettled.children
  rw [Position.mem_children_iff, Position.parentOf]

theorem settled_fts_path_of_settled_roots (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hroots : Settled parameter otsSecret ftsSecret cache (.ftsRoots index)) :
    (∀ tree, Settled parameter otsSecret ftsSecret cache
      (.ftsLeaf index tree (leaves (ftsIndexOf tree))))
      ∧ ∀ tree level (hlevel : level < ftsTreeHeight),
        Settled parameter otsSecret ftsSecret cache
          (.ftsNode index tree ⟨level, hlevel⟩
            ⟨(leaves (ftsIndexOf tree)).val / 2 ^ (level + 1),
              lt_of_le_of_lt (Nat.div_le_self _ _) (leaves (ftsIndexOf tree)).isLt⟩) := by
  have htreeRoot : ∀ tree, Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨ftsTreeHeight - 1, by decide⟩ ⟨0, by positivity⟩) := by
    intro tree
    apply hroots.children
    simp only [Position.children, List.mem_ofFn]
    exact ⟨tree, rfl⟩
  have hdown : ∀ tree offset (hoffset : offset ≤ ftsTreeHeight - 1),
      Settled parameter otsSecret ftsSecret cache
        (.ftsNode index tree ⟨ftsTreeHeight - 1 - offset, by simp only [ftsTreeHeight]; omega⟩
          ⟨(leaves (ftsIndexOf tree)).val / 2 ^ (ftsTreeHeight - offset),
            lt_of_le_of_lt (Nat.div_le_self _ _) (leaves (ftsIndexOf tree)).isLt⟩) := by
    intro tree offset
    induction offset with
    | zero =>
        intro _
        have hleaf := (leaves (ftsIndexOf tree)).isLt
        have hzero : (leaves (ftsIndexOf tree)).val / 2 ^ ftsTreeHeight = 0 :=
          Nat.div_eq_of_lt hleaf
        convert htreeRoot tree using 1
        simp only [Nat.sub_zero, Position.ftsNode.injEq, Fin.ext_iff, true_and]
        exact hzero
    | succ offset ih =>
        intro hoffset
        have hprev : offset ≤ ftsTreeHeight - 1 := by omega
        have hlevel : ftsTreeHeight - 1 - (offset + 1) + 1 < ftsTreeHeight := by omega
        have hprevious : Settled parameter otsSecret ftsSecret cache
            (.ftsNode index tree ⟨ftsTreeHeight - 1 - (offset + 1) + 1, hlevel⟩
              ⟨(leaves (ftsIndexOf tree)).val /
                  2 ^ (ftsTreeHeight - 1 - (offset + 1) + 2),
                lt_of_le_of_lt (Nat.div_le_self _ _) (leaves (ftsIndexOf tree)).isLt⟩) := by
          convert ih hprev using 1
          simp only [Position.ftsNode.injEq, Fin.ext_iff, true_and]
          refine ⟨by omega, ?_⟩
          rw [show ftsTreeHeight - 1 - (offset + 1) + 2
            = ftsTreeHeight - offset by omega]
        have hnext := settled_fts_node_of_succ index tree (leaves (ftsIndexOf tree))
          (ftsTreeHeight - 1 - (offset + 1)) hlevel hprevious
        convert hnext using 1
        simp only [Position.ftsNode.injEq, Fin.ext_iff, true_and]
        rw [show ftsTreeHeight - 1 - (offset + 1) + 1
          = ftsTreeHeight - (offset + 1) by omega]
  have hzero : ∀ tree, Settled parameter otsSecret ftsSecret cache
      (.ftsNode index tree ⟨0, by decide⟩
        ⟨(leaves (ftsIndexOf tree)).val / 2,
          lt_of_le_of_lt (Nat.div_le_self _ _) (leaves (ftsIndexOf tree)).isLt⟩) := by
    intro tree
    have h := hdown tree (ftsTreeHeight - 1) (le_refl _)
    convert h using 1
    simp only [Position.ftsNode.injEq, Fin.ext_iff, true_and]
    refine ⟨by omega, ?_⟩
    rw [show ftsTreeHeight - (ftsTreeHeight - 1) = 1 by norm_num [ftsTreeHeight], pow_one]
  refine ⟨fun tree => settled_fts_leaf_of_settled_node_zero index tree
    (leaves (ftsIndexOf tree)) (hzero tree), ?_⟩
  intro tree level hlevel
  have hoffset : ftsTreeHeight - 1 - level ≤ ftsTreeHeight - 1 := Nat.sub_le _ _
  have h := hdown tree (ftsTreeHeight - 1 - level) hoffset
  convert h using 1
  simp only [Position.ftsNode.injEq, Fin.ext_iff, true_and]
  refine ⟨by omega, ?_⟩
  rw [show ftsTreeHeight - (ftsTreeHeight - 1 - level) = level + 1 by omega]

end SphincsSecurity.Concrete
