import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootInputObservation
import SphincsSecurity.Proof.OtsProbeNativeRootMaterialization
import SphincsSecurity.Proof.OtsProbeResolvedComputedInvariant

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem DeferredPositionComputed.known {context : DeferredContext} {position : Position}
    (h : DeferredPositionComputed context position) : ∃ output, context.positionValue position = some output := by
  cases h with
  | intro _ _ _ hknown _ => exact hknown

theorem DeferredPositionComputed.treeNode_children
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) (hlevel : level + 1 ≤ maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) (context : DeferredContext)
    (h : DeferredPositionComputed context (deferredTreePosition lay tree (level + 1) nodeIdx hlevel)) :
    DeferredPositionComputed context (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)) ∧
    DeferredPositionComputed context (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega)) := by
  have hpow : 1 ≤ 2 ^ level := Nat.one_le_pow _ _ (by omega)
  have hnode : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by
    rw [pow_succ] at hspan
    nlinarith
  have hidx : nodeIdx < 2 ^ maxLayerHeight := by omega
  have hleft : 2 * nodeIdx < 2 ^ maxLayerHeight := by omega
  cases h with
  | intro _ _ _ _ hchildren =>
      constructor
      · apply hchildren
        cases level <;> simp [deferredTreePosition, Position.children, leafOfNat, Nat.mod_eq_of_lt hidx,
          Nat.mod_eq_of_lt hleft, hnode]
      · apply hchildren
        cases level <;> simp [deferredTreePosition, Position.children, leafOfNat, Nat.mod_eq_of_lt hidx,
          Nat.mod_eq_of_lt hnode, hnode]

theorem LayerRootsMaterialized.of_resolveTreeNode_computed
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel,
      2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight →
      ∀ context result,
        LayerRootsMaterialized context →
        DeferredPositionComputed context (deferredTreePosition lay tree level nodeIdx hlevel) →
        some result ∈ support (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
        LayerRootsMaterialized result.toDeferredContext
  | 0, nodeIdx, _, _, context, result, hmat, _, hresult =>
      hmat.of_resolveOtsLeaf table lay tree (leafOfNat nodeIdx) result hresult
  | level + 1, nodeIdx, hlevel, hspan, context, result, hmat, hcomputed, hresult => by
      have hchildren := hcomputed.treeNode_children lay tree level nodeIdx hlevel hspan context
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨left, hleft, htail⟩ := hresult
      cases left with
      | none => simp at htail
      | some left =>
          rw [mem_support_bind_iff] at htail
          obtain ⟨right, hright, htail⟩ := htail
          cases right with
          | none => simp at htail
          | some right =>
              have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith [pow_pos (by omega : 0 < (2 : Nat)) level]
              have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith
              have hleftMat := hmat.of_resolveTreeNode_computed table lay tree level (2 * nodeIdx) (by omega)
                hleftSpan context left hchildren.1 hleft
              have hrightComputed := hchildren.2.mono (fun position output hvalue =>
                resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx) (by omega)
                  context left position output hvalue hleft)
              have hrightMat := hleftMat.of_resolveTreeNode_computed table lay tree level (2 * nodeIdx + 1) (by omega)
                hrightSpan left.toDeferredContext right hrightComputed hright
              apply hrightMat.of_resolvePositionValue_known_root _ result ?_ htail
              intro _
              obtain ⟨output, houtput⟩ := hcomputed.known
              exact ⟨output, resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx + 1) (by omega)
                left.toDeferredContext right _ output
                (resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx) (by omega)
                  context left _ output houtput hleft) hright⟩

theorem LayerRootsMaterialized.materialize_of_resolveTreeNode_children_computed
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level + 1 ≤ maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
    (context : DeferredContext) (result : DeferredResolution) (hmat : LayerRootsMaterialized context)
    (hleftComputed : DeferredPositionComputed context (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)))
    (hrightComputed : DeferredPositionComputed context (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega)))
    (hresult : some result ∈ support (resolveDeferredTreeNode table lay tree (level + 1) nodeIdx hlevel context)) :
    LayerRootsMaterialized (materializeResolvedPosition context (deferredTreePosition lay tree (level + 1) nodeIdx hlevel) result) := by
  rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
  obtain ⟨left, hleft, htail⟩ := hresult
  cases left with
  | none => simp at htail
  | some left =>
      rw [mem_support_bind_iff] at htail
      obtain ⟨right, hright, htail⟩ := htail
      cases right with
      | none => simp at htail
      | some right =>
          have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ maxLayerHeight := by
            rw [pow_succ] at hspan
            nlinarith [pow_pos (by omega : 0 < (2 : Nat)) level]
          have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ maxLayerHeight := by
            rw [pow_succ] at hspan
            nlinarith
          have hleftMat := hmat.of_resolveTreeNode_computed table lay tree level (2 * nodeIdx) (by omega)
            hleftSpan context left hleftComputed hleft
          have hrightComputed' := hrightComputed.mono (fun position output hvalue =>
            resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx) (by omega)
              context left position output hvalue hleft)
          have hrightMat := hleftMat.of_resolveTreeNode_computed table lay tree level (2 * nodeIdx + 1) (by omega)
            hrightSpan left.toDeferredContext right hrightComputed' hright
          have hfinal := hrightMat.materialize_of_other_roots_eq
            (deferredTreePosition lay tree (level + 1) nodeIdx hlevel) result
            (fun target _ hne => resolveDeferredPositionValue_preserves_other _ target right.toDeferredContext result hne htail)
          refine LayerRootsMaterialized.of_values_eq
            (after := materializeResolvedPosition context (deferredTreePosition lay tree (level + 1) nodeIdx hlevel) result)
            hfinal ?_ rfl
          change (context.state.materialize _ result.output).values = (right.state.materialize _ result.output).values
          simp only [LazyRevealProbe.State.materialize]
          rw [resolveDeferredTreeNode_preserves_state_values table lay tree level (2 * nodeIdx + 1) (by omega)
            left.toDeferredContext right hright,
            resolveDeferredTreeNode_preserves_state_values table lay tree level (2 * nodeIdx) (by omega) context left hleft]

theorem DeferredComputationsClosed.treeNode_children_of_peek
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level + 1 ≤ maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
    (context : DeferredContext) (hclosed : DeferredComputationsClosed context)
    (hpeek : purePeekTableInput parameter context.state
      (.position (deferredTreePosition lay tree (level + 1) nodeIdx hlevel)) ≠ none) :
    DeferredPositionComputed context (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)) ∧
    DeferredPositionComputed context (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega)) := by
  have hpow : 1 ≤ 2 ^ level := Nat.one_le_pow _ _ (by omega)
  have hnode : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by
    rw [pow_succ] at hspan
    nlinarith
  have hidx : nodeIdx < 2 ^ maxLayerHeight := by omega
  have hleftIdx : 2 * nodeIdx < 2 ^ maxLayerHeight := by omega
  have hknown : ∀ child ∈ (deferredTreePosition lay tree (level + 1) nodeIdx hlevel).children,
      ∃ output, context.positionValue child = some output := by
    intro child hchild
    have hvalues : purePeekPositionValues context.state
        (deferredTreePosition lay tree (level + 1) nodeIdx hlevel).children ≠ none := by
      intro heq
      apply hpeek
      simp only [purePeekTableInput, deferredTreePosition] at *
      rw [heq]
    have hstate : context.state.values (.position child) ≠ none := by
      intro heq
      exact hvalues ((purePeekPositionValues_eq_none_iff_missing context.state _).mpr ⟨child, hchild, heq⟩)
    cases heq : context.state.values (.position child) with
    | none => exact False.elim (hstate heq)
    | some output => exact ⟨output, by simp [DeferredContext.positionValue, heq]⟩
  have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ maxLayerHeight := by
    rw [pow_succ] at hspan
    nlinarith
  have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ maxLayerHeight := by
    rw [pow_succ] at hspan
    nlinarith
  constructor
  · apply hclosed _ (resolvableOtsPosition_deferredTreePosition lay tree level (2 * nodeIdx) (by omega) hleftSpan)
    apply hknown
    cases level <;> simp [deferredTreePosition, Position.children, leafOfNat, Nat.mod_eq_of_lt hidx,
      Nat.mod_eq_of_lt hleftIdx, hnode]
  · apply hclosed _ (resolvableOtsPosition_deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega) hrightSpan)
    apply hknown
    cases level <;> simp [deferredTreePosition, Position.children, leafOfNat, Nat.mod_eq_of_lt hidx,
      Nat.mod_eq_of_lt hnode, hnode]

theorem LayerRootsMaterialized.of_resolveReveal_peek
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hmat : LayerRootsMaterialized context) (hclosed : DeferredComputationsClosed context)
    (hpeek : purePeekTableInput parameter context.state (.position position) ≠ none)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    LayerRootsMaterialized (materializeResolvedPosition context position result) := by
  by_cases hbounded : LayerBoundedPosition position
  · exact hmat.of_resolveReveal_bounded table position result hbounded hresult
  · unfold resolveDeferredReveal at hresult
    split_ifs at hresult with hresolvable
    · cases position with
      | node lay tree level nodeIdx =>
          have hlevel : level.val + 1 ≤ maxLayerHeight := by have := level.isLt; omega
          have hposition : deferredTreePosition lay tree (level.val + 1) nodeIdx hlevel = .node lay tree level nodeIdx := by
            simp [deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt nodeIdx.isLt]
          have hchildren := hclosed.treeNode_children_of_peek parameter lay tree level nodeIdx hlevel hresolvable context
            (by simpa only [hposition] using hpeek)
          have hfinal := hmat.materialize_of_resolveTreeNode_children_computed table lay tree level nodeIdx hlevel
            hresolvable context result hchildren.1 hchildren.2 hresult
          simpa only [hposition] using hfinal
      | chain | leaf | ftsLeaf | ftsNode | ftsRoots => exact False.elim (hbounded trivial)
    · exact hmat.materialize_of_other_roots_eq position result
        (fun target _ hne => resolveDeferredPositionValue_preserves_other position target context result hne hresult)

end SphincsSecurity.Concrete.OtsProbeSimulation
