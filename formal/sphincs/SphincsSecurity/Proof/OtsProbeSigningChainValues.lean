import SphincsSecurity.Proof.OtsProbeNativeChainMaterialization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local irreducible] maskedSignLayer
set_option backward.isDefEq.respectTransparency false

theorem resolvedPreservesChain_maskedTreeNode
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    ResolvedPreservesCoordinate coordinate (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree 0 nodeIdx).bind fun _ =>
        resolvedPreservesCoordinate_revealCoordinate_of_ne coordinate _ (by intro heq; subst coordinate; exact hchain)
  | succ current =>
      rw [maskedTreeNode]
      exact (resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree (current + 1) nodeIdx).bind fun _ => by
        split
        · exact resolvedPreservesCoordinate_revealCoordinate_of_ne coordinate _ (by intro heq; subst coordinate; exact hchain)
        · exact resolvedPreservesCoordinate_pure coordinate 0

theorem resolvedPreservesChain_maskedLayerMessage
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ResolvedPreservesCoordinate coordinate (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact resolvedPreservesChain_maskedTreeNode coordinate hchain _ _ _ _
  · exact resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl coordinate _

theorem resolvedPreservesChain_maskedSignLayer
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ResolvedPreservesCoordinate coordinate (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (resolvedPreservesChain_maskedLayerMessage coordinate hchain parameter ftsSecret index lay).bind fun message =>
    (resolvedPreservesCoordinate_maskedOtsSignFrom coordinate parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) message encodingAttemptLimit 0).bind fun selected =>
        match selected with
        | none => resolvedPreservesCoordinate_pure coordinate none
        | some _ =>
            (resolvedPreservesCoordinate_ensureTreePath coordinate lay (treeIndexAt index lay)
              (leafIndexAt index lay)).bind fun _ => resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesChain_revealPrivateLayerValues
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (hother : ∀ chainIdx, coordinate ≠
      chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx)) :
    ResolvedPreservesCoordinate coordinate (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun chainIdx =>
    resolvedPreservesCoordinate_revealCoordinate_of_ne coordinate _ (hother chainIdx)).bind fun _ =>
      (resolvedPreservesCoordinate_sequenceFin coordinate _ fun level => by
        by_cases hinLayer : level.val < layerHeight lay
        · simp only [hinLayer, if_pos]
          cases hlevelValue : level.val with
          | zero =>
              exact resolvedPreservesCoordinate_revealCoordinate_of_ne coordinate _ (by intro heq; subst coordinate; exact hchain)
          | succ current =>
              by_cases hcurrent : current < maxLayerHeight
              · simp only [hcurrent, dite_true]
                exact resolvedPreservesCoordinate_revealCoordinate_of_ne coordinate _ (by intro heq; subst coordinate; exact hchain)
              · simp only [hcurrent, dite_false]
                exact resolvedPreservesCoordinate_pure coordinate 0
        · simp only [hinLayer, if_false]
          exact resolvedPreservesCoordinate_pure coordinate 0).bind fun _ =>
          resolvedPreservesCoordinate_pure coordinate _

def ChainOutsideLayerPart (coordinate : Coordinate) (index : Index) (lay : Layer) :
    Option ChronologicalLayerPart → Prop
  | none => True
  | some part => ∀ chainIdx, coordinate ≠
      chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (part.encoding chainIdx)

theorem resolvedPreservesChain_maskedChronologicalSignLayer
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ResolvedPreservesCoordinateWhen coordinate (maskedChronologicalSignLayer parameter ftsSecret index lay)
      (ChainOutsideLayerPart coordinate index lay) := by
  intro context fuel table cache result hresult houtside
  rw [maskedChronologicalSignLayer, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨selectedOption, hselected, hrest⟩ := hresult
  cases selectedOption with
  | none => simp at hrest
  | some selected =>
      have hbefore := (resolvedPreservesChain_maskedSignLayer coordinate hchain parameter ftsSecret index lay
        context fuel table cache selected hselected).1
      cases hvalue : selected.value.1 with
      | none =>
          simp [hvalue, runResolvedFromTable] at hrest
          subst result
          exact hbefore
      | some chosen =>
          rcases chosen with ⟨counter, encoding⟩
          simp only [hvalue] at hrest
          rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨revealedOption, hreveal, hreturn⟩ := hrest
          cases revealedOption with
          | none => simp at hreturn
          | some revealed =>
              simp [runResolvedFromTable] at hreturn
              subst result
              have hafter := resolvedPreservesChain_revealPrivateLayerValues coordinate hchain index lay encoding houtside
                selected.context selected.remaining selected.table selected.value.2 revealed hreveal
              exact hafter.1.trans hbefore

theorem resolvedPreservesChain_maskedChronologicalSignLayers
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ResolvedPreservesCoordinateWhen coordinate (maskedChronologicalSignLayers parameter ftsSecret index)
      (fun layers => ∀ lay, ChainOutsideLayerPart coordinate index lay (layers lay)) :=
  resolvedPreservesCoordinateWhen_sequenceFin coordinate _ _ fun lay =>
    resolvedPreservesChain_maskedChronologicalSignLayer coordinate hchain parameter ftsSecret index lay

theorem resolvedPreservesChain_revealLayerValues
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (hother : ∀ chainIdx, coordinate ≠
      chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx)) :
    ResolvedPreservesCoordinate coordinate (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun chainIdx =>
    resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne coordinate _ (hother chainIdx)).bind fun _ =>
      (resolvedPreservesCoordinate_sequenceFin coordinate _ fun level => by
        by_cases hinLayer : level.val < layerHeight lay
        · simp only [hinLayer, if_pos]
          cases hlevelValue : level.val with
          | zero =>
              exact resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne coordinate _ (by intro heq; subst coordinate; exact hchain)
          | succ current =>
              by_cases hcurrent : current < maxLayerHeight
              · simp only [hcurrent, dite_true]
                exact resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne coordinate _ (by intro heq; subst coordinate; exact hchain)
              · simp only [hcurrent, dite_false]
                exact resolvedPreservesCoordinate_pure coordinate 0
        · simp only [hinLayer, if_false]
          exact resolvedPreservesCoordinate_pure coordinate 0).bind fun _ =>
          resolvedPreservesCoordinate_pure coordinate _

end SphincsSecurity.Concrete.OtsProbeSimulation
