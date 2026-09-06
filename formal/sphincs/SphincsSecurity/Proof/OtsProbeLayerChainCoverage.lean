import SphincsSecurity.Proof.OtsProbeSigningChainPublication
import SphincsSecurity.Proof.OtsProbeChronologicalLayerBody

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ChainsPublishedOutside (outside : Coordinate → Prop) (context : DeferredContext) : Prop :=
  ∀ coordinate, IsChainCoordinate coordinate → outside coordinate →
    context.state.values coordinate ≠ none → coordinate ∈ context.state.revealed

theorem MaterializedChainsPublished.outside {context : DeferredContext} (h : MaterializedChainsPublished context)
    (outside : Coordinate → Prop) : ChainsPublishedOutside outside context :=
  fun coordinate hchain _ hknown => h coordinate hchain hknown

theorem ChainsPublishedOutside.mono {left right : Coordinate → Prop} {context : DeferredContext}
    (h : ChainsPublishedOutside left context) (himp : ∀ coordinate, right coordinate → left coordinate) :
    ChainsPublishedOutside right context := fun coordinate hchain houtside hknown =>
  h coordinate hchain (himp coordinate houtside) hknown

theorem resolvedPreservesCoordinate_maskedOtsLayerAfterMessage
    (coordinate : Coordinate) (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    ResolvedPreservesCoordinate coordinate (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage maskedOtsSign
  exact (resolvedPreservesCoordinate_maskedOtsSignFrom coordinate parameter lay (treeIndexAt index lay)
    (leafIndexAt index lay) message encodingAttemptLimit 0).bind fun selected =>
      match selected with
      | none => resolvedPreservesCoordinate_pure coordinate none
      | some _ =>
          (resolvedPreservesCoordinate_ensureTreePath coordinate lay (treeIndexAt index lay)
            (leafIndexAt index lay)).bind fun _ => resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesChain_chronologicalLayerAfterMessage
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate)
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    ResolvedPreservesCoordinateWhen coordinate (maskedChronologicalLayerAfterMessage parameter index lay message)
      (ChainOutsideLayerPart coordinate index lay) := by
  intro context fuel table cache result hresult houtside
  rw [maskedChronologicalLayerAfterMessage, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨selectedOption, hselected, hrest⟩ := hresult
  cases selectedOption with
  | none => simp at hrest
  | some selected =>
      have hbefore := (resolvedPreservesCoordinate_maskedOtsLayerAfterMessage coordinate parameter index lay message
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
              exact (resolvedPreservesChain_revealPrivateLayerValues coordinate hchain index lay encoding houtside
                selected.context selected.remaining selected.table selected.value.2 revealed hreveal).1.trans hbefore

theorem resolvedPreservesChain_maskedTreeRoot
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (lay : Layer) (tree : TreeIndex) :
    ResolvedPreservesCoordinate coordinate (maskedTreeRoot lay tree) :=
  resolvedPreservesChain_maskedTreeNode coordinate hchain lay tree (layerHeight lay) 0

attribute [local irreducible] maskedTreeRoot

theorem resolvedPreservesChain_upperChronologicalLayer
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate)
    (parameter : PublicParameter) (index : Index) (lay : Fin (numLayers - 1)) :
    ResolvedPreservesCoordinateWhen coordinate (maskedUpperChronologicalLayer parameter index lay)
      (ChainOutsideLayerPart coordinate index lay.castSucc) := by
  intro context fuel table cache result hresult houtside
  rw [maskedUpperChronologicalLayer, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootOption, hroot, hrest⟩ := hresult
  cases rootOption with
  | none => simp at hrest
  | some root =>
      have hbefore := (resolvedPreservesChain_maskedTreeRoot coordinate hchain _ _
        context fuel table cache root hroot).1
      exact (resolvedPreservesChain_chronologicalLayerAfterMessage coordinate hchain parameter index lay.castSucc root.value.1
        root.context root.remaining root.table root.value.2 result hrest houtside).trans hbefore

theorem resolvedPreservesChain_upperChronologicalLayers
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) (parameter : PublicParameter) (index : Index) :
    ResolvedPreservesCoordinateWhen coordinate (maskedUpperChronologicalLayers parameter index)
      (fun layers => ∀ lay, ChainOutsideLayerPart coordinate index lay.castSucc (layers lay)) :=
  resolvedPreservesCoordinateWhen_sequenceFin coordinate _ _ fun lay =>
    resolvedPreservesChain_upperChronologicalLayer coordinate hchain parameter index lay

attribute [local irreducible] maskedUpperChronologicalLayers maskedChronologicalLayerAfterMessage

theorem chainsPublishedOutside_chronologicalLayerAfterMessage
    (outside : Coordinate → Prop) (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option ChronologicalLayerPart × SplitHashCache))
    (hpublic : ChainsPublishedOutside outside context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedChronologicalLayerAfterMessage parameter index lay message).run cache))) :
    ChainsPublishedOutside (fun coordinate => outside coordinate ∧ ChainOutsideLayerPart coordinate index lay result.value.1)
      result.context := by
  intro coordinate hchain houtside hknown
  have hvalue := resolvedPreservesChain_chronologicalLayerAfterMessage coordinate hchain parameter index lay message
    context fuel table cache result hresult houtside.2
  exact revealed_subset_of_mem_runResolvedFromTable _ context fuel table result hresult
    (hpublic coordinate hchain houtside.1 (by rwa [hvalue] at hknown))

theorem chainsPublishedOutside_upperChronologicalLayers
    (outside : Coordinate → Prop) (parameter : PublicParameter) (index : Index)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult ((Fin (numLayers - 1) → Option ChronologicalLayerPart) × SplitHashCache))
    (hpublic : ChainsPublishedOutside outside context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedUpperChronologicalLayers parameter index).run cache))) :
    ChainsPublishedOutside (fun coordinate => outside coordinate ∧
      ∀ lay, ChainOutsideLayerPart coordinate index lay.castSucc (result.value.1 lay)) result.context := by
  intro coordinate hchain houtside hknown
  have hvalue := resolvedPreservesChain_upperChronologicalLayers coordinate hchain parameter index
    context fuel table cache result hresult houtside.2
  exact revealed_subset_of_mem_runResolvedFromTable _ context fuel table result hresult
    (hpublic coordinate hchain houtside.1 (by rwa [hvalue] at hknown))

end SphincsSecurity.Concrete.OtsProbeSimulation
