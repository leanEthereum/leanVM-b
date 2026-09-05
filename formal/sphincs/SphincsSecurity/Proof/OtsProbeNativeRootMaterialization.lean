import SphincsSecurity.Proof.OtsProbeNativeResolvedRootCutRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def LayerRootsMaterialized (context : DeferredContext) : Prop :=
  ∀ target, IsLayerRoot target → context.values target ≠ none → context.state.values (.position target) ≠ none

theorem LayerRootsMaterialized.of_values_eq
    {before after : DeferredContext} (h : LayerRootsMaterialized before)
    (hstate : after.state.values = before.state.values) (hvalues : after.values = before.values) :
    LayerRootsMaterialized after := by
  intro target hroot hknown
  rw [hstate]
  exact h target hroot (by simpa only [hvalues] using hknown)

theorem LayerRootsMaterialized.state_value_of_known
    {context : DeferredContext} (h : LayerRootsMaterialized context) (target : Position) (hroot : IsLayerRoot target)
    (output : HashOutput) (hknown : context.positionValue target = some output) :
    context.state.values (.position target) = some output := by
  cases hstate : context.state.values (.position target) with
  | none =>
      have haux : context.values target = some output := by simpa [DeferredContext.positionValue, hstate] using hknown
      exact False.elim (h target hroot (by rw [haux]; simp) hstate)
  | some value =>
      have heq : value = output := by simpa [DeferredContext.positionValue, hstate] using hknown
      exact congrArg some heq

theorem LayerRootsMaterialized.materialize_of_other_roots_eq
    {context : DeferredContext} (h : LayerRootsMaterialized context) (position : Position) (result : DeferredResolution)
    (hvalues : ∀ target, IsLayerRoot target → target ≠ position → result.values target = context.values target) :
    LayerRootsMaterialized (materializeResolvedPosition context position result) := by
  intro target hroot hknown
  by_cases heq : target = position
  · subst target
    simp [materializeResolvedPosition, LazyRevealProbe.State.materialize]
  · have hbefore : context.values target ≠ none := by
      change result.values target ≠ none at hknown
      rwa [hvalues target hroot heq] at hknown
    have hstate := h target hroot hbefore
    simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize, heq] using hstate

theorem not_isLayerRoot_chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) :
    ¬IsLayerRoot (.chain lay tree leafIdx chainIdx step) := by
  rintro ⟨otherLay, otherTree, h⟩
  cases h

theorem not_isLayerRoot_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ¬IsLayerRoot (.leaf lay tree leafIdx) := by
  rintro ⟨otherLay, otherTree, h⟩
  cases h

theorem not_isLayerRoot_node_below (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
    (hbelow : level.val + 1 < layerHeight lay) : ¬IsLayerRoot (.node lay tree level nodeIdx) := by
  rintro ⟨otherLay, otherTree, h⟩
  simp only [layerRootPosition, Position.node.injEq] at h
  obtain ⟨rfl, rfl, hlevel, _⟩ := h
  have heq := congrArg Fin.val hlevel
  dsimp only at heq
  omega

theorem resolveDeferredChainPrefix_preserves_root_values
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context result,
      some result ∈ support (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      ∀ target, IsLayerRoot target → result.values target = context.values target
  | 0, hsteps, context, result, hresult, target, _ => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      exact congrFun (resolveDeferredChainStart_deferred_values_eq table ⟨lay, tree, leafIdx, chainIdx⟩ context result hresult.symm) target
  | steps + 1, hsteps, context, result, hresult, target, hroot => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previous, hprevious, htail⟩ := hresult
      cases previous with
      | none => simp at htail
      | some previous =>
          have hmiddle := resolveDeferredChainPrefix_preserves_root_values table lay tree leafIdx chainIdx steps (by omega)
            context previous hprevious target hroot
          exact (resolveDeferredPositionValue_preserves_other (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) target
            previous.toDeferredContext result (fun heq => not_isLayerRoot_chain lay tree leafIdx chainIdx _ (heq ▸ hroot)) htail).trans hmiddle

theorem resolveDeferredChains_preserves_root_values
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ∀ chains context result, some result ∈ support (resolveDeferredChains table lay tree leafIdx chains context) →
      ∀ target, IsLayerRoot target → result.values target = context.values target
  | [], context, result, hresult, target, _ => by
      simp only [resolveDeferredChains, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      rfl
  | chainIdx :: chains, context, result, hresult, target, hroot => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      cases head with
      | none => simp at htail
      | some head =>
          exact (resolveDeferredChains_preserves_root_values table lay tree leafIdx chains head.toDeferredContext result htail target hroot).trans
            (resolveDeferredChainPrefix_preserves_root_values table lay tree leafIdx chainIdx (chainLength - 1) (by omega)
              context head hhead target hroot)

theorem resolveDeferredOtsLeaf_preserves_root_values
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredOtsLeaf table lay tree leafIdx context))
    (target : Position) (hroot : IsLayerRoot target) : result.values target = context.values target := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chains, hchains, htail⟩ := hresult
  cases chains with
  | none => simp at htail
  | some chains =>
      exact (resolveDeferredPositionValue_preserves_other (.leaf lay tree leafIdx) target chains result
        (fun heq => not_isLayerRoot_leaf lay tree leafIdx (heq ▸ hroot)) htail).trans
        (resolveDeferredChains_preserves_root_values table lay tree leafIdx _ context chains hchains target hroot)

theorem resolveDeferredTreeNode_preserves_root_values_below
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context result, level < layerHeight lay →
      some result ∈ support (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      ∀ target, IsLayerRoot target → result.values target = context.values target
  | 0, nodeIdx, hlevel, context, result, _, hresult, target, hroot =>
      resolveDeferredOtsLeaf_preserves_root_values table lay tree (leafOfNat nodeIdx) context result hresult target hroot
  | level + 1, nodeIdx, hlevel, context, result, hbelow, hresult, target, hroot => by
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
              have hleftEq := resolveDeferredTreeNode_preserves_root_values_below table lay tree level (2 * nodeIdx) (by omega)
                context left (by omega) hleft target hroot
              have hrightEq := resolveDeferredTreeNode_preserves_root_values_below table lay tree level (2 * nodeIdx + 1) (by omega)
                left.toDeferredContext right (by omega) hright target hroot
              exact (resolveDeferredPositionValue_preserves_other (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) target
                right.toDeferredContext result
                (fun heq => not_isLayerRoot_node_below lay tree _ _ hbelow (heq ▸ hroot)) htail).trans (hrightEq.trans hleftEq)

theorem resolveDeferredTreeNode_preserves_other_root_values_bounded
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level ≤ maxLayerHeight) (context : DeferredContext) (result : DeferredResolution)
    (hbounded : level ≤ layerHeight lay)
    (hresult : some result ∈ support (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context))
    (target : Position) (hroot : IsLayerRoot target)
    (hne : target ≠ deferredTreePosition lay tree level nodeIdx hlevel) :
    result.values target = context.values target := by
  cases level with
  | zero => exact resolveDeferredOtsLeaf_preserves_root_values table lay tree (leafOfNat nodeIdx) context result hresult target hroot
  | succ level =>
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
              have hleftEq := resolveDeferredTreeNode_preserves_root_values_below table lay tree level (2 * nodeIdx) (by omega)
                context left (by omega) hleft target hroot
              have hrightEq := resolveDeferredTreeNode_preserves_root_values_below table lay tree level (2 * nodeIdx + 1) (by omega)
                left.toDeferredContext right (by omega) hright target hroot
              exact (resolveDeferredPositionValue_preserves_other (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) target
                right.toDeferredContext result hne htail).trans (hrightEq.trans hleftEq)

def LayerBoundedPosition : Position → Prop
  | .node lay _ level _ => level.val + 1 ≤ layerHeight lay
  | _ => True

theorem resolveDeferredReveal_preserves_other_root_values_bounded
    (table : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hbounded : LayerBoundedPosition position)
    (hresult : some result ∈ support (resolveDeferredReveal table position context))
    (target : Position) (hroot : IsLayerRoot target) (hne : target ≠ position) :
    result.values target = context.values target := by
  unfold resolveDeferredReveal at hresult
  split_ifs at hresult with hresolvable
  · cases position with
    | chain lay tree leafIdx chainIdx step =>
        exact resolveDeferredChainPrefix_preserves_root_values table lay tree leafIdx chainIdx _ _ context result hresult target hroot
    | leaf lay tree leafIdx =>
        exact resolveDeferredOtsLeaf_preserves_root_values table lay tree leafIdx context result hresult target hroot
    | node lay tree level nodeIdx =>
        apply resolveDeferredTreeNode_preserves_other_root_values_bounded table lay tree (level.val + 1) nodeIdx
          (by have := level.isLt; omega) context result hbounded hresult target hroot
        simpa [deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt nodeIdx.isLt] using hne
    | ftsLeaf | ftsNode | ftsRoots => contradiction
  · exact resolveDeferredPositionValue_preserves_other position target context result hne hresult

theorem LayerRootsMaterialized.of_resolveReveal_bounded
    {context : DeferredContext} (h : LayerRootsMaterialized context)
    (table : OtsSecretIndex → HashOutput) (position : Position) (result : DeferredResolution)
    (hbounded : LayerBoundedPosition position)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    LayerRootsMaterialized (materializeResolvedPosition context position result) :=
  h.materialize_of_other_roots_eq position result
    (resolveDeferredReveal_preserves_other_root_values_bounded table position context result hbounded hresult)

theorem LayerRootsMaterialized.of_resolvePositionValue_known_root
    {context : DeferredContext} (h : LayerRootsMaterialized context)
    (position : Position) (result : DeferredResolution)
    (hknown : IsLayerRoot position → ∃ output, context.positionValue position = some output)
    (hresult : some result ∈ support (resolveDeferredPositionValue position context)) :
    LayerRootsMaterialized result.toDeferredContext := by
  intro target hroot haux
  rw [resolveDeferredPositionValue_preserves_state_values position context result hresult]
  by_cases heq : target = position
  · subst target
    obtain ⟨output, houtput⟩ := hknown hroot
    rw [h.state_value_of_known position hroot output houtput]
    simp
  · apply h target hroot
    change result.values target ≠ none at haux
    rwa [resolveDeferredPositionValue_preserves_other position target context result heq hresult] at haux

theorem LayerRootsMaterialized.of_resolveOtsLeaf
    {context : DeferredContext} (h : LayerRootsMaterialized context)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    LayerRootsMaterialized result.toDeferredContext := by
  intro target hroot haux
  rw [resolveDeferredOtsLeaf_preserves_state_values table lay tree leafIdx context result hresult]
  apply h target hroot
  change result.values target ≠ none at haux
  rwa [resolveDeferredOtsLeaf_preserves_root_values table lay tree leafIdx context result hresult target hroot] at haux

end SphincsSecurity.Concrete.OtsProbeSimulation
