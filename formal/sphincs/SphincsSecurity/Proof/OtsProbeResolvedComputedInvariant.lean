import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedComputedResolver
import SphincsSecurity.Proof.OtsProbeRootCacheTransport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def DeferredComputationsClosed (context : DeferredContext) : Prop :=
  ∀ position, ResolvableOtsPosition position →
    (∃ output, context.positionValue position = some output) → DeferredPositionComputed context position

theorem DeferredComputationsClosed.of_positionValue_eq
    {before after : DeferredContext} (hclosed : DeferredComputationsClosed before)
    (hvalues : ∀ position, after.positionValue position = before.positionValue position) :
    DeferredComputationsClosed after := by
  intro position hresolvable hknown
  apply (hclosed position hresolvable ?_).of_positionValue_eq hvalues
  simpa only [hvalues] using hknown

theorem deferredComputationsClosed_empty :
    DeferredComputationsClosed
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } := by
  intro position _ hknown
  simp [DeferredContext.positionValue, LazyRevealProbe.State.empty, emptyDeferredStructuralValues] at hknown

theorem DeferredComputationsClosed.of_resolvePositionValue
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hclosed : DeferredComputationsClosed context)
    (hresult : some result ∈ support (resolveDeferredPositionValue position context))
    (hcomputed : ResolvableOtsPosition position → DeferredPositionComputed result.toDeferredContext position) :
    DeferredComputationsClosed result.toDeferredContext := by
  intro other hresolvable hknown
  by_cases heq : other = position
  · subst other
    exact hcomputed hresolvable
  · have hvalues : result.toDeferredContext.positionValue other = context.positionValue other := by
      unfold DeferredContext.positionValue
      rw [resolveDeferredPositionValue_preserves_state_values position context result hresult,
        resolveDeferredPositionValue_preserves_other position other context result heq hresult]
    exact (hclosed other hresolvable (by simpa only [hvalues] using hknown)).mono
      (fun position' output hvalue => resolveDeferredPositionValue_preserves_positionValue
        position position' context result output hvalue hresult)

theorem DeferredComputationsClosed.of_resolveChainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hclosed : DeferredComputationsClosed context)
    (hresult : resolveDeferredChainStart table index context = some result) :
    DeferredComputationsClosed result.toDeferredContext :=
  hclosed.of_positionValue_eq
    (congrFun (resolveDeferredChainStart_positionValue_eq table index context result hresult))

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.of_resolveChainPrefix
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context result,
      DeferredComputationsClosed context →
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      DeferredComputationsClosed result.toDeferredContext
  | 0, _, context, result, hclosed, hresult => by
      apply hclosed.of_resolveChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context result
      simpa only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] using hresult.symm
  | steps + 1, hsteps, context, result, hclosed, hresult => by
      have hcomputed := deferredPositionComputed_chainPrefix table lay tree leafIdx chainIdx
        (steps + 1) hsteps context result hresult ⟨steps, by omega⟩ (by simp)
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          exact (hclosed.of_resolveChainPrefix table lay tree leafIdx chainIdx steps
            (by omega) context previous hprevious).of_resolvePositionValue
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) previous.toDeferredContext result
            (by simpa using hrest) (fun _ => hcomputed)

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.of_resolveChains
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ∀ chains context result,
      DeferredComputationsClosed context →
      some result ∈ support (resolveDeferredChains table lay tree leafIdx chains context) →
      DeferredComputationsClosed result
  | [], context, result, hclosed, hresult => by
      simpa [resolveDeferredChains] using (show result = context from by simpa [resolveDeferredChains] using hresult) ▸ hclosed
  | chainIdx :: remaining, context, result, hclosed, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          exact (hclosed.of_resolveChainPrefix table lay tree leafIdx chainIdx
            (chainLength - 1) (by omega) context resolved hresolved).of_resolveChains table lay tree leafIdx
            remaining resolved.toDeferredContext result (by simpa using hrest)

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.of_resolveOtsLeaf
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (result : DeferredResolution)
    (hclosed : DeferredComputationsClosed context)
    (hresult : some result ∈ support (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    DeferredComputationsClosed result.toDeferredContext := by
  have hcomputed := deferredPositionComputed_otsLeaf table lay tree leafIdx context result hresult
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      exact (hclosed.of_resolveChains table lay tree leafIdx (List.ofFn fun chainIdx : ChainIndex => chainIdx)
        context chains hchains).of_resolvePositionValue (.leaf lay tree leafIdx) chains result
        (by simpa using hrest) (fun _ => hcomputed)

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.of_resolveTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel,
      2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight →
      ∀ context result,
        DeferredComputationsClosed context →
        some result ∈ support (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
        DeferredComputationsClosed result.toDeferredContext
  | 0, nodeIdx, _, _, context, result, hclosed, hresult => by
      exact hclosed.of_resolveOtsLeaf table lay tree (leafOfNat nodeIdx) context result hresult
  | level + 1, nodeIdx, hlevel, hspan, context, result, hclosed, hresult => by
      have hcomputed := deferredPositionComputed_treeNode table lay tree (level + 1) nodeIdx
        hlevel hspan context result hresult
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith [pow_pos (by omega : 0 < (2 : Nat)) level]
              have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith
              have hleftClosed := hclosed.of_resolveTreeNode table lay tree level (2 * nodeIdx)
                (by omega) hleftSpan context left hleft
              have hrightClosed := hleftClosed.of_resolveTreeNode table lay tree level (2 * nodeIdx + 1)
                (by omega) hrightSpan left.toDeferredContext right hright
              exact hrightClosed.of_resolvePositionValue
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) right.toDeferredContext result
                (by simpa using hafterRight) (fun _ => hcomputed)

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.of_resolvePosition
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (hresolvable : ResolvableOtsPosition position) (context : DeferredContext) (result : DeferredResolution)
    (hclosed : DeferredComputationsClosed context)
    (hresult : some result ∈ support (resolveDeferredPosition table position context)) :
    DeferredComputationsClosed result.toDeferredContext := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact hclosed.of_resolveChainPrefix table lay tree leafIdx chainIdx (step.val + 1)
        (by have := step.isLt; omega) context result hresult
  | leaf lay tree leafIdx =>
      exact hclosed.of_resolveOtsLeaf table lay tree leafIdx context result hresult
  | node lay tree level nodeIdx =>
      exact hclosed.of_resolveTreeNode table lay tree (level.val + 1) nodeIdx.val
        (by have := level.isLt; omega) hresolvable context result hresult
  | ftsLeaf | ftsNode | ftsRoots => contradiction

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.of_resolveReveal
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hclosed : DeferredComputationsClosed context)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    DeferredComputationsClosed result.toDeferredContext := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · exact hclosed.of_resolvePosition table position hresolvable context result
      (by simpa only [resolveDeferredReveal, if_pos hresolvable] using hresult)
  · exact hclosed.of_resolvePositionValue position context result
      (by simpa only [resolveDeferredReveal, if_neg hresolvable] using hresult)
      (fun h => False.elim (hresolvable h))

end SphincsSecurity.Concrete.OtsProbeSimulation
