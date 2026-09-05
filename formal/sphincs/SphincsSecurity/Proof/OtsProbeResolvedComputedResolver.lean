import SphincsSecurity.Proof.OtsProbeResolvedComputed

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000 in
theorem deferredPositionComputed_chainPrefix
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      ∀ step : ChainStep, step.val < steps →
        DeferredPositionComputed result.toDeferredContext (.chain lay tree leafIdx chainIdx step)
  | 0, _, _, _, _, step, hstep => by omega
  | steps + 1, hsteps, context, result, hresult, step, hstep => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hrest' : some result ∈ support
              (resolveDeferredPositionValue (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
                previous.toDeferredContext) := by simpa using hrest
          have hpreserves := resolveDeferredPositionValue_preserves_positionValue
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
          by_cases heq : step.val = steps
          · have hstepEq : step = ⟨steps, by omega⟩ := Fin.ext heq
            rw [hstepEq]
            refine .intro _ (by trivial) (by trivial)
              ⟨result.output, resolveDeferredPositionValue_resolves _ _ _ hrest'⟩ ?_
            intro child hchild
            simp only [Position.children] at hchild
            split_ifs at hchild with hpositive
            · have hchildEq := List.mem_singleton.mp hchild
              subst child
              exact (deferredPositionComputed_chainPrefix table lay tree leafIdx chainIdx
                steps (by omega) context previous hprevious ⟨steps - 1, by omega⟩
                (by change steps - 1 < steps; omega)).mono
                (fun position output hvalue => hpreserves position previous.toDeferredContext result
                  output hvalue hrest')
            · simp at hchild
          · exact (deferredPositionComputed_chainPrefix table lay tree leafIdx chainIdx steps
              (by omega) context previous hprevious step (by omega)).mono
              (fun position output hvalue => hpreserves position previous.toDeferredContext result
                output hvalue hrest')

set_option maxRecDepth 100000 in
theorem deferredPositionComputed_chains
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ chains context result,
      some result ∈ support (resolveDeferredChains table lay tree leafIdx chains context) →
      ∀ chainIdx ∈ chains, ∀ step : ChainStep,
        DeferredPositionComputed result (.chain lay tree leafIdx chainIdx step)
  | [], _, _, _, _, hmem, _ => by simp at hmem
  | chainIdx :: remaining, context, result, hresult, other, hmem, step => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst other
            exact (deferredPositionComputed_chainPrefix table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context resolved hresolved step step.isLt).mono
              (fun position output hvalue => resolveDeferredChains_preserves_positionValue table
                lay tree leafIdx remaining resolved.toDeferredContext result position output hvalue
                (by simpa using hrest))
          · exact deferredPositionComputed_chains table lay tree leafIdx remaining
              resolved.toDeferredContext result (by simpa using hrest) other hmem step

set_option maxRecDepth 100000 in
theorem deferredPositionComputed_otsLeaf
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    DeferredPositionComputed result.toDeferredContext (.leaf lay tree leafIdx) := by
  have hknown := resolveDeferredOtsLeaf_resolves table lay tree leafIdx context result hresult
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      refine .intro _ (by trivial) (by trivial) ⟨result.output, hknown⟩ ?_
      intro child hchild
      simp only [Position.children, List.mem_ofFn] at hchild
      obtain ⟨chainIdx, rfl⟩ := hchild
      exact (deferredPositionComputed_chains table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains hchains chainIdx
        (by simp) Position.lastChainStep).mono
        (fun position output hvalue => resolveDeferredPositionValue_preserves_positionValue
          (.leaf lay tree leafIdx) position chains result output hvalue (by simpa using hrest))

theorem DeferredPositionComputed.treeNode_succ
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level + 1 ≤ maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
    (context : DeferredContext)
    (hknown : ∃ output, context.positionValue
      (deferredTreePosition lay tree (level + 1) nodeIdx hlevel) = some output)
    (hleft : DeferredPositionComputed context
      (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)))
    (hright : DeferredPositionComputed context
      (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega))) :
    DeferredPositionComputed context (deferredTreePosition lay tree (level + 1) nodeIdx hlevel) := by
  have hpow : 1 ≤ 2 ^ level := Nat.one_le_pow _ _ (by omega)
  have hnode : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by
    rw [pow_succ] at hspan
    nlinarith
  have hidx : nodeIdx < 2 ^ maxLayerHeight := by omega
  refine .intro _ (by trivial) ?_ hknown ?_
  · simpa [deferredTreePosition, Position.Valid, leafOfNat, Nat.mod_eq_of_lt hidx] using hnode
  · intro child hchild
    have hleftIdx : 2 * nodeIdx < 2 ^ maxLayerHeight := by omega
    cases level with
    | zero =>
        simp [deferredTreePosition, Position.children, leafOfNat, Nat.mod_eq_of_lt hidx, hnode] at hchild
        rcases hchild with rfl | rfl
        · simpa [deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt hleftIdx] using hleft
        · simpa [deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt hnode] using hright
    | succ level =>
        simp [deferredTreePosition, Position.children, leafOfNat, Nat.mod_eq_of_lt hidx, hnode] at hchild
        rcases hchild with rfl | rfl
        · simpa [deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt hleftIdx] using hleft
        · simpa [deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt hnode] using hright

set_option maxRecDepth 100000 in
theorem deferredPositionComputed_treeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel,
      2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight →
      ∀ context result,
        some result ∈ support (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
        DeferredPositionComputed result.toDeferredContext
          (deferredTreePosition lay tree level nodeIdx hlevel)
  | 0, nodeIdx, _, _, context, result, hresult => by
      exact deferredPositionComputed_otsLeaf table lay tree (leafOfNat nodeIdx) context result hresult
  | level + 1, nodeIdx, hlevel, hspan, context, result, hresult => by
      have hknown := resolveDeferredTreeNode_resolves table lay tree (level + 1) nodeIdx hlevel
        context result hresult
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
              have hleftComputed := deferredPositionComputed_treeNode table lay tree level
                (2 * nodeIdx) (by omega) hleftSpan context left hleft
              have hrightComputed := deferredPositionComputed_treeNode table lay tree level
                (2 * nodeIdx + 1) (by omega) hrightSpan left.toDeferredContext right hright
              have hleftInRight := hleftComputed.mono
                (fun position output hvalue => resolveDeferredTreeNode_preserves_positionValue table
                  lay tree level (2 * nodeIdx + 1) (by omega) left.toDeferredContext right
                  position output hvalue hright)
              have hpreserves := fun position output hvalue =>
                resolveDeferredPositionValue_preserves_positionValue
                  (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) position
                  right.toDeferredContext result output hvalue (by simpa using hafterRight)
              exact DeferredPositionComputed.treeNode_succ lay tree level nodeIdx hlevel hspan
                result.toDeferredContext ⟨result.output, hknown⟩
                (hleftInRight.mono hpreserves) (hrightComputed.mono hpreserves)

set_option maxRecDepth 100000 in
theorem deferredPositionComputed_resolvePosition
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (hresolvable : ResolvableOtsPosition position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredPosition table position context)) :
    DeferredPositionComputed result.toDeferredContext position := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact deferredPositionComputed_chainPrefix table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) context result hresult step (by omega)
  | leaf lay tree leafIdx =>
      exact deferredPositionComputed_otsLeaf table lay tree leafIdx context result hresult
  | node lay tree level nodeIdx =>
      simpa only [deferredTreePosition, leafOfNat_val] using
        deferredPositionComputed_treeNode table lay tree (level.val + 1) nodeIdx.val
          (by have := level.isLt; omega) hresolvable context result hresult
  | ftsLeaf | ftsNode | ftsRoots => contradiction

set_option maxRecDepth 100000 in
theorem deferredPositionComputed_resolveReveal
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (hresolvable : ResolvableOtsPosition position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    DeferredPositionComputed result.toDeferredContext position :=
  deferredPositionComputed_resolvePosition table position hresolvable context result
    (by simpa only [resolveDeferredReveal, if_pos hresolvable] using hresult)

end SphincsSecurity.Concrete.OtsProbeSimulation
