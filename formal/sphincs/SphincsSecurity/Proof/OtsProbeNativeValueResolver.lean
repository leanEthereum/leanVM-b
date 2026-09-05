import SphincsSecurity.Proof.OtsProbeNativeValueCompletion

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem resolveDeferredChainStart_replaceNativePosition
    (target : Position) (after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (context : DeferredContext) :
    resolveDeferredChainStart table index (replaceNativePosition target after context) =
      (resolveDeferredChainStart table index context).map (replaceNativeResolution target after none) := by
  have hcoordinate : index.coordinate ≠ Coordinate.position target := by
    cases index
    simp [OtsSecretIndex.coordinate]
  cases hstate : context.state.values index.coordinate <;>
    simp [resolveDeferredChainStart, replaceNativePosition, hcoordinate,
      nativeValueUpdate_hitAt, hstate] <;>
    split_ifs <;> rfl

theorem evalDist_resolveDeferredChainPrefix_replaceNativePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context, NativePositionReplaceable target before after context →
      evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps
        (replaceNativePosition target after context)) =
      evalDist (Option.map (replaceNativeResolution target after
        (chainPrefixResultPosition lay tree leafIdx chainIdx steps hsteps)) <$>
          resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context)
  | 0, hsteps, context, h => by
      simp only [resolveDeferredChainPrefix, chainPrefixResultPosition, map_pure,
        resolveDeferredChainStart_replaceNativePosition]
  | steps + 1, hsteps, context, h => by
      simp only [resolveDeferredChainPrefix, chainPrefixResultPosition]
      rw [evalDist_bind,
        evalDist_resolveDeferredChainPrefix_replaceNativePosition target before after table lay tree leafIdx chainIdx
          steps (by omega) context h, ← evalDist_bind, bind_map_left, map_bind]
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => simp
      | some result =>
          have hnext := h.of_transition
            ((resolveDeferredChainPrefix_preserves_positionValue table lay tree leafIdx chainIdx steps (by omega)
              context result target before h.known hoption).trans h.known.symm)
            (resolveDeferredChainPrefix_pending_subset table lay tree leafIdx chainIdx steps (by omega)
              context result hoption)
            (h.consistent.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps (by omega)
              result hoption)
          exact congrArg evalDist (resolveDeferredPositionValue_replaceNativePosition target
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) before after result.toDeferredContext hnext)

theorem evalDist_resolveDeferredChains_replaceNativePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ∀ chains context, NativePositionReplaceable target before after context →
      evalDist (resolveDeferredChains table lay tree leafIdx chains (replaceNativePosition target after context)) =
        evalDist (Option.map (replaceNativePosition target after) <$>
          resolveDeferredChains table lay tree leafIdx chains context)
  | [], context, _ => by simp [resolveDeferredChains]
  | chainIdx :: remaining, context, h => by
      simp only [resolveDeferredChains]
      rw [evalDist_bind,
        evalDist_resolveDeferredChainPrefix_replaceNativePosition target before after table lay tree leafIdx chainIdx
          (chainLength - 1) (by omega) context h, ← evalDist_bind, bind_map_left, map_bind]
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => simp
      | some result =>
          have hnext := h.of_transition
            ((resolveDeferredChainPrefix_preserves_positionValue table lay tree leafIdx chainIdx (chainLength - 1) (by omega)
              context result target before h.known hoption).trans h.known.symm)
            (resolveDeferredChainPrefix_pending_subset table lay tree leafIdx chainIdx (chainLength - 1) (by omega)
              context result hoption)
            (h.consistent.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx (chainLength - 1) (by omega)
              result hoption)
          exact evalDist_resolveDeferredChains_replaceNativePosition target before after table lay tree leafIdx
            remaining result.toDeferredContext hnext

theorem evalDist_resolveDeferredOtsLeaf_replaceNativePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (context : DeferredContext)
    (h : NativePositionReplaceable target before after context) :
    evalDist (resolveDeferredOtsLeaf table lay tree leafIdx (replaceNativePosition target after context)) =
      evalDist (Option.map (replaceNativeResolution target after (some (.leaf lay tree leafIdx))) <$>
        resolveDeferredOtsLeaf table lay tree leafIdx context) := by
  unfold resolveDeferredOtsLeaf
  rw [evalDist_bind, evalDist_resolveDeferredChains_replaceNativePosition target before after table lay tree leafIdx
    _ context h, ← evalDist_bind, bind_map_left, map_bind]
  apply evalDist_bind_congr
  intro option hoption
  cases option with
  | none => simp
  | some result =>
      have hnext := h.of_transition
        ((resolveDeferredChains_preserves_positionValue table lay tree leafIdx _ context result target before
          h.known hoption).trans h.known.symm)
        (resolveDeferredChains_pending_subset table lay tree leafIdx _ context result hoption)
        (h.consistent.of_resolveDeferredChains table lay tree leafIdx _ result hoption)
      exact congrArg evalDist (resolveDeferredPositionValue_replaceNativePosition target (.leaf lay tree leafIdx)
        before after result hnext)

theorem evalDist_resolveDeferredTreeNode_replaceNativePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context, NativePositionReplaceable target before after context →
      evalDist (resolveDeferredTreeNode table lay tree level nodeIdx hlevel (replaceNativePosition target after context)) =
        evalDist (Option.map (replaceNativeResolution target after (some (deferredTreePosition lay tree level nodeIdx hlevel))) <$>
          resolveDeferredTreeNode table lay tree level nodeIdx hlevel context)
  | 0, nodeIdx, hlevel, context, h =>
      evalDist_resolveDeferredOtsLeaf_replaceNativePosition target before after table lay tree (leafOfNat nodeIdx) context h
  | level + 1, nodeIdx, hlevel, context, h => by
      simp only [resolveDeferredTreeNode, deferredTreePosition]
      rw [evalDist_bind,
        evalDist_resolveDeferredTreeNode_replaceNativePosition target before after table lay tree
          level (2 * nodeIdx) (by omega) context h, ← evalDist_bind, bind_map_left, map_bind]
      apply evalDist_bind_congr
      intro leftOption hleft
      cases leftOption with
      | none => simp
      | some left =>
          have hnext := h.of_transition
            ((resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx) (by omega)
              context left target before h.known hleft).trans h.known.symm)
            (resolveDeferredTreeNode_pending_subset table lay tree level (2 * nodeIdx) (by omega) context left hleft)
            (h.consistent.of_resolveDeferredTreeNode table lay tree level (2 * nodeIdx) (by omega) left hleft)
          dsimp only [Option.map, replaceNativeResolution]
          rw [evalDist_bind,
            evalDist_resolveDeferredTreeNode_replaceNativePosition target before after table lay tree
              level (2 * nodeIdx + 1) (by omega) left.toDeferredContext hnext,
            ← evalDist_bind, bind_map_left, map_bind]
          apply evalDist_bind_congr
          intro rightOption hright
          cases rightOption with
          | none => simp
          | some right =>
              have hfinal := hnext.of_transition
                ((resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx + 1) (by omega)
                  left.toDeferredContext right target before hnext.known hright).trans hnext.known.symm)
                (resolveDeferredTreeNode_pending_subset table lay tree level (2 * nodeIdx + 1) (by omega)
                  left.toDeferredContext right hright)
                (hnext.consistent.of_resolveDeferredTreeNode table lay tree level (2 * nodeIdx + 1) (by omega)
                  right hright)
              exact congrArg evalDist (resolveDeferredPositionValue_replaceNativePosition target
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) before after right.toDeferredContext hfinal)

theorem evalDist_resolveDeferredPosition_replaceNativePosition
    (target position : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context) :
    evalDist (resolveDeferredPosition table position (replaceNativePosition target after context)) =
      evalDist (Option.map (replaceNativeResolution target after (some position)) <$>
        resolveDeferredPosition table position context) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      simpa only [resolveDeferredPosition, chainPrefixResultPosition] using
        evalDist_resolveDeferredChainPrefix_replaceNativePosition target before after table lay tree leafIdx chainIdx
          (step.val + 1) (by have := step.isLt; omega) context h
  | leaf lay tree leafIdx =>
      exact evalDist_resolveDeferredOtsLeaf_replaceNativePosition target before after table lay tree leafIdx context h
  | node lay tree level nodeIdx =>
      simpa only [resolveDeferredPosition, deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt nodeIdx.isLt, Fin.eta] using
        evalDist_resolveDeferredTreeNode_replaceNativePosition target before after table lay tree
          (level.val + 1) nodeIdx (by have := level.isLt; omega) context h
  | ftsLeaf | ftsNode | ftsRoots =>
      exact congrArg evalDist (resolveDeferredPositionValue_replaceNativePosition target _ before after context h)

theorem evalDist_resolveDeferredReveal_replaceNativePosition
    (target position : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context) :
    evalDist (resolveDeferredReveal table position (replaceNativePosition target after context)) =
      evalDist (Option.map (replaceNativeResolution target after (some position)) <$>
        resolveDeferredReveal table position context) := by
  unfold resolveDeferredReveal
  split_ifs
  · exact evalDist_resolveDeferredPosition_replaceNativePosition target position before after table context h
  · exact congrArg evalDist (resolveDeferredPositionValue_replaceNativePosition target position before after context h)

end SphincsSecurity.Concrete.OtsProbeSimulation
