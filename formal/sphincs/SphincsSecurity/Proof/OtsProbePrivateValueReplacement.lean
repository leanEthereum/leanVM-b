import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeCacheCharge
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def replacePrivatePosition (target : Position) (output : HashOutput) (context : DeferredContext) : DeferredContext :=
  { context with values := context.values.install target output }

def replacePrivateResolution (target : Position) (output : HashOutput) (position : Option Position)
    (result : DeferredResolution) : DeferredResolution :=
  ⟨replacePrivatePosition target output result.toDeferredContext,
    if position = some target then output else result.output⟩

def PrivatePositionReplaceable (target : Position) (before after : HashOutput) (context : DeferredContext) : Prop :=
  context.state.values (.position target) = none ∧ context.values target = some before ∧
    ¬context.state.hitAt (.position target) before ∧ ¬context.state.hitAt (.position target) after

theorem PrivatePositionReplaceable.of_transition
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : PrivatePositionReplaceable target before after left)
    (hstate : right.state.values = left.state.values)
    (hvalue : right.positionValue target = left.positionValue target)
    (hpending : right.state.pending ⊆ left.state.pending) :
    PrivatePositionReplaceable target before after right := by
  have hnone : right.state.values (.position target) = none := by rw [hstate]; exact h.1
  refine ⟨hnone, ?_, ?_, ?_⟩
  · simpa [DeferredContext.positionValue, hnone, h.1, h.2.1] using hvalue
  all_goals
    intro hhit
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    have hmem := hpending hhit
    first
    | apply h.2.2.1
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hmem
    | apply h.2.2.2
      simpa [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] using hmem

theorem resolveDeferredPositionValue_replacePrivatePosition
    (target position : Position) (before after : HashOutput) (context : DeferredContext)
    (h : PrivatePositionReplaceable target before after context) :
    resolveDeferredPositionValue position (replacePrivatePosition target after context) =
      Option.map (replacePrivateResolution target after (some position)) <$>
        resolveDeferredPositionValue position context := by
  by_cases heq : position = target
  · subst position
    simp [resolveDeferredPositionValue, replacePrivatePosition, replacePrivateResolution,
      DeferredStructuralValues.install, h.1, h.2.1, h.2.2.1, h.2.2.2]
  · have hcomm (output : HashOutput) :
        (context.values.install target after).install position output =
          (context.values.install position output).install target after := by
        exact Function.update_comm (Ne.symm heq) (some after) (some output) context.values
    cases hstate : context.state.values (.position position) with
    | some output =>
        by_cases hhit : context.state.hitAt (.position position) output <;>
          simp [resolveDeferredPositionValue, replacePrivatePosition, replacePrivateResolution,
            hstate, hhit, heq, hcomm]
    | none =>
        cases hvalue : context.values position with
        | some output =>
            by_cases hhit : context.state.hitAt (.position position) output <;>
              simp [resolveDeferredPositionValue, replacePrivatePosition, replacePrivateResolution,
                DeferredStructuralValues.install, hstate, hvalue, hhit, heq]
        | none =>
            simp only [resolveDeferredPositionValue, replacePrivatePosition, DeferredStructuralValues.install,
              hstate, Function.update_of_ne heq, hvalue, map_bind]
            apply bind_congr
            intro output
            by_cases hhit : context.state.hitAt (.position position) output
            · simp [hhit]
            · simpa [hhit, replacePrivateResolution, replacePrivatePosition, heq,
                DeferredStructuralValues.install] using hcomm output

theorem resolveDeferredChainStart_replacePrivatePosition
    (target : Position) (after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (context : DeferredContext) :
    resolveDeferredChainStart table index (replacePrivatePosition target after context) =
      (resolveDeferredChainStart table index context).map (replacePrivateResolution target after none) := by
  cases hstate : context.state.values index.coordinate <;>
    simp [resolveDeferredChainStart, replacePrivatePosition, hstate] <;>
    split_ifs <;> rfl

theorem PrivatePositionReplaceable.positionValue
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : PrivatePositionReplaceable target before after context) :
    context.positionValue target = some before := by
  simp [DeferredContext.positionValue, h.1, h.2.1]

def chainPrefixResultPosition (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    (steps : Nat) → steps ≤ chainLength - 1 → Option Position
  | 0, _ => none
  | steps + 1, hsteps => some (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)

theorem evalDist_resolveDeferredChainPrefix_replacePrivatePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context, PrivatePositionReplaceable target before after context →
      evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps
        (replacePrivatePosition target after context)) =
      evalDist (Option.map (replacePrivateResolution target after
        (chainPrefixResultPosition lay tree leafIdx chainIdx steps hsteps)) <$>
          resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context)
  | 0, hsteps, context, h => by
      simp only [resolveDeferredChainPrefix, chainPrefixResultPosition, map_pure,
        resolveDeferredChainStart_replacePrivatePosition]
  | steps + 1, hsteps, context, h => by
      simp only [resolveDeferredChainPrefix, chainPrefixResultPosition]
      rw [evalDist_bind,
        evalDist_resolveDeferredChainPrefix_replacePrivatePosition target before after table lay tree leafIdx chainIdx
          steps (by omega) context h, ← evalDist_bind, bind_map_left, map_bind]
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => simp
      | some result =>
          have hnext := h.of_transition
            (resolveDeferredChainPrefix_preserves_state_values table lay tree leafIdx chainIdx steps (by omega)
              context result hoption)
            ((resolveDeferredChainPrefix_preserves_positionValue table lay tree leafIdx chainIdx steps (by omega)
              context result target before h.positionValue hoption).trans h.positionValue.symm)
            (resolveDeferredChainPrefix_pending_subset table lay tree leafIdx chainIdx steps (by omega)
              context result hoption)
          exact congrArg evalDist (resolveDeferredPositionValue_replacePrivatePosition target
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) before after result.toDeferredContext hnext)

theorem evalDist_resolveDeferredChains_replacePrivatePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ∀ chains context, PrivatePositionReplaceable target before after context →
      evalDist (resolveDeferredChains table lay tree leafIdx chains (replacePrivatePosition target after context)) =
        evalDist (Option.map (replacePrivatePosition target after) <$>
          resolveDeferredChains table lay tree leafIdx chains context)
  | [], context, _ => by simp [resolveDeferredChains]
  | chainIdx :: remaining, context, h => by
      simp only [resolveDeferredChains]
      rw [evalDist_bind,
        evalDist_resolveDeferredChainPrefix_replacePrivatePosition target before after table lay tree leafIdx chainIdx
          (chainLength - 1) (by omega) context h, ← evalDist_bind, bind_map_left, map_bind]
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => simp
      | some result =>
          have hnext := h.of_transition
            (resolveDeferredChainPrefix_preserves_state_values table lay tree leafIdx chainIdx (chainLength - 1) (by omega)
              context result hoption)
            ((resolveDeferredChainPrefix_preserves_positionValue table lay tree leafIdx chainIdx (chainLength - 1) (by omega)
              context result target before h.positionValue hoption).trans h.positionValue.symm)
            (resolveDeferredChainPrefix_pending_subset table lay tree leafIdx chainIdx (chainLength - 1) (by omega)
              context result hoption)
          exact evalDist_resolveDeferredChains_replacePrivatePosition target before after table lay tree leafIdx
            remaining result.toDeferredContext hnext

theorem evalDist_resolveDeferredOtsLeaf_replacePrivatePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (context : DeferredContext)
    (h : PrivatePositionReplaceable target before after context) :
    evalDist (resolveDeferredOtsLeaf table lay tree leafIdx (replacePrivatePosition target after context)) =
      evalDist (Option.map (replacePrivateResolution target after (some (.leaf lay tree leafIdx))) <$>
        resolveDeferredOtsLeaf table lay tree leafIdx context) := by
  unfold resolveDeferredOtsLeaf
  rw [evalDist_bind, evalDist_resolveDeferredChains_replacePrivatePosition target before after table lay tree leafIdx
    _ context h, ← evalDist_bind, bind_map_left, map_bind]
  apply evalDist_bind_congr
  intro option hoption
  cases option with
  | none => simp
  | some result =>
      have hnext := h.of_transition
        (resolveDeferredChains_preserves_state_values table lay tree leafIdx _ context result hoption)
        ((resolveDeferredChains_preserves_positionValue table lay tree leafIdx _ context result target before
          h.positionValue hoption).trans h.positionValue.symm)
        (resolveDeferredChains_pending_subset table lay tree leafIdx _ context result hoption)
      exact congrArg evalDist (resolveDeferredPositionValue_replacePrivatePosition target (.leaf lay tree leafIdx)
        before after result hnext)

theorem evalDist_resolveDeferredTreeNode_replacePrivatePosition
    (target : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context, PrivatePositionReplaceable target before after context →
      evalDist (resolveDeferredTreeNode table lay tree level nodeIdx hlevel (replacePrivatePosition target after context)) =
        evalDist (Option.map (replacePrivateResolution target after (some (deferredTreePosition lay tree level nodeIdx hlevel))) <$>
          resolveDeferredTreeNode table lay tree level nodeIdx hlevel context)
  | 0, nodeIdx, hlevel, context, h =>
      evalDist_resolveDeferredOtsLeaf_replacePrivatePosition target before after table lay tree (leafOfNat nodeIdx) context h
  | level + 1, nodeIdx, hlevel, context, h => by
      simp only [resolveDeferredTreeNode, deferredTreePosition]
      rw [evalDist_bind,
        evalDist_resolveDeferredTreeNode_replacePrivatePosition target before after table lay tree
          level (2 * nodeIdx) (by omega) context h, ← evalDist_bind, bind_map_left, map_bind]
      apply evalDist_bind_congr
      intro leftOption hleft
      cases leftOption with
      | none => simp
      | some left =>
          have hnext := h.of_transition
            (resolveDeferredTreeNode_preserves_state_values table lay tree level (2 * nodeIdx) (by omega) context left hleft)
            ((resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx) (by omega)
              context left target before h.positionValue hleft).trans h.positionValue.symm)
            (resolveDeferredTreeNode_pending_subset table lay tree level (2 * nodeIdx) (by omega) context left hleft)
          dsimp only [Option.map, replacePrivateResolution]
          rw [evalDist_bind,
            evalDist_resolveDeferredTreeNode_replacePrivatePosition target before after table lay tree
              level (2 * nodeIdx + 1) (by omega) left.toDeferredContext hnext,
            ← evalDist_bind, bind_map_left, map_bind]
          apply evalDist_bind_congr
          intro rightOption hright
          cases rightOption with
          | none => simp
          | some right =>
              have hfinal := hnext.of_transition
                (resolveDeferredTreeNode_preserves_state_values table lay tree level (2 * nodeIdx + 1) (by omega)
                  left.toDeferredContext right hright)
                ((resolveDeferredTreeNode_preserves_positionValue table lay tree level (2 * nodeIdx + 1) (by omega)
                  left.toDeferredContext right target before hnext.positionValue hright).trans hnext.positionValue.symm)
                (resolveDeferredTreeNode_pending_subset table lay tree level (2 * nodeIdx + 1) (by omega)
                  left.toDeferredContext right hright)
              exact congrArg evalDist (resolveDeferredPositionValue_replacePrivatePosition target
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) before after right.toDeferredContext hfinal)

theorem evalDist_resolveDeferredPosition_replacePrivatePosition
    (target position : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (h : PrivatePositionReplaceable target before after context) :
    evalDist (resolveDeferredPosition table position (replacePrivatePosition target after context)) =
      evalDist (Option.map (replacePrivateResolution target after (some position)) <$>
        resolveDeferredPosition table position context) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      simpa only [resolveDeferredPosition, chainPrefixResultPosition] using
        evalDist_resolveDeferredChainPrefix_replacePrivatePosition target before after table lay tree leafIdx chainIdx
          (step.val + 1) (by have := step.isLt; omega) context h
  | leaf lay tree leafIdx =>
      exact evalDist_resolveDeferredOtsLeaf_replacePrivatePosition target before after table lay tree leafIdx context h
  | node lay tree level nodeIdx =>
      simpa only [resolveDeferredPosition, deferredTreePosition, leafOfNat, Nat.mod_eq_of_lt nodeIdx.isLt, Fin.eta] using
        evalDist_resolveDeferredTreeNode_replacePrivatePosition target before after table lay tree
          (level.val + 1) nodeIdx (by have := level.isLt; omega) context h
  | ftsLeaf | ftsNode | ftsRoots =>
      exact congrArg evalDist (resolveDeferredPositionValue_replacePrivatePosition target _ before after context h)

theorem evalDist_resolveDeferredReveal_replacePrivatePosition
    (target position : Position) (before after : HashOutput) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (h : PrivatePositionReplaceable target before after context) :
    evalDist (resolveDeferredReveal table position (replacePrivatePosition target after context)) =
      evalDist (Option.map (replacePrivateResolution target after (some position)) <$>
        resolveDeferredReveal table position context) := by
  unfold resolveDeferredReveal
  split_ifs
  · exact evalDist_resolveDeferredPosition_replacePrivatePosition target position before after table context h
  · exact congrArg evalDist (resolveDeferredPositionValue_replacePrivatePosition target position before after context h)

end SphincsSecurity.Concrete.OtsProbeSimulation
