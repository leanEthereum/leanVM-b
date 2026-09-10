import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinary

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem no_missingChainStartHit_of_values_eq_pending_subset
    (table : OtsSecretIndex → HashOutput) (before after : DeferredContext)
    (hvalues : after.state.values = before.state.values)
    (hpending : after.state.pending ⊆ before.state.pending)
    (hclean : ¬MissingChainStartHit table before) : ¬MissingChainStartHit table after := by
  rintro ⟨index, hmissing, hhit⟩
  apply hclean
  refine ⟨index, by rwa [hvalues] at hmissing, ?_⟩
  unfold LazyRevealProbe.State.hitAt at hhit ⊢
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit ⊢
  exact hpending hhit

theorem resolveDeferredChainPrefix_positive_eq_of_no_missingChainStartHit
    (left right : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (steps : Nat)
    (hsteps : steps + 1 ≤ chainLength - 1) (context : DeferredContext)
    (hleft : ¬MissingChainStartHit left context) (hright : ¬MissingChainStartHit right context) :
    resolveDeferredChainPrefix left lay tree leafIdx chainIdx (steps + 1) hsteps context =
      resolveDeferredChainPrefix right lay tree leafIdx chainIdx (steps + 1) hsteps context := by
  induction steps with
  | zero =>
      cases hstate : context.state.values (.chainStart lay tree leafIdx chainIdx) with
      | none =>
          have hl : ¬context.state.hitAt (.chainStart lay tree leafIdx chainIdx) (left ⟨lay, tree, leafIdx, chainIdx⟩) :=
            fun hhit => hleft ⟨⟨lay, tree, leafIdx, chainIdx⟩, hstate, hhit⟩
          have hr : ¬context.state.hitAt (.chainStart lay tree leafIdx chainIdx) (right ⟨lay, tree, leafIdx, chainIdx⟩) :=
            fun hhit => hright ⟨⟨lay, tree, leafIdx, chainIdx⟩, hstate, hhit⟩
          simp [resolveDeferredChainPrefix, resolveDeferredChainStart, OtsSecretIndex.coordinate, hstate, hl, hr]
      | some output =>
          by_cases hhit : context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output <;>
            simp [resolveDeferredChainPrefix, resolveDeferredChainStart, OtsSecretIndex.coordinate, hstate, hhit]
  | succ steps ih =>
      rw [resolveDeferredChainPrefix, ih (by omega)]
      rfl

theorem evalDist_resolveDeferredChains_eq_of_no_missingChainStartHit
    (left right : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chains : List ChainIndex) (context : DeferredContext)
    (hleft : ¬MissingChainStartHit left context) (hright : ¬MissingChainStartHit right context) :
    evalDist (resolveDeferredChains left lay tree leafIdx chains context) =
      evalDist (resolveDeferredChains right lay tree leafIdx chains context) := by
  induction chains generalizing context with
  | nil => rfl
  | cons chainIdx remaining ih =>
      have hprefix := resolveDeferredChainPrefix_positive_eq_of_no_missingChainStartHit left right lay tree leafIdx chainIdx
        (chainLength - 2) (by norm_num [chainLength, winternitzBits]) context hleft hright
      have hlength : chainLength - 2 + 1 = chainLength - 1 := by norm_num [chainLength, winternitzBits]
      simp only [hlength] at hprefix
      rw [resolveDeferredChains, resolveDeferredChains, hprefix]
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => rfl
      | some result =>
          have hvalues := resolveDeferredChainPrefix_preserves_state_values right lay tree leafIdx chainIdx
            (chainLength - 1) (by omega) context result hoption
          have hpending := resolveDeferredChainPrefix_pending_subset right lay tree leafIdx chainIdx
            (chainLength - 1) (by omega) context result hoption
          exact ih result.toDeferredContext
            (no_missingChainStartHit_of_values_eq_pending_subset left context _ hvalues hpending hleft)
            (no_missingChainStartHit_of_values_eq_pending_subset right context _ hvalues hpending hright)

theorem evalDist_resolveDeferredOtsLeaf_eq_of_no_missingChainStartHit
    (left right : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext)
    (hleft : ¬MissingChainStartHit left context) (hright : ¬MissingChainStartHit right context) :
    evalDist (resolveDeferredOtsLeaf left lay tree leafIdx context) =
      evalDist (resolveDeferredOtsLeaf right lay tree leafIdx context) := by
  unfold resolveDeferredOtsLeaf
  rw [evalDist_bind, evalDist_bind,
    evalDist_resolveDeferredChains_eq_of_no_missingChainStartHit left right lay tree leafIdx _ context hleft hright]

theorem evalDist_resolveDeferredTreeNode_eq_of_no_missingChainStartHit
    (left right : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level ≤ maxLayerHeight) (context : DeferredContext)
    (hleft : ¬MissingChainStartHit left context) (hright : ¬MissingChainStartHit right context) :
    evalDist (resolveDeferredTreeNode left lay tree level nodeIdx hlevel context) =
      evalDist (resolveDeferredTreeNode right lay tree level nodeIdx hlevel context) := by
  induction level generalizing nodeIdx context with
  | zero =>
      exact evalDist_resolveDeferredOtsLeaf_eq_of_no_missingChainStartHit left right lay tree
        (leafOfNat nodeIdx) context hleft hright
  | succ level ih =>
      simp only [resolveDeferredTreeNode]
      rw [evalDist_bind, ih (2 * nodeIdx) (by omega) context hleft hright, ← evalDist_bind]
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => rfl
      | some result =>
          have hvalues := resolveDeferredTreeNode_preserves_state_values right lay tree level (2 * nodeIdx)
            (by omega) context result hoption
          have hpending := resolveDeferredTreeNode_pending_subset right lay tree level (2 * nodeIdx)
            (by omega) context result hoption
          have hl := no_missingChainStartHit_of_values_eq_pending_subset left context result.toDeferredContext
            hvalues hpending hleft
          have hr := no_missingChainStartHit_of_values_eq_pending_subset right context result.toDeferredContext
            hvalues hpending hright
          dsimp only
          rw [evalDist_bind, evalDist_bind, ih (2 * nodeIdx + 1) (by omega) result.toDeferredContext hl hr]

theorem evalDist_resolveDeferredPosition_eq_of_no_missingChainStartHit
    (left right : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (hleft : ¬MissingChainStartHit left context) (hright : ¬MissingChainStartHit right context) :
    evalDist (resolveDeferredPosition left position context) =
      evalDist (resolveDeferredPosition right position context) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact congrArg evalDist (resolveDeferredChainPrefix_positive_eq_of_no_missingChainStartHit left right
        lay tree leafIdx chainIdx step.val (by have := step.isLt; omega) context hleft hright)
  | leaf lay tree leafIdx =>
      exact evalDist_resolveDeferredOtsLeaf_eq_of_no_missingChainStartHit left right lay tree leafIdx context hleft hright
  | node lay tree level nodeIdx =>
      exact evalDist_resolveDeferredTreeNode_eq_of_no_missingChainStartHit left right lay tree
        (level.val + 1) nodeIdx (by have := level.isLt; omega) context hleft hright
  | ftsLeaf | ftsNode | ftsRoots => rfl

theorem evalDist_resolveDeferredReveal_eq_of_no_missingChainStartHit
    (left right : OtsSecretIndex → HashOutput) (position : Position) (context : DeferredContext)
    (hleft : ¬MissingChainStartHit left context) (hright : ¬MissingChainStartHit right context) :
    evalDist (resolveDeferredReveal left position context) =
      evalDist (resolveDeferredReveal right position context) := by
  unfold resolveDeferredReveal
  split_ifs
  · exact evalDist_resolveDeferredPosition_eq_of_no_missingChainStartHit left right position context hleft hright
  · rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
