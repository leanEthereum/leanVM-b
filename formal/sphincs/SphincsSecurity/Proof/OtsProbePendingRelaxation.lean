import SphincsSecurity.Proof.OtsProbePrivateValueErasedRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure PendingRelaxation (left right : DeferredContext) : Prop where
  stateValues : left.state.values = right.state.values
  privateValues : left.values = right.values
  revealed : left.state.revealed = right.state.revealed
  pending : right.state.pending ⊆ left.state.pending

def OptionRefines (relation : α → β → Prop) : Option α → Option β → Prop
  | none, _ => True
  | some left, some right => relation left right
  | some _, none => False

theorem relTriple_none_optionRefines (relation : α → β → Prop) (right : ProbComp (Option β)) :
    RelTriple (pure none : ProbComp (Option α)) right (OptionRefines relation) := by
  have h := FtsProbeSimulation.relTriple_and_left_support (relTriple_true (pure none : ProbComp (Option α)) right)
    (fun result => result = none) (by intro result hresult; simpa using hresult)
  exact relTriple_post_mono h (by intro left right h; rcases h with ⟨_, rfl⟩; trivial)

theorem PendingRelaxation.refl (context : DeferredContext) : PendingRelaxation context context :=
  ⟨rfl, rfl, rfl, Finset.Subset.refl _⟩

theorem PendingRelaxation.positionValue {left right : DeferredContext} (h : PendingRelaxation left right) (position : Position) :
    left.positionValue position = right.positionValue position := by
  simp only [DeferredContext.positionValue, h.stateValues, h.privateValues]

theorem PendingRelaxation.hitAt {left right : DeferredContext} (h : PendingRelaxation left right)
    (coordinate : Coordinate) (output : HashOutput) (hhit : right.state.hitAt coordinate output) :
    left.state.hitAt coordinate output := by
  rw [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.mem_pendingAt_iff] at hhit ⊢
  exact h.pending hhit

theorem PendingRelaxation.clearPending {left right : DeferredContext} (h : PendingRelaxation left right) (coordinate : Coordinate) :
    PendingRelaxation { left with state := left.state.clearPending coordinate }
      { right with state := right.state.clearPending coordinate } := by
  refine ⟨h.stateValues, h.privateValues, h.revealed, ?_⟩
  intro pair hpair
  exact Finset.mem_filter.mpr ⟨h.pending (Finset.mem_filter.mp hpair).1, (Finset.mem_filter.mp hpair).2⟩

theorem PendingRelaxation.completePrivatePosition {left right : DeferredContext} (h : PendingRelaxation left right)
    (position : Position) (output : HashOutput) :
    PendingRelaxation (completePrivatePosition position left output).toDeferredContext
      (completePrivatePosition position right output).toDeferredContext := by
  have hc := h.clearPending (.position position)
  exact ⟨hc.stateValues, by
    change left.values.install position output = right.values.install position output
    rw [h.privateValues], hc.revealed, hc.pending⟩

def PendingResolutionRel (left right : DeferredResolution) : Prop :=
  PendingRelaxation left.toDeferredContext right.toDeferredContext ∧ left.output = right.output

theorem relTriple_resolveDeferredPositionValue_pendingRelaxation
    (position : Position) (left right : DeferredContext) (h : PendingRelaxation left right) :
    RelTriple (resolveDeferredPositionValue position left) (resolveDeferredPositionValue position right)
      (OptionRefines PendingResolutionRel) := by
  rw [resolveDeferredPositionValue_eq_bind_output, resolveDeferredPositionValue_eq_bind_output]
  have hd : deferredPositionOutput position left = deferredPositionOutput position right := by
    simp only [deferredPositionOutput, h.positionValue position]
  rw [hd]
  apply relTriple_bind (relTriple_refl _)
  intro output other heq
  subst other
  unfold resolvePrivatePositionWithOutput
  by_cases hl : left.state.hitAt (.position position) output
  · rw [if_pos hl]
    exact relTriple_none_optionRefines PendingResolutionRel _
  · have hr : ¬right.state.hitAt (.position position) output := fun hh => hl (h.hitAt _ _ hh)
    rw [if_neg hl, if_neg hr]
    exact relTriple_pure_pure ⟨h.completePrivatePosition position output, rfl⟩

theorem resolveDeferredChainStart_pendingRelaxation
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (left right : DeferredContext) (h : PendingRelaxation left right) :
    OptionRefines PendingResolutionRel (resolveDeferredChainStart table index left) (resolveDeferredChainStart table index right) := by
  unfold resolveDeferredChainStart
  rw [h.stateValues]
  cases hs : right.state.values index.coordinate with
  | some output =>
      by_cases hl : left.state.hitAt index.coordinate output
      · simp [hs, hl, OptionRefines]
      · have hr : ¬right.state.hitAt index.coordinate output := fun hh => hl (h.hitAt _ _ hh)
        simp only [hs, if_neg hl, if_neg hr, OptionRefines, PendingResolutionRel]
        exact ⟨h.clearPending index.coordinate, trivial⟩
  | none =>
      by_cases hl : left.state.hitAt index.coordinate (table index)
      · simp [hs, hl, OptionRefines]
      · have hr : ¬right.state.hitAt index.coordinate (table index) := fun hh => hl (h.hitAt _ _ hh)
        simp only [hs, if_neg hl, if_neg hr, OptionRefines, PendingResolutionRel]
        exact ⟨h.clearPending index.coordinate, trivial⟩

theorem relTriple_resolveDeferredChainPrefix_pendingRelaxation
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps left right, PendingRelaxation left right →
      RelTriple (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps left)
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps right) (OptionRefines PendingResolutionRel)
  | 0, _, left, right, h => relTriple_pure_pure (resolveDeferredChainStart_pendingRelaxation table _ left right h)
  | steps + 1, hsteps, left, right, h => by
      simp only [resolveDeferredChainPrefix]
      apply relTriple_bind
        (relTriple_resolveDeferredChainPrefix_pendingRelaxation table lay tree leafIdx chainIdx steps (by omega) left right h)
      intro a b hab
      cases a with
      | none => exact relTriple_none_optionRefines _ _
      | some a =>
          cases b with
          | none => exact False.elim hab
          | some b => exact relTriple_resolveDeferredPositionValue_pendingRelaxation _ _ _ hab.1

theorem relTriple_resolveDeferredChains_pendingRelaxation
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ∀ chains left right, PendingRelaxation left right →
      RelTriple (resolveDeferredChains table lay tree leafIdx chains left)
        (resolveDeferredChains table lay tree leafIdx chains right) (OptionRefines PendingRelaxation)
  | [], left, right, h => relTriple_pure_pure h
  | chainIdx :: remaining, left, right, h => by
      simp only [resolveDeferredChains]
      apply relTriple_bind
        (relTriple_resolveDeferredChainPrefix_pendingRelaxation table lay tree leafIdx chainIdx _ (by omega) left right h)
      intro a b hab
      cases a with
      | none => exact relTriple_none_optionRefines _ _
      | some a =>
          cases b with
          | none => exact False.elim hab
          | some b => exact relTriple_resolveDeferredChains_pendingRelaxation table lay tree leafIdx remaining _ _ hab.1

theorem relTriple_resolveDeferredOtsLeaf_pendingRelaxation
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (left right : DeferredContext) (h : PendingRelaxation left right) :
    RelTriple (resolveDeferredOtsLeaf table lay tree leafIdx left) (resolveDeferredOtsLeaf table lay tree leafIdx right)
      (OptionRefines PendingResolutionRel) := by
  unfold resolveDeferredOtsLeaf
  apply relTriple_bind (relTriple_resolveDeferredChains_pendingRelaxation table lay tree leafIdx _ left right h)
  intro a b hab
  cases a with
  | none => exact relTriple_none_optionRefines _ _
  | some a =>
      cases b with
      | none => exact False.elim hab
      | some b => exact relTriple_resolveDeferredPositionValue_pendingRelaxation _ _ _ hab

theorem relTriple_resolveDeferredTreeNode_pendingRelaxation
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel left right, PendingRelaxation left right →
      RelTriple (resolveDeferredTreeNode table lay tree level nodeIdx hlevel left)
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel right) (OptionRefines PendingResolutionRel)
  | 0, nodeIdx, _, left, right, h => relTriple_resolveDeferredOtsLeaf_pendingRelaxation table lay tree _ left right h
  | level + 1, nodeIdx, hlevel, left, right, h => by
      simp only [resolveDeferredTreeNode]
      apply relTriple_bind
        (relTriple_resolveDeferredTreeNode_pendingRelaxation table lay tree level (2 * nodeIdx) (by omega) left right h)
      intro a b hab
      cases a with
      | none => exact relTriple_none_optionRefines _ _
      | some a =>
          cases b with
          | none => exact False.elim hab
          | some b =>
              apply relTriple_bind
                (relTriple_resolveDeferredTreeNode_pendingRelaxation table lay tree level (2 * nodeIdx + 1) (by omega) _ _ hab.1)
              intro c d hcd
              cases c with
              | none => exact relTriple_none_optionRefines _ _
              | some c =>
                  cases d with
                  | none => exact False.elim hcd
                  | some d => exact relTriple_resolveDeferredPositionValue_pendingRelaxation _ _ _ hcd.1

theorem relTriple_resolveDeferredPosition_pendingRelaxation
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (left right : DeferredContext) (h : PendingRelaxation left right) :
    RelTriple (resolveDeferredPosition table position left) (resolveDeferredPosition table position right)
      (OptionRefines PendingResolutionRel) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact relTriple_resolveDeferredChainPrefix_pendingRelaxation table lay tree leafIdx chainIdx _ _ left right h
  | leaf lay tree leafIdx => exact relTriple_resolveDeferredOtsLeaf_pendingRelaxation table lay tree leafIdx left right h
  | node lay tree level nodeIdx => exact relTriple_resolveDeferredTreeNode_pendingRelaxation table lay tree _ _ _ left right h
  | _ => exact relTriple_resolveDeferredPositionValue_pendingRelaxation _ left right h

theorem relTriple_resolveDeferredReveal_pendingRelaxation
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (left right : DeferredContext) (h : PendingRelaxation left right) :
    RelTriple (resolveDeferredReveal table position left) (resolveDeferredReveal table position right)
      (OptionRefines PendingResolutionRel) := by
  unfold resolveDeferredReveal
  split_ifs
  · exact relTriple_resolveDeferredPosition_pendingRelaxation table position left right h
  · exact relTriple_resolveDeferredPositionValue_pendingRelaxation position left right h

end SphincsSecurity.Concrete.OtsProbeSimulation
